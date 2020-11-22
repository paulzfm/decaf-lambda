package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.driver.{Config, Phase}
import decaf.frontend.annot.ScopeImplicit._
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.parsing.Pos
import decaf.frontend.tree.SyntaxTree.NoAnnot
import decaf.frontend.tree.TreeNode._
import decaf.frontend.tree.TypedTree._
import decaf.frontend.tree.{NamedTree => Named}
import decaf.lowlevel.log.IndentPrinter
import decaf.printing.PrettyScope

import scala.collection.mutable

/**
  * The typer phase: type check every statement and expression. It starts right after [[Namer]].
  *
  * Typer will NOT be interrupted by any type error. Instead, an ill-typed term will either be filled with a guessed
  * type, if this term could only be of that type in some situations, or we replace it with an error node.
  *
  * @see [[Namer]]
  * @see [[decaf.frontend.annot.Type]]
  */
class Typer(implicit config: Config) extends Phase[Named.Tree, Tree]("typer", config) with Util {

  /**
    * Transformer entry.
    *
    * @param tree a typed tree with untyped holes
    * @return a fully typed (i.e. without holes) tree if succeeds
    */
  override def transform(tree: Named.Tree): Tree = {
    val global = new ScopeContext(tree.scope)
    val checkedClasses = tree.classes.map {
      case clazz@Named.ClassDef(classMod, id, parent, fields) =>
        val symbol = clazz.symbol
        val ctx = global.open(symbol.scope)
        val checkedFields = fields.map {
          case v@Named.VarDef(typeLit, id) => VarDef(typeLit, id)(v.symbol)
          case m@Named.MethodDef(mod, id, returnType, params, body) =>
            val formalCtx = ctx.open(m.symbol.scope)
            val captured = mutable.Set[CVar]()
            val returnTypes = mutable.ArrayBuffer[Type]()
            val ps = params map {
              checkLocalVarDef(_)(formalCtx, captured, returnTypes, false)
            }
            val checkedBody = body.map { b =>
              val (checkedBody, returns) = checkBlock(b)(formalCtx, captured, returnTypes, false)
              // Check if the body always returns a value, when the method is non-void
              if (!m.symbol.returnType.isVoidType && !returns) {
                issue(new MissingReturnError(b.pos))
              }
              checkedBody
            }
            MethodDef(mod, id, returnType, ps, checkedBody)(m.symbol).setPos(m.pos)
        }
        ClassDef(classMod, id, parent, checkedFields)(symbol).setPos(clazz.pos)
    }

    TopLevel(checkedClasses)(tree.scope).setPos(tree.pos)
  }

  /**
    * After type checking succeeds, pretty print scopes if necessary.
    *
    * @param tree the typed tree
    */
  override def onSucceed(tree: Tree): Unit = {
    if (config.target == Config.Target.PA2) {
      val printer = new PrettyScope(new IndentPrinter(config.output))
      printer.pretty(tree.scope)
      printer.flush()
    }
  }

  /**
    * Type check a statement block.
    *
    * @param block      statement block
    * @param ctx        scope context
    * @param insideLoop are we inside a loop?
    * @return a pair: the typed block, and a boolean indicating if this block returns a value
    */
  def checkBlock(block: Named.Block)(implicit ctx: ScopeContext, captured: CapturedSet,
                                     returnTypes: mutable.ArrayBuffer[Type], insideLoop: Boolean): (Block, Boolean) = {
    val localCtx = ctx.open(block.scope)
    val ss = block.stmts.map {
      checkStmt(_)(localCtx, captured, returnTypes, insideLoop)
    }
    val returns = ss.nonEmpty && ss.last._2 // a block returns a value iff its last statement does so

    (Block(ss.map(_._1))(block.scope).setPos(block.pos), returns)
  }

  def checkLocalVarDef(v: Named.LocalVarDef)(implicit ctx: ScopeContext, captured: CapturedSet,
                                             returnTypes: mutable.ArrayBuffer[Type], insideLoop: Boolean): LocalVarDef = {
    v.init match {
      case Some(expr) =>
        // Special: we need to be careful that the initializer may cyclically refer to the declared variable, e.g.
        // var x = x + 1.
        v.symbol.isInitializing = true
        val r = typeExpr(expr)
        v.symbol.isInitializing = false

        if (!(r.typ <= v.typeLit.typ)) issue(new IncompatBinOpError("=", v.typeLit.typ, r.typ, v.assignPos))
        LocalVarDef(v.typeLit, v.id, Some(r), v.assignPos)(v.symbol)
      case None => LocalVarDef(v.typeLit, v.id, None, v.assignPos)(v.symbol)
    }
  }

  /**
    * Type check a statement.
    *
    * @param stmt       statement
    * @param ctx        scope context
    * @param insideLoop are we inside a loop?
    * @return a pair: the typed statement, and a boolean indicating if this statement returns a value
    */
  def checkStmt(stmt: Named.Stmt)(implicit ctx: ScopeContext, captured: CapturedSet,
                                  returnTypes: mutable.ArrayBuffer[Type], insideLoop: Boolean): (Stmt, Boolean) = {
    val checked = stmt match {
      case block: Named.Block => checkBlock(block)

      case v: Named.LocalVarDef => (checkLocalVarDef(v), false)

      case v: Named.UntypedLocalVarDef =>
        v.symbol.isInitializing = true
        val e = typeExpr(v.init)
        v.symbol.isInitializing = false

        if (e.typ.isVoidType) issue(new BadVarTypeError(v.id, v.pos))
        v.symbol.setType(e.typ)
        (UntypedLocalVarDef(v.id, e, v.assignPos)(v.symbol), false)

      case Named.Assign(lhs, rhs) =>
        val l = typeLValue(lhs)
        val r = typeExpr(rhs)
        l.typ match {
          case t if !(r.typ <= t) => issue(new IncompatBinOpError("=", l.typ, r.typ, stmt.pos))
          case _ => // do nothing
        }

        l match {
          case LocalVar(v) if ctx.inLambda && (captured contains CLocal(v)) =>
            // in lambda, cannot assign values to captured variables
            issue(new CannotAssignToCapturedError(stmt.pos))
          case m: FakeLValue =>
            issue(new CannotAssignToMethodError(m.method.name, stmt.pos))
          case _ =>
        }

        (Assign(l, r), false)

      case Named.ExprEval(expr) =>
        val e = typeExpr(expr)
        (ExprEval(e), false)

      case Named.Skip() => (Skip(), false)

      case Named.If(cond, trueBranch, falseBranch) =>
        val c = checkTestExpr(cond)
        val (t, trueReturns) = checkBlock(trueBranch)
        val f = falseBranch.map(checkBlock)
        // if-stmt returns a value if both branches return
        val returns = trueReturns && f.isDefined && f.get._2
        (If(c, t, f.map(_._1)), returns)

      case Named.While(cond, body) =>
        val c = checkTestExpr(cond)
        val (b, _) = checkBlock(body)(ctx, captured, returnTypes, true)
        (While(c, b), false)

      case Named.For(init, cond, update, body) =>
        // Since `init` and `update` may declare local variables, remember to first open the local scope of `body`.
        val local = ctx.open(body.scope)
        val (i, _) = checkStmt(init)(local, captured, returnTypes, insideLoop)
        val c = checkTestExpr(cond)(local, captured)
        val (u, _) = checkStmt(update)(local, captured, returnTypes, insideLoop)
        val ss = body.stmts.map {
          checkStmt(_)(local, captured, returnTypes, true)
        }
        val b = Block(ss.map(_._1))(body.scope)
        (For(i, c, u, b), false)

      case Named.Break() =>
        if (!insideLoop) issue(new BreakOutOfLoopError(stmt.pos))
        (Break(), false)

      case Named.Return(expr) =>
        val e = expr.map {
          typeExpr(_)
        }
        val actual = e.map(_.typ).getOrElse(VoidType)
        if (ctx.inLambda) { // in lambda
          if (expr.isDefined) returnTypes += actual
        } else { // in normal method
          val expected = ctx.currentMethod.returnType
          if (actual.noError && !(actual <= expected)) issue(new BadReturnTypeError(expected, actual, stmt.pos))
        }
        (Return(e), e.isDefined)

      case Named.Print(exprs) =>
        val es = exprs.zipWithIndex.map {
          case (expr, i) =>
            val e = typeExpr(expr)
            if (e.typ.noError && !e.typ.isBaseType) issue(new BadPrintArgError(i + 1, e.typ, expr.pos))
            e
        }
        (Print(es), false)
    }

    checked match {
      case (s, r) => (s.setPos(stmt.pos), r)
    }
  }

  /**
    * Check if an expression has type bool.
    *
    * @param expr expression
    * @param ctx  scope context
    * @return true if it has type bool
    */
  private def checkTestExpr(expr: Named.Expr)(implicit ctx: ScopeContext, captured: CapturedSet): Expr = {
    val e = typeExpr(expr)
    if (e.typ !== BoolType) issue(new BadTestExpr(expr.pos))
    e
  }

  implicit val noType: NoType.type = NoType

  /**
    * Type check an expression.
    *
    * @param expr expression
    * @param ctx  scope context
    * @return typed expression
    */
  def typeExpr(expr: Named.Expr)(implicit ctx: ScopeContext, captured: CapturedSet): Expr = {
    val err = UntypedExpr(expr)

    val typed = expr match {
      case e: Named.LValue => typeLValue(e)

      case Named.IntLit(v) => IntLit(v)(IntType)
      case Named.BoolLit(v) => BoolLit(v)(BoolType)
      case Named.StringLit(v) => StringLit(v)(StringType)
      case Named.NullLit() => NullLit()(NullType)

      case Named.ReadInt() => ReadInt()(IntType)
      case Named.ReadLine() => ReadLine()(StringType)

      case Named.Unary(op, operand) =>
        val e = typeExpr(operand)
        e.typ match {
          case NoType => // avoid nested errors
          case t =>
            if (!compatible(op, t)) issue(new IncompatUnOpError(op, t, expr.pos))
        }
        // Even when it doesn't type check, we could make a fair guess based on the operator kind.
        // Let's say the operator is `-`, then one possibly wants an integer as the operand.
        // Once he/she fixes the operand, according to our type inference rule, the whole unary expression
        // must have type int! Thus, we simply _assume_ it has type int, rather than `NoType`.
        Unary(op, e)(resultTypeOf(op))

      case Named.Binary(op, lhs, rhs) =>
        val l = typeExpr(lhs)
        val r = typeExpr(rhs)
        (l.typ, r.typ) match {
          case (_, NoType) | (NoType, _) => // avoid nested errors
          case (lt, rt) =>
            if (!compatible(op, lt, rt)) issue(new IncompatBinOpError(op, lt, rt, expr.pos))
        }
        Binary(op, l, r)(resultTypeOf(op)) // make a fair guess

      case Named.NewArray(elemType, length) =>
        // elemType is already typed
        val l = typeExpr(length)
        if (elemType.typ.isVoidType) issue(new BadArrElementError(elemType.pos))
        if (l.typ !== IntType) issue(new BadNewArrayLength(length.pos))
        NewArray(elemType, l)(ArrayType(elemType.typ)) // make a fair guess

      case Named.NewClass(id) =>
        ctx.global.find(id) match {
          case Some(clazz) =>
            if (clazz.isAbstract) issue(new CannotInstantiateError(id, expr.pos))
            NewClass(clazz)(clazz.typ)
          case None => issue(new ClassNotFoundError(id, expr.pos)); err
        }

      case Named.This() =>
        if (ctx.currentMethod.isStatic) issue(new ThisInStaticFuncError(expr.pos))
        captured += CThis
        This()(ctx.currentClass.typ) // make a fair guess

      case call@Named.Call(func, args) =>
        val f = typeExpr(func)
        f match {
          case MemberMethod(receiver, method) => typeCall(call.pos, args, Some(receiver), method)
          case StaticMethod(method) => typeCall(call.pos, args, None, method)
          case ArrayLenMethod(array) =>
            if (args.nonEmpty) issue(new BadLengthArgError(args.length, expr.pos))
            ArrayLen(array)(IntType)
          case s =>
            s.typ match {
              case NoType | VoidType => err
              case FunType(xs, t) =>
                if (xs.length != args.length) func match {
                  case Named.VarSel(None, name) => issue(new BadArgCountError(name, xs.length, args.length, call.pos))
                  case _ => issue(new LambdaBadArgCountError(xs.length, args.length, call.pos))
                }
                val as = (xs zip args).zipWithIndex.map {
                  case ((t, a), i) =>
                    val e = typeExpr(a)
                    if (e.typ.noError && !(e.typ <= t)) {
                      issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
                    }
                    e
                }
                LambdaCall(f, as)(t)
              case t => issue(new NotCallableError(t, call.pos)); err
            }
        }

      case Named.LambdaExpr(params, body, symbol) =>
        val formalCtx = ctx.open(symbol.scope)
        val innerCaptured = mutable.Set[CVar]()
        val returnTypes = mutable.ArrayBuffer[Type]()
        val ps = params map {
          checkLocalVarDef(_)(formalCtx, innerCaptured, returnTypes, false)
        }
        val (b, returns) = checkBlock(body)(formalCtx, innerCaptured, returnTypes, false)

        // any captured variable in the inner lambda that is not locally defined in the outer lambda,
        // must be captured also by the outer
        innerCaptured.foreach {
          case CThis => captured += CThis
          case CLocal(v) if ctx.indexOf(v.domain) > ctx.indexOf(ctx.currentFormal) => captured += CLocal(v)
          case _ => // not capture in outer
        }

        val returnType =
          if (!returns && returnTypes.isEmpty) VoidType
          else {
            if (!returns && returnTypes.nonEmpty) {
              issue(new MissingReturnError(body.pos))
              NoType
            }

            val t = returnTypes.reduceLeft(Type.lub)
            if (!t.noError) issue(new IncompatibleReturnTypesError(body.pos))
            t
          }
        symbol.setReturnType(returnType)
        LambdaExpr(ps, b, symbol, innerCaptured)(symbol.typ)

      case Named.ClassTest(obj, clazz) =>
        val o = typeExpr(obj)
        if (!o.typ.isClassType) issue(new NotClassError(o.typ, expr.pos))
        ctx.global.find(clazz) match {
          case Some(c) => ClassTest(o, c)(BoolType)
          case None => issue(new ClassNotFoundError(clazz.name, expr.pos)); err
        }

      case Named.ClassCast(obj, clazz) =>
        val o = typeExpr(obj)
        if (!o.typ.isClassType) issue(new NotClassError(o.typ, o.pos))
        ctx.global.find(clazz) match {
          case Some(c) => ClassCast(o, c)(c.typ)
          case None => issue(new ClassNotFoundError(clazz.name, expr.pos)); err
        }
    }
    typed.setPos(expr.pos)
  }

  private def typeCall(callPos: Pos, args: List[Expr], receiver: Option[Expr], method: MethodSymbol)
                      (implicit ctx: ScopeContext, captured: CapturedSet): Expr = {
    // Cannot call this's member methods in a static method
    if (receiver.isEmpty && ctx.currentMethod.isStatic && !method.isStatic) {
      issue(new RefNonStaticError(method.name, ctx.currentMethod.name, callPos))
    }
    if (method.arity != args.length) {
      issue(new BadArgCountError(method.name, method.arity, args.length, callPos))
    }
    val as = (method.typ.args zip args).zipWithIndex.map {
      case ((t, a), i) =>
        val e = typeExpr(a)
        if (e.typ.noError && !(e.typ <= t)) {
          issue(new BadArgTypeError(i + 1, t, e.typ, a.pos))
        }
        e
    }

    if (method.isStatic) {
      StaticCall(method, as)(method.returnType)
    } else {
      MemberCall(receiver.getOrElse(This()(ctx.currentClass.typ)), method, as)(method.returnType)
    }
  }

  private def typeLValue(expr: Named.LValue)(implicit ctx: ScopeContext, captured: CapturedSet): LValue = {
    val err = UntypedLValue(expr)

    val typed = expr match {
      // Variable, which should be complicated since a legal variable could refer to a local var,
      // a visible member var (, and a class name).
      case Named.VarSel(None, id) =>
        ctx.lookupBefore(id, expr.pos) match {
          case Some(sym) => sym match {
            case v: LocalVarSymbol if v.isInitializing =>
              issue(new UndeclVarError(id, expr.pos))
              err
            case v: LocalVarSymbol if !v.isInitializing =>
              if (ctx.indexOf(ctx.currentFormal) < ctx.indexOf(v.domain)) { // captured variable
                captured += CLocal(v)
              }
              LocalVar(v)(v.typ)
            case v: MemberVarSymbol =>
              if (ctx.currentMethod.isStatic) { // member vars cannot be accessed in a static method
                issue(new RefNonStaticError(id, ctx.currentMethod.name, expr.pos))
              }
              // captured this
              captured += CThis
              MemberVar(This(), v)(v.typ)
            case m: MethodSymbol =>
              if (!m.isStatic && ctx.currentMethod.isStatic) { // member methods cannot be accessed in a static method
                issue(new RefNonStaticError(id, ctx.currentMethod.name, expr.pos))
              }
              if (!m.isStatic) {
                // captured this
                captured += CThis
                MemberMethod(This()(ctx.currentClass.typ), m)(m.typ)
              } else StaticMethod(m)(m.typ)
            case _ => issue(new UndeclVarError(id, expr.pos)); err
          }
          case None => issue(new UndeclVarError(id, expr.pos)); err
        }

      case Named.VarSel(Some(Named.VarSel(None, id)), m) if ctx.global.contains(id) =>
        // special case like MyClass.foo
        val clazz = ctx.global(id)
        clazz.scope.lookup(m) match {
          case Some(s) => s match {
            case method: MethodSymbol if method.isStatic => StaticMethod(method)(method.typ)
            case _ => issue(new NotClassFieldError(m, clazz.typ, expr.pos)); err
          }
          case _ => issue(new FieldNotFoundError(m, clazz.typ, expr.pos)); err
        }

      case Named.VarSel(Some(receiver), id) =>
        val r = typeExpr(receiver)
        r.typ match {
          case NoType => err
          case _: ArrayType if id.name == "length" => // Special case: array.length
            ArrayLenMethod(r)(FunType(Nil, IntType))
          case t@ClassType(c, _) =>
            ctx.global(c).scope.lookup(id) match {
              case Some(sym) => sym match {
                case v: MemberVarSymbol =>
                  if (!(ctx.currentClass.typ <= t)) { // member vars are protected
                    issue(new FieldNotAccessError(id, t, expr.pos))
                  }
                  MemberVar(r, v)(v.typ)
                case m: MethodSymbol =>
                  if (m.isStatic) StaticMethod(m)(m.typ)
                  else MemberMethod(r, m)(m.typ)
                case _ => issue(new FieldNotFoundError(id, t, expr.pos)); err
              }
              case None => issue(new FieldNotFoundError(id, t, expr.pos)); err
            }
          case t => issue(new NotClassFieldError(id, t, expr.pos)); err
        }

      case Named.IndexSel(array, index) =>
        val a = typeExpr(array)
        val i = typeExpr(index)
        val typ = a.typ match {
          case NoType => NoType
          case ArrayType(elemType) =>
            if (i.typ !== IntType) issue(new SubNotIntError(expr.pos))
            elemType // make a fair guess
          case _ => issue(new NotArrayError(array.pos)); NoType
        }
        IndexSel(a, i)(typ)
    }
    typed.setPos(expr.pos)
  }

  private def compatible(op: Op, operand: Type): Boolean = op match {
    case NEG => operand === IntType // if e : int, then -e : int
    case NOT => operand === BoolType // if e : bool, then !e : bool
  }

  private def compatible(op: Op, lhs: Type, rhs: Type): Boolean = op match {
    case _: ArithOp => (lhs === IntType) && (rhs === IntType) // if e1, e2 : int, then e1 + e2 : int
    case _: LogicOp => (lhs === BoolType) && (rhs === BoolType) // if e1, e2 : bool, then e1 && e2 : bool
    case _: EqOp => (lhs <= rhs) || (rhs <= lhs) // if e1 : T1, e2 : T2, T1 <: T2 or T2 <: T1, then e1 == e2 : bool
    case _: CmpOp => (lhs === IntType) && (rhs === IntType) // if e1, e2 : int, then e1 > e2 : bool
  }

  private def resultTypeOf(op: Op): Type = op match {
    case NEG => IntType
    case NOT => BoolType
    case _: ArithOp => IntType
    case _: LogicOp | _: EqOp | _: CmpOp => BoolType
  }
}