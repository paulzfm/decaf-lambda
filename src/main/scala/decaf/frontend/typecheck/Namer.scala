package decaf.frontend.typecheck

import decaf.driver.error._
import decaf.driver.{Config, Phase}
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.tree.NamedTree.TypedTypeLit
import decaf.frontend.tree.SyntaxTree._
import decaf.frontend.tree.TreeNode._
import decaf.frontend.tree.{NamedTree => Named}

import scala.collection.mutable

/**
  * The namer phase: resolve all symbols defined in the abstract syntax tree and store them in symbol tables (i.e.
  * scopes).
  *
  * ==Overview==
  * The entire type checking pass is split into two phases -- [[Namer]] and [[Typer]].
  *
  * Why two? Note that all defined classes are visible to every other class, which means we can access another
  * class's members, and of course the type that itself represents, e.g.
  * {{{
  * class A {
  *     class B foo; // access B
  *     void bar() {
  *         foo.baz(); // access baz of B
  *     }
  * }
  * class B {
  *     void baz();
  * }
  * }}}
  *
  * Apparently, classes cannot be resolved in the order they presented in the syntax tree: `A` refers to `B`,
  * whose definition goes '''later'''. To tackle this issue, one possible way is to first scan all classes ''roughly''
  * and then step into details of every method body -- because at that time, signatures of class members are known.
  *
  * In the [[Namer]] phase, we just scan all class members, while ignoring any statement/expressions which doesn't
  * define a new symbol (a variable), because that's enough for us to know what a class looks like.
  * After this phase, a '''not fully-typed''' tree is returned. In this tree:
  *
  *   - class and members are associated with their symbols (also the scopes)
  *   - methods are associated with their formal scopes (which contains symbols of parameters)
  *   - blocks are associated with their local scopes (which contains symbols of local variables)
  *
  * However, no typing checking has yet been done for any statement or expression.
  *
  * ===Implicit Contexts===
  * As you can see, implicits are widely-used in this project. I hope all of them are appropriate and not abused.
  * In particular, contexts are quite important and common in a type checking algorithm. However, since many times
  * contexts are passing to other functions without any change, specifying them are implicit parameters makes our
  * life easier -- we only need to explicitly pass them whenever they are updated, in very few situations!
  *
  * @see [[Typer]]
  * @see [[decaf.frontend.annot.Scope]]
  * @see [[decaf.frontend.annot.Symbol]]
  */
class Namer(implicit config: Config) extends Phase[Tree, Named.Tree]("namer", config) with Util {

  class Context {

    val global: GlobalScope = new GlobalScope
    val classes: mutable.Map[String, ClassDef] = new mutable.TreeMap
  }

  /**
    * Transformer entry.
    *
    * @param tree an (untyped) abstract syntax tree
    * @return a typed tree with untyped holes
    */
  override def transform(tree: Tree): Named.Tree = {
    implicit val ctx = new Context

    // Check conflicting definitions. If any, ignore the redefined ones.
    tree.classes.foreach {
      clazz =>
        ctx.classes.get(clazz.name) match {
          case Some(earlier) => issue(new DeclConflictError(clazz.name, earlier.pos, clazz.pos))
          case None => ctx.classes(clazz.name) = clazz
        }
    }

    // Make sure the base class exists. If not, ignore the inheritance.
    ctx.classes.foreach {
      case (name, clazz) =>
        clazz.parent match {
          case Some(Id(base)) if !ctx.classes.contains(base) =>
            issue(new ClassNotFoundError(base, clazz.pos))
            ctx.classes(name) = clazz.parentDetached
          case _ =>
        }
    }

    // Make sure any inheritance does not form a cycle.
    checkCycles()
    // If so, return with errors.
    if (hasError) return Named.TopLevel(Nil)(ctx.global)

    // So far, class inheritance is well-formed, i.e. inheritance relations form a forest of trees. Now we need to
    // resolve every class definition, make sure that every member (variables and methods) is well-typed.
    // Realizing that a class type can be used in the definition of a class member, either a variable or a method,
    // we shall first know all the accessible class types in the program. These types are wrapped into what we called
    // `ClassSymbol`s. Note that currently, the associated `scope` is empty because member resolving has not started
    // yet. All class symbols are stored in the global scope.
    createClassSymbols()

    // Now, we can resolve every class definition to fill in its class scope table. To check if the overriding
    // behaves correctly, we should first resolve super class and then its subclasses.
    val resolvedClasses = resolveClasses

    // Finally, let's locate the main class, whose name is 'Main', and contains a method like:
    //  static void main() { ... }
    resolvedClasses.find(_.name == "Main") match {
      case Some(clazz) if !clazz.symbol.isAbstract =>
        clazz.symbol.scope.find("main") match {
          case Some(symbol) =>
            symbol match {
              case f: MethodSymbol if f.isStatic && (f.typ === FunType(Nil, VoidType)) => f.setMain()
              case _ => issue(NoMainClassError)
            }
          case _ => issue(NoMainClassError)
        }
      case _ => issue(NoMainClassError)
    }

    Named.TopLevel(resolvedClasses)(ctx.global).setPos(tree.pos)
  }

  /**
    * Check if class inheritance form cycle(s).
    */
  private def checkCycles()(implicit ctx: Context): Unit = {
    val visitedTime = new mutable.TreeMap[String, Int]
    ctx.classes.keys.foreach {
      visitedTime(_) = 0
    }

    @scala.annotation.tailrec
    def visit(from: ClassDef, node: String, time: Int): Unit = {
      if (visitedTime(node) == 0) { // not visited yet
        visitedTime(node) = time
        val clazz = ctx.classes(node)
        clazz.parent match {
          case Some(Id(base)) => visit(clazz, base, time)
          case _ => // done
        }
      } else if (visitedTime(node) == time) { // find a cycle
        issue(new BadInheritanceError(from.pos))
        // ctx.classes(from.name) = from.parentDetached
      } // else: this node is visited earlier, also done
    }

    var time = 1
    for {
      node <- ctx.classes.keys
      if visitedTime(node) == 0
    } yield {
      visit(null, node, time)
      time += 1
    }
  }

  /**
    * Create class symbols and declare in the global scope.
    *
    * @param ctx context
    */
  private def createClassSymbols()(implicit ctx: Context): Unit = {
    def create(clazz: ClassDef): Unit = {
      if (!ctx.global.contains(clazz.name)) {
        val symbol = clazz.parent match {
          case Some(Id(base)) =>
            create(ctx.classes(base))
            val baseSymbol = ctx.global(base)
            val typ = ClassType(clazz.name, Some(baseSymbol.typ))
            val scope = new ClassScope(Some(baseSymbol.scope))
            new ClassSymbol(clazz, typ, scope, Some(baseSymbol))
          case None =>
            val typ = ClassType(clazz.name)
            val scope = new ClassScope()
            new ClassSymbol(clazz, typ, scope)
        }
        ctx.global.declare(symbol)
      }
    }

    ctx.classes.values.foreach(create)
  }

  /**
    * Resolve class definitions.
    *
    * @param ctx context
    * @return resolved classes
    */
  def resolveClasses(implicit ctx: Context): List[Named.ClassDef] = {
    val resolved = new mutable.TreeMap[String, Named.ClassDef]
    val absTable = new mutable.TreeMap[String, Set[MethodSymbol]]

    def resolve(clazz: ClassDef): Unit = {
      if (!resolved.contains(clazz.name)) {
        val symbol = clazz.parent match {
          case Some(Id(base)) =>
            resolve(ctx.classes(base))
            ctx.global(clazz.name)
          case None =>
            ctx.global(clazz.name)
        }

        val classCtx: ScopeContext = new ScopeContext(ctx.global).open(symbol.scope)
        val toOverride = clazz.parent match {
          case None => mutable.TreeSet[MethodSymbol]()
          case Some(b) => mutable.TreeSet.from(absTable(b))
        }
        val fs = clazz.fields.flatMap {
          resolveField(_)(classCtx, toOverride)
        }
        resolved(clazz.name) = Named.ClassDef(clazz.modifiers, clazz.id, symbol.parent, fs)(symbol).setPos(clazz.pos)
        absTable(clazz.name) = toOverride.toSet

        if (!clazz.modifiers.isAbstract && toOverride.nonEmpty) {
          issue(new ClassNotAbstractError(clazz.name, clazz.pos))
        }
      }
    }

    ctx.classes.values.foreach(resolve)
    ctx.classes.keys.map(resolved).toList
  }

  /**
    * Resolve a field definition.
    *
    * @param field field
    * @param ctx   scope context
    * @return resolved field
    */
  def resolveField(field: Field)(implicit ctx: ScopeContext,
                                 abstractMethods: mutable.Set[MethodSymbol]): Option[Named.Field] = {
    val resolved = ctx.findConflict(field.name) match {
      case Some(earlier) if earlier.domain == ctx.currentScope => // always conflict
        issue(new DeclConflictError(field.name, earlier.pos, field.pos)); None
      case Some(earlier) => // maybe override?
        (earlier, field) match {
          case (_: MemberVarSymbol, _: VarDef) =>
            issue(new OverridingVarError(field.name, field.pos))
            None
          case (suspect: MethodSymbol, m@MethodDef(mod, id, returnType, params, body))
            if !suspect.isStatic && !m.isStatic =>

            // Cannot override a concrete method with abstract.
            if (m.isAbstract && !suspect.isAbstract) {
              issue(new DeclConflictError(field.name, earlier.pos, field.pos))
              None
            } else {
              val ret = typeTypeLit(returnType)
              ret.typ match {
                case NoType => None
                case retType =>
                  val formalScope = new FormalScope
                  val formalCtx = ctx.open(formalScope)
                  if (!m.isStatic) formalCtx.declare(LocalVarSymbol.thisVar(ctx.currentClass.typ, id.pos))
                  val typedParams = params.map {
                    resolveLocalVarDef(_)(formalCtx)
                  }
                  val funType = FunType(typedParams.map(_.typeLit.typ), retType)
                  if (funType <= suspect.typ) { // override success
                    val symbol = new MethodSymbol(m, funType, formalScope, ctx.currentClass)
                    ctx.declare(symbol)
                    // Possibly override an abstract method.
                    if (suspect.isAbstract) abstractMethods -= suspect
                    if (m.isAbstract) abstractMethods += symbol
                    val block = body.map {
                      resolveBlock(_)(formalCtx)
                    }
                    Some(Named.MethodDef(mod, id, TypedTypeLit(ret)(ret.typ), typedParams, block)(symbol))
                  } else { // override failure
                    issue(new BadOverrideError(m.name, suspect.owner.name, m.pos))
                    None
                  }
              }
            }
          case _ => issue(new DeclConflictError(field.name, earlier.pos, field.pos)); None
        }
      case None =>
        field match {
          case v@VarDef(typeLit, id) =>
            val lit = typeTypeLit(typeLit)
            lit.typ match {
              case NoType => None
              case VoidType =>
                issue(new BadVarTypeError(id.name, v.pos))
                None
              case t =>
                val symbol = new MemberVarSymbol(v, t, ctx.currentClass)
                ctx.declare(symbol)
                Some(Named.VarDef(TypedTypeLit(lit)(lit.typ), id)(symbol))
            }
          case m@MethodDef(mod, id, returnType, params, body) =>
            val rt = typeTypeLit(returnType)
            val retType = rt.typ
            val formalScope = new FormalScope
            val formalCtx: ScopeContext = ctx.open(formalScope)
            if (!m.isStatic) formalCtx.declare(LocalVarSymbol.thisVar(ctx.currentClass.typ, id.pos))
            val ps = params.map {
              resolveLocalVarDef(_)(formalCtx)
            }
            val funType = FunType(ps.map{ _.typeLit.typ }, retType)
            val symbol = new MethodSymbol(m, funType, formalScope, ctx.currentClass)
            ctx.declare(symbol)
            if (m.isAbstract) abstractMethods += symbol
            val block = body.map {
              resolveBlock(_)(formalCtx)
            }
            Some(Named.MethodDef(mod, id, TypedTypeLit(rt)(rt.typ), ps, block)(symbol))
        }
    }
    resolved.map(_.setPos(field.pos))
  }


  /**
    * Resolve a statement block.
    *
    * @param block statement block
    * @param ctx   scope context
    * @return resolved block
    */
  def resolveBlock(block: Block)(implicit ctx: ScopeContext): Named.Block = {
    val localScope = ctx.currentScope match {
      case s: FormalScope => s.nestedScope
      case s: LocalScope =>
        val local = new LocalScope
        s.nestedScopes += local
        local
    }
    val localCtx = ctx.open(localScope)
    val ss = block.stmts.map {
      resolveStmt(_)(localCtx)
    }
    Named.Block(ss)(localScope).setPos(block.pos)
  }

  def resolveStmt(stmt: Stmt)(implicit ctx: ScopeContext): Named.Stmt = {
    val resolved = stmt match {
      case block: Block => resolveBlock(block)
      case v: LocalVarDef => resolveLocalVarDef(v)
      case v: UntypedLocalVarDef => resolveUntypedLocalVarDef(v)
      case Assign(lhs, rhs) => Named.Assign(resolveLValue(lhs), resolveExpr(rhs))
      case ExprEval(expr) => Named.ExprEval(resolveExpr(expr))
      case Skip() => Named.Skip()
      case If(cond, trueBranch, falseBranch) =>
        Named.If(resolveExpr(cond), resolveBlock(trueBranch), falseBranch map resolveBlock)
      case While(cond, body) => Named.While(resolveExpr(cond), resolveBlock(body))
      case For(init, cond, update, body) =>
        // Since `init` and `update` may declare local variables, we must first open the local scope of `body`, and
        // then resolve `init`, `update` and statements inside `body`.
        val localScope = new LocalScope
        ctx.currentScope match {
          case s: LocalScope => s.nestedScopes += localScope
        }
        val localCtx = ctx.open(localScope)
        val i = resolveStmt(init)(localCtx)
        val u = resolveStmt(update)(localCtx)
        val ss = body.stmts.map {
          resolveStmt(_)(localCtx)
        }
        val b = Named.Block(ss)(localScope).setPos(body.pos)
        Named.For(i, resolveExpr(cond), u, b)
      case Break() => Named.Break()
      case Return(expr) => Named.Return(expr map resolveExpr)
      case Print(exprs) => Named.Print(exprs map resolveExpr)
    }
    resolved.setPos(stmt.pos)
  }

  @inline
  def resolveLocalVarDef(v: LocalVarDef)(implicit ctx: ScopeContext): Named.LocalVarDef = {
    ctx.findConflictBefore(v.name, v.pos) match {
      case Some(earlier) =>
        issue(new DeclConflictError(v.name, earlier.pos, v.pos))
        val t = typeTypeLit(v.typeLit)
        Named.LocalVarDef(Named.TypedTypeLit(t)(t.typ), v.id, v.init map resolveExpr, v.assignPos)(DummyLocalVar)
      case None =>
        val t = typeTypeLit(v.typeLit)
        val symbol = t.typ match {
          case NoType =>
            // NOTE: to avoid flushing a large number of error messages, if we know one error is caused by another,
            // then we shall not report both, but the earlier found one only. In this case, the error of the entire
            // LocalVarDef is caused by the bad typeLit, and thus we don't make further type check.
            DummyLocalVar
          case VoidType => issue(new BadVarTypeError(v.name, v.pos)); DummyLocalVar
          case t =>
            val symbol = new LocalVarSymbol(v, t)
            ctx.declare(symbol)
            symbol
        }
        Named.LocalVarDef(Named.TypedTypeLit(t)(t.typ), v.id, v.init map resolveExpr, v.assignPos)(symbol)
    }
  }

  @inline
  def resolveUntypedLocalVarDef(v: UntypedLocalVarDef)
                               (implicit ctx: ScopeContext): Named.UntypedLocalVarDef = {
    ctx.findConflictBefore(v.name, v.pos) match {
      case Some(earlier) =>
        issue(new DeclConflictError(v.name, earlier.pos, v.pos))
        Named.UntypedLocalVarDef(v.id, resolveExpr(v.init), v.assignPos)(DummyLocalVar)
      case None =>
        val symbol = new LocalVarSymbol(v.name, NoType, v.pos)
        ctx.declare(symbol)
        Named.UntypedLocalVarDef(v.id, resolveExpr(v.init), v.assignPos)(symbol)
    }
  }

  implicit val noType: NoType.type = NoType

  def resolveExpr(expr: Expr)(implicit ctx: ScopeContext): Named.Expr = {
    val resolved = expr match {
      case e: LValue => resolveLValue(e)

      case Lambda(params, e) =>
        val e1 = BlockLambda(params, Block(List(Return(Some(e))))).setPos(expr.pos)
        resolveExpr(e1)

      case BlockLambda(params, body) =>
        val formalScope = new FormalScope
        ctx.currentScope match {
          case s: LocalScope => s.nestedScopes += formalScope
        }
        val formalCtx = ctx.open(formalScope)
        val ps = params.map {
          resolveLocalVarDef(_)(formalCtx)
        }
        val b = resolveBlock(body)(formalCtx)
        val funType = FunType(ps.map(_.typeLit.typ), NoType)
        val symbol = new LambdaSymbol(expr.pos, funType, formalScope)
        ctx.declare(symbol)

        Named.LambdaExpr(ps, b, symbol)

      // others: just resolve every subexpression, if any
      case IntLit(v) => Named.IntLit(v)
      case BoolLit(v) => Named.BoolLit(v)
      case StringLit(v) => Named.StringLit(v)
      case NullLit() => Named.NullLit()
      case ReadInt() => Named.ReadInt()
      case ReadLine() => Named.ReadLine()
      case Unary(op, operand) => Named.Unary(op, resolveExpr(operand))
      case Binary(op, lhs, rhs) => Named.Binary(op, resolveExpr(lhs), resolveExpr(rhs))
      case NewArray(elemType, length) =>
        val t = typeTypeLit(elemType)
        Named.NewArray(Named.TypedTypeLit(t)(t.typ), resolveExpr(length))
      case NewClass(clazz) => Named.NewClass(clazz)
      case This() => Named.This()
      case Call(method, args) => Named.Call(resolveExpr(method), args map resolveExpr)
      case ClassCast(obj, to) => Named.ClassCast(resolveExpr(obj), to)
      case ClassTest(obj, is) => Named.ClassTest(resolveExpr(obj), is)
    }
    resolved.setPos(expr.pos)
  }

  def resolveLValue(expr: LValue)(implicit ctx: ScopeContext): Named.LValue = {
    val resolved = expr match {
      case VarSel(receiver, name) => Named.VarSel(receiver map resolveExpr, name)
      case IndexSel(array, index) => Named.IndexSel(resolveExpr(array), resolveExpr(index))
    }
    resolved.setPos(expr.pos)
  }
}