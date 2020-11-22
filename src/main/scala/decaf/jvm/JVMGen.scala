package decaf.jvm

import decaf.driver.{Config, Phase}
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.annot.TypeImplicit._
import decaf.frontend.annot._
import decaf.frontend.tree.TreeNode.{ArithOp, EqOrCmpOp}
import decaf.frontend.tree.TypedTree._
import decaf.frontend.tree.{TreeNode, TypedTree}
import decaf.lowlevel.StringUtils
import org.objectweb.asm.{Type => _, _}

import scala.collection.mutable

class JVMGen(implicit config: Config) extends Phase[Tree, List[JVMClass]]("jvm", config) with Util {

  /**
    * Transformer entry.
    *
    * @param input a typed abstract syntax tree
    * @return a possibly collection of JVM classes
    */
  override def transform(input: Tree): List[JVMClass] =
    input.classes.map(emitClass) ++ neededInterfaces.map(emitInterface)

  /**
    * After generating JVM classes, dump them to binary files.
    *
    * @param classes JVM classes
    */
  override def onSucceed(classes: List[JVMClass]): Unit = {
    classes.foreach {
      _.writeFile(config.dstDir)
    }
  }

  /**
    * Generate bytecode for a decaf class.
    *
    * @param clazz the class
    * @return the wrapped class file
    */
  def emitClass(clazz: ClassDef): JVMClass = {
    implicit val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS)

    // As said in https://docs.oracle.com/javase/specs/jvms/se9/html/jvms-4.html#jvms-4.1-200-E.1:
    //   In Java SE 8 and above, the Java Virtual Machine considers the ACC_SUPER flag to be set in every class file,
    //   regardless of the actual value of the flag in the class file and the version of the class file.
    // Thus, we always set on ACC_SUPER flag and let a non-inherited decaf class extend java.lang.Object.
    val access = Opcodes.ACC_PUBLIC + Opcodes.ACC_SUPER + (if (clazz.symbol.isAbstract) Opcodes.ACC_ABSTRACT else 0)
    val superClass = clazz.parent.map(internalName).getOrElse(JAVA_SUPER_INTERNAL_NAME)
    cw.visit(Opcodes.V1_8, access, clazz.name, null, superClass, null)

    // First add the default constructor:
    val mv = cw.visitMethod(Opcodes.ACC_PUBLIC, CONSTRUCTOR_NAME, CONSTRUCTOR_DESC, null, null)
    mv.visitCode()
    mv.visitVarInsn(Opcodes.ALOAD, 0)
    mv.visitMethodInsn(Opcodes.INVOKESPECIAL, superClass, CONSTRUCTOR_NAME, CONSTRUCTOR_DESC, false) // call super
    mv.visitInsn(Opcodes.RETURN)
    mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    mv.visitEnd()

    // Then generate every user-defined member:
    clazz.fields.foreach {
      case field: VarDef =>
        cw.visitField(Opcodes.ACC_PROTECTED, field.name, descriptor(field.symbol), null, null)
      case method: MethodDef => emitMethod(method)
    }
    cw.visitEnd()

    JVMClass(clazz.name, cw.toByteArray)
  }

  /**
    * Emit bytecode for a method. Code will be appended to the class writer.
    *
    * @param method the method
    * @param cw     the current class writer
    */
  def emitMethod(method: MethodDef)(implicit cw: ClassWriter): Unit = {
    // Methods are always public, but they can be static or not.
    val access = Opcodes.ACC_PUBLIC + (if (method.isStatic) Opcodes.ACC_STATIC else 0) +
      (if (method.symbol.isAbstract) Opcodes.ACC_ABSTRACT else 0)
    val desc = if (method.symbol.isMain) MAIN_DESCRIPTOR else descriptor(method.symbol)
    implicit val mv = cw.visitMethod(access, method.name, desc, null, null)

    // Allocate indexes (in JVM local variable array) for every argument. For member methods, index 0 is reserved for
    // `this`.
    implicit val ctx = new Context(method.symbol.owner)
    if (!method.isStatic) ctx.declare(CThis)
    method.params.foreach { p => ctx.declare(CLocal(p.symbol)) }

    // Visit method body and emit bytecode.
    mv.visitCode()
    implicit val loopExits: List[Label] = Nil
    method.body.foreach(emitStmt)
    appendReturnIfNecessary(method)
    mv.visitMaxs(-1, -1) // again, random arguments
    mv.visitEnd()
  }

  /**
    * JVM requires every method to have explicit RETURN instruction for every execution path. For methods that actually
    * returns a value, our compiler frontend should ensure this. However, a decaf program may omit redundant return
    * statements in a method that returns nothing (or, returns void). In these conditions, we shall insert a RETURN
    * instruction at the end, if not any.
    *
    * @param methodDef the method
    * @param mv        the current method visitor
    */
  def appendReturnIfNecessary(methodDef: MethodDef)(implicit mv: MethodVisitor): Unit = {
    if (!methodDef.returnType.typ.isVoidType) return
    if (methodDef.body.isEmpty) return

    val stmts = methodDef.body.get.stmts
    if (stmts.isEmpty || !stmts.last.isInstanceOf[Return]) mv.visitInsn(Opcodes.RETURN)
  }

  private val neededInterfaces = mutable.HashSet[FunctionalInterface]()

  type LocalVars = mutable.HashMap[CVar, Int]

  private class Context(val clazz: ClassSymbol) {

    val index: LocalVars = new LocalVars

    def declare(v: CVar): Int = {
      index(v) = next
      val retIndex = next
      next += 1
      retIndex
    }

    private var next: Int = 0
  }

  /**
    * Emit bytecode for a statement. Code will be appended to the method writer.
    *
    * @param stmt      the statement
    * @param mv        the current method writers
    * @param loopExits exit labels for the entered loops so far, arranged from the inner most to the outer most
    * @param ctx       the current context
    */
  def emitStmt(stmt: Stmt)(implicit mv: MethodVisitor, cw: ClassWriter, loopExits: List[Label], ctx: Context): Unit = stmt match {
    case Block(stmts) => stmts foreach emitStmt

    case v: LocalVarDef =>
      // JVM will complain if a local variable is read but not initialized yet. It also seems that when the local
      // variable is firstly initialized in a more inner scope rather than the outer most local scope, JVM reports
      // an error. To avoid these, let's simply initialize every user-defined local variable right now, in case
      // the user didn't.
      val index = ctx.declare(CLocal(v.symbol))
      v.init match {
        case Some(expr) => emitExpr(expr)
        case None => loadDefaultValue(v.symbol.typ)
      }
      mv.visitVarInsn(storeOp(v.symbol.typ), index)

    case v: UntypedLocalVarDef =>
      val index = ctx.declare(CLocal(v.symbol))
      emitExpr(v.init)
      mv.visitVarInsn(storeOp(v.symbol.typ), index)

    case Assign(LocalVar(v), rhs) =>
      emitExpr(rhs)
      mv.visitVarInsn(storeOp(v.typ), ctx.index(CLocal(v)))
    case Assign(MemberVar(receiver, v), rhs) =>
      emitExpr(receiver)
      emitExpr(rhs)
      mv.visitFieldInsn(Opcodes.PUTFIELD, internalName(v.owner), v.name, descriptor(v))
    case Assign(IndexSel(array, index), rhs) =>
      emitExpr(array)
      emitExpr(index)
      emitExpr(rhs)
      val elemType = array.typ.asInstanceOf[ArrayType].elemType
      mv.visitInsn(arrayStoreOp(elemType))

    case ExprEval(expr) => emitExpr(expr)
    case Skip() => // nop

    case If(cond, trueBranch, falseBranch) =>
      emitExpr(cond)
      ifThenElse(emitStmt(trueBranch), emitStmt(falseBranch.getOrElse(TypedTree.Block()(null))))
    case While(cond, body) =>
      val exit = new Label
      loop(emitExpr(cond), exit) {
        emitStmt(body)(mv, cw, exit :: loopExits, ctx)
      }
    case For(init, cond, update, body) =>
      val exit = new Label
      emitStmt(init)
      loop(emitExpr(cond), exit) {
        emitStmt(body)(mv, cw, exit :: loopExits, ctx);
        emitStmt(update)
      }
    case Break() => mv.visitJumpInsn(Opcodes.GOTO, loopExits.head)
    case Return(None) => mv.visitInsn(Opcodes.RETURN)
    case Return(Some(expr)) =>
      emitExpr(expr)
      //      if (ctx.inLambda) {
      //        emitBox(expr.typ)
      //        mv.visitInsn(Opcodes.ARETURN)
      //      } else
      mv.visitInsn(returnOp(expr.typ))
    case Print(exprs) =>
      exprs.foreach { expr => printing(emitExpr(expr), expr.typ) }
  }

  /**
    * Emit bytecode for an expression. Code will be appended to the method writer.
    *
    * @param expr the expression
    * @param mv   the current method writer
    * @param ctx  the current context
    */
  def emitExpr(expr: Expr)(implicit mv: MethodVisitor, cw: ClassWriter, ctx: Context): Unit = expr match {
    case IntLit(v) => mv.visitLdcInsn(v)
    case BoolLit(v) => mv.visitLdcInsn(v)
    case StringLit(str) => mv.visitLdcInsn(StringUtils.unquote(str))
    case NullLit() => mv.visitInsn(Opcodes.ACONST_NULL)

    // Prebuilt functions
    case ReadInt() => callScanner("nextInt")
    case ReadLine() => callScanner("nextLine")

    // Unary expressions
    case Unary(op, expr) =>
      emitExpr(expr)
      op match {
        case TreeNode.NEG => mv.visitInsn(Opcodes.INEG)
        case TreeNode.NOT =>
          // NOTE: !b = b xor 1
          mv.visitInsn(Opcodes.ICONST_1)
          mv.visitInsn(Opcodes.IXOR)
      }

    // Binary expressions
    case Binary(op, lhs, rhs) =>
      emitExpr(lhs)
      emitExpr(rhs)
      op match {
        case op: ArithOp => mv.visitInsn(arithOp(op))
        // Warning: JVM doesn't support operations directly on booleans. Thus, we always use integer instuctions on
        // them, i.e. IAND and IOR. Remember that LAND and LOR are for _long_ integers, not _logical_ and/or!
        case TreeNode.AND => mv.visitInsn(Opcodes.IAND)
        case TreeNode.OR => mv.visitInsn(Opcodes.IOR)
        case op: EqOrCmpOp => compare(op, lhs.typ)
      }

    // Local variables: they must be already assigned to an index
    case LocalVar(v) => mv.visitVarInsn(loadOp(v.typ), ctx.index(CLocal(v)))

    // Array related
    case NewArray(elemType, len) =>
      emitExpr(len)
      elemType.typ match {
        case t: JNativeType => mv.visitIntInsn(Opcodes.NEWARRAY, arrayTypeCode(t))
        case t => mv.visitTypeInsn(Opcodes.ANEWARRAY, toASMType(t).getInternalName)
      }
    case IndexSel(array, index) =>
      emitExpr(array)
      emitExpr(index)
      val elemType = array.typ.asInstanceOf[ArrayType].elemType
      mv.visitInsn(arrayLoadOp(elemType))
    case ArrayLen(array) =>
      emitExpr(array)
      mv.visitInsn(Opcodes.ARRAYLENGTH)
    case ArrayLenMethod(array) =>
      emitExpr(array)

      val interface = interfaceOf(FunType(Nil, IntType))
      neededInterfaces += interface
      val boxedType = toASMMethodType(toBoxType(IntType), Nil)

      val capturedTypes = List(toASMType(array.typ))
      val implDesc = toASMMethodType(toASMType(IntType), capturedTypes).getDescriptor
      val name = "array$len" + expr.pos

      // invoke dynamic: push the function object to stack
      val bootstrapMethodHandle = new Handle(Opcodes.H_INVOKESTATIC,
        LAMBDA_FACTORY_INTERNAL_NAME, META_FACTORY, META_FACTORY_DESC, false)
      val implMethodHandle = new Handle(Opcodes.H_INVOKESTATIC, ctx.clazz.name, name, implDesc, false)
      mv.visitInvokeDynamicInsn("apply", toASMMethodType(interface.classType, capturedTypes).getDescriptor,
        bootstrapMethodHandle, interface.applyType, implMethodHandle, boxedType)

      { // generate implementation method
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC + Opcodes.ACC_SYNTHETIC + Opcodes.ACC_FINAL,
          name, implDesc, null, null)

        mv.visitCode()
        mv.visitVarInsn(Opcodes.ALOAD, 0)
        mv.visitInsn(Opcodes.ARRAYLENGTH)
        mv.visitInsn(Opcodes.IRETURN)
        mv.visitMaxs(-1, -1)
        mv.visitEnd()
      }

    // Class related
    case NewClass(clazz) =>
      mv.visitTypeInsn(Opcodes.NEW, internalName(clazz))
      mv.visitInsn(Opcodes.DUP)
      mv.visitMethodInsn(Opcodes.INVOKESPECIAL, internalName(clazz), CONSTRUCTOR_NAME, CONSTRUCTOR_DESC, false)
    case This() => mv.visitVarInsn(Opcodes.ALOAD, ctx.index(CThis))
    case MemberVar(receiver, v) =>
      emitExpr(receiver)
      mv.visitFieldInsn(Opcodes.GETFIELD, internalName(v.owner), v.name, descriptor(v))

    case StaticMethod(method) =>
      val interface = interfaceOf(method.typ)
      neededInterfaces += interface
      val boxedType = toASMMethodType(toBoxType(method.typ.ret), method.typ.args.map(toBoxType))

      // invoke dynamic: push the function object to stack
      val bootstrapMethodHandle = new Handle(Opcodes.H_INVOKESTATIC,
        LAMBDA_FACTORY_INTERNAL_NAME, META_FACTORY, META_FACTORY_DESC, false)
      val implMethodHandle = new Handle(Opcodes.H_INVOKESTATIC, method.owner.name, method.name, descriptor(method), false)
      mv.visitInvokeDynamicInsn("apply", toASMMethodType(interface.classType, Nil).getDescriptor,
        bootstrapMethodHandle, interface.applyType, implMethodHandle, boxedType)

    case MemberMethod(receiver, method) =>
      emitExpr(receiver)
      val receiverType = toASMType(receiver.typ)
      val interface = interfaceOf(method.typ)
      neededInterfaces += interface
      val boxedType = toASMMethodType(toBoxType(method.typ.ret), method.typ.args.map(toBoxType))

      // invoke dynamic: push the function object to stack
      val bootstrapMethodHandle = new Handle(Opcodes.H_INVOKESTATIC,
        LAMBDA_FACTORY_INTERNAL_NAME, META_FACTORY, META_FACTORY_DESC, false)
      val implMethodHandle = new Handle(Opcodes.H_INVOKEVIRTUAL, method.owner.name, method.name, descriptor(method), false)
      mv.visitInvokeDynamicInsn("apply", toASMMethodType(interface.classType, List(receiverType)).getDescriptor,
        bootstrapMethodHandle, interface.applyType, implMethodHandle, boxedType)

    case StaticCall(m, args) =>
      args foreach emitExpr
      mv.visitMethodInsn(Opcodes.INVOKESTATIC, internalName(m.owner), m.name, descriptor(m), false)
    case MemberCall(receiver, m, args) =>
      (receiver :: args) foreach emitExpr
      mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, internalName(m.owner), m.name, descriptor(m), false)

    case ClassTest(obj, clazz) =>
      emitExpr(obj)
      mv.visitTypeInsn(Opcodes.INSTANCEOF, internalName(clazz))
    case ClassCast(obj, clazz) =>
      emitExpr(obj)
      mv.visitTypeInsn(Opcodes.CHECKCAST, internalName(clazz))

    // Lambda related
    case LambdaExpr(params, body, symbol, capturedSet) =>
      // load captured values as arguments
      capturedSet.foreach { v =>
        mv.visitVarInsn(v match {
          case CThis => Opcodes.ALOAD
          case CLocal(s) => loadOp(s.typ)
        }, ctx.index(v))
      }

      // functional interface of the lambda
      val interface = interfaceOf(symbol.typ)
      neededInterfaces += interface
      val boxedType = toASMMethodType(toBoxType(symbol.typ.ret), symbol.typ.args.map(toBoxType))

      // Params of the actual implementation: captured variables, and lambda's params.
      val capturedTypes = capturedSet.toList.map {
        case CThis => toASMType(ctx.clazz.typ)
        case CLocal(s) => toASMType(s.typ)
      }
      val implDesc = toASMMethodType(toASMType(symbol.typ.ret), capturedTypes ++ symbol.typ.args.map(toASMType)).getDescriptor

      // invoke dynamic: push the function object to stack
      val bootstrapMethodHandle = new Handle(Opcodes.H_INVOKESTATIC,
        LAMBDA_FACTORY_INTERNAL_NAME, META_FACTORY, META_FACTORY_DESC, false)
      val implMethodHandle = new Handle(Opcodes.H_INVOKESTATIC, ctx.clazz.name, symbol.name, implDesc, false)
      mv.visitInvokeDynamicInsn("apply", toASMMethodType(interface.classType, capturedTypes).getDescriptor,
        bootstrapMethodHandle, interface.applyType, implMethodHandle, boxedType)

      { // generate implementation method
        val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_STATIC + Opcodes.ACC_SYNTHETIC + Opcodes.ACC_FINAL,
          symbol.name, implDesc, null, null)

        // setup context
        val lCtx = new Context(ctx.clazz)
        capturedSet.toList.foreach(lCtx.declare)
        params.foreach { p => lCtx.declare(CLocal(p.symbol)) }

        mv.visitCode()
        emitStmt(body)(mv, cw, Nil, lCtx)
        mv.visitInsn(Opcodes.RETURN)
        mv.visitMaxs(-1, -1)
        mv.visitEnd()
      }

    case LambdaCall(func, args) =>
      emitExpr(func)
      args.foreach { a =>
        emitExpr(a)
        emitBox(a.typ)
      }
      func.typ match {
        case t: FunType =>
          val interface = interfaceOf(t)
          neededInterfaces += interface
          mv.visitMethodInsn(Opcodes.INVOKEINTERFACE,
            interface.toString, "apply", interface.applyType.getDescriptor, true)
          if (!t.ret.isVoidType) {
            mv.visitTypeInsn(Opcodes.CHECKCAST, toBoxType(t.ret).getInternalName)
            emitUnbox(t.ret)
          }
      }
  }

  def emitBox(t: Type)(implicit mv: MethodVisitor): Unit = t match {
    case IntType => mv.visitMethodInsn(Opcodes.INVOKESTATIC,
      JAVA_INTEGER_INTERNAL_NAME, "valueOf", s"(I)L$JAVA_INTEGER_INTERNAL_NAME;", false)
    case BoolType => mv.visitMethodInsn(Opcodes.INVOKESTATIC,
      JAVA_BOOLEAN_INTERNAL_NAME, "valueOf", s"(Z)L$JAVA_BOOLEAN_INTERNAL_NAME;", false)
    case _ => // no conversion
  }

  def emitUnbox(t: Type)(implicit mv: MethodVisitor): Unit = t match {
    case IntType => mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL,
      JAVA_INTEGER_INTERNAL_NAME, "intValue", "()I", false)
    case BoolType => mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL,
      JAVA_BOOLEAN_INTERNAL_NAME, "booleanValue", "()Z", false)
    case _ => // no conversion
  }

  def emitInterface(fi: FunctionalInterface): JVMClass = {
    val cw = new ClassWriter(ClassWriter.COMPUTE_FRAMES + ClassWriter.COMPUTE_MAXS)
    val access = Opcodes.ACC_PUBLIC + Opcodes.ACC_ABSTRACT + Opcodes.ACC_INTERFACE
    cw.visit(Opcodes.V1_8, access, fi.toString, null, JAVA_SUPER_INTERNAL_NAME, null)
    cw.visitAnnotation("Ljava/lang/FunctionalInterface;", true)

    val mv = cw.visitMethod(Opcodes.ACC_PUBLIC + Opcodes.ACC_ABSTRACT + Opcodes.ACC_SYNTHETIC,
      "apply", fi.applyType.getDescriptor, null, null)
    mv.visitCode()
    mv.visitMaxs(-1, -1) // pass in random numbers, as COMPUTE_MAXS flag enables the computation
    mv.visitEnd()

    cw.visitEnd()
    JVMClass(fi.toString, cw.toByteArray)
  }

}
