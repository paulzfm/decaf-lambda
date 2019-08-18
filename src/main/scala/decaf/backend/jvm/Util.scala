package decaf.backend.jvm

import decaf.frontend.annot._
import decaf.frontend.tree.TreeNode
import org.objectweb.asm.{Label, MethodVisitor, Opcodes, Type => ASMType}

trait Util {
  val JAVA_SUPER_INTERNAL_NAME = "java/lang/Object"
  val CONSTRUCTOR_NAME = "<init>"
  val CONSTRUCTOR_DESC = "()V"

  /**
    * {{{
    *     if != 0 goto true
    *     falseBranch
    *     goto exit
    *   true:
    *     trueBranch
    *   exit:
    * }}}
    */
  def ifThenElse(trueBranch: => Unit, falseBranch: => Unit)(implicit mv: MethodVisitor): Unit = {
    val trueLabel = new Label
    val exitLabel = new Label

    mv.visitJumpInsn(Opcodes.IFNE, trueLabel)
    falseBranch
    mv.visitJumpInsn(Opcodes.GOTO, exitLabel)
    mv.visitLabel(trueLabel)
    trueBranch
    mv.visitLabel(exitLabel)
  }

  /**
    * {{{
    *   enter:
    *     cond
    *     if = 0 goto exit
    *     body
    *     goto enter
    *   exit:
    * }}}
    *
    * @param body
    * @param exit
    * @param mv
    */
  def loop(cond: => Unit, exit: Label)(body: => Unit)(implicit mv: MethodVisitor): Unit = {
    val enter = new Label

    mv.visitLabel(enter)
    cond
    mv.visitJumpInsn(Opcodes.IFEQ, exit)
    body
    mv.visitJumpInsn(Opcodes.GOTO, enter)
    mv.visitLabel(exit)
  }

  def printing(arg: => Unit, typ: Type)(implicit mv: MethodVisitor): Unit = {
    mv.visitFieldInsn(Opcodes.GETSTATIC, "java/lang/System", "out", "Ljava/io/PrintStream;")
    arg
    val descriptor = typ match {
      case IntType => "(I)V"
      case BoolType => "(I)V" // TODO: print "true" or "false"
      case StringType => "(Ljava/lang/String;)V"
    }
    mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/io/PrintStream", "print", descriptor,
      false)
  }

  def toASMType(typ: Type): ASMType = typ match {
    case IntType => ASMType.INT_TYPE
    case BoolType => ASMType.BOOLEAN_TYPE
    case StringType => ASMType.getType(classOf[java.lang.String])
    case VoidType => ASMType.VOID_TYPE
    case ClassType(name, _) => ASMType.getObjectType(name)
    case ArrayType(elemType) => ASMType.getType('[' + toASMType(elemType).getDescriptor)
    case FunType(params, ret) => ASMType.getMethodType(toASMType(ret), params.map(toASMType): _*)
  }

  /**
    * Get the ASM internal name of a class symbol.
    *
    * @param clazz the class symbol
    * @return its internal name
    */
  def internalName(clazz: ClassSymbol): String = toASMType(clazz.typ).getInternalName

  /**
    * Get the JVM (type) descriptor of a field symbol.
    * See https://docs.oracle.com/javase/specs/jvms/se7/html/jvms-4.html#jvms-4.3 for descriptor syntax.
    *
    * @param field the field symbol, i.e. member var/method
    * @return its descriptor
    */
  def descriptor(field: FieldSymbol): String = toASMType(field.typ).getDescriptor

  val MAIN_DESCRIPTOR: String = "([Ljava/lang/String;)V"

  def loadDefaultValue(typ: Type)(implicit mv: MethodVisitor): Any = typ match {
    case IntType | BoolType => mv.visitInsn(Opcodes.ICONST_0)
    case _ => mv.visitInsn(Opcodes.ACONST_NULL)
  }

  def loadOp(typ: Type): Int = typ match {
    case IntType | BoolType => Opcodes.ILOAD
    case _ => Opcodes.ALOAD
  }

  def storeOp(typ: Type): Int = typ match {
    case IntType | BoolType => Opcodes.ISTORE
    case _ => Opcodes.ASTORE
  }

  def returnOp(typ: Type): Int = typ match {
    case IntType | BoolType => Opcodes.IRETURN
    case _ => Opcodes.ARETURN
  }

  def arrayTypeCode(elemType: JNative): Int = elemType match {
    case IntType => Opcodes.T_INT
    case BoolType => Opcodes.T_BOOLEAN
  }

  def arrayLoadOp(elemType: Type): Int = elemType match {
    case IntType => Opcodes.IALOAD
    case BoolType => Opcodes.BALOAD
    case _ => Opcodes.AALOAD
  }

  def arrayStoreOp(elemType: Type): Int = elemType match {
    case IntType => Opcodes.IASTORE
    case BoolType => Opcodes.BASTORE
    case _ => Opcodes.AASTORE
  }

  def unaryOp(op: TreeNode.Op): Int = op match {
    case TreeNode.NEG => Opcodes.INEG
    case TreeNode.NOT => Opcodes.IXOR
  }

  def arithOp(op: TreeNode.ArithOp): Int = op match {
    case TreeNode.ADD => Opcodes.IADD
    case TreeNode.SUB => Opcodes.ISUB
    case TreeNode.MUL => Opcodes.IMUL
    case TreeNode.DIV => Opcodes.IDIV
    case TreeNode.MOD => Opcodes.IREM
  }

  /**
    * Emit bytecode for comparing two values `left` and `right` (already on stack).
    * Procedure:
    * {{{
    *     if (left ? right) goto true
    *     push 0
    *     goto exit
    *   true:
    *     push 1
    *   exit:
    * }}}
    *
    * For <, <=, >, >=, the two values must both have type int.
    * However, for == and !=, three cases need be handled separately:
    * - Values are both integers or booleans: compare their actual value by int instructions.
    * - Values are both strings: compare their actual value by invoking ???. // TODO
    * - Values are both arrays/objects: compare their address by reference instructions.
    */
  def compare(op: TreeNode.EqOrCmpOp, typ: Type)(implicit mv: MethodVisitor): Unit = {
    val trueLabel = new Label
    val exitLabel = new Label
    val opCode = op match {
      case TreeNode.EQ =>
        if (typ === IntType) Opcodes.IF_ICMPEQ else Opcodes.IF_ACMPEQ
      case TreeNode.NE =>
        if (typ === IntType) Opcodes.IF_ICMPNE else Opcodes.IF_ACMPNE
      case TreeNode.LE =>
        assert(typ === IntType)
        Opcodes.IF_ICMPLE
      case TreeNode.LT =>
        assert(typ === IntType)
        Opcodes.IF_ICMPLT
      case TreeNode.GE =>
        assert(typ === IntType)
        Opcodes.IF_ICMPGE
      case TreeNode.GT =>
        assert(typ === IntType)
        Opcodes.IF_ICMPGT
    }

    mv.visitJumpInsn(opCode, trueLabel)
    mv.visitInsn(Opcodes.ICONST_0)
    mv.visitJumpInsn(Opcodes.GOTO, exitLabel)
    mv.visitLabel(trueLabel)
    mv.visitInsn(Opcodes.ICONST_1)
    mv.visitLabel(exitLabel)
  }
}