package decaf.frontend.tree

import decaf.frontend.annot.Annot
import decaf.frontend.tree.TreeNode.Id

/**
  * A syntax tree, with no annotations.
  *
  * @see [[TreeTmpl]]
  */
trait SyntaxTreeTmpl extends TreeTmpl {

  /**
    * Dummy annotation.
    *
    * Here we made a dummy annotation to act as a placeholder for the `annot` field, and we made it implicit.
    * In this way, we can simply write:
    * {{{ VarSel(r, v) }}}
    * to create a `VarSel` node, because the Scala compiler will expand it to:
    * {{{ VarSel(r, v)(NoAnnot) }}}
    */
  implicit object NoAnnot extends Annot {

    override def toString: String = ""
  }

  type No = NoAnnot.type

  type StmtAnnot = No
  type ExprAnnot = No

  type ClassRef = Id

  case class VarSel(receiver: Option[Expr], id: Id)(implicit val annot: ExprAnnot) extends LValue

  case class Call(method: Expr, args: List[Expr])(implicit val annot: ExprAnnot) extends Expr
}

object SyntaxTree extends SyntaxTreeTmpl {
  type TopLevelAnnot = No
  type ClassAnnot = No
  type MemberVarAnnot = No
  type LocalVarAnnot = No
  type MethodAnnot = No
  type TypeLitAnnot = No
  type BlockAnnot = No

  type ClassRef1 = Id

  case class Lambda(args: List[LocalVarDef], body: Expr)(implicit val annot: ExprAnnot) extends Expr

  case class BlockLambda(args: List[LocalVarDef], body: Block)(implicit val annot: ExprAnnot) extends Expr {
    override def productPrefix: String = "Lambda"
  }
}