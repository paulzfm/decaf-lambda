package decaf.frontend.tree

import decaf.frontend.annot._

object NamedTree extends SyntaxTreeTmpl {
  override type TopLevelAnnot = GlobalScope
  override type MemberVarAnnot = MemberVarSymbol
  override type LocalVarAnnot = LocalVarSymbol
  override type MethodAnnot = MethodSymbol
  override type TypeLitAnnot = Type
  override type BlockAnnot = LocalScope
  override type ClassRef1 = ClassSymbol
  override type ClassAnnot = ClassSymbol

  case class LambdaExpr(params: List[LocalVarDef], body: Block, symbol: LambdaSymbol)
                       (implicit val annot: ExprAnnot) extends Expr

  case class TypedTypeLit(wrap: TypedTree.TypeLit)(implicit val annot: TypeLitAnnot) extends TypeLit

}
