package decaf.printing

import decaf.annot.Annotated
import decaf.parsing.Util.quote
import decaf.tree.TreeNode.{Id, Node}

object PrettyTree {

  case class PrettyConfig(showPos: Boolean = false, showAnnot: Boolean = false)

  def prettyElement(element: Any)(implicit printer: IndentPrinter, config: PrettyConfig): Unit = element match {
    case e: Node with Annotated[_] => pretty(e)
    case Id(name) => printer.writeln(name)
    case Some(e) => prettyElement(e)
    case None => printer.writeln("<none>")
    case es: List[_] =>
      printer.writeln("list")
      printer.withIndent {
        if (es.isEmpty) printer.writeln("<empty>")
        else es.foreach(prettyElement)
      }
    case e: String => printer.writeln(quote(e))
    case e => printer.writeln(e.toString)
  }

  def pretty(node: Node with Annotated[_])(implicit printer: IndentPrinter, config: PrettyConfig): Unit = {
    val annotStr = if (config.showAnnot) s" { ${ node.annot } }" else ""
    val posStr = if (config.showPos) s" @ (${ node.pos.line },${ node.pos.column })"

    printer.writeln(node.productPrefix + annotStr + posStr)
    printer.withIndent {
      node.productIterator.foreach(prettyElement)
    }
  }
}