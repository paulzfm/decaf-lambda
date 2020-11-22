package decaf.frontend.tac

import java.io.PrintWriter
import java.util

import decaf.driver.{Config, Phase}
import decaf.frontend.annot.LambdaSymbol
import decaf.frontend.annot.ScopeImplicit._
import decaf.frontend.annot.SymbolImplicit._
import decaf.frontend.tree.TypedTree._
import decaf.lowlevel.tac.{ClassInfo, ProgramWriter, Simulator, TacProg}
import decaf.util.Conversions._

/**
  * The tacgen phase: translate a typed abstract syntax tree to TAC IR.
  */
class TacGen(implicit config: Config) extends Phase[Tree, TacProg]("tacgen", config) with TacEmitter {

  /**
    * Transformer entry.
    *
    * @param tree a typed abstract syntax tree
    * @return TAC program
    */
  override def transform(tree: Tree): TacProg = {
    // Create class info.
    val info = tree.classes.map(_.symbol.getInfo)

    // a special class to store all lambda functions
    val set = new util.TreeSet[String]
    for {
      clazz <- tree.classes
      method <- clazz.methods
      if !method.isAbstract
    } {
      set.add(nameOf(method.symbol)) // collect class method
      method.body.get.scope.traverse {
        case f: LambdaSymbol => set.add(nameOf(f)) // collect lambda
        case _ => // do nothing
      }
    }
    set.add(nameOfArrayLen)

    val emptySet = new java.util.HashSet[String]
    val funClass = new ClassInfo(FUN_CLASS, None, emptySet, set, emptySet, false)
    val pw = new ProgramWriter(info :+ funClass)

    // Step 1: create virtual tables.
    pw.visitVTables()

    // Step 2: emit tac instructions for every concrete method.
    for {
      clazz <- tree.classes
      method <- clazz.methods
      if !method.isAbstract
      body = method.body.get
    } {
      if (method.symbol.isMain) {
        val fv = pw.visitMainMethod
        emitStmt(body)(new Context, Nil, fv, pw)
        fv.visitEnd()
      } else {
        val base = if (method.isStatic) 0 else 1 // arg 0 is reserved for `this`, when this is a member method
        val fv = pw.visitFunc(clazz.name, method.name, base + method.params.length)
        val ctx = new Context
        if (!method.isStatic) ctx.vars(CThis) = fv.getArgTemp(0)
        method.params.zipWithIndex.foreach {
          case (p, i) => ctx.vars(CLocal(p.symbol)) = fv.getArgTemp(base + i)
        }
        emitStmt(body)(ctx, Nil, fv, pw)
        fv.visitEnd()
      }

      // for every method, generate its lambda form
      val m = method.symbol
      if (m.isStatic) {
        val fv = pw.visitFunc(FUN_CLASS, nameOf(m), 1 + m.arity)
        // remember we needn't read any captured vars, but temp 0 is still reserved
        val args = for (i <- 0 until m.arity) yield fv.getArgTemp(i + 1)
        if (m.returnType.isVoidType) fv.visitStaticCall(m.owner.name, m.name, args.toList)
        else {
          val rt = fv.visitStaticCall(m.owner.name, m.name, args.toList, true)
          fv.visitReturn(rt)
        }
        fv.visitEnd()
      } else {
        val fv = pw.visitFunc(FUN_CLASS, nameOf(m), 1 + m.arity)
        val self = fv.visitLoadFrom(fv.getArgTemp(0))
        val args = for (i <- 0 until m.arity) yield fv.getArgTemp(i + 1)
        if (m.returnType.isVoidType) fv.visitMemberCall(self, m.owner.name, m.name, args.toList)
        else {
          val rt = fv.visitMemberCall(self, m.owner.name, m.name, args.toList, true)
          fv.visitReturn(rt)
        }
        fv.visitEnd()
      }
    }

    // Step 3: emit empty implementation for every abstract method, to make simulator happy!
    for {
      clazz <- tree.classes
      method <- clazz.methods
      if method.isAbstract
    } {
      val fv = pw.visitFunc(clazz.name, method.name, 0)
      fv.visitEnd()
    }

    // Step 4: don't forget our little array len method
    val fv = pw.visitFunc(FUN_CLASS, nameOfArrayLen, 1)
    val at = fv.visitLoadFrom(fv.getArgTemp(0))
    val len = fv.visitLoadFrom(at, -4)
    fv.visitReturn(len)
    fv.visitEnd()

    pw.visitEnd()
  }

  /**
    * After generating TAC program, dump it and start the simulator if necessary.
    *
    * @param program TAC program
    */
  override def onSucceed(program: TacProg): Unit = {
    if (config.target.equals(Config.Target.PA3)) { // First dump the tac program to file,
      val path = config.dstDir / config.sourceBaseName + ".tac"
      val printer = new PrintWriter(path)
      program.printTo(printer)
      printer.close()

      // and then execute it using our simulator.
      val simulator = new Simulator(System.in, config.output)
      simulator.execute(program)
    }
  }
}
