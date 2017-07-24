package scala.meta.testkit

import java.io.Reader

import com.github.gumtreediff.actions.ActionGenerator

import scala.meta._
import scala.reflect.runtime.{universe => ru}
import com.github.gumtreediff.gen.Register
import com.github.gumtreediff.gen.Registry
import com.github.gumtreediff.gen.TreeGenerator
import com.github.gumtreediff.tree.TreeContext

import scala.meta.Tree
import com.github.gumtreediff.gen.Register
import com.github.gumtreediff.gen.Registry
import com.github.gumtreediff.gen.TreeGenerator
import com.github.gumtreediff.io.ActionsIoUtils
import com.github.gumtreediff.matchers.Matchers
import com.github.gumtreediff.tree.ITree
import com.github.gumtreediff.tree.TreeContext

object StructuralDiff {
  class ScalaTreeGenerator(tree: Tree) {
    val context = new TreeContext()

    private def computeContextTree(currentTree: Tree, indent: Int = 0): ITree = {
      if (indent == 0) {
        println("==============")
      }

      val typ = currentTree.productPrefix.hashCode
      val label = currentTree.productPrefix
      val typLabel = currentTree.getClass.getName

      println(s"${"\t" * indent} $typ $label $typLabel")

      val currentTreeCtx = context.createTree(typ, label, typLabel)
      currentTreeCtx.setPos(currentTree.pos.start)
      currentTreeCtx.setLength(currentTree.pos.end - currentTree.pos.start)

      val childTrees = currentTree.productIterator.toList.collect { case treeElem: Tree =>
        computeContextTree(treeElem, indent + 1)
      }

      for (childTree <- childTrees) {
        childTree.setParentAndUpdateChildren(currentTreeCtx)
      }

      currentTreeCtx
    }

    def computeContext(): Unit = {
      val r = computeContextTree(tree)
      context.setRoot(r)
    }
  }

  def diff(treeSrc: Tree, treeDst: Tree): Unit = {
    val genSrc = new ScalaTreeGenerator(treeSrc)
    val genDst = new ScalaTreeGenerator(treeDst)

    genSrc.computeContext()
    genDst.computeContext()

    val matchers = Matchers.getInstance()
    val matcher = matchers.getMatcher(genSrc.context.getRoot, genDst.context.getRoot)
    matcher.`match`()
    val g = new ActionGenerator(genSrc.context.getRoot, genDst.context.getRoot, matcher.getMappings)
    g.generate()
    val serializer = ActionsIoUtils.toText(genSrc.context, g.getActions, matcher.getMappings)
    serializer.writeTo(System.out)
  }

  def testCall(): Unit = {
    val tree1 = q"""
      class A {
        val a: Int = 1
        val b: Double = 2.0
      }
    """
    val tree2 = q"""
      class A {
        val b: Double = 2.0
        val a1: Int = 1
      }
    """
    diff(tree1, tree2)
  }
}
