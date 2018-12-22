package scala.meta.internal.semanticdb.javac.semantics

import com.github.{javaparser => jp}
import javax.tools.JavaFileObject
import scala.collection.mutable

trait Semantics extends Elements with TypeMirrors with Nodes {
  type SymbolTable = mutable.Map[String, Option[jp.ast.Node]]
  def emptySymbolTable: SymbolTable =
    mutable.Map.empty[String, Option[jp.ast.Node]]

  val sourceFile: JavaFileObject

  val symbolTable: SymbolTable = {
    val content = sourceFile.getCharContent(true).toString
    val cu = jp.JavaParser.parse(content)
    val stg = new SymbolTableGenerator()
    val symbolTable = emptySymbolTable
    stg.visit(cu, symbolTable)
    symbolTable
  }
}
