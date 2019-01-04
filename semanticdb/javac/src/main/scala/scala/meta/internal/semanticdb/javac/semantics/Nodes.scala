package scala.meta.internal.semanticdb.javac.semantics

import com.github.{javaparser => jp}
import scala.annotation.switch
import scala.collection.JavaConverters._
import scala.collection.mutable
import scala.compat.java8.OptionConverters._
import scala.meta.internal.semanticdb.Scala.{Descriptor => d, _}
import scala.meta.internal.{semanticdb => s}
import scala.meta.internal.semanticdb.SymbolInformation.{Kind => k}
import scala.meta.internal.semanticdb.SymbolInformation.{Property => p}

trait Nodes { semantics: Semantics =>

  implicit class NodeOps(node: jp.ast.Node) {
    def owner: String = {
      node.getParentNode.asScala match {
        case Some(parent) =>
          parent match {
            case elem: jp.ast.CompilationUnit =>
              elem.getPackageDeclaration.asScala.map { _.sym }.getOrElse("")
            case elem @ (
                  _: jp.ast.body.TypeDeclaration[_] | _: jp.ast.body.CallableDeclaration[_] |
                  _: jp.ast.PackageDeclaration
                ) =>
              elem.sym
            case _ =>
              parent.owner
          }
        case _ =>
          throw new RuntimeException("Unexpected kind of node. Please, submit the issue")
      }
    }

    def symbolName: String = node match {
      case _: jp.ast.body.ConstructorDeclaration =>
        "<init>"
      case elem: jp.ast.nodeTypes.NodeWithSimpleName[_] =>
        elem.getNameAsString
      case _ =>
        throw new RuntimeException("Unexpected kind of node. Please, submit the issue")
    }

    def sym: String = node match {
      case elem: jp.ast.CompilationUnit =>
        elem.getPackageDeclaration.asScala.map { _.sym }.getOrElse("")
      case elem: jp.ast.PackageDeclaration =>
        val qualName = elem.getName.asString
        if (qualName == "") {
          Symbols.EmptyPackage
        } else {
          qualName.replace('.', '/') + "/"
        }
      case _: jp.ast.body.TypeDeclaration[_] =>
        Symbols.Global(owner, d.Type(symbolName))
      case _: jp.ast.stmt.LocalClassDeclarationStmt =>
        ""
      case _: jp.ast.body.Parameter =>
        Symbols.Global(owner, d.Parameter(symbolName))
      case elem: jp.ast.body.CallableDeclaration[_] =>
        elem.getParentNode.asScala match {
          case Some(owner: jp.ast.body.TypeDeclaration[_]) =>
            val disambig = {
              val siblingMethods: mutable.Buffer[jp.ast.body.CallableDeclaration[_]] = {
                if (elem.isConstructorDeclaration) {
                  val siblingMethods = owner
                    .asInstanceOf[jp.ast.nodeTypes.NodeWithConstructors[_]]
                    .getConstructors
                    .asScala
                  siblingMethods.map { _.asCallableDeclaration }
                } else {
                  val siblingMethods = owner.getMethodsByName(symbolName).asScala
                  val (instance, static) = siblingMethods.partition { method =>
                    !method.getModifiers.contains(jp.ast.Modifier.STATIC)
                  }
                  val r = instance ++ static
                  r.map { _.asCallableDeclaration }
                }
              }
              val methodPlace = siblingMethods.indexOf(elem)
              (methodPlace: @switch) match {
                case -1 =>
                  throw new RuntimeException("Unexpected state. Please, submit the issue")
                case 0 => "()"
                case x => s"(+$x)"
              }
            }
            Symbols.Global(owner.sym, d.Method(symbolName, disambig))
          case Some(_: jp.ast.expr.ObjectCreationExpr) =>
            ""
          case _ =>
            throw new RuntimeException("Unexpected kind of node. Please, submit the issue")
        }
      case _: jp.ast.body.EnumConstantDeclaration =>
        Symbols.Global(owner, d.Term(symbolName))
      case _: jp.ast.body.VariableDeclarator =>
        val sn = symbolName
        Symbols.Global(owner, d.Term(sn))
      case _: jp.ast.`type`.TypeParameter =>
        Symbols.Global(owner, d.TypeParameter(symbolName))
      case _ =>
        throw new RuntimeException("Unexpected kind of node. Please, submit the issue")
    }

    def kindNode: Option[s.SymbolInformation.Kind] = node match {
      case _: jp.ast.`type`.TypeParameter =>
        Some(k.TYPE_PARAMETER)
      case n => None
    }
  }

  class SymbolTableGenerator extends jp.ast.visitor.VoidVisitorAdapter[SymbolTable] {
    override def visit(pd: jp.ast.PackageDeclaration, arg: SymbolTable): Unit = {
      super.visit(pd, arg)
      arg += pd.sym -> Some(pd)
    }

    override def visit(vd: jp.ast.body.VariableDeclarator, arg: SymbolTable): Unit = {
      super.visit(vd, arg)
      arg += vd.sym -> Some(vd)
    }

    override def visit(cd: jp.ast.body.ConstructorDeclaration, arg: SymbolTable): Unit = {
      super.visit(cd, arg)
      arg += cd.sym -> Some(cd)
    }

    override def visit(cid: jp.ast.body.ClassOrInterfaceDeclaration, arg: SymbolTable): Unit = {
      if (cid.getConstructors.isEmpty) {
        cid.addConstructor(jp.ast.Modifier.PUBLIC)
      }

      super.visit(cid, arg)
      arg += cid.sym -> Some(cid)
    }

    override def visit(p: jp.ast.body.Parameter, arg: SymbolTable): Unit = {
      super.visit(p, arg)
      arg += p.sym -> Some(p)
    }

    override def visit(md: jp.ast.body.MethodDeclaration, arg: SymbolTable): Unit = {
      super.visit(md, arg)
      arg += md.sym -> Some(md)
    }

    override def visit(ad: jp.ast.body.AnnotationDeclaration, arg: SymbolTable): Unit = {
      super.visit(ad, arg)
      arg += ad.sym -> Some(ad)
    }

    override def visit(tp: jp.ast.`type`.TypeParameter, arg: SymbolTable): Unit = {
      super.visit(tp, arg)
      arg += tp.sym -> Some(tp)
    }

    override def visit(ecd: jp.ast.body.EnumConstantDeclaration, arg: SymbolTable): Unit = {
      super.visit(ecd, arg)
      arg += ecd.sym -> Some(ecd)
    }

    override def visit(ed: jp.ast.body.EnumDeclaration, arg: SymbolTable): Unit = {
      super.visit(ed, arg)

      // add synthetic `values` method
      val valuesMethodName = "values"
      if (ed.getMethodsByName(valuesMethodName).isEmpty) {
        val methodSymbol = Symbols.Global(ed.sym, d.Method(valuesMethodName, "()"))
        arg += methodSymbol -> None
      }

      // add synthetic `valueOf(string)` method
      val valueOfMethodName = "valueOf"
      if (ed.getMethodsByName(valueOfMethodName).isEmpty) {
        val methodSymbol = Symbols.Global(ed.sym, d.Method(valueOfMethodName, "()"))
        arg += methodSymbol -> None

        val parameterSymbol = Symbols.Global(methodSymbol, d.Parameter("name"))
        arg += parameterSymbol -> None
      }

      arg += ed.sym -> Some(ed)
    }
  }

}
