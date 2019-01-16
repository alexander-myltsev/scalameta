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

  implicit class PackageDeclarationOptOps(pOpt: Option[jp.ast.PackageDeclaration]) {
    def sym: String = pOpt match {
      case Some(p) => p.getNameAsString.replace('.', '/') + '/'
      case None => Symbols.EmptyPackage
    }
  }

  implicit class NodeOps(node: jp.ast.Node) {
    def enclosingPackage: Option[jp.ast.PackageDeclaration] = node match {
      case e: jp.ast.CompilationUnit => e.getPackageDeclaration.asScala
      case n => n.getParentNode.asScala.flatMap { _.enclosingPackage }
    }

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

    def kind: s.SymbolInformation.Kind = node match {
      case _: jp.ast.`type`.TypeParameter =>
        k.TYPE_PARAMETER
      case _: jp.ast.body.FieldDeclaration =>
        k.FIELD
      case _: jp.ast.body.VariableDeclarator =>
        k.FIELD
      case _: jp.ast.body.EnumConstantDeclaration =>
        k.FIELD
      case _: jp.ast.body.Parameter =>
        k.PARAMETER
      case elem: jp.ast.body.CallableDeclaration[_] =>
        if (elem.isConstructorDeclaration) {
          k.CONSTRUCTOR
        } else if (elem.isMethodDeclaration) {
          k.METHOD
        } else {
          sys.error(elem.toString)
        }
      case elem: jp.ast.body.ClassOrInterfaceDeclaration =>
        if (elem.isInterface) {
          k.INTERFACE
        } else {
          k.CLASS
        }
      case _: jp.ast.body.EnumDeclaration =>
        k.CLASS
      case _: jp.ast.body.AnnotationDeclaration =>
        k.INTERFACE
      case n => sys.error(n.toString)
    }

    def properties: Int = {
      var prop = 0
      def extractProperties(n: jp.ast.nodeTypes.NodeWithModifiers[_]) = {
        n.getModifiers.asScala.foreach {
          case jp.ast.Modifier.STATIC =>
            prop |= p.STATIC.value
          case jp.ast.Modifier.FINAL =>
            prop |= p.FINAL.value
          case jp.ast.Modifier.ABSTRACT =>
            prop |= p.ABSTRACT.value
          case _ =>
        }
      }

      node match {
        case n: jp.ast.nodeTypes.NodeWithModifiers[_] =>
          extractProperties(n)
        case n: jp.ast.body.VariableDeclarator =>
          n.getParentNode.asScala match {
            case Some(fd: jp.ast.body.FieldDeclaration) =>
              extractProperties(fd)
            case _ => sys.error(n.toString)
          }
        case _ =>
      }

      node match {
        case _: jp.ast.body.EnumConstantDeclaration =>
          prop |= p.ENUM.value
          prop |= p.FINAL.value
          prop |= p.STATIC.value
        case _: jp.ast.body.EnumDeclaration =>
          prop |= p.ENUM.value
          prop |= p.FINAL.value
        case cid: jp.ast.body.ClassOrInterfaceDeclaration if cid.isInterface =>
          prop |= p.ABSTRACT.value
        case ad: jp.ast.body.AnnotationDeclaration =>
          prop |= p.ABSTRACT.value
        case _ =>
      }

      node match {
        case md: jp.ast.body.MethodDeclaration
          if (prop & p.ABSTRACT.value) == 0 && (prop & p.STATIC.value) == 0 =>
          md.getParentNode.asScala match {
            case Some(x) if x.kind == k.INTERFACE =>
              prop |= p.DEFAULT.value
            case _ =>
          }
        case _ =>
      }
      prop
    }

    def access: s.Access = kind match {
      case k.LOCAL | k.PARAMETER | k.TYPE_PARAMETER | k.PACKAGE =>
        s.NoAccess
      case k.INTERFACE =>
        s.PublicAccess()
      case knd =>
        node match {
          case n: jp.ast.Node with jp.ast.nodeTypes.NodeWithModifiers[_] =>
            val mods = n.getModifiers
            if (mods.contains(jp.ast.Modifier.PUBLIC)) s.PublicAccess()
            else if (mods.contains(jp.ast.Modifier.PRIVATE)) s.PrivateAccess()
            else if (mods.contains(jp.ast.Modifier.PROTECTED)) s.ProtectedAccess()
            else {
              def withinInterface =
                n.getParentNode.asScala match {
                  case Some(cid: jp.ast.body.ClassOrInterfaceDeclaration) => cid.isInterface
                  case _ => false
                }
              def syntheticConstructorWithinPackageClass = {
                n.getParentNode.asScala match {
                  case Some(cid: jp.ast.body.ClassOrInterfaceDeclaration) =>
                    cid.getConstructors.asScala.toList match {
                      case List(c) if c.getModifiers.isEmpty =>
                        cid.getParentNode.asScala match {
                          case Some(_: jp.ast.CompilationUnit) => true
                          case _ => false
                        }
                      case _ => false
                    }
                  case _ => false
                }
              }
              knd match {
                case k.METHOD if withinInterface => s.PublicAccess()
                case k.CONSTRUCTOR if syntheticConstructorWithinPackageClass =>
                  n.getParentNode.get.asInstanceOf[jp.ast.body.ClassOrInterfaceDeclaration].access
                case _ => s.PrivateWithinAccess(n.enclosingPackage.sym)
              }
            }
          case vd: jp.ast.body.VariableDeclarator =>
            vd.getParentNode.asScala match {
              case Some(fd: jp.ast.body.FieldDeclaration) =>
                fd.access
              case _ => sys.error(vd.toString)
            }
          case ecd: jp.ast.body.EnumConstantDeclaration =>
            ecd.getParentNode.asScala match {
              case Some(n: jp.ast.Node with jp.ast.nodeTypes.NodeWithModifiers[_]) =>
                n.access
              case _ => sys.error(ecd.toString)
            }
          case n =>
            s.PrivateWithinAccess(n.enclosingPackage.sym)
        }
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
        cid.addConstructor()
      }

      if (cid.isInterface) {
        cid.getMethods.asScala.foreach { md =>
          if (md.getModifiers.isEmpty) {
            md.addModifier(jp.ast.Modifier.ABSTRACT)
          }
        }
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
      // add synthetic `values` method
      val valuesMethodName = "values"
      if (ed.getMethodsByName(valuesMethodName).isEmpty) {
        val m = ed.addMethod(valuesMethodName, jp.ast.Modifier.PUBLIC, jp.ast.Modifier.STATIC)
      }

      // add synthetic `valueOf(string)` method
      val valueOfMethodName = "valueOf"
      if (ed.getMethodsByName(valueOfMethodName).isEmpty) {
        val m = ed.addMethod(valueOfMethodName, jp.ast.Modifier.PUBLIC, jp.ast.Modifier.STATIC)
        m.addParameter(
          new jp.ast.body.Parameter(
            jp.JavaParser.parseClassOrInterfaceType("java.lang.String"),
            new jp.ast.expr.SimpleName("name")
          )
        )
      }

      super.visit(ed, arg)
      arg += ed.sym -> Some(ed)
    }
  }

}
