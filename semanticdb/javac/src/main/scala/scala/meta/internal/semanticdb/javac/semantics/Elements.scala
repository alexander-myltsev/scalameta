package scala.meta.internal.semanticdb.javac.semantics

import javax.lang.model.`type`.TypeKind
import javax.lang.model.element._
import scala.collection.mutable
import scala.meta.internal.{semanticdb => s}
import scala.meta.internal.semanticdb.SymbolInformation.{Kind => k}
import scala.meta.internal.semanticdb.SymbolInformation.{Property => p}
import scala.collection.JavaConverters._
import scala.meta.internal.semanticdb.Scala.{Descriptor => d, _}
import com.github.{javaparser => jp}
import scala.compat.java8.OptionConverters._

trait Elements { semantics: Semantics =>

  implicit class ElementOps(elem: Element) {

    def enclosingPackage: PackageElement = elem.getEnclosingElement match {
      case enclosing: PackageElement => enclosing
      case enclosing => enclosing.enclosingPackage
    }

    def enclosedElements: Seq[Element] = elem.getEnclosedElements.asScala

    def annotations: Seq[s.Annotation] = elem match {
      case elem: ExecutableElement if elem.getModifiers.contains(Modifier.STRICTFP) =>
        Seq(
          s.Annotation(
            tpe = s.TypeRef(symbol = "scala/annotation/strictfp#")
          ))
      case _ => Seq()
    }

    def isStatic(elem: ExecutableElement): Boolean = elem.getModifiers.contains(Modifier.STATIC)

    def owner: String = elem.getEnclosingElement.sym

    def sym: String = elem match {
      case elem: PackageElement =>
        val qualName = elem.getQualifiedName.toString
        if (qualName == "") Symbols.EmptyPackage
        else qualName.replace('.', '/') + "/"
      case elem: TypeElement =>
        Symbols.Global(owner, d.Type(symbolName))
      case elem: ExecutableElement =>
        val owner = elem.getEnclosingElement
        val disambig = {
          val siblings = owner.enclosedElements
          val siblingMethods = siblings.collect {
            case sibling: ExecutableElement if sibling.symbolName == symbolName => sibling
          }
          val (instance, static) = siblingMethods.partition(method => !isStatic(method))
          val methodPlace = (instance ++ static).indexOf(elem)
          if (methodPlace == 0) "()"
          else s"(+$methodPlace)"
        }
        Symbols.Global(owner.sym, d.Method(symbolName, disambig))
      case elem: VariableElement if elem.getKind == ElementKind.PARAMETER =>
        Symbols.Global(owner, d.Parameter(symbolName))
      case elem: VariableElement =>
        Symbols.Global(owner, d.Term(symbolName))
      case elem: TypeParameterElement =>
        Symbols.Global(owner, d.TypeParameter(symbolName))
    }

    def displayName: String = symbolName

    def symbolName: String = elem match {
      case elem: PackageElement =>
        if (elem.isUnnamed) "_empty_"
        else {
          val fullName = elem.getSimpleName.toString
          fullName.substring(fullName.lastIndexOf('.') + 1)
        }
      case elem => elem.getSimpleName.toString
    }

    def kind: s.SymbolInformation.Kind = {
      symbolTable.get(sym).flatten match {
        case Some(n: jp.ast.Node) => n.kind
        case None => sys.error(elem.toString)
      }
    }

    def access: s.Access = {
      symbolTable.get(sym).flatten match {
        case Some(n: jp.ast.Node) => n.access
        case None => sys.error(elem.toString)
      }
    }

    def properties: Int = {
      symbolTable.get(sym).flatten match {
        case Some(n: jp.ast.Node) => n.properties
        case None => sys.error(elem.toString)
      }
    }

    def isSynthetic: Boolean = elem match {
      case elem: ExecutableElement => Set("<init>", "<clinit>").contains(elem.symbolName)
      case _ => false
    }

    def signature: s.Signature = {
      elem match {
        case elem: PackageElement => s.NoSignature
        case elem: ExecutableElement =>
          val returnType =
            if (elem.getKind == ElementKind.CONSTRUCTOR) s.NoType
            else elem.getReturnType.tpe
          val params = elem.paramElements.map(_.sym)
          val tparams = elem.typeParamElements.map(_.sym)
          s.MethodSignature(
            typeParameters = Some(s.Scope(symlinks = tparams)),
            parameterLists = Seq(s.Scope(symlinks = params)),
            returnType = returnType
          )
        case elem: TypeElement =>
          val parents = {
            val superclass = elem.getSuperclass
            val extendParent =
              if (superclass.getKind == TypeKind.NONE) List(ObjectType)
              else List(superclass.tpe)
            val implementationParents = elem.getInterfaces.asScala.map(_.tpe)
            extendParent ++ implementationParents
          }
          val decls = {
            val (synthetics, others) = elem.enclosedElements.partition(_.isSynthetic)
            (synthetics ++ others).map(_.sym)
          }
          val tparams = elem.typeParamElements.map(_.sym)
          s.ClassSignature(
            typeParameters = Some(s.Scope(symlinks = tparams)),
            parents = parents,
            declarations = Some(s.Scope(symlinks = decls))
          )
        case elem: TypeParameterElement =>
          val bounds = {
            val elemBounds =
              elem.getBounds.asScala.map(_.tpe)
            elemBounds match {
              case Seq() => ObjectType
              case Seq(b) => b
              case elemBounds => s.IntersectionType(elemBounds)
            }
          }
          s.TypeSignature(
            typeParameters = Some(s.Scope()),
            upperBound = bounds
          )
        case elem: VariableElement if elem.getKind == ElementKind.PARAMETER =>
          val parent = elem.getEnclosingElement.asInstanceOf[ExecutableElement]
          val tpe = {
            val parentParams =
              parent.getParameters.asInstanceOf[java.util.List[VariableElement]].asScala
            if (parent.isVarArgs && elem == parentParams.last) {
              val containedType = elem.asType().tpe match {
                case s.TypeRef(_, _, Seq(contained)) => contained
              }
              s.RepeatedType(containedType)
            } else elem.asType().tpe
          }
          s.ValueSignature(
            tpe = tpe
          )
        case elem: VariableElement =>
          s.ValueSignature(
            tpe = elem.asType().tpe
          )
        case _ => s.NoSignature
      }
    }

    def range: Option[s.Range] = {
      for {
        nodeOpt <- symbolTable.get(sym)
        node <- nodeOpt
        _ <- node.getRange.asScala
        rangeOpt = node match {
          case n: jp.ast.nodeTypes.NodeWithSimpleName[_] => n.getName.getRange.asScala
          case n: jp.ast.nodeTypes.NodeWithName[_] => n.getName.getRange.asScala
          case _ => None
        }
        range <- rangeOpt
      } yield {
        s.Range(
          startLine = range.begin.line - 1,
          startCharacter = range.begin.column - 1,
          endLine = range.end.line - 1,
          endCharacter = range.end.column
        )
      }
    }

    def role: s.SymbolOccurrence.Role = elem.getKind match {
      case ElementKind.PACKAGE | ElementKind.ENUM | ElementKind.CLASS |
          ElementKind.ANNOTATION_TYPE | ElementKind.INTERFACE | ElementKind.ENUM_CONSTANT |
          ElementKind.FIELD | ElementKind.PARAMETER | ElementKind.METHOD | ElementKind.CONSTRUCTOR |
          ElementKind.STATIC_INIT | ElementKind.INSTANCE_INIT | ElementKind.TYPE_PARAMETER =>
        s.SymbolOccurrence.Role.DEFINITION

      case _ => s.SymbolOccurrence.Role.UNKNOWN_ROLE
    }

    def info: s.SymbolInformation = s.SymbolInformation(
      symbol = sym,
      language = s.Language.JAVA,
      kind = kind,
      displayName = displayName,
      annotations = annotations,
      access = access,
      properties = properties,
      signature = signature
    )

    def occurrence: s.SymbolOccurrence =
      s.SymbolOccurrence(symbol = sym, range = range, role = role)

    def populateInfos(
        infos: mutable.ListBuffer[s.SymbolInformation],
        occurrences: mutable.ListBuffer[s.SymbolOccurrence]): s.SymbolInformation = {
      val myInfo = info
      infos += myInfo
      if (range.isDefined) {
        occurrences += occurrence
      }

      elem match {
        case elem: TypeElement =>
          elem.typeParamElements.foreach { elem =>
            elem.populateInfos(infos, occurrences)
          }
          elem.enclosedElements.foreach { elem =>
            elem.populateInfos(infos, occurrences)
          }
        case elem: ExecutableElement =>
          elem.typeParamElements.foreach { elem =>
            elem.populateInfos(infos, occurrences)
          }
          elem.paramElements.foreach { elem =>
            elem.populateInfos(infos, occurrences)
          }
        case _ =>
      }
      myInfo
    }

  }

  implicit class ExecutableElementOps(elem: ExecutableElement) {
    def typeParamElements: Seq[TypeParameterElement] = elem.getTypeParameters.asScala
    def paramElements: Seq[VariableElement] = elem.getParameters.asScala
  }

  implicit class TypeElementOps(elem: TypeElement) {
    def typeParamElements: Seq[TypeParameterElement] = elem.getTypeParameters.asScala
  }

}
