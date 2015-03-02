package scala.meta
package internal
package tokenizers

import scala.collection.{immutable, mutable}
import org.scalameta.unreachable
import org.scalameta.invariants._
import Chars.{CR, LF, FF}
import LegacyToken._

private[meta] object tokenize {
  def apply(input: Input)(implicit dialect: Dialect): Vector[Token] = {
    def legacyTokenToToken(curr: LegacyTokenData): Token = {
      (curr.token: @scala.annotation.switch) match {
        case CHARLIT         => Token.Literal.Char(input, curr.offset, curr.endOffset, curr.charVal)
        case INTLIT          => Token.Literal.Int(input, curr.offset, curr.endOffset, isNegated => curr.intVal(isNegated).map(_.toInt).get)
        case LONGLIT         => Token.Literal.Long(input, curr.offset, curr.endOffset, isNegated => curr.intVal(isNegated).get)
        case FLOATLIT        => Token.Literal.Float(input, curr.offset, curr.endOffset, isNegated => curr.floatVal(isNegated).map(_.toFloat).get)
        case DOUBLELIT       => Token.Literal.Double(input, curr.offset, curr.endOffset, isNegated => curr.floatVal(isNegated).get)
        case STRINGLIT       => Token.Literal.String(input, curr.offset, curr.endOffset, curr.strVal)
        case SYMBOLLIT       => Token.Literal.Symbol(input, curr.offset, curr.endOffset, scala.Symbol(curr.strVal))

        case IDENTIFIER       => Token.Ident(input, curr.offset, curr.endOffset)
        case BACKQUOTED_IDENT => Token.Ident(input, curr.offset, curr.endOffset)
        case INTERPOLATIONID  => Token.Interpolation.Id(input, curr.offset, curr.endOffset)

        case NEW   => Token.`new`(input, curr.offset)
        case THIS  => Token.`this`(input, curr.offset)
        case SUPER => Token.`super`(input, curr.offset)
        case NULL  => Token.`null`(input, curr.offset)
        case TRUE  => Token.`true`(input, curr.offset)
        case FALSE => Token.`false`(input, curr.offset)

        case IMPLICIT  => Token.`implicit`(input, curr.offset)
        case OVERRIDE  => Token.`override`(input, curr.offset)
        case PROTECTED => Token.`protected`(input, curr.offset)
        case PRIVATE   => Token.`private`(input, curr.offset)
        case ABSTRACT  => Token.`abstract`(input, curr.offset)
        case FINAL     => Token.`final`(input, curr.offset)
        case SEALED    => Token.`sealed`(input, curr.offset)
        case LAZY      => Token.`lazy`(input, curr.offset)
        case MACRO     => Token.`macro`(input, curr.offset)

        case PACKAGE    => Token.`package `(input, curr.offset)
        case IMPORT     => Token.`import`(input, curr.offset)
        case CLASS      => Token.`class `(input, curr.offset)
        case CASECLASS  => unreachable
        case OBJECT     => Token.`object`(input, curr.offset)
        case CASEOBJECT => unreachable
        case TRAIT      => Token.`trait`(input, curr.offset)
        case EXTENDS    => Token.`extends`(input, curr.offset)
        case WITH       => Token.`with`(input, curr.offset)
        case TYPE       => Token.`type`(input, curr.offset)
        case FORSOME    => Token.`forSome`(input, curr.offset)
        case DEF        => Token.`def`(input, curr.offset)
        case VAL        => Token.`val`(input, curr.offset)
        case VAR        => Token.`var`(input, curr.offset)

        case IF      => Token.`if`(input, curr.offset)
        case THEN    => unreachable
        case ELSE    => Token.`else`(input, curr.offset)
        case WHILE   => Token.`while`(input, curr.offset)
        case DO      => Token.`do`(input, curr.offset)
        case FOR     => Token.`for`(input, curr.offset)
        case YIELD   => Token.`yield`(input, curr.offset)
        case THROW   => Token.`throw`(input, curr.offset)
        case TRY     => Token.`try`(input, curr.offset)
        case CATCH   => Token.`catch`(input, curr.offset)
        case FINALLY => Token.`finally`(input, curr.offset)
        case CASE    => Token.`case`(input, curr.offset)
        case RETURN  => Token.`return`(input, curr.offset)
        case MATCH   => Token.`match`(input, curr.offset)

        case LPAREN   => Token.`(`(input, curr.offset)
        case RPAREN   => Token.`)`(input, curr.offset)
        case LBRACKET => Token.`[`(input, curr.offset)
        case RBRACKET => Token.`]`(input, curr.offset)
        case LBRACE   => Token.`{`(input, curr.offset)
        case RBRACE   => Token.`}`(input, curr.offset)

        case COMMA     => Token.`,`(input, curr.offset)
        case SEMI      => Token.`;`(input, curr.offset)
        case DOT       => Token.`.`(input, curr.offset)
        case COLON     => Token.`:`(input, curr.offset)
        case EQUALS    => Token.`=`(input, curr.offset)
        case AT        => Token.`@`(input, curr.offset)
        case HASH      => Token.`#`(input, curr.offset)
        case USCORE    => Token.`_ `(input, curr.offset)
        case ARROW     => Token.`=>`(input, curr.offset, curr.endOffset)
        case LARROW    => Token.`<-`(input, curr.offset, curr.endOffset)
        case SUBTYPE   => Token.`<:`(input, curr.offset)
        case SUPERTYPE => Token.`>:`(input, curr.offset)
        case VIEWBOUND => Token.`<%`(input, curr.offset)

        case WHITESPACE =>
          if (curr.strVal == " ") Token.` `(input, curr.offset)
          else if (curr.strVal == "\t") Token.`\t`(input, curr.offset)
          else if (curr.strVal == "\r") Token.`\r`(input, curr.offset)
          else if (curr.strVal == "\n") Token.`\n`(input, curr.offset)
          else if (curr.strVal == "\f") Token.`\f`(input, curr.offset)
          else unreachable(debug(curr.strVal))

        case COMMENT   => Token.Comment(input, curr.offset, curr.endOffset)

        case ELLIPSIS  => Token.Ellipsis(input, curr.offset, curr.endOffset, curr.base)

        case EOF       => Token.EOF(input)
        case XMLSTART  => Token.XMLStart(input, curr.offset, curr.endOffset)

        case EMPTY    => unreachable
        case UNDEF    => unreachable
        case ERROR    => unreachable
      }
    }
    val scanner = new LegacyScanner(input)
    val buf = scanner.reader.buf

    var legacyTokenBuf = new mutable.UnrolledBuffer[LegacyTokenData]
    scanner.foreach(curr => {
      // TODO: reinstate error handling
      // try legacyTokenBuf += curr
      // catch { case e: Exception => scanner.report.error(e.getMessage) }
      // val tokenGetters = Tokens.getClass.getMethods.filter(_.getParameterTypes().length == 0)
      // println(tokenGetters.find(m => m.invoke(Tokens) == curr).get.getName)
      val currCopy = new LegacyTokenData{}.copyFrom(curr)
      if (currCopy.token == EOF) currCopy.offset = buf.length // NOTE: sometimes EOF's offset is `buf.length - 1`, and that might mess things up
      legacyTokenBuf += currCopy
    })
    val legacyTokens = legacyTokenBuf.toVector

    var tokens = new mutable.UnrolledBuffer[Token]
    def loop(startingFrom: Int, braceBalance: Int = 0, returnWhenBraceBalanceHitsZero: Boolean = false): Int = {
      var i = startingFrom
      def prev = legacyTokens(i - 1)
      def curr = legacyTokens(i)
      def emitToken() = tokens += legacyTokenToToken(curr)
      def nextToken() = i += 1
      if (i >= legacyTokens.length) return i

      emitToken()
      nextToken()

      // NOTE: need to track this in order to correctly emit SpliceEnd tokens after splices end
      var braceBalance1 = braceBalance
      if (prev.token == LBRACE) braceBalance1 += 1
      if (prev.token == RBRACE) braceBalance1 -= 1
      if (braceBalance1 == 0 && returnWhenBraceBalanceHitsZero) return i

      if (prev.token == INTERPOLATIONID) {
        // NOTE: funnily enough, messing with interpolation tokens is what I've been doing roughly 3 years ago, on New Year's Eve of 2011/2012
        // I vividly remember spending 2 or 3 days making scanner emit detailed tokens for string interpolations, and that was tedious.
        // Now we need to do the same for our new token stream, but I don't really feel like going through the pain again.
        // Therefore, I'm giving up the 1-to-1 legacy-to-new token correspondence and will be trying to reverse engineer sane tokens here rather than in scanner.
        var startEnd = prev.endOffset + 1
        while (startEnd < buf.length && buf(startEnd) == '\"') startEnd += 1
        val numStartQuotes = startEnd - prev.endOffset - 1
        val numQuotes = if (numStartQuotes <= 2) 1 else 3
        def emitStart(offset: Offset) = tokens += Token.Interpolation.Start(input, offset, offset + numQuotes - 1)
        def emitEnd(offset: Offset) = tokens += Token.Interpolation.End(input, offset, offset + numQuotes - 1)
        def emitContents(): Unit = {
          require(curr.token == STRINGPART || curr.token == STRINGLIT)
          if (curr.token == STRINGPART) {
            tokens += Token.Interpolation.Part(input, curr.offset, curr.endOffset)
            require(buf(curr.endOffset + 1) == '$')
            val dollarOffset = curr.endOffset + 1
            def emitSpliceStart(offset: Offset) = tokens += Token.Interpolation.SpliceStart(input, offset)
            def emitSpliceEnd(offset: Offset) = tokens += Token.Interpolation.SpliceEnd(input, offset)
            def requireExpectedToken(expected: LegacyToken) = { require(curr.token == expected) }
            def emitExpectedToken(expected: LegacyToken) = { require(curr.token == expected); emitToken() }
            if (buf(dollarOffset + 1) == '{') {
              emitSpliceStart(dollarOffset)
              nextToken()
              i = loop(i, braceBalance = 0, returnWhenBraceBalanceHitsZero = true)
              emitSpliceEnd(curr.offset - 1)
              emitContents()
            } else if (buf(dollarOffset + 1) == '_') {
              emitSpliceStart(dollarOffset)
              nextToken()
              emitExpectedToken(USCORE)
              nextToken()
              emitSpliceEnd(curr.offset - 1)
              emitContents()
            } else {
              emitSpliceStart(dollarOffset)
              nextToken()
              require(curr.token == IDENTIFIER || curr.token == THIS)
              emitToken()
              nextToken()
              emitSpliceEnd(curr.offset - 1)
              emitContents()
            }
          } else {
            curr.endOffset -= numQuotes
            tokens += Token.Interpolation.Part(input, curr.offset, curr.endOffset)
            require(buf(curr.endOffset + 1) == '\"')
            nextToken()
          }
        }
        // NOTE: before emitStart, curr is the first token that follows INTERPOLATIONID
        // i.e. STRINGLIT (if the interpolation is empty) or STRINGPART (if it's not)
        // NOTE: before emitEnd, curr is the first token that follows the concluding STRINGLIT of the interpolation
        // for example, EOF in the case of `q""` or `q"$foobar"`
        numStartQuotes match {
          case 1 => emitStart(curr.offset - 1); emitContents(); emitEnd(curr.offset - 1)
          case 2 => emitStart(curr.offset); curr.offset += 1; emitContents(); emitEnd(curr.offset - 1)
          case n if 3 <= n && n < 6 => emitStart(curr.offset - 3); emitContents(); emitEnd(curr.offset - 3)
          case 6 => emitStart(curr.offset - 3); emitContents(); emitEnd(curr.offset - 3)
        }
      }

      loop(i, braceBalance1, returnWhenBraceBalanceHitsZero)
    }

    loop(startingFrom = 0)
    tokens.toVector
  }
}