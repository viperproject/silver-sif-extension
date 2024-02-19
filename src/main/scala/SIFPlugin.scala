// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.


package viper.silver.sif

import fastparse._
import viper.silver.ast.Program
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.parser.FastParserCompanion.whitespace

import scala.annotation.unused

class SIFPlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin with ParserPluginTemplate {
  import fp.{integer, exp, ParserExtension, parenthesizedExp, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym}

  def condition[$: P]: P[(PReserved[PLowKeyword.type], PExp)] = P(P(PLowKeyword) ~ exp)
  // def low[$: P]: P[PLowExp] = P((P[PLowKeyword.type](PLowKeyword) ~ parenthesizedExp) map (PLowExp.apply _).tupled).pos
  // def rel[$: P]: P[PRelExp] = FP("rel" ~ "(" ~ exp ~ "," ~ integer ~ ")").map { case (pos, (e, i)) => PRelExp(e, i)(pos) }
  // def lowEvent[$: P]: P[PLowEventExp] = P("lowEvent").map { case (_) => PLowEventExp()(_) }

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewKeywords(Set(PLowKeyword, PLowEventKeyword, PRelKeyword))
    // ParserExtension.addNewExpAtEnd(low(_))
    // ParserExtension.addNewExpAtEnd(rel(_))
    // ParserExtension.addNewExpAtEnd(lowEvent(_))
    input
  }

  override def beforeVerify(input: Program): Program = {
    SIFExtendedTransformer.transform(input, false)
  }
}
