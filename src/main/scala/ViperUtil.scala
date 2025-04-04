// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2025 ETH Zurich.

package viper.silver.sif

import viper.silver.ast.{And, ErrorTrafo, Exp, Info, Position, TrueLit}

object ViperUtil {
  def bigAnd(it: Iterable[Exp])(pos: Position, info: Info, errT: ErrorTrafo): Exp = {
    it.headOption match {
      case Some(hd) =>
        val tl = it.tail
        tl.foldLeft[Exp](hd) { case (accum, elem) => And(accum, elem)(pos, info, errT) }
      case None => TrueLit()(pos, info, errT)
    }
  }
}
