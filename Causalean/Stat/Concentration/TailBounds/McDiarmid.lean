/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bounded-difference inequalities (thin re-export of `FoML.McDiarmid`,
  `FoML.BoundedDifference`, `FoML.Rademacher`)

Thin re-export of FoML's bounded-difference material. Original lived under
`auto-res/lean-rademacher`, MIT License — see the FoML package
(`third_party/lean-rademacher/`) for full provenance and `LICENSE`.

The FoML symbols (`mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg`,
`mcdiarmid_inequality_pos'`, `mcdiarmid_inequality_aux`,
`uniformDeviation_bounded_difference`, `bounded_difference_of_bounded`) live in
the root namespace and are re-imported here for unqualified use.
-/

module
public import FoML.BoundedDifference
public import FoML.McDiarmid
public import FoML.Rademacher

/-! # McDiarmid bounded-difference inequalities

This file is the library's single entry point for FoML's bounded-difference
concentration results: a function whose value changes only modestly when one
coordinate of the sample is replaced concentrates sharply about its mean. It
re-exports the McDiarmid inequalities themselves (`mcdiarmid_inequality_pos`,
`mcdiarmid_inequality_neg`, `mcdiarmid_inequality_pos'`,
`mcdiarmid_inequality_aux`) together with the bounded-difference property of the
uniform deviation functional (`uniformDeviation_bounded_difference`) and the
criterion deriving that property from a pointwise bound
(`bounded_difference_of_bounded`).
-/

public section

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
