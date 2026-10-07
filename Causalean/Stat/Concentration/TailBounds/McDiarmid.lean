/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import FoML.BoundedDifference
public import FoML.McDiarmid
public import FoML.Rademacher

/-! # McDiarmid bounded-difference inequalities

McDiarmid's inequality: a function of independent variables that changes by at most cᵢ when the
i-th argument alone is replaced concentrates about its mean. For independent X₁, …, Xₙ, a
measurable f with these bounded differences, ε ≥ 0 and any t with t·Σ cᵢ² ≤ 1,

    P( f(X) − E f(X) ≥ ε ) ≤ exp(−2 ε² t),

and symmetrically for the lower tail; t = 1/Σ cᵢ² gives the classical exp(−2ε²/Σ cᵢ²). The
theorems are proved in the FoML library and stated in the root namespace; this file declares
nothing and is the library's entry point for them.

## Main results

* `mcdiarmid_inequality_pos`, `mcdiarmid_inequality_neg` — upper and lower tail bounds for
  independent variables indexed by a finite type.
* `mcdiarmid_inequality_pos'` — the upper tail for coordinates of an iid product sample.
* `mcdiarmid_inequality_aux` — the version indexed by `Fin m`, from which the others follow.
* `uniformDeviation_bounded_difference` — for a class of functions bounded by b, the uniform
  deviation sup over the class of |sample mean − mean| changes by at most 2b/n when one sample
  point is replaced.
* `bounded_difference_of_bounded` — for such a class, sums over two samples of size n differ by
  at most 2nb.
-/

public section

namespace Causalean
namespace Stat
namespace Concentration

end Concentration
end Stat
end Causalean
