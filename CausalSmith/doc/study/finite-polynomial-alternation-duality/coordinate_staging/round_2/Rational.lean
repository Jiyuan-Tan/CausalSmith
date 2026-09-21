/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.Alternation

/-!
# Finite moment duality for a pole-separated rational target

This module specializes the generic finite alternation-duality API to the
continuous rational function `x ↦ x/(x+a)` on any interval avoiding its pole.
-/

open Set

namespace Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- The rational target with parameter `a` is the function `x ↦ x/(x+a)`. [the stated inputs](hyp:a,x) establish [the defined object](goal). -/
noncomputable def rationalTarget (a : ℝ) (x : ℝ) : ℝ := x / (x + a)

/-- If the pole `-a` is outside a closed interval, the rational target
`x ↦ x/(x+a)` is continuous on that interval. [the stated inputs](hyp:a,r,s,hpole) establish [the stated conclusion](goal). -/
theorem continuousOn_rationalTarget {a r s : ℝ}
    (hpole : -a ∉ Set.Icc r s) :
    ContinuousOn (rationalTarget a) (Set.Icc r s) := by
  unfold rationalTarget
  apply continuousOn_id.div (continuousOn_id.add continuousOn_const)
  intro x hx hzero
  apply hpole
  change x + a = 0 at hzero
  have hxa : x = -a := by linarith
  simpa [hxa] using hx

/-- On a nondegenerate interval avoiding `-a`, there are `L+2` ordered,
normalized finite weights that match moments through degree `L` and whose
rational-target separation is the exact best degree-`L` uniform error. [the stated inputs](hyp:a,r,s,hrs,hpole,L) establish [the stated conclusion](goal). -/
theorem exists_rationalFiniteMomentDual
    {a r s : ℝ} (hrs : r < s) (hpole : -a ∉ Set.Icc r s) (L : ℕ) :
    Nonempty (FiniteMomentDual (rationalTarget a) r s L) := by
  exact exists_finiteMomentDual hrs (continuousOn_rationalTarget hpole) L

end Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
