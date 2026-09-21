/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.Analysis.Convex.StdSimplex

/-!
# Finite probability coordinates

This module packages probability mass functions on a finite alphabet as the
standard real simplex.  It also records the coordinate and finite-product
continuity facts used by finite side-information experiments.
-/

open scoped BigOperators
open Set

namespace Causalean.Stat.Minimax.FiniteSideInformation

variable (C : Type*) [Fintype C]

/-- A [finite alphabet](hyp:C) has as its [coordinate probability simplex](goal) the collection of
real probability vectors with nonnegative coordinates summing to one. -/
abbrev FinitePmf := {w : C → ℝ // w ∈ stdSimplex ℝ C}

/-- The [finite probability simplex](hyp:C) is [compact](goal) in its coordinate topology. -/
theorem isCompact_finitePmf : IsCompact (Set.univ : Set (FinitePmf C)) := by
  exact isCompact_univ

/-- Evaluation at an [atom](hyp:c) of a [finite alphabet](hyp:C) is a [continuous coordinate](goal)
on the finite probability simplex. -/
theorem continuous_atom (c : C) : Continuous (fun w : FinitePmf C ↦ (w.1 c : ℝ)) := by
  exact (continuous_apply c).comp continuous_subtype_val

/-- The mass assigned by a [finite probability vector](hyp:w) on a [finite alphabet](hyp:C) to an [atom](hyp:c) is
[nonnegative](goal). -/
theorem FinitePmf.nonneg (w : FinitePmf C) (c : C) : 0 ≤ w.1 c := by
  exact w.2.1 c

/-- The atom masses of a [finite probability vector](hyp:w) over the [finite alphabet](hyp:C)
[sum to one](goal). -/
theorem FinitePmf.sum_eq_one (w : FinitePmf C) : ∑ c, w.1 c = 1 := by
  exact w.2.2

/-- Given a [finite alphabet](hyp:C), [finite probability vector](hyp:w), and [finite sample](hyp:z), the
[product probability](goal) is the product of the sampled atom masses. -/
def productProbability {m : ℕ} (w : FinitePmf C) (z : Fin m → C) : ℝ :=
  ∏ i, w.1 (z i)

/-- For a [finite alphabet](hyp:C) and [fixed finite sample](hyp:z), its
[product probability varies continuously](goal) with the underlying probability vector. -/
theorem continuous_productProbability {m : ℕ} (z : Fin m → C) :
    Continuous (fun w : FinitePmf C ↦ productProbability C w z) := by
  apply continuous_finsetProd
  intro i _
  exact (continuous_apply (z i)).comp continuous_subtype_val

/-- Every [finite-alphabet](hyp:C) [product probability](hyp:w,z) is [nonnegative](goal). -/
theorem productProbability_nonneg {m : ℕ} (w : FinitePmf C) (z : Fin m → C) :
    0 ≤ productProbability C w z := by
  exact Finset.prod_nonneg fun i _ ↦ FinitePmf.nonneg C w (z i)

/-- The [product probabilities](hyp:w) on a [finite alphabet](hyp:C) of all length-`m` samples
[sum to one](goal). -/
theorem sum_productProbability {m : ℕ} (w : FinitePmf C) :
    ∑ z : Fin m → C, productProbability C w z = 1 := by
  calc
    ∑ z : Fin m → C, productProbability C w z = ∏ _i : Fin m, ∑ c, w.1 c := by
      symm
      exact Fintype.prod_sum fun _i : Fin m ↦ fun c : C ↦ w.1 c
    _ = 1 := by simp [w.sum_eq_one]

end Causalean.Stat.Minimax.FiniteSideInformation
