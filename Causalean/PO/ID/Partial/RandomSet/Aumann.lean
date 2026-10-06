/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.PO.ID.Partial.RandomSet.Interval
public import Causalean.PO.ID.Partial.RandomSet.Hausdorff
public import Causalean.PO.ID.Partial.SupportFunction.Basic

/-! # The One-Dimensional Everywhere-Selection Support Bridge

This file connects the interval produced by the everywhere-selection
expectation with support functions in the two unit directions on the real line.
The support function of `[a,b]` at `+1` is `b`, and at `-1` is `-a`; these
endpoint formulas yield scalar support-expectation identities and the interval
Hausdorff identity. The selection interface used here requires membership at
every outcome, not merely almost surely.

Main declarations:
* `supportFn_Icc_one` and `supportFn_Icc_neg_one` compute support functions of
  real intervals at the two unit directions.
* `hausdorffDist_Icc_eq_supportFn` rewrites interval Hausdorff distance in the
  `d = 1` support-function form.
* `artstein_supportFn_one` and `artstein_supportFn_neg_one` prove endpoint
  support-expectation identities for `selectionExpectation`.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace Causalean.PartialID.RandomSet

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {L U : Ω → ℝ}

/-- The real inner product against `1` is the identity (`⟪1, y⟫ = y`). -/
private lemma inner_one_left (y : ℝ) : ⟪(1 : ℝ), y⟫ = y := by
  simpa using real_inner_smul_right (1 : ℝ) 1 y

/-- The real inner product against `−1` is negation (`⟪-1, y⟫ = -y`). -/
private lemma inner_neg_one_left (y : ℝ) : ⟪(-1 : ℝ), y⟫ = -y := by
  rw [show (-1 : ℝ) = -(1 : ℝ) from rfl, inner_neg_left, inner_one_left]

/-- Support function of a real interval at `+1`: the upper endpoint. -/
theorem supportFn_Icc_one {a b : ℝ} (hab : a ≤ b) :
    supportFn (Set.Icc a b) (1 : ℝ) = b := by
  rw [supportFn_eq_iSup_image]
  simp only [inner_one_left, Set.image_id']
  exact csSup_Icc hab

/-- Support function of a real interval at `−1`: the negated lower endpoint. -/
theorem supportFn_Icc_neg_one {a b : ℝ} (hab : a ≤ b) :
    supportFn (Set.Icc a b) (-1 : ℝ) = -a := by
  rw [supportFn_eq_iSup_image]
  simp only [inner_neg_one_left]
  rw [Set.image_neg_Icc]
  exact csSup_Icc (by linarith)

/-- **The `d = 1` Hörmander identity (Beresteanu–Molinari eq. (A.1)).** For real numbers
`a ≤ b` and `c ≤ d` forming [two well-ordered closed intervals](hyp:hab,hcd), [the
Hausdorff distance between the intervals `[a,b]` and `[c,d]` equals the largest, over
the two unit directions `+1` and `−1`, of the absolute difference between their
support functions in that direction](goal). -/
theorem hausdorffDist_Icc_eq_supportFn {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    hausdorffDist
        (Set.Icc a b) (Set.Icc c d)
      = max |supportFn (Set.Icc a b) (-1 : ℝ) - supportFn (Set.Icc c d) (-1 : ℝ)|
            |supportFn (Set.Icc a b) (1 : ℝ) - supportFn (Set.Icc c d) (1 : ℝ)| := by
  rw [hausdorffDist_Icc hab hcd, supportFn_Icc_one hab, supportFn_Icc_one hcd,
    supportFn_Icc_neg_one hab, supportFn_Icc_neg_one hcd,
    show (-a) - (-c) = -(a - c) by ring, abs_neg]

/-- **Endpoint support identity in direction `+1`.** For [measurable lower and upper
endpoint functions `L`, `U` of an interval-valued random set](hyp:hL,hU) that are
[integrable](hyp:hLint,hUint) and satisfy [`L` pointwise at most `U`](hyp:hLU), [the
support function of the everywhere-selection expectation of `[L, U]` in direction
`+1` equals the expected support function of the realized interval in that
direction](goal):
`s(+1, E[F]) = E[s(+1, F)]`. -/
theorem artstein_supportFn_one (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    supportFn (selectionExpectation L U μ) (1 : ℝ)
      = ∫ ω, supportFn (randomInterval L U ω) (1 : ℝ) ∂μ := by
  have hfun : (fun ω => supportFn (randomInterval L U ω) (1 : ℝ)) = fun ω => U ω := by
    funext ω; exact supportFn_Icc_one (hLU ω)
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU,
    supportFn_Icc_one (integral_le_integral_of_le hLint hUint hLU), hfun]

/-- **Endpoint support identity in direction `−1`.** For [measurable lower and upper
endpoint functions `L`, `U` of an interval-valued random set](hyp:hL,hU) that are
[integrable](hyp:hLint,hUint) and satisfy [`L` pointwise at most `U`](hyp:hLU), [the
support function of the everywhere-selection expectation of `[L, U]` in direction
`−1` equals the expected support function of the realized interval in that
direction](goal):
`s(−1, E[F]) = E[s(−1, F)]`. -/
theorem artstein_supportFn_neg_one (hL : Measurable L) (hU : Measurable U)
    (hLint : Integrable L μ) (hUint : Integrable U μ) (hLU : ∀ ω, L ω ≤ U ω) :
    supportFn (selectionExpectation L U μ) (-1 : ℝ)
      = ∫ ω, supportFn (randomInterval L U ω) (-1 : ℝ) ∂μ := by
  have hfun : (fun ω => supportFn (randomInterval L U ω) (-1 : ℝ)) = fun ω => -L ω := by
    funext ω; exact supportFn_Icc_neg_one (hLU ω)
  rw [selectionExpectation_eq_Icc hL hU hLint hUint hLU,
    supportFn_Icc_neg_one (integral_le_integral_of_le hLint hUint hLU), hfun,
    integral_neg]

end Causalean.PartialID.RandomSet
