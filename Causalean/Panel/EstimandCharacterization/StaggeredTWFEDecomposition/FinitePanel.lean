/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Goodman-Bacon (2021): TWFE decomposition under staggered timing — Layer A primitives

**Role in the folder.** *Finite base.* Every other file in the folder sits on
these definitions. Pure finite ℝ data — **no probability space, no potential
outcomes**. See `StaggeredTWFEDecomposition.lean` for the folder layer-map.

Layer A — pure finite-cell algebra. This file holds the cell-statistics record
`CohortPanel`, the adoption-date helpers, the residualized treatment `Dtilde`,
the residualized variance `VD`, the window mean `Ybar`, the three 2x2
comparison contrasts `Δ_TN, Δ_EL, Δ_LE`, the raw and normalized weights
(`λ_TN, λ_EL, λ_LE, w_TN, w_EL, w_LE`), and the comparison index set
`𝒦` together with the unified `weight, contrast, lambdaWeight`.

Implementation note (per NL doc A5.5 / orchestrator dispatch). The
admissible filter `𝒦 P` enforces only the type-of-comparison side conditions
(`isFin`, `isInf`, adoption-date order). Empty-window filtering is omitted:
when a comparison window is empty the corresponding raw weight already
contains a `0` factor (`barD g · (1 - barD g)` or `q · (1 - q)`), so the
contribution to the headline identity vanishes naturally.

NL artifact:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.md`.
Source LaTeX:
`doc/basic_concepts/po/estimand_characterization/goodman_bacon_twfe_timing.tex`.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Causalean.Panel.WeightedTwoWayPanel
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.WithBot
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Goodman-Bacon Panel Algebra

This file provides the finite cohort-period primitives for the Goodman-Bacon
two-way fixed-effect decomposition. It defines staggered adoption panels,
absorbing treatment, residualized treatment, the TWFE coefficient, comparison
windows, pairwise comparison contrasts, and the raw and normalized weights for
treated-versus-never, early-versus-late, and late-versus-early comparisons. -/

namespace Causalean
namespace Panel.EstimandCharacterization
namespace StaggeredTWFEDecomposition

open Finset

/-- The [three-category comparison label](goal) classifies each admissible two-by-two comparison as [a treated cohort against a never-treated cohort](hyp:TN), [an early-adopting cohort against a later-adopting cohort before the latter adopts](hyp:EL), or [a later-adopting cohort against an early-adopting cohort after the latter adopts](hyp:LE). -/
inductive CompTag | TN | EL | LE deriving DecidableEq

/-- [A finite enumeration of the three comparison labels](goal) consists exactly of the treated-versus-never, early-versus-late, and late-versus-early categories. -/
instance : Fintype CompTag :=
  ⟨{CompTag.TN, CompTag.EL, CompTag.LE}, by intro c; cases c <;> decide⟩

/-- A staggered-adoption cohort panel: a cell-statistics record carrying, per cohort, [a
population share](hyp:p), [an adoption date — a finite period, or `⊤` for the never-treated
case](hyp:A), and [the cohort-period factual outcome mean](hyp:Y), subject to [a positive number
of periods](hyp:T_pos), [strictly positive cohort shares](hyp:p_pos), and [cohort shares summing
to one](hyp:p_sum_one). -/
structure CohortPanel (𝒢 : Type*) (T : ℕ) [Fintype 𝒢] where
  /-- Cohort population share `p_g`. -/
  p : 𝒢 → ℝ
  /-- Adoption date `A_g ∈ 𝒯 ∪ {∞}`, encoded with `⊤ = ∞`. -/
  A : 𝒢 → WithTop (Fin T)
  /-- Cohort-period factual outcome mean `Y_{gt}`. -/
  Y : 𝒢 → Fin T → ℝ
  /-- The number of periods is positive. -/
  T_pos : 0 < T
  /-- Cohort shares are strictly positive. -/
  p_pos : ∀ g, 0 < p g
  /-- Cohort shares sum to one. -/
  p_sum_one : ∑ g, p g = 1

namespace AdoptionDate

/-- For [an adoption date](hyp:a) and [a panel period](hyp:t), [the adopted-by-period condition](goal) holds exactly when the adoption date is no later than that period; a never-adopting cohort does not satisfy it. -/
def le {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop := a ≤ (t : WithTop (Fin T))

/-- For [an adoption date](hyp:a) and [a panel period](hyp:t), [the untreated-at-period condition](goal) holds exactly when the period precedes the adoption date, including every period for a never-adopting cohort. -/
def lt {T : ℕ} (a : WithTop (Fin T)) (t : Fin T) : Prop := (t : WithTop (Fin T)) < a

/-- For [an adoption date](hyp:a), [the eventually-treated condition](goal) holds exactly when the date is a finite panel period rather than the never-adopting value. -/
def isFin {T : ℕ} (a : WithTop (Fin T)) : Prop := a ≠ ⊤

/-- For [an adoption date](hyp:a), [the never-treated condition](goal) holds exactly when the date is the never-adopting value. -/
def isInf {T : ℕ} (a : WithTop (Fin T)) : Prop := a = ⊤

end AdoptionDate

variable {𝒢 : Type*} [Fintype 𝒢] [DecidableEq 𝒢] {T : ℕ}

open Classical in
/-- For [a cohort panel](hyp:P), [a cohort](hyp:g), and [a period](hyp:t), [the treatment indicator](goal) equals one if the cohort has adopted by that period and zero otherwise, and is therefore binary and absorbing.

Marked `noncomputable` because the adoption-date order predicate is taken via classical decidability. -/
noncomputable def D (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  if AdoptionDate.le (P.A g) t then 1 else 0

/-- For [a cohort panel](hyp:P) and [a cohort](hyp:g), [the cohort treatment share](goal) is that cohort's treatment indicator averaged over all panel periods. -/
noncomputable def barD (P : CohortPanel 𝒢 T) (g : 𝒢) : ℝ :=
  (T : ℝ)⁻¹ * ∑ t, D P g t

/-- For [a cohort panel](hyp:P), [the overall treatment share](goal) is the sum of each cohort's population share times its average treatment indicator. -/
noncomputable def pCohort (P : CohortPanel 𝒢 T) : ℝ :=
  ∑ g, P.p g * barD P g

/-- For [a cohort panel](hyp:P), [the cohort weight system](goal) assigns each cohort its population share and carries the panel's positivity and unit-sum conditions. -/
noncomputable def cohortWeights (P : CohortPanel 𝒢 T) :
    WeightedTwoWayPanel.UnitWeights 𝒢 :=
  ⟨P.p, P.p_pos, P.p_sum_one⟩

omit [DecidableEq 𝒢] in
/-- Goodman-Bacon's cohort treatment share is the shared unit mean. -/
theorem barD_eq_unitMean (P : CohortPanel 𝒢 T) (g : 𝒢) :
    barD P g = WeightedTwoWayPanel.unitMean (D P) g := by
  simp [barD, WeightedTwoWayPanel.unitMean]

omit [DecidableEq 𝒢] in
/-- Goodman-Bacon's overall treatment share is the shared weighted grand mean. -/
theorem pCohort_eq_grandMean (P : CohortPanel 𝒢 T) :
    pCohort P = WeightedTwoWayPanel.grandMean (cohortWeights P) (D P) := by
  simp [pCohort, WeightedTwoWayPanel.grandMean, cohortWeights, ← barD_eq_unitMean]

/-- For [a cohort panel](hyp:P), [a cohort](hyp:g), and [a period](hyp:t), [the residualized treatment](goal) is the treatment indicator minus its cohort mean and its cross-cohort period mean, plus the grand mean. -/
noncomputable def Dtilde (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) : ℝ :=
  WeightedTwoWayPanel.ddot (cohortWeights P) (D P) g t

omit [DecidableEq 𝒢] in
/-- For [a cohort panel](hyp:P) and [a cohort-period cell](hyp:g,t), [the double-demeaned
residualized treatment `Dtilde P g t` equals the original Goodman-Bacon closed form: the raw
treatment minus the cohort mean, minus the period cross-cohort mean, plus the grand mean](goal). -/
theorem Dtilde_eq (P : CohortPanel 𝒢 T) (g : 𝒢) (t : Fin T) :
    Dtilde P g t =
      D P g t - barD P g - (∑ g', P.p g' * D P g' t) + pCohort P := by
  unfold Dtilde WeightedTwoWayPanel.ddot
  rw [← barD_eq_unitMean P g, ← pCohort_eq_grandMean P]
  unfold WeightedTwoWayPanel.timeMean cohortWeights
  simp

/-- For [a cohort panel](hyp:P), [the residualized-treatment variance](goal) is the sum, over cohorts and periods, of the cohort share divided by the number of periods times squared residualized treatment. -/
noncomputable def VD (P : CohortPanel 𝒢 T) : ℝ :=
  ∑ g, ∑ t, (P.p g / (T : ℝ)) * (Dtilde P g t)^2

/-- For [a cohort panel](hyp:P), [the finite-cell population two-way-fixed-effects coefficient](goal) is the weighted covariance of residualized treatment and factual outcomes divided by residualized-treatment variance; it is defined even when that denominator is zero.

Positivity of the denominator is supplied at theorem-use time via `hVD_pos`. -/
noncomputable def betaTWFE (P : CohortPanel 𝒢 T) : ℝ :=
  (∑ g, ∑ t, (P.p g / (T : ℝ)) * Dtilde P g t * P.Y g t) / VD P

/-- For [a cohort panel](hyp:P), [a cohort](hyp:g), and [a set of periods](hyp:S), [the factual-outcome window mean](goal) is the average factual outcome for that cohort over the specified periods, and is defined as zero when the set is empty. -/
noncomputable def Ybar (P : CohortPanel 𝒢 T) (g : 𝒢) (S : Finset (Fin T)) : ℝ :=
  (S.card : ℝ)⁻¹ * ∑ t ∈ S, P.Y g t

/-! ### Comparison windows -/

open Classical in
/-- For [a cohort panel](hyp:P) and [a cohort](hyp:g), [the treated-versus-never untreated window](goal) is the set of all panel periods before that cohort's adoption date. -/
noncomputable def S0_TN (P : CohortPanel 𝒢 T) (g : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.lt (P.A g) t)

open Classical in
/-- For [a cohort panel](hyp:P) and [a cohort](hyp:g), [the treated-versus-never treated window](goal) is the set of all panel periods at or after that cohort's adoption date. -/
noncomputable def S1_TN (P : CohortPanel 𝒢 T) (g : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A g) t)

open Classical in
/-- For [a cohort panel](hyp:P) and [an early-adopting cohort](hyp:e), [the early-versus-late untreated window](goal) is the set of all periods before the early cohort's adoption date. -/
noncomputable def S0_EL (P : CohortPanel 𝒢 T) (e : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.lt (P.A e) t)

open Classical in
/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the early-versus-late treated window](goal) is the set of periods from the early cohort's adoption through the period before the late cohort's adoption. -/
noncomputable def S1_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A e) t ∧ AdoptionDate.lt (P.A ℓ) t)

open Classical in
/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the late-versus-early early-treated window](goal) is the set of periods from the early cohort's adoption through the period before the late cohort's adoption. -/
noncomputable def S0_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : Finset (Fin T) :=
  S1_EL P e ℓ

open Classical in
/-- For [a cohort panel](hyp:P) and [a late cohort](hyp:ℓ), [the late-versus-early both-treated window](goal) is the set of all periods at or after the late cohort's adoption date. -/
noncomputable def S1_LE (P : CohortPanel 𝒢 T) (ℓ : 𝒢) : Finset (Fin T) :=
  Finset.univ.filter (fun t => AdoptionDate.le (P.A ℓ) t)

/-! ### 2x2 comparison contrasts -/

/-- For [a cohort panel](hyp:P), [a treated cohort](hyp:g), and [a never-treated comparison cohort](hyp:u), [the treated-versus-never two-by-two difference-in-differences contrast](goal) is the treated cohort's outcome change between its treated and untreated windows minus the comparison cohort's change over those same windows. -/
noncomputable def Δ_TN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  (Ybar P g (S1_TN P g) - Ybar P g (S0_TN P g))
    - (Ybar P u (S1_TN P g) - Ybar P u (S0_TN P g))

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the early-versus-late two-by-two difference-in-differences contrast](goal) is the early cohort's outcome change from its untreated to its treated-before-late window minus the late cohort's change over those same windows. -/
noncomputable def Δ_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (Ybar P e (S1_EL P e ℓ) - Ybar P e (S0_EL P e))
    - (Ybar P ℓ (S1_EL P e ℓ) - Ybar P ℓ (S0_EL P e))

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the late-versus-early two-by-two difference-in-differences contrast](goal) is the late cohort's outcome change from the early-treated window to the both-treated window minus the early cohort's change over those same windows. -/
noncomputable def Δ_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (Ybar P ℓ (S1_LE P ℓ) - Ybar P ℓ (S0_LE P e ℓ))
    - (Ybar P e (S1_LE P ℓ) - Ybar P e (S0_LE P e ℓ))

/-! ### Raw and normalized weights -/

/-- For [a cohort panel](hyp:P), [a treated cohort](hyp:g), and [a never-treated cohort](hyp:u), [the treated-versus-never raw weight](goal) is the product of their population shares and the treated cohort's average treatment indicator times one minus that indicator. -/
noncomputable def lambdaTN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  P.p g * P.p u * (barD P g * (1 - barD P g))

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the treatment-share gap](goal) is the early cohort's average treatment indicator minus the late cohort's average treatment indicator. -/
noncomputable def q (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  barD P e - barD P ℓ

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the comparison splitting fraction](goal) is one minus the early cohort's treatment share divided by one minus their treatment-share gap, with the usual zero-denominator convention. -/
noncomputable def mu (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  (1 - barD P e) / (1 - q P e ℓ)

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the early-versus-late raw weight](goal) is the product of their shares, their treatment-share gap, one minus that gap, and the comparison splitting fraction. -/
noncomputable def lambdaEL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) * mu P e ℓ

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the late-versus-early raw weight](goal) is the product of their shares, their treatment-share gap, one minus that gap, and one minus the comparison splitting fraction. -/
noncomputable def lambdaLE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  P.p e * P.p ℓ * q P e ℓ * (1 - q P e ℓ) * (1 - mu P e ℓ)

open Classical in
/-- For [a cohort panel](hyp:P), [the aggregate raw-weight denominator](goal) is the sum of treated-versus-never raw weights for finite-versus-never-treated pairs and the two timing-comparison raw weights for ordered finite adoption-date pairs. -/
noncomputable def Lambda (P : CohortPanel 𝒢 T) : ℝ :=
  (∑ g, ∑ u, if AdoptionDate.isFin (P.A g) ∧ AdoptionDate.isInf (P.A u) then
              lambdaTN P g u else 0)
  + (∑ e, ∑ ℓ, if P.A e < P.A ℓ ∧ AdoptionDate.isFin (P.A ℓ) then
                lambdaEL P e ℓ + lambdaLE P e ℓ else 0)

/-- For [a cohort panel](hyp:P), [a treated cohort](hyp:g), and [a never-treated cohort](hyp:u), [the normalized treated-versus-never weight](goal) is its raw weight divided by the aggregate raw-weight denominator. -/
noncomputable def w_TN (P : CohortPanel 𝒢 T) (g u : 𝒢) : ℝ :=
  lambdaTN P g u / Lambda P

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the normalized early-versus-late weight](goal) is its raw weight divided by the aggregate raw-weight denominator. -/
noncomputable def w_EL (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  lambdaEL P e ℓ / Lambda P

/-- For [a cohort panel](hyp:P), [an early cohort](hyp:e), and [a late cohort](hyp:ℓ), [the normalized late-versus-early weight](goal) is its raw weight divided by the aggregate raw-weight denominator. -/
noncomputable def w_LE (P : CohortPanel 𝒢 T) (e ℓ : 𝒢) : ℝ :=
  lambdaLE P e ℓ / Lambda P

/-! ### Comparison index set 𝒦 and unified weight/contrast/lambdaWeight -/

/-- For [a cohort panel](hyp:P) and [a tagged ordered cohort pair](hyp:k), [the admissibility condition](goal) holds precisely when a treated-versus-never tag pairs an eventually treated cohort with a never-treated cohort, or either timing-comparison tag orders two finitely adopting cohorts by adoption date, and in every case both cohort shares are positive. -/
def admissible (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : Prop :=
  match k.1 with
  | CompTag.TN =>
      AdoptionDate.isFin (P.A k.2.1) ∧ AdoptionDate.isInf (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2
  | CompTag.EL =>
      P.A k.2.1 < P.A k.2.2 ∧ AdoptionDate.isFin (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2
  | CompTag.LE =>
      P.A k.2.1 < P.A k.2.2 ∧ AdoptionDate.isFin (P.A k.2.2)
        ∧ 0 < P.p k.2.1 ∧ 0 < P.p k.2.2

open Classical in
/-- For [a cohort panel](hyp:P), [the comparison index set](goal) is the finite set of every tagged ordered cohort pair satisfying the admissibility condition. -/
noncomputable def 𝒦 (P : CohortPanel 𝒢 T) : Finset (CompTag × 𝒢 × 𝒢) :=
  (Finset.univ : Finset (CompTag × 𝒢 × 𝒢)).filter (fun k => admissible P k)

open Classical in
/-- For [a cohort panel](hyp:P) and [a tagged ordered cohort pair](hyp:k), [the unified normalized weight](goal) is the normalized weight associated with that pair's comparison tag when the pair is admissible, and zero otherwise. -/
noncomputable def weight (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => w_TN P k.2.1 k.2.2
    | CompTag.EL => w_EL P k.2.1 k.2.2
    | CompTag.LE => w_LE P k.2.1 k.2.2
  else 0

open Classical in
/-- For [a cohort panel](hyp:P) and [a tagged ordered cohort pair](hyp:k), [the unified two-by-two contrast](goal) is the contrast associated with that pair's comparison tag when the pair is admissible, and zero otherwise. -/
noncomputable def contrast (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => Δ_TN P k.2.1 k.2.2
    | CompTag.EL => Δ_EL P k.2.1 k.2.2
    | CompTag.LE => Δ_LE P k.2.1 k.2.2
  else 0

open Classical in
/-- For [a cohort panel](hyp:P) and [a tagged ordered cohort pair](hyp:k), [the unified raw weight](goal) is the raw weight associated with that pair's comparison tag when the pair is admissible, and zero otherwise. -/
noncomputable def lambdaWeight (P : CohortPanel 𝒢 T) (k : CompTag × 𝒢 × 𝒢) : ℝ :=
  if admissible P k then
    match k.1 with
    | CompTag.TN => lambdaTN P k.2.1 k.2.2
    | CompTag.EL => lambdaEL P k.2.1 k.2.2
    | CompTag.LE => lambdaLE P k.2.1 k.2.2
  else 0

end StaggeredTWFEDecomposition
end Panel.EstimandCharacterization
end Causalean
