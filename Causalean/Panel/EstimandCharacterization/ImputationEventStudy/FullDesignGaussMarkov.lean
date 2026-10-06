/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Full-design OLS Gauss–Markov inequality under spherical errors

This file applies `linearCombination_variance_spherical_le_of_colSpan` to
the event-study design `designFull` (a treated-cell indicator block stacked with
the covariate block). It compares the resulting full-rank OLS weight with any
algebraically unbiased linear weight. It does not identify that OLS weight with
the panel's `ImputationWeights` or `psiImp` representation.
-/

module
public import Causalean.Panel.EstimandCharacterization.ImputationEventStudy.Imputation
public import Causalean.Stat.LinearModel.GaussMarkov.BLUE
public import Causalean.Stat.LinearModel.GaussMarkov.OLS
public import Causalean.Stat.Weighted.IndicatorSpan

/-! # Full-Design OLS Gauss–Markov Variance Comparison

This file builds the finite BJS full event-study design matrix and proves that
its full-rank OLS weights attain no larger variance than any algebraically
unbiased linear estimator under spherical cell-outcome errors. No bridge to the
panel's concrete imputation-weight representation is proved here. -/

@[expose] public section

namespace Causalean.Panel.EstimandCharacterization.ImputationEventStudy

open Matrix MeasureTheory ProbabilityTheory Causalean.Stat.GaussMarkov

variable {Treated Untreated Regressor : Type*}
  [Fintype Treated] [Fintype Untreated] [Fintype Regressor]
  [DecidableEq Treated] [DecidableEq Regressor]

namespace BJSPanel

/-- For [a BJS event-study panel with finite treated cells, untreated cells, and
regressors](hyp:P), the [full event-study design matrix](goal) has one row for
each observed cell and one column for each treated-cell effect or regressor. A
treated-cell row has its own effect indicator and regressor row, whereas an
untreated-cell row has zero effect indicators and its untreated-cell regressor
row.

Rows are observed cells, and columns stack treated-cell effects with covariates. -/
def designFull (P : BJSPanel Treated Untreated Regressor) :
    Matrix (Treated ⊕ Untreated) (Treated ⊕ Regressor) ℝ :=
  Matrix.of (Sum.elim
    (fun c => Sum.elim (fun d => if c = d then (1 : ℝ) else 0) (fun r => P.qT c r))
    (fun u => Sum.elim (fun _ => (0 : ℝ)) (fun r => P.qU u r)))

/-- For [a BJS event-study panel with finite treated cells, untreated cells, and
regressors](hyp:P), the [target functional in full-design coordinates](goal)
assigns the panel's target weight to each treated-cell-effect coordinate and
zero to every regressor coordinate.

This is the target vector used with the full design matrix. -/
def cFull (P : BJSPanel Treated Untreated Regressor) : Treated ⊕ Regressor → ℝ :=
  Sum.elim P.a (fun _ => 0)

/-- For [a linear estimator of a BJS event-study panel with finite cell
sets](hyp:L), the [weight vector over all observed cells](goal) equals its
treated-cell weights on treated cells and its untreated-cell weights on
untreated cells. -/
def weightOf {P : BJSPanel Treated Untreated Regressor} (L : P.LinearEstimator) :
    Treated ⊕ Untreated → ℝ :=
  Sum.elim L.vT L.vU

omit [DecidableEq Regressor] in
/-- **Unbiasedness bridge.** If a linear estimator is unbiased for every `tau`, its
weight vector satisfies the design constraint `w ᵥ* designFull = cFull`, capturing
both `vT = a` and the nuisance left-null constraint. -/
lemma weightOf_vecMul_designFull {P : BJSPanel Treated Untreated Regressor}
    (L : P.LinearEstimator) (h : L.unbiasedForAllTau) :
    weightOf L ᵥ* designFull P = cFull P := by
  classical
  funext j
  have hsplit : (weightOf L ᵥ* designFull P) j
      = (∑ c : Treated, weightOf L (Sum.inl c) * designFull P (Sum.inl c) j)
        + ∑ u : Untreated, weightOf L (Sum.inr u) * designFull P (Sum.inr u) j := by
    simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
  rw [hsplit]
  cases j with
  | inl d =>
    simp only [weightOf, designFull, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
      cFull, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      Finset.sum_const_zero, add_zero]
    exact L.vT_eq_a h d
  | inr r =>
    simp only [weightOf, designFull, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, cFull]
    rw [show (∑ c : Treated, L.vT c * P.qT c r)
        = ∑ c : Treated, P.a c * P.qT c r from
      Finset.sum_congr rfl (fun c _ => by rw [L.vT_eq_a h c])]
    exact L.nuisance_coord h r

/-- **Full-design OLS Gauss–Markov inequality under spherical errors.** For a BJS
event-study panel `P` and a family of cell outcomes `Y` on a probability space,
suppose [each cell outcome is square-integrable](hyp:hY), [the cell outcomes
form a spherical family with common variance `σ²` — equal variances and zero
cross-covariances](hyp:hsph), and [the full event-study design matrix
`designFull P` has full column rank](hyp:hRank). Then for [any linear
estimator `L` unbiased for every value of the treatment-effect
vector](hyp:hL), [the variance of the OLS estimator built from
`designFull P` and the target functional `cFull P` is no larger than the
variance of `L`](goal). This statement does not identify the OLS weight with
`ImputationWeights` or `psiImp`. -/
theorem bjs_full_design_ols_min_variance_spherical
    {P : BJSPanel Treated Untreated Regressor}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Treated ⊕ Untreated → Ω → ℝ) (hY : ∀ i, MemLp (Y i) 2 μ)
    {σ : ℝ} (hsph : SphericalFamily Y μ σ)
    (hRank : IsUnit ((designFull P)ᵀ * designFull P).det)
    (L : P.LinearEstimator) (hL : L.unbiasedForAllTau) :
    Var[fun ω => ∑ i, olsWeight (designFull P) (cFull P) i * Y i ω; μ]
      ≤ Var[fun ω => ∑ i, weightOf L i * Y i ω; μ] := by
  exact linearCombination_variance_spherical_le_of_colSpan Y hY hsph
    (olsWeight_mem_colSpan (designFull P) (cFull P))
    (olsWeight_vecMul_eq (cFull P) hRank)
    (weightOf_vecMul_designFull L hL)

/-! ### Fixed-effect block ↔ panel `IndicatorSpan`

The treated-cell fixed-effect block of `designFull` (the τ-columns) is exactly the
panel indicator-span substrate `Causalean.Stat.Weighted.IndicatorSpan`: each
τ-column is the cell indicator of the treated-cell classifier on observed cells.
This connects the event-study design to the panel FE/indicator-span layer; it is
additive — the variance comparison above stays on the finite Gauss-Markov substrate
(§13gm), the correct home for the variance argument. -/

open Causalean.Stat.Weighted in
/-- The [treated-cell classifier](goal) maps each treated observed cell to its
own treated-cell label and maps every untreated observed cell to no label.

Its nonempty-label indicators are the treated-cell-effect columns of the full design matrix. -/
def treatedClassifier : (Treated ⊕ Untreated) → Option Treated :=
  Sum.elim (fun c => some c) (fun _ => none)

open Causalean.Stat.Weighted in
omit [DecidableEq Regressor] in
/-- Each treated-cell fixed-effect column of `designFull` is the panel cell
indicator of `treatedClassifier`. -/
lemma designFull_col_eq_cellIndicator (P : BJSPanel Treated Untreated Regressor)
    (d : Treated) :
    (fun i => designFull P i (Sum.inl d))
      = cellIndicator (treatedClassifier (Untreated := Untreated)) (some d) := by
  funext i
  cases i with
  | inl c =>
    simp [designFull, treatedClassifier, cellIndicator]
  | inr u =>
    simp [designFull, treatedClassifier, cellIndicator]

open Causalean.Stat.Weighted in
omit [DecidableEq Regressor] in
/-- The treated-cell fixed-effect block of `designFull` lies in the panel
`IndicatorSpan` of the treated-cell classifier: the BJS event-study FE design is
the panel indicator-span substrate. -/
lemma designFull_col_mem_indicatorSpan (P : BJSPanel Treated Untreated Regressor)
    (d : Treated) :
    (fun i => designFull P i (Sum.inl d))
      ∈ indicatorSpan (treatedClassifier (Untreated := Untreated)) := by
  rw [designFull_col_eq_cellIndicator]
  exact cellIndicator_mem_indicatorSpan _ _

end BJSPanel

end Causalean.Panel.EstimandCharacterization.ImputationEventStudy
