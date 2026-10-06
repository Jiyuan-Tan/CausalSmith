/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.OLSAsymptotics.Wald

/-! # HC1 studentization and Wald inference for OLS

This module supplies the degrees-of-freedom-corrected HC1 t statistic in both
true-parameter and null-value forms, together with its standard-normal limit
and the asymptotic coverage of the corresponding two-sided Wald interval.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology

noncomputable section

variable {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
the [HC1 standard error for the rescaled contrast](goal) is `√(c′V̂₁c)`. -/
def olsHC1ContrastSE
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (olsContrastVariance (olsHC1 S x y n ω) c)

private def olsHC1Studentized
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  olsContrastRescaled S x y c n ω / olsHC1ContrastSE S x y c n ω

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
the [HC1 heteroskedasticity-robust t statistic centered at the true
population contrast](goal) is `(c′β̂ₙ-c′β)/√(c′V̂₁c/n)`. -/
def olsHC1TStatistic
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) : ℝ :=
  (inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y)) /
    Real.sqrt (olsContrastVariance (olsHC1 S x y n ω) c / (n : ℝ))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a hypothesized null value](hyp:r), [a sample
size](hyp:n), and [a sample outcome](hyp:ω), the [HC1 t statistic for the null
`c′β = r`](goal) is `(c′β̂ₙ-r)/√(c′V̂₁c/n)`. -/
def olsHC1NullTStatistic
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (r : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (inner ℝ c (olsBetaHat S x y n ω) - r) /
    Real.sqrt (olsContrastVariance (olsHC1 S x y n ω) c / (n : ℝ))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), [a sample size](hyp:n), and
[a sample outcome](hyp:ω), the [HC1 Wald half-width](goal) is
`z√(c′V̂₁c/n)`. -/
def olsHC1WaldRadius
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  z * Real.sqrt (olsContrastVariance (olsHC1 S x y n ω) c / (n : ℝ))

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), [a sample size](hyp:n), and
[a sample outcome](hyp:ω), the [two-sided HC1 Wald interval covers the
population contrast](goal) exactly when `c′β` lies between
`c′β̂ₙ ± z√(c′V̂₁c/n)`. -/
def olsHC1WaldCovers
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) (ω : Ω) : Prop :=
  inner ℝ c (olsBeta P x y) ∈ Set.Icc
    (inner ℝ c (olsBetaHat S x y n ω) - olsHC1WaldRadius S x y c z n ω)
    (inner ℝ c (olsBetaHat S x y n ω) + olsHC1WaldRadius S x y c z n ω)

/-- Given [an iid sample](hyp:S), [regressors](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a critical value](hyp:z), and [a sample size](hyp:n),
the [true coverage probability of the two-sided HC1 Wald interval](goal) is
the sampling probability that `c′β` lies between its two endpoints. -/
def olsHC1WaldCoverageProbability
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) (n : ℕ) : ℝ :=
  μ.real {ω | olsHC1WaldCovers S x y c z n ω}

/-- Given [an iid sample](hyp:S), [a regressor](hyp:x), [an outcome](hyp:y),
[a contrast](hyp:c), [a sample size](hyp:n), and [a sample outcome](hyp:ω),
[centering the null-value HC1 statistic at the true population contrast
recovers the true-value statistic](goal). -/
theorem olsHC1NullTStatistic_trueValue
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (n : ℕ) (ω : Ω) :
    olsHC1NullTStatistic S x y c (inner ℝ c (olsBeta P x y)) n ω =
      olsHC1TStatistic S x y c n ω := by
  rfl

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), and [a sample
size](hyp:n), [the HC1 contrast-variance estimate is measurable](goal). -/
@[fun_prop]
theorem measurable_olsHC1Contrast
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    Measurable (fun ω => olsContrastVariance (olsHC1 S x y n ω) c) := by
  have h0 := measurable_olsHC0Contrast S hx hy c n
  convert h0.const_mul ((n : ℝ) / ((n : ℝ) - Fintype.card K)) using 1
  funext ω
  simp only [olsHC1, olsContrastVariance, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

@[fun_prop]
private theorem aemeasurable_olsHC1Studentized
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    AEMeasurable (olsHC1Studentized S x y c n) μ := by
  apply AEMeasurable.div
  · exact aemeasurable_olsContrastRescaled S hx hy c n
  · exact (Real.continuous_sqrt.measurable.comp
      (measurable_olsHC1Contrast S hx hy c n)).aemeasurable

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), and [a sample
size](hyp:n), [the true-value HC1 t statistic is measurable](goal). -/
@[fun_prop]
theorem measurable_olsHC1TStatistic
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K) (n : ℕ) :
    Measurable (olsHC1TStatistic S x y c n) := by
  apply Measurable.div
  · exact ((innerSL ℝ c).measurable.comp
      (measurable_olsBetaHat S hx hy n)).sub
        (measurable_const : Measurable (fun _ : Ω => inner ℝ c (olsBeta P x y)))
  · exact (Real.continuous_sqrt.measurable.comp
      ((measurable_olsHC1Contrast S hx hy c n).div_const (n : ℝ)))

/-- Given [an iid sample](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [a contrast](hyp:c), [a null value](hyp:r), and
[a sample size](hyp:n), [the null-value HC1 t statistic is measurable](goal). -/
@[fun_prop]
theorem measurable_olsHC1NullTStatistic
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K)
    (r : ℝ) (n : ℕ) : Measurable (olsHC1NullTStatistic S x y c r n) := by
  apply Measurable.div
  · exact ((innerSL ℝ c).measurable.comp
      (measurable_olsBetaHat S hx hy n)).sub_const r
  · exact (Real.continuous_sqrt.measurable.comp
      ((measurable_olsHC1Contrast S hx hy c n).div_const (n : ℝ)))

private theorem measurableSet_olsHC1WaldCovers
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) (c : EuclideanSpace ℝ K)
    (z : ℝ) (n : ℕ) :
    MeasurableSet {ω | olsHC1WaldCovers S x y c z n ω} := by
  have hest : Measurable (fun ω => inner ℝ c (olsBetaHat S x y n ω)) :=
    (innerSL ℝ c).measurable.comp (measurable_olsBetaHat S hx hy n)
  have hrad : Measurable (olsHC1WaldRadius S x y c z n) := by
    exact (Real.continuous_sqrt.measurable.comp
      ((measurable_olsHC1Contrast S hx hy c n).div_const (n : ℝ))).const_mul z
  exact (measurableSet_le (hest.sub hrad) measurable_const).inter
    (measurableSet_le measurable_const (hest.add hrad))

private theorem olsHC1Studentized_tendsto [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c) :
    Tendsto_dist (olsHC1Studentized S x y c) (gaussianMeasure 0 1) μ
      (aemeasurable_olsHC1Studentized S hx hy c) := by
  let v := olsContrastVariance (olsAsymptoticCovariance P x y) c
  let σ := Real.sqrt v
  have hσpos : 0 < σ := Real.sqrt_pos.mpr hpos
  have hσsq : σ ^ 2 = v := Real.sq_sqrt hpos.le
  have hnum : Tendsto_dist (olsContrastRescaled S x y c)
      (gaussianMeasure 0 (σ ^ 2)) μ
      (aemeasurable_olsContrastRescaled S hx hy c) := by
    rw [hσsq]
    exact olsContrast_tendsto_normal S hx hy hraw hQ c
  have hse : Tendsto_inProb (olsHC1ContrastSE S x y c) (fun _ => σ) μ := by
    exact tendstoInMeasure_comp_continuousAt_const Real.continuous_sqrt.continuousAt
      (olsHC1_contrast_tendsto_inProb S hx hy hraw hQ c)
  exact Tendsto_dist.div_tendsto_inProb_gaussian hσpos
    (aemeasurable_olsContrastRescaled S hx hy c) hnum hse
    (aemeasurable_olsHC1Studentized S hx hy c)

private theorem olsHC1TStatistic_eq_studentized
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) {n : ℕ} (hn : 0 < n) (ω : Ω) :
    olsHC1TStatistic S x y c n ω = olsHC1Studentized S x y c n ω := by
  let v := olsContrastVariance (olsHC1 S x y n ω) c
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases hv : 0 ≤ v
  · rw [olsHC1TStatistic, olsHC1Studentized, olsContrastRescaled,
      olsHC1ContrastSE]
    rw [Real.sqrt_div hv]
    have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 hnR).ne'
    field_simp
    ring
  · have hv' : v ≤ 0 := le_of_not_ge hv
    simp [olsHC1TStatistic, olsHC1Studentized, olsContrastRescaled,
      olsHC1ContrastSE, v, Real.sqrt_eq_zero_of_nonpos hv',
      Real.sqrt_eq_zero_of_nonpos
        (div_nonpos_of_nonpos_of_nonneg hv' hnR.le)]

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram matrix](hyp:hQ), [a
contrast vector](hyp:c), and [a nondegenerate contrast variance](hyp:hpos),
[the true-value HC1 t statistic converges in distribution to the standard
normal law](goal). -/
theorem olsHC1TStatistic_tendsto_normal [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c) :
    Tendsto_dist (olsHC1TStatistic S x y c) (gaussianMeasure 0 1) μ
      (fun n => (measurable_olsHC1TStatistic S hx hy c n).aemeasurable) := by
  have hstud : Tendsto_dist (olsHC1Studentized S x y c) (gaussianMeasure 0 1) μ
      (aemeasurable_olsHC1Studentized S hx hy c) :=
    olsHC1Studentized_tendsto S hx hy hraw hQ c hpos
  apply Tendsto_dist.congr_ae
    (aemeasurable_olsHC1Studentized S hx hy c)
    (fun n => (measurable_olsHC1TStatistic S hx hy c n).aemeasurable) hstud
  filter_upwards [eventually_gt_atTop 0] with n hn
  filter_upwards with ω
  exact (olsHC1TStatistic_eq_studentized S x y c hn ω).symm

private theorem olsHC1WaldCovers_iff_statistic
    (S : IIDSample Ω X μ P) (x : X → EuclideanSpace ℝ K) (y : X → ℝ)
    (c : EuclideanSpace ℝ K) (z : ℝ) {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hv : 0 < olsContrastVariance (olsHC1 S x y n ω) c) :
    olsHC1WaldCovers S x y c z n ω ↔
      olsHC1TStatistic S x y c n ω ∈ Set.Icc (-z) z := by
  let d := inner ℝ c (olsBetaHat S x y n ω) - inner ℝ c (olsBeta P x y)
  let s := Real.sqrt (olsContrastVariance (olsHC1 S x y n ω) c / (n : ℝ))
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hs : 0 < s := Real.sqrt_pos.2 (div_pos hv hnR)
  change (inner ℝ c (olsBetaHat S x y n ω) - z * s ≤ inner ℝ c (olsBeta P x y) ∧
      inner ℝ c (olsBeta P x y) ≤ inner ℝ c (olsBetaHat S x y n ω) + z * s) ↔
    -z ≤ d / s ∧ d / s ≤ z
  constructor
  · rintro ⟨hl, hu⟩
    constructor
    · rw [le_div_iff₀ hs]
      dsimp [d]
      linarith
    · rw [div_le_iff₀ hs]
      dsimp [d]
      linarith
  · rintro ⟨hl, hu⟩
    rw [le_div_iff₀ hs] at hl
    rw [div_le_iff₀ hs] at hu
    dsimp [d] at hl hu
    constructor <;> linarith

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram matrix](hyp:hQ), [a
contrast](hyp:c) with [positive asymptotic variance](hyp:hpos), and [a
positive critical value](hyp:hz), the [coverage probability of the HC1
interval `c′β̂ₙ ± z√(c′V̂₁c/n)` converges to the standard-normal probability
of `[-z,z]`](goal). -/
theorem olsHC1_wald_coverage [IsProbabilityMeasure μ] [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c)
    {z : ℝ} (hz : 0 < z) :
    Tendsto (olsHC1WaldCoverageProbability S x y c z) atTop
      (𝓝 ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal) := by
  let f : ℕ → Ω → ℝ := fun n ω => olsContrastVariance (olsHC1 S x y n ω) c
  let v : ℝ := olsContrastVariance (olsAsymptoticCovariance P x y) c
  let A : ℕ → Set Ω := fun n => {ω | olsHC1WaldCovers S x y c z n ω}
  let B : ℕ → Set Ω := fun n => {ω | olsHC1TStatistic S x y c n ω ∈ Set.Icc (-z) z}
  let D : ℕ → Set Ω := fun n => {ω | f n ω ≤ 0}
  have hf : TendstoInMeasure μ f atTop (fun _ => v) :=
    olsHC1_contrast_tendsto_inProb S hx hy hraw hQ c
  have herr : Tendsto (fun n => μ.real {ω | v ≤ ‖f n ω - v‖}) atTop (𝓝 0) :=
    (tendstoInMeasure_iff_measureReal_norm.mp hf) v hpos
  have hD_le : ∀ n, μ.real (D n) ≤ μ.real {ω | v ≤ ‖f n ω - v‖} := by
    intro n
    apply measureReal_mono
    · intro ω hω
      change v ≤ ‖f n ω - v‖
      rw [Real.norm_eq_abs, abs_of_nonpos]
      · change f n ω ≤ 0 at hω
        change 0 < v at hpos
        linarith
      · exact sub_nonpos.mpr (hω.trans hpos.le)
    · exact measure_ne_top _ _
  have hD : Tendsto (fun n => μ.real (D n)) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds herr
      (Eventually.of_forall fun _ => measureReal_nonneg)
      (Eventually.of_forall hD_le)
  have hA : ∀ n, MeasurableSet (A n) := fun n =>
    measurableSet_olsHC1WaldCovers S hx hy c z n
  have hB : ∀ n, MeasurableSet (B n) := fun n =>
    measurableSet_Icc.preimage (measurable_olsHC1TStatistic S hx hy c n)
  have hsymm : ∀ᶠ n in atTop, symmDiff (A n) (B n) ⊆ D n := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    intro ω hω
    rw [Set.mem_symmDiff] at hω
    by_contra hnot
    have hvhat : 0 < f n ω := lt_of_not_ge hnot
    have heq := olsHC1WaldCovers_iff_statistic S x y c z hn ω hvhat
    rcases hω with ⟨ha, hnb⟩ | ⟨hb, hna⟩
    · exact hnb (heq.mp ha)
    · exact hna (heq.mpr hb)
  have hgap_abs : Tendsto
      (fun n => |olsHC1WaldCoverageProbability S x y c z n - μ.real (B n)|)
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hD
    · exact Eventually.of_forall fun _ => abs_nonneg _
    · filter_upwards [hsymm] with n hn
      calc
        |olsHC1WaldCoverageProbability S x y c z n - μ.real (B n)| =
            |μ.real (A n) - μ.real (B n)| := by rfl
        _ ≤ μ.real (symmDiff (A n) (B n)) :=
          abs_measureReal_sub_le_measureReal_symmDiff (hA n).nullMeasurableSet
            (hB n).nullMeasurableSet
        _ ≤ μ.real (D n) := measureReal_mono hn (measure_ne_top _ _)
  have hbridge : Tendsto
      (fun n => olsHC1WaldCoverageProbability S x y c z n - μ.real (B n))
      atTop (𝓝 0) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hgap_abs
  have hstat : Tendsto_dist (olsHC1TStatistic S x y c) (gaussianMeasure 0 1) μ
      (fun n => (measurable_olsHC1TStatistic S hx hy c n).aemeasurable) :=
    olsHC1TStatistic_tendsto_normal S hx hy hraw hQ c hpos
  exact Tendsto_dist.wald_coverage
    (fun n => (measurable_olsHC1TStatistic S hx hy c n).aemeasurable) hstat hz
    (olsHC1WaldCoverageProbability S x y c z)
    (by simpa [B, measureReal_def] using hbridge)

/-- Under [iid sampling](hyp:S), [measurable regressors](hyp:hx), [a
measurable outcome](hyp:hy), [integrable OLS raw moments through degree
four](hyp:hraw), [a positive-definite population Gram matrix](hyp:hQ), [a
contrast](hyp:c) with [positive asymptotic variance](hyp:hpos), [a positive
critical value](hyp:hz), and [standard-normal calibration to `1-α`](hyp:hcal),
the [HC1 Wald interval has asymptotic coverage `1-α`](goal). -/
theorem olsHC1_wald_coverage_one_sub [IsProbabilityMeasure μ]
    [IsProbabilityMeasure P]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K)
    (hpos : 0 < olsContrastVariance (olsAsymptoticCovariance P x y) c)
    {α z : ℝ} (hz : 0 < z)
    (hcal : ((gaussianMeasure 0 1) (Set.Icc (-z) z)).toReal = 1 - α) :
    Tendsto (olsHC1WaldCoverageProbability S x y c z) atTop (𝓝 (1 - α)) := by
  rw [← hcal]
  exact olsHC1_wald_coverage S hx hy hraw hQ c hpos hz

end

end Causalean.Stat
