/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.LinearModel.OLSAsymptotics.Basic

/-! # Consistency of OLS and the HC0 sandwich covariance

This module obtains both consistency results from one finite-dimensional weak
law for raw moments.  Matrix inversion is used only through its continuity at
the positive-definite population design matrix.
-/

public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal

noncomputable section

variable {Ω X K : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [Fintype K] [DecidableEq K] {μ : Measure Ω} {P : Measure X}

/-- For [measurable regressors](hyp:hx) and [a measurable outcome](hyp:hy),
the [degree-at-most-four OLS raw-moment vector is measurable](goal). -/
@[fun_prop]
theorem measurable_olsRawMoment {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (olsRawMoment x y) := by
  unfold olsRawMoment
  refine measurable_pi_lambda _ fun a => Finset.measurable_prod _ fun t _ => ?_
  cases hat : a t with
  | none => simp [olsAugmented]
  | some q =>
      cases q with
      | none => simpa [olsAugmented, hat] using hy
      | some i =>
          simpa [olsAugmented, hat, Function.comp_def] using
            (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : K => ℝ) i).measurable.comp hx

/-- Under [a finite population law](hyp:P), [measurable regressors](hyp:hx),
[a measurable outcome](hyp:hy), and [uniform bounds on the regressors and
outcome](hyp:hx_bdd,hy_bdd), the [degree-at-most-four OLS raw-moment vector is
integrable](goal). -/
@[fun_prop]
theorem integrable_olsRawMoment [IsFiniteMeasure P]
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hx_bdd : ∃ C, ∀ z, ‖x z‖ ≤ C)
    (hy_bdd : ∃ C, ∀ z, |y z| ≤ C) :
    Integrable (olsRawMoment x y) P := by
  rcases hx_bdd with ⟨Cx, hx_bdd⟩
  rcases hy_bdd with ⟨Cy, hy_bdd⟩
  let B : ℝ := 1 + |Cx| + |Cy|
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hCxB : Cx ≤ B :=
    (le_abs_self Cx).trans (by dsimp [B]; linarith [abs_nonneg Cy])
  have hCyB : Cy ≤ B :=
    (le_abs_self Cy).trans (by dsimp [B]; linarith [abs_nonneg Cx])
  have haug : ∀ z a, |olsAugmented x y z a| ≤ B := by
    intro z a
    cases a with
    | none =>
        simp only [olsAugmented, abs_one]
        dsimp [B]
        nlinarith [abs_nonneg Cx, abs_nonneg Cy]
    | some q =>
        cases q with
        | none => exact (hy_bdd z).trans hCyB
        | some i =>
            calc
              |x z i| = ‖x z i‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖x z‖ := PiLp.norm_apply_le (p := (2 : ℝ≥0∞)) (x z) i
              _ ≤ Cx := hx_bdd z
              _ ≤ B := hCxB
  apply Integrable.of_eval
  intro a
  refine Integrable.of_bound
    (((measurable_pi_apply a).comp (measurable_olsRawMoment hx hy)).aestronglyMeasurable)
    (B ^ 4) ?_
  filter_upwards with z
  unfold olsRawMoment
  rw [Real.norm_eq_abs, Finset.abs_prod]
  calc
    ∏ t : Fin 4, |olsAugmented x y z (a t)|
        ≤ ∏ _t : Fin 4, B :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => haug z (a t))
    _ = B ^ 4 := by simp

/-- If [a random-element sequence converges in measure to a constant](hyp:h)
and [a map is continuous at that constant](hyp:hg), then [the mapped sequence
converges in measure to the mapped constant](goal). -/
theorem tendstoInMeasure_comp_continuousAt_const
    {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    {Yn : ℕ → Ω → E} {c : E} {g : E → F}
    (hg : ContinuousAt g c)
    (h : TendstoInMeasure μ Yn atTop (fun _ => c)) :
    TendstoInMeasure μ (fun n ω => g (Yn n ω)) atTop (fun _ => g c) := by
  rw [tendstoInMeasure_iff_dist] at h ⊢
  intro ε hε
  have hev : ∀ᶠ y in 𝓝 c, dist (g y) (g c) < ε :=
    (Metric.tendsto_nhds.mp hg) ε hε
  rcases Metric.eventually_nhds_iff.mp hev with ⟨η, hηpos, hη⟩
  have ht := h η hηpos
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  exact le_of_not_gt fun hd => not_le_of_gt (hη hd) hω

private theorem continuous_olsQFromMoments :
    Continuous (fun M : OLSMoment K => olsQFromMoments M) := by
  unfold olsQFromMoments
  exact continuous_pi fun i => continuous_pi fun j => continuous_apply _

private theorem continuous_olsRFromMoments :
    Continuous (fun M : OLSMoment K => olsRFromMoments M) := by
  unfold olsRFromMoments
  exact continuous_pi fun i => continuous_apply _

private theorem continuousAt_olsBetaFromMoments
    (M : OLSMoment K) (hdet : (olsQFromMoments M).det ≠ 0) :
    ContinuousAt (fun N : OLSMoment K => olsBetaFromMoments N) M := by
  have hinv : ContinuousAt (fun N : OLSMoment K => (olsQFromMoments N)⁻¹) M := by
    apply (continuousAt_matrix_inv (olsQFromMoments M)
      (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))).comp
    exact continuous_olsQFromMoments.continuousAt
  unfold olsBetaFromMoments
  change ContinuousAt (fun N => WithLp.toLp 2
    ((olsQFromMoments N)⁻¹ *ᵥ olsRFromMoments N)) M
  have hmul : Continuous
      (fun p : Matrix K K ℝ × (K → ℝ) => p.1 *ᵥ p.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  exact (PiLp.continuous_toLp (2 : ℝ≥0∞) (fun _ : K => ℝ)).continuousAt.comp
    (hmul.continuousAt.comp (hinv.prodMk continuous_olsRFromMoments.continuousAt))

private theorem continuous_olsMeatFromMoments :
    Continuous (fun p : OLSMoment K × EuclideanSpace ℝ K =>
      olsMeatFromMoments p.1 p.2) := by
  unfold olsMeatFromMoments
  exact continuous_matrix fun i j => by fun_prop

private theorem continuousAt_olsHC0FromMoments
    (M : OLSMoment K) (hdet : (olsQFromMoments M).det ≠ 0) :
    ContinuousAt (fun N : OLSMoment K =>
      (olsQFromMoments N)⁻¹ *
        olsMeatFromMoments N (olsBetaFromMoments N) *
        (olsQFromMoments N)⁻¹) M := by
  have hinv : ContinuousAt (fun N : OLSMoment K => (olsQFromMoments N)⁻¹) M := by
    apply (continuousAt_matrix_inv (olsQFromMoments M)
      (NormedRing.inverse_continuousAt (Units.mk0 _ hdet))).comp
    exact continuous_olsQFromMoments.continuousAt
  have hb := continuousAt_olsBetaFromMoments M hdet
  have hmeat : ContinuousAt
      (fun N : OLSMoment K => olsMeatFromMoments N (olsBetaFromMoments N)) M :=
    continuous_olsMeatFromMoments.continuousAt.comp (continuousAt_id.prodMk hb)
  exact (hinv.mul hmeat).mul hinv

private theorem ols_population_det_ne_zero
    {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hQ : (olsQ P x y).PosDef) :
    (olsQFromMoments (olsPopulationMoments P x y)).det ≠ 0 := by
  have hu : IsUnit (olsQ P x y) := hQ.isUnit
  have hudet : IsUnit (olsQ P x y).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hu
  simpa [olsQ] using hudet.ne_zero

/-- **OLS consistency.** Under [iid sampling](hyp:S), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population design second
moment](hyp:hQ), for every [positive tolerance](hyp:hε), [the probability that the OLS
coefficient is farther than that tolerance from the projection coefficient
converges to zero](goal). -/
theorem olsBetaHat_consistent [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => μ {ω | ε < ‖olsBetaHat S x y n ω - olsBeta P x y‖})
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let M₀ := olsPopulationMoments P x y
  have hM := S.sampleMeanVec_tendstoInMeasure
    (measurable_olsRawMoment hx hy)
    hraw
  have hb := continuousAt_olsBetaFromMoments M₀ (ols_population_det_ne_zero hQ)
  have hg : ContinuousAt
      (fun M : OLSMoment K => ‖olsBetaFromMoments M - olsBetaFromMoments M₀‖) M₀ :=
    continuous_norm.continuousAt.comp (hb.sub continuousAt_const)
  have hnorm := tendstoInMeasure_comp_continuousAt_const hg hM
  rw [tendstoInMeasure_iff_norm] at hnorm
  have ht := hnorm ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => zero_le) ?_
  intro n
  apply measure_mono
  intro ω hω
  simpa [M₀, olsBetaHat, olsEmpiricalMoments, olsBeta, olsPopulationMoments,
    Real.norm_eq_abs, abs_of_nonneg] using le_of_lt hω

/-- **HC0 consistency.** For [an iid sample](hyp:S), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population design second
moment](hyp:hQ), at every [pair of coordinates](hyp:i,j), the [corresponding
HC0 sandwich entry converges in probability to the entry of `Q⁻¹ΩQ⁻¹`](goal). -/
theorem olsHC0_entry_tendsto_inProb [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (i j : K) :
    Tendsto_inProb (fun n ω => olsHC0 S x y n ω i j)
      (fun _ => olsAsymptoticCovariance P x y i j) μ := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hM := S.sampleMeanVec_tendstoInMeasure
    (measurable_olsRawMoment hx hy)
    hraw
  have hcont := continuousAt_olsHC0FromMoments
    (olsPopulationMoments P x y) (ols_population_det_ne_zero hQ)
  have hentry : ContinuousAt (fun N : OLSMoment K =>
      ((olsQFromMoments N)⁻¹ *
        olsMeatFromMoments N (olsBetaFromMoments N) *
        (olsQFromMoments N)⁻¹) i j) (olsPopulationMoments P x y) :=
    (continuousAt_apply j _).comp ((continuousAt_apply i _).comp hcont)
  change TendstoInMeasure μ (fun n ω => olsHC0 S x y n ω i j) atTop
    (fun _ => olsAsymptoticCovariance P x y i j)
  simpa [olsHC0, olsHC0Meat, olsQHat, olsBetaHat, olsEmpiricalMoments,
    olsAsymptoticCovariance, olsOmega, olsQ, olsBeta] using
      tendstoInMeasure_comp_continuousAt_const hentry hM

/-- **HC0 contrast-variance consistency.** For [an iid sample](hyp:S),
[measurable regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable
OLS raw moments through degree four](hyp:hraw), [a positive-definite
population design second moment](hyp:hQ), and [a contrast vector](hyp:c), the
[HC0 estimate of `c′Vc` converges in probability to `c′Vc`](goal). -/
theorem olsHC0_contrast_tendsto_inProb [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K) :
    Tendsto_inProb
      (fun n ω => olsContrastVariance (olsHC0 S x y n ω) c)
      (fun _ => olsContrastVariance (olsAsymptoticCovariance P x y) c) μ := by
  letI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hM := S.sampleMeanVec_tendstoInMeasure
    (measurable_olsRawMoment hx hy)
    hraw
  have hcont := continuousAt_olsHC0FromMoments
    (olsPopulationMoments P x y) (ols_population_det_ne_zero hQ)
  have hcontrast : ContinuousAt (fun N : OLSMoment K =>
      olsContrastVariance
        ((olsQFromMoments N)⁻¹ *
          olsMeatFromMoments N (olsBetaFromMoments N) *
          (olsQFromMoments N)⁻¹) c) (olsPopulationMoments P x y) := by
    have hc : Continuous (fun V : Matrix K K ℝ => olsContrastVariance V c) := by
      unfold olsContrastVariance
      fun_prop
    exact hc.continuousAt.comp hcont
  change TendstoInMeasure μ
    (fun n ω => olsContrastVariance (olsHC0 S x y n ω) c) atTop
    (fun _ => olsContrastVariance (olsAsymptoticCovariance P x y) c)
  simpa [olsHC0, olsHC0Meat, olsQHat, olsBetaHat, olsEmpiricalMoments,
    olsAsymptoticCovariance, olsOmega, olsQ, olsBeta] using
      tendstoInMeasure_comp_continuousAt_const hcontrast hM

private theorem olsHC1_factor_tendsto :
    Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - Fintype.card K))
      atTop (𝓝 1) := by
  let k := Fintype.card K
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hden : Tendsto (fun n : ℕ => 1 - (k : ℝ) * (n : ℝ)⁻¹)
      atTop (𝓝 (1 - (k : ℝ) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)
  have hquot := hden.inv₀ (by norm_num : (1 - (k : ℝ) * 0) ≠ 0)
  have hquot' : Tendsto (fun n : ℕ =>
      (1 - (k : ℝ) * (n : ℝ)⁻¹)⁻¹) atTop (𝓝 1) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [eventually_gt_atTop k] with n hn
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le k) hn))
  dsimp [k]
  field_simp

private theorem deterministic_mul_tendstoInMeasure
    {Xn : ℕ → Ω → ℝ} {c : ℝ} {a : ℕ → ℝ}
    (hX : Tendsto_inProb Xn (fun _ => c) μ)
    (ha : Tendsto a atTop (𝓝 1)) :
    Tendsto_inProb (fun n ω => a n * Xn n ω) (fun _ => c) μ := by
  rw [Tendsto_inProb_iff] at hX ⊢
  rw [tendstoInMeasure_iff_dist] at hX ⊢
  intro ε hε
  have hbase := hX (ε / 4) (div_pos hε (by norm_num))
  have ha2 : ∀ᶠ n in atTop, |a n| ≤ 2 := by
    have he := (Metric.tendsto_nhds.mp ha) 1 zero_lt_one
    filter_upwards [he] with n hn
    rw [Real.dist_eq] at hn
    have ht := abs_add_le (a n - 1) 1
    rw [sub_add_cancel, abs_one] at ht
    linarith
  have haerr : Tendsto (fun n => |(a n - 1) * c|) atTop (𝓝 0) := by
    have hsub0 :=
      ha.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    have hsub : Tendsto (fun n => a n - 1) atTop (𝓝 0) := by
      simpa only [sub_self] using hsub0
    have hprod0 :=
      hsub.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
    have hprod : Tendsto (fun n => (a n - 1) * c) atTop (𝓝 0) := by
      simpa only [zero_mul] using hprod0
    convert continuous_abs.continuousAt.tendsto.comp hprod using 1 <;>
      simp [Function.comp_def]
  have herr : ∀ᶠ n in atTop, |(a n - 1) * c| < ε / 2 := by
    simpa [Real.dist_eq] using
      (Metric.tendsto_nhds.mp haerr) (ε / 2) (div_pos hε (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hbase (Eventually.of_forall fun _ => zero_le)
  filter_upwards [ha2, herr] with n han herrn
  apply measure_mono
  intro ω hω
  by_contra hnot
  simp only [Set.mem_setOf_eq] at hω hnot
  have hdist : dist (Xn n ω) c < ε / 4 := lt_of_not_ge hnot
  have hbound : dist (a n * Xn n ω) c < ε := by
    rw [Real.dist_eq] at hdist ⊢
    have hid : a n * Xn n ω - c =
        a n * (Xn n ω - c) + (a n - 1) * c := by ring
    rw [hid]
    calc
      |a n * (Xn n ω - c) + (a n - 1) * c|
          ≤ |a n| * |Xn n ω - c| + |(a n - 1) * c| := by
            simpa [abs_mul] using
              abs_add_le (a n * (Xn n ω - c)) ((a n - 1) * c)
      _ < 2 * (ε / 4) + ε / 2 := by
        have hprod : |a n| * |Xn n ω - c| < 2 * (ε / 4) := by
          calc
            _ ≤ 2 * |Xn n ω - c| :=
              mul_le_mul_of_nonneg_right han (abs_nonneg _)
            _ < 2 * (ε / 4) := mul_lt_mul_of_pos_left hdist (by norm_num)
        linarith
      _ = ε := by ring
  exact (not_le_of_gt hbound) hω

/-- **HC1 consistency.** For [an iid sample](hyp:S), [measurable
regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable OLS raw
moments through degree four](hyp:hraw), and [a positive-definite population design second
moment](hyp:hQ), at every [pair of coordinates](hyp:i,j), the [corresponding
HC1 sandwich entry converges in probability to the entry of
`Q⁻¹ΩQ⁻¹`](goal). -/
theorem olsHC1_entry_tendsto_inProb [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (i j : K) :
    Tendsto_inProb (fun n ω => olsHC1 S x y n ω i j)
      (fun _ => olsAsymptoticCovariance P x y i j) μ := by
  have h := deterministic_mul_tendstoInMeasure
    (olsHC0_entry_tendsto_inProb S hx hy hraw hQ i j)
    (olsHC1_factor_tendsto (K := K))
  simpa [olsHC1] using h

/-- **HC1 contrast-variance consistency.** For [an iid sample](hyp:S),
[measurable regressors](hyp:hx), [a measurable outcome](hyp:hy), [integrable
OLS raw moments through degree four](hyp:hraw), [a positive-definite
population design second moment](hyp:hQ), and [a contrast vector](hyp:c), the
[HC1 estimate of `c′Vc` converges in probability to `c′Vc`](goal). -/
theorem olsHC1_contrast_tendsto_inProb [IsProbabilityMeasure μ]
    (S : IIDSample Ω X μ P) {x : X → EuclideanSpace ℝ K} {y : X → ℝ}
    (hx : Measurable x) (hy : Measurable y)
    (hraw : Integrable (olsRawMoment x y) P)
    (hQ : (olsQ P x y).PosDef) (c : EuclideanSpace ℝ K) :
    Tendsto_inProb
      (fun n ω => olsContrastVariance (olsHC1 S x y n ω) c)
      (fun _ => olsContrastVariance (olsAsymptoticCovariance P x y) c) μ := by
  have h := deterministic_mul_tendstoInMeasure
    (olsHC0_contrast_tendsto_inProb S hx hy hraw hQ c)
    (olsHC1_factor_tendsto (K := K))
  convert h using 1
  funext n ω
  simp only [olsHC1, olsContrastVariance, Matrix.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end

end Causalean.Stat
