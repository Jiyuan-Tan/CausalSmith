/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.OrthogonalPerturbation
import Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Turning a bounded Gaussian-orthogonal function into a nearby probability law

The perturbed law has Radon--Nikodym density `1 + ε h` relative to the standard
Gaussian.  Pointwise boundedness of `h` gives nonnegativity and domination, while
orthogonality gives normalization and exact finite moment matching.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Given [a signed profile](hyp:h) and [a real amplitude](hyp:ε), the [Gaussian density
perturbation](goal) is [given by weighting the standard Gaussian law by one plus the scaled
profile](step:1). -/
noncomputable def gaussianPerturbation (h : ℝ → ℝ) (ε : ℝ) : Measure ℝ :=
  (gaussianReal 0 1).withDensity (fun x => ENNReal.ofReal (1 + ε * h x))

private lemma standardGaussian_abs_pow_integrable (k : ℕ) :
    Integrable (fun x : ℝ => |x| ^ k) (gaussianReal 0 1) := by
  simpa [Real.norm_eq_abs, Function.id_def] using
    (memLp_id_gaussianReal (μ := (0 : ℝ)) (v := 1) (p := k)).integrable_norm_pow'

private lemma iteratedDeriv_standardGaussian_mgf_add_two (m : ℕ) :
    iteratedDeriv (m + 2) (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 =
      (m + 1 : ℝ) * iteratedDeriv m (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
  let g : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have hg : ContDiff ℝ ⊤ g := by fun_prop
  have hderiv : deriv g = fun t => t * g t := by
    funext t
    have hi : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      simpa [Function.id_def] using ((hasDerivAt_id t).pow 2).div_const 2
    simpa [g, mul_comm] using hi.exp.deriv
  rw [show m + 2 = (m + 1) + 1 by omega, iteratedDeriv_succ', hderiv]
  change iteratedDeriv (m + 1) ((fun t : ℝ => t) * g) 0 =
    (m + 1 : ℝ) * iteratedDeriv m g 0
  rw [iteratedDeriv_mul (n := m + 1) (x := (0 : ℝ)) (by fun_prop)
    (hg.contDiffAt.of_le (by simp))]
  rw [Finset.sum_eq_single 1]
  · simp [g]
  · intro i hi hne
    simp [iteratedDeriv_fun_id_zero, hne]
  · simp

private lemma standardGaussian_evenMoment_le (n : ℕ) :
    (∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1) ≤ (2 * n : ℝ) ^ n := by
  have hmoment (m : ℕ) :
      ∫ x : ℝ, x ^ m ∂gaussianReal 0 1 =
        iteratedDeriv m (fun t : ℝ => Real.exp (t ^ 2 / 2)) 0 := by
    calc
      _ = iteratedDeriv m (mgf id (gaussianReal 0 1)) 0 :=
        (iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 1) (by simp) m).symm
      _ = _ := by rw [mgf_id_gaussianReal]; simp
  induction n with
  | zero => simp [hmoment]
  | succ n ih =>
      rw [hmoment, show 2 * (n + 1) = 2 * n + 2 by omega,
        iteratedDeriv_standardGaussian_mgf_add_two, ← hmoment]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
      push_cast
      calc
        (2 * (n : ℝ) + 1) * ∫ x : ℝ, x ^ (2 * n) ∂gaussianReal 0 1
            ≤ (2 * (n : ℝ) + 1) * (2 * (n : ℝ)) ^ n := by
                exact mul_le_mul_of_nonneg_left ih (by positivity)
        _ ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ (n + 1) := by
          have hfac : 2 * (n : ℝ) + 1 ≤ 2 * ((n + 1 : ℕ) : ℝ) := by
            push_cast
            linarith
          have hpow : (2 * (n : ℝ)) ^ n ≤ (2 * ((n + 1 : ℕ) : ℝ)) ^ n :=
            pow_le_pow_left₀ (by positivity) (by push_cast; linarith) n
          rw [pow_succ]
          simpa [mul_comm] using
            mul_le_mul hfac hpow (by positivity) (by positivity)
      all_goals norm_num only [Nat.cast_add, Nat.cast_one]
      all_goals rfl

/-- If [a profile is measurable](hyp:hmeas), [bounded by one](hyp:hbound), [nonzero under the
standard Gaussian law](hyp:hnonzero), and [orthogonal to the required monomials](hyp:horth), while
[its amplitude is positive](hyp:hεpos), [below one](hyp:hεone), and [below the requested
distance radius](hyp:hερho), then [the resulting density perturbation is a distinct nearby
probability law with the specified raw moments, all absolute moments, and a Gaussian-scale
even-moment bound](goal). -/
theorem gaussianPerturbation_spec
    {K : ℕ} {h : ℝ → ℝ} {ε rho : ℝ}
    (hmeas : Measurable h)
    (hbound : ∀ x, |h x| ≤ 1)
    (hnonzero : 0 < ∫ x, |h x| ∂gaussianReal 0 1)
    (horth : ∀ k, k ≤ K →
      Integrable (fun x => x ^ k * h x) (gaussianReal 0 1) ∧
      (∫ x, x ^ k * h x ∂gaussianReal 0 1) = 0)
    (hεpos : 0 < ε) (hεone : ε < 1) (hερho : ε < rho) :
    let F := gaussianPerturbation h ε
    IsProbabilityMeasure F ∧
    F ≠ gaussianReal 0 1 ∧
    totalVariationDistance F (gaussianReal 0 1) < rho ∧
    (∀ k, k ≤ K → rawMoment F k = rawMoment (gaussianReal 0 1) k) ∧
    (∀ k, Integrable (fun x : ℝ => |x| ^ k) F) ∧
    (∀ n : ℕ, 0 < n →
      |rawMoment F (2 * n)| ≤ 2 * (2 * n : ℝ) ^ n) := by
  let μ : Measure ℝ := gaussianReal 0 1
  let d : ℝ → ℝ := fun x => 1 + ε * h x
  let f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (d x)
  have hd_pos (x : ℝ) : 0 < d x := by
    have hx := (abs_le.mp (hbound x)).1
    dsimp [d]
    nlinarith
  have hd_nonneg (x : ℝ) : 0 ≤ d x := (hd_pos x).le
  have hd_le (x : ℝ) : d x ≤ 2 := by
    have hx := (abs_le.mp (hbound x)).2
    dsimp [d]
    nlinarith
  have hf_meas : Measurable f := by
    exact (measurable_const.add (measurable_const.mul hmeas)).ennreal_ofReal
  have hf_top : ∀ᵐ x ∂μ, f x < ∞ := by
    exact Filter.Eventually.of_forall fun x => by simp [f]
  have hf_toReal (x : ℝ) : (f x).toReal = d x := by
    simp [f, ENNReal.toReal_ofReal (hd_nonneg x)]
  obtain ⟨hh_int0, hh_mean0⟩ := horth 0 (Nat.zero_le K)
  have hh_int : Integrable h μ := by
    simpa [μ] using hh_int0
  have habsh_int : Integrable (fun x => |h x|) μ := by
    simpa [Real.norm_eq_abs] using hh_int.norm
  have hh_mean : ∫ x, h x ∂μ = 0 := by
    simpa [μ] using hh_mean0
  let F : Measure ℝ := gaussianPerturbation h ε
  have hF_def : F = μ.withDensity f := by
    rfl
  have hprob : IsProbabilityMeasure F := by
    dsimp [F, gaussianPerturbation, μ]
    change IsProbabilityMeasure
      (Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.tiltMeasure
        (gaussianReal 0 1) h ε)
    apply Causalean.Mathlib.InformationTheory.KlDensityTiltExpansion.isProbabilityMeasure_tiltMeasure
      hmeas hbound
    · simpa [μ] using hh_mean
    · rw [abs_of_pos hεpos]
      linarith
  letI : IsProbabilityMeasure F := hprob
  have hpower_int (k : ℕ) : Integrable (fun x : ℝ => x ^ k) μ := by
    apply (integrable_norm_iff (by fun_prop)).mp
    simpa [μ, Real.norm_eq_abs, abs_pow] using standardGaussian_abs_pow_integrable k
  have habs_mul_h_int (k : ℕ) :
      Integrable (fun x : ℝ => |x| ^ k * h x) μ := by
    apply (standardGaussian_abs_pow_integrable k).mono'
    · exact ((measurable_id.abs.pow_const k).mul hmeas).aestronglyMeasurable
    · filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (abs_nonneg x) k)]
      exact mul_le_of_le_one_right (by positivity) (hbound x)
  have habs_F_int (k : ℕ) : Integrable (fun x : ℝ => |x| ^ k) F := by
    rw [hF_def, integrable_withDensity_iff hf_meas hf_top]
    have hi : Integrable (fun x : ℝ => |x| ^ k + ε * (|x| ^ k * h x)) μ :=
      (standardGaussian_abs_pow_integrable k).add ((habs_mul_h_int k).const_mul ε)
    apply hi.congr
    filter_upwards [] with x
    rw [hf_toReal]
    dsimp [d]
    ring
  have hmoment_match (k : ℕ) (hk : k ≤ K) :
      rawMoment F k = rawMoment μ k := by
    obtain ⟨hkh_int, hkh_zero⟩ := horth k hk
    rw [rawMoment_eq_integral, rawMoment_eq_integral, hF_def,
      integral_withDensity_eq_integral_toReal_smul hf_meas hf_top]
    have heq : (fun x : ℝ => (f x).toReal • x ^ k) =
        fun x => x ^ k + ε * (x ^ k * h x) := by
      funext x
      rw [hf_toReal]
      dsimp [d]
      change (1 + ε * h x) * x ^ k = x ^ k + ε * (x ^ k * h x)
      ring
    rw [heq, integral_add (hpower_int k) (hkh_int.const_mul ε),
      integral_const_mul, hkh_zero]
    ring
  have hne : F ≠ μ := by
    intro heq
    have hdensEq : μ.withDensity f =
        μ.withDensity (fun _ : ℝ => (1 : ℝ≥0∞)) := by
      calc
        μ.withDensity f = F := hF_def.symm
        _ = μ := heq
        _ = μ.withDensity (fun _ : ℝ => (1 : ℝ≥0∞)) := by
          symm
          change μ.withDensity (1 : ℝ → ℝ≥0∞) = μ
          exact withDensity_one
    have hfdens : f =ᵐ[μ] (1 : ℝ → ℝ≥0∞) :=
      (withDensity_eq_iff_of_sigmaFinite hf_meas.aemeasurable
        measurable_const.aemeasurable).mp hdensEq
    have hh_zero : h =ᵐ[μ] 0 := by
      filter_upwards [hfdens] with x hx
      have hx' := congrArg ENNReal.toReal hx
      rw [hf_toReal] at hx'
      simp only [Pi.one_apply, ENNReal.toReal_one] at hx'
      dsimp [d] at hx'
      have : h x = 0 := by nlinarith
      simpa [this]
    have : ∫ x, |h x| ∂μ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hh_zero] with x hx
      simp [hx]
    exact (by simpa [μ, this] using hnonzero : False)
  have htv : totalVariationDistance F μ < rho := by
    rw [totalVariationDistance_eq_tvDist, Causalean.Stat.tvDist]
    apply lt_of_le_of_lt (ciSup_le fun A => ?_) hερho
    have hAint : Integrable (A.1.indicator h) μ := hh_int.indicator A.2
    have hevent : F.real A.1 - μ.real A.1 = ε * ∫ x in A.1, h x ∂μ := by
      have hFI : F.real A.1 = ∫ x, A.1.indicator (fun _ => (1 : ℝ)) x ∂F := by
        rw [integral_indicator A.2, setIntegral_const]
        simp [measureReal_def]
      have hμI : μ.real A.1 = ∫ x, A.1.indicator (fun _ => (1 : ℝ)) x ∂μ := by
        rw [integral_indicator A.2, setIntegral_const]
        simp [measureReal_def]
      rw [hFI, hμI, hF_def,
        integral_withDensity_eq_integral_toReal_smul hf_meas hf_top]
      have hi : (fun x : ℝ => (f x).toReal • A.1.indicator (fun _ => (1 : ℝ)) x) =
          fun x => A.1.indicator (fun _ => (1 : ℝ)) x +
            ε * A.1.indicator h x := by
        funext x
        rw [hf_toReal]
        by_cases hx : x ∈ A.1 <;> simp [d, hx] <;> ring
      rw [hi, integral_add ((integrable_const 1).indicator A.2) (hAint.const_mul ε),
        integral_const_mul]
      rw [← integral_indicator A.2]
      ring
    rw [abs_sub_comm, ← neg_sub, hevent, abs_neg, abs_mul, abs_of_pos hεpos]
    calc
      ε * |∫ x in A.1, h x ∂μ| ≤ ε * ∫ x in A.1, |h x| ∂μ := by
        gcongr
        exact abs_integral_le_integral_abs
      _ ≤ ε * ∫ x, |h x| ∂μ := by
        exact mul_le_mul_of_nonneg_left
          (setIntegral_le_integral habsh_int
            (Filter.Eventually.of_forall fun x => abs_nonneg (h x))) hεpos.le
      _ ≤ ε := by
        have hint_le : ∫ x, |h x| ∂μ ≤ 1 := by
          calc
            _ ≤ ∫ _x, (1 : ℝ) ∂μ := integral_mono
              habsh_int (integrable_const 1) hbound
            _ = 1 := by simp [μ]
        nlinarith
  refine ⟨hprob, ?_, htv, hmoment_match, habs_F_int, ?_⟩
  · simpa [F, μ] using hne
  · intro n _hn
    rw [rawMoment_eq_integral]
    calc
      |∫ x : ℝ, x ^ (2 * n) ∂F| ≤ ∫ x : ℝ, |x ^ (2 * n)| ∂F :=
        abs_integral_le_integral_abs
      _ = ∫ x : ℝ, |x| ^ (2 * n) ∂F := by
        congr 1
        funext x
        rw [abs_pow]
      _ = ∫ x : ℝ, d x * |x| ^ (2 * n) ∂μ := by
        rw [hF_def, integral_withDensity_eq_integral_toReal_smul hf_meas hf_top]
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hf_toReal]
        simp [smul_eq_mul, mul_comm]
      _ ≤ ∫ x : ℝ, 2 * |x| ^ (2 * n) ∂μ := by
        apply integral_mono
        · have hi : Integrable (fun x : ℝ => d x * |x| ^ (2 * n)) μ := by
            apply ((standardGaussian_abs_pow_integrable (2 * n)).const_mul 2).mono'
            · fun_prop
            · filter_upwards [] with x
              rw [Real.norm_eq_abs, abs_mul, abs_of_pos (hd_pos x),
                abs_of_nonneg (pow_nonneg (abs_nonneg x) (2 * n))]
              exact mul_le_mul_of_nonneg_right (hd_le x) (by positivity)
          exact hi
        · exact (standardGaussian_abs_pow_integrable (2 * n)).const_mul 2
        · intro x
          exact mul_le_mul_of_nonneg_right (hd_le x) (by positivity)
      _ = 2 * ∫ x : ℝ, x ^ (2 * n) ∂μ := by
        rw [integral_const_mul]
        congr 2
        funext x
        rw [← abs_pow, abs_of_nonneg (Even.pow_nonneg (even_two_mul n) x)]
      _ ≤ 2 * (2 * n : ℝ) ^ n := by
        gcongr
        simpa [μ] using standardGaussian_evenMoment_le n

end Causalean.Stat.MomentProblems
