module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.OneCellComparison

/-! The multivariate Taylor expansion of the one-cell marked-Poisson Gram
kernel, forming the exact series layer between the Gram identity and the
moment-matched tail estimate. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
open scoped BigOperators

/-- The concrete one-cell intensity prior is supported coordinatewise between
zero and the common reference intensity. -/
lemma signedScoreIntensityPrior_ae_mem_Icc
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) :
    ∀ᵐ v ∂signedScoreIntensityPrior kappa gamma rho a J D h,
      ∀ i, v i ∈ Icc 0 (kappa * (J : ℝ)) := by
  let S := {v : Fin 4 → ℝ | ∀ i, v i ∈ Icc 0 (kappa * (J : ℝ))}
  have hS : MeasurableSet S := by
    dsimp only [S]
    measurability
  have hpre : MeasurableSet {z : LatentCell |
      ∀ i, signedScoreIntensity kappa gamma rho J z i ∈
        Icc 0 (kappa * (J : ℝ))} := by
    measurability
  rw [signedScoreIntensityPrior,
    ae_map_iff (signedScoreIntensity_measurable kappa gamma rho J).aemeasurable hS,
    oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff hpre]
    intro i
    rw [signedScoreIntensity_reference]
    exact ⟨by positivity, le_rfl⟩
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hpre]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D (!h)] with x hx
      rcases hx with rfl | hx
      · intro i
        rw [show latentFromIntensity false a 0 = zeroLatent false by
          simp [latentFromIntensity], signedScoreIntensity_zero]
        exact ⟨le_rfl, by positivity⟩
      · exact signedScoreIntensity_latentFromIntensity_mem_Icc
          kappa gamma rho a x J false hkappa hgamma hrho ha hx
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hpre]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D h] with x hx
      rcases hx with rfl | hx
      · intro i
        rw [show latentFromIntensity true a 0 = zeroLatent true by
          simp [latentFromIntensity], signedScoreIntensity_zero]
        exact ⟨le_rfl, by positivity⟩
      · exact signedScoreIntensity_latentFromIntensity_mem_Icc
          kappa gamma rho a x J true hkappa hgamma hrho ha hx

/-- One coefficient in the factorized four-coordinate Taylor expansion of
the exponential Gram kernel. -/
@[expose] noncomputable def signedScoreTaylorCoefficient (Lambda : ℝ)
    (alpha : Fin 4 → ℕ) (v w : Fin 4 → ℝ) : ℝ :=
  ∏ s, (((v s - Lambda) * (w s - Lambda) / Lambda) ^ alpha s /
    (alpha s).factorial)

/-- The factorized four-index Taylor coefficients are absolutely summable. -/
lemma signedScoreTaylorCoefficient_summable (Lambda : ℝ)
    (v w : Fin 4 → ℝ) :
    Summable (fun alpha : Fin 4 → ℕ =>
      signedScoreTaylorCoefficient Lambda alpha v w) := by
  classical
  let x : Fin 4 → ℝ := fun s =>
    (v s - Lambda) * (w s - Lambda) / Lambda
  let f : Fin 4 → ℕ → ℝ := fun s n => x s ^ n / n.factorial
  let e : ((((ℕ × ℕ) × ℕ) × ℕ)) ≃ (Fin 4 → ℕ) :=
    { toFun := fun q => ![q.1.1.1, q.1.1.2, q.1.2, q.2]
      invFun := fun alpha => (((alpha 0, alpha 1), alpha 2), alpha 3)
      left_inv := by rintro ⟨⟨⟨a, b⟩, c⟩, d⟩; rfl
      right_inv := by intro alpha; funext s; fin_cases s <;> rfl }
  have hfnorm (s : Fin 4) : Summable (fun n => ‖f s n‖) := by
    simpa only [f, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
        Real.summable_pow_div_factorial |x s|
  have hnorm01 : Summable (fun q : ℕ × ℕ =>
      ‖f 0 q.1 * f 1 q.2‖) := (hfnorm 0).mul_norm (hfnorm 1)
  have hnorm012 : Summable (fun q : ((ℕ × ℕ) × ℕ) =>
      ‖(f 0 q.1.1 * f 1 q.1.2) * f 2 q.2‖) :=
    hnorm01.mul_norm (hfnorm 2)
  have hnorm0123 : Summable (fun q : (((ℕ × ℕ) × ℕ) × ℕ) =>
      ‖((f 0 q.1.1.1 * f 1 q.1.1.2) * f 2 q.1.2) * f 3 q.2‖) :=
    hnorm012.mul_norm (hfnorm 3)
  have hsource : Summable (fun q : (((ℕ × ℕ) × ℕ) × ℕ) =>
      ((f 0 q.1.1.1 * f 1 q.1.1.2) * f 2 q.1.2) * f 3 q.2) :=
    hnorm0123.of_norm
  apply (e.summable_iff).1
  convert hsource using 1
  funext q
  rcases q with ⟨⟨⟨a, b⟩, c⟩, d⟩
  simp [signedScoreTaylorCoefficient, e, f, x, Fin.prod_univ_four]
  ring

private lemma abs_signedScoreTaylorCoefficient_le
    (Lambda : ℝ) (alpha : Fin 4 → ℕ) (v w : Fin 4 → ℝ)
    (hLambda : 0 < Lambda) (hv : ∀ s, v s ∈ Icc 0 Lambda)
    (hw : ∀ s, w s ∈ Icc 0 Lambda) :
    |signedScoreTaylorCoefficient Lambda alpha v w| ≤
      ∏ s, Lambda ^ alpha s / (alpha s).factorial := by
  rw [signedScoreTaylorCoefficient, Finset.abs_prod]
  apply Finset.prod_le_prod
  · intro s _hs
    positivity
  · intro s _hs
    have hvabs : |v s - Lambda| ≤ Lambda := by
      rw [abs_le]
      constructor <;> linarith [(hv s).1, (hv s).2]
    have hwabs : |w s - Lambda| ≤ Lambda := by
      rw [abs_le]
      constructor <;> linarith [(hw s).1, (hw s).2]
    have hx : |(v s - Lambda) * (w s - Lambda) / Lambda| ≤ Lambda := by
      rw [abs_div, abs_mul, abs_of_pos hLambda]
      apply (div_le_iff₀ hLambda).2
      nlinarith [abs_nonneg (v s - Lambda), abs_nonneg (w s - Lambda)]
    rw [abs_div, abs_pow, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) hx _) (by positivity)

/-- The exponential Gram kernel is the absolutely convergent multi-index
series of products of centered monomials.  This is the pointwise Taylor
identity underlying equation (65). -/
lemma signedScore_exp_centered_eq_tsum (Lambda : ℝ) (v w : Fin 4 → ℝ) :
    Real.exp (∑ s : Fin 4, (v s - Lambda) * (w s - Lambda) / Lambda) =
      ∑' alpha : Fin 4 → ℕ,
        (∏ s, (v s - Lambda) ^ alpha s) *
            (∏ s, (w s - Lambda) ^ alpha s) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            Lambda ^ (∑ s, alpha s)) := by
  classical
  let x : Fin 4 → ℝ := fun s =>
    (v s - Lambda) * (w s - Lambda) / Lambda
  let e : ((((ℕ × ℕ) × ℕ) × ℕ)) ≃ (Fin 4 → ℕ) :=
    { toFun := fun q => ![q.1.1.1, q.1.1.2, q.1.2, q.2]
      invFun := fun alpha => (((alpha 0, alpha 1), alpha 2), alpha 3)
      left_inv := by
        rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
        rfl
      right_inv := by
        intro alpha
        funext s
        fin_cases s <;> rfl }
  let f : Fin 4 → ℕ → ℝ := fun s n => x s ^ n / n.factorial
  have hf (s : Fin 4) : Summable (f s) := by
    exact Real.summable_pow_div_factorial (x s)
  have hfnorm (s : Fin 4) : Summable (fun n => ‖f s n‖) := by
    simpa only [f, Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)] using
        Real.summable_pow_div_factorial |x s|
  have hnorm01 : Summable (fun q : ℕ × ℕ =>
      ‖f 0 q.1 * f 1 q.2‖) := (hfnorm 0).mul_norm (hfnorm 1)
  have hnorm012 : Summable (fun q : ((ℕ × ℕ) × ℕ) =>
      ‖(f 0 q.1.1 * f 1 q.1.2) * f 2 q.2‖) :=
    hnorm01.mul_norm (hfnorm 2)
  have hnorm0123 : Summable (fun q : (((ℕ × ℕ) × ℕ) × ℕ) =>
      ‖((f 0 q.1.1.1 * f 1 q.1.1.2) * f 2 q.1.2) * f 3 q.2‖) :=
    hnorm012.mul_norm (hfnorm 3)
  have hprod : Summable (fun q : (((ℕ × ℕ) × ℕ) × ℕ) =>
      ((f 0 q.1.1.1 * f 1 q.1.1.2) * f 2 q.1.2) * f 3 q.2) :=
    hnorm0123.of_norm
  have hterm (alpha : Fin 4 → ℕ) :
      ∏ s, f s (alpha s) =
        (∏ s, (v s - Lambda) ^ alpha s) *
            (∏ s, (w s - Lambda) ^ alpha s) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            Lambda ^ (∑ s, alpha s)) := by
    have hcoord (s : Fin 4) :
        f s (alpha s) =
          ((v s - Lambda) ^ alpha s * (w s - Lambda) ^ alpha s) /
            (((alpha s).factorial : ℝ) * Lambda ^ alpha s) := by
      simp only [f, x, div_pow, mul_pow]
      ring
    rw [Fin.prod_univ_four, hcoord 0, hcoord 1, hcoord 2, hcoord 3]
    simp only [Fin.prod_univ_four, Fin.sum_univ_four, pow_add]
    ring
  calc
    Real.exp (∑ s : Fin 4, (v s - Lambda) * (w s - Lambda) / Lambda) =
        ∏ s, Real.exp (x s) := by
      rw [← Real.exp_sum]
    _ = ∏ s, ∑' n, f s n := by
      apply Finset.prod_congr rfl
      intro s _hs
      simpa only [f, Real.exp_eq_exp_ℝ] using
        (NormedSpace.expSeries_div_hasSum_exp (x s)).tsum_eq.symm
    _ = ∑' q : (((ℕ × ℕ) × ℕ) × ℕ),
        ((f 0 q.1.1.1 * f 1 q.1.1.2) * f 2 q.1.2) * f 3 q.2 := by
      rw [Fin.prod_univ_four]
      rw [(hf 0).tsum_mul_tsum (hf 1) hnorm01.of_norm,
        (hnorm01.of_norm).tsum_mul_tsum (hf 2) hnorm012.of_norm,
        (hnorm012.of_norm).tsum_mul_tsum (hf 3) hprod]
    _ = ∑' alpha : Fin 4 → ℕ, ∏ s, f s (alpha s) := by
      calc
        _ = ∑' q : (((ℕ × ℕ) × ℕ) × ℕ),
            (fun alpha : Fin 4 → ℕ => ∏ s, f s (alpha s)) (e q) := by
          apply tsum_congr
          rintro ⟨⟨⟨a, b⟩, c⟩, d⟩
          simp [e, Fin.prod_univ_four]
        _ = _ := e.tsum_eq
          (fun alpha : Fin 4 → ℕ => ∏ s, f s (alpha s))
    _ = ∑' alpha : Fin 4 → ℕ,
        (∏ s, (v s - Lambda) ^ alpha s) *
            (∏ s, (w s - Lambda) ^ alpha s) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            Lambda ^ (∑ s, alpha s)) := tsum_congr hterm

/-- The factorized Taylor series sums to the exponential Gram kernel. -/
lemma signedScore_exp_eq_tsum_taylorCoefficient (Lambda : ℝ)
    (v w : Fin 4 → ℝ) :
    Real.exp (∑ s : Fin 4, (v s - Lambda) * (w s - Lambda) / Lambda) =
      ∑' alpha : Fin 4 → ℕ,
        signedScoreTaylorCoefficient Lambda alpha v w := by
  rw [signedScore_exp_centered_eq_tsum]
  apply tsum_congr
  intro alpha
  simp only [signedScoreTaylorCoefficient, Fin.prod_univ_four,
    Fin.sum_univ_four, div_pow, mul_pow, pow_add]
  ring

/-- The Gram integral of two concrete four-count Poisson likelihoods equals
the exact centered-moment multi-index series. -/
-- keep: exact one-cell likelihood expansion underlying the tail comparison
lemma signedScoreLikelihood_inner_eq_tsum (Lambda : ℝ)
    (v w : Fin 4 → ℝ) (hLambda : 0 < Lambda) :
    (∫ z, signedScoreLikelihood Lambda v z * signedScoreLikelihood Lambda w z
        ∂signedScoreReferenceLaw Lambda) =
      ∑' alpha : Fin 4 → ℕ,
        (∏ s, (v s - Lambda) ^ alpha s) *
            (∏ s, (w s - Lambda) ^ alpha s) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            Lambda ^ (∑ s, alpha s)) := by
  rw [signedScoreLikelihood_inner Lambda v w hLambda]
  exact signedScore_exp_centered_eq_tsum Lambda v w

/-- The joint two-intensity likelihood product is integrable for every pair
of the concrete one-cell priors.  This is the Fubini witness needed by the
mixture Gram identity. -/
lemma signedScoreLikelihood_joint_integrable_intensityPrior
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    Integrable (fun p : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts =>
      signedScoreLikelihood (kappa * (J : ℝ)) p.1.1 p.2 *
        signedScoreLikelihood (kappa * (J : ℝ)) p.1.2 p.2)
      (((signedScoreIntensityPrior kappa gamma rho a J D h0).prod
        (signedScoreIntensityPrior kappa gamma rho a J D h1)).prod
          (signedScoreReferenceLaw (kappa * (J : ℝ)))) := by
  let Lambda := kappa * (J : ℝ)
  let pi0 := signedScoreIntensityPrior kappa gamma rho a J D h0
  let pi1 := signedScoreIntensityPrior kappa gamma rho a J D h1
  let Q := signedScoreReferenceLaw Lambda
  let F : ((Fin 4 → ℝ) × (Fin 4 → ℝ)) × SignedScoreCounts → ℝ :=
    fun p => signedScoreLikelihood Lambda p.1.1 p.2 *
      signedScoreLikelihood Lambda p.1.2 p.2
  let G : (Fin 4 → ℝ) × (Fin 4 → ℝ) → ℝ := fun p =>
    Real.exp (∑ s : Fin 4,
      (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda)
  letI : IsProbabilityMeasure pi0 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure pi1 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  have hLambda : 0 < Lambda := by positivity
  have hsupp0 : ∀ᵐ v ∂pi0, ∀ s, v s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h0 hkappa.le hgamma hrho ha
  have hsupp1 : ∀ᵐ w ∂pi1, ∀ s, w s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h1 hkappa.le hgamma hrho ha
  have hsupp : ∀ᵐ p ∂pi0.prod pi1,
      (∀ s, p.1 s ∈ Icc 0 Lambda) ∧ (∀ s, p.2 s ∈ Icc 0 Lambda) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hsupp0] with v hv
    filter_upwards [hsupp1] with w hw
    exact ⟨hv, hw⟩
  have hGsm : StronglyMeasurable G := by
    dsimp only [G]
    fun_prop
  have hGint : Integrable G (pi0.prod pi1) := by
    apply (integrable_const (c := Real.exp (4 * Lambda))).mono'
      hGsm.aestronglyMeasurable
    filter_upwards [hsupp] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hterm (s : Fin 4) :
        (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda ≤ Lambda := by
      apply (div_le_iff₀ hLambda).2
      rcases hp.1 s with ⟨hv0, hvL⟩
      rcases hp.2 s with ⟨hw0, hwL⟩
      have hv' : 0 ≤ Lambda - p.1 s ∧ Lambda - p.1 s ≤ Lambda := by
        constructor <;> linarith
      have hw' : 0 ≤ Lambda - p.2 s ∧ Lambda - p.2 s ≤ Lambda := by
        constructor <;> linarith
      have hprod : (Lambda - p.1 s) * (Lambda - p.2 s) ≤ Lambda * Lambda :=
        mul_le_mul hv'.2 hw'.2 hw'.1 hLambda.le
      nlinarith
    rw [Fin.sum_univ_four]
    nlinarith [hterm 0, hterm 1, hterm 2, hterm 3]
  have hFsm : StronglyMeasurable F := by
    dsimp only [F]
    apply StronglyMeasurable.mul
    · exact (signedScoreLikelihood_joint_stronglyMeasurable Lambda).comp_measurable
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    · exact (signedScoreLikelihood_joint_stronglyMeasurable Lambda).comp_measurable
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  apply (integrable_prod_iff hFsm.aestronglyMeasurable).2
  constructor
  · filter_upwards [] with p
    apply Integrable.of_integral_ne_zero
    dsimp only [F, Q]
    rw [signedScoreLikelihood_inner Lambda p.1 p.2 hLambda]
    positivity
  · apply hGint.congr
    filter_upwards [hsupp] with p hp
    have hnonneg (z : SignedScoreCounts) : 0 ≤ F (p, z) := by
      exact mul_nonneg
        (signedScoreLikelihood_nonneg Lambda p.1 z hLambda
          (fun s => (hp.1 s).1))
        (signedScoreLikelihood_nonneg Lambda p.2 z hLambda
          (fun s => (hp.2 s).1))
    symm
    calc
      (∫ z, ‖F (p, z)‖ ∂Q) = ∫ z, F (p, z) ∂Q := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
      _ = G p := by
        simpa only [F, G, Q] using
          signedScoreLikelihood_inner Lambda p.1 p.2 hLambda

/-- The integrated concrete Taylor coefficients sum to the product-prior
exponential Gram integral. -/
lemma hasSum_signedScoreIntensityPrior_taylor_integral
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    HasSum (fun alpha : Fin 4 → ℕ =>
        ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
          signedScoreTaylorCoefficient (kappa * (J : ℝ)) alpha p.1 p.2
          ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
            (signedScoreIntensityPrior kappa gamma rho a J D h1))
      (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        Real.exp (∑ s : Fin 4,
          (p.1 s - kappa * (J : ℝ)) * (p.2 s - kappa * (J : ℝ)) /
            (kappa * (J : ℝ)))
        ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
          (signedScoreIntensityPrior kappa gamma rho a J D h1)) := by
  let Lambda := kappa * (J : ℝ)
  let pi0 := signedScoreIntensityPrior kappa gamma rho a J D h0
  let pi1 := signedScoreIntensityPrior kappa gamma rho a J D h1
  let B : (Fin 4 → ℕ) → ℝ := fun alpha =>
    ∏ s, Lambda ^ alpha s / (alpha s).factorial
  letI : IsProbabilityMeasure pi0 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure pi1 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  have hLambda : 0 < Lambda := by positivity
  have hsupp0 : ∀ᵐ v ∂pi0, ∀ s, v s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h0 hkappa.le hgamma hrho ha
  have hsupp1 : ∀ᵐ w ∂pi1, ∀ s, w s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h1 hkappa.le hgamma hrho ha
  have hsupp : ∀ᵐ p ∂pi0.prod pi1,
      (∀ s, p.1 s ∈ Icc 0 Lambda) ∧ (∀ s, p.2 s ∈ Icc 0 Lambda) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hsupp0] with v hv
    filter_upwards [hsupp1] with w hw
    exact ⟨hv, hw⟩
  have hB : Summable B := by
    have h := signedScoreTaylorCoefficient_summable Lambda
      (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 0)
    apply h.congr
    intro alpha
    simp only [signedScoreTaylorCoefficient, B, zero_sub,
      neg_mul_neg, mul_div_cancel_left₀ _ hLambda.ne', Fin.prod_univ_four]
  simpa only [Lambda, pi0, pi1] using
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (μ := pi0.prod pi1)
      (fun alpha (_p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) => B alpha)
      (F := fun alpha (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) =>
        signedScoreTaylorCoefficient Lambda alpha p.1 p.2)
      (f := fun (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) => Real.exp
        (∑ s : Fin 4, (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda))
      (fun _alpha => by
        apply StronglyMeasurable.aestronglyMeasurable
        unfold signedScoreTaylorCoefficient
        fun_prop)
      (fun alpha => by
        filter_upwards [hsupp] with p hp
        exact abs_signedScoreTaylorCoefficient_le
          Lambda alpha p.1 p.2 hLambda hp.1 hp.2)
      (by filter_upwards with p; exact hB)
      (by
        simpa only [Pi.one_apply] using
          (integrable_const (μ := pi0.prod pi1) (∑' alpha, B alpha)))
      (by
        filter_upwards with p
        rw [signedScore_exp_eq_tsum_taylorCoefficient]
        exact (signedScoreTaylorCoefficient_summable Lambda p.1 p.2).hasSum)

/-- Integrating one Taylor coefficient against a concrete product prior
factors into the product of the corresponding centered moments. -/
lemma integral_signedScoreTaylorCoefficient_intensityPrior_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (alpha : Fin 4 → ℕ) (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        signedScoreTaylorCoefficient (kappa * (J : ℝ)) alpha p.1 p.2
        ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
          (signedScoreIntensityPrior kappa gamma rho a J D h1)) =
      ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D h0) *
        (∫ w, ∏ s, (w s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D h1)) /
        ((∏ s, ((alpha s).factorial : ℝ)) *
          (kappa * (J : ℝ)) ^ (∑ s, alpha s)) := by
  letI : IsProbabilityMeasure
      (signedScoreIntensityPrior kappa gamma rho a J D h0) :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure
      (signedScoreIntensityPrior kappa gamma rho a J D h1) :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  let Lambda := kappa * (J : ℝ)
  let c : ℝ := 1 / ((∏ s, ((alpha s).factorial : ℝ)) *
    Lambda ^ (∑ s, alpha s))
  let g : (Fin 4 → ℝ) → ℝ := fun v =>
    ∏ s, (v s - Lambda) ^ alpha s
  have hpoint : (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      signedScoreTaylorCoefficient Lambda alpha p.1 p.2) =
      fun p => c * (g p.1 * g p.2) := by
    funext p
    simp only [signedScoreTaylorCoefficient, Lambda, c, g,
      Fin.prod_univ_four, Fin.sum_univ_four, div_pow, mul_pow, pow_add]
    ring
  rw [hpoint, integral_const_mul, MeasureTheory.integral_prod_mul]
  simp only [c, g, Lambda]
  ring

/-- The concrete centered-moment product series is summable for every pair
of true/false one-cell intensity priors. -/
lemma signedScoreIntensityPrior_moment_product_summable
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    Summable (fun alpha : Fin 4 → ℕ =>
      ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D h0) *
        (∫ w, ∏ s, (w s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D h1)) /
        ((∏ s, ((alpha s).factorial : ℝ)) *
          (kappa * (J : ℝ)) ^ (∑ s, alpha s))) := by
  apply (hasSum_signedScoreIntensityPrior_taylor_integral
    kappa gamma rho a J D h0 h1 hkappa hgamma hrho ha hJ).summable.congr
  intro alpha
  exact integral_signedScoreTaylorCoefficient_intensityPrior_eq
    kappa gamma rho a J D h0 h1 alpha ha hJ

/-- For either pair of concrete one-cell intensity priors, the exponential
Gram integral commutes with the absolutely convergent four-index Taylor
series. -/
lemma signedScoreIntensityPrior_exp_integral_eq_tsum
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        Real.exp (∑ s : Fin 4,
          (p.1 s - kappa * (J : ℝ)) * (p.2 s - kappa * (J : ℝ)) /
            (kappa * (J : ℝ)))
        ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
          (signedScoreIntensityPrior kappa gamma rho a J D h1)) =
      ∑' alpha : Fin 4 → ℕ,
        ∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
          signedScoreTaylorCoefficient (kappa * (J : ℝ)) alpha p.1 p.2
          ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
            (signedScoreIntensityPrior kappa gamma rho a J D h1) := by
  let Lambda := kappa * (J : ℝ)
  let pi0 := signedScoreIntensityPrior kappa gamma rho a J D h0
  let pi1 := signedScoreIntensityPrior kappa gamma rho a J D h1
  let B : (Fin 4 → ℕ) → ℝ := fun alpha =>
    ∏ s, Lambda ^ alpha s / (alpha s).factorial
  letI : IsProbabilityMeasure pi0 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure pi1 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  have hLambda : 0 < Lambda := by positivity
  have hsupp0 : ∀ᵐ v ∂pi0, ∀ s, v s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h0 hkappa.le hgamma hrho ha
  have hsupp1 : ∀ᵐ w ∂pi1, ∀ s, w s ∈ Icc 0 Lambda :=
    signedScoreIntensityPrior_ae_mem_Icc
      kappa gamma rho a J D h1 hkappa.le hgamma hrho ha
  have hsupp : ∀ᵐ p ∂pi0.prod pi1,
      (∀ s, p.1 s ∈ Icc 0 Lambda) ∧ (∀ s, p.2 s ∈ Icc 0 Lambda) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hsupp0] with v hv
    filter_upwards [hsupp1] with w hw
    exact ⟨hv, hw⟩
  have hB : Summable B := by
    have h := signedScoreTaylorCoefficient_summable Lambda
      (fun _ : Fin 4 => 0) (fun _ : Fin 4 => 0)
    apply h.congr
    intro alpha
    simp only [signedScoreTaylorCoefficient, B, zero_sub,
      neg_mul_neg, mul_div_cancel_left₀ _ hLambda.ne',
      Fin.prod_univ_four]
  have hseries := MeasureTheory.hasSum_integral_of_dominated_convergence
    (μ := pi0.prod pi1) (fun alpha (_p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) => B alpha)
    (F := fun alpha (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) =>
      signedScoreTaylorCoefficient Lambda alpha p.1 p.2)
    (f := fun (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) => Real.exp (∑ s : Fin 4,
      (p.1 s - Lambda) * (p.2 s - Lambda) / Lambda))
    (fun _alpha => by
      apply StronglyMeasurable.aestronglyMeasurable
      unfold signedScoreTaylorCoefficient
      fun_prop)
    (fun alpha => by
      filter_upwards [hsupp] with p hp
      exact abs_signedScoreTaylorCoefficient_le
        Lambda alpha p.1 p.2 hLambda hp.1 hp.2)
    (by
      filter_upwards with p
      exact hB)
    (by
      simpa only [Pi.one_apply] using
        (integrable_const (μ := pi0.prod pi1) (∑' alpha, B alpha)))
    (by
      filter_upwards with p
      rw [signedScore_exp_eq_tsum_taylorCoefficient]
      exact (signedScoreTaylorCoefficient_summable Lambda p.1 p.2).hasSum)
  simpa only [Lambda, pi0, pi1] using hseries.tsum_eq.symm

/-- The concrete product-prior exponential Gram integral is the sum of
products of its two centered moments, with the exact multi-index factorial
and reference-intensity denominator. -/
lemma signedScoreIntensityPrior_exp_integral_eq_tsum_moments
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ p : (Fin 4 → ℝ) × (Fin 4 → ℝ),
        Real.exp (∑ s : Fin 4,
          (p.1 s - kappa * (J : ℝ)) * (p.2 s - kappa * (J : ℝ)) /
            (kappa * (J : ℝ)))
        ∂(signedScoreIntensityPrior kappa gamma rho a J D h0).prod
          (signedScoreIntensityPrior kappa gamma rho a J D h1)) =
      ∑' alpha : Fin 4 → ℕ,
        ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
            ∂signedScoreIntensityPrior kappa gamma rho a J D h0) *
          (∫ w, ∏ s, (w s - kappa * (J : ℝ)) ^ alpha s
            ∂signedScoreIntensityPrior kappa gamma rho a J D h1)) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            (kappa * (J : ℝ)) ^ (∑ s, alpha s)) := by
  letI : IsProbabilityMeasure
      (signedScoreIntensityPrior kappa gamma rho a J D h0) :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure
      (signedScoreIntensityPrior kappa gamma rho a J D h1) :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  rw [signedScoreIntensityPrior_exp_integral_eq_tsum
    kappa gamma rho a J D h0 h1 hkappa hgamma hrho ha hJ]
  apply tsum_congr
  intro alpha
  let Lambda := kappa * (J : ℝ)
  let c : ℝ := 1 / ((∏ s, ((alpha s).factorial : ℝ)) *
    Lambda ^ (∑ s, alpha s))
  let g : (Fin 4 → ℝ) → ℝ := fun v =>
    ∏ s, (v s - Lambda) ^ alpha s
  have hpoint : (fun p : (Fin 4 → ℝ) × (Fin 4 → ℝ) =>
      signedScoreTaylorCoefficient Lambda alpha p.1 p.2) =
      fun p => c * (g p.1 * g p.2) := by
    funext p
    simp only [signedScoreTaylorCoefficient, Lambda, c, g,
      Fin.prod_univ_four, Fin.sum_univ_four, div_pow, mul_pow, pow_add]
    ring
  rw [hpoint, integral_const_mul, MeasureTheory.integral_prod_mul]
  simp only [c, g, Lambda]
  ring

/-- Each concrete TT, FF, or TF mixture-likelihood Gram term equals the exact
series of products of the corresponding centered moments. -/
lemma signedScoreMixtureLikelihood_inner_intensityPrior_eq_tsum_moments
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (h0 h1 : Bool) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ z, signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D h0) z *
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D h1) z
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) =
      ∑' alpha : Fin 4 → ℕ,
        ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
            ∂signedScoreIntensityPrior kappa gamma rho a J D h0) *
          (∫ w, ∏ s, (w s - kappa * (J : ℝ)) ^ alpha s
            ∂signedScoreIntensityPrior kappa gamma rho a J D h1)) /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            (kappa * (J : ℝ)) ^ (∑ s, alpha s)) := by
  let pi0 := signedScoreIntensityPrior kappa gamma rho a J D h0
  let pi1 := signedScoreIntensityPrior kappa gamma rho a J D h1
  let Lambda := kappa * (J : ℝ)
  letI : IsProbabilityMeasure pi0 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h0 ha hJ
  letI : IsProbabilityMeasure pi1 :=
    signedScoreIntensityPrior_isProbabilityMeasure
      kappa gamma rho a J D h1 ha hJ
  have hLambda : 0 < Lambda := by positivity
  rw [signedScoreMixtureLikelihood_inner_prod Lambda pi0 pi1 hLambda
    (signedScoreLikelihood_joint_integrable_intensityPrior
      kappa gamma rho a J D h0 h1 hkappa hgamma hrho ha hJ)]
  exact signedScoreIntensityPrior_exp_integral_eq_tsum_moments
    kappa gamma rho a J D h0 h1 hkappa hgamma hrho ha hJ

/-- The concrete one-cell squared likelihood distance is exactly the
four-index Taylor series of squared true/false centered-moment differences. -/
lemma signedScoreMixtureLikelihood_sq_sub_integral_eq_tsum_momentDiffSq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ z, (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) =
      ∑' alpha : Fin 4 → ℕ,
        ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
              ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
            (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
              ∂signedScoreIntensityPrior kappa gamma rho a J D false)) ^ 2 /
          ((∏ s, ((alpha s).factorial : ℝ)) *
            (kappa * (J : ℝ)) ^ (∑ s, alpha s)) := by
  rw [signedScoreMixtureLikelihood_sq_sub_integral_intensityPrior_eq
    kappa gamma rho a J D hkappa ha hJ]
  rw [signedScoreMixtureLikelihood_inner_intensityPrior_eq_tsum_moments
    kappa gamma rho a J D true true hkappa hgamma hrho ha hJ]
  rw [signedScoreMixtureLikelihood_inner_intensityPrior_eq_tsum_moments
    kappa gamma rho a J D false false hkappa hgamma hrho ha hJ]
  rw [signedScoreMixtureLikelihood_inner_intensityPrior_eq_tsum_moments
    kappa gamma rho a J D true false hkappa hgamma hrho ha hJ]
  let mT : (Fin 4 → ℕ) → ℝ := fun alpha =>
    ∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
      ∂signedScoreIntensityPrior kappa gamma rho a J D true
  let mF : (Fin 4 → ℕ) → ℝ := fun alpha =>
    ∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
      ∂signedScoreIntensityPrior kappa gamma rho a J D false
  let den : (Fin 4 → ℕ) → ℝ := fun alpha =>
    (∏ s, ((alpha s).factorial : ℝ)) *
      (kappa * (J : ℝ)) ^ (∑ s, alpha s)
  let TT : (Fin 4 → ℕ) → ℝ := fun alpha => mT alpha * mT alpha / den alpha
  let FF : (Fin 4 → ℕ) → ℝ := fun alpha => mF alpha * mF alpha / den alpha
  let TF : (Fin 4 → ℕ) → ℝ := fun alpha => mT alpha * mF alpha / den alpha
  let R : (Fin 4 → ℕ) → ℝ := fun alpha =>
    (mT alpha - mF alpha) ^ 2 / den alpha
  change (∑' alpha, TT alpha) + (∑' alpha, FF alpha) -
      2 * (∑' alpha, TF alpha) = ∑' alpha, R alpha
  have hTT : Summable TT := by
    simpa only [TT, mT, den] using
      signedScoreIntensityPrior_moment_product_summable
        kappa gamma rho a J D true true hkappa hgamma hrho ha hJ
  have hFF : Summable FF := by
    simpa only [FF, mF, den] using
      signedScoreIntensityPrior_moment_product_summable
        kappa gamma rho a J D false false hkappa hgamma hrho ha hJ
  have hTF : Summable TF := by
    simpa only [TF, mT, mF, den] using
      signedScoreIntensityPrior_moment_product_summable
        kappa gamma rho a J D true false hkappa hgamma hrho ha hJ
  have hseries : HasSum (fun alpha => TT alpha + FF alpha - 2 * TF alpha)
      ((∑' alpha, TT alpha) + (∑' alpha, FF alpha) -
        2 * (∑' alpha, TF alpha)) :=
    (hTT.hasSum.add hFF.hasSum).sub (hTF.hasSum.mul_left 2)
  have hR : HasSum R ((∑' alpha, TT alpha) + (∑' alpha, FF alpha) -
      2 * (∑' alpha, TF alpha)) := by
    apply hseries.congr_fun
    intro alpha
    simp only [TT, FF, TF, R]
    ring
  exact hR.tsum_eq.symm

/-- The concrete true and false intensity priors match raw centered-product
moments through total degree `3J`. -/
lemma signedScoreIntensityPrior_raw_centered_moments_eq
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (alpha : Fin 4 → ℕ) (ha : 0 < a) (hJ : 1 ≤ J)
    (hdeg : (∑ i, alpha i) ≤ 3 * J) :
    (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
      ∂signedScoreIntensityPrior kappa gamma rho a J D true) =
    ∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
      ∂signedScoreIntensityPrior kappa gamma rho a J D false := by
  simpa only [signedScoreCenteredMonomial_eq_prod] using
    signedScoreIntensityPrior_centered_moments_eq
      kappa gamma rho a J D alpha ha hJ hdeg

/-- Flipping the latent sign changes a centered monomial by at most the
coordinatewise sign radius times its total degree. -/
lemma abs_signedScoreCenteredMonomial_intensity_sign_sub_le
    (kappa gamma rho a x : ℝ) (J : ℕ) (alpha : Fin 4 → ℕ)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hrho : rho ∈ Icc (0 : ℝ) 2) (ha : 0 < a) (hx : x ∈ Icc a 1) :
    |signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
        (signedScoreIntensity kappa gamma rho J
          (latentFromIntensity true a x)) -
      signedScoreCenteredMonomial (kappa * (J : ℝ)) alpha
        (signedScoreIntensity kappa gamma rho J
          (latentFromIntensity false a x))| ≤
      ((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
        (kappa * (J : ℝ)) ^ (∑ s, alpha s) := by
  let Lambda := kappa * (J : ℝ)
  let vT := signedScoreIntensity kappa gamma rho J
    (latentFromIntensity true a x)
  let vF := signedScoreIntensity kappa gamma rho J
    (latentFromIntensity false a x)
  let cT : Fin 4 → ℝ := fun s => vT s - Lambda
  let cF : Fin 4 → ℝ := fun s => vF s - Lambda
  have hLambda : 0 ≤ Lambda := by positivity
  have hT := signedScoreIntensity_latentFromIntensity_mem_Icc
    kappa gamma rho a x J true hkappa hgamma hrho ha hx
  have hF := signedScoreIntensity_latentFromIntensity_mem_Icc
    kappa gamma rho a x J false hkappa hgamma hrho ha hx
  have hcT (s : Fin 4) : |cT s| ≤ Lambda := by
    have hs := hT s
    change vT s ∈ Icc 0 Lambda at hs
    rw [abs_le]
    exact ⟨by dsimp [cT]; linarith [hs.1],
      by dsimp [cT]; linarith [hs.2]⟩
  have hcF (s : Fin 4) : |cF s| ≤ Lambda := by
    have hs := hF s
    change vF s ∈ Icc 0 Lambda at hs
    rw [abs_le]
    exact ⟨by dsimp [cF]; linarith [hs.1],
      by dsimp [cF]; linarith [hs.2]⟩
  have hgr : 0 ≤ gamma * rho / 8 :=
    div_nonneg (mul_nonneg hgamma.1 hrho.1) (by norm_num)
  have hdelta : 0 ≤ (gamma * rho / 8) * Lambda :=
    mul_nonneg hgr hLambda
  have hx0 : 0 < x := ha.trans_le hx.1
  have hxa : 0 < x + a := add_pos hx0 ha
  have hdist (s : Fin 4) : |cT s - cF s| ≤ (gamma * rho / 8) * Lambda := by
    have hx1 : x ≤ 1 := hx.2
    fin_cases s
    · have heq : cT 0 = cF 0 := by
        simp [cT, cF, vT, vF, signedScoreIntensity, latentFromIntensity,
          hx0.ne', latentIntensity, latentPropensity]
      change |cT 0 - cF 0| ≤ (gamma * rho / 8) * Lambda
      rw [heq, sub_self, abs_zero]
      exact hdelta
    · have heq : cT 1 = cF 1 := by
        simp [cT, cF, vT, vF, signedScoreIntensity, latentFromIntensity,
          hx0.ne', latentIntensity, latentPropensity]
      change |cT 1 - cF 1| ≤ (gamma * rho / 8) * Lambda
      rw [heq, sub_self, abs_zero]
      exact hdelta
    · have heq : cT 2 - cF 2 = -x * ((gamma * rho / 8) * Lambda) := by
        dsimp [cT, cF, vT, vF, Lambda]
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne',
          latentIntensity, latentPropensity, latentScore, latentSignValue,
          latentSign]
        field_simp [hx0.ne', hxa.ne']
        ring
      change |cT 2 - cF 2| ≤ (gamma * rho / 8) * Lambda
      rw [heq, abs_mul, abs_neg, abs_of_nonneg hx0.le,
        abs_of_nonneg hdelta]
      simpa using mul_le_mul_of_nonneg_right hx1 hdelta
    · have heq : cT 3 - cF 3 = x * ((gamma * rho / 8) * Lambda) := by
        dsimp [cT, cF, vT, vF, Lambda]
        simp [signedScoreIntensity, latentFromIntensity, hx0.ne',
          latentIntensity, latentPropensity, latentScore, latentSignValue,
          latentSign]
        field_simp [hx0.ne', hxa.ne']
        ring
      change |cT 3 - cF 3| ≤ (gamma * rho / 8) * Lambda
      rw [heq, abs_mul, abs_of_nonneg hx0.le, abs_of_nonneg hdelta]
      simpa using mul_le_mul_of_nonneg_right hx1 hdelta
  have hmono := abs_signedScoreCenteredMonomial_sub_le_radius
    Lambda (gamma * rho / 8) alpha cT cF hLambda hgr hcT hcF hdist
  simpa only [signedScoreCenteredMonomial_eq_prod, cT, cF, vT, vF,
    zero_add, sub_zero] using hmono

private lemma tiltedSide_integrable_any_tail (a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J)) (h : Bool)
    (f : ℝ → ℝ) : Integrable f (tiltedSide a J D h) := by
  classical
  rw [tiltedSide]
  apply Integrable.add_measure
  · apply integrable_finsetSum_measure.2
    intro i _
    exact (integrable_dirac (by finiteness)).smul_measure (by simp)
  · exact (integrable_dirac (by finiteness)).smul_measure (by simp)

/-- The true and false concrete intensity priors differ in their centered
multi-index moment by at most the sign-coupling radius. -/
lemma abs_signedScoreIntensityPrior_raw_moment_sub_le
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (alpha : Fin 4 → ℕ) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    |(∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
      (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D false)| ≤
      ((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
        (kappa * (J : ℝ)) ^ (∑ s, alpha s) := by
  let Lambda := kappa * (J : ℝ)
  let gI : (Fin 4 → ℝ) → ℝ := fun v =>
    ∏ s, (v s - Lambda) ^ alpha s
  let g : LatentCell → ℝ := fun z =>
    gI (signedScoreIntensity kappa gamma rho J z)
  let B : ℝ := ((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
    Lambda ^ (∑ s, alpha s)
  have hLambda : 0 ≤ Lambda := by positivity
  have hgr : 0 ≤ gamma * rho / 8 :=
    div_nonneg (mul_nonneg hgamma.1 hrho.1) (by norm_num)
  have hB : 0 ≤ B := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hgr)
      (pow_nonneg hLambda _)
  have hgI : StronglyMeasurable gI := by
    dsimp [gI]
    fun_prop
  have hg : StronglyMeasurable g :=
    hgI.comp_measurable (signedScoreIntensity_measurable kappa gamma rho J)
  have hmap (s t : Bool) : Integrable g
      (Measure.map (latentFromIntensity s a) (tiltedSide a J D t)) := by
    rw [integrable_map_measure hg.aestronglyMeasurable
      (latentFromIntensity_measurable s a).aemeasurable]
    exact tiltedSide_integrable_any_tail a J D t (g ∘ latentFromIntensity s a)
  have hside (t : Bool) :
      |∫ x, g (latentFromIntensity true a x) -
          g (latentFromIntensity false a x) ∂tiltedSide a J D t| ≤ B := by
    letI : IsProbabilityMeasure (tiltedSide a J D t) :=
      tiltedSide_isProbabilityMeasure a J D t ha
    have hd : Integrable (fun x => g (latentFromIntensity true a x) -
        g (latentFromIntensity false a x)) (tiltedSide a J D t) :=
      (tiltedSide_integrable_any_tail a J D t _).sub
        (tiltedSide_integrable_any_tail a J D t _)
    calc
      |∫ x, g (latentFromIntensity true a x) -
          g (latentFromIntensity false a x) ∂tiltedSide a J D t| ≤
          ∫ x, |g (latentFromIntensity true a x) -
            g (latentFromIntensity false a x)| ∂tiltedSide a J D t :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _x, B ∂tiltedSide a J D t := by
        apply integral_mono_ae hd.abs (integrable_const B)
        filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D t] with x hx
        rcases hx with rfl | hx
        · simp [g, gI, latentFromIntensity, signedScoreIntensity_zero, hB]
        · simpa only [g, gI, Lambda, signedScoreCenteredMonomial_eq_prod] using
            abs_signedScoreCenteredMonomial_intensity_sign_sub_le
              kappa gamma rho a x J alpha hkappa hgamma hrho ha hx
      _ = B := by simp
  rw [signedScoreIntensityPrior, signedScoreIntensityPrior,
    integral_map_of_stronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J) hgI,
    integral_map_of_stronglyMeasurable
      (signedScoreIntensity_measurable kappa gamma rho J) hgI]
  change |(∫ z, g z ∂oneCellPrior a J D true) -
    (∫ z, g z ∂oneCellPrior a J D false)| ≤ B
  have hone (h : Bool) :
      (∫ z, g z ∂oneCellPrior a J D h) =
        (ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
        (ENNReal.ofReal (1 - 1 / (J : ℝ))).toReal *
          ((1 / 2 : ENNReal).toReal *
              ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D (!h) +
            (1 / 2 : ENNReal).toReal *
              ∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D h) := by
    have href : Integrable g
        (ENNReal.ofReal (1 / (J : ℝ)) • Measure.dirac referenceLatent) :=
      (integrable_dirac (by finiteness)).smul_measure (by simp)
    have hfalse : Integrable g
        ((1 / 2 : ENNReal) •
          Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h))) :=
      (hmap false (!h)).smul_measure (by norm_num)
    have htrue : Integrable g
        ((1 / 2 : ENNReal) •
          Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
      (hmap true h).smul_measure (by norm_num)
    have hmix : Integrable g
        ((1 / 2 : ENNReal) •
            Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h)) +
          (1 / 2 : ENNReal) •
            Measure.map (latentFromIntensity true a) (tiltedSide a J D h)) :=
      hfalse.add_measure htrue
    have hscaled : Integrable g
        (ENNReal.ofReal (1 - 1 / (J : ℝ)) •
          ((1 / 2 : ENNReal) •
              Measure.map (latentFromIntensity false a) (tiltedSide a J D (!h)) +
            (1 / 2 : ENNReal) •
              Measure.map (latentFromIntensity true a) (tiltedSide a J D h))) :=
      hmix.smul_measure (by simp)
    rw [oneCellPrior, integral_add_measure href hscaled,
      integral_smul_measure, integral_dirac, integral_smul_measure,
      integral_add_measure hfalse htrue,
      integral_smul_measure, integral_smul_measure,
      integral_map_of_stronglyMeasurable
        (latentFromIntensity_measurable false a) hg,
      integral_map_of_stronglyMeasurable
        (latentFromIntensity_measurable true a) hg]
    rfl
  rw [hone true, hone false]
  simp only [Bool.not_true, Bool.not_false]
  let w : ℝ := (ENNReal.ofReal (1 - 1 / (J : ℝ))).toReal
  let AT : ℝ := ∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D true
  let AF : ℝ := ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D true
  let BT : ℝ := ∫ x, g (latentFromIntensity true a x) ∂tiltedSide a J D false
  let BF : ℝ := ∫ x, g (latentFromIntensity false a x) ∂tiltedSide a J D false
  have hsT : |AT - AF| ≤ B := by
    have h := hside true
    rw [integral_sub
      (tiltedSide_integrable_any_tail a J D true _)
      (tiltedSide_integrable_any_tail a J D true _)] at h
    exact h
  have hsF : |BT - BF| ≤ B := by
    have h := hside false
    rw [integral_sub
      (tiltedSide_integrable_any_tail a J D false _)
      (tiltedSide_integrable_any_tail a J D false _)] at h
    exact h
  have hJr : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hJpos : (0 : ℝ) < J := lt_of_lt_of_le (by norm_num) hJr
  have honeDiv : 1 / (J : ℝ) ≤ 1 := by
    rw [div_le_iff₀ hJpos]
    simpa using hJr
  have hw : w ∈ Icc (0 : ℝ) 1 := by
    dsimp [w]
    rw [ENNReal.toReal_ofReal]
    · constructor
      · linarith
      · exact sub_le_self _ (one_div_nonneg.mpr (by positivity : (0 : ℝ) ≤ J))
    · linarith
  have halg :
      (ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
            w * ((1 / 2 : ENNReal).toReal * BF +
              (1 / 2 : ENNReal).toReal * AT) -
          ((ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
            w * ((1 / 2 : ENNReal).toReal * AF +
              (1 / 2 : ENNReal).toReal * BT)) =
        w / 2 * ((AT - AF) - (BT - BF)) := by
    norm_num
    ring
  change |(ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
      w * ((1 / 2 : ENNReal).toReal * BF +
        (1 / 2 : ENNReal).toReal * AT) -
      ((ENNReal.ofReal (1 / (J : ℝ))).toReal * g referenceLatent +
        w * ((1 / 2 : ENNReal).toReal * AF +
          (1 / 2 : ENNReal).toReal * BT))| ≤ B
  rw [halg, abs_mul, abs_of_nonneg (div_nonneg hw.1 (by norm_num))]
  calc
    w / 2 * |AT - AF - (BT - BF)| ≤
        w / 2 * (|AT - AF| + |BT - BF|) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hw.1 (by norm_num))
      have ht := abs_sub_le (AT - AF) (0 : ℝ) (BT - BF)
      simpa only [sub_zero, zero_sub, abs_neg] using ht
    _ ≤ w / 2 * (B + B) := by gcongr
    _ ≤ B := by nlinarith [hw.2]

/-- Squaring the concrete moment-difference bound and dividing by the exact
Taylor denominator preserves the factorial weight. -/
lemma signedScoreIntensityPrior_squared_coefficient_le
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (alpha : Fin 4 → ℕ) (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
        (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
          ∂signedScoreIntensityPrior kappa gamma rho a J D false)) ^ 2 /
        ((∏ s, ((alpha s).factorial : ℝ)) *
          (kappa * (J : ℝ)) ^ (∑ s, alpha s)) ≤
      (((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
          (kappa * (J : ℝ)) ^ (∑ s, alpha s)) ^ 2 /
        ((∏ s, ((alpha s).factorial : ℝ)) *
          (kappa * (J : ℝ)) ^ (∑ s, alpha s)) := by
  let d : ℝ :=
    (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
        ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
      (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
        ∂signedScoreIntensityPrior kappa gamma rho a J D false)
  let B : ℝ := ((∑ s, alpha s : ℕ) : ℝ) * (gamma * rho / 8) *
    (kappa * (J : ℝ)) ^ (∑ s, alpha s)
  have habs : |d| ≤ B := by
    exact abs_signedScoreIntensityPrior_raw_moment_sub_le
      kappa gamma rho a J D alpha hkappa.le hgamma hrho ha hJ
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (mul_nonneg hgamma.1 hrho.1) (by norm_num)))
      (pow_nonneg (by positivity) _)
  have hsq : d ^ 2 ≤ B ^ 2 := by
    apply (sq_le_sq).2
    simpa only [abs_of_nonneg hB] using habs
  have hden : 0 ≤ (∏ s, ((alpha s).factorial : ℝ)) *
      (kappa * (J : ℝ)) ^ (∑ s, alpha s) := by positivity
  exact div_le_div_of_nonneg_right hsq hden

lemma signedScoreMixtureLikelihood_sq_sub_integral_eq_tsum_highDegree
    (kappa gamma rho a : ℝ) (J : ℕ)
    (D : FiniteMomentDual (rationalTarget a) a 1 (3 * J))
    (hkappa : 0 < kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1) (hrho : rho ∈ Icc (0 : ℝ) 2)
    (ha : 0 < a) (hJ : 1 ≤ J) :
    (∫ z, (signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D true) z -
        signedScoreMixtureLikelihood (kappa * (J : ℝ))
          (signedScoreIntensityPrior kappa gamma rho a J D false) z) ^ 2
        ∂signedScoreReferenceLaw (kappa * (J : ℝ))) =
      ∑' alpha : Fin 4 → ℕ,
        if 3 * J < ∑ s, alpha s then
          ((∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
                ∂signedScoreIntensityPrior kappa gamma rho a J D true) -
              (∫ v, ∏ s, (v s - kappa * (J : ℝ)) ^ alpha s
                ∂signedScoreIntensityPrior kappa gamma rho a J D false)) ^ 2 /
            ((∏ s, ((alpha s).factorial : ℝ)) *
              (kappa * (J : ℝ)) ^ (∑ s, alpha s))
        else 0 := by
  rw [signedScoreMixtureLikelihood_sq_sub_integral_eq_tsum_momentDiffSq
    kappa gamma rho a J D hkappa hgamma hrho ha hJ]
  apply tsum_congr
  intro alpha
  by_cases hdeg : (∑ s, alpha s) ≤ 3 * J
  · rw [if_neg (Nat.not_lt_of_ge hdeg)]
    rw [signedScoreIntensityPrior_raw_centered_moments_eq
      kappa gamma rho a J D alpha ha hJ hdeg]
    norm_num
  · rw [if_pos (Nat.lt_of_not_ge hdeg)]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
