module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionInverseL2

/-! # Test-function pairing for the inverse truncations

Fubini transfers the normalized inverse angular integral to an integrable test
function. This is the adjoint-identification step in reflection-budget roadmap (3).
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Absolute integrability of the two-variable inverse pairing kernel.](goal) Under [the stated conditions](hyp:hψ,hφ). -/
-- @node: reflectionInversePairing_integrable
lemma reflectionInversePairing_integrable {p : ℕ}
    {ψ φ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : Integrable ψ volume) (hφ : Integrable φ volume) :
    Integrable (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      Complex.exp (Complex.I * ((∑ j, z.2 j * z.1 j : ℝ) : ℂ)) *
        (φ z.1 * ψ z.2)) (volume.prod volume) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) =>
      Complex.exp (Complex.I * ((∑ j, z.2 j * z.1 j : ℝ) : ℂ))) := by
    fun_prop
  exact (hφ.mul_prod hψ).bdd_mul (c := 1) hc.aestronglyMeasurable
    (Eventually.of_forall fun z => by simp [Complex.norm_exp])

/-- [ Bilinear pairing with an inverse integral transfers the inverse transform to
an arbitrary L¹ test. No L¹ assumption on the inverse integral is needed.](goal) Under [the stated conditions](hyp:hψ,hφ). -/
-- @node: reflectionInverseIntegral_pairing
lemma reflectionInverseIntegral_pairing {p : ℕ}
    {ψ φ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : Integrable ψ volume) (hφ : Integrable φ volume) :
    (∫ u, φ u * Fourier ψ (-u)) = ∫ ω, Fourier φ (-ω) * ψ ω := by
  have hswap := integral_integral_swap
    (f := fun u ω => Complex.exp (Complex.I * ((∑ j, ω j * u j : ℝ) : ℂ)) *
      (φ u * ψ ω)) (reflectionInversePairing_integrable hψ hφ)
  unfold Fourier
  simp only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg, neg_neg]
  simp only [mul_smul_comm, smul_mul_assoc]
  simp_rw [← integral_const_mul, ← integral_mul_const]
  simp only [integral_smul]
  congr 1
  convert hswap using 1 <;> congr 1 <;> funext x <;> congr 1 <;> funext y
  · simp only [mul_comm, mul_left_comm, mul_assoc]
  · simp only [mul_comm, mul_assoc]

/-- [ The actual ball-truncated smooth inverse integrals satisfy the test pairing
used to identify their spatial L² limit in the endpoint proof.](goal) Under [the stated conditions](hyp:hψ,hφ). -/
-- @node: reflectionSmoothApproximation_pairing
lemma reflectionSmoothApproximation_pairing {p : ℕ}
    {ψ φ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : MemLp ψ 2 volume) (hφ : Integrable φ volume) (R : ℝ) :
    (∫ u, φ u * reflectionSmoothApproximation ψ R u) =
      ∫ ω, Fourier φ (-ω) * reflectionFrequencyTruncation ψ R ω :=
  reflectionInverseIntegral_pairing (reflectionFrequencyTruncation_integrable hψ R) hφ

/-- Conjugation exchanges the forward angular kernel and the inverse kernel.
The real unitary prefactor is unchanged. [The asserted mathematical result follows](goal). -/
-- @node: reflectionFourier_conj_neg
lemma reflectionFourier_conj_neg {p : ℕ}
    (φ : EuclideanSpace ℝ (Fin p) → ℂ) (ω : EuclideanSpace ℝ (Fin p)) :
    Fourier (fun u => star (φ u)) (-ω) = star (Fourier φ ω) := by
  unfold Fourier
  rw [star_smul]
  simp only [star_trivial, Complex.star_def]
  rw [← integral_conj]
  simp only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg, neg_neg]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with u
  simp [map_mul, ← Complex.exp_conj]

/-- Sesquilinear pairing identifies the inverse integral with the adjoint of
the angular transform on integrable tests. Under [the stated conditions](hyp:hψ,hφ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionInverseIntegral_adjoint_pairing
lemma reflectionInverseIntegral_adjoint_pairing {p : ℕ}
    {ψ φ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : Integrable ψ volume) (hφ : Integrable φ volume) :
    (∫ u, star (φ u) * Fourier ψ (-u)) =
      ∫ ω, star (Fourier φ ω) * ψ ω := by
  have hc : Integrable (fun u => star (φ u)) volume := by
    exact hφ.mono (by fun_prop) (Eventually.of_forall fun u => by simp)
  have h := reflectionInverseIntegral_pairing hψ hc
  simpa only [reflectionFourier_conj_neg] using h

/-- [ The smooth truncations obey the exact adjoint pairing, with the genuine
Fourier ball cutoff and the paper's unitary angular normalization.](goal) Under [the stated conditions](hyp:hψ,hφ). -/
-- @node: reflectionSmoothApproximation_adjoint_pairing
lemma reflectionSmoothApproximation_adjoint_pairing {p : ℕ}
    {ψ φ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : MemLp ψ 2 volume) (hφ : Integrable φ volume) (R : ℝ) :
    (∫ u, star (φ u) * reflectionSmoothApproximation ψ R u) =
      ∫ ω, star (Fourier φ ω) * reflectionFrequencyTruncation ψ R ω :=
  reflectionInverseIntegral_adjoint_pairing
    (reflectionFrequencyTruncation_integrable hψ R) hφ

/-- [ The inverse integral of an L¹∩L² frequency profile agrees with the
reflected, normalized dilation of Mathlib's actual Fourier L² representative.
Pulling the a.e. identity through negation is justified by measure preservation.](goal) Under [the stated conditions](hyp:hψ1,hψ2). -/
-- @node: reflectionInverseIntegral_ae_L2
lemma reflectionInverseIntegral_ae_L2 {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) :
    (fun u => Fourier ψ (-u)) =ᵐ[volume] (fun u =>
      Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ (hψ2.toLp ψ))
          ((2 * Real.pi)⁻¹ • (-u))) := by
  exact (Measure.measurePreserving_neg volume).quasiMeasurePreserving.ae
    (Causalean.Mathlib.Analysis.Fourier.angularFourier_ae_L2 ψ hψ1 hψ2)

/-- [ Each constructed truncation has the L² representative required for
adjoint identification; no integrability of its spatial inverse is assumed.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_ae_L2
lemma reflectionSmoothApproximation_ae_L2 {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : MemLp ψ 2 volume) (R : ℝ) :
    reflectionSmoothApproximation ψ R =ᵐ[volume] (fun u =>
      Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
        (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ
          ((reflectionFrequencyTruncation_memLp hψ R).toLp
            (reflectionFrequencyTruncation ψ R))) ((2 * Real.pi)⁻¹ • (-u))) :=
  reflectionInverseIntegral_ae_L2 (reflectionFrequencyTruncation_integrable hψ R)
    (reflectionFrequencyTruncation_memLp hψ R)

/-- [ Unweighted frequency truncation error vanishes for every measurable L² profile.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionFrequencyTruncation_error_tendsto
lemma reflectionFrequencyTruncation_error_tendsto {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero, mul_one] using
    reflectionFrequencyTruncation_weighted_error_tendsto 0 hm (by
      simpa only [Causalean.Mathlib.Analysis.Fourier.l2Energy, Real.rpow_zero, mul_one] using
        (Causalean.Mathlib.Analysis.Fourier.l2Energy_lt_top_of_memLp ψ hψ).ne)

/-- [ For an L¹∩L² profile the spatial error relative to its actual inverse integral
has exactly the frequency truncation error, with unit constant.](goal) Under [the stated conditions](hyp:hψ1,hψ2). -/
-- @node: reflectionSmoothApproximation_inverse_error_energy
lemma reflectionSmoothApproximation_inverse_error_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) (R : ℝ) :
    (∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ R u - Fourier ψ (-u)‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖reflectionFrequencyTruncation ψ R ω - ψ ω‖ ^ 2) :=
  reflectionInverseIntegral_difference_energy
    (reflectionFrequencyTruncation_integrable hψ2 R)
    (reflectionFrequencyTruncation_memLp hψ2 R) hψ1 hψ2

/-- [ The smooth inverses converge in squared spatial L² error to the actual
inverse integral whenever the profile is L¹∩L².](goal) Under [the stated conditions](hyp:hm,hψ1,hψ2). -/
-- @node: reflectionSmoothApproximation_inverse_error_tendsto
lemma reflectionSmoothApproximation_inverse_error_tendsto {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) :
    Tendsto (fun n : ℕ => ∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ (n : ℝ) u - Fourier ψ (-u)‖ ^ 2))
      atTop (𝓝 0) := by
  simpa only [reflectionSmoothApproximation_inverse_error_energy hψ1 hψ2] using
    reflectionFrequencyTruncation_error_tendsto hm hψ2

/-- [ The limit in spatial L² is the class of the genuine inverse integral,
rather than an unidentified completeness witness, for L¹∩L² profiles.](goal) Under [the stated conditions](hyp:hm,hψ1,hψ2). -/
-- @node: reflectionSmoothApproximation_tendsto_inverse_L2
lemma reflectionSmoothApproximation_tendsto_inverse_L2 {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) :
    Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ2 (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) atTop
      (𝓝 ((reflectionInverseIntegral_memLp hψ1 hψ2).toLp
        (fun u => Fourier ψ (-u)))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => reflectionSmoothApproximation ψ (n : ℝ))
    (fun n => reflectionSmoothApproximation_memLp hψ2 (n : ℝ))
    (fun u => Fourier ψ (-u)) (reflectionInverseIntegral_memLp hψ1 hψ2)).mpr
  have he := reflectionSmoothApproximation_inverse_error_tendsto hm hψ1 hψ2
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp he
  norm_num at hr
  convert hr using 1
  funext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  norm_num only [ENNReal.toReal_ofNat, Pi.sub_apply, ENNReal.rpow_two]

/-- [ Any spatial L² limit produced by completeness has the normalized reflected
Mathlib Fourier representative for an L¹∩L² frequency profile.](goal) Under [the stated conditions](hyp:hm,hψ1,hψ2,hH). -/
-- @node: reflectionSmoothApproximation_limit_ae_inverse
lemma reflectionSmoothApproximation_limit_ae_inverse {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume)
    (H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))))
    (hH : Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ2 (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) atTop (𝓝 H)) :
    H =ᵐ[volume] (fun u => Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ (hψ2.toLp ψ))
        ((2 * Real.pi)⁻¹ • (-u))) := by
  have hident := tendsto_nhds_unique hH
    (reflectionSmoothApproximation_tendsto_inverse_L2 hm hψ1 hψ2)
  rw [hident]
  exact (MemLp.coeFn_toLp (reflectionInverseIntegral_memLp hψ1 hψ2)).trans
    (reflectionInverseIntegral_ae_L2 hψ1 hψ2)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
