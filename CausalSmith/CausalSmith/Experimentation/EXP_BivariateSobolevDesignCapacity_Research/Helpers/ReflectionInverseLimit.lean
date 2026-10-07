module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionInversePairing

/-! # Identification of the inverse-truncation L² limit

The normalized reflected Mathlib Fourier representative gives the inverse
angular transform on all frequency L² classes. Its exact energy and distance
identities identify the limit in reflection-budget roadmap (3), without L¹
regularity of the full frequency profile.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology FourierTransform
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ The inverse angular L² representative is the normalized, dilated, reflected
Mathlib Fourier L² transform. The input is a frequency equivalence class. -/
-- @node: reflectionInverseL2Representative
def reflectionInverseL2Representative {p : ℕ}
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))))
    (u : EuclideanSpace ℝ (Fin p)) : ℂ :=
  Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ)
      ((2 * Real.pi)⁻¹ • (-u))

/-- The dilation and reflection used by the inverse preserve null sets.](goal) This uses [the stated conclusion](goal). -/
-- @node: reflectionInverseDilation_quasiMeasurePreserving
lemma reflectionInverseDilation_quasiMeasurePreserving (p : ℕ) :
    Measure.QuasiMeasurePreserving
      (fun u : EuclideanSpace ℝ (Fin p) => (2 * Real.pi)⁻¹ • (-u)) volume volume :=
  (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero (by positivity))).comp
    (Measure.measurePreserving_neg volume).quasiMeasurePreserving

/-- [ The inverse angular representative is strongly measurable almost everywhere.](goal) -/
-- @node: reflectionInverseL2Representative_aestronglyMeasurable
lemma reflectionInverseL2Representative_aestronglyMeasurable {p : ℕ}
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    AEStronglyMeasurable (reflectionInverseL2Representative ψ) volume := by
  exact ((Lp.aestronglyMeasurable
    (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ)).comp_quasiMeasurePreserving
      (reflectionInverseDilation_quasiMeasurePreserving p)).const_smul
        (Causalean.Mathlib.Analysis.Fourier.angularPrefactor p)

/-- [ The squared energy of any L² representative is its squared extended norm.](goal) -/
-- @node: reflectionLp_energy_eq_enorm_sq
lemma reflectionLp_energy_eq_enorm_sq {p : ℕ}
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    (∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2)) = ‖ψ‖ₑ ^ 2 := by
  rw [Lp.enorm_def]
  simpa only [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm,
    ENNReal.rpow_two, NNReal.coe_ofNat, ENNReal.coe_ofNat] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := fun ω => ψ ω) (μ := volume)
      (p := 2) (by norm_num)).symm

/-- [ Spatial reflection, the exact Jacobian, and Fourier unitarity give the
inverse energy with constant one for every L² frequency class.](goal) -/
-- @node: reflectionInverseL2Representative_energy
lemma reflectionInverseL2Representative_energy {p : ℕ}
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionInverseL2Representative ψ u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2) := by
  let F := Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ
  have hd := Causalean.Mathlib.Analysis.Fourier.l2Energy_normalized_dilation
    (fun u => F u)
  calc
    _ = ∫⁻ u, ENNReal.ofReal
        (‖Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
          F ((2 * Real.pi)⁻¹ • u)‖ ^ 2) :=
      (Measure.measurePreserving_neg volume).lintegral_comp_emb
        (MeasurableEquiv.neg _).measurableEmbedding _
    _ = ∫⁻ u, ENNReal.ofReal (‖F u‖ ^ 2) := hd
    _ = ‖F‖ₑ ^ 2 := reflectionLp_energy_eq_enorm_sq F
    _ = ‖ψ‖ₑ ^ 2 := by
      congr 1
      simpa only [F, ofReal_norm] using congrArg ENNReal.ofReal
        ((Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ).norm_map ψ)
    _ = _ := (reflectionLp_energy_eq_enorm_sq ψ).symm

/-- [ The inverse representative has finite L² norm, without an L¹ premise.](goal) -/
-- @node: reflectionInverseL2Representative_memLp
lemma reflectionInverseL2Representative_memLp {p : ℕ}
    (ψ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    MemLp (reflectionInverseL2Representative ψ) 2 volume := by
  refine ⟨reflectionInverseL2Representative_aestronglyMeasurable ψ, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  simp only [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [reflectionInverseL2Representative_energy]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity)
    (Causalean.Mathlib.Analysis.Fourier.l2Energy_lt_top_of_memLp
      (fun ω => ψ ω) (Lp.memLp ψ)).ne

/-- [ Subtraction of inverse representatives agrees almost everywhere with the
inverse of the difference class; the a.e. Fourier identity is pulled through a
map that preserves null sets.](goal) -/
-- @node: reflectionInverseL2Representative_sub
lemma reflectionInverseL2Representative_sub {p : ℕ}
    (ψ χ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    reflectionInverseL2Representative (ψ - χ) =ᵐ[volume]
      reflectionInverseL2Representative ψ - reflectionInverseL2Representative χ := by
  have h := (reflectionInverseDilation_quasiMeasurePreserving p).ae
    (Lp.coeFn_sub
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ ψ)
      (Lp.fourierTransformₗᵢ (EuclideanSpace ℝ (Fin p)) ℂ χ))
  filter_upwards [h] with u hu
  simp only [reflectionInverseL2Representative, map_sub, hu, Pi.sub_apply, smul_sub]

/-- [ The inverse map preserves the exact squared distance between frequency
classes, including profiles with no integrable representative.](goal) -/
-- @node: reflectionInverseL2Representative_difference_energy
lemma reflectionInverseL2Representative_difference_energy {p : ℕ}
    (ψ χ : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p)))) :
    (∫⁻ u, ENNReal.ofReal
      (‖reflectionInverseL2Representative ψ u - reflectionInverseL2Representative χ u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω - χ ω‖ ^ 2) := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal (‖reflectionInverseL2Representative (ψ - χ) u‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [reflectionInverseL2Representative_sub ψ χ] with u hu
      rw [hu, Pi.sub_apply]
    _ = ∫⁻ ω, ENNReal.ofReal (‖(ψ - χ) ω‖ ^ 2) :=
      reflectionInverseL2Representative_energy (ψ - χ)
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [Lp.coeFn_sub ψ χ] with ω hω
      rw [hω, Pi.sub_apply]

/-- Smooth inverse truncations agree with the inverse L² representative of
their frequency truncation class. Under [the stated conditions](hyp:hψ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothApproximation_ae_inverseL2Representative
lemma reflectionSmoothApproximation_ae_inverseL2Representative {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : MemLp ψ 2 volume) (R : ℝ) :
    reflectionSmoothApproximation ψ R =ᵐ[volume]
      reflectionInverseL2Representative ((reflectionFrequencyTruncation_memLp hψ R).toLp
        (reflectionFrequencyTruncation ψ R)) :=
  reflectionSmoothApproximation_ae_L2 hψ R

/-- [ The spatial error relative to the full inverse L² class is exactly the
frequency truncation error, even when the full frequency profile is not L¹.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_inverseL2_error_energy
lemma reflectionSmoothApproximation_inverseL2_error_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ R u -
        reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖reflectionFrequencyTruncation ψ R ω - ψ ω‖ ^ 2) := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal
        (‖reflectionInverseL2Representative
          ((reflectionFrequencyTruncation_memLp hψ R).toLp
            (reflectionFrequencyTruncation ψ R)) u -
          reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2) := by
      apply lintegral_congr_ae
      filter_upwards [reflectionSmoothApproximation_ae_inverseL2Representative hψ R] with u hu
      rw [hu]
    _ = ∫⁻ ω, ENNReal.ofReal
        (‖((reflectionFrequencyTruncation_memLp hψ R).toLp
          (reflectionFrequencyTruncation ψ R)) ω - (hψ.toLp ψ) ω‖ ^ 2) :=
      reflectionInverseL2Representative_difference_energy _ _
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [(reflectionFrequencyTruncation_memLp hψ R).coeFn_toLp,
        hψ.coeFn_toLp] with ω hω hω'
      rw [hω, hω']

/-- [ The genuine smooth inverse truncations converge to the explicit inverse
Fourier L² class of every measurable square-integrable frequency profile.
No integrability assumption on the full frequency profile is used.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionSmoothApproximation_tendsto_inverseL2Representative
lemma reflectionSmoothApproximation_tendsto_inverseL2Representative {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) atTop
      (𝓝 ((reflectionInverseL2Representative_memLp (hψ.toLp ψ)).toLp
        (reflectionInverseL2Representative (hψ.toLp ψ)))) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => reflectionSmoothApproximation ψ (n : ℝ))
    (fun n => reflectionSmoothApproximation_memLp hψ (n : ℝ))
    (reflectionInverseL2Representative (hψ.toLp ψ))
    (reflectionInverseL2Representative_memLp (hψ.toLp ψ))).mpr
  have he : Tendsto (fun n : ℕ => ∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ (n : ℝ) u -
        reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) atTop (𝓝 0) := by
    simpa only [reflectionSmoothApproximation_inverseL2_error_energy hψ] using
      reflectionFrequencyTruncation_error_tendsto hm hψ
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp he
  norm_num at hr
  convert hr using 1
  funext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  norm_num only [ENNReal.toReal_ofNat, Pi.sub_apply, ENNReal.rpow_two]

/-- [ Every completeness limit of the inverse truncations is the explicit
normalized reflected Fourier representative for an arbitrary measurable L²
profile. This identifies the limit used in roadmap (3).](goal) Under [the stated conditions](hyp:hm,hψ,hH). -/
-- @node: reflectionSmoothApproximation_limit_ae_inverseL2Representative
lemma reflectionSmoothApproximation_limit_ae_inverseL2Representative {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume)
    (H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))))
    (hH : Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) atTop (𝓝 H)) :
    H =ᵐ[volume] reflectionInverseL2Representative (hψ.toLp ψ) := by
  have hident := tendsto_nhds_unique hH
    (reflectionSmoothApproximation_tendsto_inverseL2Representative hm hψ)
  rw [hident]
  exact MemLp.coeFn_toLp (reflectionInverseL2Representative_memLp (hψ.toLp ψ))

/-- [ L² class norms recover the squared energy of the supplied representative.](goal) Under [the stated conditions](hyp:hf). -/
-- @node: reflectionToLp_norm_sq
lemma reflectionToLp_norm_sq {p : ℕ}
    {f : EuclideanSpace ℝ (Fin p) → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = (∫⁻ u, ENNReal.ofReal (‖f u‖ ^ 2)).toReal := by
  have he := reflectionLp_energy_eq_enorm_sq (hf.toLp f)
  have hc : (∫⁻ u, ENNReal.ofReal (‖(hf.toLp f) u‖ ^ 2)) =
      ∫⁻ u, ENNReal.ofReal (‖f u‖ ^ 2) := by
    apply lintegral_congr_ae
    filter_upwards [hf.coeFn_toLp] with u hu
    rw [hu]
  rw [hc] at he
  simpa using (congrArg ENNReal.toReal he).symm

/-- [ The L² inner product is the genuine sesquilinear integral of representatives.](goal) Under [the stated conditions](hyp:hf,hg). -/
-- @node: reflectionToLp_inner
lemma reflectionToLp_inner {p : ℕ}
    {f g : EuclideanSpace ℝ (Fin p) → ℂ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℂ (hf.toLp f) (hg.toLp g) = ∫ u, star (f u) * g u := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with u hfu hgu
  simp [hfu, hgu, RCLike.inner_apply, mul_comm]

/-- [ Adjoint pairing and Plancherel give the exact spatial error of a smooth
inverse truncation of the Fourier profile of an L¹∩L² extension. The full
Fourier profile need not be integrable.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionSmoothApproximation_original_error_norm_sq
lemma reflectionSmoothApproximation_original_error_norm_sq {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) (R : ℝ) :
    let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    ‖hG2.toLp G - (reflectionSmoothApproximation_memLp hF R).toLp
      (reflectionSmoothApproximation (Fourier G) R)‖ ^ 2 =
    ‖hF.toLp (Fourier G) - (reflectionFrequencyTruncation_memLp hF R).toLp
      (reflectionFrequencyTruncation (Fourier G) R)‖ ^ 2 := by
  dsimp only
  let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  rw [norm_sub_sq (𝕜 := ℂ), norm_sub_sq (𝕜 := ℂ)]
  have hzero : ‖hG2.toLp G‖ ^ 2 = ‖hF.toLp (Fourier G)‖ ^ 2 := by
    rw [reflectionToLp_norm_sq, reflectionToLp_norm_sq]
    exact congrArg ENNReal.toReal
      (Causalean.Mathlib.Analysis.Fourier.angular_plancherel_integral G hG1 hG2).symm
  have hcut : ‖(reflectionSmoothApproximation_memLp hF R).toLp
      (reflectionSmoothApproximation (Fourier G) R)‖ ^ 2 =
      ‖(reflectionFrequencyTruncation_memLp hF R).toLp
        (reflectionFrequencyTruncation (Fourier G) R)‖ ^ 2 := by
    rw [reflectionToLp_norm_sq, reflectionToLp_norm_sq]
    exact congrArg ENNReal.toReal (reflectionSmoothApproximation_energy hF R)
  have hinner : inner ℂ (hG2.toLp G)
      ((reflectionSmoothApproximation_memLp hF R).toLp
        (reflectionSmoothApproximation (Fourier G) R)) =
      inner ℂ (hF.toLp (Fourier G))
        ((reflectionFrequencyTruncation_memLp hF R).toLp
          (reflectionFrequencyTruncation (Fourier G) R)) := by
    rw [reflectionToLp_inner, reflectionToLp_inner]
    exact reflectionSmoothApproximation_adjoint_pairing hF hG1 R
  rw [hzero, hcut, hinner]

/-- [ The actual frequency truncation classes converge to the original frequency
class in L², using the proved dominated-convergence error estimate.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionFrequencyTruncation_tendsto_L2
lemma reflectionFrequencyTruncation_tendsto_L2 {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    Tendsto (fun n : ℕ => (reflectionFrequencyTruncation_memLp hψ (n : ℝ)).toLp
      (reflectionFrequencyTruncation ψ (n : ℝ))) atTop (𝓝 (hψ.toLp ψ)) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
    (fun n : ℕ => reflectionFrequencyTruncation ψ (n : ℝ))
    (fun n => reflectionFrequencyTruncation_memLp hψ (n : ℝ)) ψ hψ).mpr
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp
    (reflectionFrequencyTruncation_error_tendsto hm hψ)
  norm_num at hr
  convert hr using 1
  funext n
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  congr 1
  norm_num only [ENNReal.toReal_ofNat, Pi.sub_apply, ENNReal.rpow_two]

/-- [ The inverse truncations of an extension's angular Fourier profile converge
to that very extension in spatial L². Adjoint pairing supplies the cross term
and Plancherel supplies both norms, so no Fourier inversion integrability gate
is imposed on the untruncated profile.](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionSmoothApproximation_tendsto_original
lemma reflectionSmoothApproximation_tendsto_original {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hF (n : ℝ)).toLp
      (reflectionSmoothApproximation (Fourier G) (n : ℝ))) atTop (𝓝 (hG2.toLp G)) := by
  dsimp only
  let hF : MemLp (Fourier G) 2 volume :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  have hm : Measurable (Fourier G) :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_measurable G hG1
  have ht := tendsto_iff_dist_tendsto_zero.mp
    (reflectionFrequencyTruncation_tendsto_L2 hm hF)
  apply tendsto_iff_dist_tendsto_zero.mpr
  convert ht using 1
  funext n
  rw [dist_comm, dist_eq_norm, dist_comm, dist_eq_norm]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (reflectionSmoothApproximation_original_error_norm_sq hG1 hG2 (n : ℝ))

/-- [ The explicit inverse L² representative recovers every admissible extension
from its genuine angular Fourier profile. This completes the original-extension
identification in reflection-budget roadmap (3).](goal) Under [the stated conditions](hyp:hG1,hG2). -/
-- @node: reflectionInverseL2Representative_fourier_ae_original
lemma reflectionInverseL2Representative_fourier_ae_original {p : ℕ}
    {G : EuclideanSpace ℝ (Fin p) → ℂ}
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume) :
    let hF : MemLp (Fourier G) 2 volume :=
      Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
    reflectionInverseL2Representative (hF.toLp (Fourier G)) =ᵐ[volume] G := by
  dsimp only
  let hF : MemLp (Fourier G) 2 volume :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  have hm : Measurable (Fourier G) :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_measurable G hG1
  exact (reflectionSmoothApproximation_limit_ae_inverseL2Representative hm hF
    (hG2.toLp G) (reflectionSmoothApproximation_tendsto_original hG1 hG2)).symm.trans
      hG2.coeFn_toLp

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
