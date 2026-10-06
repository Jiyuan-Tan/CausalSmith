module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionInverseL2

/-! # Coordinate derivatives of the smooth inverse truncations

Differentiation under the inverse integral in roadmap (3) produces the genuine
coordinate multiplier. Plancherel then identifies its spatial energy exactly.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.Fourier
set_option backward.isDefEq.respectTransparency false

/-- [ The spatial coordinate derivative constructed by the inverse angular integral. -/
-- @node: reflectionSmoothDerivative
def reflectionSmoothDerivative {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ) (r : Fin p)
    (u : EuclideanSpace ℝ (Fin p)) : ℂ :=
  Fourier (fun ω => Complex.I * (ω r : ℂ) * reflectionFrequencyTruncation ψ R ω) (-u)

/-- The derivative's frequency profile is both L¹ and L².](goal) Under [the stated conditions](hyp:hψ). This uses [the stated conclusion](goal). -/
-- @node: reflectionSmoothDerivative_profile_integrable
lemma reflectionSmoothDerivative_profile_integrable {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) :
    Integrable (fun ω => Complex.I * (ω r : ℂ) *
      reflectionFrequencyTruncation ψ R ω) volume := by
  apply reflectionFrequencyTruncation_multiplier_integrable hψ
  fun_prop

/-- [ Polynomial multiplication on a compact frequency ball preserves L².](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothDerivative_profile_memLp
lemma reflectionSmoothDerivative_profile_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) :
    MemLp (fun ω => Complex.I * (ω r : ℂ) *
      reflectionFrequencyTruncation ψ R ω) 2 volume := by
  apply reflectionFrequencyTruncation_multiplier_memLp hψ
  fun_prop

/-- [ The actual inverse derivative is spatially square integrable.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothDerivative_memLp
lemma reflectionSmoothDerivative_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) :
    MemLp (reflectionSmoothDerivative ψ R r) 2 volume :=
  reflectionInverseIntegral_memLp
    (reflectionSmoothDerivative_profile_integrable hψ R r)
    (reflectionSmoothDerivative_profile_memLp hψ R r)

/-- [ Plancherel gives the exact coordinate-weighted energy, without an extra constant.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothDerivative_energy
lemma reflectionSmoothDerivative_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothDerivative ψ R r u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal ((ω r) ^ 2 * ‖reflectionFrequencyTruncation ψ R ω‖ ^ 2) := by
  simp only [reflectionSmoothDerivative]
  rw [reflectionInverseIntegral_energy
    (reflectionSmoothDerivative_profile_integrable hψ R r)
    (reflectionSmoothDerivative_profile_memLp hψ R r)]
  apply lintegral_congr
  intro ω
  simp [mul_pow, sq_abs]

/-- The positive angular phase has the expected derivative on each coordinate slice. [The asserted mathematical result follows](goal). -/
-- @node: reflectionInversePhase_hasDerivAt
lemma reflectionInversePhase_hasDerivAt {p : ℕ}
    (ω x : EuclideanSpace ℝ (Fin p)) (r : Fin p) (t : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (Complex.I *
      ((∑ j, ω j * updateCoordinate x r v j : ℝ) : ℂ)))
      (Complex.I * (ω r : ℂ) * Complex.exp (Complex.I *
        ((∑ j, ω j * updateCoordinate x r t j : ℝ) : ℂ))) t := by
  have hc : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun u : EuclideanSpace ℝ (Fin p) =>
      Complex.exp (-Complex.I * ((∑ j, (-ω) j * u j : ℝ) : ℂ))) := by
    have hs : ContDiff ℝ (↑(⊤ : ℕ∞))
        (fun u : EuclideanSpace ℝ (Fin p) => ∑ j, (-ω) j * u j) := by
      fun_prop
    exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hs)).cexp
  have h := hasDerivAt_test_coordinate_slice _ hc x r t
  rw [coordinateDerivative_angular_phase] at h
  simpa only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg, neg_neg] using h

/-- Positive angular kernels preserve integrability of any L¹ profile. Under [the stated conditions](hyp:hχ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionInversePhase_integrable
lemma reflectionInversePhase_integrable {p : ℕ}
    {χ : EuclideanSpace ℝ (Fin p) → ℂ} (hχ : Integrable χ volume)
    (u : EuclideanSpace ℝ (Fin p)) :
    Integrable (fun ω => Complex.exp (Complex.I *
      ((∑ j, ω j * u j : ℝ) : ℂ)) * χ ω) volume := by
  simpa only [PiLp.neg_apply, neg_mul, Finset.sum_neg_distrib,
    Complex.ofReal_neg, mul_neg, neg_neg, mul_comm] using
    integrable_angular_kernel χ hχ (-u)

/-- [ Differentiation under the inverse integral identifies the constructed derivative
on every coordinate line. Compact spectral support supplies its integrable dominator.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_hasDerivAt_slice
lemma reflectionSmoothApproximation_hasDerivAt_slice {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (x : EuclideanSpace ℝ (Fin p)) (r : Fin p) (t : ℝ) :
    HasDerivAt (fun v : ℝ => reflectionSmoothApproximation ψ R (updateCoordinate x r v))
      (reflectionSmoothDerivative ψ R r (updateCoordinate x r t)) t := by
  let χ := reflectionFrequencyTruncation ψ R
  let D := fun ω => Complex.I * (ω r : ℂ) * χ ω
  let F := fun v ω => Complex.exp (Complex.I *
    ((∑ j, ω j * updateCoordinate x r v j : ℝ) : ℂ)) * χ ω
  let F' := fun v ω => Complex.exp (Complex.I *
    ((∑ j, ω j * updateCoordinate x r v j : ℝ) : ℂ)) * D ω
  have hχ : Integrable χ volume := reflectionFrequencyTruncation_integrable hψ R
  have hD : Integrable D volume := reflectionSmoothDerivative_profile_integrable hψ R r
  have hF (v : ℝ) : Integrable (F v) volume :=
    reflectionInversePhase_integrable hχ (updateCoordinate x r v)
  have hF' (v : ℝ) : Integrable (F' v) volume :=
    reflectionInversePhase_integrable hD (updateCoordinate x r v)
  have hb : ∀ᵐ ω ∂volume, ∀ v ∈ (Set.univ : Set ℝ), ‖F' v ω‖ ≤ ‖D ω‖ := by
    filter_upwards [] with ω v hv
    simp [F', Complex.norm_exp]
  have hd : ∀ᵐ ω ∂volume, ∀ v ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun z => F z ω) (F' v ω) v := by
    filter_upwards [] with ω v hv
    convert! (reflectionInversePhase_hasDerivAt ω x r v).mul_const (χ ω) using 1
    dsimp [F', D]
    ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (bound := fun ω => ‖D ω‖) (Filter.univ_mem)
    (Eventually.of_forall fun v => (hF v).aestronglyMeasurable)
    (hF t) (hF' t).aestronglyMeasurable hb hD.norm hd).2
  have he : reflectionSmoothDerivative ψ R r (updateCoordinate x r t) =
      (2 * Real.pi) ^ (-(p : ℝ) / 2) • ∫ ω, F' t ω := by
    simp only [reflectionSmoothDerivative, Fourier, PiLp.neg_apply, neg_mul,
      Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg, neg_neg]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with ω
    dsimp [F', D, χ]
    congr 4
    exact Finset.sum_congr rfl (fun j hj => mul_comm _ _)
  rw [he]
  convert! h.const_smul ((2 * Real.pi) ^ (-(p : ℝ) / 2)) using 1
  funext v
  exact reflectionSmoothApproximation_eq_integral ψ R (updateCoordinate x r v)

/-- [ The constructed slice derivative is the genuine Fréchet coordinate derivative.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_coordinateDerivative
lemma reflectionSmoothApproximation_coordinateDerivative {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) (x : EuclideanSpace ℝ (Fin p)) :
    coordinateDerivative (reflectionSmoothApproximation ψ R) r x =
      reflectionSmoothDerivative ψ R r x := by
  have he : updateCoordinate x r (x r) = x := by
    ext j
    simp [updateCoordinate]
  have h₁ := hasDerivAt_test_coordinate_slice _
    (reflectionSmoothApproximation_contDiff hψ R) x r (x r)
  have h₂ := reflectionSmoothApproximation_hasDerivAt_slice hψ R x r (x r)
  rw [he] at h₁ h₂
  exact h₁.unique h₂

/-- [ Each constructed coordinate derivative is continuous, even though the spectral
cutoff itself has a discontinuity at the ball boundary. This uses [the hψ hypothesis](hyp:hψ), [the stated conclusion](goal). -/
-- @node: reflectionSmoothDerivative_continuous
@[fun_prop] lemma reflectionSmoothDerivative_continuous {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (r : Fin p) : Continuous (reflectionSmoothDerivative ψ R r) := by
  exact (angularFourier_continuous _
    (reflectionSmoothDerivative_profile_integrable hψ R r)).comp continuous_neg

/-- All spatial coordinate derivative energies together equal the exact radial
frequency moment; no dimension factor enters Plancherel.](goal) Under [the stated conditions](hyp:hψ). This uses [the stated conclusion](goal). -/
-- @node: reflectionSmoothApproximation_gradient_energy
lemma reflectionSmoothApproximation_gradient_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal (‖reflectionSmoothDerivative ψ R r u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ω‖ ^ 2 * ‖reflectionFrequencyTruncation ψ R ω‖ ^ 2) := by
  simp_rw [reflectionSmoothDerivative_energy hψ]
  rw [← lintegral_finsetSum']
  · apply lintegral_congr
    intro ω
    rw [norm_sq_eq_sum_coordinates, Finset.sum_mul,
      ENNReal.ofReal_sum_of_nonneg]
    intro r hr
    positivity
  · intro r hr
    have hm := (reflectionFrequencyTruncation_memLp hψ R).aestronglyMeasurable
    exact (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      ((by fun_prop : Continuous
        (fun ω : EuclideanSpace ℝ (Fin p) => (ω r) ^ 2)).aestronglyMeasurable.mul
        (hm.norm.pow 2))).aemeasurable

/-- [ Roadmap (3)'s exact first-order energy identity for the smooth inverse
truncations, expressed using their actual coordinate derivatives.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_firstOrder_energy
lemma reflectionSmoothApproximation_firstOrder_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothApproximation ψ R u‖ ^ 2)) +
      ENNReal.ofReal ((p : ℝ)⁻¹) *
        (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal
          (‖coordinateDerivative (reflectionSmoothApproximation ψ R) r u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal
        (‖reflectionFrequencyTruncation ψ R ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ))) := by
  simp_rw [reflectionSmoothApproximation_coordinateDerivative hψ]
  rw [reflectionSmoothApproximation_energy hψ,
    reflectionSmoothApproximation_gradient_energy hψ,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : AEMeasurable (fun ω => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ R ω‖ ^ 2)) volume :=
    (ENNReal.continuous_ofReal.comp_aestronglyMeasurable
      ((reflectionFrequencyTruncation_memLp hψ R).aestronglyMeasurable.norm.pow 2)).aemeasurable
  rw [← lintegral_add_left' hm]
  apply lintegral_congr
  intro ω
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  simp only [div_eq_mul_inv]
  ring

/-- [ Restricting the spectral profile to a ball cannot increase the exact H¹
energy. Combined with the identity above this is the spatial approximation bound.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_firstOrder_le_profile
lemma reflectionSmoothApproximation_firstOrder_le_profile {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothApproximation ψ R u‖ ^ 2)) +
      ENNReal.ofReal ((p : ℝ)⁻¹) *
        (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal
          (‖coordinateDerivative (reflectionSmoothApproximation ψ R) r u‖ ^ 2)) ≤
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ))) := by
  rw [reflectionSmoothApproximation_firstOrder_energy hψ]
  apply lintegral_mono
  intro ω
  by_cases hω : ω ∈ Metric.closedBall 0 R
  · simp [reflectionFrequencyTruncation, hω]
  · simp [reflectionFrequencyTruncation, hω]

/-- [ The exact coordinate-energy identity also holds for differences of two
smooth truncations, as required in endpoint completion.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothDerivative_difference_energy
lemma reflectionSmoothDerivative_difference_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R S : ℝ) (r : Fin p) :
    (∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothDerivative ψ R r u - reflectionSmoothDerivative ψ S r u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal ((ω r) ^ 2 *
        ‖reflectionFrequencyTruncation ψ R ω - reflectionFrequencyTruncation ψ S ω‖ ^ 2) := by
  simp only [reflectionSmoothDerivative]
  rw [reflectionInverseIntegral_difference_energy
    (reflectionSmoothDerivative_profile_integrable hψ R r)
    (reflectionSmoothDerivative_profile_memLp hψ R r)
    (reflectionSmoothDerivative_profile_integrable hψ S r)
    (reflectionSmoothDerivative_profile_memLp hψ S r)]
  apply lintegral_congr
  intro ω
  rw [← mul_sub]
  simp [mul_pow, sq_abs]

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
