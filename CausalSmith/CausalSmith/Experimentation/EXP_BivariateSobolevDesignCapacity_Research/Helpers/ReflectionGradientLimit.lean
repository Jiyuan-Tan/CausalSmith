module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionEndpointLimit
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionSmoothDerivative

/-! # First-order convergence of the genuine inverse truncations

Finite first-order Fourier energy supplies square-integrable coordinate multipliers.
Their inverse L² representatives are the limits of the actual smooth derivatives
in roadmap (3), without imposing L¹ regularity on these full multipliers.
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
open Causalean.Mathlib.Analysis.Fourier
set_option backward.isDefEq.respectTransparency false

/-- [ Finite first-order energy implies L² membership of each full coordinate
multiplier; this regularity is derived rather than assumed.](goal) Under [the stated conditions](hyp:hp,hm,hfinite). -/
-- @node: reflectionCoordinateProfile_memLp
lemma reflectionCoordinateProfile_memLp {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) (r : Fin p) :
    MemLp (fun ω => Complex.I * (ω r : ℂ) * ψ ω) 2 volume := by
  have hweight : Integrable (fun ω => ‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ))) volume := by
    refine ⟨by fun_prop, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun ω => by positivity)).2 (lt_top_iff_ne_top.mpr hfinite)
  have hmul : Measurable (fun ω => Complex.I * (ω r : ℂ) * ψ ω) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm hmul.aestronglyMeasurable).2
  apply (hweight.const_mul (p : ℝ)).mono' (by fun_prop)
  filter_upwards [] with ω
  have hc : (ω r) ^ 2 ≤ ‖ω‖ ^ 2 := by
    rw [norm_sq_eq_sum_coordinates]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (ω j)) (Finset.mem_univ r)
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have hw : (ω r) ^ 2 ≤ (p : ℝ) * (1 + ‖ω‖ ^ 2 / (p : ℝ)) := by
    rw [mul_add, mul_one, mul_div_cancel₀ _ hp'.ne']
    linarith
  simp only [norm_pow, norm_mul, Complex.norm_I, one_mul,
    Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hw (sq_nonneg ‖ψ ω‖)]

/-- Truncation commutes with the coordinate multiplier, so the actual smooth
spatial derivative is precisely its inverse Fourier approximation. [The asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothDerivative_eq_multiplier_approximation
lemma reflectionSmoothDerivative_eq_multiplier_approximation {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ) (r : Fin p) :
    reflectionSmoothDerivative ψ R r =
      reflectionSmoothApproximation (fun ω => Complex.I * (ω r : ℂ) * ψ ω) R := by
  have he : (fun ω => Complex.I * (ω r : ℂ) * reflectionFrequencyTruncation ψ R ω) =
      reflectionFrequencyTruncation (fun ω => Complex.I * (ω r : ℂ) * ψ ω) R := by
    funext ω
    by_cases hω : ω ∈ Metric.closedBall 0 R <;>
      simp [reflectionFrequencyTruncation, hω]
  funext u
  simp only [reflectionSmoothDerivative, reflectionSmoothApproximation, he]

/-- Every actual smooth coordinate derivative converges to the inverse L²
class of its full frequency multiplier. The multiplier's L² regularity follows
from the original finite first-order energy. Under [the stated conditions](hyp:hp,hm,hψ,hfinite), [the asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothDerivative_tendsto_inverseL2
lemma reflectionSmoothDerivative_tendsto_inverseL2 {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hψ : MemLp ψ 2 volume)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) (r : Fin p) :
    let D := fun ω => Complex.I * (ω r : ℂ) * ψ ω
    let hD := reflectionCoordinateProfile_memLp hp hm hfinite r
    Tendsto (fun n : ℕ => (reflectionSmoothDerivative_memLp hψ (n : ℝ) r).toLp
      (reflectionSmoothDerivative ψ (n : ℝ) r)) atTop
      (𝓝 ((reflectionInverseL2Representative_memLp (hD.toLp D)).toLp
        (reflectionInverseL2Representative (hD.toLp D)))) := by
  dsimp only
  have hD := reflectionCoordinateProfile_memLp hp hm hfinite r
  have hDm : Measurable (fun ω => Complex.I * (ω r : ℂ) * ψ ω) := by fun_prop
  have ht := reflectionSmoothApproximation_tendsto_inverseL2Representative hDm hD
  convert ht using 1
  funext n
  apply Lp.ext
  filter_upwards [(reflectionSmoothDerivative_memLp hψ (n : ℝ) r).coeFn_toLp,
    (reflectionSmoothApproximation_memLp hD (n : ℝ)).coeFn_toLp] with u hu hv
  rw [hu, hv, reflectionSmoothDerivative_eq_multiplier_approximation]

/-- [ The limiting coordinate derivative has exactly its full coordinate-weighted
frequency energy, even when that multiplier is not L¹.](goal) Under [the stated conditions](hyp:hp,hm,hfinite). -/
-- @node: reflectionInverseCoordinate_energy
lemma reflectionInverseCoordinate_energy {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) (r : Fin p) :
    let D := fun ω => Complex.I * (ω r : ℂ) * ψ ω
    let hD := reflectionCoordinateProfile_memLp hp hm hfinite r
    (∫⁻ u, ENNReal.ofReal (‖reflectionInverseL2Representative (hD.toLp D) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal ((ω r) ^ 2 * ‖ψ ω‖ ^ 2) := by
  dsimp only
  rw [reflectionInverseL2Representative_energy]
  apply lintegral_congr_ae
  filter_upwards [(reflectionCoordinateProfile_memLp hp hm hfinite r).coeFn_toLp] with ω hω
  rw [hω]
  simp [mul_pow, sq_abs]

/-- [ The limiting inverse function and all limiting coordinate derivatives have
the exact first-order energy from roadmap (3), with local gradient factor 1/p.](goal) Under [the stated conditions](hyp:hp,hm,hψ,hfinite). -/
-- @node: reflectionInverse_firstOrder_energy
lemma reflectionInverse_firstOrder_energy {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hψ : MemLp ψ 2 volume)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) +
      ENNReal.ofReal ((p : ℝ)⁻¹) *
        (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal
          (‖reflectionInverseL2Representative
            ((reflectionCoordinateProfile_memLp hp hm hfinite r).toLp
              (fun ω => Complex.I * (ω r : ℂ) * ψ ω)) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ))) := by
  have he : (∫⁻ u, ENNReal.ofReal
      (‖reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2) := by
    rw [reflectionInverseL2Representative_energy]
    apply lintegral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with ω hω
    rw [hω]
  rw [he]
  simp_rw [reflectionInverseCoordinate_energy hp hm hfinite]
  rw [← lintegral_finsetSum']
  · have hsum : (fun ω : EuclideanSpace ℝ (Fin p) =>
        ∑ r : Fin p, ENNReal.ofReal ((ω r) ^ 2 * ‖ψ ω‖ ^ 2)) =
        (fun ω => ENNReal.ofReal (‖ω‖ ^ 2 * ‖ψ ω‖ ^ 2)) := by
      funext ω
      rw [norm_sq_eq_sum_coordinates, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro r hr
      positivity
    rw [hsum, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmE : AEMeasurable (fun ω => ENNReal.ofReal (‖ψ ω‖ ^ 2)) volume := by fun_prop
    rw [← lintegral_add_left' hmE]
    apply lintegral_congr
    intro ω
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  · intro r hr
    fun_prop

/-- [ Spatial inverse truncations and their actual coordinate derivatives converge
together to the explicit inverse Fourier classes. All derivative regularity is
derived from the one finite first-order energy assumption.](goal) Under [the stated conditions](hyp:hp,hm,hψ,hfinite). -/
-- @node: reflectionSmoothApproximation_firstOrder_tendsto
lemma reflectionSmoothApproximation_firstOrder_tendsto {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hψ : MemLp ψ 2 volume)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) :
    Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) atTop
      (𝓝 ((reflectionInverseL2Representative_memLp (hψ.toLp ψ)).toLp
        (reflectionInverseL2Representative (hψ.toLp ψ)))) ∧
    (∀ r : Fin p, Tendsto
      (fun n : ℕ => (reflectionSmoothDerivative_memLp hψ (n : ℝ) r).toLp
        (reflectionSmoothDerivative ψ (n : ℝ) r)) atTop
      (𝓝 ((reflectionInverseL2Representative_memLp
        ((reflectionCoordinateProfile_memLp hp hm hfinite r).toLp
          (fun ω => Complex.I * (ω r : ℂ) * ψ ω))).toLp
        (reflectionInverseL2Representative
          ((reflectionCoordinateProfile_memLp hp hm hfinite r).toLp
            (fun ω => Complex.I * (ω r : ℂ) * ψ ω)))))) := by
  exact ⟨reflectionSmoothApproximation_tendsto_inverseL2Representative hm hψ,
    fun r => reflectionSmoothDerivative_tendsto_inverseL2 hp hm hψ hfinite r⟩

/-- [ The derivative error relative to its full inverse class has the exact
coordinate-weighted truncation error, with no spatial normalization loss.](goal) Under [the stated conditions](hyp:hp,hm,hfinite). -/
-- @node: reflectionSmoothDerivative_inverseL2_error_energy
lemma reflectionSmoothDerivative_inverseL2_error_energy {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) (R : ℝ) (r : Fin p) :
    let D := fun ω => Complex.I * (ω r : ℂ) * ψ ω
    let hD := reflectionCoordinateProfile_memLp hp hm hfinite r
    (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothDerivative ψ R r u -
      reflectionInverseL2Representative (hD.toLp D) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal ((ω r) ^ 2 *
        ‖reflectionFrequencyTruncation ψ R ω - ψ ω‖ ^ 2) := by
  dsimp only
  simp_rw [reflectionSmoothDerivative_eq_multiplier_approximation]
  rw [reflectionSmoothApproximation_inverseL2_error_energy]
  apply lintegral_congr
  intro ω
  by_cases hω : ω ∈ Metric.closedBall 0 R
  · simp [reflectionFrequencyTruncation, hω]
  · simp [reflectionFrequencyTruncation, hω, mul_pow, sq_abs]

/-- [ Roadmap (3)'s entire first-order squared error tends to zero. This is
convergence in the genuine spatial endpoint norm, not only coefficientwise
convergence, and keeps the exact local gradient factor 1/p.](goal) Under [the stated conditions](hyp:hp,hm,hψ,hfinite). -/
-- @node: reflectionSmoothApproximation_firstOrder_error_tendsto
lemma reflectionSmoothApproximation_firstOrder_error_tendsto {p : ℕ} (hp : 0 < p)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hm : Measurable ψ)
    (hψ : MemLp ψ 2 volume)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)))) ≠ ⊤) :
    Tendsto (fun n : ℕ =>
      (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothApproximation ψ (n : ℝ) u -
        reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) +
      ENNReal.ofReal ((p : ℝ)⁻¹) *
        (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal
          (‖reflectionSmoothDerivative ψ (n : ℝ) r u - reflectionInverseL2Representative
            ((reflectionCoordinateProfile_memLp hp hm hfinite r).toLp
              (fun ω => Complex.I * (ω r : ℂ) * ψ ω)) u‖ ^ 2))) atTop (𝓝 0) := by
  have he (n : ℕ) :
      (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothApproximation ψ (n : ℝ) u -
        reflectionInverseL2Representative (hψ.toLp ψ) u‖ ^ 2)) +
      ENNReal.ofReal ((p : ℝ)⁻¹) *
        (∑ r : Fin p, ∫⁻ u, ENNReal.ofReal
          (‖reflectionSmoothDerivative ψ (n : ℝ) r u - reflectionInverseL2Representative
            ((reflectionCoordinateProfile_memLp hp hm hfinite r).toLp
              (fun ω => Complex.I * (ω r : ℂ) * ψ ω)) u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ))) := by
    rw [reflectionSmoothApproximation_inverseL2_error_energy hψ]
    simp_rw [reflectionSmoothDerivative_inverseL2_error_energy hp hm hfinite]
    rw [← lintegral_finsetSum']
    · have hsum : (fun ω : EuclideanSpace ℝ (Fin p) =>
          ∑ r : Fin p, ENNReal.ofReal ((ω r) ^ 2 *
            ‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2)) =
          (fun ω => ENNReal.ofReal (‖ω‖ ^ 2 *
            ‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2)) := by
        funext ω
        rw [norm_sq_eq_sum_coordinates, Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
        intro r hr
        positivity
      rw [hsum, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmE : AEMeasurable (fun ω => ENNReal.ofReal
          (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2)) volume := by fun_prop
      rw [← lintegral_add_left' hmE]
      apply lintegral_congr
      intro ω
      rw [← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      simp only [div_eq_mul_inv]
      ring
    · intro r hr
      fun_prop
  simp_rw [he]
  simpa only [Real.rpow_one] using
    reflectionFrequencyTruncation_weighted_error_tendsto 1 hm (by
      simpa only [Real.rpow_one] using hfinite)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
