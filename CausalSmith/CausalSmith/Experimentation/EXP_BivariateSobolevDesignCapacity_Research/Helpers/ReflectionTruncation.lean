module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionEndpointZero
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Fourier ball truncations for endpoint completion

The frequency truncations in step (3) of the reflection-budget proof have compact
support and converge in the exact weighted Fourier energy. No endpoint estimate
or periodic boundary condition is assumed here.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology FourierTransform
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Cut a frequency profile off at the closed ball of radius R. -/
-- @node: reflectionFrequencyTruncation
def reflectionFrequencyTruncation {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ) :
    EuclideanSpace ℝ (Fin p) → ℂ :=
  (Metric.closedBall 0 R).indicator ψ

/-- The cutoff of a measurable frequency profile is measurable. This uses [the hψ hypothesis](hyp:hψ), [the stated conclusion](goal). -/
-- @node: reflectionFrequencyTruncation_measurable
@[fun_prop] lemma reflectionFrequencyTruncation_measurable {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : Measurable ψ) (R : ℝ) :
    Measurable (reflectionFrequencyTruncation ψ R) := by
  exact hψ.indicator Metric.isClosed_closedBall.measurableSet

/-- Cutting off a square-integrable profile preserves square integrability.](goal) Under [the stated conditions](hyp:hψ). This uses [the stated conclusion](goal). -/
-- @node: reflectionFrequencyTruncation_memLp
lemma reflectionFrequencyTruncation_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    MemLp (reflectionFrequencyTruncation ψ R) 2 volume := by
  exact hψ.indicator Metric.isClosed_closedBall.measurableSet

/-- Every frequency cutoff has compact support, including negative-radius cutoffs. [The asserted mathematical result follows](goal). -/
-- @node: reflectionFrequencyTruncation_hasCompactSupport
lemma reflectionFrequencyTruncation_hasCompactSupport {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ) :
    HasCompactSupport (reflectionFrequencyTruncation ψ R) := by
  apply (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R).of_isClosed_subset
    isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  exact support_indicator_subset

/-- A frequency cutoff of an L² profile is L¹ by finite volume of the ball. Under [the stated conditions](hyp:hψ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionFrequencyTruncation_integrable
lemma reflectionFrequencyTruncation_integrable {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    Integrable (reflectionFrequencyTruncation ψ R) volume := by
  have : IsFiniteMeasure (volume.restrict
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R)) :=
    ⟨by simpa using (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R).measure_lt_top⟩
  exact (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
    ((hψ.restrict _).integrable (by norm_num))

/-- [ Every continuous multiplier of an L² frequency cutoff is again L².
In particular this covers all polynomial moments used to differentiate the inverse integral.](goal) Under [the stated conditions](hyp:hψ,hP). -/
-- @node: reflectionFrequencyTruncation_multiplier_memLp
lemma reflectionFrequencyTruncation_multiplier_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (P : EuclideanSpace ℝ (Fin p) → ℂ) (hP : Continuous P) (R : ℝ) :
    MemLp (fun ω => P ω * reflectionFrequencyTruncation ψ R ω) 2 volume := by
  obtain ⟨B, hB⟩ := ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R).image
    hP).isBounded.exists_norm_le
  have hcut := reflectionFrequencyTruncation_memLp hψ R
  refine (hcut.const_smul (B : ℝ)).mono
    (hP.aestronglyMeasurable.mul hcut.aestronglyMeasurable) ?_
  apply Eventually.of_forall
  intro ω
  by_cases hω : ω ∈ Metric.closedBall 0 R
  · rw [norm_mul, Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right
      ((hB (P ω) ⟨ω, hω, rfl⟩).trans (le_abs_self B)) (norm_nonneg _)
  · simp [reflectionFrequencyTruncation, indicator_of_notMem hω]

/-- [ Continuous multipliers of frequency cutoffs are L¹ as well as L², since
their supports lie in the same finite-volume ball.](goal) Under [the stated conditions](hyp:hψ,hP). -/
-- @node: reflectionFrequencyTruncation_multiplier_integrable
lemma reflectionFrequencyTruncation_multiplier_integrable {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (P : EuclideanSpace ℝ (Fin p) → ℂ) (hP : Continuous P) (R : ℝ) :
    Integrable (fun ω => P ω * reflectionFrequencyTruncation ψ R ω) volume := by
  have hmul := reflectionFrequencyTruncation_multiplier_memLp hψ P hP R
  have : IsFiniteMeasure (volume.restrict
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin p)) R)) :=
    ⟨by simpa using (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin p)) R).measure_lt_top⟩
  have hi := (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
    ((hmul.restrict (Metric.closedBall 0 R)).integrable (by norm_num))
  have he : (Metric.closedBall 0 R).indicator
      (fun ω => P ω * reflectionFrequencyTruncation ψ R ω) =
      (fun ω => P ω * reflectionFrequencyTruncation ψ R ω) := by
    funext ω
    by_cases hω : ω ∈ Metric.closedBall 0 R
    · simp [hω]
    · simp [reflectionFrequencyTruncation, hω]
  rw [he] at hi
  exact hi

/-- [ Every norm moment of a truncated L² profile is integrable.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionFrequencyTruncation_norm_moment_integrable
lemma reflectionFrequencyTruncation_norm_moment_integrable {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume)
    (R : ℝ) (n : ℕ) :
    Integrable (fun ω => ‖ω‖ ^ n * ‖reflectionFrequencyTruncation ψ R ω‖) volume := by
  have hc : Continuous (fun ω : EuclideanSpace ℝ (Fin p) => (‖ω‖ ^ n : ℂ)) := by
    fun_prop
  have hi := (reflectionFrequencyTruncation_multiplier_integrable hψ _ hc R).norm
  simpa only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _)] using hi

/-- The smooth inverse angular Fourier integral of a ball-truncated profile.
Evaluating the forward angular transform at minus the spatial argument gives
exactly the positive exponential and the unitary prefactor in step (3). -/
-- @node: reflectionSmoothApproximation
def reflectionSmoothApproximation {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ) :
    EuclideanSpace ℝ (Fin p) → ℂ :=
  fun u => Fourier (reflectionFrequencyTruncation ψ R) (-u)

/-- The constructed smooth approximation is the normalized inverse angular integral
from step (3), with the positive exponential and no extra dilation constant. [The asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothApproximation_eq_integral
lemma reflectionSmoothApproximation_eq_integral {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (R : ℝ)
    (u : EuclideanSpace ℝ (Fin p)) :
    reflectionSmoothApproximation ψ R u =
      (2 * Real.pi) ^ (-(p : ℝ) / 2) •
        ∫ ω, Complex.exp (Complex.I * ((∑ h, ω h * u h : ℝ) : ℂ)) *
          reflectionFrequencyTruncation ψ R ω := by
  simp only [reflectionSmoothApproximation, Fourier, PiLp.neg_apply, neg_mul,
    Finset.sum_neg_distrib, Complex.ofReal_neg, mul_neg, neg_neg, mul_comm]

/-- The inverse integral from the roadmap is smooth to every order, because
all norm moments of its compactly supported L² frequency profile are L¹. Under [the stated conditions](hyp:hψ), [the asserted mathematical result follows](goal). -/
-- @node: reflectionSmoothApproximation_contDiff
lemma reflectionSmoothApproximation_contDiff {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (reflectionSmoothApproximation ψ R) := by
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) (𝓕 (reflectionFrequencyTruncation ψ R)) :=
    Real.contDiff_fourier (fun n _ =>
      reflectionFrequencyTruncation_norm_moment_integrable hψ R n)
  have he : reflectionSmoothApproximation ψ R = (fun u =>
      Causalean.Mathlib.Analysis.Fourier.angularPrefactor p •
        (𝓕 (reflectionFrequencyTruncation ψ R)) ((2 * Real.pi)⁻¹ • (-u))) := by
    funext u
    exact Causalean.Mathlib.Analysis.Fourier.angularFourier_eq_mathlib _ _
  rw [he]
  have hd : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun u : EuclideanSpace ℝ (Fin p) => (2 * Real.pi)⁻¹ • (-u)) := by
    fun_prop
  exact (hf.comp hd).const_smul _

/-- At each frequency the integer-radius truncations eventually equal the profile. [The asserted mathematical result follows](goal). -/
-- @node: reflectionFrequencyTruncation_eventually_eq
lemma reflectionFrequencyTruncation_eventually_eq {p : ℕ}
    (ψ : EuclideanSpace ℝ (Fin p) → ℂ) (ω : EuclideanSpace ℝ (Fin p)) :
    ∀ᶠ n : ℕ in atTop, reflectionFrequencyTruncation ψ (n : ℝ) ω = ψ ω := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖ω‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply indicator_of_mem
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    hN.trans (Nat.cast_le.mpr hn)

/-- The exact weighted squared error of the frequency truncations tends to zero.
This is the dominated-convergence assertion in step (3), with the paper's local
normalization by p and with no loss in the weight. Under [the stated conditions](hyp:hψ,hfinite), [the asserted mathematical result follows](goal). -/
-- @node: reflectionFrequencyTruncation_weighted_error_tendsto
lemma reflectionFrequencyTruncation_weighted_error_tendsto {p : ℕ} (s : ℝ)
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : Measurable ψ)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) ≠ ⊤) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) atTop (𝓝 0) := by
  have hmeas (n : ℕ) : Measurable (fun ω => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) := by
    fun_prop
  have hbound (n : ℕ) : (fun ω => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) ≤ᵐ[volume]
      (fun ω => ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) := by
    apply Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ Metric.closedBall 0 (n : ℝ)
    · simp only [reflectionFrequencyTruncation, indicator_of_mem hω, sub_self,
        norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, ENNReal.ofReal_zero]
      exact bot_le
    · simp only [reflectionFrequencyTruncation, indicator_of_notMem hω, zero_sub,
        norm_neg]
      exact le_rfl
  have hlim : ∀ᵐ ω ∂volume, Tendsto (fun n : ℕ => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (n : ℝ) ω - ψ ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro ω
    apply tendsto_const_nhds.congr'
    filter_upwards [reflectionFrequencyTruncation_eventually_eq ψ ω] with n hn
    simp [hn]
  simpa using tendsto_lintegral_of_dominated_convergence
    (fun ω => ENNReal.ofReal (‖ψ ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s))
    hmeas hbound hfinite hlim

/-- [ The genuine Fourier ball truncations of an admissible whole-space extension
satisfy the smoothness, integrable-moment and weighted frequency-convergence
parts of step (3). Identifying the inverse integrals in L² remains a separate step.](goal) Under [the stated conditions](hyp:hG1,hG2,hfinite). -/
-- @node: reflectionFourierTruncation_approximation
lemma reflectionFourierTruncation_approximation {p : ℕ} (s : ℝ)
    (G : EuclideanSpace ℝ (Fin p) → ℂ)
    (hG1 : Integrable G volume) (hG2 : MemLp G 2 volume)
    (hfinite : (∫⁻ ω, ENNReal.ofReal
      (‖Fourier G ω‖ ^ 2 * (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) ≠ ⊤) :
    (∀ R : ℝ, ContDiff ℝ (↑(⊤ : ℕ∞)) (reflectionSmoothApproximation (Fourier G) R)) ∧
    (∀ (R : ℝ) (n : ℕ), Integrable
      (fun ω => ‖ω‖ ^ n * ‖reflectionFrequencyTruncation (Fourier G) R ω‖) volume) ∧
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal
      (‖reflectionFrequencyTruncation (Fourier G) (n : ℝ) ω - Fourier G ω‖ ^ 2 *
        (1 + ‖ω‖ ^ 2 / (p : ℝ)) ^ s)) atTop (𝓝 0) := by
  have hLp : MemLp (Fourier G) 2 volume :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp G hG1 hG2
  have hm : Measurable (Fourier G) :=
    Causalean.Mathlib.Analysis.Fourier.angularFourier_measurable G hG1
  exact ⟨fun R => reflectionSmoothApproximation_contDiff hLp R,
    fun R n => reflectionFrequencyTruncation_norm_moment_integrable hLp R n,
    reflectionFrequencyTruncation_weighted_error_tendsto s hm hfinite⟩

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
