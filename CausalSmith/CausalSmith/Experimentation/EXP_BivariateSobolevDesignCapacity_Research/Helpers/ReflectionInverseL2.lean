module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.ReflectionTruncation

/-! # Spatial L² control of the smooth inverse truncations

Angular Plancherel and the measure-preserving spatial reflection identify the
exact spatial energies and differences of the inverse integrals in roadmap step (3).
-/

public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity

/-- [ Angular Fourier transformation commutes with subtraction of L¹ profiles.](goal) Under [the stated conditions](hyp:hψ,hχ). -/
-- @node: reflectionFourier_sub
lemma reflectionFourier_sub {p : ℕ} {ψ χ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ : Integrable ψ volume) (hχ : Integrable χ volume) :
    Fourier (ψ - χ) = Fourier ψ - Fourier χ := by
  funext u
  unfold Fourier
  simp only [Pi.sub_apply, mul_sub]
  rw [integral_sub
    (Causalean.Mathlib.Analysis.Fourier.integrable_angular_kernel ψ hψ u)
    (Causalean.Mathlib.Analysis.Fourier.integrable_angular_kernel χ hχ u), smul_sub]

/-- [ The inverse angular integral of an L¹∩L² profile is square integrable.](goal) Under [the stated conditions](hyp:hψ1,hψ2). -/
-- @node: reflectionInverseIntegral_memLp
lemma reflectionInverseIntegral_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) :
    MemLp (fun u => Fourier ψ (-u)) 2 volume := by
  exact (Causalean.Mathlib.Analysis.Fourier.angularFourier_memLp ψ hψ1 hψ2).comp_measurePreserving
     (Measure.measurePreserving_neg volume)

/-- [ Spatial negation and angular Plancherel preserve the exact inverse-integral energy.](goal) Under [the stated conditions](hyp:hψ1,hψ2). -/
-- @node: reflectionInverseIntegral_energy
lemma reflectionInverseIntegral_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume) :
    (∫⁻ u, ENNReal.ofReal (‖Fourier ψ (-u)‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω‖ ^ 2) := by
  calc
    _ = ∫⁻ u, ENNReal.ofReal (‖Fourier ψ u‖ ^ 2) :=
      (Measure.measurePreserving_neg volume).lintegral_comp (by
        have hc := Causalean.Mathlib.Analysis.Fourier.angularFourier_continuous ψ hψ1
        change Measurable (fun u => ENNReal.ofReal
          (‖Causalean.Mathlib.Analysis.Fourier.angularFourier ψ u‖ ^ 2))
        fun_prop)
    _ = _ := Causalean.Mathlib.Analysis.Fourier.angular_plancherel_integral ψ hψ1 hψ2

/-- [ The inverse-integral squared distance equals the frequency squared distance,
including profiles whose inverse integrals need not be L¹.](goal) Under [the stated conditions](hyp:hψ1,hψ2,hχ1,hχ2). -/
-- @node: reflectionInverseIntegral_difference_energy
lemma reflectionInverseIntegral_difference_energy {p : ℕ}
    {ψ χ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hψ1 : Integrable ψ volume) (hψ2 : MemLp ψ 2 volume)
    (hχ1 : Integrable χ volume) (hχ2 : MemLp χ 2 volume) :
    (∫⁻ u, ENNReal.ofReal (‖Fourier ψ (-u) - Fourier χ (-u)‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖ψ ω - χ ω‖ ^ 2) := by
  simpa only [reflectionFourier_sub hψ1 hχ1, Pi.sub_apply] using
    reflectionInverseIntegral_energy (hψ1.sub hχ1) (hψ2.sub hχ2)

/-- [ Every smooth ball-truncated inverse integral is genuinely in spatial L².](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_memLp
lemma reflectionSmoothApproximation_memLp {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    MemLp (reflectionSmoothApproximation ψ R) 2 volume :=
  reflectionInverseIntegral_memLp (reflectionFrequencyTruncation_integrable hψ R)
    (reflectionFrequencyTruncation_memLp hψ R)

/-- [ The smooth inverse approximations have exactly the truncated frequency energy.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_energy
lemma reflectionSmoothApproximation_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R : ℝ) :
    (∫⁻ u, ENNReal.ofReal (‖reflectionSmoothApproximation ψ R u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal (‖reflectionFrequencyTruncation ψ R ω‖ ^ 2) :=
  reflectionInverseIntegral_energy (reflectionFrequencyTruncation_integrable hψ R)
    (reflectionFrequencyTruncation_memLp hψ R)

/-- [ Differences of smooth inverse truncations preserve squared L² distance with constant one.](goal) Under [the stated conditions](hyp:hψ). -/
-- @node: reflectionSmoothApproximation_difference_energy
lemma reflectionSmoothApproximation_difference_energy {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ} (hψ : MemLp ψ 2 volume) (R S : ℝ) :
    (∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ R u - reflectionSmoothApproximation ψ S u‖ ^ 2)) =
      ∫⁻ ω, ENNReal.ofReal
        (‖reflectionFrequencyTruncation ψ R ω - reflectionFrequencyTruncation ψ S ω‖ ^ 2) :=
  reflectionInverseIntegral_difference_energy
    (reflectionFrequencyTruncation_integrable hψ R) (reflectionFrequencyTruncation_memLp hψ R)
    (reflectionFrequencyTruncation_integrable hψ S) (reflectionFrequencyTruncation_memLp hψ S)

/-- [ The frequency truncations are Cauchy in squared L² energy, jointly in both radii.
The domination has constant one because two nested indicators differ only by a sign.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionFrequencyTruncation_difference_tendsto
lemma reflectionFrequencyTruncation_difference_tendsto {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    Tendsto (fun q : ℕ × ℕ => ∫⁻ ω, ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (q.1 : ℝ) ω -
        reflectionFrequencyTruncation ψ (q.2 : ℝ) ω‖ ^ 2)) atTop (𝓝 0) := by
  have hmeas (q : ℕ × ℕ) : Measurable (fun ω => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (q.1 : ℝ) ω -
        reflectionFrequencyTruncation ψ (q.2 : ℝ) ω‖ ^ 2)) := by
    fun_prop
  have hbound (q : ℕ × ℕ) : (fun ω => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (q.1 : ℝ) ω -
        reflectionFrequencyTruncation ψ (q.2 : ℝ) ω‖ ^ 2)) ≤ᵐ[volume]
      (fun ω => ENNReal.ofReal (‖ψ ω‖ ^ 2)) := by
    apply Eventually.of_forall
    intro ω
    by_cases h₁ : ω ∈ Metric.closedBall 0 (q.1 : ℝ) <;>
      by_cases h₂ : ω ∈ Metric.closedBall 0 (q.2 : ℝ) <;>
      simp [reflectionFrequencyTruncation, h₁, h₂]
  have hlim : ∀ᵐ ω ∂volume, Tendsto (fun q : ℕ × ℕ => ENNReal.ofReal
      (‖reflectionFrequencyTruncation ψ (q.1 : ℝ) ω -
        reflectionFrequencyTruncation ψ (q.2 : ℝ) ω‖ ^ 2)) atTop (𝓝 (0 : ℝ≥0∞)) := by
    apply Eventually.of_forall
    intro ω
    obtain ⟨N, hN⟩ := exists_nat_ge ‖ω‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (N, N)] with q hq
    have h₁ : ω ∈ Metric.closedBall 0 (q.1 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        hN.trans (Nat.cast_le.mpr hq.1)
    have h₂ : ω ∈ Metric.closedBall 0 (q.2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        hN.trans (Nat.cast_le.mpr hq.2)
    simp [reflectionFrequencyTruncation, h₁, h₂]
  simpa using tendsto_lintegral_filter_of_dominated_convergence
    (fun ω => ENNReal.ofReal (‖ψ ω‖ ^ 2))
    (Eventually.of_forall hmeas) (Eventually.of_forall hbound)
    (Causalean.Mathlib.Analysis.Fourier.l2Energy_lt_top_of_memLp ψ hψ).ne hlim

/-- [ The smooth inverse integrals are Cauchy in spatial squared L² energy.
This uses the exact Plancherel distance identity rather than assuming inverse L¹ regularity.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionSmoothApproximation_difference_tendsto
lemma reflectionSmoothApproximation_difference_tendsto {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    Tendsto (fun q : ℕ × ℕ => ∫⁻ u, ENNReal.ofReal
      (‖reflectionSmoothApproximation ψ (q.1 : ℝ) u -
        reflectionSmoothApproximation ψ (q.2 : ℝ) u‖ ^ 2)) atTop (𝓝 0) := by
  simpa only [reflectionSmoothApproximation_difference_energy hψ] using
    reflectionFrequencyTruncation_difference_tendsto hm hψ

/-- [ The inverse truncations define a Cauchy sequence of actual spatial L² classes.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionSmoothApproximation_cauchySeq
lemma reflectionSmoothApproximation_cauchySeq {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    CauchySeq (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ (n : ℝ)).toLp
      (reflectionSmoothApproximation ψ (n : ℝ))) := by
  have he := reflectionSmoothApproximation_difference_tendsto hm hψ
  have hr := (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0 |>.comp he
  norm_num at hr
  have ht := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp hr
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  convert ht using 1
  · funext q
    rw [dist_edist, Lp.edist_toLp_toLp]
    congr 1
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    congr 1
    norm_num only [ENNReal.toReal_ofNat, Pi.sub_apply, ENNReal.rpow_two]
  · simp

/-- [ Completeness produces the spatial L² limit of the smooth inverse truncations.
Identifying this limit with the inverse Fourier class is a separate obligation.](goal) Under [the stated conditions](hyp:hm,hψ). -/
-- @node: reflectionSmoothApproximation_exists_L2_limit
lemma reflectionSmoothApproximation_exists_L2_limit {p : ℕ}
    {ψ : EuclideanSpace ℝ (Fin p) → ℂ}
    (hm : Measurable ψ) (hψ : MemLp ψ 2 volume) :
    ∃ H : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin p))),
      Tendsto (fun n : ℕ => (reflectionSmoothApproximation_memLp hψ (n : ℝ)).toLp
        (reflectionSmoothApproximation ψ (n : ℝ))) atTop (𝓝 H) :=
  cauchySeq_tendsto_of_complete (reflectionSmoothApproximation_cauchySeq hm hψ)

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
