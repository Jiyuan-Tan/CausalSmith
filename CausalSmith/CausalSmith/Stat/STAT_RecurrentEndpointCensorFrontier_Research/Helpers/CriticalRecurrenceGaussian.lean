module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalRecurrenceCharFun
public import Causalean.Stat.CLT.Martingale.Main
public import Causalean.Stat.Quantile.CdfConvergence

/-!
# Critical recurrence Gaussian limit

The exact selected-arm characteristic-function identity and its exponential
expectation limit imply weak Gaussian convergence by the existing Lévy bridge.
The continuous Gaussian CDF then gives the pointwise recurrence limit.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The critical recurrence contrast is measurable for every admitted sample size. -/
-- @node: measurable_critical_recurrence_standardized
@[fun_prop]
lemma measurable_critical_recurrence_standardized (c : ClassConstants)
    (P : SubjectLaw) (hP : ModelClass c P) {n : ℕ} (hn : 3 ≤ n) :
    Measurable (fun s : Fin n → ObsHistory => Real.sqrt ((n : ℝ) / Real.log n) *
      (recurrenceError c P true s (bandwidth c n) -
        recurrenceError c P false s (bandwidth c n)) / Real.sqrt (criticalVariance c P)) := by
  have hh := bandwidth_pos_and_le_cap c (show 0 < n by omega)
  have hh1 : bandwidth c n ≤ 1 := by linarith [c.x0_le]
  have ht := measurable_recurrenceError c P hP true n hh.1 hh1
  have hf := measurable_recurrenceError c P hP false n hh.1 hh1
  fun_prop

/-- The standardized recurrence CDF converges to the standard normal CDF
along arbitrary triangular model laws, as in roadmap (19)--(20). -/
-- @node: critical_recurrence_cdf_triangular_tendsto
lemma critical_recurrence_cdf_triangular_tendsto
    (c : ClassConstants) (hk : c.kappa = 1) (Pseq : ℕ → SubjectLaw)
    (hP : ∀ n, ModelClass c (Pseq n)) (x : ℝ) :
    Tendsto (fun n => (sampleLaw (Pseq n) n).real {s |
      Real.sqrt ((n : ℝ) / Real.log n) *
        (recurrenceError c (Pseq n) true s (bandwidth c n) -
          recurrenceError c (Pseq n) false s (bandwidth c n)) /
        Real.sqrt (criticalVariance c (Pseq n)) ≤ x}) atTop (nhds (normalCDF x)) := by
  letI (n : ℕ) : IsProbabilityMeasure (Pseq n).latent := ⟨(Pseq n).prob⟩
  letI (n : ℕ) : IsProbabilityMeasure (observedLaw (Pseq n)) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw (Pseq n) n) := by
    unfold sampleLaw; infer_instance
  let V := fun n (s : Fin n → ObsHistory) => if 3 ≤ n then
    Real.sqrt ((n : ℝ) / Real.log n) *
      (recurrenceError c (Pseq n) true s (bandwidth c n) -
        recurrenceError c (Pseq n) false s (bandwidth c n)) /
      Real.sqrt (criticalVariance c (Pseq n)) else 0
  have hm (n : ℕ) : Measurable (V n) := by
    by_cases hn : 3 ≤ n
    · simpa only [V, if_pos hn] using
        measurable_critical_recurrence_standardized c (Pseq n) (hP n) hn
    · simpa only [V, if_neg hn] using (measurable_const (a := (0 : ℝ)))
  let νs : ℕ → ProbabilityMeasure ℝ := fun n =>
    ProbabilityMeasure.map
      (⟨sampleLaw (Pseq n) n, inferInstance⟩ : ProbabilityMeasure (Fin n → ObsHistory))
      (hm n).aemeasurable
  let ν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩
  have hweak : Tendsto νs atTop (nhds ν) := by
    apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
    intro u
    have hg : charFun (ν : Measure ℝ) u =
        Complex.exp (-((u ^ 2 / 2 : ℝ) : ℂ)) := by
      change charFun (gaussianReal 0 1) u = _
      rw [charFun_gaussianReal]
      simp only [Complex.ofReal_zero, zero_mul, mul_zero, zero_sub,
        NNReal.coe_one, Complex.ofReal_one, one_mul]
      congr 1
      push_cast
      ring
    rw [hg]
    apply (critical_recurrence_charFun_triangular_tendsto c hk Pseq hP u).congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    change _ = charFun ((sampleLaw (Pseq n) n).map (V n)) u
    rw [charFun_apply_real, integral_map (hm n).aemeasurable (by fun_prop)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun s => by
      simp only [V, if_pos hn]
      congr 1
      push_cast
      ring)
  have ht := Causalean.Stat.tendsto_cdf_at_of_tendsto hweak
    (Causalean.Stat.continuous_cdf_gaussianReal_zero (by norm_num : (0 : NNReal) < 1)).continuousAt
      (t := x)
  have hnormal : cdf (ν : Measure ℝ) x = normalCDF x := by
    exact cdf_eq_real (gaussianReal 0 1) x
  rw [hnormal] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [cdf_eq_real]
  have he := map_measureReal_apply_of_aemeasurable
    (μ := sampleLaw (Pseq n) n) (s := Iic x) (hm n).aemeasurable measurableSet_Iic
  change ((sampleLaw (Pseq n) n).map (V n)).real (Iic x) = _
  simpa only [V, if_pos hn, Set.preimage, mem_Iic] using he

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
