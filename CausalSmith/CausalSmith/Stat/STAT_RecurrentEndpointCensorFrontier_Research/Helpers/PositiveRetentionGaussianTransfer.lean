module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionAsymptoticLinearity
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalCoverage

/-!
# Weak-limit transfer for the positive-retention contrast

The bounded Lipschitz criterion transfers a Gaussian influence limit to the
observable contrast using its proved negligible remainder. Rows may have
different sample spaces; all probability bounds use the actual sample law.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory Topology

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

set_option backward.isDefEq.respectTransparency.types false in
/-- A negligible difference preserves the weak limit on the actual iid sample rows. -/
-- @node: sampleLaw_convergesInLaw_of_negligible
lemma sampleLaw_convergesInLaw_of_negligible (P : SubjectLaw)
    (Xn Yn : (n : ℕ) → (Fin n → ObsHistory) → ℝ)
    (Q : Measure ℝ) [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) (sampleLaw P n))
    (hYn : ∀ n, AEMeasurable (Yn n) (sampleLaw P n))
    (hCLT : ConvergesInLaw (fun n => (sampleLaw P n).map (Xn n)) Q)
    (hRem : ∀ ε, 0 < ε → Tendsto (fun n => (sampleLaw P n).real
      {s | ε < |Yn n s - Xn n s|}) atTop (nhds 0)) :
    ConvergesInLaw (fun n => (sampleLaw P n).map (Yn n)) Q := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI (n : ℕ) : IsProbabilityMeasure (sampleLaw P n) := by
    unfold sampleLaw; infer_instance
  let νX : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(sampleLaw P n).map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩
  let νY : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨(sampleLaw P n).map (Yn n), Measure.isProbabilityMeasure_map (hYn n)⟩
  let ν : ProbabilityMeasure ℝ := ⟨Q, inferInstance⟩
  have hX : Tendsto νX atTop (nhds ν) := by
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact hCLT f f.continuous
      ⟨‖f‖, fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  have hXY (ε : ℝ) (hε : 0 < ε) : Tendsto (fun n => (sampleLaw P n).real
      {s | ε ≤ |Yn n s - Xn n s|}) atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) (fun n => ?_)
      (hRem (ε / 2) (half_pos hε))
    apply measureReal_mono _ (by finiteness)
    intro s hs
    exact (half_lt_self hε).trans_le hs
  have hweak : Tendsto νY atTop (nhds ν) := by
    suffices ∀ (F : ℝ → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
        (hF_lip : ∃ L, LipschitzWith L F),
        Tendsto (fun n ↦ ∫ y, F y ∂((sampleLaw P n).map (Yn n))) atTop (𝓝 (∫ y, F y ∂Q)) by
      rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
    rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
    have hF_cont : Continuous F := hF_lip.continuous
    obtain rfl | hL := eq_zero_or_pos L
    · simp only [LipschitzWith.zero_iff] at hF_lip
      specialize hF_lip (0 : ℝ)
      simp only [← hF_lip, integral_const, smul_eq_mul]
      have h_prob n : IsProbabilityMeasure ((sampleLaw P n).map (Yn n)) := Measure.isProbabilityMeasure_map (hYn n)
      simp
    simp_rw [Metric.tendsto_nhds, Real.dist_eq]
    suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ y, F y ∂((sampleLaw P n).map (Yn n)) - ∫ y, F y ∂Q| < L * ε by
      intro ε hε
      convert this (ε / L) (by positivity)
      field_simp
    intro ε hε
    have h_le n : |∫ y, F y ∂((sampleLaw P n).map (Yn n)) - ∫ y, F y ∂Q|
        ≤ L * (ε / 2) + M * (sampleLaw P n).real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
          + |∫ y, F y ∂((sampleLaw P n).map (Xn n)) - ∫ y, F y ∂Q| := by
      refine (abs_sub_le (∫ y, F y ∂((sampleLaw P n).map (Yn n))) (∫ y, F y ∂((sampleLaw P n).map (Xn n)))
        (∫ y, F y ∂Q)).trans ?_
      gcongr
      have h_int_Y : Integrable (fun x ↦ F (Yn n x)) (sampleLaw P n) := by
        refine Integrable.of_bound (by fun_prop) (‖F (0 : ℝ)‖ + M) (ae_of_all _ fun a ↦ ?_)
        specialize hF_bounded (Yn n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (Yn n a)) (F 0)).trans hF_bounded
      have h_int_X : Integrable (fun x ↦ F (Xn n x)) (sampleLaw P n) := by
        refine Integrable.of_bound (by fun_prop) (‖F (0 : ℝ)‖ + M) (ae_of_all _ fun a ↦ ?_)
        specialize hF_bounded (Xn n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (Xn n a)) (F 0)).trans hF_bounded
      have h_int_sub : Integrable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) (sampleLaw P n) := by
        rw [integrable_norm_iff (by fun_prop)]
        exact h_int_Y.sub h_int_X
      rw [integral_map (by fun_prop) (by fun_prop), integral_map (by fun_prop) (by fun_prop),
        ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
      calc ‖∫ a, F (Yn n a) - F (Xn n a) ∂(sampleLaw P n)‖
      _ ≤ ∫ a, ‖F (Yn n a) - F (Xn n a)‖ ∂(sampleLaw P n) := norm_integral_le_integral_norm _
      _ = ∫ a in {x | ‖Yn n x - Xn n x‖ < ε / 2}, ‖F (Yn n a) - F (Xn n a)‖ ∂(sampleLaw P n)
          + ∫ a in {x | ε / 2 ≤ ‖Yn n x - Xn n x‖}, ‖F (Yn n a) - F (Xn n a)‖ ∂(sampleLaw P n) := by
        symm
        simp_rw [← not_lt]
        refine integral_add_compl₀ ?_ h_int_sub
        exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
      _ ≤ ∫ a in {x | ‖Yn n x - Xn n x‖ < ε / 2}, L * (ε / 2) ∂(sampleLaw P n)
          + ∫ a in {x | ε / 2 ≤ ‖Yn n x - Xn n x‖}, M ∂(sampleLaw P n) := by
        gcongr ?_ + ?_
        · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
          · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
          · exact fun x hx ↦ hF_lip.norm_sub_le_of_le hx.le
        · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
          rw [← dist_eq_norm]
          convert hF_bounded _ _
      _ = L * (ε / 2) * (sampleLaw P n).real {x | ‖Yn n x - Xn n x‖ < ε / 2}
          + M * (sampleLaw P n).real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
        simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
          smul_eq_mul]
        ring
      _ ≤ L * (ε / 2) + M * (sampleLaw P n).real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
        rw [mul_assoc]
        gcongr
        grw [measureReal_le_one, mul_one]
    have h_tendsto :
        Tendsto (fun n ↦ L * (ε / 2) + M * (sampleLaw P n).real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
          + |∫ y, F y ∂((sampleLaw P n).map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2)) := by
      suffices Tendsto (fun n ↦ L * (ε / 2) + M * (sampleLaw P n).real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
          + |∫ y, F y ∂((sampleLaw P n).map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by
        simpa
      refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
      · rw [mul_div_assoc]
        exact tendsto_const_nhds
      · simpa only [Real.norm_eq_abs] using hXY (ε / 2) (by positivity)
      · simp_rw [tendsto_iff_forall_lipschitz_integral_tendsto] at hX
        simpa [νX, ν, tendsto_iff_dist_tendsto_zero, Real.dist_eq] using hX F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
    have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
    filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn
  intro f hf hb
  obtain ⟨M, hM⟩ := hb
  let F : BoundedContinuousFunction ℝ ℝ :=
    ⟨⟨f, hf⟩, ⟨2 * M, fun x y => by
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hM x, hM y])⟩⟩
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) F

/-- The normalized benchmark influence sum is measurable on each actual sample row. -/
-- @node: positiveRetention_aemeasurable_influence_normalizedSum
@[fun_prop] lemma positiveRetention_aemeasurable_influence_normalizedSum
    (c : ClassConstants) (P : SubjectLaw)
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (n : ℕ) :
    AEMeasurable (fun s => (∑ i : Fin n,
      (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
        Real.sqrt n) (sampleLaw P n) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  apply AEMeasurable.div_const
  exact Finset.aemeasurable_fun_sum Finset.univ (fun i _ =>
    (positiveRetention_aemeasurable_subcriticalContrast c P hRandom hAssignment
      hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon).comp_quasiMeasurePreserving
          (measurePreserving_eval (fun _ : Fin n => observedLaw P) i).quasiMeasurePreserving)

/-- The observable ordinary contrast has the Gaussian influence limit when
centered at the survival-intensity arm-mean contrast. -/
-- @node: positiveRetention_ordinaryEstimator_armMean_gaussian
lemma positiveRetention_ordinaryEstimator_armMean_gaussian
    (c : ClassConstants) (P : SubjectLaw)
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) :
    ConvergesInLaw (fun n : ℕ => (sampleLaw P n).map
      (fun s => Real.sqrt n * (ordinaryEstimator c s -
        (armMean P true - armMean P false))))
      (gaussianReal 0 (Real.toNNReal (subcriticalVariance c P))) := by
  apply sampleLaw_convergesInLaw_of_negligible P
    (fun n s => (∑ i : Fin n,
      (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
        Real.sqrt n)
  · intro n
    exact positiveRetention_aemeasurable_influence_normalizedSum c P hRandom
      hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon n
  · intro n
    exact ((measurable_ordinaryEstimator c n).sub_const _).aemeasurable.const_mul _
  · exact positiveRetention_subcriticalInfluence_normalizedSum_gaussian c P
      hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds
      hDeathBounds hHorizon
  · intro ε hε
    exact positiveRetention_ordinaryEstimator_influence_probability_tendsto_zero
      c P hIid hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor
      hRecurBounds hDeathBounds hHorizon hε

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
