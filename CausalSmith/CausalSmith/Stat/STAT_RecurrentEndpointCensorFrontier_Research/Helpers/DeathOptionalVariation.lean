module
public import Causalean.Stat.RecurrentEvent.CountingProcess.NelsonAalen

/-! # Deterministic weighted death optional variation

The nonnegative compensator identity applies to inverse-risk squared death
marks with any measurable deterministic weight. Extended integrals retain
terminal weights without an unjustified bounded-integrand isometry.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP

open Causalean.Stat.RecurrentEvent.CountingProcess

/-- A deterministic measurable weight times inverse risk squared is a
predictable, jointly measurable death payoff. -/
-- @node: weightedInverseRiskSq_predictable
lemma weightedInverseRiskSq_predictable {n : ℕ} (W : ℝ → ℝ) :
    LeftPredictable (fun t (x : Sample n) => W t * inverseRisk t x ^ 2) := by
  intro t x y hxy
  change W t * inverseRisk t x ^ 2 = W t * inverseRisk t y ^ 2
  rw [inverseRisk_leftPredictable t x y hxy]

/-- Nonnegative weighted squared inverse-risk marks have exactly their
hazard compensator expectation, including weights unbounded at the endpoint. -/
-- @node: weightedInverseRiskSq_event_lintegral
lemma weightedInverseRiskSq_event_lintegral {n : ℕ}
    (failureLaw deathLaw : Measure ℝ) (hazard W : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard deathLaw hazard)
    (hW : Measurable W) (hW0 : ∀ t, 0 ≤ W t)
    (i : Fin n) {U : ℝ} (hU : 0 ≤ U) :
    (∫⁻ x : Sample n, ENNReal.ofReal
      (if (x i).2 ≤ U ∧ (x i).2 < (x i).1 then
        W (x i).2 * inverseRisk (x i).2 x ^ 2 else 0)
      ∂sampleLaw n failureLaw deathLaw) =
    ∫⁻ x : Sample n, ∫⁻ t in Icc 0 U,
      ENNReal.ofReal (W t * inverseRisk t x ^ 2 * hazard t * riskIndicator i t x)
      ∂volume ∂sampleLaw n failureLaw deathLaw := by
  apply predictable_censor_compensator_lintegral failureLaw deathLaw hazard
    hFailure hHazard _ (weightedInverseRiskSq_predictable W)
  · exact (hW.comp measurable_fst).mul (inverseRisk_jointMeasurable.pow_const 2)
  · intro t x
    exact mul_nonneg (hW0 t) (sq_nonneg _)

/-- Summing the subject compensators cancels one inverse-risk factor exactly.
This is the optional-variation identity needed before terminal tail bounds. -/
-- @node: weightedInverseRiskSq_sum_lintegral
lemma weightedInverseRiskSq_sum_lintegral {n : ℕ}
    (failureLaw deathLaw : Measure ℝ) (hazard W : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard deathLaw hazard)
    (hW : Measurable W) (hW0 : ∀ t, 0 ≤ W t)
    {U : ℝ} (hU : 0 ≤ U) :
    (∫⁻ x : Sample n, ∑ i : Fin n, ENNReal.ofReal
      (if (x i).2 ≤ U ∧ (x i).2 < (x i).1 then
        W (x i).2 * inverseRisk (x i).2 x ^ 2 else 0)
      ∂sampleLaw n failureLaw deathLaw) =
    ∫⁻ x : Sample n, ∫⁻ t in Icc 0 U,
      ENNReal.ofReal (W t * hazard t * inverseRisk t x)
      ∂volume ∂sampleLaw n failureLaw deathLaw := by
  classical
  have hm (i : Fin n) : Measurable (fun x : Sample n => ENNReal.ofReal
      (if (x i).2 ≤ U ∧ (x i).2 < (x i).1 then
        W (x i).2 * inverseRisk (x i).2 x ^ 2 else 0)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.ite
    · exact (measurableSet_le (show Measurable (fun x : Sample n => (x i).2) by fun_prop)
        measurable_const).inter
        (measurableSet_lt (show Measurable (fun x : Sample n => (x i).2) by fun_prop)
          (show Measurable (fun x : Sample n => (x i).1) by fun_prop))
    · exact (hW.comp (by fun_prop)).mul
        ((inverseRisk_jointMeasurable.comp
          ((show Measurable (fun x : Sample n => (x i).2) by fun_prop).prodMk
            measurable_id)).pow_const 2)
    · exact measurable_const
  have hd (i : Fin n) : Measurable (fun p : Sample n × ℝ =>
      ENNReal.ofReal (W p.2 * inverseRisk p.2 p.1 ^ 2 * hazard p.2 *
        riskIndicator i p.2 p.1)) := by
    have hr : Measurable (fun p : Sample n × ℝ => riskIndicator i p.2 p.1) := by
      unfold riskIndicator
      apply Measurable.ite _ measurable_const measurable_const
      exact (measurableSet_le measurable_const measurable_snd).inter
        ((measurableSet_le measurable_snd
          (show Measurable (fun p : Sample n × ℝ => (p.1 i).1) by fun_prop)).inter
          (measurableSet_le measurable_snd
            (show Measurable (fun p : Sample n × ℝ => (p.1 i).2) by fun_prop)))
    exact (((hW.comp measurable_snd).mul
      ((inverseRisk_jointMeasurable.comp measurable_swap).pow_const 2)).mul
        (hHazard.2.1.comp measurable_snd)).mul hr |>.ennreal_ofReal
  rw [lintegral_finsetSum _ (fun i _ => hm i)]
  simp_rw [weightedInverseRiskSq_event_lintegral failureLaw deathLaw hazard W
    hFailure hHazard hW hW0 _ hU]
  rw [← lintegral_finsetSum _ (fun i _ => (hd i).lintegral_prod_right')]
  apply lintegral_congr
  intro x
  have hs := lintegral_finsetSum (μ := volume.restrict (Icc 0 U)) Finset.univ
    (f := fun i t => ENNReal.ofReal
      (W t * inverseRisk t x ^ 2 * hazard t * riskIndicator i t x))
    (fun i _ => (hd i).comp
      ((measurable_const : Measurable (fun _ : ℝ => x)).prodMk measurable_id))
  rw [← hs]
  apply lintegral_congr
  intro t
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
    have hr : 0 ≤ riskIndicator i t x := by unfold riskIndicator; split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg (hW0 t) (sq_nonneg _))
      (hHazard.2.2.1 t)) hr)]
  congr 1
  calc
    _ = W t * hazard t * (inverseRisk t x ^ 2 * ∑ i : Fin n, riskIndicator i t x) := by
      rw [← Finset.mul_sum]
      ring
    _ = _ := by rw [inverseRisk_square_risk]

/-- Tonelli separates deterministic death weights from the expected reciprocal
risk. This formula permits integrable endpoint envelopes without a global
bound on the oracle weight. -/
-- @node: weightedInverseRiskSq_sum_tonelli
lemma weightedInverseRiskSq_sum_tonelli {n : ℕ}
    (failureLaw deathLaw : Measure ℝ) (hazard W : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard deathLaw hazard)
    (hW : Measurable W) (hW0 : ∀ t, 0 ≤ W t)
    {U : ℝ} (hU : 0 ≤ U) :
    (∫⁻ x : Sample n, ∑ i : Fin n, ENNReal.ofReal
      (if (x i).2 ≤ U ∧ (x i).2 < (x i).1 then
        W (x i).2 * inverseRisk (x i).2 x ^ 2 else 0)
      ∂sampleLaw n failureLaw deathLaw) =
    ∫⁻ t in Icc 0 U, ENNReal.ofReal (W t * hazard t) *
      (∫⁻ x : Sample n, ENNReal.ofReal (inverseRisk t x)
        ∂sampleLaw n failureLaw deathLaw) ∂volume := by
  letI : IsProbabilityMeasure failureLaw := ⟨hFailure.1⟩
  letI : IsProbabilityMeasure deathLaw := ⟨hHazard.1.1⟩
  letI : IsProbabilityMeasure (sampleLaw n failureLaw deathLaw) := by
    unfold sampleLaw; infer_instance
  rw [weightedInverseRiskSq_sum_lintegral failureLaw deathLaw hazard W
    hFailure hHazard hW hW0 hU]
  rw [lintegral_lintegral_swap (by
    exact (((hW.comp measurable_snd).mul (hHazard.2.1.comp measurable_snd)).mul
      (inverseRisk_jointMeasurable.comp measurable_swap)).ennreal_ofReal.aemeasurable)]
  apply lintegral_congr
  intro t
  simp_rw [ENNReal.ofReal_mul (mul_nonneg (hW0 t) (hHazard.2.2.1 t))]
  exact lintegral_const_mul _
    (inverseRisk_jointMeasurable.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal

/-- A terminal interval is selected by a deterministic indicator before
compensation. The exact tail formula retains the squared remaining-mean weight. -/
-- @node: terminalInverseRiskSq_sum_tonelli
lemma terminalInverseRiskSq_sum_tonelli {n : ℕ}
    (failureLaw deathLaw : Measure ℝ) (hazard H : ℝ → ℝ)
    (hFailure : NonnegativeTimeLaw failureLaw)
    (hHazard : HasCensorHazard deathLaw hazard)
    (hH : Measurable H) (T : ℝ) {U : ℝ} (hU : 0 ≤ U) :
    (∫⁻ x : Sample n, ∑ i : Fin n, ENNReal.ofReal
      (if T < (x i).2 ∧ (x i).2 ≤ U ∧ (x i).2 < (x i).1 then
        H (x i).2 ^ 2 * inverseRisk (x i).2 x ^ 2 else 0)
      ∂sampleLaw n failureLaw deathLaw) =
    ∫⁻ t in Icc 0 U, ENNReal.ofReal
      ((if T < t then H t ^ 2 else 0) * hazard t) *
      (∫⁻ x : Sample n, ENNReal.ofReal (inverseRisk t x)
        ∂sampleLaw n failureLaw deathLaw) ∂volume := by
  have h := weightedInverseRiskSq_sum_tonelli (n := n) failureLaw deathLaw hazard
    (fun t => if T < t then H t ^ 2 else 0) hFailure hHazard
    ((hH.pow_const 2).ite (measurableSet_lt measurable_const measurable_id)
      measurable_const)
    (by intro t; split_ifs <;> positivity) hU
  convert h using 1
  apply lintegral_congr
  intro x
  apply Finset.sum_congr rfl
  intro i _
  by_cases hT : T < (x i).2 <;>
    by_cases hU : (x i).2 ≤ U <;>
    by_cases hd : (x i).2 < (x i).1 <;> simp [hT, hU, hd]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier.DeathCP
