module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionDeathReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionExtinction
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionInfluenceAssembly
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionProjection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.PositiveRetentionRecurrenceReplacement
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalAsymptoticLinearity

/-!
# Positive-retention influence expansion

Roadmap (27): assemble the full-horizon recurrence and death oracle replacements
with the exact error decomposition and negligible extinction. Subtract the arm
expansions and remove projection using its proved inactivity. The contrast is
centered at the difference of the survival-intensity arm means; identifying this
with the clinical causal target is a separate expectation identity.
-/

public section

open MeasureTheory Set Filter ProbabilityTheory
open Causalean.Stat.RecurrentEvent.CountingProcess

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The raw ordinary arm mean has the exact paper influence expansion at
root-n scale, by the actual oracle replacements and negligible extinction. -/
-- @node: positiveRetention_ordinaryMuTilde_influence_probability_tendsto_zero
lemma positiveRetention_ordinaryMuTilde_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) 
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) (a : Arm) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a) -
        (∑ i : Fin n, subcriticalInfluence c P a (s i)) / Real.sqrt n|})
      atTop (nhds 0) := by
  let R := fun n (s : Fin n → ObsHistory) => Real.sqrt n * recurrenceError c P a s 0 -
    observedRecurrenceScore P a n 1 (fun t => (retention P a t)⁻¹) s /
      (P.p a * Real.sqrt n)
  let D := fun n (s : Fin n → ObsHistory) => Real.sqrt n * deathError c P a s 0 -
    aggregateIntegral (referenceDeathHazard P a)
      (fun t (_ : Sample n) => subcriticalDeathOracleWeight c P a t) 1
      (observedDeathSample a s) / Real.sqrt n
  let E := fun n (s : Fin n → ObsHistory) => Real.sqrt n * extinctionError c P a s 0
  have hR : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |R n s|}) atTop (nhds 0) := fun _ hδ =>
    positiveRetention_recurrenceError_zero_oracle_difference_probability_tendsto_zero c P hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon a hδ
  have hD : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |D n s|}) atTop (nhds 0) := fun _ hδ =>
    positiveRetention_deathError_zero_oracle_difference_probability_tendsto_zero c P hPoisson hDeath hDeathBounds hRandom hAssignment hCensor hOverlap hRecurBounds hHorizon a hδ
  have hE : ∀ δ, 0 < δ → Tendsto (fun n => (sampleLaw P n).real
      {s | δ < |E n s|}) atTop (nhds 0) := fun _ hδ =>
    positiveRetention_extinctionError_rootn_probability_tendsto_zero c P hRandom hAssignment hOverlap hDeath hCensor hRecurBounds hDeathBounds hHorizon a hδ
  have ht := sampleLaw_negligible_sub P (fun n s => R n s - D n s) E
    (fun _ hδ => sampleLaw_negligible_sub P R D hR hD hδ) hE hε
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 3] with n hn
  apply measureReal_congr
  filter_upwards [positiveRetention_ordinaryMuTilde_error_decomposition_ae c P hIid hRandom hAssignment hPoisson hDeath hRD hCensor hDeathBounds a hn,
    positiveRetention_armOracle_ae_eq_influence_sum c P hPoisson hDeath hRecurBounds hDeathBounds hHorizon a n] with s hs ho
  change (ε < |R n s - D n s - E n s|) =
    (ε < |Real.sqrt n * (ordinaryMuTilde a s - armMean P a) -
      (∑ i : Fin n, subcriticalInfluence c P a (s i)) / Real.sqrt n|)
  rw [← ho, hs]
  dsimp [R, D, E]
  congr 2
  simp only [sub_div, div_div]
  ring

/-- Subtracting the two raw arm expansions gives the unprojected causal
contrast expansion with the paper's subject-level influence contrast. -/
-- @node: positiveRetention_rawContrast_influence_probability_tendsto_zero
lemma positiveRetention_rawContrast_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) 
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryMuTilde true s - ordinaryMuTilde false s -
        (armMean P true - armMean P false)) - (∑ i : Fin n,
          (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
            Real.sqrt n|}) atTop (nhds 0) := by
  have ht := sampleLaw_negligible_sub P
    (fun n s => Real.sqrt n * (ordinaryMuTilde true s - armMean P true) -
      (∑ i : Fin n, subcriticalInfluence c P true (s i)) / Real.sqrt n)
    (fun n s => Real.sqrt n * (ordinaryMuTilde false s - armMean P false) -
      (∑ i : Fin n, subcriticalInfluence c P false (s i)) / Real.sqrt n)
    (fun _ hδ => positiveRetention_ordinaryMuTilde_influence_probability_tendsto_zero
      c P hIid hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon true hδ)
    (fun _ hδ => positiveRetention_ordinaryMuTilde_influence_probability_tendsto_zero
      c P hIid hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon false hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  simp only [Finset.sum_sub_distrib, sub_div]
  congr 2
  ring

/-- The actual observable ordinary estimator is root-n asymptotically
linear, since projection is inactive with probability tending to one. -/
-- @node: positiveRetention_ordinaryEstimator_influence_probability_tendsto_zero
lemma positiveRetention_ordinaryEstimator_influence_probability_tendsto_zero
    (c : ClassConstants) (P : SubjectLaw) 
    (hIid : ∀ n, IidSampling P n (sampleLaw P n))
    (hRandom : RandomAssignment P) (hAssignment : AssignmentLaw P)
    (hOverlap : TreatmentOverlap c P) (hPoisson : PoissonRecurrence P)
    (hDeath : DeathHazard P) (hRD : RecurrenceDeathIndependence P)
    (hCensor : IndependentCensoring P) (hRecurBounds : RecurrenceBounds c P)
    (hDeathBounds : DeathBounds c P) (hHorizon : PositiveHorizonRetention c P) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (sampleLaw P n).real {s |
      ε < |Real.sqrt n * (ordinaryEstimator c s - (armMean P true - armMean P false)) -
        (∑ i : Fin n, (subcriticalInfluence c P true (s i) -
          subcriticalInfluence c P false (s i))) / Real.sqrt n|})
      atTop (nhds 0) := by
  have ht := sampleLaw_negligible_sub P
    (fun n s => Real.sqrt n * (ordinaryMuTilde true s - ordinaryMuTilde false s -
      (armMean P true - armMean P false)) - (∑ i : Fin n,
        (subcriticalInfluence c P true (s i) - subcriticalInfluence c P false (s i))) /
          Real.sqrt n)
    (fun n s => -(Real.sqrt n *
      (ordinaryEstimator c s - (ordinaryMuTilde true s - ordinaryMuTilde false s))))
    (fun _ hδ => positiveRetention_rawContrast_influence_probability_tendsto_zero c P hIid hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon hδ)
    (fun _ hδ => by simpa only [abs_neg] using
      positiveRetention_projectionDifference_rootn_probability_tendsto_zero c P hIid hRandom hAssignment hOverlap hPoisson hDeath hRD hCensor hRecurBounds hDeathBounds hHorizon hδ) hε
  convert ht using 1
  funext n
  congr 1
  ext s
  simp only [Set.mem_setOf_eq]
  congr 2
  ring

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
