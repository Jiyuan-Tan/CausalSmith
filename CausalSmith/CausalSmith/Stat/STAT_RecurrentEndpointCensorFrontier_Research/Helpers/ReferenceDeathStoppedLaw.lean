module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ReferenceDeathGlobalDensity

/-!
# Finite-horizon equivalence of the reference death law

The global exponential continuation changes no death-time observation after
administrative capping at the paper horizon.
-/

public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Capping at time one gives exactly the same law under the reference and
original arm-specific death distributions. -/
lemma referenceDeathLaw_map_min_one (P : SubjectLaw) (a : Arm) :
    (referenceDeathLaw P a).map (fun d : ℝ => min d 1) =
      (armDeathEventLaw P a).map (fun d : ℝ => min d 1) := by
  let μ := armDeathEventLaw P a
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, armDeathEventLaw]
    exact Measure.isProbabilityMeasure_map
      (measurable_latentSubject_death a).aemeasurable
  apply Measure.ext_of_Ici
  intro s
  rw [Measure.map_apply (by fun_prop) measurableSet_Ici,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  by_cases hs : s ≤ 1
  · have hpre : (fun d : ℝ => min d 1) ⁻¹' Set.Ici s = Set.Ici s := by
      ext d
      simp only [Set.mem_preimage, Set.mem_Ici, le_min_iff, and_iff_left hs]
    rw [hpre, referenceDeathLaw_apply_Ici_eq_original P a hs]
  · have hpre : (fun d : ℝ => min d 1) ⁻¹' Set.Ici s = ∅ := by
      ext d
      change (s ≤ min d 1 ↔ False)
      constructor
      · exact fun h => hs (h.trans (min_le_right d 1))
      · exact False.elim
    rw [hpre, measure_empty, measure_empty]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
