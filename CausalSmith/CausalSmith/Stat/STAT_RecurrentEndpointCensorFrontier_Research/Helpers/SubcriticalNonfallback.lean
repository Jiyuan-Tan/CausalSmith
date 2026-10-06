module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SubcriticalVariance
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Subcritical nonfallback probability

The exact empty-arm probability and consistency of a positive variance imply
vanishing fallback probability, as in roadmap equations (22) and (43).
-/

public section

open MeasureTheory Set Filter ProbabilityTheory

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Independent sampling gives the exact probability of an empty treatment arm. -/
-- @node: armSize_zero_probability
lemma armSize_zero_probability (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) (n : ℕ) :
    (sampleLaw P n).real {s | armSize a s = 0} = (1 - P.p a) ^ n := by
  classical
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  let E : Set ObsHistory := {o | o.treatment = a}
  have hm : MeasurableSet E :=
    measurableSet_eq_fun measurable_obsHistory_treatment measurable_const
  have he : {s : Fin n → ObsHistory | armSize a s = 0} =
      Set.pi Set.univ (fun _ => Eᶜ) := by
    ext s
    simp [armSize, Finset.card_eq_zero, Finset.filter_eq_empty_iff, E, Set.mem_pi]
  have hp : (observedLaw P).real E = P.p a := by
    rw [observedLaw, measureReal_def, Measure.map_apply measurable_observe hm]
    exact hP.assignmentLaw a
  rw [he, sampleLaw, measureReal_def, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]
  rw [← measureReal_def, probReal_compl_eq_one_sub hm, hp]

/-- Treatment overlap makes each empty-arm probability vanish geometrically. -/
-- @node: armSize_zero_probability_tendsto_zero
lemma armSize_zero_probability_tendsto_zero (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    Tendsto (fun n => (sampleLaw P n).real {s | armSize a s = 0})
      atTop (nhds 0) := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  have hp : P.p a ≤ 1 := by
    rw [← hP.assignmentLaw a]
    exact measureReal_le_one
  simp_rw [armSize_zero_probability c P hP a]
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (sub_nonneg.mpr hp)
    (by linarith [c.pMin_pos, hP.treatmentOverlap a])

/-- If both arms are present, a fallback requires a variance error of at
least half the positive population variance. -/
-- @node: nonFallbackSub_compl_subset_variance_error
lemma nonFallbackSub_compl_subset_variance_error (c : ClassConstants) {v : ℝ}
    (hv : 0 < v) (n : ℕ) :
    {s : Fin n → ObsHistory | ¬ nonFallbackSub c s} ⊆
      {s | armSize false s = 0} ∪ {s | armSize true s = 0} ∪
        {s | v / 2 < |sigmaHatSq c s - v|} := by
  intro s hs
  by_cases hf : armSize false s = 0
  · exact Or.inl (Or.inl hf)
  by_cases ht : armSize true s = 0
  · exact Or.inl (Or.inr ht)
  apply Or.inr
  have hbad : sigmaHatSq c s ≤ 0 := by
    by_contra h
    exact hs ⟨Nat.pos_of_ne_zero hf, Nat.pos_of_ne_zero ht, lt_of_not_ge h⟩
  change v / 2 < |sigmaHatSq c s - v|
  rw [abs_of_nonpos (by linarith : sigmaHatSq c s - v ≤ 0)]
  linarith

/-- A union bound controls fallback by the two empty-arm probabilities and
one variance-consistency event, without any independence requirement. -/
-- @node: nonFallbackSub_compl_probability_le
lemma nonFallbackSub_compl_probability_le (c : ClassConstants) (P : SubjectLaw)
    {v : ℝ} (hv : 0 < v) (n : ℕ) :
    (sampleLaw P n).real {s | ¬ nonFallbackSub c s} ≤
      (sampleLaw P n).real {s | armSize false s = 0} +
      (sampleLaw P n).real {s | armSize true s = 0} +
      (sampleLaw P n).real {s | v / 2 < |sigmaHatSq c s - v|} := by
  letI : IsProbabilityMeasure P.latent := ⟨P.prob⟩
  letI : IsProbabilityMeasure (observedLaw P) :=
    Measure.isProbabilityMeasure_map measurable_observe.aemeasurable
  letI : IsProbabilityMeasure (sampleLaw P n) := by unfold sampleLaw; infer_instance
  exact (measureReal_mono (nonFallbackSub_compl_subset_variance_error c hv n)
    (by finiteness)).trans ((measureReal_union_le _ _).trans
      (add_le_add (measureReal_union_le _ _) le_rfl))

/-- Consistency of the observable subcritical variance proves that its
nonfallback event has probability tending to one. -/
-- @node: nonFallbackSub_compl_probability_tendsto_of_variance_consistency
lemma nonFallbackSub_compl_probability_tendsto_of_variance_consistency
    (c : ClassConstants) (P : SubjectLaw) (hP : ModelClass c P)
    (hk : c.kappa < 1)
    (hvar : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (sampleLaw P n).real
      {s | ε < |sigmaHatSq c s - subcriticalVariance c P|}) atTop (nhds 0)) :
    Tendsto (fun n => (sampleLaw P n).real {s | ¬ nonFallbackSub c s})
      atTop (nhds 0) := by
  have hv := subcriticalVariance_pos c P hP hk
  have hsum := ((armSize_zero_probability_tendsto_zero c P hP false).add
    (armSize_zero_probability_tendsto_zero c P hP true)).add
    (hvar (subcriticalVariance c P / 2) (half_pos hv))
  exact squeeze_zero (fun n => measureReal_nonneg)
    (nonFallbackSub_compl_probability_le c P hv) (by simpa using hsum)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
