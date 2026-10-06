module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.EnergyDeviation
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservableRegularity
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ScalarInversion

/-! Total measurable connectedness, explicit endpoints and bounded loss for the
frozen attaining rule on the original sample space. -/

public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The tuned bias allowance is nonnegative at every finite sample size. -/
-- @node: tunedB_nonneg
lemma tunedB_nonneg (n : ℕ) : 0 ≤ tunedB n := by
  unfold tunedB
  exact BAllow_nonneg _ _ (by positivity) (hAllow_nonneg _ (by positivity) _ _ _) _ _ _ _ _ _

/-- Both scalar inversion budgets are nonnegative, including public fallback sizes. -/
-- @node: tuned_inversion_nonneg
lemma tuned_inversion_nonneg (n : ℕ) :
    0 ≤ aci (tunedB n) (tunedW n) ∧
      0 ≤ dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)) := by
  have hb := tunedB_nonneg n
  unfold aci dci
  constructor <;> positivity

/-- The observable procedure ignores its allowed public randomization. -/
-- @node: starRule_data_only
lemma starRule_data_only (n : ℕ) (data : Data n) (u up : ℝ) :
    starRule n (data, u) = starRule n (data, up) := by
  rfl

open Classical in
/-- The original acceptance-set rule agrees exactly with the frozen quadratic endpoints. -/
-- @node: starRule_eq_endpoints
lemma starRule_eq_endpoints (n : ℕ) (ω : SampleSpace n) :
    starRule n ω = if reportingBranch n then
      invEndpoints (tunedEnergy n ω.1) (aci (tunedB n) (tunedW n))
        (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))
      else Set.Icc 0 16 := by
  unfold starRule
  split_ifs
  · exact (invSet_eq_endpoint_interval _ _ _ (tuned_inversion_nonneg n).1).trans
      (invEndpoints_eq_endpoint_interval _ _ _).symm
  · rfl

/-- Every fiber is connected and lies in the fixed reporting range. -/
-- @node: starRule_fiber_geometry
lemma starRule_fiber_geometry (n : ℕ) (ω : SampleSpace n) :
    Set.OrdConnected (starRule n ω) ∧ starRule n ω ⊆ Set.Icc 0 16 := by
  unfold starRule
  split_ifs
  · constructor
    · rw [invSet_eq_endpoint_interval _ _ _ (tuned_inversion_nonneg n).1]
      exact Set.ordConnected_Icc
    · exact invSet_subset _ _ _
  · exact ⟨Set.ordConnected_Icc, Set.Subset.rfl⟩

/-- The inclusion graph is Borel measurable, jointly in data, randomization and energy. -/
-- @node: starRule_isIntervalRule
lemma starRule_isIntervalRule (n : ℕ) : IsIntervalRule n (starRule n) := by
  refine ⟨starRule_fiber_geometry n, ?_⟩
  by_cases h : reportingBranch n
  · have heq : {p : SampleSpace n × ℝ | p.2 ∈ starRule n p.1} =
        {p | invLower (tunedEnergy n p.1.1) (aci (tunedB n) (tunedW n))
            (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) ≤ p.2 ∧
          p.2 ≤ invUpper (tunedEnergy n p.1.1) (aci (tunedB n) (tunedW n))
            (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))} := by
      ext p
      simp only [starRule, if_pos h,
        invSet_eq_endpoint_interval _ _ _ (tuned_inversion_nonneg n).1, Set.mem_Icc,
        Set.mem_setOf_eq]
    rw [heq]
    have hz : Measurable (fun p : SampleSpace n × ℝ => tunedEnergy n p.1.1) := by fun_prop
    have hl := (inversion_endpoints_measurable (aci (tunedB n) (tunedW n))
      (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))).1.comp hz
    have hu := (inversion_endpoints_measurable (aci (tunedB n) (tunedW n))
      (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))).2.comp hz
    exact (measurableSet_le hl measurable_snd).inter (measurableSet_le measurable_snd hu)
  · simpa [starRule, h, Set.preimage] using
      (measurableSet_Icc.preimage (measurable_snd : Measurable (fun p : SampleSpace n × ℝ => p.2)))

/-- Reported length is a Borel statistic on the original sample space. -/
-- @node: measurable_starRule_length
@[fun_prop] lemma measurable_starRule_length (n : ℕ) :
    Measurable (fun ω : SampleSpace n => intervalLength (starRule n ω)) := by
  by_cases h : reportingBranch n
  · have heq : (fun ω : SampleSpace n => intervalLength (starRule n ω)) =
        (fun ω => invUpper (tunedEnergy n ω.1) (aci (tunedB n) (tunedW n))
          (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n))) -
        invLower (tunedEnergy n ω.1) (aci (tunedB n) (tunedW n))
          (dci (tunedB n) (tunedW n) (tunedV n) (tunedJ (roleSize n)))) := by
      funext ω
      simp only [starRule, if_pos h, inversion_length_eq _ _ _ (tuned_inversion_nonneg n).1]
    rw [heq]
    exact ((inversion_endpoints_measurable _ _).2.comp
      ((measurable_tunedEnergy n).comp measurable_fst)).sub
        ((inversion_endpoints_measurable _ _).1.comp
          ((measurable_tunedEnergy n).comp measurable_fst))
  · have heq : (fun ω : SampleSpace n => intervalLength (starRule n ω)) =
        fun _ => intervalLength (Set.Icc (0 : ℝ) 16) := by
      funext ω
      simp only [starRule, if_neg h]
    rw [heq]
    exact measurable_const

/-- Even bad training realizations have reported length between zero and sixteen. -/
-- @node: starRule_length_range
lemma starRule_length_range (n : ℕ) (ω : SampleSpace n) :
    intervalLength (starRule n ω) ∈ Set.Icc 0 16 := by
  unfold starRule
  split_ifs
  · exact inversion_length_range _ _ _
  · have hne : (Set.Icc (0 : ℝ) 16).Nonempty := Set.nonempty_Icc.mpr (by norm_num)
    norm_num [intervalLength, hne.ne_empty, csSup_Icc, csInf_Icc]

/-- Bounded reported length is integrable under every observed probability law. -/
-- @node: integrable_starRule_length
@[fun_prop] lemma integrable_starRule_length (P : ObsLaw) (n : ℕ) :
    Integrable (fun ω => intervalLength (starRule n ω)) (sampleLaw P n) := by
  letI : IsFiniteMeasure (sampleLaw P n) := by
    unfold sampleLaw dataLaw unitVolume
    infer_instance
  exact Integrable.of_bound (measurable_starRule_length n).aestronglyMeasurable 16
    (Filter.Eventually.of_forall (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (starRule_length_range n ω).1]
      exact (starRule_length_range n ω).2))

end CausalSmith.Stat.DensityEffectRoughNull
