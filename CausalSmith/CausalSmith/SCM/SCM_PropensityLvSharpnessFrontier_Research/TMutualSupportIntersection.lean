import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.BinaryWitness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TBowMixtureCompleteness
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TOneSidedBowMixtureCompleteness

/-! # Fixed-stratum reverse-support intersections -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Every measure on a full-support binary alphabet is dominated by that
binary law.  For the specified model objects, [the stated conditions](hyp:hp), [the stated mathematical relationship holds](goal).
-/
-- @node: measure_absolutelyContinuous_binaryLaw
lemma measure_absolutelyContinuous_binaryLaw (Q : Measure Bool) (p : ℝ)
    (hp : p ∈ Set.Ioo 0 1) : Q.AbsolutelyContinuous (binaryLaw p) := by
  intro s hs
  simp [binaryLaw] at hs
  have hfs : false ∉ s := hs.1.resolve_left (not_le_of_gt hp.2)
  have hts : true ∉ s := hs.2.resolve_left (not_le_of_gt hp.1)
  have hempty : s = ∅ := by
    ext b
    cases b <;> simp [hfs, hts]
  simp [hempty]

/-- Mutual-support classes are reverse-support intersections of their literal
one-sided counterparts; on full-support binary alphabets the regimes agree.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: prop:mutual-support-intersection
theorem mutual_support_intersection {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y]
    (a : Bool) (e : ℝ) (P : Measure Y) (f : ℝ → ℝ)
    [IsProbabilityMeasure P] (hPos : StrictPositivity e)
    (hf : AdmissibleGenerator f) :
    bowCompatibleSet a e P =
        bowCompatibleOneSidedSet a e P ∩ {Q | Q.AbsolutelyContinuous P} ∧
    mixtureClassSet e P =
        mixtureClassOneSidedSet e P ∩ {Q | Q.AbsolutelyContinuous P} ∧
    jkBallSet f e P =
        jkBallOneSidedSet f e P ∩ {Q | Q.AbsolutelyContinuous P} ∧
    (∀ p : ℝ, p ∈ Set.Ioo 0 1 →
      jkBallSet f e (binaryLaw p) = jkBallOneSidedSet f e (binaryLaw p)) := by
  letI := upgradeStandardBorel Y
  have hBow := (bowCompatible_eq_mixtureClass a e P hPos).1
  have hBowOne := (bowCompatibleOneSided_eq_mixtureClassOneSided a e P hPos).1
  have hMix : mixtureClassSet e P =
      mixtureClassOneSidedSet e P ∩ {Q | Q.AbsolutelyContinuous P} := by
    ext Q
    exact mixture_reverse_support e P Q hPos
  refine ⟨?_, hMix, ?_, ?_⟩
  · rw [hBow, hBowOne]
    exact hMix
  · ext Q
    constructor
    · intro hQ
      exact ⟨
        { positivity := hQ.positivity
          admissible := hQ.admissible
          observed_probability := hQ.observed_probability
          candidate_probability := hQ.candidate_probability
          forward_support := hQ.mutual_ac.2
          divergence_le := hQ.divergence_le },
        hQ.mutual_ac.1⟩
    · rintro ⟨hQ, hQP⟩
      exact
        { positivity := hQ.positivity
          admissible := hQ.admissible
          observed_probability := hQ.observed_probability
          candidate_probability := hQ.candidate_probability
          mutual_ac := ⟨hQP, hQ.forward_support⟩
          divergence_le := hQ.divergence_le }
  · intro p hp
    ext Q
    constructor
    · intro hQ
      exact
        { positivity := hQ.positivity
          admissible := hQ.admissible
          observed_probability := hQ.observed_probability
          candidate_probability := hQ.candidate_probability
          forward_support := hQ.mutual_ac.2
          divergence_le := hQ.divergence_le }
    · intro hQ
      exact
        { positivity := hQ.positivity
          admissible := hQ.admissible
          observed_probability := hQ.observed_probability
          candidate_probability := hQ.candidate_probability
          mutual_ac :=
            ⟨measure_absolutelyContinuous_binaryLaw Q p hp, hQ.forward_support⟩
          divergence_le := hQ.divergence_le }

end CausalSmith.SCM.PropensityLvSharpnessFrontier
