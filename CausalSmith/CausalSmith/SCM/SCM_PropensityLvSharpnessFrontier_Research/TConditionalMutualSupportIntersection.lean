import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements

/-! # Conditional reverse-support intersections -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set

/-- The three mutual-support conditional classes are the intersections of the
corresponding one-sided classes with one common-conull reverse-support class,
and the one-sided mixture and adaptive-hinge classes have automatic forward
support on a common measurable conull set.  For the specified model objects, [the stated conditions](hyp:hOverlap,hP), [the stated mathematical relationship holds](goal).
-/
-- @node: prop:conditional-mutual-support-intersection
theorem cond_mutual_support_intersection
    {X Y : Type*} [MeasurableSpace X] [StandardBorelSpace X]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    (kappa : ℝ) (muX : Measure X) (e : Bool → X → ℝ)
    [IsProbabilityMeasure muX] (P : Bool → Kernel X Y)
    (hOverlap : CondOverlap kappa e) (hP : ∀ a, IsMarkovKernel (P a)) :
    condBowCompatibleSet kappa muX e P =
      condBowCompatibleOneSidedSet kappa muX e P ∩ reverseSupportSet muX P ∧
    condMixtureClassSet kappa muX e P =
      condMixtureClassOneSidedSet kappa muX e P ∩ reverseSupportSet muX P ∧
    condAdaptiveHingeBallSet kappa muX e P =
      condAdaptiveHingeBallOneSidedSet kappa muX e P ∩ reverseSupportSet muX P ∧
    (∀ Q ∈ condMixtureClassOneSidedSet kappa muX e P,
      ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧
        ∀ x ∈ S, ∀ a, (P a x).AbsolutelyContinuous (Q a x)) ∧
    (∀ Q ∈ condAdaptiveHingeBallOneSidedSet kappa muX e P,
      ∃ S : Set X, MeasurableSet S ∧ muX Sᶜ = 0 ∧
        ∀ x ∈ S, ∀ a, (P a x).AbsolutelyContinuous (Q a x)) := by
  have hinter (S T : Set X) (hS : MeasurableSet S) (hT : MeasurableSet T)
      (hSc : muX Sᶜ = 0) (hTc : muX Tᶜ = 0) :
      MeasurableSet (S ∩ T) ∧ muX (S ∩ T)ᶜ = 0 := by
    refine ⟨hS.inter hT, ?_⟩
    rw [compl_inter]
    exact measure_union_null hSc hTc
  constructor
  · ext Q
    constructor
    · rintro ⟨hmu, hov, hQ⟩
      refine ⟨⟨hmu, hov, ?_⟩, hP, hQ.candidate_markov, hQ.reverse_support⟩
      refine
        { realization := ?_
          architecture := hQ.architecture
          overlap := hQ.overlap
          consistency := hQ.consistency
          observed_markov := hQ.observed_markov
          candidate_markov := hQ.candidate_markov }
      obtain ⟨w, hwarch, hwcons, hwmu, S, hS, hSc, hw⟩ := hQ.realization
      refine ⟨w, hwarch, hwcons, hwmu, S, hS, hSc, ?_⟩
      intro x hx a
      exact ⟨(hw x hx a).1, (hw x hx a).2.1, (hw x hx a).2.2.1⟩
    · rintro ⟨⟨hmu, hov, hQ⟩, _, _, hrev⟩
      refine ⟨hmu, hov, ?_⟩
      refine
        { realization := ?_
          architecture := hQ.architecture
          overlap := hQ.overlap
          consistency := hQ.consistency
          reverse_support := hrev
          observed_markov := hQ.observed_markov
          candidate_markov := hQ.candidate_markov }
      obtain ⟨w, hwarch, hwcons, hwmu, S, hS, hSc, hw⟩ := hQ.realization
      obtain ⟨T, hT, hTc, hTrev⟩ := hrev
      obtain ⟨hST, hSTc⟩ := hinter S T hS hT hSc hTc
      refine ⟨w, hwarch, hwcons, hwmu, S ∩ T, hST, hSTc, ?_⟩
      rintro x ⟨hxS, hxT⟩ a
      exact ⟨(hw x hxS a).1, (hw x hxS a).2.1, (hw x hxS a).2.2,
        hTrev x hxT a⟩
  constructor
  · ext Q
    constructor
    · intro hQ
      obtain ⟨R, hRmarkov, S, hS, hSc, hrep⟩ := hQ.representation
      refine ⟨?_, hP, hQ.candidate_markov, ?_⟩
      · exact
          { overlap := hQ.overlap
            covariate_probability := hQ.covariate_probability
            observed_markov := hQ.observed_markov
            candidate_markov := hQ.candidate_markov
            representation := ⟨R, hRmarkov, S, hS, hSc,
              fun x hx a => (hrep x hx a).1⟩ }
      · refine ⟨S, hS, hSc, ?_⟩
        intro x hx a B hPB
        rw [(hrep x hx a).1, Measure.add_apply, Measure.smul_apply,
          Measure.smul_apply, hPB, (hrep x hx a).2 hPB]
        simp
    · rintro ⟨hQ, _, _, hrev⟩
      obtain ⟨R, hRmarkov, S, hS, hSc, hrep⟩ := hQ.representation
      obtain ⟨T, hT, hTc, hTrev⟩ := hrev
      obtain ⟨hST, hSTc⟩ := hinter S T hS hT hSc hTc
      refine
        { overlap := hQ.overlap
          covariate_probability := hQ.covariate_probability
          observed_markov := hQ.observed_markov
          candidate_markov := hQ.candidate_markov
          representation := ⟨R, hRmarkov, S ∩ T, hST, hSTc, ?_⟩ }
      rintro x ⟨hxS, hxT⟩ a
      refine ⟨hrep x hxS a, ?_⟩
      intro B hPB
      have hQzero : Q a x B = 0 := hTrev x hxT a hPB
      rw [hrep x hxS a, Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply] at hQzero
      have he_lt : e a x < 1 := by
        have he_le := (hQ.overlap.2.2.2 x a).2
        linarith [hQ.overlap.1]
      have hcoef : ENNReal.ofReal (1 - e a x) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr he_lt))
      have hz : (ENNReal.ofReal (e a x) = 0 ∨ P a x B = 0) ∧ R a x B = 0 := by
        simpa [hcoef] using hQzero
      exact hz.2
  constructor
  · ext Q
    constructor
    · intro hQ
      refine ⟨?_, hP, hQ.candidate_markov, hQ.reverse_support⟩
      obtain ⟨S, hS, hSc, hfib⟩ := hQ.fiberwise
      exact
        { overlap := hQ.overlap
          covariate_probability := hQ.covariate_probability
          observed_markov := hQ.observed_markov
          candidate_markov := hQ.candidate_markov
          fiberwise := ⟨S, hS, hSc, fun x hx a =>
            ⟨(hfib x hx a).1.1, (hfib x hx a).2⟩⟩ }
    · rintro ⟨hQ, _, _, hrev⟩
      obtain ⟨S, hS, hSc, hfib⟩ := hQ.fiberwise
      obtain ⟨T, hT, hTc, hTrev⟩ := hrev
      obtain ⟨hST, hSTc⟩ := hinter S T hS hT hSc hTc
      exact
        { overlap := hQ.overlap
          reverse_support := ⟨T, hT, hTc, hTrev⟩
          covariate_probability := hQ.covariate_probability
          observed_markov := hQ.observed_markov
          candidate_markov := hQ.candidate_markov
          fiberwise := ⟨S ∩ T, hST, hSTc, fun x hx a =>
            ⟨⟨(hfib x hx.1 a).1, hTrev x hx.2 a⟩, (hfib x hx.1 a).2⟩⟩ }
  · constructor
    · intro Q hQ
      obtain ⟨R, _, S, hS, hSc, hrep⟩ := hQ.representation
      refine ⟨S, hS, hSc, ?_⟩
      intro x hx a B hQB
      rw [hrep x hx a, Measure.add_apply, Measure.smul_apply,
        Measure.smul_apply] at hQB
      have hcoef : ENNReal.ofReal (e a x) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr
          (lt_of_lt_of_le hQ.overlap.1 (hQ.overlap.2.2.2 x a).1))
      have hz : P a x B = 0 ∧
          (ENNReal.ofReal (1 - e a x) = 0 ∨ R a x B = 0) := by
        simpa [hcoef] using hQB
      exact hz.1
    · intro Q hQ
      obtain ⟨S, hS, hSc, hfib⟩ := hQ.fiberwise
      exact ⟨S, hS, hSc, fun x hx a => (hfib x hx a).1⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
