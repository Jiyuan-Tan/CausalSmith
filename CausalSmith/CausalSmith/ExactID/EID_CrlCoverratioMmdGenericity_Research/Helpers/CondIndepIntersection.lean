import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Decoder
import Causalean.Mathlib.CondIndep.CondExp
import Mathlib.Probability.Kernel.CondDistrib

/-!
# Conditional-independence bridges for parent pruning

This file scaffolds the positivity-based graphoid intersection step and the
finite-coordinate product bridge used with Causalean's generic weak-union lemma.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- Positivity-based graphoid intersection on the paper's full product support. -/
-- @node: condIndep_intersection_of_pos
lemma condIndep_intersection_of_pos
    {n : ℕ} {G : Causalean.DAG (Fin n)} {s : SignVector n} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    (order : Fin n → ℕ) (i b : Fin n) (C Z : Finset (Fin n))
    (h₁ : CondIndepGiven (W.law 0)
      (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i)
      (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order b)
      (fun x =>
        (familyProjection
            (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) Z x,
          familyProjection
            (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) C x)))
    (h₂ : CondIndepGiven (W.law 0)
      (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i)
      (familyProjection
        (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) C)
      (fun x =>
        (familyProjection
            (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) Z x,
          observedLawRankCoordinate (observedProbabilityLawFamily W.law) order b x))) :
    CondIndepGiven (W.law 0)
        (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i)
        (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order b)
        (familyProjection
          (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) Z) ∧
      CondIndepGiven (W.law 0)
        (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order i)
        (fun x =>
          (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order b x,
            familyProjection
              (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) C x))
        (familyProjection
          (observedLawRankCoordinate (observedProbabilityLawFamily W.law) order) Z) := by
  -- BLOCKER: needs-substrate(positivity-based CondIndepFun graphoid intersection)
  sorry

/-- Coordinate-pair presentation of generic weak union for a finite family of measurable maps. -/
-- @node: condIndep_coordSplit_prodMk
lemma condIndep_coordSplit_prodMk
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {n : ℕ} (U : Fin n → Ω → ℝ) (i b : Fin n) (A S : Finset (Fin n))
    (hU : ∀ c, Measurable (U c))
    (hA : A ⊆ S) (hb : b ∈ S) (hbA : b ∉ A)
    (hCI : CondIndepGiven μ (U i)
      (familyProjection U (S \ A)) (familyProjection U A)) :
    (MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
        MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance =
      MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance) ∧
    CondIndepGiven μ (U i) (U b) (familyProjection U (S.erase b)) := by
  have hproj (T : Finset (Fin n)) : Measurable (familyProjection U T) := by
    apply measurable_pi_lambda
    intro j
    exact hU j
  have hbDiff : b ∈ S \ A := Finset.mem_sdiff.mpr ⟨hb, hbA⟩
  let split : ((j : {j // j ∈ S \ A}) → ℝ) →
      ℝ × ((j : {j // j ∈ (S \ A).erase b}) → ℝ) :=
    fun x => (x ⟨b, hbDiff⟩, fun j => x ⟨j, Finset.mem_sdiff.mpr
      (Finset.mem_sdiff.mp (Finset.mem_erase.mp j.2).2)⟩)
  have hsplit : Measurable split := by
    apply Measurable.prod
    · exact measurable_pi_apply _
    · apply measurable_pi_lambda
      intro j
      exact measurable_pi_apply _
  have hCIpair : CondIndepGiven μ (U i)
      (fun ω => (U b ω, familyProjection U ((S \ A).erase b) ω))
      (familyProjection U A) := by
    rcases hCI with ⟨hμ, hXi, hY, hZA, hCI⟩
    refine ⟨hμ, hXi, (hU b).prod (hproj _), hZA, ?_⟩
    convert hCI.comp measurable_id hsplit using 1 <;>
      ext ω j <;> rfl
  have hsigma :
      MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
          MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance =
        MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance := by
    apply le_antisymm
    · apply sup_le
      · have hm : @Measurable Ω _
            (MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance)
            inferInstance (familyProjection U A) := by
          letI : MeasurableSpace Ω :=
            MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance
          refine measurable_pi_lambda _ (fun j => ?_)
          have hjS : (j : Fin n) ∈ S.erase b := Finset.mem_erase.mpr
            ⟨by intro h; subst b; exact hbA j.2, hA j.2⟩
          have heval : Measurable (fun x : ((j : {j // j ∈ S.erase b}) → ℝ) =>
              x ⟨j, hjS⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_rfl) using 1
          funext c
          rfl
        exact hm.comap_le
      · have hm : @Measurable Ω _
            (MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance)
            inferInstance (familyProjection U ((S \ A).erase b)) := by
          letI : MeasurableSpace Ω :=
            MeasurableSpace.comap (familyProjection U (S.erase b)) inferInstance
          refine measurable_pi_lambda _ (fun j => ?_)
          have hjS : (j : Fin n) ∈ S.erase b := by
            rcases Finset.mem_erase.mp j.2 with ⟨hjb, hjSA⟩
            exact Finset.mem_erase.mpr ⟨hjb, (Finset.mem_sdiff.mp hjSA).1⟩
          have heval : Measurable (fun x : ((j : {j // j ∈ S.erase b}) → ℝ) =>
              x ⟨j, hjS⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_rfl) using 1
          funext c
          rfl
        exact hm.comap_le
    · have hm : @Measurable Ω _
          (MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
            MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance)
          inferInstance (familyProjection U (S.erase b)) := by
        letI : MeasurableSpace Ω :=
          MeasurableSpace.comap (familyProjection U A) inferInstance ⊔
            MeasurableSpace.comap (familyProjection U ((S \ A).erase b)) inferInstance
        refine measurable_pi_lambda _ (fun j => ?_)
        rcases Finset.mem_erase.mp j.2 with ⟨hjb, hjS⟩
        by_cases hjA : (j : Fin n) ∈ A
        · have heval : Measurable (fun x : ((j : {j // j ∈ A}) → ℝ) =>
              x ⟨j, hjA⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_sup_left) using 1
          funext c
          rfl
        · have hjRest : (j : Fin n) ∈ (S \ A).erase b :=
            Finset.mem_erase.mpr ⟨hjb, Finset.mem_sdiff.mpr ⟨hjS, hjA⟩⟩
          have heval : Measurable
              (fun x : ((j : {j // j ∈ (S \ A).erase b}) → ℝ) =>
                x ⟨j, hjRest⟩) := measurable_pi_apply _
          convert heval.comp (Measurable.of_comap_le le_sup_right) using 1
          funext c
          rfl
      exact hm.comap_le
  refine ⟨hsigma, ?_⟩
  rcases hCIpair with ⟨hμ, hXi, hPair, hZA, hCIpair⟩
  refine ⟨hμ, hXi, hU b, hproj _, ?_⟩
  have hraw := Causalean.condIndepFun_weak_union_of_prodMk hZA.comap_le
    (hU i) (hU b) (hproj ((S \ A).erase b)) hCIpair
  simpa only [hsigma] using hraw

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
