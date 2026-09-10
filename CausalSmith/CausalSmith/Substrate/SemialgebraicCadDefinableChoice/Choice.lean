import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.CAD

/-!
# Semialgebraic definable choice

This module states semialgebraic selection on a semialgebraic domain, specializes it to total
relations, and derives Borel measurability directly from semialgebraicity of the selector graph.
Relations and graphs live in the sum-indexed coordinate space `(Sum ι κ → ℝ)`.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

/-- Combine input and output coordinate vectors into one sum-indexed coordinate vector. -/
def joinCoordinates {ι κ : Type*} (input : ι → ℝ) (output : κ → ℝ) : Sum ι κ → ℝ :=
  Sum.elim input output

/-- Read the input coordinates from a sum-indexed coordinate vector. -/
def inputCoordinates {ι κ : Type*} (point : Sum ι κ → ℝ) : ι → ℝ :=
  fun i => point (.inl i)

/-- Read the output coordinates from a sum-indexed coordinate vector. -/
def outputCoordinates {ι κ : Type*} (point : Sum ι κ → ℝ) : κ → ℝ :=
  fun k => point (.inr k)

/-- The graph of a map restricted to a specified input domain. -/
def graphOn {ι κ : Type*} (domain : Set (ι → ℝ))
    (selector : (ι → ℝ) → (κ → ℝ)) : Set (Sum ι κ → ℝ) :=
  {point | inputCoordinates point ∈ domain ∧
    outputCoordinates point = selector (inputCoordinates point)}

/-- A map is semialgebraic on a domain when its restricted graph is semialgebraic. -/
def IsSemialgebraicMapOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    (domain : Set (ι → ℝ)) (selector : (ι → ℝ) → (κ → ℝ)) : Prop :=
  IsSemialgebraicSet (graphOn domain selector)

/-- A total map between finite real coordinate spaces is semialgebraic when its graph is. -/
def IsSemialgebraicMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (selector : (ι → ℝ) → (κ → ℝ)) : Prop :=
  IsSemialgebraicMapOn Set.univ selector

/-- The set of inputs having a witness in a relation is its projection onto input coordinates. -/
def relationDomain {ι κ : Type*} (relation : Set (Sum ι κ → ℝ)) : Set (ι → ℝ) :=
  {input | ∃ output, joinCoordinates input output ∈ relation}

/-- A relation is total on a domain when every point of that domain has an output witness. -/
def RelationTotalOn {ι κ : Type*} (domain : Set (ι → ℝ))
    (relation : Set (Sum ι κ → ℝ)) : Prop :=
  ∀ input ∈ domain, ∃ output, joinCoordinates input output ∈ relation

/-- A relation is total when every input has an output witness. -/
def RelationTotal {ι κ : Type*} (relation : Set (Sum ι κ → ℝ)) : Prop :=
  RelationTotalOn Set.univ relation

/-- **Semialgebraic definable choice on a domain.** A semialgebraic relation whose fibers are
nonempty over a semialgebraic domain admits a selector with semialgebraic restricted graph. -/
theorem exists_semialgebraic_selectorOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    {domain : Set (ι → ℝ)} {relation : Set (Sum ι κ → ℝ)}
    (hDomain : IsSemialgebraicSet domain) (hRelation : IsSemialgebraicSet relation)
    (hTotal : RelationTotalOn domain relation) :
    ∃ selector : (ι → ℝ) → (κ → ℝ),
      IsSemialgebraicMapOn domain selector ∧
        ∀ input ∈ domain, joinCoordinates input (selector input) ∈ relation := by
  sorry

/-- **Semialgebraic definable choice.** A total semialgebraic relation admits a selector whose
full graph is semialgebraic and whose selected pair belongs to the relation at every input. -/
theorem exists_semialgebraic_selector {ι κ : Type*} [Fintype ι] [Fintype κ]
    {relation : Set (Sum ι κ → ℝ)} (hRelation : IsSemialgebraicSet relation)
    (hTotal : RelationTotal relation) :
    ∃ selector : (ι → ℝ) → (κ → ℝ),
      IsSemialgebraicMap selector ∧
        ∀ input, joinCoordinates input (selector input) ∈ relation := by
  simpa [IsSemialgebraicMap, RelationTotal] using
    exists_semialgebraic_selectorOn (isSemialgebraicSet_univ (ι := ι)) hRelation hTotal

/-- A total map with semialgebraic graph is Borel measurable.  The proof projects the graph
intersected with each rational-open coordinate half-space and then uses the real Borel
generators. -/
theorem IsSemialgebraicMap.measurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    {selector : (ι → ℝ) → (κ → ℝ)}
    (hSelector : IsSemialgebraicMap selector) :
    Measurable selector := by
  rw [measurable_pi_iff]
  intro outputIndex
  apply measurable_of_Iio
  intro threshold
  let inputEmbedding : ι ↪ Sum ι κ := ⟨Sum.inl, Sum.inl_injective⟩
  let halfSpace : Set (Sum ι κ → ℝ) :=
    {point | outputCoordinates point outputIndex < threshold}
  have hHalfSpace : IsSemialgebraicSet halfSpace := by
    let condition : PolynomialSignCondition (Sum ι κ) :=
      { polynomial := MvPolynomial.C threshold - MvPolynomial.X (.inr outputIndex)
        sign := .positive }
    convert isSemialgebraicSet_signCondition condition using 1
    ext point
    simp [halfSpace, condition, outputCoordinates, PolynomialSignCondition.Holds,
      PolynomialSign.Holds]
  have hProjected : IsSemialgebraicSet
      (coordinateProjection inputEmbedding '' (graphOn Set.univ selector ∩ halfSpace)) := by
    apply isSemialgebraicSet_coordinateProjection inputEmbedding
    exact hSelector.inter hHalfSpace
  have hPreimage :
      (fun input => selector input outputIndex) ⁻¹' Iio threshold =
        coordinateProjection inputEmbedding '' (graphOn Set.univ selector ∩ halfSpace) := by
    ext input
    constructor
    · intro hInput
      refine ⟨joinCoordinates input (selector input), ?_, ?_⟩
      · constructor
        · exact ⟨Set.mem_univ _, by
            ext outputCoordinate
            rfl⟩
        · exact hInput
      · rfl
    · rintro ⟨point, ⟨hGraph, hHalf⟩, hPoint⟩
      have hInput : inputCoordinates point = input := by
        exact hPoint
      change selector input outputIndex < threshold
      rw [← hInput, ← hGraph.2]
      exact hHalf
  rw [hPreimage]
  exact hProjected.measurableSet

/-- A total semialgebraic relation admits a Borel measurable selector that stays in every fiber. -/
theorem exists_measurable_semialgebraic_selector {ι κ : Type*} [Fintype ι] [Fintype κ]
    {relation : Set (Sum ι κ → ℝ)} (hRelation : IsSemialgebraicSet relation)
    (hTotal : RelationTotal relation) :
    ∃ selector : (ι → ℝ) → (κ → ℝ),
      IsSemialgebraicMap selector ∧ Measurable selector ∧
        ∀ input, joinCoordinates input (selector input) ∈ relation := by
  rcases exists_semialgebraic_selector hRelation hTotal with ⟨selector, hGraph, hSelects⟩
  exact ⟨selector, hGraph, hGraph.measurable, hSelects⟩

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
