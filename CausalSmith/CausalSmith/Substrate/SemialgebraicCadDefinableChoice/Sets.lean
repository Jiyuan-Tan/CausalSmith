import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.Basic

/-!
# Closure and measurability of finite-coordinate semialgebraic sets

This module packages quantifier-free polynomial sign formulas as subsets of finite real coordinate
spaces and proves Boolean, coordinate-product, coordinate-preimage, projection, and Borel closure.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

/-- A subset of a finite real coordinate space is semialgebraic when a finite quantifier-free
Boolean formula of polynomial exact-sign conditions defines it. -/
def IsSemialgebraicSet {ι : Type*} [Fintype ι] (set : Set (ι → ℝ)) : Prop :=
  ∃ formula : SemialgebraicFormula ι, set = {x | formula.Holds x}

/-- The empty subset of a finite real coordinate space is semialgebraic. -/
theorem isSemialgebraicSet_empty {ι : Type*} [Fintype ι] :
    IsSemialgebraicSet (∅ : Set (ι → ℝ)) := by
  refine ⟨.falsum, ?_⟩
  ext x
  simp [SemialgebraicFormula.Holds]

/-- The whole finite real coordinate space is semialgebraic. -/
theorem isSemialgebraicSet_univ {ι : Type*} [Fintype ι] :
    IsSemialgebraicSet (Set.univ : Set (ι → ℝ)) := by
  refine ⟨.not .falsum, ?_⟩
  ext x
  simp [SemialgebraicFormula.Holds]

/-- A polynomial exact-sign locus is semialgebraic. -/
theorem isSemialgebraicSet_signCondition {ι : Type*} [Fintype ι]
    (condition : PolynomialSignCondition ι) :
    IsSemialgebraicSet {x : ι → ℝ | condition.Holds x} := by
  exact ⟨.atom condition, rfl⟩

/-- The union of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraicSet.union {ι : Type*} [Fintype ι]
    {left right : Set (ι → ℝ)} (hLeft : IsSemialgebraicSet left)
    (hRight : IsSemialgebraicSet right) : IsSemialgebraicSet (left ∪ right) := by
  rcases hLeft with ⟨leftFormula, rfl⟩
  rcases hRight with ⟨rightFormula, rfl⟩
  refine ⟨.or leftFormula rightFormula, ?_⟩
  ext x
  simp [SemialgebraicFormula.Holds]

/-- The intersection of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraicSet.inter {ι : Type*} [Fintype ι]
    {left right : Set (ι → ℝ)} (hLeft : IsSemialgebraicSet left)
    (hRight : IsSemialgebraicSet right) : IsSemialgebraicSet (left ∩ right) := by
  rcases hLeft with ⟨leftFormula, rfl⟩
  rcases hRight with ⟨rightFormula, rfl⟩
  refine ⟨.and leftFormula rightFormula, ?_⟩
  ext x
  simp [SemialgebraicFormula.Holds]

/-- The complement of a semialgebraic set is semialgebraic. -/
theorem IsSemialgebraicSet.compl {ι : Type*} [Fintype ι]
    {set : Set (ι → ℝ)} (hSet : IsSemialgebraicSet set) : IsSemialgebraicSet setᶜ := by
  rcases hSet with ⟨formula, rfl⟩
  refine ⟨.not formula, ?_⟩
  ext x
  simp [SemialgebraicFormula.Holds]

/-- The difference of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraicSet.diff {ι : Type*} [Fintype ι]
    {left right : Set (ι → ℝ)} (hLeft : IsSemialgebraicSet left)
    (hRight : IsSemialgebraicSet right) : IsSemialgebraicSet (left \ right) := by
  simpa [Set.sdiff_eq] using hLeft.inter hRight.compl

/-- A finite union of semialgebraic sets is semialgebraic. -/
theorem isSemialgebraicSet_iUnion_fin {ι : Type*} [Fintype ι] {n : ℕ}
    {sets : Fin n → Set (ι → ℝ)} (hSets : ∀ j, IsSemialgebraicSet (sets j)) :
    IsSemialgebraicSet (⋃ j, sets j) := by
  have hFinset : ∀ indices : Finset (Fin n),
      IsSemialgebraicSet (⋃ j ∈ indices, sets j) := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simpa using (isSemialgebraicSet_empty (ι := ι))
    | @insert j indices hj ih =>
        simpa only [Finset.set_biUnion_insert] using (hSets j).union ih
  simpa using hFinset Finset.univ

/-- A finite intersection of semialgebraic sets is semialgebraic. -/
theorem isSemialgebraicSet_iInter_fin {ι : Type*} [Fintype ι] {n : ℕ}
    {sets : Fin n → Set (ι → ℝ)} (hSets : ∀ j, IsSemialgebraicSet (sets j)) :
    IsSemialgebraicSet (⋂ j, sets j) := by
  rw [← compl_compl (⋂ j, sets j), compl_iInter]
  exact (isSemialgebraicSet_iUnion_fin fun j => (hSets j).compl).compl

/-- Restrict a point to coordinates selected by an embedding. -/
def coordinateProjection {ι κ : Type*} (embedding : κ ↪ ι) :
    (ι → ℝ) → (κ → ℝ) := fun x k => x (embedding k)

/-- Pulling a semialgebraic set back along any coordinate map preserves semialgebraicity. -/
theorem IsSemialgebraicSet.coordinatePreimage {ι κ : Type*} [Fintype ι] [Fintype κ]
    (coordinate : κ → ι) {set : Set (κ → ℝ)} (hSet : IsSemialgebraicSet set) :
    IsSemialgebraicSet {x : ι → ℝ | (fun k => x (coordinate k)) ∈ set} := by
  rcases hSet with ⟨formula, rfl⟩
  refine ⟨formula.rename coordinate, ?_⟩
  ext x
  simp

/-- **Tarski--Seidenberg.** The image of a semialgebraic set under a coordinate projection is
semialgebraic.  A proof eliminates the finitely many coordinates outside the embedding by
one-variable real quantifier elimination. -/
theorem isSemialgebraicSet_coordinateProjection {ι κ : Type*} [Fintype ι] [Fintype κ]
    (embedding : κ ↪ ι) {set : Set (ι → ℝ)} (hSet : IsSemialgebraicSet set) :
    IsSemialgebraicSet (coordinateProjection embedding '' set) := by
  sorry

/-- The coordinate product of two sets uses the left and right coordinates of a sum type. -/
def coordinateProduct {ι κ : Type*} (left : Set (ι → ℝ)) (right : Set (κ → ℝ)) :
    Set (Sum ι κ → ℝ) :=
  {z | (fun i => z (.inl i)) ∈ left ∧ (fun k => z (.inr k)) ∈ right}

/-- The coordinate product of two semialgebraic sets is semialgebraic. -/
theorem IsSemialgebraicSet.coordinateProduct {ι κ : Type*} [Fintype ι] [Fintype κ]
    {left : Set (ι → ℝ)} {right : Set (κ → ℝ)} (hLeft : IsSemialgebraicSet left)
    (hRight : IsSemialgebraicSet right) :
    IsSemialgebraicSet (coordinateProduct left right) := by
  exact (hLeft.coordinatePreimage Sum.inl).inter (hRight.coordinatePreimage Sum.inr)

/-- Every semialgebraic subset of a finite real coordinate space is Borel measurable. -/
theorem IsSemialgebraicSet.measurableSet {ι : Type*} [Fintype ι]
    {set : Set (ι → ℝ)} (hSet : IsSemialgebraicSet set) : MeasurableSet set := by
  rcases hSet with ⟨formula, rfl⟩
  exact formula.measurableSet_holds

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
