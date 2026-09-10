import CausalSmith.Substrate.SemialgebraicCadDefinableChoice.Choice

/-!
# First-nonempty-cell bridge

This module packages the data used by certified-CAD consumers: a cylindrical partition of a
relation, a semialgebraic choice on each cell projection, the least cell meeting each input fiber,
and semialgebraicity of the globally selected graph.  The resulting selected map is measurable
and lies in the original relation.
-/

open Set

namespace CausalSmith.Substrate.SemialgebraicCadDefinableChoice

/-- A coordinate order puts the input block before the output block when every input coordinate
has smaller rank than every output coordinate. -/
def InputsBeforeOutputs {ι κ : Type*} [Fintype ι] [Fintype κ]
    (order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))) : Prop :=
  ∀ input output, (order (.inl input)).1 < (order (.inr output)).1

/-- The input projection of one CAD cell is the set of inputs whose fiber meets that cell. -/
def cellInputDomain {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    (cad : CylindricalPartition order relation) (cell : Fin cad.cellCount) :
    Set (ι → ℝ) :=
  relationDomain (cad.cells cell)

/-- The input projection of every semialgebraic CAD cell is semialgebraic. -/
theorem CylindricalPartition.cellInputDomain_semialgebraic
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    (cad : CylindricalPartition order relation) (cell : Fin cad.cellCount) :
    IsSemialgebraicSet (cellInputDomain cad cell) := by
  let embedding : ι ↪ Sum ι κ := ⟨Sum.inl, Sum.inl_injective⟩
  have hProjection := isSemialgebraicSet_coordinateProjection embedding
    (cad.cellSemialgebraic cell)
  convert hProjection using 1
  ext input
  constructor
  · rintro ⟨output, hPoint⟩
    refine ⟨joinCoordinates input output, hPoint, ?_⟩
    rfl
  · rintro ⟨point, hPoint, hInput⟩
    refine ⟨outputCoordinates point, ?_⟩
    have hCoordinates :
        joinCoordinates (inputCoordinates point) (outputCoordinates point) = point := by
      funext coordinate
      cases coordinate <;> rfl
    have hInput' : inputCoordinates point = input := hInput
    rw [← hInput', hCoordinates]
    exact hPoint

/-- A first-nonempty-cell selector packages within-cell semialgebraic choices and their global
least-cell assembly for a cylindrical partition of a total relation. -/
structure FirstNonemptyCellBridge {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    (cad : CylindricalPartition order relation) where
  /-- A total output-valued choice function associated with every cell. -/
  cellChoice : Fin cad.cellCount → (ι → ℝ) → (κ → ℝ)
  /-- On the projection of a cell, its choice function selects a point of that cell. -/
  cellChoiceInCell : ∀ cell input, input ∈ cellInputDomain cad cell →
    joinCoordinates input (cellChoice cell input) ∈ cad.cells cell
  /-- Each within-cell choice has a semialgebraic graph over the cell projection. -/
  cellChoiceSemialgebraic : ∀ cell,
    IsSemialgebraicMapOn (cellInputDomain cad cell) (cellChoice cell)
  /-- The chosen index is the first cell whose projection contains the input. -/
  firstCell : (ι → ℝ) → Fin cad.cellCount
  /-- Every input belongs to the projection of its chosen cell. -/
  firstCellActive : ∀ input, input ∈ cellInputDomain cad (firstCell input)
  /-- Every cell earlier than the chosen cell has empty fiber at that input. -/
  earlierCellsEmpty : ∀ input cell, cell < firstCell input →
    input ∉ cellInputDomain cad cell
  /-- Assembling the within-cell choices by the first active cell has a semialgebraic graph. -/
  selectedGraphSemialgebraic : IsSemialgebraicMap
    (fun input => cellChoice (firstCell input) input)

namespace FirstNonemptyCellBridge

/-- The selected map evaluates the within-cell choice at the first cell meeting the input fiber. -/
def selector {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    {cad : CylindricalPartition order relation}
    (bridge : FirstNonemptyCellBridge cad) : (ι → ℝ) → (κ → ℝ) :=
  fun input => bridge.cellChoice (bridge.firstCell input) input

/-- The first-nonempty-cell selector belongs to the original relation at every input. -/
theorem selector_mem_relation {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    {cad : CylindricalPartition order relation}
    (bridge : FirstNonemptyCellBridge cad) (input : ι → ℝ) :
    joinCoordinates input (bridge.selector input) ∈ relation := by
  let selectedPoint := joinCoordinates input (bridge.selector input)
  have hCell : selectedPoint ∈ cad.cells (bridge.firstCell input) :=
    bridge.cellChoiceInCell _ _ (bridge.firstCellActive input)
  have hUnion : selectedPoint ∈ ⋃ cell, cad.cells cell :=
    Set.mem_iUnion.2 ⟨bridge.firstCell input, hCell⟩
  exact (congrArg (fun set : Set (Sum ι κ → ℝ) => selectedPoint ∈ set)
    cad.cellsCover).mpr hUnion

/-- The first-nonempty-cell selector has a semialgebraic graph. -/
theorem selector_semialgebraic {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    {cad : CylindricalPartition order relation}
    (bridge : FirstNonemptyCellBridge cad) : IsSemialgebraicMap bridge.selector := by
  exact bridge.selectedGraphSemialgebraic

/-- The first-nonempty-cell selector is Borel measurable. -/
theorem selector_measurable {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    {cad : CylindricalPartition order relation}
    (bridge : FirstNonemptyCellBridge cad) : Measurable bridge.selector := by
  exact bridge.selector_semialgebraic.measurable

end FirstNonemptyCellBridge

/-- Every cylindrical partition of a total semialgebraic relation admits a first-nonempty-cell
bridge with semialgebraic within-cell choices and a semialgebraic global selector graph. -/
theorem exists_firstNonemptyCellBridge
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    {order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ))}
    {relation : Set (Sum ι κ → ℝ)}
    (cad : CylindricalPartition order relation) (hTotal : RelationTotal relation) :
    Nonempty (FirstNonemptyCellBridge cad) := by
  sorry

/-- A total semialgebraic relation admits, along any supplied coordinate order, a finite
cylindrical partition together with a first-nonempty-cell bridge and its certified selector. -/
theorem exists_cad_firstNonemptyCellBridge
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (order : Sum ι κ ≃ Fin (Fintype.card (Sum ι κ)))
    {relation : Set (Sum ι κ → ℝ)} (hRelation : IsSemialgebraicSet relation)
    (hTotal : RelationTotal relation) :
    ∃ cad : CylindricalPartition order relation,
      Nonempty (FirstNonemptyCellBridge cad) := by
  rcases exists_cylindricalPartition order hRelation with ⟨cad⟩
  exact ⟨cad, exists_firstNonemptyCellBridge cad hTotal⟩

end CausalSmith.Substrate.SemialgebraicCadDefinableChoice
