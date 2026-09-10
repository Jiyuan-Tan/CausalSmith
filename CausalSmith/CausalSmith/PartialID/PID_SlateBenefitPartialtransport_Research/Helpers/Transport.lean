import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Exact-mass partial transport

The finite capacity polytopes, strict-benefit objective, and total endpoint-flow
selectors used by the sharpness and complexity statements.
-/

open scoped BigOperators Matrix
open Set MeasureTheory Causalean PO

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

noncomputable section

universe uV uVal uOmega

-- @env: S2
variable {𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] [MeasurableSpace 𝒳]
  [MeasurableSingletonClass 𝒳]
variable {K : ℕ}

/-- The coupling is the object specified here for the slate-benefit partial-transport construction. -/
abbrev Coupling (K : ℕ) := Matrix (Fin K) (Fin K) ℝ
  -- @realizes \gamma_x(nonnegative K by K survivor-complier subcoupling)

/-- The matrix nonnegative condition is the stated property of the slate-benefit partial-transport model. -/
def matrixNonnegative (γ : Coupling K) : Prop := ∀ i j, 0 ≤ γ i j

/-- The row mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def rowMass (γ : Coupling K) (i : Fin K) : ℝ := ∑ j, γ i j
/-- The column mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def columnMass (γ : Coupling K) (j : Fin K) : ℝ := ∑ i, γ i j
/-- The total mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def totalMass (γ : Coupling K) : ℝ := ∑ i, ∑ j, γ i j

/-- A partial transport polytopes records the data and compatibility conditions used by the slate-benefit partial-transport construction. -/
structure PartialTransportPolytopes (K : ℕ) where
  gammaStar : Set (Coupling K)
  gammaPlus : Set (Coupling K)
  gammaMinus : Set (Coupling K)
  gammaZero : Set (Coupling K)

/-- The reusable four-polytope family: branch-free exact mass, exact rows,
exact columns, and the doubly-exact tie face. -/
def exactMassPolytope (c : Capacities 𝒳 K) (_hValid : ValidCapacities c)
    (x : 𝒳) : PartialTransportPolytopes K where
  gammaStar :=
    {γ | matrixNonnegative γ ∧
      (∀ i, rowMass γ i ≤ c.lower x i) ∧
      (∀ j, columnMass γ j ≤ c.upper x j) ∧
      totalMass γ = c.mass x}
  gammaPlus :=
    {γ | matrixNonnegative γ ∧
      (∀ i, rowMass γ i = c.lower x i) ∧
      (∀ j, columnMass γ j ≤ c.upper x j)}
  gammaMinus :=
    {γ | matrixNonnegative γ ∧
      (∀ i, rowMass γ i ≤ c.lower x i) ∧
      (∀ j, columnMass γ j = c.upper x j)}
  gammaZero :=
    {γ | matrixNonnegative γ ∧
      (∀ i, rowMass γ i = c.lower x i) ∧
      (∀ j, columnMass γ j = c.upper x j)}

/-- The complete four-polytope family on the paper's observed-law domain. -/
-- @node: def:partial-transport-polytope
def paperExactMassPolytope (Pobs : Measure (ObservedDatum 𝒳 K))
    (_hK : 3 ≤ K) (_hDomain : ObservedLawDomain Pobs)
    (c : Capacities 𝒳 K) (_hc : c = observableCapacities Pobs)
    (_hCompatible : CompatibleObservedLaw Pobs)
    (hValid : ValidCapacities c) (x : 𝒳) : PartialTransportPolytopes K :=
  exactMassPolytope c hValid x

/-- The branch free polytope is the event specified by the stated potential-outcome conditions. -/
def branchFreePolytope (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Set (Coupling K) :=
  (exactMassPolytope c hValid x).gammaStar
  -- @realizes \Gamma_x^{\ast}(capacity inequalities and exact mass)
  -- @realizes \Gamma_x(branch-free definition equal to Gamma-star)

/-- The inc polytope is the event specified by the stated potential-outcome conditions. -/
def incPolytope (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Set (Coupling K) :=
  (exactMassPolytope c hValid x).gammaPlus
  -- @realizes \Gamma_x^{+}(exact rows and bounded columns)

/-- The dec polytope is the event specified by the stated potential-outcome conditions. -/
def decPolytope (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Set (Coupling K) :=
  (exactMassPolytope c hValid x).gammaMinus
  -- @realizes \Gamma_x^{-}(bounded rows and exact columns)

/-- The tie polytope is the event specified by the stated potential-outcome conditions. -/
def tiePolytope (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Set (Coupling K) :=
  (exactMassPolytope c hValid x).gammaZero
  -- @realizes \Gamma_x^{0}(both margins exact)

/-- The benefit mass is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def benefitMass (γ : Coupling K) : ℝ :=
  ∑ i, ∑ j with i < j, γ i j
  -- @realizes b_x(\gamma_x)(strict-benefit mass sum over i less than j)

/-- The positive support card is the object specified here for the slate-benefit partial-transport construction. -/
noncomputable def positiveSupportCard (γ : Coupling K) : ℕ :=
  ((Finset.univ.product Finset.univ).filter fun ij => 0 < γ ij.1 ij.2).card

/-- One positive sparse allocation, represented by its row, column, and mass. -/
abbrev Allocation (K : ℕ) := Fin K × Fin K × ℝ

private def indexedMasses (f : Fin K → ℝ) : List (Fin K × ℝ) :=
  (List.finRange K).map fun i => (i, f i)

/-- A sparse nested-graph pass returns both its emitted allocations and the
unconsumed row and column capacities. Carrying the residuals through the pass
avoids a later quadratic family of residual folds. -/
private structure SparsePassResult (K : ℕ) where
  allocations : List (Allocation K)
  rowResiduals : List (Fin K × ℝ)
  columnResiduals : List (Fin K × ℝ)

/-- Descending two-pointer pass on the nested graph `i < j`. The largest
remaining row is matched to the largest column when eligible. If `j ≤ i`, that
row is retained as a residual and discarded from the benefit scan, since no
later (smaller) column can use it. -/
private def maxBenefitPass :
    List (Fin K × ℝ) → List (Fin K × ℝ) → SparsePassResult K
  | [], columns => ⟨[], [], columns⟩
  | rows, [] => ⟨[], rows, []⟩
  | (i, a) :: rows, (j, b) :: columns =>
      if i < j then
        if a ≤ b then
          let out := maxBenefitPass rows ((j, b - min a b) :: columns)
          { out with allocations := (i, j, min a b) :: out.allocations }
        else
          let out := maxBenefitPass ((i, a - min a b) :: rows) columns
          { out with allocations := (i, j, min a b) :: out.allocations }
      else
        let out := maxBenefitPass rows ((j, b) :: columns)
        { out with rowResiduals := (i, a) :: out.rowResiduals }
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

/-- Ascending two-pointer pass on the nested nonbenefit graph `j ≤ i`.  A
row skipped because `i < j` is retained for the complete residual pass. -/
private def maxNonBenefitPass :
    List (Fin K × ℝ) → List (Fin K × ℝ) → SparsePassResult K
  | [], columns => ⟨[], [], columns⟩
  | rows, [] => ⟨[], rows, []⟩
  | (i, a) :: rows, (j, b) :: columns =>
      if j ≤ i then
        if a ≤ b then
          let out := maxNonBenefitPass rows ((j, b - min a b) :: columns)
          { out with allocations := (i, j, min a b) :: out.allocations }
        else
          let out := maxNonBenefitPass ((i, a - min a b) :: rows) columns
          { out with allocations := (i, j, min a b) :: out.allocations }
      else
        let out := maxNonBenefitPass rows ((j, b) :: columns)
        { out with rowResiduals := (i, a) :: out.rowResiduals }
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

private def maxBenefitSparse (rows columns : List (Fin K × ℝ)) : List (Allocation K) :=
  (maxBenefitPass rows columns).allocations

private def maxNonBenefitSparse (rows columns : List (Fin K × ℝ)) : List (Allocation K) :=
  (maxNonBenefitPass rows columns).allocations

/-- Ordinary two-pointer transport on the residual complete bipartite graph. -/
private def completeSparse :
    List (Fin K × ℝ) → List (Fin K × ℝ) → List (Allocation K)
  | [], _ => []
  | _, [] => []
  | (i, a) :: rows, (j, b) :: columns =>
      if a ≤ b then
        (i, j, min a b) :: completeSparse rows ((j, b - min a b) :: columns)
      else
        (i, j, min a b) :: completeSparse ((i, a - min a b) :: rows) columns
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

private def completePrimary (primary : SparsePassResult K) : List (Allocation K) :=
  primary.allocations ++ completeSparse primary.rowResiduals primary.columnResiduals

private def sparseMatrix (a : List (Allocation K)) : Coupling K :=
  fun i j => a.foldl
    (fun total e => if e.1 = i ∧ e.2.1 = j then total + e.2.2 else total) 0

/-- A sparse allocation list with nonnegative emitted masses materializes to a
nonnegative matrix.  This isolates the common sign argument from the two
greedy-pass invariants below. -/
private theorem sparseMatrix_nonnegative (a : List (Allocation K))
    (ha : ∀ e ∈ a, 0 ≤ e.2.2) :
    matrixNonnegative (sparseMatrix a) := by
  intro i j
  unfold sparseMatrix
  have fold_nonnegative :
      ∀ (entries : List (Allocation K)) (total : ℝ),
        0 ≤ total → (∀ e ∈ entries, 0 ≤ e.2.2) →
          0 ≤ entries.foldl
            (fun acc e => if e.1 = i ∧ e.2.1 = j then acc + e.2.2 else acc) total := by
    intro entries
    induction entries with
    | nil => simp
    | cons e entries ih =>
        intro total htotal hentries
        apply ih
        · dsimp
          split_ifs
          · exact add_nonneg htotal (hentries e (by simp))
          · exact htotal
        · intro e' he'
          exact hentries e' (by simp [he'])
  exact fold_nonnegative a 0 (le_refl 0) ha

/-- Every allocation emitted by the descending benefit pass has nonnegative
mass when its input residual capacities are nonnegative. -/
private theorem maxBenefitPass_allocations_nonnegative
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    ∀ e ∈ (maxBenefitPass rows columns).allocations, 0 ≤ e.2.2 := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all [maxBenefitPass] <;> grind

/-- Every allocation emitted by the ascending nonbenefit pass has nonnegative
mass when its input residual capacities are nonnegative. -/
private theorem maxNonBenefitPass_allocations_nonnegative
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    ∀ e ∈ (maxNonBenefitPass rows columns).allocations, 0 ≤ e.2.2 := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all [maxNonBenefitPass] <;> grind

/-- Both residual lists of the descending benefit pass remain nonnegative. -/
private theorem maxBenefitPass_residuals_nonnegative
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    (∀ e ∈ (maxBenefitPass rows columns).rowResiduals, 0 ≤ e.2) ∧
      ∀ e ∈ (maxBenefitPass rows columns).columnResiduals, 0 ≤ e.2 := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all [maxBenefitPass] <;> grind

/-- Both residual lists of the ascending nonbenefit pass remain nonnegative. -/
private theorem maxNonBenefitPass_residuals_nonnegative
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    (∀ e ∈ (maxNonBenefitPass rows columns).rowResiduals, 0 ≤ e.2) ∧
      ∀ e ∈ (maxNonBenefitPass rows columns).columnResiduals, 0 ≤ e.2 := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all [maxNonBenefitPass] <;> grind

/-- Ordinary residual transport emits only nonnegative masses. -/
private theorem completeSparse_allocations_nonnegative
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    ∀ e ∈ completeSparse rows columns, 0 ≤ e.2.2 := by
  induction rows, columns using completeSparse.induct <;>
    simp_all [completeSparse] <;> grind

/-- Completing either greedy pass preserves nonnegativity of all emitted
allocations. -/
private theorem completePrimary_allocations_nonnegative (primary : SparsePassResult K)
    (halloc : ∀ e ∈ primary.allocations, 0 ≤ e.2.2)
    (hrows : ∀ e ∈ primary.rowResiduals, 0 ≤ e.2)
    (hcolumns : ∀ e ∈ primary.columnResiduals, 0 ≤ e.2) :
    ∀ e ∈ completePrimary primary, 0 ≤ e.2.2 := by
  intro e he
  rw [completePrimary, List.mem_append] at he
  rcases he with he | he
  · exact halloc e he
  · exact completeSparse_allocations_nonnegative _ _ hrows hcolumns e he

private def rowCapacityOf (rows : List (Fin K × ℝ)) (i : Fin K) : ℝ :=
  (rows.map fun e => if e.1 = i then e.2 else 0).sum

private def columnCapacityOf (columns : List (Fin K × ℝ)) (j : Fin K) : ℝ :=
  (columns.map fun e => if e.1 = j then e.2 else 0).sum

/-- Summing row capacities over an index predicate equals filtering the
capacity list by that predicate. -/
private theorem rowCapacityOf_sum_filter (rows : List (Fin K × ℝ))
    (p : Fin K → Prop) [DecidablePred p] :
    (∑ i with p i, rowCapacityOf rows i) =
      (rows.map fun e => if p e.1 then e.2 else 0).sum := by
  classical
  induction rows with
  | nil => simp [rowCapacityOf]
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      simp [rowCapacityOf, Finset.sum_add_distrib]

/-- Summing column capacities over an index predicate equals filtering the
capacity list by that predicate. -/
private theorem columnCapacityOf_sum_filter (columns : List (Fin K × ℝ))
    (p : Fin K → Prop) [DecidablePred p] :
    (∑ j with p j, columnCapacityOf columns j) =
      (columns.map fun e => if p e.1 then e.2 else 0).sum := by
  exact rowCapacityOf_sum_filter columns p

/-- A filtered row-capacity sum vanishes when every listed residual index is
outside the filter. -/
private theorem rowCapacityOf_sum_filter_eq_zero
    (rows : List (Fin K × ℝ)) (p : Fin K → Prop) [DecidablePred p]
    (hrows : ∀ r ∈ rows, ¬ p r.1) :
    (∑ i with p i, rowCapacityOf rows i) = 0 := by
  rw [rowCapacityOf_sum_filter]
  induction rows with
  | nil => simp
  | cons r rows ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hrows
      simp [hrows.1, ih hrows.2]

/-- A filtered column-capacity sum vanishes when every listed residual index
is outside the filter. -/
private theorem columnCapacityOf_sum_filter_eq_zero
    (columns : List (Fin K × ℝ)) (p : Fin K → Prop) [DecidablePred p]
    (hcolumns : ∀ c ∈ columns, ¬ p c.1) :
    (∑ j with p j, columnCapacityOf columns j) = 0 := by
  rw [columnCapacityOf_sum_filter]
  induction columns with
  | nil => simp
  | cons c columns ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hcolumns
      simp [hcolumns.1, ih hcolumns.2]

private def allocationRowMass (a : List (Allocation K)) (i : Fin K) : ℝ :=
  (a.map fun e => if e.1 = i then e.2.2 else 0).sum

private def allocationColumnMass (a : List (Allocation K)) (j : Fin K) : ℝ :=
  (a.map fun e => if e.2.1 = j then e.2.2 else 0).sum

private def allocationTotalMass (a : List (Allocation K)) : ℝ :=
  (a.map fun e => e.2.2).sum

private def allocationBenefitMass (a : List (Allocation K)) : ℝ :=
  (a.map fun e => if e.1 < e.2.1 then e.2.2 else 0).sum

/-- Summing row masses over an index predicate equals filtering the allocation
list by that predicate on row indices. -/
private theorem allocationRowMass_sum_filter (a : List (Allocation K))
    (p : Fin K → Prop) [DecidablePred p] :
    (∑ i with p i, allocationRowMass a i) =
      (a.map fun e => if p e.1 then e.2.2 else 0).sum := by
  classical
  induction a with
  | nil => simp [allocationRowMass]
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      simp [allocationRowMass, Finset.sum_add_distrib]

/-- Summing column masses over an index predicate equals filtering the
allocation list by that predicate on column indices. -/
private theorem allocationColumnMass_sum_filter (a : List (Allocation K))
    (p : Fin K → Prop) [DecidablePred p] :
    (∑ j with p j, allocationColumnMass a j) =
      (a.map fun e => if p e.2.1 then e.2.2 else 0).sum := by
  classical
  induction a with
  | nil => simp [allocationColumnMass]
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      simp [allocationColumnMass, Finset.sum_add_distrib]

/-- A nonbenefit allocation list that does not cross an ascending threshold
is partitioned exactly between rows above the threshold and columns at or
below it. -/
private theorem allocationTotalMass_eq_ascending_cut
    (a : List (Allocation K)) (t : Fin K)
    (heligible : ∀ e ∈ a, ¬ e.1 < e.2.1)
    (hnoncrossing : ∀ e ∈ a, ¬ (t < e.1 ∧ e.2.1 ≤ t)) :
    allocationTotalMass a =
      (∑ i with t < i, allocationRowMass a i) +
        ∑ j with j ≤ t, allocationColumnMass a j := by
  rw [allocationRowMass_sum_filter, allocationColumnMass_sum_filter]
  induction a with
  | nil => simp [allocationTotalMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at heligible hnoncrossing
      have ih' := ih heligible.2 hnoncrossing.2
      unfold allocationTotalMass at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih']
      by_cases hrow : t < e.1
      · have hcolumn : ¬ e.2.1 ≤ t := by
          intro h
          exact hnoncrossing.1 ⟨hrow, h⟩
        simp [hrow, hcolumn]
        ring
      · have hrowLe : e.1 ≤ t := le_of_not_gt hrow
        have hcolumn : e.2.1 ≤ t :=
          le_trans (le_of_not_gt heligible.1) hrowLe
        simp [hrow, hcolumn]
        ring

/-- A benefit allocation list that does not cross a descending threshold is
partitioned exactly between rows below the threshold and columns above it. -/
private theorem allocationTotalMass_eq_descending_cut
    (a : List (Allocation K)) (t : Fin K)
    (heligible : ∀ e ∈ a, e.1 < e.2.1)
    (hnoncrossing : ∀ e ∈ a, ¬ (e.1 < t ∧ t < e.2.1)) :
    allocationTotalMass a =
      (∑ i with i < t, allocationRowMass a i) +
        ∑ j with t < j, allocationColumnMass a j := by
  rw [allocationRowMass_sum_filter, allocationColumnMass_sum_filter]
  induction a with
  | nil => simp [allocationTotalMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at heligible hnoncrossing
      have ih' := ih heligible.2 hnoncrossing.2
      unfold allocationTotalMass at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      rw [ih']
      by_cases hrow : e.1 < t
      · have hcolumn : ¬ t < e.2.1 := by
          intro h
          exact hnoncrossing.1 ⟨hrow, h⟩
        simp [hrow, hcolumn]
        ring
      · have htrow : t ≤ e.1 := le_of_not_gt hrow
        have hcolumn : t < e.2.1 := lt_of_le_of_lt htrow heligible.1
        simp [hrow, hcolumn]
        ring

/-- Nonnegative nonbenefit allocations are bounded by every ascending
row-above/column-below cut. -/
private theorem allocationTotalMass_le_ascending_cut
    (a : List (Allocation K)) (t : Fin K)
    (hnonnegative : ∀ e ∈ a, 0 ≤ e.2.2)
    (heligible : ∀ e ∈ a, ¬ e.1 < e.2.1) :
    allocationTotalMass a ≤
      (∑ i with t < i, allocationRowMass a i) +
        ∑ j with j ≤ t, allocationColumnMass a j := by
  rw [allocationRowMass_sum_filter, allocationColumnMass_sum_filter]
  induction a with
  | nil => simp [allocationTotalMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hnonnegative heligible
      have ih' := ih hnonnegative.2 heligible.2
      unfold allocationTotalMass at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      by_cases hrow : t < e.1
      · simp [hrow]
        split_ifs <;> linarith
      · have hcolumn : e.2.1 ≤ t :=
          le_trans (le_of_not_gt heligible.1) (le_of_not_gt hrow)
        simp [hrow, hcolumn]
        linarith

/-- Nonnegative benefit allocations are bounded by every descending
row-below/column-above cut. -/
private theorem allocationTotalMass_le_descending_cut
    (a : List (Allocation K)) (t : Fin K)
    (hnonnegative : ∀ e ∈ a, 0 ≤ e.2.2)
    (heligible : ∀ e ∈ a, e.1 < e.2.1) :
    allocationTotalMass a ≤
      (∑ i with i < t, allocationRowMass a i) +
        ∑ j with t < j, allocationColumnMass a j := by
  rw [allocationRowMass_sum_filter, allocationColumnMass_sum_filter]
  induction a with
  | nil => simp [allocationTotalMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hnonnegative heligible
      have ih' := ih hnonnegative.2 heligible.2
      unfold allocationTotalMass at ih' ⊢
      simp only [List.map_cons, List.sum_cons]
      by_cases hrow : e.1 < t
      · simp [hrow]
        split_ifs <;> linarith
      · have hcolumn : t < e.2.1 :=
          lt_of_le_of_lt (le_of_not_gt hrow) heligible.1
        simp [hrow, hcolumn]
        linarith

/-- A nonempty finite residual-row list has a maximal-index cut boundary;
cross-residual separation and allocation non-crossing transfer to that cut. -/
private theorem ascendingCutBoundary_exists
    (rows columns : List (Fin K × ℝ)) (a : List (Allocation K))
    (hsep : ∀ r ∈ rows, ∀ c ∈ columns, r.1 < c.1)
    (hnoncrossing : ∀ r ∈ rows, ∀ e ∈ a,
      ¬ (r.1 < e.1 ∧ e.2.1 ≤ r.1)) :
    rows = [] ∨ ∃ t : Fin K,
      (∀ r ∈ rows, r.1 ≤ t) ∧
      (∀ c ∈ columns, t < c.1) ∧
      (∀ e ∈ a, ¬ (t < e.1 ∧ e.2.1 ≤ t)) := by
  classical
  by_cases hrows : rows = []
  · exact Or.inl hrows
  · right
    obtain ⟨rFirst, hrFirst⟩ := List.exists_mem_of_ne_nil rows hrows
    have hrowsNonempty : rows.toFinset.Nonempty := by
      exact ⟨rFirst, by simpa using hrFirst⟩
    let indices := rows.toFinset.image Prod.fst
    have hindices : indices.Nonempty := hrowsNonempty.image _
    let t := indices.max' hindices
    have htmem : t ∈ indices := Finset.max'_mem _ _
    obtain ⟨r0, hr0, hr0eq⟩ := Finset.mem_image.mp htmem
    refine ⟨t, ?_, ?_, ?_⟩
    · intro r hr
      apply Finset.le_max' indices r.1
      exact Finset.mem_image.mpr ⟨r, by simpa using hr, rfl⟩
    · intro c hc
      have hr0List : r0 ∈ rows := by simpa using hr0
      simpa [t, hr0eq] using hsep r0 hr0List c hc
    · intro e he
      have hr0List : r0 ∈ rows := by simpa using hr0
      simpa [t, hr0eq] using hnoncrossing r0 hr0List e he

/-- A nonempty finite residual-row list has a minimal-index cut boundary;
descending separation and allocation non-crossing transfer to that cut. -/
private theorem descendingCutBoundary_exists
    (rows columns : List (Fin K × ℝ)) (a : List (Allocation K))
    (hsep : ∀ r ∈ rows, ∀ c ∈ columns, c.1 ≤ r.1)
    (hnoncrossing : ∀ r ∈ rows, ∀ e ∈ a,
      ¬ (e.1 < r.1 ∧ r.1 < e.2.1)) :
    rows = [] ∨ ∃ t : Fin K,
      (∀ r ∈ rows, t ≤ r.1) ∧
      (∀ c ∈ columns, c.1 ≤ t) ∧
      (∀ e ∈ a, ¬ (e.1 < t ∧ t < e.2.1)) := by
  classical
  by_cases hrows : rows = []
  · exact Or.inl hrows
  · right
    obtain ⟨rFirst, hrFirst⟩ := List.exists_mem_of_ne_nil rows hrows
    have hrowsNonempty : rows.toFinset.Nonempty := by
      exact ⟨rFirst, by simpa using hrFirst⟩
    let indices := rows.toFinset.image Prod.fst
    have hindices : indices.Nonempty := hrowsNonempty.image _
    let t := indices.min' hindices
    have htmem : t ∈ indices := Finset.min'_mem _ _
    obtain ⟨r0, hr0, hr0eq⟩ := Finset.mem_image.mp htmem
    refine ⟨t, ?_, ?_, ?_⟩
    · intro r hr
      apply Finset.min'_le indices r.1
      exact Finset.mem_image.mpr ⟨r, by simpa using hr, rfl⟩
    · intro c hc
      have hr0List : r0 ∈ rows := by simpa using hr0
      simpa [t, hr0eq] using hsep r0 hr0List c hc
    · intro e he
      have hr0List : r0 ∈ rows := by simpa using hr0
      simpa [t, hr0eq] using hnoncrossing r0 hr0List e he

/-- At an ascending residual boundary, pointwise conservation and
non-crossing make the corresponding nonbenefit cut exactly saturated. -/
private theorem allocationTotalMass_eq_ascending_input_cut
    (a : List (Allocation K)) (rowResiduals columnResiduals : List (Fin K × ℝ))
    (inputRows inputColumns : List (Fin K × ℝ)) (t : Fin K)
    (hrow : ∀ i, allocationRowMass a i + rowCapacityOf rowResiduals i =
      rowCapacityOf inputRows i)
    (hcolumn : ∀ j, allocationColumnMass a j +
      columnCapacityOf columnResiduals j = columnCapacityOf inputColumns j)
    (heligible : ∀ e ∈ a, ¬ e.1 < e.2.1)
    (hnoncrossing : ∀ e ∈ a, ¬ (t < e.1 ∧ e.2.1 ≤ t))
    (hrows : ∀ r ∈ rowResiduals, r.1 ≤ t)
    (hcolumns : ∀ c ∈ columnResiduals, t < c.1) :
    allocationTotalMass a =
      (∑ i with t < i, rowCapacityOf inputRows i) +
        ∑ j with j ≤ t, columnCapacityOf inputColumns j := by
  have hrowZero : (∑ i with t < i, rowCapacityOf rowResiduals i) = 0 := by
    apply rowCapacityOf_sum_filter_eq_zero
    intro r hr htr
    exact (not_lt_of_ge (hrows r hr)) htr
  have hcolumnZero :
      (∑ j with j ≤ t, columnCapacityOf columnResiduals j) = 0 := by
    apply columnCapacityOf_sum_filter_eq_zero
    intro c hc hct
    exact (not_le_of_gt (hcolumns c hc)) hct
  have hrowSum :
      (∑ i with t < i, (allocationRowMass a i + rowCapacityOf rowResiduals i)) =
        ∑ i with t < i, rowCapacityOf inputRows i :=
    Finset.sum_congr rfl fun i _ => hrow i
  have hcolumnSum :
      (∑ j with j ≤ t, (allocationColumnMass a j +
        columnCapacityOf columnResiduals j)) =
        ∑ j with j ≤ t, columnCapacityOf inputColumns j :=
    Finset.sum_congr rfl fun j _ => hcolumn j
  rw [Finset.sum_add_distrib] at hrowSum hcolumnSum
  rw [hrowZero, add_zero] at hrowSum
  rw [hcolumnZero, add_zero] at hcolumnSum
  rw [allocationTotalMass_eq_ascending_cut a t heligible hnoncrossing,
    hrowSum, hcolumnSum]

/-- At a descending residual boundary, pointwise conservation and
non-crossing make the corresponding benefit cut exactly saturated. -/
private theorem allocationTotalMass_eq_descending_input_cut
    (a : List (Allocation K)) (rowResiduals columnResiduals : List (Fin K × ℝ))
    (inputRows inputColumns : List (Fin K × ℝ)) (t : Fin K)
    (hrow : ∀ i, allocationRowMass a i + rowCapacityOf rowResiduals i =
      rowCapacityOf inputRows i)
    (hcolumn : ∀ j, allocationColumnMass a j +
      columnCapacityOf columnResiduals j = columnCapacityOf inputColumns j)
    (heligible : ∀ e ∈ a, e.1 < e.2.1)
    (hnoncrossing : ∀ e ∈ a, ¬ (e.1 < t ∧ t < e.2.1))
    (hrows : ∀ r ∈ rowResiduals, t ≤ r.1)
    (hcolumns : ∀ c ∈ columnResiduals, c.1 ≤ t) :
    allocationTotalMass a =
      (∑ i with i < t, rowCapacityOf inputRows i) +
        ∑ j with t < j, columnCapacityOf inputColumns j := by
  have hrowZero : (∑ i with i < t, rowCapacityOf rowResiduals i) = 0 := by
    apply rowCapacityOf_sum_filter_eq_zero
    intro r hr hrt
    exact (not_lt_of_ge (hrows r hr)) hrt
  have hcolumnZero :
      (∑ j with t < j, columnCapacityOf columnResiduals j) = 0 := by
    apply columnCapacityOf_sum_filter_eq_zero
    intro c hc htc
    exact (not_lt_of_ge (hcolumns c hc)) htc
  have hrowSum :
      (∑ i with i < t, (allocationRowMass a i + rowCapacityOf rowResiduals i)) =
        ∑ i with i < t, rowCapacityOf inputRows i :=
    Finset.sum_congr rfl fun i _ => hrow i
  have hcolumnSum :
      (∑ j with t < j, (allocationColumnMass a j +
        columnCapacityOf columnResiduals j)) =
        ∑ j with t < j, columnCapacityOf inputColumns j :=
    Finset.sum_congr rfl fun j _ => hcolumn j
  rw [Finset.sum_add_distrib] at hrowSum hcolumnSum
  rw [hrowZero, add_zero] at hrowSum
  rw [hcolumnZero, add_zero] at hcolumnSum
  rw [allocationTotalMass_eq_descending_cut a t heligible hnoncrossing,
    hrowSum, hcolumnSum]

/-- The descending greedy pass conserves every row margin. -/
private theorem maxBenefitPass_row_conservation
    (rows columns : List (Fin K × ℝ)) (i : Fin K) :
    allocationRowMass (maxBenefitPass rows columns).allocations i +
      rowCapacityOf (maxBenefitPass rows columns).rowResiduals i =
        rowCapacityOf rows i := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass, allocationRowMass, rowCapacityOf]
  | case2 => simp [maxBenefitPass, allocationRowMass, rowCapacityOf]
  | case3 i' a rows j b columns hij hab ih =>
      by_cases hi : i' = i
      · subst i'
        simp [maxBenefitPass, hij, hab, allocationRowMass, rowCapacityOf] at ih ⊢
        linarith
      · simp [maxBenefitPass, hij, hab, allocationRowMass, rowCapacityOf, hi] at ih ⊢
        exact ih
  | case4 i' a rows j b columns hij hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      by_cases hi : i' = i
      · subst i'
        simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationRowMass,
          rowCapacityOf] at ih ⊢
        linarith
      · simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationRowMass,
          rowCapacityOf, hi] at ih ⊢
        exact ih
  | case5 i' a rows j b columns hji ih =>
      by_cases hi : i' = i
      · subst i'
        simp [maxBenefitPass, hji, allocationRowMass, rowCapacityOf] at ih ⊢
        linarith
      · simp [maxBenefitPass, hji, allocationRowMass, rowCapacityOf, hi] at ih ⊢
        exact ih

/-- The descending greedy pass conserves every column margin. -/
private theorem maxBenefitPass_column_conservation
    (rows columns : List (Fin K × ℝ)) (j : Fin K) :
    allocationColumnMass (maxBenefitPass rows columns).allocations j +
      columnCapacityOf (maxBenefitPass rows columns).columnResiduals j =
        columnCapacityOf columns j := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass, allocationColumnMass, columnCapacityOf]
  | case2 => simp [maxBenefitPass, allocationColumnMass, columnCapacityOf]
  | case3 i a rows j' b columns hij hab ih =>
      by_cases hj : j' = j
      · subst j'
        simp [maxBenefitPass, hij, hab, allocationColumnMass, columnCapacityOf] at ih ⊢
        linarith
      · simp [maxBenefitPass, hij, hab, allocationColumnMass, columnCapacityOf, hj] at ih ⊢
        exact ih
  | case4 i a rows j' b columns hij hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      by_cases hj : j' = j
      · subst j'
        simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationColumnMass,
          columnCapacityOf] at ih ⊢
        linarith
      · simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationColumnMass,
          columnCapacityOf, hj] at ih ⊢
        exact ih
  | case5 i a rows j' b columns hji ih =>
      simpa [maxBenefitPass, hji, allocationColumnMass, columnCapacityOf] using ih

/-- The descending greedy pass conserves total row-side mass. -/
private theorem maxBenefitPass_rowTotal_conservation
    (rows columns : List (Fin K × ℝ)) :
    allocationTotalMass (maxBenefitPass rows columns).allocations +
      ((maxBenefitPass rows columns).rowResiduals.map Prod.snd).sum =
        (rows.map Prod.snd).sum := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass, allocationTotalMass]
  | case2 => simp [maxBenefitPass, allocationTotalMass]
  | case3 i a rows j b columns hij hab ih =>
      simp [maxBenefitPass, hij, hab, allocationTotalMass] at ih ⊢
      linarith
  | case4 i a rows j b columns hij hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationTotalMass] at ih ⊢
      linarith
  | case5 i a rows j b columns hji ih =>
      simp [maxBenefitPass, hji, allocationTotalMass] at ih ⊢
      linarith

/-- The descending greedy pass conserves total column-side mass. -/
private theorem maxBenefitPass_columnTotal_conservation
    (rows columns : List (Fin K × ℝ)) :
    allocationTotalMass (maxBenefitPass rows columns).allocations +
      ((maxBenefitPass rows columns).columnResiduals.map Prod.snd).sum =
        (columns.map Prod.snd).sum := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass, allocationTotalMass]
  | case2 => simp [maxBenefitPass, allocationTotalMass]
  | case3 i a rows j b columns hij hab ih =>
      simp [maxBenefitPass, hij, hab, allocationTotalMass] at ih ⊢
      linarith
  | case4 i a rows j b columns hij hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      simp [maxBenefitPass, hij, hba, min_eq_right hba', allocationTotalMass] at ih ⊢
      linarith
  | case5 i a rows j b columns hji ih =>
      simpa [maxBenefitPass, hji, allocationTotalMass] using ih

/-- The ascending greedy pass conserves every row margin. -/
private theorem maxNonBenefitPass_row_conservation
    (rows columns : List (Fin K × ℝ)) (i : Fin K) :
    allocationRowMass (maxNonBenefitPass rows columns).allocations i +
      rowCapacityOf (maxNonBenefitPass rows columns).rowResiduals i =
        rowCapacityOf rows i := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass, allocationRowMass, rowCapacityOf]
  | case2 => simp [maxNonBenefitPass, allocationRowMass, rowCapacityOf]
  | case3 i' a rows j b columns hji hab ih =>
      by_cases hi : i' = i
      · subst i'
        simp [maxNonBenefitPass, hji, hab, allocationRowMass, rowCapacityOf] at ih ⊢
        linarith
      · simp [maxNonBenefitPass, hji, hab, allocationRowMass, rowCapacityOf, hi] at ih ⊢
        exact ih
  | case4 i' a rows j b columns hji hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      by_cases hi : i' = i
      · subst i'
        simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationRowMass,
          rowCapacityOf] at ih ⊢
        linarith
      · simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationRowMass,
          rowCapacityOf, hi] at ih ⊢
        exact ih
  | case5 i' a rows j b columns hij ih =>
      by_cases hi : i' = i
      · subst i'
        simp [maxNonBenefitPass, hij, allocationRowMass, rowCapacityOf] at ih ⊢
        linarith
      · simp [maxNonBenefitPass, hij, allocationRowMass, rowCapacityOf, hi] at ih ⊢
        exact ih

/-- The ascending greedy pass conserves every column margin. -/
private theorem maxNonBenefitPass_column_conservation
    (rows columns : List (Fin K × ℝ)) (j : Fin K) :
    allocationColumnMass (maxNonBenefitPass rows columns).allocations j +
      columnCapacityOf (maxNonBenefitPass rows columns).columnResiduals j =
        columnCapacityOf columns j := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass, allocationColumnMass, columnCapacityOf]
  | case2 => simp [maxNonBenefitPass, allocationColumnMass, columnCapacityOf]
  | case3 i a rows j' b columns hji hab ih =>
      by_cases hj : j' = j
      · subst j'
        simp [maxNonBenefitPass, hji, hab, allocationColumnMass, columnCapacityOf] at ih ⊢
        linarith
      · simp [maxNonBenefitPass, hji, hab, allocationColumnMass, columnCapacityOf, hj] at ih ⊢
        exact ih
  | case4 i a rows j' b columns hji hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      by_cases hj : j' = j
      · subst j'
        simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationColumnMass,
          columnCapacityOf] at ih ⊢
        linarith
      · simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationColumnMass,
          columnCapacityOf, hj] at ih ⊢
        exact ih
  | case5 i a rows j' b columns hij ih =>
      simpa [maxNonBenefitPass, hij, allocationColumnMass, columnCapacityOf] using ih

/-- The ascending greedy pass conserves total row-side mass. -/
private theorem maxNonBenefitPass_rowTotal_conservation
    (rows columns : List (Fin K × ℝ)) :
    allocationTotalMass (maxNonBenefitPass rows columns).allocations +
      ((maxNonBenefitPass rows columns).rowResiduals.map Prod.snd).sum =
        (rows.map Prod.snd).sum := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass, allocationTotalMass]
  | case2 => simp [maxNonBenefitPass, allocationTotalMass]
  | case3 i a rows j b columns hji hab ih =>
      simp [maxNonBenefitPass, hji, hab, allocationTotalMass] at ih ⊢
      linarith
  | case4 i a rows j b columns hji hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationTotalMass] at ih ⊢
      linarith
  | case5 i a rows j b columns hij ih =>
      simp [maxNonBenefitPass, hij, allocationTotalMass] at ih ⊢
      linarith

/-- The ascending greedy pass conserves total column-side mass. -/
private theorem maxNonBenefitPass_columnTotal_conservation
    (rows columns : List (Fin K × ℝ)) :
    allocationTotalMass (maxNonBenefitPass rows columns).allocations +
      ((maxNonBenefitPass rows columns).columnResiduals.map Prod.snd).sum =
        (columns.map Prod.snd).sum := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass, allocationTotalMass]
  | case2 => simp [maxNonBenefitPass, allocationTotalMass]
  | case3 i a rows j b columns hji hab ih =>
      simp [maxNonBenefitPass, hji, hab, allocationTotalMass] at ih ⊢
      linarith
  | case4 i a rows j b columns hji hba ih =>
      have hba' : b ≤ a := le_of_not_ge hba
      simp [maxNonBenefitPass, hji, hba, min_eq_right hba', allocationTotalMass] at ih ⊢
      linarith
  | case5 i a rows j b columns hij ih =>
      simpa [maxNonBenefitPass, hij, allocationTotalMass] using ih

/-- Materializing a sparse allocation list preserves each individual cell
mass. -/
private theorem sparseMatrix_apply (a : List (Allocation K)) (i j : Fin K) :
    sparseMatrix a i j =
      (a.map fun e => if e.1 = i ∧ e.2.1 = j then e.2.2 else 0).sum := by
  unfold sparseMatrix
  suffices ∀ total : ℝ,
      a.foldl
          (fun acc e => if e.1 = i ∧ e.2.1 = j then acc + e.2.2 else acc) total =
        total + (a.map fun e => if e.1 = i ∧ e.2.1 = j then e.2.2 else 0).sum by
    simpa using this 0
  intro total
  induction a generalizing total with
  | nil => simp
  | cons e entries ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      split_ifs <;> ring

/-- Materializing a sparse list cannot create a positive matrix cell at a
row-column pair absent from the list, so its positive support is no larger
than the list itself. -/
private theorem positiveSupportCard_sparseMatrix_le_length
    (a : List (Allocation K)) :
    positiveSupportCard (sparseMatrix a) ≤ a.length := by
  classical
  let coordinates : Finset (Fin K × Fin K) :=
    a.toFinset.image fun e => (e.1, e.2.1)
  have hsubset :
      (Finset.univ.product Finset.univ).filter
          (fun ij => 0 < sparseMatrix a ij.1 ij.2) ⊆ coordinates := by
    intro ij hij
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ,
      and_self, true_and] at hij
    have hex : ∃ e ∈ a, e.1 = ij.1 ∧ e.2.1 = ij.2 := by
      by_contra hnone
      push_neg at hnone
      have hzero :
          (a.map fun e => if e.1 = ij.1 ∧ e.2.1 = ij.2 then e.2.2 else 0).sum = 0 := by
        apply List.sum_eq_zero
        intro z hz
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hz
        split_ifs with h
        · exact False.elim ((hnone e he h.1) h.2)
        · rfl
      rw [sparseMatrix_apply, hzero] at hij
      linarith
    obtain ⟨e, he, hi, hj⟩ := hex
    apply Finset.mem_image.mpr
    refine ⟨e, by simpa using he, ?_⟩
    simp [hi, hj]
  calc
    positiveSupportCard (sparseMatrix a) ≤ coordinates.card :=
      Finset.card_le_card hsubset
    _ ≤ a.toFinset.card := Finset.card_image_le
    _ ≤ a.length := List.toFinset_card_le a

/-- Sparse materialization preserves row masses. -/
private theorem sparseMatrix_rowMass (a : List (Allocation K)) (i : Fin K) :
    rowMass (sparseMatrix a) i = allocationRowMass a i := by
  unfold rowMass allocationRowMass
  simp_rw [sparseMatrix_apply]
  induction a with
  | nil => simp
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      by_cases hi : e.1 = i
      · simp [hi]
      · simp [hi]

/-- Sparse materialization preserves column masses. -/
private theorem sparseMatrix_columnMass (a : List (Allocation K)) (j : Fin K) :
    columnMass (sparseMatrix a) j = allocationColumnMass a j := by
  unfold columnMass allocationColumnMass
  simp_rw [sparseMatrix_apply]
  induction a with
  | nil => simp
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      by_cases hj : e.2.1 = j
      · simp [hj]
      · simp [hj]

/-- Sparse materialization preserves total mass. -/
private theorem sparseMatrix_totalMass (a : List (Allocation K)) :
    totalMass (sparseMatrix a) = allocationTotalMass a := by
  change (∑ i, rowMass (sparseMatrix a) i) = allocationTotalMass a
  simp_rw [sparseMatrix_rowMass]
  induction a with
  | nil => simp [allocationRowMass, allocationTotalMass]
  | cons e entries ih =>
      simp [allocationRowMass, allocationTotalMass, Finset.sum_add_distrib]
      exact ih

/-- Sparse materialization preserves the mass on strict-benefit cells. -/
private theorem sparseMatrix_benefitMass (a : List (Allocation K)) :
    benefitMass (sparseMatrix a) = allocationBenefitMass a := by
  classical
  unfold benefitMass allocationBenefitMass
  simp_rw [sparseMatrix_apply]
  induction a with
  | nil => simp
  | cons e entries ih =>
      simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
      have hdelta :
          (∑ i, ∑ j with i < j,
            if e.1 = i ∧ e.2.1 = j then e.2.2 else 0) =
            if e.1 < e.2.1 then e.2.2 else 0 := by
        rw [Finset.sum_eq_single e.1]
        · by_cases he : e.1 < e.2.1
          · rw [Finset.sum_eq_single e.2.1]
            · simp [he]
            · intro j hj hne
              rw [if_neg]
              intro h
              exact hne h.2.symm
            · simp [he]
          · simp [he]
        · intro i hi hne
          apply Finset.sum_eq_zero
          intro j hj
          rw [if_neg]
          intro h
          exact hne h.1.symm
        · simp
      simpa [hdelta]

/-- The complete transport never invents a row or column index. -/
private theorem completeSparse_indices
    (rows columns : List (Fin K × ℝ)) (e : Allocation K)
    (he : e ∈ completeSparse rows columns) :
    (∃ r ∈ rows, r.1 = e.1) ∧ (∃ c ∈ columns, c.1 = e.2.1) := by
  induction rows, columns using completeSparse.induct <;>
    simp_all [completeSparse] <;> grind

/-- If every residual row lies weakly below a cut and every residual column
lies strictly above it, all allocations made by completion are benefit cells. -/
private theorem completeSparse_all_benefit_of_cut
    (rows columns : List (Fin K × ℝ)) (t : Fin K)
    (hrows : ∀ r ∈ rows, r.1 ≤ t) (hcolumns : ∀ c ∈ columns, t < c.1) :
    ∀ e ∈ completeSparse rows columns, e.1 < e.2.1 := by
  intro e he
  obtain ⟨⟨r, hr, hre⟩, c, hc, hce⟩ := completeSparse_indices rows columns e he
  simpa [← hre, ← hce] using lt_of_le_of_lt (hrows r hr) (hcolumns c hc)

/-- If every residual row lies weakly above a cut and every residual column
lies weakly below it, completion creates no strict-benefit cell. -/
private theorem completeSparse_no_benefit_of_cut
    (rows columns : List (Fin K × ℝ)) (t : Fin K)
    (hrows : ∀ r ∈ rows, t ≤ r.1) (hcolumns : ∀ c ∈ columns, c.1 ≤ t) :
    ∀ e ∈ completeSparse rows columns, ¬ e.1 < e.2.1 := by
  intro e he hbenefit
  obtain ⟨⟨r, hr, hre⟩, c, hc, hce⟩ := completeSparse_indices rows columns e he
  have := lt_of_lt_of_le (show r.1 < c.1 by simpa [hre, hce] using hbenefit) (hcolumns c hc)
  exact (not_lt_of_ge (hrows r hr)) this

/-- Every allocation emitted by the benefit pass is a strict-benefit cell. -/
private theorem maxBenefitPass_allocations_benefit
    (rows columns : List (Fin K × ℝ)) :
    ∀ e ∈ (maxBenefitPass rows columns).allocations, e.1 < e.2.1 := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all [maxBenefitPass] <;> grind

/-- Every allocation emitted by the nonbenefit pass lies on or below the
diagonal. -/
private theorem maxNonBenefitPass_allocations_nonbenefit
    (rows columns : List (Fin K × ℝ)) :
    ∀ e ∈ (maxNonBenefitPass rows columns).allocations, ¬ e.1 < e.2.1 := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all [maxNonBenefitPass] <;> grind

/-- Both endpoints of every allocation emitted by the ascending pass come
from the corresponding input lists. -/
private theorem maxNonBenefitPass_allocation_indices
    (rows columns : List (Fin K × ℝ)) (e : Allocation K)
    (he : e ∈ (maxNonBenefitPass rows columns).allocations) :
    (∃ r ∈ rows, r.1 = e.1) ∧ (∃ c ∈ columns, c.1 = e.2.1) := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all [maxNonBenefitPass] <;> grind

/-- Both endpoints of every allocation emitted by the descending pass come
from the corresponding input lists. -/
private theorem maxBenefitPass_allocation_indices
    (rows columns : List (Fin K × ℝ)) (e : Allocation K)
    (he : e ∈ (maxBenefitPass rows columns).allocations) :
    (∃ r ∈ rows, r.1 = e.1) ∧ (∃ c ∈ columns, c.1 = e.2.1) := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all [maxBenefitPass] <;> grind

/-- Residuals of the ascending pass retain indices from their respective
input lists. -/
private theorem maxNonBenefitPass_residual_indices
    (rows columns : List (Fin K × ℝ)) :
    (∀ r ∈ (maxNonBenefitPass rows columns).rowResiduals,
      ∃ r' ∈ rows, r'.1 = r.1) ∧
    (∀ c ∈ (maxNonBenefitPass rows columns).columnResiduals,
      ∃ c' ∈ columns, c'.1 = c.1) := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all [maxNonBenefitPass] <;> grind

/-- On strictly increasing inputs, every row left by the ascending nonbenefit
pass lies strictly below every column it leaves. -/
private theorem maxNonBenefitPass_residual_separated
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => r.1 < s.1)
    (hcolumns : columns.Pairwise fun c d => c.1 < d.1) :
    ∀ r ∈ (maxNonBenefitPass rows columns).rowResiduals,
      ∀ c ∈ (maxNonBenefitPass rows columns).columnResiduals, r.1 < c.1 := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass]
  | case2 => simp [maxNonBenefitPass]
  | case3 i a rows j b columns hji hab ih =>
      have hrows' := (List.pairwise_cons.mp hrows).2
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hcolumns' :
          ((j, b - min a b) :: columns).Pairwise fun c d => c.1 < d.1 := by
        exact List.pairwise_cons.mpr hcolumnsParts
      simpa [maxNonBenefitPass, hji, hab] using ih hrows' hcolumns'
  | case4 i a rows j b columns hji hba ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hrows' :
          ((i, a - min a b) :: rows).Pairwise fun r s => r.1 < s.1 := by
        exact List.pairwise_cons.mpr hrowsParts
      have hcolumns' := (List.pairwise_cons.mp hcolumns).2
      simpa [maxNonBenefitPass, hji, hba] using ih hrows' hcolumns'
  | case5 i a rows j b columns hij ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hrec := ih hrowsParts.2 hcolumns
      have hij' : i < j := lt_of_not_ge hij
      simp only [maxNonBenefitPass, if_neg hij, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro c hc
        obtain ⟨c', hc', hc'eq⟩ :=
          (maxNonBenefitPass_residual_indices rows ((j, b) :: columns)).2 c hc
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · have hjeq : j = c.1 := by simpa using hc'eq
          rw [← hjeq]
          exact hij'
        · have hjc : j < c'.1 := hcolumnsParts.1 c' hc'
          simpa [hc'eq] using lt_trans hij' hjc
      · exact hrec

/-- The ascending pass is a nonbenefit-flow cut certificate: it emits only
nonbenefit edges, and no nonbenefit edge joins two residual vertices. -/
private theorem maxNonBenefitPass_cut_certificate
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => r.1 < s.1)
    (hcolumns : columns.Pairwise fun c d => c.1 < d.1) :
    (∀ e ∈ (maxNonBenefitPass rows columns).allocations,
      ¬ e.1 < e.2.1) ∧
    (∀ r ∈ (maxNonBenefitPass rows columns).rowResiduals,
      ∀ c ∈ (maxNonBenefitPass rows columns).columnResiduals,
        ¬ c.1 ≤ r.1) := by
  constructor
  · exact maxNonBenefitPass_allocations_nonbenefit rows columns
  · intro r hr c hc
    exact not_le_of_gt
      (maxNonBenefitPass_residual_separated rows columns hrows hcolumns r hr c hc)

/-- No allocation emitted by the ascending pass crosses both sides of a
residual-row threshold. -/
private theorem maxNonBenefitPass_allocations_nonCrossing
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => r.1 < s.1)
    (hcolumns : columns.Pairwise fun c d => c.1 < d.1) :
    ∀ r ∈ (maxNonBenefitPass rows columns).rowResiduals,
      ∀ e ∈ (maxNonBenefitPass rows columns).allocations,
        ¬ (r.1 < e.1 ∧ e.2.1 ≤ r.1) := by
  induction rows, columns using maxNonBenefitPass.induct with
  | case1 => simp [maxNonBenefitPass]
  | case2 => simp [maxNonBenefitPass]
  | case3 i a rows j b columns hji hab ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hcolumns' :
          ((j, b - min a b) :: columns).Pairwise fun c d => c.1 < d.1 :=
        List.pairwise_cons.mpr hcolumnsParts
      have hrec := ih hrowsParts.2 hcolumns'
      simp only [maxNonBenefitPass, if_pos hji, if_pos hab, List.mem_cons,
        forall_eq_or_imp]
      intro r hr
      constructor
      · intro hcross
        obtain ⟨r', hr', hr'eq⟩ :=
          (maxNonBenefitPass_residual_indices rows
            ((j, b - min a b) :: columns)).1 r hr
        have hir : i < r'.1 := hrowsParts.1 r' hr'
        exact (not_lt_of_ge (le_of_lt (by simpa [hr'eq] using hir))) hcross.1
      · exact hrec r hr
  | case4 i a rows j b columns hji hba ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hrows' :
          ((i, a - min a b) :: rows).Pairwise fun r s => r.1 < s.1 :=
        List.pairwise_cons.mpr hrowsParts
      have hrec := ih hrows' (List.pairwise_cons.mp hcolumns).2
      simp only [maxNonBenefitPass, if_pos hji, if_neg hba, List.mem_cons,
        forall_eq_or_imp]
      intro r hr
      constructor
      · intro hcross
        obtain ⟨r', hr', hr'eq⟩ :=
          (maxNonBenefitPass_residual_indices
            ((i, a - min a b) :: rows) columns).1 r hr
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | hr'
        · have hrii : r.1 = i := by simpa using hr'eq.symm
          exact (not_lt_of_ge (le_of_eq hrii.symm)) hcross.1
        · have hir : i < r'.1 := hrowsParts.1 r' hr'
          exact (not_lt_of_ge (le_of_lt (by simpa [hr'eq] using hir))) hcross.1
      · exact hrec r hr
  | case5 i a rows j b columns hij ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hrec := ih hrowsParts.2 hcolumns
      have hij' : i < j := lt_of_not_ge hij
      simp only [maxNonBenefitPass, if_neg hij, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro e he hcross
        obtain ⟨c', hc', hc'eq⟩ :=
          (maxNonBenefitPass_allocation_indices rows ((j, b) :: columns) e he).2
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · have : j = e.2.1 := by simpa using hc'eq
          omega
        · have hjc : j < c'.1 := hcolumnsParts.1 c' hc'
          have : c'.1 = e.2.1 := hc'eq
          omega
      · exact hrec

/-- Residuals of the descending pass retain indices from their respective
input lists. -/
private theorem maxBenefitPass_residual_indices
    (rows columns : List (Fin K × ℝ)) :
    (∀ r ∈ (maxBenefitPass rows columns).rowResiduals,
      ∃ r' ∈ rows, r'.1 = r.1) ∧
    (∀ c ∈ (maxBenefitPass rows columns).columnResiduals,
      ∃ c' ∈ columns, c'.1 = c.1) := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all [maxBenefitPass] <;> grind

/-- On strictly decreasing inputs, every column left by the descending
benefit pass lies weakly below every row it leaves. -/
private theorem maxBenefitPass_residual_separated
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => s.1 < r.1)
    (hcolumns : columns.Pairwise fun c d => d.1 < c.1) :
    ∀ r ∈ (maxBenefitPass rows columns).rowResiduals,
      ∀ c ∈ (maxBenefitPass rows columns).columnResiduals, c.1 ≤ r.1 := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass]
  | case2 => simp [maxBenefitPass]
  | case3 i a rows j b columns hij hab ih =>
      have hrows' := (List.pairwise_cons.mp hrows).2
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hcolumns' :
          ((j, b - min a b) :: columns).Pairwise fun c d => d.1 < c.1 := by
        exact List.pairwise_cons.mpr hcolumnsParts
      simpa [maxBenefitPass, hij, hab] using ih hrows' hcolumns'
  | case4 i a rows j b columns hij hba ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hrows' :
          ((i, a - min a b) :: rows).Pairwise fun r s => s.1 < r.1 := by
        exact List.pairwise_cons.mpr hrowsParts
      have hcolumns' := (List.pairwise_cons.mp hcolumns).2
      simpa [maxBenefitPass, hij, hba] using ih hrows' hcolumns'
  | case5 i a rows j b columns hji ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hrec := ih hrowsParts.2 hcolumns
      have hji' : j ≤ i := not_lt.mp hji
      simp only [maxBenefitPass, if_neg hji, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro c hc
        obtain ⟨c', hc', hc'eq⟩ :=
          (maxBenefitPass_residual_indices rows ((j, b) :: columns)).2 c hc
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · have hjeq : j = c.1 := by simpa using hc'eq
          rw [← hjeq]
          exact hji'
        · have hcj : c'.1 < j := hcolumnsParts.1 c' hc'
          have hc'i : c'.1 ≤ i := le_trans (le_of_lt hcj) hji'
          simpa [hc'eq] using hc'i
      · exact hrec

/-- The descending pass is a benefit-flow cut certificate: it emits only
benefit edges, and no benefit edge joins two residual vertices. -/
private theorem maxBenefitPass_cut_certificate
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => s.1 < r.1)
    (hcolumns : columns.Pairwise fun c d => d.1 < c.1) :
    (∀ e ∈ (maxBenefitPass rows columns).allocations, e.1 < e.2.1) ∧
    (∀ r ∈ (maxBenefitPass rows columns).rowResiduals,
      ∀ c ∈ (maxBenefitPass rows columns).columnResiduals,
        ¬ r.1 < c.1) := by
  constructor
  · exact maxBenefitPass_allocations_benefit rows columns
  · intro r hr c hc
    exact not_lt_of_ge
      (maxBenefitPass_residual_separated rows columns hrows hcolumns r hr c hc)

/-- No allocation emitted by the descending pass crosses both sides of a
residual-row threshold. -/
private theorem maxBenefitPass_allocations_nonCrossing
    (rows columns : List (Fin K × ℝ))
    (hrows : rows.Pairwise fun r s => s.1 < r.1)
    (hcolumns : columns.Pairwise fun c d => d.1 < c.1) :
    ∀ r ∈ (maxBenefitPass rows columns).rowResiduals,
      ∀ e ∈ (maxBenefitPass rows columns).allocations,
        ¬ (e.1 < r.1 ∧ r.1 < e.2.1) := by
  induction rows, columns using maxBenefitPass.induct with
  | case1 => simp [maxBenefitPass]
  | case2 => simp [maxBenefitPass]
  | case3 i a rows j b columns hij hab ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hcolumns' :
          ((j, b - min a b) :: columns).Pairwise fun c d => d.1 < c.1 :=
        List.pairwise_cons.mpr hcolumnsParts
      have hrec := ih hrowsParts.2 hcolumns'
      simp only [maxBenefitPass, if_pos hij, if_pos hab, List.mem_cons,
        forall_eq_or_imp]
      intro r hr
      constructor
      · intro hcross
        obtain ⟨r', hr', hr'eq⟩ :=
          (maxBenefitPass_residual_indices rows
            ((j, b - min a b) :: columns)).1 r hr
        have hri : r'.1 < i := hrowsParts.1 r' hr'
        exact (not_lt_of_ge (le_of_lt (by simpa [hr'eq] using hri))) hcross.1
      · exact hrec r hr
  | case4 i a rows j b columns hij hba ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hrows' :
          ((i, a - min a b) :: rows).Pairwise fun r s => s.1 < r.1 :=
        List.pairwise_cons.mpr hrowsParts
      have hrec := ih hrows' (List.pairwise_cons.mp hcolumns).2
      simp only [maxBenefitPass, if_pos hij, if_neg hba, List.mem_cons,
        forall_eq_or_imp]
      intro r hr
      constructor
      · intro hcross
        obtain ⟨r', hr', hr'eq⟩ :=
          (maxBenefitPass_residual_indices
            ((i, a - min a b) :: rows) columns).1 r hr
        simp only [List.mem_cons] at hr'
        rcases hr' with rfl | hr'
        · have hrii : r.1 = i := by simpa using hr'eq.symm
          exact (not_lt_of_ge (le_of_eq hrii)) hcross.1
        · have hri : r'.1 < i := hrowsParts.1 r' hr'
          exact (not_lt_of_ge (le_of_lt (by simpa [hr'eq] using hri))) hcross.1
      · exact hrec r hr
  | case5 i a rows j b columns hji ih =>
      have hrowsParts := List.pairwise_cons.mp hrows
      have hcolumnsParts := List.pairwise_cons.mp hcolumns
      have hrec := ih hrowsParts.2 hcolumns
      have hji' : j ≤ i := not_lt.mp hji
      simp only [maxBenefitPass, if_neg hji, List.mem_cons, forall_eq_or_imp]
      constructor
      · intro e he hcross
        obtain ⟨c', hc', hc'eq⟩ :=
          (maxBenefitPass_allocation_indices rows ((j, b) :: columns) e he).2
        simp only [List.mem_cons] at hc'
        rcases hc' with rfl | hc'
        · have hjeq : j = e.2.1 := by simpa using hc'eq
          have : e.2.1 ≤ i := by simpa [← hjeq] using hji'
          exact (not_lt_of_ge this) hcross.2
        · have hcj : c'.1 < j := hcolumnsParts.1 c' hc'
          have hci : c'.1 ≤ i := le_trans (le_of_lt hcj) hji'
          have : e.2.1 ≤ i := by simpa [hc'eq] using hci
          exact (not_lt_of_ge this) hcross.2
      · exact hrec

/-- Indexed capacity lists enumerate their indices in strict ascending order. -/
private theorem indexedMasses_pairwise (f : Fin K → ℝ) :
    (indexedMasses f).Pairwise fun r s => r.1 < s.1 := by
  unfold indexedMasses
  rw [List.pairwise_map, List.pairwise_iff_get]
  intro i j hij
  simp only [List.length_finRange, List.get_finRange]
  change i.val < j.val at hij ⊢
  exact hij

/-- Reversing an indexed capacity list enumerates its indices in strict
descending order. -/
private theorem indexedMasses_reverse_pairwise (f : Fin K → ℝ) :
    (indexedMasses f).reverse.Pairwise fun r s => s.1 < r.1 := by
  exact (indexedMasses_pairwise f).reverse

/-- The lower public greedy input has an ascending nonbenefit cut
certificate. -/
private theorem thresholdFlowLower_cut_certificate (c : Capacities 𝒳 K) (x : 𝒳) :
    let primary := maxNonBenefitPass
      (indexedMasses (c.lower x)) (indexedMasses (c.upper x))
    (∀ e ∈ primary.allocations, ¬ e.1 < e.2.1) ∧
    (∀ r ∈ primary.rowResiduals, ∀ d ∈ primary.columnResiduals,
      ¬ d.1 ≤ r.1) := by
  exact maxNonBenefitPass_cut_certificate _ _
    (indexedMasses_pairwise _) (indexedMasses_pairwise _)

/-- The upper public greedy input has a descending benefit cut certificate. -/
private theorem thresholdFlowUpper_cut_certificate (c : Capacities 𝒳 K) (x : 𝒳) :
    let primary := maxBenefitPass
      (indexedMasses (c.lower x)).reverse (indexedMasses (c.upper x)).reverse
    (∀ e ∈ primary.allocations, e.1 < e.2.1) ∧
    (∀ r ∈ primary.rowResiduals, ∀ d ∈ primary.columnResiduals,
      ¬ r.1 < d.1) := by
  exact maxBenefitPass_cut_certificate _ _
    (indexedMasses_reverse_pairwise _) (indexedMasses_reverse_pairwise _)

/-- The public ascending primary pass either exhausts every row or saturates
one nonbenefit threshold cut. -/
private theorem thresholdFlowLower_attains_cut_or_total_cap
    (c : Capacities 𝒳 K) (x : 𝒳) :
    let rows := indexedMasses (c.lower x)
    let columns := indexedMasses (c.upper x)
    let primary := maxNonBenefitPass rows columns
    (primary.rowResiduals = [] ∧
      allocationTotalMass primary.allocations = (rows.map Prod.snd).sum) ∨
    ∃ t : Fin K, allocationTotalMass primary.allocations =
      (∑ i with t < i, rowCapacityOf rows i) +
        ∑ j with j ≤ t, columnCapacityOf columns j := by
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  let primary := maxNonBenefitPass rows columns
  have hsep := maxNonBenefitPass_residual_separated rows columns
    (indexedMasses_pairwise _) (indexedMasses_pairwise _)
  have hnoncross := maxNonBenefitPass_allocations_nonCrossing rows columns
    (indexedMasses_pairwise _) (indexedMasses_pairwise _)
  rcases ascendingCutBoundary_exists primary.rowResiduals primary.columnResiduals
      primary.allocations hsep hnoncross with hempty | ⟨t, hrows, hcolumns, hcut⟩
  · left
    refine ⟨hempty, ?_⟩
    have htotal := maxNonBenefitPass_rowTotal_conservation rows columns
    simpa [primary, rows, hempty] using htotal
  · right
    refine ⟨t, ?_⟩
    exact allocationTotalMass_eq_ascending_input_cut primary.allocations
      primary.rowResiduals primary.columnResiduals rows columns t
      (maxNonBenefitPass_row_conservation rows columns)
      (maxNonBenefitPass_column_conservation rows columns)
      (maxNonBenefitPass_allocations_nonbenefit rows columns) hcut hrows hcolumns

/-- The public descending primary pass either exhausts every row or saturates
one benefit threshold cut. -/
private theorem thresholdFlowUpper_attains_cut_or_total_cap
    (c : Capacities 𝒳 K) (x : 𝒳) :
    let rows := (indexedMasses (c.lower x)).reverse
    let columns := (indexedMasses (c.upper x)).reverse
    let primary := maxBenefitPass rows columns
    (primary.rowResiduals = [] ∧
      allocationTotalMass primary.allocations = (rows.map Prod.snd).sum) ∨
    ∃ t : Fin K, allocationTotalMass primary.allocations =
      (∑ i with i < t, rowCapacityOf rows i) +
        ∑ j with t < j, columnCapacityOf columns j := by
  let rows := (indexedMasses (c.lower x)).reverse
  let columns := (indexedMasses (c.upper x)).reverse
  let primary := maxBenefitPass rows columns
  have hsep := maxBenefitPass_residual_separated rows columns
    (indexedMasses_reverse_pairwise _) (indexedMasses_reverse_pairwise _)
  have hnoncross := maxBenefitPass_allocations_nonCrossing rows columns
    (indexedMasses_reverse_pairwise _) (indexedMasses_reverse_pairwise _)
  rcases descendingCutBoundary_exists primary.rowResiduals primary.columnResiduals
      primary.allocations hsep hnoncross with hempty | ⟨t, hrows, hcolumns, hcut⟩
  · left
    refine ⟨hempty, ?_⟩
    have htotal := maxBenefitPass_rowTotal_conservation rows columns
    simpa [primary, rows, hempty] using htotal
  · right
    refine ⟨t, ?_⟩
    exact allocationTotalMass_eq_descending_input_cut primary.allocations
      primary.rowResiduals primary.columnResiduals rows columns t
      (maxBenefitPass_row_conservation rows columns)
      (maxBenefitPass_column_conservation rows columns)
      (maxBenefitPass_allocations_benefit rows columns) hcut hrows hcolumns

private def ascendingPrimaryCut (rows columns : List (Fin K × ℝ)) :
    Option (Fin K) → ℝ
  | none => min (rows.map Prod.snd).sum (columns.map Prod.snd).sum
  | some t => (∑ i with t < i, rowCapacityOf rows i) +
      ∑ j with j ≤ t, columnCapacityOf columns j

private def descendingPrimaryCut (rows columns : List (Fin K × ℝ)) :
    Option (Fin K) → ℝ
  | none => min (rows.map Prod.snd).sum (columns.map Prod.snd).sum
  | some t => (∑ i with i < t, rowCapacityOf rows i) +
      ∑ j with t < j, columnCapacityOf columns j

private theorem allocationBenefitMass_append (a b : List (Allocation K)) :
    allocationBenefitMass (a ++ b) =
      allocationBenefitMass a + allocationBenefitMass b := by
  simp [allocationBenefitMass]

private theorem allocationBenefitMass_eq_total_of_all_benefit
    (a : List (Allocation K)) (ha : ∀ e ∈ a, e.1 < e.2.1) :
    allocationBenefitMass a = allocationTotalMass a := by
  induction a with
  | nil => simp [allocationBenefitMass, allocationTotalMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at ha
      unfold allocationBenefitMass allocationTotalMass at ih ⊢
      simp only [List.map_cons, List.sum_cons, if_pos ha.1]
      rw [ih ha.2]

private theorem allocationBenefitMass_eq_zero_of_no_benefit
    (a : List (Allocation K)) (ha : ∀ e ∈ a, ¬ e.1 < e.2.1) :
    allocationBenefitMass a = 0 := by
  induction a with
  | nil => simp [allocationBenefitMass]
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at ha
      unfold allocationBenefitMass at ih ⊢
      simp only [List.map_cons, List.sum_cons, if_neg ha.1, zero_add]
      exact ih ha.2

/-- If every residual row is strictly below every residual column, all
allocations made by completion are benefit cells. -/
private theorem completeSparse_all_benefit_of_separation
    (rows columns : List (Fin K × ℝ))
    (hsep : ∀ r ∈ rows, ∀ c ∈ columns, r.1 < c.1) :
    ∀ e ∈ completeSparse rows columns, e.1 < e.2.1 := by
  intro e he
  obtain ⟨⟨r, hr, hre⟩, c, hc, hce⟩ := completeSparse_indices rows columns e he
  simpa [← hre, ← hce] using hsep r hr c hc

/-- If no residual row-column pair is a benefit cell, completion creates no
benefit allocation. -/
private theorem completeSparse_no_benefit_of_separation
    (rows columns : List (Fin K × ℝ))
    (hsep : ∀ r ∈ rows, ∀ c ∈ columns, ¬ r.1 < c.1) :
    ∀ e ∈ completeSparse rows columns, ¬ e.1 < e.2.1 := by
  intro e he
  obtain ⟨⟨r, hr, hre⟩, c, hc, hce⟩ := completeSparse_indices rows columns e he
  simpa [← hre, ← hce] using hsep r hr c hc

/-- Completing a certified nonbenefit pass puts exactly the mass not already
transported by that pass on benefit edges. -/
private theorem completePrimary_benefit_eq_total_sub_primary
    (primary : SparsePassResult K)
    (hprimary : ∀ e ∈ primary.allocations, ¬ e.1 < e.2.1)
    (hsep : ∀ r ∈ primary.rowResiduals,
      ∀ c ∈ primary.columnResiduals, r.1 < c.1) :
    allocationBenefitMass (completePrimary primary) =
      allocationTotalMass (completePrimary primary) -
        allocationTotalMass primary.allocations := by
  rw [completePrimary, allocationBenefitMass_append,
    allocationBenefitMass_eq_zero_of_no_benefit _ hprimary,
    allocationBenefitMass_eq_total_of_all_benefit]
  · simp [allocationTotalMass]
  · exact completeSparse_all_benefit_of_separation _ _ hsep

/-- Completing a certified benefit pass adds no benefit mass. -/
private theorem completePrimary_benefit_eq_primary
    (primary : SparsePassResult K)
    (hprimary : ∀ e ∈ primary.allocations, e.1 < e.2.1)
    (hsep : ∀ r ∈ primary.rowResiduals,
      ∀ c ∈ primary.columnResiduals, ¬ r.1 < c.1) :
    allocationBenefitMass (completePrimary primary) =
      allocationTotalMass primary.allocations := by
  rw [completePrimary, allocationBenefitMass_append,
    allocationBenefitMass_eq_total_of_all_benefit _ hprimary,
    allocationBenefitMass_eq_zero_of_no_benefit]
  · simp
  · exact completeSparse_no_benefit_of_separation _ _ hsep

/-- Once the ascending pass leaves residuals separated by a cut, all benefit
mass of its completion is exactly the mass transported in the complete pass. -/
private theorem completePrimary_benefit_of_nonbenefit_cut
    (primary : SparsePassResult K) (t : Fin K)
    (hprimary : ∀ e ∈ primary.allocations, ¬ e.1 < e.2.1)
    (hrows : ∀ r ∈ primary.rowResiduals, r.1 ≤ t)
    (hcolumns : ∀ c ∈ primary.columnResiduals, t < c.1) :
    allocationBenefitMass (completePrimary primary) =
      allocationTotalMass (completeSparse primary.rowResiduals primary.columnResiduals) := by
  rw [completePrimary, allocationBenefitMass_append,
    allocationBenefitMass_eq_zero_of_no_benefit _ hprimary,
    allocationBenefitMass_eq_total_of_all_benefit]
  · simp
  · exact completeSparse_all_benefit_of_cut _ _ t hrows hcolumns

/-- Once the descending pass leaves residuals separated by a cut, completion
adds no benefit mass, so the benefit total is exactly the primary-pass total. -/
private theorem completePrimary_benefit_of_benefit_cut
    (primary : SparsePassResult K) (t : Fin K)
    (hprimary : ∀ e ∈ primary.allocations, e.1 < e.2.1)
    (hrows : ∀ r ∈ primary.rowResiduals, t ≤ r.1)
    (hcolumns : ∀ c ∈ primary.columnResiduals, c.1 ≤ t) :
    allocationBenefitMass (completePrimary primary) =
      allocationTotalMass primary.allocations := by
  rw [completePrimary, allocationBenefitMass_append,
    allocationBenefitMass_eq_total_of_all_benefit _ hprimary,
    allocationBenefitMass_eq_zero_of_no_benefit]
  · simp
  · exact completeSparse_no_benefit_of_cut _ _ t hrows hcolumns

private theorem listTotal_nonnegative (entries : List (Fin K × ℝ))
    (hentries : ∀ e ∈ entries, 0 ≤ e.2) :
    0 ≤ (entries.map Prod.snd).sum := by
  induction entries with
  | nil => simp
  | cons e entries ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hentries
      simpa using add_nonneg hentries.1 (ih hentries.2)

private theorem rowCapacityOf_nonnegative (rows : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (i : Fin K) :
    0 ≤ rowCapacityOf rows i := by
  induction rows with
  | nil => simp [rowCapacityOf]
  | cons e rows ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hrows
      rw [rowCapacityOf]
      simp only [List.map_cons, List.sum_cons]
      apply add_nonneg
      · split_ifs
        · exact hrows.1
        · exact le_refl 0
      · exact ih hrows.2

private theorem columnCapacityOf_nonnegative (columns : List (Fin K × ℝ))
    (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) (j : Fin K) :
    0 ≤ columnCapacityOf columns j := by
  exact rowCapacityOf_nonnegative columns hcolumns j

/-- Pointwise row conservation with nonnegative residual capacities bounds
every filtered sum of allocation row masses by the matching input sum. -/
private theorem allocationRowMass_sum_filter_le
    (a : List (Allocation K)) (residuals input : List (Fin K × ℝ))
    (p : Fin K → Prop) [DecidablePred p]
    (hconservation : ∀ i, allocationRowMass a i + rowCapacityOf residuals i =
      rowCapacityOf input i)
    (hresiduals : ∀ r ∈ residuals, 0 ≤ r.2) :
    (∑ i with p i, allocationRowMass a i) ≤
      ∑ i with p i, rowCapacityOf input i := by
  apply Finset.sum_le_sum
  intro i hi
  have hnonnegative := rowCapacityOf_nonnegative residuals hresiduals i
  linarith [hconservation i]

/-- Pointwise column conservation with nonnegative residual capacities bounds
every filtered sum of allocation column masses by the matching input sum. -/
private theorem allocationColumnMass_sum_filter_le
    (a : List (Allocation K)) (residuals input : List (Fin K × ℝ))
    (p : Fin K → Prop) [DecidablePred p]
    (hconservation : ∀ j, allocationColumnMass a j +
      columnCapacityOf residuals j = columnCapacityOf input j)
    (hresiduals : ∀ c ∈ residuals, 0 ≤ c.2) :
    (∑ j with p j, allocationColumnMass a j) ≤
      ∑ j with p j, columnCapacityOf input j := by
  apply Finset.sum_le_sum
  intro j hj
  have hnonnegative := columnCapacityOf_nonnegative residuals hresiduals j
  linarith [hconservation j]

/-- Total conservation with a nonnegative residual list bounds allocated mass
by the corresponding input total. -/
private theorem allocationTotalMass_le_input_total
    (a : List (Allocation K)) (residuals input : List (Fin K × ℝ))
    (hconservation : allocationTotalMass a + (residuals.map Prod.snd).sum =
      (input.map Prod.snd).sum)
    (hresiduals : ∀ r ∈ residuals, 0 ≤ r.2) :
    allocationTotalMass a ≤ (input.map Prod.snd).sum := by
  have hnonnegative := listTotal_nonnegative residuals hresiduals
  linarith

/-- If a conserved pass leaves no row residual and its allocated mass is
bounded by the column total, it attains the smaller input total. -/
private theorem allocationTotalMass_eq_min_of_rowResiduals_eq_nil
    (a : List (Allocation K)) (rowResiduals inputRows inputColumns : List (Fin K × ℝ))
    (hrowTotal : allocationTotalMass a + (rowResiduals.map Prod.snd).sum =
      (inputRows.map Prod.snd).sum)
    (hempty : rowResiduals = [])
    (hcolumn : allocationTotalMass a ≤ (inputColumns.map Prod.snd).sum) :
    allocationTotalMass a =
      min (inputRows.map Prod.snd).sum (inputColumns.map Prod.snd).sum := by
  have hrow : allocationTotalMass a = (inputRows.map Prod.snd).sum := by
    simpa [hempty] using hrowTotal
  rw [hrow]
  exact (min_eq_left (by simpa [hrow] using hcolumn)).symm

/-- The public ascending primary mass is below every nonbenefit cut and both
input total capacities. -/
private theorem thresholdFlowLower_primary_le_cuts
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    let rows := indexedMasses (c.lower x)
    let columns := indexedMasses (c.upper x)
    let primary := maxNonBenefitPass rows columns
    (∀ t : Fin K, allocationTotalMass primary.allocations ≤
      (∑ i with t < i, rowCapacityOf rows i) +
        ∑ j with j ≤ t, columnCapacityOf columns j) ∧
    allocationTotalMass primary.allocations ≤ (rows.map Prod.snd).sum ∧
    allocationTotalMass primary.allocations ≤ (columns.map Prod.snd).sum := by
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  let primary := maxNonBenefitPass rows columns
  have hrows : ∀ r ∈ rows, 0 ≤ r.2 := by
    simp [rows, indexedMasses, hValid.1 x]
  have hcolumns : ∀ d ∈ columns, 0 ≤ d.2 := by
    simp [columns, indexedMasses, hValid.2 x]
  have hres := maxNonBenefitPass_residuals_nonnegative rows columns hrows hcolumns
  have halloc := maxNonBenefitPass_allocations_nonnegative rows columns hrows hcolumns
  constructor
  · intro t
    calc
      allocationTotalMass primary.allocations ≤
          (∑ i with t < i, allocationRowMass primary.allocations i) +
            ∑ j with j ≤ t, allocationColumnMass primary.allocations j :=
        allocationTotalMass_le_ascending_cut _ _ halloc
          (maxNonBenefitPass_allocations_nonbenefit rows columns)
      _ ≤ (∑ i with t < i, rowCapacityOf rows i) +
          ∑ j with j ≤ t, columnCapacityOf columns j := add_le_add
        (allocationRowMass_sum_filter_le _ _ _ _
          (maxNonBenefitPass_row_conservation rows columns) hres.1)
        (allocationColumnMass_sum_filter_le _ _ _ _
          (maxNonBenefitPass_column_conservation rows columns) hres.2)
  · constructor
    · exact allocationTotalMass_le_input_total _ _ _
        (maxNonBenefitPass_rowTotal_conservation rows columns) hres.1
    · exact allocationTotalMass_le_input_total _ _ _
        (maxNonBenefitPass_columnTotal_conservation rows columns) hres.2

/-- The public descending primary mass is below every benefit cut and both
input total capacities. -/
private theorem thresholdFlowUpper_primary_le_cuts
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    let rows := (indexedMasses (c.lower x)).reverse
    let columns := (indexedMasses (c.upper x)).reverse
    let primary := maxBenefitPass rows columns
    (∀ t : Fin K, allocationTotalMass primary.allocations ≤
      (∑ i with i < t, rowCapacityOf rows i) +
        ∑ j with t < j, columnCapacityOf columns j) ∧
    allocationTotalMass primary.allocations ≤ (rows.map Prod.snd).sum ∧
    allocationTotalMass primary.allocations ≤ (columns.map Prod.snd).sum := by
  let rows := (indexedMasses (c.lower x)).reverse
  let columns := (indexedMasses (c.upper x)).reverse
  let primary := maxBenefitPass rows columns
  have hrows : ∀ r ∈ rows, 0 ≤ r.2 := by
    simp [rows, indexedMasses, hValid.1 x]
  have hcolumns : ∀ d ∈ columns, 0 ≤ d.2 := by
    simp [columns, indexedMasses, hValid.2 x]
  have hres := maxBenefitPass_residuals_nonnegative rows columns hrows hcolumns
  have halloc := maxBenefitPass_allocations_nonnegative rows columns hrows hcolumns
  constructor
  · intro t
    calc
      allocationTotalMass primary.allocations ≤
          (∑ i with i < t, allocationRowMass primary.allocations i) +
            ∑ j with t < j, allocationColumnMass primary.allocations j :=
        allocationTotalMass_le_descending_cut _ _ halloc
          (maxBenefitPass_allocations_benefit rows columns)
      _ ≤ (∑ i with i < t, rowCapacityOf rows i) +
          ∑ j with t < j, columnCapacityOf columns j := add_le_add
        (allocationRowMass_sum_filter_le _ _ _ _
          (maxBenefitPass_row_conservation rows columns) hres.1)
        (allocationColumnMass_sum_filter_le _ _ _ _
          (maxBenefitPass_column_conservation rows columns) hres.2)
  · constructor
    · exact allocationTotalMass_le_input_total _ _ _
        (maxBenefitPass_rowTotal_conservation rows columns) hres.1
    · exact allocationTotalMass_le_input_total _ _ _
        (maxBenefitPass_columnTotal_conservation rows columns) hres.2

private theorem thresholdFlowLower_primary_inf
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    let rows := indexedMasses (c.lower x)
    let columns := indexedMasses (c.upper x)
    allocationTotalMass (maxNonBenefitPass rows columns).allocations =
      Finset.univ.inf' Finset.univ_nonempty (ascendingPrimaryCut rows columns) := by
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  let primary := maxNonBenefitPass rows columns
  have hb := thresholdFlowLower_primary_le_cuts c hValid x
  have ha := thresholdFlowLower_attains_cut_or_total_cap c x
  apply le_antisymm
  · apply Finset.le_inf' Finset.univ_nonempty
    intro o ho
    cases o with
    | none => exact le_min hb.2.1 hb.2.2
    | some t => exact hb.1 t
  · rcases ha with ⟨hempty, htotal⟩ | ⟨t, hcut⟩
    · have hmin := allocationTotalMass_eq_min_of_rowResiduals_eq_nil
        primary.allocations primary.rowResiduals rows columns
        (maxNonBenefitPass_rowTotal_conservation rows columns) hempty hb.2.2
      calc
        Finset.univ.inf' Finset.univ_nonempty (ascendingPrimaryCut rows columns) ≤
            ascendingPrimaryCut rows columns none := Finset.inf'_le _ (Finset.mem_univ none)
        _ = allocationTotalMass primary.allocations := hmin.symm
    · calc
        Finset.univ.inf' Finset.univ_nonempty (ascendingPrimaryCut rows columns) ≤
            ascendingPrimaryCut rows columns (some t) :=
          Finset.inf'_le _ (Finset.mem_univ (some t))
        _ = allocationTotalMass primary.allocations := hcut.symm

private theorem thresholdFlowUpper_primary_inf
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    let rows := (indexedMasses (c.lower x)).reverse
    let columns := (indexedMasses (c.upper x)).reverse
    allocationTotalMass (maxBenefitPass rows columns).allocations =
      Finset.univ.inf' Finset.univ_nonempty (descendingPrimaryCut rows columns) := by
  let rows := (indexedMasses (c.lower x)).reverse
  let columns := (indexedMasses (c.upper x)).reverse
  let primary := maxBenefitPass rows columns
  have hb := thresholdFlowUpper_primary_le_cuts c hValid x
  have ha := thresholdFlowUpper_attains_cut_or_total_cap c x
  apply le_antisymm
  · apply Finset.le_inf' Finset.univ_nonempty
    intro o ho
    cases o with
    | none => exact le_min hb.2.1 hb.2.2
    | some t => exact hb.1 t
  · rcases ha with ⟨hempty, htotal⟩ | ⟨t, hcut⟩
    · have hmin := allocationTotalMass_eq_min_of_rowResiduals_eq_nil
        primary.allocations primary.rowResiduals rows columns
        (maxBenefitPass_rowTotal_conservation rows columns) hempty hb.2.2
      calc
        Finset.univ.inf' Finset.univ_nonempty (descendingPrimaryCut rows columns) ≤
            descendingPrimaryCut rows columns none := Finset.inf'_le _ (Finset.mem_univ none)
        _ = allocationTotalMass primary.allocations := hmin.symm
    · calc
        Finset.univ.inf' Finset.univ_nonempty (descendingPrimaryCut rows columns) ≤
            descendingPrimaryCut rows columns (some t) :=
          Finset.inf'_le _ (Finset.mem_univ (some t))
        _ = allocationTotalMass primary.allocations := hcut.symm

private theorem sub_finset_inf'_eq_sup'_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (a : ℝ) (f : ι → ℝ) :
    a - s.inf' hs f = s.sup' hs (fun i => a - f i) := by
  apply le_antisymm
  · have hle : a - s.sup' hs (fun i => a - f i) ≤ s.inf' hs f := by
      apply Finset.le_inf' hs
      intro i hi
      have hi' := Finset.le_sup' (fun i => a - f i) hi
      linarith
    linarith
  · apply Finset.sup'_le hs
    intro i hi
    have hi' := Finset.inf'_le f hi
    linarith

private theorem min_eq_left_add_min_sub (a b : ℝ) :
    min a b = a + min (b - a) 0 := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, min_eq_right (sub_nonneg.mpr hab)]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, min_eq_left (sub_nonpos.mpr hba)]
    ring

private theorem lowerLe_add_lowerGt (c : Capacities 𝒳 K) (x : 𝒳) (t : Fin K) :
    c.lowerLe x t + c.lowerGt x t = c.q0 x := by
  simpa [Capacities.lowerLe, Capacities.lowerGt, Capacities.q0, not_le] using
    (Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : Fin K => i ≤ t) (c.lower x))

private theorem keySum_nonnegative (entries : List (Fin K × ℝ))
    (hentries : ∀ e ∈ entries, 0 ≤ e.2) (i : Fin K) :
    0 ≤ (entries.map fun e => if e.1 = i then e.2 else 0).sum := by
  simpa [rowCapacityOf] using rowCapacityOf_nonnegative entries hentries i

/-- Ordinary two-pointer transport respects every input margin and transports
the smaller of the two total residual masses. -/
private theorem completeSparse_margin_spec
    (rows columns : List (Fin K × ℝ))
    (hrows : ∀ e ∈ rows, 0 ≤ e.2) (hcolumns : ∀ e ∈ columns, 0 ≤ e.2) :
    (∀ i, allocationRowMass (completeSparse rows columns) i ≤ rowCapacityOf rows i) ∧
    (∀ j, allocationColumnMass (completeSparse rows columns) j ≤ columnCapacityOf columns j) ∧
    allocationTotalMass (completeSparse rows columns) =
      min (rows.map Prod.snd).sum (columns.map Prod.snd).sum := by
  induction rows, columns using completeSparse.induct with
  | case1 columns =>
      simp [completeSparse, allocationRowMass, allocationColumnMass,
        allocationTotalMass, rowCapacityOf, columnCapacityOf,
        listTotal_nonnegative columns hcolumns, keySum_nonnegative columns hcolumns]
  | case2 rows hrowsNe =>
      simp [completeSparse, allocationRowMass, allocationColumnMass,
        allocationTotalMass, rowCapacityOf, columnCapacityOf,
        listTotal_nonnegative rows hrows, keySum_nonnegative rows hrows]
  | case3 i a rows j b columns hab ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hrows hcolumns
      have hba : 0 ≤ b - a := sub_nonneg.mpr hab
      have hcolumns' : ∀ e ∈ (j, b - min a b) :: columns, 0 ≤ e.2 := by
        simpa [min_eq_left hab] using And.intro hba hcolumns.2
      have ih' := ih hrows.2 hcolumns'
      simp [min_eq_left hab] at ih'
      simp only [allocationRowMass, allocationColumnMass, allocationTotalMass,
        rowCapacityOf, columnCapacityOf, List.map_cons, List.sum_cons] at ih'
      simp only [completeSparse, hab, if_pos, min_eq_left hab]
      simp only [allocationRowMass, allocationColumnMass, allocationTotalMass,
        rowCapacityOf, columnCapacityOf, List.map_cons, List.sum_cons]
      constructor
      · intro i'
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (ih'.1 i') (if i = i' then a else 0)
      constructor
      · intro j'
        have hc := ih'.2.1 j'
        by_cases hj : j = j'
        · simp [hj] at hc ⊢
          linarith
        · simpa [hj] using hc
      · rw [ih'.2.2]
        by_cases htot : (rows.map Prod.snd).sum ≤ b - a + (columns.map Prod.snd).sum
        · rw [min_eq_left htot]
          have htot' : a + (rows.map Prod.snd).sum ≤
              b + (columns.map Prod.snd).sum := by linarith
          rw [min_eq_left htot']
        · rw [min_eq_right (le_of_not_ge htot)]
          have htot' : b + (columns.map Prod.snd).sum ≤
              a + (rows.map Prod.snd).sum := by linarith
          rw [min_eq_right htot']
          ring
  | case4 i a rows j b columns hab ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hrows hcolumns
      have hab' : b ≤ a := le_of_not_ge hab
      have habNonnegative : 0 ≤ a - b := sub_nonneg.mpr hab'
      have hrows' : ∀ e ∈ (i, a - min a b) :: rows, 0 ≤ e.2 := by
        simpa [min_eq_right hab'] using And.intro habNonnegative hrows.2
      have ih' := ih hrows' hcolumns.2
      simp [min_eq_right hab'] at ih'
      simp only [allocationRowMass, allocationColumnMass, allocationTotalMass,
        rowCapacityOf, columnCapacityOf, List.map_cons, List.sum_cons] at ih'
      simp [completeSparse, hab, min_eq_right hab']
      simp only [allocationRowMass, allocationColumnMass, allocationTotalMass,
        rowCapacityOf, columnCapacityOf, List.map_cons, List.sum_cons]
      constructor
      · intro i'
        have hr := ih'.1 i'
        by_cases hi : i = i'
        · simp [hi] at hr ⊢
          linarith
        · simpa [hi] using hr
      constructor
      · intro j'
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_left (ih'.2.1 j') (if j = j' then b else 0)
      · rw [ih'.2.2]
        by_cases htot : a - b + (rows.map Prod.snd).sum ≤ (columns.map Prod.snd).sum
        · rw [min_eq_left htot]
          have htot' : a + (rows.map Prod.snd).sum ≤
              b + (columns.map Prod.snd).sum := by linarith
          rw [min_eq_left htot']
          ring
        · rw [min_eq_right (le_of_not_ge htot)]
          have htot' : b + (columns.map Prod.snd).sum ≤
              a + (rows.map Prod.snd).sum := by linarith
          rw [min_eq_right htot']

/-- Completing a greedy pass respects its allocation-plus-residual margins and
transports the minimum of its two conserved totals. -/
private theorem completePrimary_margin_spec (primary : SparsePassResult K)
    (hrows : ∀ e ∈ primary.rowResiduals, 0 ≤ e.2)
    (hcolumns : ∀ e ∈ primary.columnResiduals, 0 ≤ e.2) :
    (∀ i, allocationRowMass (completePrimary primary) i ≤
      allocationRowMass primary.allocations i + rowCapacityOf primary.rowResiduals i) ∧
    (∀ j, allocationColumnMass (completePrimary primary) j ≤
      allocationColumnMass primary.allocations j +
        columnCapacityOf primary.columnResiduals j) ∧
    allocationTotalMass (completePrimary primary) =
      min
        (allocationTotalMass primary.allocations +
          (primary.rowResiduals.map Prod.snd).sum)
        (allocationTotalMass primary.allocations +
          (primary.columnResiduals.map Prod.snd).sum) := by
  have hs := completeSparse_margin_spec primary.rowResiduals primary.columnResiduals
    hrows hcolumns
  constructor
  · intro i
    have hi := hs.1 i
    simp [completePrimary, allocationRowMass] at hi ⊢
    linarith
  constructor
  · intro j
    have hj := hs.2.1 j
    simp [completePrimary, allocationColumnMass] at hj ⊢
    linarith
  · change allocationTotalMass
        (primary.allocations ++ completeSparse primary.rowResiduals primary.columnResiduals) = _
    rw [show allocationTotalMass
        (primary.allocations ++ completeSparse primary.rowResiduals primary.columnResiduals) =
          allocationTotalMass primary.allocations +
            allocationTotalMass (completeSparse primary.rowResiduals primary.columnResiduals) by
      simp [allocationTotalMass]]
    rw [hs.2.2]
    exact (min_add_add_left _ _ _).symm

private theorem indexedMasses_capacity (f : Fin K → ℝ) (i : Fin K) :
    rowCapacityOf (indexedMasses f) i = f i := by
  unfold rowCapacityOf indexedMasses
  rw [List.map_map]
  change (List.map (fun k => if k = i then f k else 0) (List.finRange K)).sum = f i
  rw [← List.sum_toFinset _ (List.nodup_finRange K)]
  simp

private theorem indexedMasses_columnCapacity (f : Fin K → ℝ) (j : Fin K) :
    columnCapacityOf (indexedMasses f) j = f j := by
  exact indexedMasses_capacity f j

private theorem indexedMasses_total (f : Fin K → ℝ) :
    ((indexedMasses f).map Prod.snd).sum = ∑ i, f i := by
  unfold indexedMasses
  rw [List.map_map]
  change (List.map f (List.finRange K)).sum = ∑ i, f i
  rw [← List.sum_toFinset _ (List.nodup_finRange K)]
  simp

private theorem rowCapacityOf_reverse (rows : List (Fin K × ℝ)) (i : Fin K) :
    rowCapacityOf rows.reverse i = rowCapacityOf rows i := by
  simp [rowCapacityOf]

private theorem columnCapacityOf_reverse (columns : List (Fin K × ℝ)) (j : Fin K) :
    columnCapacityOf columns.reverse j = columnCapacityOf columns j := by
  exact rowCapacityOf_reverse columns j

private theorem listTotal_reverse (rows : List (Fin K × ℝ)) :
    (rows.reverse.map Prod.snd).sum = (rows.map Prod.snd).sum := by
  simp

private theorem descendingPrimaryCut_eq_upperCandidate
    (c : Capacities 𝒳 K) (x : 𝒳) :
    Finset.univ.inf' Finset.univ_nonempty
        (descendingPrimaryCut (indexedMasses (c.lower x)).reverse
          (indexedMasses (c.upper x)).reverse) =
      c.benefitUpper x := by
  unfold Capacities.benefitUpper
  apply Finset.inf'_congr Finset.univ_nonempty rfl
  intro o ho
  cases o with
  | none =>
      change descendingPrimaryCut (indexedMasses (c.lower x)).reverse
          (indexedMasses (c.upper x)).reverse none = c.mass x
      simp [descendingPrimaryCut, listTotal_reverse, indexedMasses_total,
        Capacities.mass, Capacities.q0, Capacities.q1]
  | some t =>
      change descendingPrimaryCut (indexedMasses (c.lower x)).reverse
          (indexedMasses (c.upper x)).reverse (some t) =
        c.lowerLt x t + c.upperGt x t
      simp [descendingPrimaryCut, rowCapacityOf_reverse, columnCapacityOf_reverse,
        indexedMasses_capacity,
        indexedMasses_columnCapacity, Capacities.lowerLt, Capacities.upperGt]

private theorem ascendingPrimaryCut_complement_eq_lowerCandidate
    (c : Capacities 𝒳 K) (x : 𝒳) :
    Finset.univ.sup' Finset.univ_nonempty
        (fun o => c.mass x - ascendingPrimaryCut
          (indexedMasses (c.lower x)) (indexedMasses (c.upper x)) o) =
      c.benefitLower x := by
  unfold Capacities.benefitLower
  apply Finset.sup'_congr Finset.univ_nonempty rfl
  intro o ho
  cases o with
  | none =>
      change c.mass x - ascendingPrimaryCut
          (indexedMasses (c.lower x)) (indexedMasses (c.upper x)) none = 0
      simp [ascendingPrimaryCut, indexedMasses_total, Capacities.mass,
        Capacities.q0, Capacities.q1]
  | some t =>
      change c.mass x - ascendingPrimaryCut
          (indexedMasses (c.lower x)) (indexedMasses (c.upper x)) (some t) =
        c.lowerLe x t - c.upperLe x t + min (c.gap x) 0
      simp only [ascendingPrimaryCut, indexedMasses_capacity,
        indexedMasses_columnCapacity]
      rw [Capacities.mass]
      rw [min_eq_left_add_min_sub (c.q0 x) (c.q1 x)]
      simp only [Capacities.gap, Capacities.upperLe]
      have hpart := lowerLe_add_lowerGt c x t
      rw [Capacities.lowerGt] at hpart
      linarith

/-- The threshold flow lower sparse is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowLowerSparse (c : Capacities 𝒳 K) (_hValid : ValidCapacities c)
    (x : 𝒳) : List (Allocation K) :=
  completePrimary <|
    maxNonBenefitPass (indexedMasses (c.lower x)) (indexedMasses (c.upper x))

/-- The threshold flow upper sparse is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowUpperSparse (c : Capacities 𝒳 K) (_hValid : ValidCapacities c)
    (x : 𝒳) : List (Allocation K) :=
  completePrimary <|
    maxBenefitPass (indexedMasses (c.lower x)).reverse (indexedMasses (c.upper x)).reverse

/-- For the public lower construction, benefit mass is total transported mass
minus the mass emitted by the primary nonbenefit pass. -/
private theorem thresholdFlowLower_benefit_bridge
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    allocationBenefitMass (thresholdFlowLowerSparse c hValid x) =
      allocationTotalMass (thresholdFlowLowerSparse c hValid x) -
        allocationTotalMass
          (maxNonBenefitPass (indexedMasses (c.lower x))
            (indexedMasses (c.upper x))).allocations := by
  let primary := maxNonBenefitPass
    (indexedMasses (c.lower x)) (indexedMasses (c.upper x))
  have hcert := thresholdFlowLower_cut_certificate c x
  apply completePrimary_benefit_eq_total_sub_primary primary hcert.1
  intro r hr d hd
  exact lt_of_not_ge (hcert.2 r hr d hd)

/-- For the public upper construction, completion adds no benefit mass to the
mass emitted by the primary benefit pass. -/
private theorem thresholdFlowUpper_benefit_bridge
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    allocationBenefitMass (thresholdFlowUpperSparse c hValid x) =
      allocationTotalMass
        (maxBenefitPass (indexedMasses (c.lower x)).reverse
          (indexedMasses (c.upper x)).reverse).allocations := by
  let primary := maxBenefitPass
    (indexedMasses (c.lower x)).reverse (indexedMasses (c.upper x)).reverse
  have hcert := thresholdFlowUpper_cut_certificate c x
  exact completePrimary_benefit_eq_primary primary hcert.1 hcert.2

/-- The threshold flow lower is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowLower (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Coupling K :=
  sparseMatrix (thresholdFlowLowerSparse c hValid x)

/-- The threshold flow upper is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowUpper (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Coupling K :=
  sparseMatrix (thresholdFlowUpperSparse c hValid x)

/-- Both public threshold matrices are entrywise nonnegative. -/
private theorem thresholdFlow_matrices_nonnegative (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) :
    matrixNonnegative (thresholdFlowLower c hValid x) ∧
      matrixNonnegative (thresholdFlowUpper c hValid x) := by
  have hrows : ∀ e ∈ indexedMasses (c.lower x), 0 ≤ e.2 := by
    simp [indexedMasses, hValid.1 x]
  have hcolumns : ∀ e ∈ indexedMasses (c.upper x), 0 ≤ e.2 := by
    simp [indexedMasses, hValid.2 x]
  have hrowsReverse : ∀ e ∈ (indexedMasses (c.lower x)).reverse, 0 ≤ e.2 := by
    simpa using hrows
  have hcolumnsReverse : ∀ e ∈ (indexedMasses (c.upper x)).reverse, 0 ≤ e.2 := by
    simpa using hcolumns
  constructor
  · apply sparseMatrix_nonnegative
    apply completePrimary_allocations_nonnegative
    · exact maxNonBenefitPass_allocations_nonnegative _ _ hrows hcolumns
    · exact (maxNonBenefitPass_residuals_nonnegative _ _ hrows hcolumns).1
    · exact (maxNonBenefitPass_residuals_nonnegative _ _ hrows hcolumns).2
  · apply sparseMatrix_nonnegative
    apply completePrimary_allocations_nonnegative
    · exact maxBenefitPass_allocations_nonnegative _ _ hrowsReverse hcolumnsReverse
    · exact (maxBenefitPass_residuals_nonnegative _ _ hrowsReverse hcolumnsReverse).1
    · exact (maxBenefitPass_residuals_nonnegative _ _ hrowsReverse hcolumnsReverse).2

/-- Both threshold flows respect the public capacity margins and transport
exactly the smaller arm total. -/
private theorem thresholdFlow_margin_spec (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) :
    ((∀ i, rowMass (thresholdFlowLower c hValid x) i ≤ c.lower x i) ∧
      (∀ j, columnMass (thresholdFlowLower c hValid x) j ≤ c.upper x j) ∧
      totalMass (thresholdFlowLower c hValid x) = c.mass x) ∧
    ((∀ i, rowMass (thresholdFlowUpper c hValid x) i ≤ c.lower x i) ∧
      (∀ j, columnMass (thresholdFlowUpper c hValid x) j ≤ c.upper x j) ∧
      totalMass (thresholdFlowUpper c hValid x) = c.mass x) := by
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  have hrows : ∀ e ∈ rows, 0 ≤ e.2 := by
    simp [rows, indexedMasses, hValid.1 x]
  have hcolumns : ∀ e ∈ columns, 0 ≤ e.2 := by
    simp [columns, indexedMasses, hValid.2 x]
  have hrowsReverse : ∀ e ∈ rows.reverse, 0 ≤ e.2 := by simpa using hrows
  have hcolumnsReverse : ∀ e ∈ columns.reverse, 0 ≤ e.2 := by simpa using hcolumns
  constructor
  · let primary := maxNonBenefitPass rows columns
    have hres := maxNonBenefitPass_residuals_nonnegative rows columns hrows hcolumns
    have hp := completePrimary_margin_spec primary hres.1 hres.2
    have hrow := maxNonBenefitPass_row_conservation rows columns
    have hcolumn := maxNonBenefitPass_column_conservation rows columns
    have hrowTotal := maxNonBenefitPass_rowTotal_conservation rows columns
    have hcolumnTotal := maxNonBenefitPass_columnTotal_conservation rows columns
    constructor
    · intro i
      rw [thresholdFlowLower, sparseMatrix_rowMass]
      change allocationRowMass (completePrimary primary) i ≤ c.lower x i
      calc
        allocationRowMass (completePrimary primary) i ≤
            allocationRowMass primary.allocations i +
              rowCapacityOf primary.rowResiduals i := hp.1 i
        _ = rowCapacityOf rows i := hrow i
        _ = c.lower x i := by simp [rows, indexedMasses_capacity]
    constructor
    · intro j
      rw [thresholdFlowLower, sparseMatrix_columnMass]
      change allocationColumnMass (completePrimary primary) j ≤ c.upper x j
      calc
        allocationColumnMass (completePrimary primary) j ≤
            allocationColumnMass primary.allocations j +
              columnCapacityOf primary.columnResiduals j := hp.2.1 j
        _ = columnCapacityOf columns j := hcolumn j
        _ = c.upper x j := by
          simpa [columns, columnCapacityOf, rowCapacityOf] using
            indexedMasses_capacity (c.upper x) j
    · rw [thresholdFlowLower, sparseMatrix_totalMass]
      change allocationTotalMass (completePrimary primary) = c.mass x
      rw [hp.2.2, hrowTotal, hcolumnTotal]
      simp [rows, columns, indexedMasses_total, Capacities.mass,
        Capacities.q0, Capacities.q1]

  · let primary := maxBenefitPass rows.reverse columns.reverse
    have hres := maxBenefitPass_residuals_nonnegative rows.reverse columns.reverse
      hrowsReverse hcolumnsReverse
    have hp := completePrimary_margin_spec primary hres.1 hres.2
    have hrow := maxBenefitPass_row_conservation rows.reverse columns.reverse
    have hcolumn := maxBenefitPass_column_conservation rows.reverse columns.reverse
    have hrowTotal := maxBenefitPass_rowTotal_conservation rows.reverse columns.reverse
    have hcolumnTotal := maxBenefitPass_columnTotal_conservation rows.reverse columns.reverse
    constructor
    · intro i
      rw [thresholdFlowUpper, sparseMatrix_rowMass]
      change allocationRowMass (completePrimary primary) i ≤ c.lower x i
      calc
        allocationRowMass (completePrimary primary) i ≤
            allocationRowMass primary.allocations i +
              rowCapacityOf primary.rowResiduals i := hp.1 i
        _ = rowCapacityOf rows.reverse i := hrow i
        _ = rowCapacityOf rows i := rowCapacityOf_reverse rows i
        _ = c.lower x i := by simp [rows, indexedMasses_capacity]
    constructor
    · intro j
      rw [thresholdFlowUpper, sparseMatrix_columnMass]
      change allocationColumnMass (completePrimary primary) j ≤ c.upper x j
      calc
        allocationColumnMass (completePrimary primary) j ≤
            allocationColumnMass primary.allocations j +
              columnCapacityOf primary.columnResiduals j := hp.2.1 j
        _ = columnCapacityOf columns.reverse j := hcolumn j
        _ = columnCapacityOf columns j := by simp [columnCapacityOf]
        _ = c.upper x j := by
          simpa [columns, columnCapacityOf, rowCapacityOf] using
            indexedMasses_capacity (c.upper x) j
    · rw [thresholdFlowUpper, sparseMatrix_totalMass]
      change allocationTotalMass (completePrimary primary) = c.mass x
      rw [hp.2.2, hrowTotal, hcolumnTotal, listTotal_reverse, listTotal_reverse]
      simp [rows, columns, indexedMasses_total, Capacities.mass,
        Capacities.q0, Capacities.q1]

/-- The two public threshold matrices attain the lower and upper benefit
endpoints defined by the finite threshold-cut formulas. -/
private theorem thresholdFlow_benefit_spec (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) :
    benefitMass (thresholdFlowLower c hValid x) = c.benefitLower x ∧
      benefitMass (thresholdFlowUpper c hValid x) = c.benefitUpper x := by
  have htotal : allocationTotalMass (thresholdFlowLowerSparse c hValid x) =
      c.mass x := by
    rw [← sparseMatrix_totalMass]
    exact (thresholdFlow_margin_spec c hValid x).1.2.2
  constructor
  · rw [thresholdFlowLower, sparseMatrix_benefitMass,
      thresholdFlowLower_benefit_bridge c hValid x, htotal,
      thresholdFlowLower_primary_inf c hValid x,
      sub_finset_inf'_eq_sup'_sub,
      ascendingPrimaryCut_complement_eq_lowerCandidate]
  · rw [thresholdFlowUpper, sparseMatrix_benefitMass,
      thresholdFlowUpper_benefit_bridge c hValid x,
      thresholdFlowUpper_primary_inf c hValid x,
      descendingPrimaryCut_eq_upperCandidate]

/-- Both threshold matrices are feasible and attain their respective benefit endpoints, without requiring a compatible-baseline witness. Given [the stated hypotheses](hyp:hValid), [the stated conclusion follows](goal). -/
theorem thresholdFlow_endpoint_spec (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) (x : 𝒳) :
    thresholdFlowLower c hValid x ∈ branchFreePolytope c hValid x ∧
    benefitMass (thresholdFlowLower c hValid x) = c.benefitLower x ∧
    thresholdFlowUpper c hValid x ∈ branchFreePolytope c hValid x ∧
    benefitMass (thresholdFlowUpper c hValid x) = c.benefitUpper x := by
  have hnonnegative := thresholdFlow_matrices_nonnegative c hValid x
  have hmargins := thresholdFlow_margin_spec c hValid x
  have hbenefit := thresholdFlow_benefit_spec c hValid x
  constructor
  · exact ⟨hnonnegative.1, hmargins.1⟩
  exact ⟨hbenefit.1, ⟨hnonnegative.2, hmargins.2⟩, hbenefit.2⟩

/-- The selection/outcome table within one treatment principal stratum. -/
abbrev PrincipalStratumComponent (K : ℕ) :=
  Bool → Bool → Fin K → Fin K → ℝ

/-- Conditional complier mass in a baseline full law. -/
noncomputable def baselineComplierMass {P₀ : POSystem.{uV, uVal, uOmega}}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) : ℝ :=
  conditionalReal W.system.μ W.slate.complierEvent (W.slate.xEvent x)

/-- The baseline never-taker selection/outcome component in a cell. -/
noncomputable def baselineNeverTakerComponent {P₀ : POSystem.{uV, uVal, uOmega}}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) : PrincipalStratumComponent K :=
  fun s0 s1 y0 y1 => conditionalReal W.system.μ
    {ω | W.slate.D0 ω = false ∧ W.slate.D1 ω = false ∧
      W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
      W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1}
    (W.slate.xEvent x)

/-- The baseline always-taker selection/outcome component in a cell. -/
noncomputable def baselineAlwaysTakerComponent {P₀ : POSystem.{uV, uVal, uOmega}}
    (W : FullLawCandidate P₀ 𝒳 K) (x : 𝒳) : PrincipalStratumComponent K :=
  fun s0 s1 y0 y1 => conditionalReal W.system.μ
    {ω | W.slate.D0 ω = true ∧ W.slate.D1 ω = true ∧
      W.slate.S0 ω = s0 ∧ W.slate.S1 ω = s1 ∧
      W.slate.Y0 ω = y0 ∧ W.slate.Y1 ω = y1}
    (W.slate.xEvent x)

/-- A baseline law compatible with the supplied observed law and capacities.
It exposes the conditional complier mass and the two noncomplier components
that the latent completion must preserve. -/
structure CompatibleBaseline (P₀ : POSystem.{uV, uVal, uOmega})
    (Pobs : Measure (ObservedDatum 𝒳 K)) (c : Capacities 𝒳 K) where
  law : FullLawCandidate P₀ 𝒳 K
  feasible : FullLawFeasible Pobs law
  capacities_eq : observableCapacities Pobs = c
  complierMass : 𝒳 → ℝ
  complierMass_eq : ∀ x, complierMass x = baselineComplierMass law x
  qMax_le_complierMass : ∀ x, max (c.q0 x) (c.q1 x) ≤ complierMass x
  neverTakerComponent : 𝒳 → PrincipalStratumComponent K
  neverTaker_eq : ∀ x, neverTakerComponent x = baselineNeverTakerComponent law x
  alwaysTakerComponent : 𝒳 → PrincipalStratumComponent K
  alwaysTaker_eq : ∀ x, alwaysTakerComponent x = baselineAlwaysTakerComponent law x

/-- Residual selected-complier strata together with the baseline law and its
definitionally unchanged never-taker and always-taker components. -/
structure ThresholdLatentCompletion (P₀ : POSystem.{uV, uVal, uOmega})
    (Pobs : Measure (ObservedDatum 𝒳 K)) (c : Capacities 𝒳 K) where
  survivor : Coupling K
  selectedOnlyUnderZero : Fin K → ℝ
  selectedOnlyUnderOne : Fin K → ℝ
  neverSelectedMass : ℝ
  neverTakerComponent : PrincipalStratumComponent K
  alwaysTakerComponent : PrincipalStratumComponent K
  baselineLaw : FullLawCandidate P₀ 𝒳 K
  baselineCompatible : FullLawFeasible Pobs baselineLaw

/-- The threshold latent completion is the measure produced by the stated finite slate-benefit construction. -/
def thresholdLatentCompletion {P₀ : POSystem.{uV, uVal, uOmega}}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (_hValid : ValidCapacities c)
    (x : 𝒳) (γ : Coupling K) : ThresholdLatentCompletion P₀ Pobs c where
  survivor := γ
  selectedOnlyUnderZero := fun i => if c.gap x < 0 then c.lower x i - rowMass γ i else 0
  selectedOnlyUnderOne := fun j => if 0 < c.gap x then c.upper x j - columnMass γ j else 0
  neverSelectedMass := baseline.complierMass x - max (c.q0 x) (c.q1 x)
  neverTakerComponent := baseline.neverTakerComponent x
  alwaysTakerComponent := baseline.alwaysTakerComponent x
  baselineLaw := baseline.law
  baselineCompatible := baseline.feasible

/-- A threshold flow result records the data and compatibility conditions used by the slate-benefit partial-transport construction. -/
structure ThresholdFlowResult (P₀ : POSystem.{uV, uVal, uOmega})
    (Pobs : Measure (ObservedDatum 𝒳 K)) (c : Capacities 𝒳 K) where
  lower : ThresholdLatentCompletion P₀ Pobs c
  upper : ThresholdLatentCompletion P₀ Pobs c

/-- Total lower- and upper-endpoint flows, including the one-sided residual
selection strata, never-selected mass, and unchanged baseline-law component. -/
-- @node: def:threshold-flow-construction
noncomputable def thresholdFlow {P₀ : POSystem.{uV, uVal, uOmega}}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (x : 𝒳) : ThresholdFlowResult P₀ Pobs c where
  lower := thresholdLatentCompletion baseline hValid x (thresholdFlowLower c hValid x)
  upper := thresholdLatentCompletion baseline hValid x (thresholdFlowUpper c hValid x)

/-- The threshold construction returns feasible endpoint-attaining survivor couplings while preserving the compatible baseline's noncomplier components. Given [the stated hypotheses](hyp:hValid), [the stated conclusion follows](goal). -/
theorem thresholdFlow_spec {P₀ : POSystem.{uV, uVal, uOmega}}
    {Pobs : Measure (ObservedDatum 𝒳 K)} {c : Capacities 𝒳 K}
    (baseline : CompatibleBaseline P₀ Pobs c) (hValid : ValidCapacities c)
    (x : 𝒳) :
    let out := thresholdFlow baseline hValid x
    out.lower.survivor ∈ branchFreePolytope c hValid x ∧
    benefitMass out.lower.survivor = c.benefitLower x ∧
    out.upper.survivor ∈ branchFreePolytope c hValid x ∧
    benefitMass out.upper.survivor = c.benefitUpper x ∧
    out.lower.neverSelectedMass =
      baseline.complierMass x - max (c.q0 x) (c.q1 x) ∧
    out.upper.neverSelectedMass =
      baseline.complierMass x - max (c.q0 x) (c.q1 x) ∧
    out.lower.neverTakerComponent = baseline.neverTakerComponent x ∧
    out.upper.neverTakerComponent = baseline.neverTakerComponent x ∧
    out.lower.alwaysTakerComponent = baseline.alwaysTakerComponent x ∧
    out.upper.alwaysTakerComponent = baseline.alwaysTakerComponent x := by
  have hnonnegative := thresholdFlow_matrices_nonnegative c hValid x
  have hmargins := thresholdFlow_margin_spec c hValid x
  have hbenefit := thresholdFlow_benefit_spec c hValid x
  have hlower : thresholdFlowLower c hValid x ∈ branchFreePolytope c hValid x := by
    change matrixNonnegative (thresholdFlowLower c hValid x) ∧
      (∀ i, rowMass (thresholdFlowLower c hValid x) i ≤ c.lower x i) ∧
      (∀ j, columnMass (thresholdFlowLower c hValid x) j ≤ c.upper x j) ∧
      totalMass (thresholdFlowLower c hValid x) = c.mass x
    exact ⟨hnonnegative.1, hmargins.1⟩
  have hupper : thresholdFlowUpper c hValid x ∈ branchFreePolytope c hValid x := by
    change matrixNonnegative (thresholdFlowUpper c hValid x) ∧
      (∀ i, rowMass (thresholdFlowUpper c hValid x) i ≤ c.lower x i) ∧
      (∀ j, columnMass (thresholdFlowUpper c hValid x) j ≤ c.upper x j) ∧
      totalMass (thresholdFlowUpper c hValid x) = c.mass x
    exact ⟨hnonnegative.2, hmargins.2⟩
  exact ⟨hlower, hbenefit.1, hupper, hbenefit.2, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An output bundled with the number of arithmetic operations and comparisons
performed by its costed implementation. -/
structure Costed (α : Type*) where
  value : α
  operations : ℕ

private def prefixInclusive (values : List ℝ) : List ℝ :=
  (values.scanl (· + ·) 0).drop 1

private def prefixStrict (values : List ℝ) : List ℝ :=
  (values.scanl (· + ·) 0).take values.length

private def strictUpperTail (values : List ℝ) : List ℝ :=
  ((values.reverse.scanl (· + ·) 0).take values.length).reverse

private theorem foldl_add_eq_add_sum (values : List ℝ) (a : ℝ) :
    values.foldl (· + ·) a = a + values.sum := by
  induction values generalizing a with
  | nil => simp
  | cons v values ih =>
      rw [List.foldl_cons, ih]
      simp only [List.sum_cons]
      ring

/-- Each inclusive scan entry is the sum through the corresponding list
position. -/
private theorem prefixInclusive_getElem (values : List ℝ) (n : ℕ)
    (hn : n < (prefixInclusive values).length) :
    (prefixInclusive values)[n] = (values.take (n + 1)).sum := by
  unfold prefixInclusive at hn ⊢
  have hn' : 1 + n < (values.scanl (· + ·) 0).length := by
    rw [List.length_drop, List.length_scanl] at hn
    rw [List.length_scanl]
    omega
  rw [List.getElem_drop, List.getElem_scanl (h := hn')]
  simpa [foldl_add_eq_add_sum, add_comm]

/-- Each strict-prefix scan entry is the sum before the corresponding list
position. -/
private theorem prefixStrict_getElem (values : List ℝ) (n : ℕ)
    (hn : n < (prefixStrict values).length) :
    (prefixStrict values)[n] = (values.take n).sum := by
  unfold prefixStrict at hn ⊢
  rw [List.getElem_take, List.getElem_scanl]
  simpa [foldl_add_eq_add_sum]

/-- Each reverse-prefix scan entry is the sum strictly after the
corresponding list position. -/
private theorem strictUpperTail_getElem (values : List ℝ) (n : ℕ)
    (hn : n < (strictUpperTail values).length) :
    (strictUpperTail values)[n] = (values.drop (n + 1)).sum := by
  have hnValues : n < values.length := by
    simpa [strictUpperTail] using hn
  unfold strictUpperTail at hn ⊢
  rw [List.getElem_reverse]
  have htakeLength :
      ((values.reverse.scanl (· + ·) 0).take values.length).length = values.length := by
    simp
  simp only [htakeLength]
  rw [List.getElem_take, List.getElem_scanl]
  rw [foldl_add_eq_add_sum]
  simp only [zero_add]
  rw [List.take_reverse, List.sum_reverse]
  congr 2
  omega

private theorem mem_take_finRange_iff {n : ℕ} (i : Fin K) :
    i ∈ (List.finRange K).take n ↔ i.val < n := by
  rw [List.mem_take_iff_getElem]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hval := congrArg Fin.val hji
    simp at hval
    omega
  · intro hi
    refine ⟨i.val, ?_, ?_⟩
    · simp
      omega
    · apply Fin.ext
      simp

private theorem mem_drop_finRange_iff {n : ℕ} (i : Fin K) :
    i ∈ (List.finRange K).drop n ↔ n ≤ i.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, hj, hji⟩
    have hval := congrArg Fin.val hji
    simp at hval
    omega
  · intro hi
    refine ⟨i.val - n, ?_, ?_⟩
    · simp
      omega
    · apply Fin.ext
      simp
      omega

/-- Taking through index `t` in `finRange` gives the inclusive finite sum. -/
private theorem finRange_map_take_succ_sum (f : Fin K → ℝ) (t : Fin K) :
    (((List.finRange K).map f).take (t.val + 1)).sum =
      ∑ i with i ≤ t, f i := by
  rw [show ((List.finRange K).map f).take (t.val + 1) =
      ((List.finRange K).take (t.val + 1)).map f by simp]
  rw [← List.sum_toFinset _ (List.nodup_finRange K).take]
  apply Finset.sum_congr
  · ext i
    simp [mem_take_finRange_iff]
  · simp

/-- Taking before index `t` in `finRange` gives the strict-prefix finite sum. -/
private theorem finRange_map_take_sum (f : Fin K → ℝ) (t : Fin K) :
    (((List.finRange K).map f).take t.val).sum =
      ∑ i with i < t, f i := by
  rw [show ((List.finRange K).map f).take t.val =
      ((List.finRange K).take t.val).map f by simp]
  rw [← List.sum_toFinset _ (List.nodup_finRange K).take]
  apply Finset.sum_congr
  · ext i
    simp [mem_take_finRange_iff]
  · simp

/-- Dropping through index `t` in `finRange` gives the strict upper-tail
finite sum. -/
private theorem finRange_map_drop_succ_sum (f : Fin K → ℝ) (t : Fin K) :
    (((List.finRange K).map f).drop (t.val + 1)).sum =
      ∑ i with t < i, f i := by
  rw [show ((List.finRange K).map f).drop (t.val + 1) =
      ((List.finRange K).drop (t.val + 1)).map f by simp]
  rw [← List.sum_toFinset _ (List.nodup_finRange K).drop]
  apply Finset.sum_congr
  · ext i
    simp [mem_drop_finRange_iff]
  · simp

private theorem finRange_map_sum (f : Fin K → ℝ) :
    ((List.finRange K).map f).sum = ∑ i, f i := by
  rw [← List.sum_toFinset _ (List.nodup_finRange K)]
  simp

private theorem prefixInclusive_length (values : List ℝ) :
    (prefixInclusive values).length = values.length := by
  simp [prefixInclusive]

private theorem prefixStrict_length (values : List ℝ) :
    (prefixStrict values).length = values.length := by
  simp [prefixStrict]

private theorem strictUpperTail_length (values : List ℝ) :
    (strictUpperTail values).length = values.length := by
  simp [strictUpperTail]

/-- All lower candidates from a single pair of prefix scans. -/
private def lowerThresholdValues (c : Capacities 𝒳 K) (x : 𝒳) : List ℝ :=
  let lower := (List.finRange K).map (c.lower x)
  let upper := (List.finRange K).map (c.upper x)
  let gapPart := min (upper.sum - lower.sum) 0
  0 :: List.zipWith (fun l h => l - h + gapPart)
    (prefixInclusive lower) (prefixInclusive upper)

/-- All upper candidates from one prefix and one reverse-prefix scan. -/
private def upperThresholdValues (c : Capacities 𝒳 K) (x : 𝒳) : List ℝ :=
  let lower := (List.finRange K).map (c.lower x)
  let upper := (List.finRange K).map (c.upper x)
  let mass := min lower.sum upper.sum
  mass :: List.zipWith (· + ·) (prefixStrict lower) (strictUpperTail upper)

/-- The lower scan list consists exactly of the zero candidate followed by
the inclusive-cut candidates in outcome order. -/
private theorem lowerThresholdValues_eq_candidates
    (c : Capacities 𝒳 K) (x : 𝒳) :
    lowerThresholdValues c x =
      0 :: (List.finRange K).map (fun t =>
        c.lowerLe x t - c.upperLe x t + min (c.gap x) 0) := by
  dsimp [lowerThresholdValues]
  congr 1
  apply List.ext_getElem
  · simp [prefixInclusive_length]
  · intro n hnLeft hnRight
    rw [List.getElem_zipWith, List.getElem_map]
    rw [prefixInclusive_getElem, prefixInclusive_getElem]
    let t : Fin K := (List.finRange K)[n]'(by simpa using hnRight)
    have ht : t.val = n := by simp [t]
    have hl := finRange_map_take_succ_sum (c.lower x) t
    have hu := finRange_map_take_succ_sum (c.upper x) t
    simp only [ht] at hl hu
    rw [hl, hu]
    simp only [Capacities.lowerLe, Capacities.upperLe]
    rw [finRange_map_sum, finRange_map_sum]
    simp only [Capacities.gap, Capacities.q0, Capacities.q1]
    simpa [t]

/-- The upper scan list consists exactly of the total-mass candidate followed
by the strict-prefix/strict-tail candidates in outcome order. -/
private theorem upperThresholdValues_eq_candidates
    (c : Capacities 𝒳 K) (x : 𝒳) :
    upperThresholdValues c x =
      c.mass x :: (List.finRange K).map (fun t =>
        c.lowerLt x t + c.upperGt x t) := by
  dsimp [upperThresholdValues]
  rw [finRange_map_sum, finRange_map_sum]
  simp only [Capacities.mass, Capacities.q0, Capacities.q1]
  congr 1
  apply List.ext_getElem
  · simp [prefixStrict_length, strictUpperTail_length]
  · intro n hnLeft hnRight
    rw [List.getElem_zipWith, List.getElem_map]
    rw [prefixStrict_getElem, strictUpperTail_getElem]
    let t : Fin K := (List.finRange K)[n]'(by simpa using hnRight)
    have ht : t.val = n := by simp [t]
    have hl := finRange_map_take_sum (c.lower x) t
    have hu := finRange_map_drop_succ_sum (c.upper x) t
    simp only [ht] at hl hu
    rw [hl, hu]
    simp only [Capacities.lowerLt, Capacities.upperGt]
    simpa [t]

private theorem foldl_max_mem_and_bounds (values : List ℝ) (a : ℝ) :
    (List.foldl max a values ∈ a :: values) ∧
      ∀ b ∈ a :: values, b ≤ List.foldl max a values := by
  induction values generalizing a with
  | nil => simp
  | cons b values ih =>
      have h := ih (max a b)
      simp only [List.foldl_cons, List.mem_cons] at h ⊢
      constructor
      · rcases h.1 with hEq | hmem
        · rw [hEq]
          by_cases hab : a ≤ b
          · exact Or.inr (Or.inl (max_eq_right hab))
          · exact Or.inl (max_eq_left (le_of_not_ge hab))
        · exact Or.inr (Or.inr hmem)
      · intro x hx
        rcases hx with rfl | rfl | hx
        · exact (le_max_left _ _).trans (h.2 _ (Or.inl rfl))
        · exact (le_max_right _ _).trans (h.2 _ (Or.inl rfl))
        · exact h.2 x (Or.inr hx)

private theorem foldl_min_mem_and_bounds (values : List ℝ) (a : ℝ) :
    (List.foldl min a values ∈ a :: values) ∧
      ∀ b ∈ a :: values, List.foldl min a values ≤ b := by
  induction values generalizing a with
  | nil => simp
  | cons b values ih =>
      have h := ih (min a b)
      simp only [List.foldl_cons, List.mem_cons] at h ⊢
      constructor
      · rcases h.1 with hEq | hmem
        · rw [hEq]
          by_cases hab : a ≤ b
          · exact Or.inl (min_eq_left hab)
          · exact Or.inr (Or.inl (min_eq_right (le_of_not_ge hab)))
        · exact Or.inr (Or.inr hmem)
      · intro x hx
        rcases hx with rfl | rfl | hx
        · exact (h.2 _ (Or.inl rfl)).trans (min_le_left _ _)
        · exact (h.2 _ (Or.inl rfl)).trans (min_le_right _ _)
        · exact h.2 x (Or.inr hx)

private theorem foldl_max_finRange_eq_sup' (head : ℝ) (f : Fin K → ℝ) :
    (head :: (List.finRange K).map f).foldl max head =
      Finset.univ.sup' Finset.univ_nonempty
        (fun t : Option (Fin K) => match t with
          | none => head
          | some i => f i) := by
  let result := (head :: (List.finRange K).map f).foldl max head
  have h := foldl_max_mem_and_bounds (head :: (List.finRange K).map f) head
  change result ∈ head :: head :: (List.finRange K).map f ∧
    (∀ b ∈ head :: head :: (List.finRange K).map f, b ≤ result) at h
  change result = _
  let g : Option (Fin K) → ℝ := fun t => match t with
    | none => head
    | some i => f i
  change result = Finset.univ.sup' Finset.univ_nonempty g
  apply le_antisymm
  · by_cases hhead : result = head
    · exact hhead.trans_le (Finset.le_sup' g (Finset.mem_univ none))
    · have htail := (List.mem_cons.mp h.1).resolve_left hhead
      have hvalue := (List.mem_cons.mp htail).resolve_left hhead
      obtain ⟨i, hi, hfi⟩ := List.mem_map.mp hvalue
      exact hfi.symm.trans_le (Finset.le_sup' g (Finset.mem_univ (some i)))
  · apply Finset.sup'_le
    intro t ht
    cases t with
    | none => simpa [g] using h.2 head (by simp)
    | some i => simpa [g] using h.2 (f i) (by simp)

private theorem foldl_min_finRange_eq_inf' (head : ℝ) (f : Fin K → ℝ) :
    (head :: (List.finRange K).map f).foldl min head =
      Finset.univ.inf' Finset.univ_nonempty
        (fun t : Option (Fin K) => match t with
          | none => head
          | some i => f i) := by
  have h := foldl_min_mem_and_bounds (head :: (List.finRange K).map f) head
  let result := (head :: (List.finRange K).map f).foldl min head
  change result ∈ head :: head :: (List.finRange K).map f ∧
    (∀ b ∈ head :: head :: (List.finRange K).map f, result ≤ b) at h
  change result = _
  let g : Option (Fin K) → ℝ := fun t => match t with
    | none => head
    | some i => f i
  change result = Finset.univ.inf' Finset.univ_nonempty g
  apply le_antisymm
  · apply Finset.le_inf'
    intro t ht
    cases t with
    | none => simpa [g] using h.2 head (by simp)
    | some i => simpa [g] using h.2 (f i) (by simp)
  · by_cases hhead : result = head
    · exact (Finset.inf'_le g (Finset.mem_univ none)).trans hhead.symm.le
    · have htail := (List.mem_cons.mp h.1).resolve_left hhead
      have hvalue := (List.mem_cons.mp htail).resolve_left hhead
      obtain ⟨i, hi, hfi⟩ := List.mem_map.mp hvalue
      exact (Finset.inf'_le g (Finset.mem_univ (some i))).trans hfi.le

/-- The costed threshold scan uses linear prefix/tail scans and then folds the
candidate lists by maximum and minimum. -/
def costedThresholdCuts (c : Capacities 𝒳 K) (x : 𝒳) : Costed (ℝ × ℝ) :=
  let lowerValues := lowerThresholdValues c x
  let upperValues := upperThresholdValues c x
  { value := (lowerValues.foldl max 0, upperValues.foldl min (c.mass x))
    operations := 12 * K + 8 }

/-- The costed scan computes exactly the two public threshold endpoint functionals. [the stated conclusion follows](goal). -/
theorem costedThresholdCuts_value (c : Capacities 𝒳 K) (x : 𝒳) :
    (costedThresholdCuts c x).value = (c.benefitLower x, c.benefitUpper x) := by
  rw [show (costedThresholdCuts c x).value =
      ((lowerThresholdValues c x).foldl max 0,
        (upperThresholdValues c x).foldl min (c.mass x)) by rfl]
  rw [lowerThresholdValues_eq_candidates, upperThresholdValues_eq_candidates]
  rw [foldl_max_finRange_eq_sup', foldl_min_finRange_eq_inf']
  rfl

private def maxBenefitSparseOperations :
    List (Fin K × ℝ) → List (Fin K × ℝ) → ℕ
  | [], _ => 1
  | _, [] => 1
  | (i, a) :: rows, (j, b) :: columns =>
      if i < j then
        if a ≤ b then 5 + maxBenefitSparseOperations rows ((j, b - min a b) :: columns)
        else 5 + maxBenefitSparseOperations ((i, a - min a b) :: rows) columns
      else 2 + maxBenefitSparseOperations rows ((j, b) :: columns)
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

private def maxNonBenefitSparseOperations :
    List (Fin K × ℝ) → List (Fin K × ℝ) → ℕ
  | [], _ => 1
  | _, [] => 1
  | (i, a) :: rows, (j, b) :: columns =>
      if j ≤ i then
        if a ≤ b then 5 + maxNonBenefitSparseOperations rows ((j, b - min a b) :: columns)
        else 5 + maxNonBenefitSparseOperations ((i, a - min a b) :: rows) columns
      else 2 + maxNonBenefitSparseOperations rows ((j, b) :: columns)
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

private def completeSparseOperations :
    List (Fin K × ℝ) → List (Fin K × ℝ) → ℕ
  | [], _ => 1
  | _, [] => 1
  | (i, a) :: rows, (j, b) :: columns =>
      if a ≤ b then 4 + completeSparseOperations rows ((j, b - min a b) :: columns)
      else 4 + completeSparseOperations ((i, a - min a b) :: rows) columns
termination_by rows columns => rows.length + columns.length
decreasing_by all_goals simp_wf

-- @node: maxBenefitSparseOperations_le
private theorem maxBenefitSparseOperations_le
    (rows columns : List (Fin K × ℝ)) :
    maxBenefitSparseOperations rows columns ≤ 5 * (rows.length + columns.length) + 1 := by
  induction rows, columns using maxBenefitSparseOperations.induct <;>
    simp_all only [maxBenefitSparseOperations, if_pos, if_neg, if_true, if_false,
      List.length_cons] <;>
    omega

-- @node: maxNonBenefitSparseOperations_le
private theorem maxNonBenefitSparseOperations_le
    (rows columns : List (Fin K × ℝ)) :
    maxNonBenefitSparseOperations rows columns ≤ 5 * (rows.length + columns.length) + 1 := by
  induction rows, columns using maxNonBenefitSparseOperations.induct <;>
    simp_all only [maxNonBenefitSparseOperations, if_pos, if_neg, if_true, if_false,
      List.length_cons] <;>
    omega

-- @node: completeSparseOperations_le
private theorem completeSparseOperations_le
    (rows columns : List (Fin K × ℝ)) :
    completeSparseOperations rows columns ≤ 4 * (rows.length + columns.length) + 1 := by
  induction rows, columns using completeSparseOperations.induct <;>
    simp_all only [completeSparseOperations, if_pos, if_neg, if_true, if_false,
      List.length_cons] <;>
    omega

-- @node: maxBenefitPass_residual_length_le
private theorem maxBenefitPass_residual_length_le
    (rows columns : List (Fin K × ℝ)) :
    (maxBenefitPass rows columns).rowResiduals.length +
        (maxBenefitPass rows columns).columnResiduals.length ≤
      rows.length + columns.length := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all only [maxBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

-- @node: maxNonBenefitPass_residual_length_le
private theorem maxNonBenefitPass_residual_length_le
    (rows columns : List (Fin K × ℝ)) :
    (maxNonBenefitPass rows columns).rowResiduals.length +
        (maxNonBenefitPass rows columns).columnResiduals.length ≤
      rows.length + columns.length := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all only [maxNonBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem completeSparse_length_lt_input_length
    (rows columns : List (Fin K × ℝ))
    (hpos : 0 < rows.length + columns.length) :
    (completeSparse rows columns).length < rows.length + columns.length := by
  induction rows, columns using completeSparse.induct <;>
    simp_all only [completeSparse, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem maxBenefitPass_trace_length_le
    (rows columns : List (Fin K × ℝ)) :
    (maxBenefitPass rows columns).allocations.length +
        (maxBenefitPass rows columns).rowResiduals.length +
        (maxBenefitPass rows columns).columnResiduals.length ≤
      rows.length + columns.length := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all only [maxBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem maxNonBenefitPass_trace_length_le
    (rows columns : List (Fin K × ℝ)) :
    (maxNonBenefitPass rows columns).allocations.length +
        (maxNonBenefitPass rows columns).rowResiduals.length +
        (maxNonBenefitPass rows columns).columnResiduals.length ≤
      rows.length + columns.length := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all only [maxNonBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem maxBenefitPass_residual_length_pos
    (rows columns : List (Fin K × ℝ))
    (hpos : 0 < rows.length + columns.length) :
    0 < (maxBenefitPass rows columns).rowResiduals.length +
      (maxBenefitPass rows columns).columnResiduals.length := by
  induction rows, columns using maxBenefitPass.induct <;>
    simp_all only [maxBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem maxNonBenefitPass_residual_length_pos
    (rows columns : List (Fin K × ℝ))
    (hpos : 0 < rows.length + columns.length) :
    0 < (maxNonBenefitPass rows columns).rowResiduals.length +
      (maxNonBenefitPass rows columns).columnResiduals.length := by
  induction rows, columns using maxNonBenefitPass.induct <;>
    simp_all only [maxNonBenefitPass, if_pos, if_neg, if_true, if_false,
      List.length_nil, List.length_cons] <;>
    omega

private theorem completePrimary_maxBenefitPass_length_lt
    (rows columns : List (Fin K × ℝ))
    (hpos : 0 < rows.length + columns.length) :
    (completePrimary (maxBenefitPass rows columns)).length <
      rows.length + columns.length := by
  let primary := maxBenefitPass rows columns
  have htrace := maxBenefitPass_trace_length_le rows columns
  have hres := maxBenefitPass_residual_length_pos rows columns hpos
  have hcomplete := completeSparse_length_lt_input_length
    primary.rowResiduals primary.columnResiduals hres
  dsimp [primary] at htrace hcomplete
  simp only [completePrimary, List.length_append]
  omega

private theorem completePrimary_maxNonBenefitPass_length_lt
    (rows columns : List (Fin K × ℝ))
    (hpos : 0 < rows.length + columns.length) :
    (completePrimary (maxNonBenefitPass rows columns)).length <
      rows.length + columns.length := by
  let primary := maxNonBenefitPass rows columns
  have htrace := maxNonBenefitPass_trace_length_le rows columns
  have hres := maxNonBenefitPass_residual_length_pos rows columns hpos
  have hcomplete := completeSparse_length_lt_input_length
    primary.rowResiduals primary.columnResiduals hres
  dsimp [primary] at htrace hcomplete
  simp only [completePrimary, List.length_append]
  omega

/-- The lower threshold coupling has at most `2 * K - 1` positive cells. Given [the stated hypotheses](hyp:hK,hValid), [the stated conclusion follows](goal). -/
theorem thresholdFlowLower_positiveSupportCard_le (hK : 3 ≤ K)
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    positiveSupportCard (thresholdFlowLower c hValid x) ≤ 2 * K - 1 := by
  rw [thresholdFlowLower]
  calc
    positiveSupportCard (sparseMatrix (thresholdFlowLowerSparse c hValid x)) ≤
        (thresholdFlowLowerSparse c hValid x).length :=
      positiveSupportCard_sparseMatrix_le_length _
    _ ≤ 2 * K - 1 := by
      have hlt := completePrimary_maxNonBenefitPass_length_lt
        (indexedMasses (c.lower x)) (indexedMasses (c.upper x)) (by
          simp [indexedMasses]
          omega)
      have hlt' : (thresholdFlowLowerSparse c hValid x).length < 2 * K := by
        simpa [thresholdFlowLowerSparse, indexedMasses, two_mul] using hlt
      exact Nat.le_sub_one_of_lt hlt'

/-- The upper threshold coupling has at most `2 * K - 1` positive cells. Given [the stated hypotheses](hyp:hK,hValid), [the stated conclusion follows](goal). -/
theorem thresholdFlowUpper_positiveSupportCard_le (hK : 3 ≤ K)
    (c : Capacities 𝒳 K) (hValid : ValidCapacities c) (x : 𝒳) :
    positiveSupportCard (thresholdFlowUpper c hValid x) ≤ 2 * K - 1 := by
  rw [thresholdFlowUpper]
  calc
    positiveSupportCard (sparseMatrix (thresholdFlowUpperSparse c hValid x)) ≤
        (thresholdFlowUpperSparse c hValid x).length :=
      positiveSupportCard_sparseMatrix_le_length _
    _ ≤ 2 * K - 1 := by
      have hlt := completePrimary_maxBenefitPass_length_lt
        (indexedMasses (c.lower x)).reverse (indexedMasses (c.upper x)).reverse (by
          simp [indexedMasses]
          omega)
      have hlt' : (thresholdFlowUpperSparse c hValid x).length < 2 * K := by
        simpa [thresholdFlowUpperSparse, indexedMasses, two_mul] using hlt
      exact Nat.le_sub_one_of_lt hlt'

/-- A capacity-magnitude-independent operation budget for the fixed-schedule
sparse implementation. It covers the prefix/tail scans, both nested-graph
passes, residual propagation within those passes, both complete transports,
and final folds. Unused slots are padding, so the charged count is independent
of comparison outcomes. -/
def sparseCellOperationBudget (K : ℕ) : ℕ := 64 * K + 32

/-- The unpadded work counter mirrors every arithmetic operation and comparison
in the residual-carrying implementation. -/
def sparseCellActualOperations (c : Capacities 𝒳 K) (x : 𝒳) : ℕ :=
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  let lowerPrimary := maxNonBenefitPass rows columns
  let upperPrimary := maxBenefitPass rows.reverse columns.reverse
  (costedThresholdCuts c x).operations +
    maxNonBenefitSparseOperations rows columns +
    maxBenefitSparseOperations rows.reverse columns.reverse +
    completeSparseOperations lowerPrimary.rowResiduals lowerPrimary.columnResiduals +
    completeSparseOperations upperPrimary.rowResiduals upperPrimary.columnResiduals

/-- The fixed schedule covers every operation in the residual-carrying sparse implementation. Given [the stated hypotheses](hyp:hK), [the stated conclusion follows](goal). -/
-- @node: sparseCellActualOperations_le_budget
theorem sparseCellActualOperations_le_budget (hK : 3 ≤ K)
    (c : Capacities 𝒳 K) (x : 𝒳) :
    sparseCellActualOperations c x ≤ sparseCellOperationBudget K := by
  let rows := indexedMasses (c.lower x)
  let columns := indexedMasses (c.upper x)
  let lowerPrimary := maxNonBenefitPass rows columns
  let upperPrimary := maxBenefitPass rows.reverse columns.reverse
  have hRows : rows.length = K := by simp [rows, indexedMasses]
  have hColumns : columns.length = K := by simp [columns, indexedMasses]
  have hLowerResidual :
      lowerPrimary.rowResiduals.length + lowerPrimary.columnResiduals.length ≤ 2 * K := by
    change (maxNonBenefitPass rows columns).rowResiduals.length +
      (maxNonBenefitPass rows columns).columnResiduals.length ≤ 2 * K
    have h := maxNonBenefitPass_residual_length_le rows columns
    omega
  have hUpperResidual :
      upperPrimary.rowResiduals.length + upperPrimary.columnResiduals.length ≤ 2 * K := by
    change (maxBenefitPass rows.reverse columns.reverse).rowResiduals.length +
      (maxBenefitPass rows.reverse columns.reverse).columnResiduals.length ≤ 2 * K
    have h := maxBenefitPass_residual_length_le rows.reverse columns.reverse
    simp only [List.length_reverse] at h
    omega
  have hLowerPass := maxNonBenefitSparseOperations_le rows columns
  have hUpperPass := maxBenefitSparseOperations_le rows.reverse columns.reverse
  have hLowerComplete := completeSparseOperations_le
    lowerPrimary.rowResiduals lowerPrimary.columnResiduals
  have hUpperComplete := completeSparseOperations_le
    upperPrimary.rowResiduals upperPrimary.columnResiduals
  simp only [List.length_reverse] at hUpperPass
  simp only [sparseCellActualOperations, costedThresholdCuts, Costed.operations,
    sparseCellOperationBudget]
  dsimp [rows, columns, lowerPrimary, upperPrimary] at *
  simp only [indexedMasses, List.length_map, List.length_finRange, List.length_reverse] at *
  omega

/-- A costed cell implementation. Its value contains the evaluated threshold
formulas and the actual sparse allocation traces. The charged fixed schedule
dominates the fully enumerated unpadded work and depends only on `K`. -/
def costedSparseThresholdFlow (c : Capacities 𝒳 K) (hValid : ValidCapacities c)
    (x : 𝒳) : Costed ((ℝ × ℝ) × (List (Allocation K) × List (Allocation K))) :=
  let lower := thresholdFlowLowerSparse c hValid x
  let upper := thresholdFlowUpperSparse c hValid x
  let cuts := costedThresholdCuts c x
  { value := (cuts.value, (lower, upper))
    operations := sparseCellOperationBudget K }

/-- The threshold flow cost for is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowCostFor (c : Capacities 𝒳 K) (hValid : ValidCapacities c) : ℕ :=
  ∑ x, (costedSparseThresholdFlow c hValid x).operations

/-- The threshold flow actual cost for is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def thresholdFlowActualCostFor (c : Capacities 𝒳 K) : ℕ :=
  ∑ x, sparseCellActualOperations c x

/-- Explicit row-major materialization of every matrix entry. -/
def materializeDense (γ : Coupling K) : List (Allocation K) :=
  (List.finRange K).flatMap fun i =>
    (List.finRange K).map fun j => (i, j, γ i j)

/-- The dense implementation materializes every entry of both matrices after
running the costed threshold and sparse-flow implementation. -/
def costedDenseThresholdFlow (c : Capacities 𝒳 K) (hValid : ValidCapacities c) :
    Costed (𝒳 → List (Allocation K) × List (Allocation K)) :=
  { value := fun x =>
      (materializeDense (thresholdFlowLower c hValid x),
        materializeDense (thresholdFlowUpper c hValid x))
    operations := thresholdFlowCostFor c hValid + 2 * Fintype.card 𝒳 * K ^ 2 }

/-- The dense threshold flow cost for is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def denseThresholdFlowCostFor (c : Capacities 𝒳 K)
    (hValid : ValidCapacities c) : ℕ :=
  (costedDenseThresholdFlow c hValid).operations

/-- The dense threshold flow actual cost for is the corresponding numerical quantity in the slate-benefit partial-transport calculation. -/
def denseThresholdFlowActualCostFor (c : Capacities 𝒳 K) : ℕ :=
  thresholdFlowActualCostFor c + 2 * Fintype.card 𝒳 * K ^ 2

end

end CausalSmith.PartialID.SlateBenefitPartialTransport
