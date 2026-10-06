module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Defs.Model
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Embedding.Basic

/-! Projective directions, assignment fibers, completion fibers, and peeling. -/

@[expose] public section

open Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @env: S1
variable {p M q : ℕ}

/-- Projective equivalence of nonzero shift directions. @realizes \sim(nonzero scalar multiple) -/
def ProjSim (d : Fin M → Fin p → ℝ) (m m' : Fin M) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ d m = c • d m'

/-- A finite presentation of the distinct projective directions. -/
structure ProjectiveReduction (d : Fin M → Fin p → ℝ) where
  q : ℕ -- @realizes q(number of projective classes)
  κ : Fin M → Fin q -- @realizes \kappa(class map)
  v : Fin q → Fin p → ℝ -- @realizes v_g(direction representative) @realizes V(family)
  -- @realizes [q](Fin q group labels)
  c : Fin M → ℝ -- @realizes c_m(within-class scale)
  κ_surj : Function.Surjective κ
  v_ne : ∀ g, v g ≠ 0
  c_ne : ∀ m, c m ≠ 0
  decomp : ∀ m, d m = c m • v (κ m)
  classes : ∀ m m', κ m = κ m' ↔ ProjSim d m m'

-- @node: exists_projectiveReduction
theorem exists_projectiveReduction (d : Fin M → Fin p → ℝ)
    (hd : ∀ m, d m ≠ 0) : Nonempty (ProjectiveReduction d) := by
  classical
  let s : Setoid (Fin M) := {
    r := ProjSim d
    iseqv := ⟨by
      intro m
      exact ⟨1, one_ne_zero, by simp⟩, by
      intro m n h
      obtain ⟨c, hc, hmn⟩ := h
      refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
      rw [hmn, smul_smul, inv_mul_cancel₀ hc, one_smul], by
      intro m n k hmn hnk
      obtain ⟨c, hc, hmn⟩ := hmn
      obtain ⟨b, hb, hnk⟩ := hnk
      refine ⟨c * b, mul_ne_zero hc hb, ?_⟩
      rw [hmn, hnk, smul_smul]⟩ }
  letI : Setoid (Fin M) := s
  let Q := Quotient s
  letI : Fintype Q := Fintype.ofFinite Q
  let e : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let κ : Fin M → Fin (Fintype.card Q) := fun m => e (Quotient.mk s m)
  let v : Fin (Fintype.card Q) → Fin p → ℝ :=
    fun g => d (Quotient.out (e.symm g))
  have hrel (m : Fin M) : ProjSim d m (Quotient.out (e.symm (κ m))) := by
    change s.r m (Quotient.out (e.symm (κ m)))
    apply Quotient.exact
    simp [κ, e, Quotient.out_eq]
  let c : Fin M → ℝ := fun m => Classical.choose (hrel m)
  refine ⟨{
    q := Fintype.card Q
    κ := κ
    v := v
    c := c
    κ_surj := ?_
    v_ne := ?_
    c_ne := ?_
    decomp := ?_
    classes := ?_ }⟩
  · intro g
    obtain ⟨m, hm⟩ := Quotient.exists_rep (e.symm g)
    use m
    change e (Quotient.mk s m) = g
    rw [hm, e.apply_symm_apply]
  · intro g
    exact hd _
  · intro m
    exact (Classical.choose_spec (hrel m)).1
  · intro m
    exact (Classical.choose_spec (hrel m)).2
  · intro m m'
    change e (Quotient.mk s m) = e (Quotient.mk s m') ↔ ProjSim d m m'
    constructor
    · intro h
      exact (Quotient.eq).mp (e.injective h)
    · intro h
      exact congrArg e ((Quotient.eq).mpr h)

/-- A concrete projective grouping by normalized finite directions. -/
-- @node: def:projective-reduction
noncomputable def projectiveReduction (d : Fin M → Fin p → ℝ)
    (hd : ∀ m, d m ≠ 0) : ProjectiveReduction d :=
  Classical.choice (exists_projectiveReduction d hd)

/-- A model generates exactly the displayed projective direction family. -/
def GeneratesDirections {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    (𝔐 : AtomicCountModel p M Ω μ) (v : Fin q → Fin p → ℝ) : Prop :=
  ∃ r : ProjectiveReduction (obsShift μ 𝔐), r.q = q ∧
    ∃ e : Fin r.q ≃ Fin q, ∀ g, r.v g = v (e g)

/-- Support of a direction. @realizes S_g(nonzero coordinates) -/
noncomputable def support (v : Fin q → Fin p → ℝ) (g : Fin q) : Finset (Fin p) :=
  Finset.univ.filter (fun i => v g i ≠ 0)

/-- Support-implied directed graph. @realizes H_f(edges f(g)→i) -/
def Hf (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (i j : Fin p) : Prop :=
  -- @realizes f(injective direction-to-target assignment)
  ∃ g, f g = i ∧ j ∈ support v g ∧ j ≠ i

/-- Support-compatible acyclic target injections. -/
-- @node: def:compatibility-fiber
def assignmentFiber (v : Fin q → Fin p → ℝ) : Set (Fin q ↪ Fin p) :=
  {f | (∀ g, f g ∈ support v g) ∧
    ∀ i, ¬ Relation.TransGen (Hf v f) i i} -- @realizes \mathfrak F(V)(assignment fiber)

/-- The sharp marginal target set. @realizes \mathcal T_g(V)(assignment image) -/
def targetSet (v : Fin q → Fin p → ℝ) (g : Fin q) : Set (Fin p) :=
  (fun f => f g) '' assignmentFiber v

/-- Uncovered coordinates. @realizes \mathcal U_f(complement of image) -/
def uncovered (f : Fin q ↪ Fin p) : Finset (Fin p) :=
  Finset.univ \ Finset.univ.map f

/-- Fixed-assignment completion slice. -/
def completionFiberAt (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p) :
    Set (Matrix (Fin p) (Fin p) ℝ) :=
  {B | (∀ g i, B i (f g) = v g i / v g (f g)) ∧
    (∀ i, B i i = 1) ∧
    ∀ i, ¬ Relation.TransGen (fun j k => j ≠ k ∧ B k j ≠ 0) i i}

/-- Full total-effect completion fiber.
@realizes \mathfrak B(V)(union of completion slices) -/
-- @node: def:completion-fiber
def completionFiber (v : Fin q → Fin p → ℝ) :
    Set (Matrix (Fin p) (Fin p) ℝ) :=
  ⋃ f ∈ assignmentFiber v, completionFiberAt v f

/-- Structural coefficient fiber. @realizes \mathfrak A(V)(I-B⁻¹ image) -/
noncomputable def coefficientFiber (v : Fin q → Fin p → ℝ) :
    Set (Matrix (Fin p) (Fin p) ℝ) :=
  (fun B => 1 - B⁻¹) '' completionFiber v

/-- Reparameterization of a matrix in the compatible completion fiber, retaining
the conditional Poisson count kernel of the original observed experiment. -/
-- @node: def:same-law-completion
noncomputable def sameLawCompletion {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (v : Fin q → Fin p → ℝ)
    (𝔐 : AtomicCountModel p M Ω μ)
    (B' : Matrix (Fin p) (Fin p) ℝ) (_hB' : B' ∈ completionFiber v) :
    Matrix (Fin p) (Fin p) ℝ ×
    (Fin (M + 1) → Fin p → ℝ) ×
    (Fin (M + 1) → Matrix (Fin p) (Fin p) ℝ) ×
    (Fin (M + 1) → Ω → Fin p → ℝ) ×
    ((Fin p → ℝ) → (Fin p → ℝ) → MeasureTheory.Measure (Fin p → ℕ)) :=
  (1 - B'⁻¹,
    (fun m => B'⁻¹ *ᵥ obsMean μ 𝔐 m),
    (fun m => B'⁻¹ * (Matrix.of (obsCov μ 𝔐 m)) * (B'⁻¹).transpose),
    (fun m ω => B'⁻¹ *ᵥ
      (fun i => latentState 𝔐.A 𝔐.η 𝔐.ξ m ω i - obsMean μ 𝔐 m i)),
    poissonCountLaw)

/-- Joint structural fiber. @realizes \Theta(V)(assignment, completion, coefficient) -/
noncomputable def structuralFiber (v : Fin q → Fin p → ℝ) :=
  (assignmentFiber v, completionFiber v, coefficientFiber v)

/-- The structural fiber computed from the observable moment shifts using any
fixed projective reduction. The outer sigma type retains the class count. -/
noncomputable def lawIndexedFiber {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (r : ProjectiveReduction (obsShift μ 𝔐)) :
    Σ q : ℕ, Set (Fin q ↪ Fin p) ×
      Set (Matrix (Fin p) (Fin p) ℝ) ×
      Set (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨r.q, structuralFiber r.v⟩

/-- Retain the frozen group and groups with no private row. -/
def peelStep {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (R : Finset G) : Finset G :=
  R.filter (fun h => some h = frozen ∨
    ¬ ∃ i ∈ S h, ∀ h' ∈ R, h' ≠ h → i ∉ S h')

/-- Closure of parallel private-row deletion after at most q rounds. -/
def peelResidual {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) : Finset G :=
  (peelStep S frozen)^[Fintype.card G] Finset.univ

/-- Private coordinates of a frozen direction after peeling. -/
-- @node: def:frozen-peeling
def frozenPeeling {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (g : G) : Finset (Fin p) :=
  (S g).filter (fun i => ∀ h ∈ peelResidual S (some g), h ≠ g → i ∉ S h)

/-- A remaining, nonfrozen group with a coordinate private among the remaining groups. -/
def FrozenDeletable {G : Type*} [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (R : Finset G) (h : G) : Prop :=
  h ∈ R ∧ some h ≠ frozen ∧
    ∃ i ∈ S h, ∀ h' ∈ R, h' ≠ h → i ∉ S h'

/-- One sequential deletion of a currently private, nonfrozen group. -/
def FrozenDeletionStep {G : Type*} [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (R R' : Finset G) : Prop :=
  ∃ h, FrozenDeletable S frozen R h ∧ R' = R.erase h

/-- A finite deletion history from all groups to a residual with no legal deletion. -/
def MaximalFrozenDeletionRun {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (run : List (Finset G)) (terminal : Finset G) : Prop :=
  run.head? = some Finset.univ ∧
    (∀ R R', (R, R') ∈ run.zip run.tail → FrozenDeletionStep S frozen R R') ∧
    run.getLast? = some terminal ∧
    ∀ h, ¬ FrozenDeletable S frozen terminal h

/-- Build adjacency lists by inserting each supplied incidence once, while
charging each group visit and each incidence visit, neighbor insertion, and
degree update. -/
noncomputable def incidenceBuild {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) :
    ((Fin p → Finset G) × (Fin p → ℕ)) × ℕ := by
  classical
  exact Finset.univ.toList.foldl (fun st g =>
    (S g).toList.foldl (fun st i =>
      ((Function.update st.1.1 i (insert g (st.1.1 i)),
        Function.update st.1.2 i (st.1.2 i + 1)), st.2 + 3))
      (st.1, st.2 + 1)) ((fun _ => ∅, fun _ => 0), 0)

/-- Scan each support to populate the initial private-row queue. The counter
charges group visits, support incidences examined, and queue insertions. -/
noncomputable def incidenceQueueBuild {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (degree : Fin p → ℕ) : Finset G × ℕ := by
  classical
  exact Finset.univ.toList.foldl (fun st g =>
    if some g ≠ frozen ∧ ∃ i ∈ S g, degree i = 1 then
      (insert g st.1, st.2 + 2 + (S g).card)
    else (st.1, st.2 + 1 + (S g).card)) (∅, 0)

/-- State of one frozen peeling run. The counter records coordinate initialization,
group and incidence construction, queue operations, deleted incidences, and
original-neighbor scans when a coordinate first becomes private. -/
structure IncidencePeelState (p : ℕ) (G : Type*) where
  remaining : Finset G
  neighbors : Fin p → Finset G
  degree : Fin p → ℕ
  queue : Finset G
  cost : ℕ

noncomputable def incidencePeelInit {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) : IncidencePeelState p G := by
  classical
  let built := incidenceBuild S
  let queued := incidenceQueueBuild S frozen built.1.2
  exact {
    remaining := Finset.univ
    neighbors := built.1.1
    degree := built.1.2
    queue := queued.1
    cost := p + built.2 + queued.2 }

/-- Delete one queued group and update only its incident degrees. A coordinate whose
degree falls to one exposes its remaining incident group to the queue. -/
noncomputable def incidencePeelStep {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G)
    (st : IncidencePeelState p G) : IncidencePeelState p G := by
  classical
  exact if hq : st.queue.Nonempty then
    let g := Classical.choose hq
    let R := st.remaining.erase g
    let newly := (S g).biUnion (fun i =>
      if st.degree i = 2 then
        (st.neighbors i).filter (fun h => h ∈ R ∧ some h ≠ frozen)
      else ∅)
    { remaining := R
      neighbors := st.neighbors
      degree := fun i => if i ∈ S g then st.degree i - 1 else st.degree i
      queue := st.queue.erase g ∪ newly
      cost := st.cost + 2 + 3 * (S g).card +
        ∑ i ∈ S g, if st.degree i = 2 then 2 * (st.neighbors i).card else 0 }
  else { st with cost := st.cost + 1 }

/-- Run the maintained-degree queue for at most one deletion per group. -/
noncomputable def incidencePeelRun {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (frozen : Option G) : IncidencePeelState p G :=
  (incidencePeelStep S frozen)^[Fintype.card G] (incidencePeelInit S frozen)

/-- The computed marginal set and its counted elementary incidence operations,
including a visit to every output-support coordinate. -/
noncomputable def costedFrozenPeeling {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) (g : G) : Finset (Fin p) × ℕ := by
  classical
  let st := incidencePeelRun S (some g)
  exact ((S g).filter (fun i => st.degree i = 1), st.cost + (S g).card)

def peelsAll {G : Type*} [Fintype G] [DecidableEq G]
    (S : G → Finset (Fin p)) : Prop :=
  peelResidual S none = ∅

/-- Orders consistent with the forced support graph. -/
def IsLinearExtension (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (σ : Equiv.Perm (Fin p)) : Prop :=
  ∀ i j, Hf v f i j → σ.symm i < σ.symm j

/-- Affine unit-triangular completion at a fixed topological order. -/
def triangularFamily (v : Fin q → Fin p → ℝ) (f : Fin q ↪ Fin p)
    (σ : Equiv.Perm (Fin p)) : Set (Matrix (Fin p) (Fin p) ℝ) :=
  {B | B ∈ completionFiberAt v f ∧
    ∀ i j, i ≠ j → σ.symm i ≤ σ.symm j → B i j = 0}

/-- Minimum nonzero shift coordinate. @realizes \beta(nonzero support margin) -/
noncomputable def supportMargin (d : Fin M → Fin p → ℝ) : ℝ :=
  sInf {x : ℝ | ∃ m i, d m i ≠ 0 ∧ x = |d m i|}

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
