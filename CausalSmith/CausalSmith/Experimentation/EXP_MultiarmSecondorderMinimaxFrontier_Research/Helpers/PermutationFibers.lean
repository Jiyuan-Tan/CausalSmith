import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.World
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Logic.Equiv.Fintype

/-!
Finite fiber permutations and the assignment/observation orbit facts used by
the response-type reduction.
-/

open scoped BigOperators
open Finset
open Equiv MulAction

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

variable {K n : ℕ}

/-- Relabeling a schedule by a unit permutation moves each unit’s response type along the inverse permutation. -/
def permuteSchedule (σ : Equiv.Perm (Unit n)) (z : Schedule K n) : Schedule K n :=
  fun i => z (σ.symm i)

/-- Relabeling an assignment by a unit permutation moves each unit’s treatment along the inverse permutation. -/
def permuteAssign (σ : Equiv.Perm (Unit n)) (A : Assign K n) : Assign K n :=
  fun i => A (σ.symm i)

/-- Relabeling an observed-outcome vector by a unit permutation moves each outcome along the inverse permutation. -/
def permuteObserved (σ : Equiv.Perm (Unit n)) (y : ObservedOutcome n) : ObservedOutcome n :=
  fun i => y (σ.symm i)

/-- Allocation counts of a labeled assignment. -/
def rawAssignmentCount (A : Assign K n) (a : Arm K) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => A i = a).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => A i = a) Finset.univ))⟩

/-- [the raw assignment count sums](goal). -/
lemma rawAssignmentCount_sum (A : Assign K n) :
    ∑ a, ((rawAssignmentCount A a : Fin (n + 1)) : ℕ) = n := by
  symm
  simpa [rawAssignmentCount] using
    (Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Unit n)))
      (t := (Finset.univ : Finset (Arm K))) (f := A) (by simp))

/-- The assignment-count vector records the number of units allocated to each treatment arm. -/
def assignmentCounts (A : Assign K n) : AllocVec K n :=
  ⟨rawAssignmentCount A, rawAssignmentCount_sum A⟩

/-- Observed-success counts paired with the allocation orbit of `(A,y)`. -/
def rawObservedCount (A : Assign K n) (y : ObservedOutcome n) (a : Arm K) :
    Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i => A i = a ∧ y i).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i => A i = a ∧ y i) Finset.univ))⟩

/-- [the raw observed count is at most property holds](goal). -/
lemma rawObservedCount_le (A : Assign K n) (y : ObservedOutcome n) (a : Arm K) :
    (rawObservedCount A y a : ℕ) ≤ (rawAssignmentCount A a : ℕ) := by
  change (Finset.univ.filter fun i => A i = a ∧ y i).card ≤
    (Finset.univ.filter fun i => A i = a).card
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.1

/-- The observed-count vector records the number of observed successes within each treatment arm. -/
def observedCounts (A : Assign K n) (y : ObservedOutcome n) : ObsVec (assignmentCounts A) :=
  ⟨rawObservedCount A y, rawObservedCount_le A y⟩

/-- A permutation obtained by matching corresponding finite fibers. -/
noncomputable def fiberwisePermOfCardEq {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C]
    (f g : I → C)
    (h : ∀ a, Fintype.card {i // f i = a} = Fintype.card {i // g i = a}) :
    Equiv.Perm I :=
  Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq (h a)

/-- [the stated side condition holds](hyp:h), [the fiberwise perm when cardinality equals spec](goal). -/
lemma fiberwisePermOfCardEq_spec {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C]
    (f g : I → C)
    (h : ∀ a, Fintype.card {i // f i = a} = Fintype.card {i // g i = a}) (i : I) :
    g (fiberwisePermOfCardEq f g h i) = f i :=
  Equiv.ofFiberEquiv_map (fun a => Fintype.equivOfCardEq (h a)) i

/-- Functions with the same fiber cardinalities as a fixed finite function. -/
def FiberProfile {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] (f : I → C) :=
  {g : I → C // ∀ c, Fintype.card {i // g i = c} = Fintype.card {i // f i = c}}

private noncomputable def fiberProfileEquivOrbit
    {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C] (f : I → C) :
    FiberProfile f ≃ MulAction.orbit ((Equiv.Perm I)ᵈᵐᵃ) f where
  toFun g := ⟨g.1, by
    let σ := fiberwisePermOfCardEq f g.1 (fun c => (g.2 c).symm)
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨DomMulAct.mk σ.symm, funext fun i => ?_⟩
    have hs := fiberwisePermOfCardEq_spec f g.1 (fun c => (g.2 c).symm) (σ.symm i)
    simpa [DomMulAct.smul_apply, σ] using hs.symm⟩
  invFun g := ⟨g.1, fun c => by
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp g.2
    let e : {i // g.1 i = c} ≃ {i // f i = c} :=
      { toFun := fun i => ⟨DomMulAct.mk.symm σ • i.1, (congrFun hσ i.1).trans i.2⟩
        invFun := fun i => ⟨(DomMulAct.mk.symm σ)⁻¹ • i.1, by
          have hi := congrFun hσ ((DomMulAct.mk.symm σ)⁻¹ • i.1)
          have hi' : f i.1 = g.1 ((DomMulAct.mk.symm σ)⁻¹ • i.1) := by
            simpa [DomMulAct.smul_apply] using hi
          exact hi'.symm.trans i.2⟩
        left_inv := fun i => by ext; simp
        right_inv := fun i => by ext; simp }
    exact Fintype.card_congr e⟩
  left_inv g := rfl
  right_inv g := rfl

private noncomputable instance fiberProfileFintype
    {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C] (f : I → C) :
    Fintype (FiberProfile f) := by
  classical
  letI : Fintype ((Equiv.Perm I)ᵈᵐᵃ) :=
    Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  exact Fintype.ofEquiv (MulAction.orbit ((Equiv.Perm I)ᵈᵐᵃ) f)
    (fiberProfileEquivOrbit f).symm

/-- [Orbit-stabilizer cardinality for a prescribed finite fiber profile.](goal) -/
lemma fiberProfile_card_mul {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C] (f : I → C) :
    Fintype.card (FiberProfile f) *
        ∏ c, (Fintype.card {i // f i = c}).factorial =
      (Fintype.card I).factorial := by
  classical
  letI : Fintype ((Equiv.Perm I)ᵈᵐᵃ) :=
    Fintype.ofEquiv (Equiv.Perm I) DomMulAct.mk
  rw [Fintype.card_congr (fiberProfileEquivOrbit f)]
  have hstab : Fintype.card (MulAction.stabilizer ((Equiv.Perm I)ᵈᵐᵃ) f) =
      ∏ c, (Fintype.card {i // f i = c}).factorial := by
    let e : MulAction.stabilizer ((Equiv.Perm I)ᵈᵐᵃ) f ≃
        {σ : Equiv.Perm I // f ∘ σ = f} :=
      Equiv.subtypeEquiv DomMulAct.mk.symm fun _ => DomMulAct.mem_stabilizer_iff
    rw [Fintype.card_congr e, DomMulAct.stabilizer_card]
  have hgroup : Fintype.card ((Equiv.Perm I)ᵈᵐᵃ) =
      (Fintype.card I).factorial := by
    rw [Fintype.card_congr DomMulAct.mk.symm, Fintype.card_perm]
  have horbit := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    ((Equiv.Perm I)ᵈᵐᵃ) f
  rw [hstab, hgroup] at horbit
  exact horbit

private lemma card_fiber_eq_filter {I C : Type*} [Fintype I]
    [DecidableEq C] (f : I → C) (a : C) :
    Fintype.card {i // f i = a} = #(Finset.univ.filter fun i => f i = a) := by
  rw [Fintype.card_subtype]

/-- [the assignment counts permute property holds](goal). -/
lemma assignmentCounts_permute (A : Assign K n) (σ : Equiv.Perm (Unit n)) :
    assignmentCounts (permuteAssign σ A) = assignmentCounts A := by
  apply Subtype.ext
  funext a
  apply Fin.ext
  change #(Finset.univ.filter fun i => A (σ.symm i) = a) =
    #(Finset.univ.filter fun i => A i = a)
  let e : {i // A (σ.symm i) = a} ≃ {i // A i = a} :=
    { toFun := fun i => ⟨σ.symm i, i.2⟩
      invFun := fun i => ⟨σ i, by simpa using i.2⟩
      left_inv := fun i => by ext; simp
      right_inv := fun i => by ext; simp }
  simpa only [← Fintype.card_subtype] using Fintype.card_congr e

/-- [the observed counts permute property holds](goal). -/
lemma observedCounts_permute (A : Assign K n) (y : ObservedOutcome n)
    (σ : Equiv.Perm (Unit n)) :
    (observedCounts (permuteAssign σ A) (permuteObserved σ y)).1 =
      (observedCounts A y).1 := by
  funext a
  apply Fin.ext
  change #(Finset.univ.filter fun i => A (σ.symm i) = a ∧ y (σ.symm i)) =
    #(Finset.univ.filter fun i => A i = a ∧ y i)
  let e : {i // A (σ.symm i) = a ∧ y (σ.symm i)} ≃
      {i // A i = a ∧ y i} :=
    { toFun := fun i => ⟨σ.symm i, i.2⟩
      invFun := fun i => ⟨σ i, by simpa using i.2⟩
      left_inv := fun i => by ext; simp
      right_inv := fun i => by ext; simp }
  simpa only [← Fintype.card_subtype] using Fintype.card_congr e

/-- [Equal allocation counts are exactly equality up to a unit permutation.](goal) -/
lemma assignmentCounts_eq_iff_perm (A B : Assign K n) :
    assignmentCounts A = assignmentCounts B ↔
      ∃ σ : Equiv.Perm (Unit n), permuteAssign σ A = B := by
  constructor
  · intro hAB
    have hfiber : ∀ a, Fintype.card {i // A i = a} = Fintype.card {i // B i = a} := by
      intro a
      have ha := congrArg (fun r : AllocVec K n => (r.1 a : ℕ)) hAB
      simpa [assignmentCounts, rawAssignmentCount, card_fiber_eq_filter] using ha
    let σ := fiberwisePermOfCardEq A B hfiber
    refine ⟨σ, funext fun i => ?_⟩
    have hs := fiberwisePermOfCardEq_spec A B hfiber (σ.symm i)
    simpa [permuteAssign, σ] using hs.symm
  · rintro ⟨σ, rfl⟩
    exact (assignmentCounts_permute A σ).symm

/-- [the prescribed fiber sizes sum to the domain cardinality](hyp:hd), [Realize prescribed finite fiber sizes by a function on `Fin n`.](goal) -/
lemma exists_fun_card_fiber_eq {C : Type*} [Fintype C] [DecidableEq C] (d : C → ℕ)
    (hd : ∑ a, d a = n) :
    ∃ f : Fin n → C, ∀ a, #(Finset.univ.filter fun i => f i = a) = d a := by
  classical
  let S := Σ a : C, Fin (d a)
  have hcard : Fintype.card (Fin n) = Fintype.card S := by
    simp [S, hd]
  let e : Fin n ≃ S := Fintype.equivOfCardEq hcard
  let f : Fin n → C := fun i => (e i).1
  refine ⟨f, fun a => ?_⟩
  let ef : {i // f i = a} ≃ {s : S // s.1 = a} :=
    e.subtypeEquiv fun i => by rfl
  let es : {s : S // s.1 = a} ≃ Fin (d a) :=
    { toFun := fun s => cast (congrArg Fin (congrArg d s.2)) s.1.2
      invFun := fun j => ⟨⟨a, j⟩, rfl⟩
      left_inv := fun s => by
        rcases s with ⟨⟨b, j⟩, hb⟩
        dsimp at hb ⊢
        subst b
        rfl
      right_inv := fun j => rfl }
  let ea := ef.trans es
  rw [← card_fiber_eq_filter]
  exact (Fintype.card_congr ea).trans (Fintype.card_fin _)

/-- Functions on a finite type with prescribed fiber cardinalities. -/
def ExactFiber {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (d : C → ℕ) :=
  {f : I → C // ∀ c, Fintype.card {i // f i = c} = d c}

/-- The exact fiber collection has a finite enumeration. -/
noncomputable instance exactFiberFintype
    {I C : Type*} [Fintype I] [Fintype C] [DecidableEq C]
    (d : C → ℕ) : Fintype (ExactFiber (I := I) d) := by
  classical
  unfold ExactFiber
  infer_instance

/-- [the prescribed fiber sizes sum to the domain cardinality](hyp:hd), [Prescribed fibers whose sizes sum to the domain cardinality are realizable.](goal) -/
lemma exists_fun_fiber_card_eq {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] (d : C → ℕ) (hd : ∑ c, d c = Fintype.card I) :
    ∃ f : I → C, ∀ c, Fintype.card {i // f i = c} = d c := by
  classical
  obtain ⟨g, hg⟩ := exists_fun_card_fiber_eq (n := Fintype.card I) d hd
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨fun i => g (e i), fun c => ?_⟩
  let ec : {i // g (e i) = c} ≃ {j // g j = c} := e.subtypeEquiv fun _ => Iff.rfl
  rw [Fintype.card_congr ec, Fintype.card_subtype]
  exact hg c

/-- [the prescribed fiber sizes sum to the domain cardinality](hyp:hd), [Multinomial cardinality identity for prescribed finite fibers.](goal) -/
lemma exactFiber_card_mul {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C] (d : C → ℕ)
    (hd : ∑ c, d c = Fintype.card I) :
    Fintype.card (ExactFiber (I := I) d) * ∏ c, (d c).factorial =
      (Fintype.card I).factorial := by
  classical
  obtain ⟨f, hf⟩ := exists_fun_fiber_card_eq (I := I) d hd
  let e : ExactFiber (I := I) d ≃ FiberProfile f :=
    { toFun := fun g => ⟨g.1, fun c => (g.2 c).trans (hf c).symm⟩
      invFun := fun g => ⟨g.1, fun c => (g.2 c).trans (hf c)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simpa only [hf] using fiberProfile_card_mul f

/-- [the prescribed fiber sizes sum to the domain cardinality](hyp:hd), [Rational multinomial formula for the number of functions with prescribed fibers.](goal) -/
lemma exactFiber_card_cast_eq_div {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq I] [DecidableEq C] (d : C → ℕ)
    (hd : ∑ c, d c = Fintype.card I) :
    (Fintype.card (ExactFiber (I := I) d) : ℚ) =
      ((Fintype.card I).factorial : ℚ) / ∏ c, ((d c).factorial : ℚ) := by
  have h := congrArg (fun q : ℕ => (q : ℚ)) (exactFiber_card_mul d hd)
  push_cast at h
  apply (eq_div_iff ?_).2 h
  exact Finset.prod_ne_zero_iff.mpr fun _ _ => by positivity

/-- [the assignment counts surjective property holds](goal). -/
lemma assignmentCounts_surjective :
    Function.Surjective (assignmentCounts : Assign K n → AllocVec K n) := by
  intro r
  obtain ⟨A, hA⟩ := exists_fun_card_fiber_eq (fun a => (r.1 a : ℕ)) r.2
  refine ⟨A, Subtype.ext (funext fun a => Fin.ext ?_)⟩
  simpa [assignmentCounts, rawAssignmentCount] using hA a

/-- [Prescribed success counts below prescribed allocation counts are jointly realizable.](goal) -/
lemma observedCounts_realizable (r : AllocVec K n) (x : ObsVec r) :
    ∃ (A : Assign K n) (y : ObservedOutcome n),
      assignmentCounts A = r ∧
      ∀ a, (rawObservedCount A y a : ℕ) = (x.1 a : ℕ) := by
  classical
  obtain ⟨A, hA⟩ := assignmentCounts_surjective r
  have hcard (a : Arm K) :
      #(Finset.univ.filter fun i => A i = a) = (r.1 a : ℕ) := by
    have ha := congrArg (fun s : AllocVec K n => (s.1 a : ℕ)) hA
    simpa [assignmentCounts, rawAssignmentCount] using ha
  have hexists (a : Arm K) :
      ∃ s ⊆ (Finset.univ.filter fun i => A i = a), #s = (x.1 a : ℕ) := by
    apply Finset.exists_subset_card_eq
    rw [hcard]
    exact x.2 a
  let s : Arm K → Finset (Unit n) := fun a => Classical.choose (hexists a)
  have hs_subset (a : Arm K) : s a ⊆ Finset.univ.filter fun i => A i = a :=
    (Classical.choose_spec (hexists a)).1
  have hs_card (a : Arm K) : #(s a) = (x.1 a : ℕ) :=
    (Classical.choose_spec (hexists a)).2
  let y : ObservedOutcome n := fun i => i ∈ s (A i)
  refine ⟨A, y, hA, fun a => ?_⟩
  simp only [rawObservedCount]
  simp only [y, decide_eq_true_eq]
  rw [← hs_card a]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hiA, hi⟩
    simpa [hiA] using hi
  · intro hi
    have hiA : A i = a := (Finset.mem_filter.mp (hs_subset a hi)).2
    exact ⟨hiA, by simpa [hiA] using hi⟩

private lemma jointFiberCard_eq_of_counts
    (A B : Assign K n) (y v : ObservedOutcome n)
    (hA : assignmentCounts A = assignmentCounts B)
    (hx : (observedCounts A y).1 = (observedCounts B v).1) (a : Arm K) (b : Bool) :
    Fintype.card {i // (A i, y i) = (a, b)} =
      Fintype.card {i // (B i, v i) = (a, b)} := by
  classical
  have halloc := congrArg (fun r : AllocVec K n => (r.1 a : ℕ)) hA
  have hsuccess := congrFun hx a
  have halloc' : #(Finset.univ.filter fun i => A i = a) =
      #(Finset.univ.filter fun i => B i = a) := by
    simpa [assignmentCounts, rawAssignmentCount] using halloc
  have hsuccess' : #(Finset.univ.filter fun i => A i = a ∧ y i) =
      #(Finset.univ.filter fun i => B i = a ∧ v i) := by
    exact Fin.mk.inj_iff.mp hsuccess
  cases b with
  | false =>
      have hpartA := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter fun i => A i = a) (fun i => y i)
      have hpartB := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter fun i => B i = a) (fun i => v i)
      have hpartA' :
          #(Finset.univ.filter fun i => A i = a ∧ y i) +
            #(Finset.univ.filter fun i => A i = a ∧ y i = false) =
              #(Finset.univ.filter fun i => A i = a) := by
        simpa only [Finset.filter_filter, Bool.not_eq_true] using hpartA
      have hpartB' :
          #(Finset.univ.filter fun i => B i = a ∧ v i) +
            #(Finset.univ.filter fun i => B i = a ∧ v i = false) =
              #(Finset.univ.filter fun i => B i = a) := by
        simpa only [Finset.filter_filter, Bool.not_eq_true] using hpartB
      rw [card_fiber_eq_filter (fun i => (A i, y i)) (a, false),
        card_fiber_eq_filter (fun i => (B i, v i)) (a, false)]
      simp only [Prod.mk.injEq]
      omega
  | true =>
      rw [card_fiber_eq_filter (fun i => (A i, y i)) (a, true),
        card_fiber_eq_filter (fun i => (B i, v i)) (a, true)]
      simpa using hsuccess'

/-- [Allocation and success counts classify labeled assignment/outcome pairs up to permutation.](goal) -/
lemma assignmentObservedCounts_eq_iff_perm (A B : Assign K n)
    (y v : ObservedOutcome n) :
    (assignmentCounts A = assignmentCounts B ∧
      (observedCounts A y).1 = (observedCounts B v).1) ↔
      ∃ σ : Equiv.Perm (Unit n),
        permuteAssign σ A = B ∧ permuteObserved σ y = v := by
  constructor
  · rintro ⟨hA, hx⟩
    let f : Unit n → Arm K × Bool := fun i => (A i, y i)
    let g : Unit n → Arm K × Bool := fun i => (B i, v i)
    have hfiber : ∀ ab, Fintype.card {i // f i = ab} = Fintype.card {i // g i = ab} := by
      rintro ⟨a, b⟩
      exact jointFiberCard_eq_of_counts A B y v hA hx a b
    let σ := fiberwisePermOfCardEq f g hfiber
    refine ⟨σ, funext fun i => ?_, funext fun i => ?_⟩
    · have hs := fiberwisePermOfCardEq_spec f g hfiber (σ.symm i)
      simpa [permuteAssign, σ, f, g] using congrArg Prod.fst hs.symm
    · have hs := fiberwisePermOfCardEq_spec f g hfiber (σ.symm i)
      simpa [permuteObserved, σ, f, g] using congrArg Prod.snd hs.symm
  · rintro ⟨σ, rfl, rfl⟩
    exact ⟨(assignmentCounts_permute A σ).symm,
      (observedCounts_permute A y σ).symm⟩

/-- Number of labeled assignments in one allocation-count orbit. -/
noncomputable def allocationOrbitCard (r : AllocVec K n) : ℕ :=
  by
    classical
    exact Fintype.card {A : Assign K n // assignmentCounts A = r}

/-- [the allocation orbit cardinality is positive](goal). -/
lemma allocationOrbitCard_pos (r : AllocVec K n) : 0 < allocationOrbitCard r := by
  classical
  obtain ⟨A, hA⟩ := assignmentCounts_surjective r
  unfold allocationOrbitCard
  exact Fintype.card_pos_iff.mpr ⟨⟨A, hA⟩⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
