module
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Relation
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Connected runs on a finite path

Path connectivity is order convexity of the occupied cells. A relation on labelled
vertices may omit any eligible edge: only connectivity within the specified set
and equality-or-neighbour locality are used to obtain the run and its span.
-/

@[expose] public section

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- [Two fine cells](hyp:a,b) are [equal or adjacent on the path](goal). -/
def Adjacent {K : ℕ} (a b : Fin K) : Prop :=
  a.val ≤ b.val + 1 ∧ b.val ≤ a.val + 1

/-- [A finite set of fine cells](hyp:s) [contains every cell between any two
of its members](goal). -/
def PathConnected {K : ℕ} (s : Finset (Fin K)) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, ∀ c : Fin K,
    a.val ≤ c.val → c.val ≤ b.val → c ∈ s

/-- [An assignment to a finite labelled set](hyp:x) has [connected occupied cells](goal). -/
noncomputable def ConnectedAssignment {ι : Type*} [Fintype ι] {K : ℕ}
    (x : ι → Fin K) : Prop := PathConnected (Finset.univ.image x)

/-- A [nonempty](hyp:hs), [connected](hyp:hc) set of [fine cells](hyp:s)
has [an occupied left endpoint and lies in a run of length its cardinality](goal).

Prove interval saturation between the minimum and maximum, then use the cardinality
of the integer interval. This gives a sharp span, including singleton sets.
-/
theorem connected_run_cover {K : ℕ} (s : Finset (Fin K))
    (hs : s.Nonempty) (hc : PathConnected s) :
    ∃ a ∈ s, ∀ b ∈ s, a.val ≤ b.val ∧ b.val < a.val + s.card := by
  obtain ⟨a, ha, hmin⟩ := Finset.exists_min_image s Fin.val hs
  refine ⟨a, ha, fun b hb => ⟨hmin b hb, ?_⟩⟩
  have hsub : Finset.Icc a.val b.val ⊆ s.image Fin.val := by
    intro n hn
    obtain ⟨han, hnb⟩ := Finset.mem_Icc.mp hn
    let c : Fin K := ⟨n, lt_of_le_of_lt hnb b.isLt⟩
    exact Finset.mem_image.mpr ⟨c, hc a ha b hb c han hnb, rfl⟩
  have hcard := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Nat.card_Icc] at hcard
  have hab := hmin b hb
  omega

/-- [A connected relation on a nonempty labelled subset](hyp:s,hs,hconn)
whose [edges join equal or adjacent assigned cells](hyp:hlocal)
has [connected occupied cells](goal) under the [given assignment](hyp:x).

The equivalence closure is taken on the subtype of the subset, so no path can
leave the subset. One way to prove saturation is to cut the vertices at a missing
intermediate cell; an eligible edge cannot cross that cut.
-/
theorem connected_image_of_local_relation {ι : Type*}
    {K : ℕ} (s : Finset ι) (x : ι → Fin K) (hs : s.Nonempty)
    (R : s → s → Prop)
    (hlocal : ∀ i j, R i j → Adjacent (x i) (x j))
    (hconn : ∀ i j, Relation.EqvGen R i j) : PathConnected (s.image x) := by
  classical
  intro a ha b hb c hac hcb
  by_contra hmissing
  have hne : ∀ i : s, (x i).val ≠ c.val := by
    intro i heq
    apply hmissing
    exact Finset.mem_image.mpr ⟨i, i.property, Fin.ext heq⟩
  have hcut : ∀ i j : s, Relation.EqvGen R i j →
      ((x i).val < c.val ↔ (x j).val < c.val) := by
    intro i j hij
    induction hij with
    | rel i j hij =>
        obtain ⟨hij₁, hij₂⟩ := hlocal i j hij
        have hi := hne i
        have hj := hne j
        constructor <;> intro h <;> omega
    | refl i => exact Iff.rfl
    | symm i j hij ih => exact ih.symm
    | trans i j k hij hjk ihij ihjk => exact ihij.trans ihjk
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
  have hni := hne ⟨i, hi⟩
  change (x i).val ≠ c.val at hni
  have hiff := hcut ⟨i, hi⟩ ⟨j, hj⟩ (hconn ⟨i, hi⟩ ⟨j, hj⟩)
  change (x i).val < c.val ↔ (x j).val < c.val at hiff
  have hleft : (x i).val < c.val := by omega
  have hright := hiff.mp hleft
  omega

end Causalean.Stat.RandomGraph.PathOccupancy
