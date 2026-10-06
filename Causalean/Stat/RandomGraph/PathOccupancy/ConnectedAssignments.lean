module
public import Causalean.Stat.RandomGraph.PathOccupancy.Path
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Counting connected labelled assignments

Every nonempty connected assignment is encoded by its leftmost occupied cell
and one bounded offset for each label. The resulting injection gives the
finite-path assignment count used in occupancy union bounds.
-/

public section

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- [Connected assignments on nonempty labels](hyp:hm), to [a finite path](hyp:K),
[have an injective encoding by an occupied anchor and a bounded offset for each
label, reconstructing the original fine-cell values](goal).

Apply connected_run_cover to the occupied image; its cardinality is at most the
label cardinality. Choose the occupied left endpoint, subtract it from every
value, and package these differences in the bounded finite type. Reconstruction
proves injectivity. Anchor membership is needed to count paired assignments in
a shared coarse-pair class without excluding coincident occupied cells.
-/
theorem connected_assignment_encoding {ι : Type*} [Fintype ι] (K : ℕ)
    (hm : 1 ≤ Fintype.card ι) :
    ∃ encode : {x : ι → Fin K // ConnectedAssignment x} →
        Fin K × (ι → Fin (Fintype.card ι)),
      Function.Injective encode ∧
      ∀ x, (encode x).1 ∈ Finset.univ.image x.val ∧
        ∀ i, (x.val i).val = (encode x).1.val + ((encode x).2 i).val := by
  classical
  have hlabels : (Finset.univ : Finset ι).Nonempty := by
    apply Finset.card_pos.mp
    simpa using (Nat.zero_lt_of_lt hm)
  have hanchor : ∀ x : {x : ι → Fin K // ConnectedAssignment x},
      ∃ a ∈ Finset.univ.image x.val,
        ∀ i, a.val ≤ (x.val i).val ∧
          (x.val i).val < a.val + Fintype.card ι := by
    intro x
    have hnonempty : (Finset.univ.image x.val).Nonempty := by
      obtain ⟨i, hi⟩ := hlabels
      exact ⟨x.val i, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
    obtain ⟨a, ha, hcover⟩ := connected_run_cover _ hnonempty x.property
    refine ⟨a, ha, fun i => ?_⟩
    have hi := hcover (x.val i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hcard : (Finset.univ.image x.val).card ≤ Fintype.card ι := by
      simpa using (Finset.card_image_le (s := Finset.univ) (f := x.val))
    constructor
    · exact hi.1
    · exact hi.2.trans_le (Nat.add_le_add_left hcard a.val)
  let anchor := fun x => Classical.choose (hanchor x)
  have ha := fun x => Classical.choose_spec (hanchor x)
  let encode : {x : ι → Fin K // ConnectedAssignment x} →
      Fin K × (ι → Fin (Fintype.card ι)) := fun x =>
    (anchor x, fun i => ⟨(x.val i).val - (anchor x).val, by
      have hi := (ha x).2 i
      change (anchor x).val ≤ (x.val i).val ∧
        (x.val i).val < (anchor x).val + Fintype.card ι at hi
      omega⟩)
  have hreconstruct : ∀ x i,
      (x.val i).val = (encode x).1.val + ((encode x).2 i).val := by
    intro x i
    have hi := (ha x).2 i
    change (anchor x).val ≤ (x.val i).val ∧
      (x.val i).val < (anchor x).val + Fintype.card ι at hi
    change (x.val i).val = (anchor x).val + ((x.val i).val - (anchor x).val)
    omega
  refine ⟨encode, ?_, fun x => ⟨(ha x).1, hreconstruct x⟩⟩
  intro x y hxy
  apply Subtype.ext
  funext i
  apply Fin.ext
  rw [hreconstruct x i, hreconstruct y i, hxy]

/-- For [a nonempty labelled type](hyp:hm), the [number of connected
assignments](goal) to [the finite path](hyp:K) is at most the number of cells
times the cardinality of the labelled type raised to itself.

Encode an assignment by its minimum occupied cell and the labelled offsets in
a run of length m, using connected_run_cover and card_image_le.
-/
theorem connected_assignment_count {ι : Type*} [Fintype ι] (K : ℕ)
    (hm : 1 ≤ Fintype.card ι) :
    Nat.card {x : ι → Fin K // ConnectedAssignment x} ≤
      K * Fintype.card ι ^ Fintype.card ι := by
  obtain ⟨encode, hinj, _⟩ := connected_assignment_encoding K hm
  simpa [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card] using
    Nat.card_le_card_of_injective encode hinj

end Causalean.Stat.RandomGraph.PathOccupancy
