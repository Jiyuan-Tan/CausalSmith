module
public import Causalean.Stat.RandomGraph.PathOccupancy.CoarsePairs
public import Causalean.Stat.RandomGraph.PathOccupancy.ConnectedAssignments

/-!
# Counting connected assignment pairs

Two connected labelled assignments in a common consecutive coarse pair have
an encoding by their ordered anchors and their labelled offsets. Equal anchors
are retained because distinct components of a local subrelation can occupy the
same fine cell. The imported modules expose the individual assignment count and
the ordered and unordered fine-cell pair counts.
-/

public section

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- For [two nonempty labelled types](hyp:hm,hl) and [positive even coarse
count dividing the fine count](hyp:hM,hK,heven,hdiv), [the connected assignment
pairs sharing one coarse pair obey the anchor-times-offset count](goal).

Apply connected_assignment_encoding separately to each labelled type. Its
occupied-anchor clause and SamePair place both anchors in the ordered_same_pair
subtype. The product of both offset encodings remains injective. Compare its
cardinality and substitute ordered_same_pair_count; equal anchors stay valid.
-/
theorem connected_same_pair_assignment_count {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K M : ℕ) (hm : 1 ≤ Fintype.card ι) (hl : 1 ≤ Fintype.card κ)
    (hM : 0 < M) (hK : 0 < K) (heven : 2 ∣ M) (hdiv : M ∣ K) :
    M * Nat.card {p : (ι → Fin K) × (κ → Fin K) //
      ConnectedAssignment p.1 ∧ ConnectedAssignment p.2 ∧ SamePair K M p.1 p.2} ≤
      2 * K ^ 2 * Fintype.card ι ^ Fintype.card ι *
        Fintype.card κ ^ Fintype.card κ := by
  classical
  obtain ⟨eι, heι, haι⟩ := connected_assignment_encoding K hm
  obtain ⟨eκ, heκ, haκ⟩ := connected_assignment_encoding K hl
  let P := {p : (ι → Fin K) × (κ → Fin K) //
    ConnectedAssignment p.1 ∧ ConnectedAssignment p.2 ∧ SamePair K M p.1 p.2}
  let O := {p : Fin K × Fin K // pairClass K M p.1 = pairClass K M p.2}
  let x (p : P) : {x : ι → Fin K // ConnectedAssignment x} :=
    ⟨p.val.1, p.property.1⟩
  let y (p : P) : {y : κ → Fin K // ConnectedAssignment y} :=
    ⟨p.val.2, p.property.2.1⟩
  have hanchors (p : P) :
      pairClass K M (eι (x p)).1 = pairClass K M (eκ (y p)).1 := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (haι (x p)).1
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (haκ (y p)).1
    obtain ⟨c, _, hx, hy⟩ := p.property.2.2
    rw [← hi, ← hj]
    exact (hx i).trans (hy j).symm
  let encode : P → O × ((ι → Fin (Fintype.card ι)) ×
      (κ → Fin (Fintype.card κ))) := fun p =>
    (⟨((eι (x p)).1, (eκ (y p)).1), hanchors p⟩,
      (eι (x p)).2, (eκ (y p)).2)
  have hinj : Function.Injective encode := by
    intro p q hpq
    have hx : x p = x q := heι (Prod.ext
      (congrArg (fun t => t.1.val.1) hpq)
      (congrArg (fun t => t.2.1) hpq))
    have hy : y p = y q := heκ (Prod.ext
      (congrArg (fun t => t.1.val.2) hpq)
      (congrArg (fun t => t.2.2) hpq))
    exact Subtype.ext (Prod.ext (congrArg Subtype.val hx) (congrArg Subtype.val hy))
  have hc : Nat.card P ≤ Nat.card O *
      (Fintype.card ι ^ Fintype.card ι * Fintype.card κ ^ Fintype.card κ) := by
    simpa [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card] using
      Nat.card_le_card_of_injective encode hinj
  have ho : M * Nat.card O = 2 * K ^ 2 :=
    ordered_same_pair_count K M hM hK heven hdiv
  calc
    M * Nat.card P ≤ M * (Nat.card O *
        (Fintype.card ι ^ Fintype.card ι * Fintype.card κ ^ Fintype.card κ)) :=
      Nat.mul_le_mul_left M hc
    _ = (M * Nat.card O) *
        (Fintype.card ι ^ Fintype.card ι * Fintype.card κ ^ Fintype.card κ) := by ring
    _ = 2 * K ^ 2 * Fintype.card ι ^ Fintype.card ι *
        Fintype.card κ ^ Fintype.card κ := by rw [ho]; ring

end Causalean.Stat.RandomGraph.PathOccupancy
