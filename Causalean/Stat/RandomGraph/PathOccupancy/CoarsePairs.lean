module
public import Causalean.Stat.RandomGraph.PathOccupancy.PairClasses
public import Mathlib.Data.Fintype.Prod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Counting fine-cell anchors in consecutive coarse pairs

For an even coarse count dividing the fine count, all pair classes have width
twice the fine-to-coarse ratio. Ordered anchor pairs include diagonal pairs;
unordered distinct-cell pairs use their unique increasing orientation.
-/

public section

namespace Causalean.Stat.RandomGraph.PathOccupancy

/-- Under [positive even coarse count and divisibility](hyp:hM,hK,heven,hdiv),
[the ordered same-pair anchor count, including equal anchors, is exactly
twice K squared over M](goal), for [the cell counts](hyp:K,M).

There are M/2 classes of width 2K/M. Keeping diagonal pairs is essential for
components of arbitrary subrelations that overlap in occupied cells.

Let q = K/M and w = 2q. Evenness and divisibility give K = (M/2)*w,
with w positive. Euclidean quotient and remainder encode a same-class ordered
pair as Fin (M/2) × Fin w × Fin w; decode via p*w+r and p*w+s.
Use cardinality of a product and arithmetic, retaining the diagonal.
-/
theorem ordered_same_pair_count (K M : ℕ) (hM : 0 < M) (hK : 0 < K)
    (heven : 2 ∣ M) (hdiv : M ∣ K) :
    M * Nat.card {p : Fin K × Fin K //
      pairClass K M p.1 = pairClass K M p.2} = 2 * K ^ 2 := by
  classical
  let n := M / 2
  let w := 2 * (K / M)
  have hMn : M = 2 * n := (Nat.mul_div_cancel' heven).symm
  have hKq : M * (K / M) = K := Nat.mul_div_cancel' hdiv
  have hKw : K = n * w := by
    calc
      K = M * (K / M) := hKq.symm
      _ = (2 * n) * (K / M) := congrArg (fun m => m * (K / M)) hMn
      _ = n * w := by dsimp [w]; ring
  have hw : 0 < w := by
    have : 0 < K / M := Nat.div_pos (Nat.le_of_dvd hK hdiv) hM
    dsimp [w]; omega
  let enc (a : Fin K) : Fin n × Fin w :=
    (⟨a.val / w, (Nat.div_lt_iff_lt_mul hw).2 (by rw [← hKw]; exact a.isLt)⟩,
      ⟨a.val % w, Nat.mod_lt _ hw⟩)
  let dec (p : Fin n × Fin w) : Fin K :=
    ⟨p.1.val * w + p.2.val, by
      rw [hKw]
      exact lt_of_lt_of_le (Nat.add_lt_add_left p.2.isLt _)
        (by simpa [Nat.add_mul] using Nat.mul_le_mul_right w (Nat.succ_le_of_lt p.1.isLt))⟩
  have hencdec (p : Fin n × Fin w) : enc (dec p) = p := by
    apply Prod.ext <;> apply Fin.ext
    · change (p.1.val * w + p.2.val) / w = p.1.val
      rw [Nat.add_comm, Nat.mul_comm p.1.val w, Nat.add_mul_div_left _ _ hw,
        Nat.div_eq_of_lt p.2.isLt, Nat.zero_add]
    · change (p.1.val * w + p.2.val) % w = p.2.val
      simp [Nat.add_mod, Nat.mod_eq_of_lt p.2.isLt]
  have hdecenc (a : Fin K) : dec (enc a) = a := by
    apply Fin.ext
    change a.val / w * w + a.val % w = a.val
    simpa [Nat.mul_comm] using Nat.div_add_mod a.val w
  let E : {p : Fin K × Fin K // pairClass K M p.1 = pairClass K M p.2} ≃
      Fin n × (Fin w × Fin w) :=
    { toFun := fun p => ((enc p.val.1).1, (enc p.val.1).2, (enc p.val.2).2)
      invFun := fun t => ⟨(dec (t.1, t.2.1), dec (t.1, t.2.2)), by
        change (enc (dec (t.1, t.2.1))).1.val = (enc (dec (t.1, t.2.2))).1.val
        rw [hencdec, hencdec]⟩
      left_inv := by
        intro p
        have hp : (enc p.val.1).1 = (enc p.val.2).1 := Fin.ext p.property
        apply Subtype.ext
        apply Prod.ext
        · exact hdecenc p.val.1
        · change dec ((enc p.val.1).1, (enc p.val.2).2) = p.val.2
          rw [hp]; exact hdecenc p.val.2
      right_inv := by
        intro t
        change ((enc (dec (t.1, t.2.1))).1,
          (enc (dec (t.1, t.2.1))).2, (enc (dec (t.1, t.2.2))).2) = t
        rw [hencdec, hencdec] }
  rw [Nat.card_congr E, Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin]
  rw [hMn, hKw]
  ring

/-- When [the coarse count is positive and even](hyp:hM,heven) and
[divides the positive fine count](hyp:hdiv,hK), [the number of unordered
distinct cell pairs within one coarse pair is at most K squared over M](goal).
Unordered pairs are represented uniquely by their increasing orientation.

The ordered_same_pair_count theorem supplies the exact ordered count.
Swap the two coordinates to biject
the increasing and decreasing orientations. Partition ordered pairs into these
two orientations and the diagonal; hence twice the increasing count is bounded
by the ordered count. Multiplication and cancellation give the stated bound.
-/
theorem unordered_same_pair_count (K M : ℕ) (hM : 0 < M) (hK : 0 < K)
    (heven : 2 ∣ M) (hdiv : M ∣ K) :
    M * Nat.card {p : Fin K × Fin K //
      p.1.val < p.2.val ∧ pairClass K M p.1 = pairClass K M p.2} ≤ K ^ 2 := by
  classical
  let U := {p : Fin K × Fin K //
    p.1.val < p.2.val ∧ pairClass K M p.1 = pairClass K M p.2}
  let O := {p : Fin K × Fin K // pairClass K M p.1 = pairClass K M p.2}
  let f : Bool × U → O := fun t =>
    if t.1 then ⟨(t.2.val.2, t.2.val.1), t.2.property.2.symm⟩
    else ⟨t.2.val, t.2.property.2⟩
  have hf : Function.Injective f := by
    rintro ⟨b, p⟩ ⟨c, q⟩ h
    have hv := congrArg Subtype.val h
    cases b <;> cases c
    · have hpq : p = q := Subtype.ext (by simpa [f] using hv)
      subst q; rfl
    · have h₁ := congrArg (fun t : Fin K × Fin K => t.1.val) hv
      have h₂ := congrArg (fun t : Fin K × Fin K => t.2.val) hv
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      have hp := p.property.1
      have hq := q.property.1
      omega
    · have h₁ := congrArg (fun t : Fin K × Fin K => t.1.val) hv
      have h₂ := congrArg (fun t : Fin K × Fin K => t.2.val) hv
      simp only [f, Bool.false_eq_true, ↓reduceIte] at h₁ h₂
      have hp := p.property.1
      have hq := q.property.1
      omega
    · have hpq : p = q := Subtype.ext (by
        apply Prod.ext
        · exact congrArg Prod.snd hv
        · exact congrArg Prod.fst hv)
      subst q; rfl
  have hc : 2 * Nat.card U ≤ Nat.card O := by
    have := Nat.card_le_card_of_injective f hf
    simpa [Nat.card_prod, Nat.card_eq_fintype_card] using this
  have ho := ordered_same_pair_count K M hM hK heven hdiv
  have hb := Nat.mul_le_mul_left M hc
  change M * Nat.card U ≤ K ^ 2
  change M * Nat.card O = 2 * K ^ 2 at ho
  nlinarith

end Causalean.Stat.RandomGraph.PathOccupancy
