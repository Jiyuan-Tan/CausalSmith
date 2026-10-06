module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.Gray

/-!
# Reflected Gray order visits each cube vertex once

The bitwise reflected Gray map gives the bijection needed to turn a local
face-adjacent Gray path into an ordering of all children of a dyadic cube.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a cube dimension](hyp:d), [the reflected Gray-code map visits every binary cube vertex exactly once](goal). -/
theorem grayBits_bijective (d : ℕ) :
    Function.Bijective
      (fun k : Fin (2 ^ d) => fun i : Fin d => grayBit k.val i.val) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro x y hxy
    have hbit (n i : ℕ) : grayBit n i = (n.testBit i ^^ n.testBit (i + 1)) := by
      simp only [grayBit, reflectedGray, Nat.xor_eq, Nat.testBit_xor,
        Nat.testBit_div_two]
    have hdown : ∀ j : ℕ, j ≤ d →
        x.val.testBit (d - j) = y.val.testBit (d - j) := by
      intro j
      induction j with
      | zero =>
          intro _
          have hx : x.val.testBit d = false := Nat.testBit_lt_two_pow x.isLt
          have hy : y.val.testBit d = false := Nat.testBit_lt_two_pow y.isLt
          simp [hx, hy]
      | succ j ih =>
          intro hj
          have hj' : j ≤ d := by omega
          let i := d - (j + 1)
          have hi : i < d := by dsimp [i]; omega
          have his : i + 1 = d - j := by dsimp [i]; omega
          have hg := congrFun hxy ⟨i, hi⟩
          change grayBit x.val i = grayBit y.val i at hg
          rw [hbit, hbit, his, ih hj'] at hg
          exact Bool.xor_left_inj.mp hg
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < d
    · simpa only [Nat.sub_sub_self (Nat.le_of_lt hi)] using hdown (d - i) (Nat.sub_le d i)
    · have hx : x.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le x.isLt
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : d ≤ i)))
      have hy : y.val.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt
          (Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : d ≤ i)))
      simp [hx, hy]
  · simp

end Causalean.Mathlib.Topology.SpaceFillingCurve
