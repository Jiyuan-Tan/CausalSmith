module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.GrayBijection

/-!
# Gray paths with prescribed adjacent endpoints

Coordinate permutations and bit reflections transport the standard reflected
Gray path to any adjacent pair of binary cube vertices. This is the local gate
ingredient for orienting the children of a dyadic parent cell.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [two binary cube vertices](hyp:u,v), [face adjacency](goal) is [the condition that exactly one coordinate differs](step:1). -/
def FaceAdjacentVertex {d : ℕ} (u v : Fin d → Bool) : Prop :=
  ∃ i : Fin d, u i ≠ v i ∧ ∀ j : Fin d, j ≠ i → u j = v j

private theorem grayBit_last (n i : ℕ) (hi : i < n + 1) :
    grayBit (2 ^ (n + 1) - 1) i = decide (i = n) := by
  have hp : 0 < 2 ^ n := pow_pos (by omega) _
  have hdiv : (2 ^ (n + 1) - 1) / 2 = 2 ^ n - 1 := by
    rw [pow_succ]
    omega
  rw [grayBit, reflectedGray, Nat.xor_eq, Nat.testBit_xor, hdiv,
    Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases hin : i < n
  · have hne : i ≠ n := by omega
    simp [hin, hne, show i < n + 1 by omega]
  · have heq : i = n := by omega
    simp [heq]

/-- Given [a positive dimension](hyp:d,hd) and [two face-adjacent binary vertices](hyp:u,v,huv),
[a reflected-Gray path visits every vertex once while using them as its endpoints](goal). -/
theorem exists_grayPath_between_adjacent_vertices (d : ℕ) (hd : 0 < d)
    (u v : Fin d → Bool) (huv : FaceAdjacentVertex u v) :
    ∃ path : Fin (2 ^ d) → Fin d → Bool,
      Function.Bijective path ∧
      (∀ k l : Fin (2 ^ d), l.val = k.val + 1 →
        FaceAdjacentVertex (path k) (path l)) ∧
      path 0 = u ∧ path (Fin.rev 0) = v := by
  obtain ⟨i, hdiff, hsame⟩ := huv
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  let top : Fin (n + 1) := ⟨n, by omega⟩
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i top
  let path : Fin (2 ^ (n + 1)) → Fin (n + 1) → Bool :=
    fun k j => u j ^^ grayBit k.val (σ j).val
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro k l hkl
      apply (grayBits_bijective (n + 1)).1
      funext j
      have h := congrFun hkl (σ j)
      simp only [path, σ, Equiv.swap_apply_self] at h
      exact Bool.xor_right_inj.mp h
    · simp
  · intro k l hkl
    obtain ⟨j, hj, hother⟩ := grayBit_adjacent (n + 1) k.val (by
      simpa only [← hkl] using l.isLt)
    refine ⟨σ.symm j, ?_, ?_⟩
    · simp only [path, Equiv.apply_symm_apply, hkl]
      intro he
      exact hj (Bool.xor_right_inj.mp he)
    · intro a ha
      have hneq : σ a ≠ j := by
        intro h
        apply ha
        apply σ.injective
        exact h.trans (σ.apply_symm_apply j).symm
      have heq := hother (σ a) hneq
      simpa only [path, hkl] using congrArg (fun b => u a ^^ b) heq
  · funext j
    simp [path, grayBit, reflectedGray]
  · funext j
    have hlast : (Fin.rev (0 : Fin (2 ^ (n + 1)))).val = 2 ^ (n + 1) - 1 := by
      simp [Fin.rev]
    simp only [path]
    rw [hlast, grayBit_last n (σ j).val (σ j).isLt]
    by_cases hj : j = i
    · subst j
      simp only [σ, Equiv.swap_apply_left, top, Fin.val_mk, decide_true,
        Bool.xor_true]
      cases hu : u i <;> cases hv : v i <;> simp_all
    · have hσ : σ j ≠ top := by
        intro h
        apply hj
        apply σ.injective
        exact h.trans (Equiv.swap_apply_left i top).symm
      have hne : (σ j).val ≠ n := by
        intro h
        apply hσ
        exact Fin.ext h
      simp [hne, hsame j hj]

end Causalean.Mathlib.Topology.SpaceFillingCurve
