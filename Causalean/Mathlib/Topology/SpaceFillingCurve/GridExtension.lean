module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.ChildPaths

/-!
# Extending a dyadic grid order by one level

Each parent cell is replaced by a compatible face-adjacent order of its
binary children. This module records the index arithmetic separately from
induction over finite traversals.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a dimension d and level n](hyp:d,n), [a dimension of at least two](hyp:hd), [an order of the level-n dyadic grid cells](hyp:parent),
[its bijectivity](hyp:hbij), and [face adjacency of its consecutive cells](hyp:hadj), [there is a bijective order of the level-(n+1) grid cells
in which consecutive cells are face-adjacent and each consecutive block of 2^d cells consists of the children of the
corresponding parent cell](goal). -/
theorem exists_child_grid_order (d n : ℕ) (hd : 2 ≤ d)
    (parent : Fin (2 ^ (d * n)) → Fin d → Fin (2 ^ n))
    (hbij : Function.Bijective parent)
    (hadj : ∀ k l : Fin (2 ^ (d * n)), l.val = k.val + 1 →
      FaceAdjacentGrid (fun i => (parent k i).val)
        (fun i => (parent l i).val)) :
    ∃ child : Fin (2 ^ (d * (n + 1))) → Fin d → Fin (2 ^ (n + 1)),
      Function.Bijective child ∧
      (∀ k l : Fin (2 ^ (d * (n + 1))), l.val = k.val + 1 →
        FaceAdjacentGrid (fun i => (child k i).val)
          (fun i => (child l i).val)) ∧
      (∀ (k : Fin (2 ^ (d * n))) (l : Fin (2 ^ (d * (n + 1)))),
        l.val / 2 ^ d = k.val →
        ∀ i : Fin d, (child l i).val / 2 = (parent k i).val) := by
  classical
  let P := 2 ^ (d * n)
  let B := 2 ^ d
  let T := 2 ^ (d * (n + 1))
  have hT : T = P * B := by
    dsimp [T, P, B]
    rw [mul_add, mul_one, pow_add]
  have hB : 0 < B := by dsimp [B]; positivity
  let e : Fin P × Fin B ≃ Fin T :=
    finProdFinEquiv.trans (finCongr hT.symm)
  have he (k : Fin P) (a : Fin B) : (e (k, a)).val = B * k.val + a.val := by
    simp [e, finCongr_apply, finProdFinEquiv_apply_val]
    omega
  have hdiv (l : Fin T) : (e.symm l).1.val = l.val / B := by
    have h := he (e.symm l).1 (e.symm l).2
    rw [e.apply_symm_apply] at h
    have ha := (e.symm l).2.isLt
    rw [h, Nat.add_comm, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt ha]
    omega
  have hmod (l : Fin T) : (e.symm l).2.val = l.val % B := by
    have h := he (e.symm l).1 (e.symm l).2
    rw [e.apply_symm_apply] at h
    have ha := (e.symm l).2.isLt
    rw [h, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  obtain ⟨path, hpbij, hpadj, hpbridge⟩ :=
    exists_compatible_child_paths d n hd
      (fun k i => (parent k i).val) hadj
  have hcoord (k : Fin P) (a : Fin B) (i : Fin d) :
      childGridCoord (fun i => (parent k i).val) (path k a) i < 2 ^ (n + 1) := by
    have hk := (parent k i).isLt
    dsimp [childGridCoord]
    rw [pow_succ]
    split <;> omega
  let child : Fin T → Fin d → Fin (2 ^ (n + 1)) :=
    fun l i => ⟨childGridCoord (fun i => (parent (e.symm l).1 i).val)
      (path (e.symm l).1 (e.symm l).2) i,
      hcoord (e.symm l).1 (e.symm l).2 i⟩
  have hchild (k : Fin P) (a : Fin B) (i : Fin d) :
      (child (e (k, a)) i).val =
        2 * (parent k i).val + if path k a i then 1 else 0 := by
    simp [child, childGridCoord]
  have hnest (l : Fin T) (i : Fin d) :
      (child l i).val / 2 = (parent (e.symm l).1 i).val := by
    change (2 * (parent (e.symm l).1 i).val +
      if path (e.symm l).1 (e.symm l).2 i then 1 else 0) / 2 = _
    split <;> omega
  have hcbij : Function.Bijective child := by
    constructor
    · intro l m hlm
      have hk : (e.symm l).1 = (e.symm m).1 := by
        apply hbij.1
        funext i
        apply Fin.ext
        calc
          (parent (e.symm l).1 i).val = (child l i).val / 2 := (hnest l i).symm
          _ = (child m i).val / 2 := by rw [hlm]
          _ = (parent (e.symm m).1 i).val := hnest m i
      have ha : (e.symm l).2 = (e.symm m).2 := by
        apply (hpbij (e.symm m).1).1
        funext i
        have hi := congrFun hlm i
        have hv := congrArg Fin.val hi
        change 2 * (parent (e.symm l).1 i).val +
          (if path (e.symm l).1 (e.symm l).2 i then 1 else 0) =
          2 * (parent (e.symm m).1 i).val +
          (if path (e.symm m).1 (e.symm m).2 i then 1 else 0) at hv
        rw [hk] at hv
        by_cases hb : path (e.symm m).1 (e.symm l).2 i <;>
          by_cases hc : path (e.symm m).1 (e.symm m).2 i <;>
          simp [hb, hc] at hv ⊢
      apply e.symm.injective
      exact Prod.ext hk ha
    · intro y
      have hybound (i : Fin d) : (y i).val / 2 < 2 ^ n := by
        have hi := (y i).isLt
        have hp : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
        have hi' : (y i).val < 2 ^ n * 2 := hp ▸ hi
        omega
      let u : Fin d → Fin (2 ^ n) := fun i => ⟨(y i).val / 2, hybound i⟩
      obtain ⟨k, hk⟩ := hbij.2 u
      let bits : Fin d → Bool := fun i => (y i).val % 2 = 1
      obtain ⟨a, ha⟩ := (hpbij k).2 bits
      refine ⟨e (k, a), ?_⟩
      funext i
      apply Fin.ext
      rw [hchild]
      have hv := (y i).val.mod_add_div 2
      have hr : (y i).val % 2 < 2 := Nat.mod_lt _ (by omega)
      have hk' := congrFun hk i
      have ha' := congrFun ha i
      have hk'' := congrArg Fin.val hk'
      change (parent k i).val = (y i).val / 2 at hk''
      change path k a i = ((y i).val % 2 = 1) at ha'
      rw [hk'', ha']
      by_cases hb : (y i).val % 2 = 1 <;> simp [hb] <;> omega
  have hcadj (k l : Fin T) (hkl : l.val = k.val + 1) :
      FaceAdjacentGrid (fun i => (child k i).val) (fun i => (child l i).val) := by
    let q := (e.symm k).1
    let r := (e.symm k).2
    let q' := (e.symm l).1
    let r' := (e.symm l).2
    have hkval : k.val = B * q.val + r.val := by
      simpa only [q, r, e.apply_symm_apply] using (he q r)
    have hlval : l.val = B * q'.val + r'.val := by
      simpa only [q', r', e.apply_symm_apply] using (he q' r')
    by_cases hsame : q = q'
    · have hrr : r'.val = r.val + 1 := by
        have hr := r.isLt
        have hr' := r'.isLt
        rw [hsame] at hkval
        omega
      obtain ⟨i, hi, hother⟩ := hpadj q r r' hrr
      refine ⟨i, ?_, ?_⟩
      · change (2 * (parent q i).val + if path q r i then 1 else 0) + 1 =
          (2 * (parent q' i).val + if path q' r' i then 1 else 0) ∨
          (2 * (parent q' i).val + if path q' r' i then 1 else 0) + 1 =
          (2 * (parent q i).val + if path q r i then 1 else 0)
        rw [← hsame]
        by_cases hb : path q r i <;> by_cases hc : path q r' i <;>
          simp [hb, hc] at hi ⊢
      · intro j hj
        change 2 * (parent q j).val + (if path q r j then 1 else 0) =
          2 * (parent q' j).val + (if path q' r' j then 1 else 0)
        rw [← hsame, hother j hj]
    · have hq : q'.val = q.val + 1 := by
        have hstep : q'.val = q.val + (if B ∣ k.val + 1 then 1 else 0) := by
          rw [show q'.val = l.val / B from hdiv l,
            show q.val = k.val / B from hdiv k, hkl, Nat.succ_div]
        split_ifs at hstep with hdvd
        · exact hstep
        · have hqeq : q = q' := Fin.ext (by omega)
          exact False.elim (hsame hqeq)
      have hr : r.val = B - 1 := by
        have hr := r.isLt
        have hr' := r'.isLt
        rw [hq] at hlval
        simp only [mul_add, mul_one] at hlval
        omega
      have hr' : r'.val = 0 := by
        have hrr := r.isLt
        have hrr' := r'.isLt
        rw [hq] at hlval
        simp only [mul_add, mul_one] at hlval
        omega
      have hrfin : r = Fin.rev (0 : Fin B) := by
        apply Fin.ext
        simpa using hr
      have hrfin' : r' = 0 := Fin.ext hr'
      simpa only [child, Fin.val_mk, q, q', r, r', hrfin, hrfin'] using
        hpbridge q q' hq
  refine ⟨child, hcbij, hcadj, ?_⟩
  intro k l hkl i
  rw [hnest]
  have hq : (e.symm l).1 = k := Fin.ext ((hdiv l).trans hkl)
  rw [hq]

end Causalean.Mathlib.Topology.SpaceFillingCurve
