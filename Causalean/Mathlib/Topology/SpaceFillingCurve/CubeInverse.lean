module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.CubeCover

/-!
# Inverse parameters for nested dyadic cube cells

Finite cube covering and compactness give a time whose visited cube contains a
specified point at every level. Shrinking cells then identify that point with
the value of any localized cube map at that time.
-/

public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

private theorem dyadic_interval_parent (q b a p : ℕ) (hq : 0 < q) (hb : 0 < b)
    (h : a / b = p) (z : ℝ)
    (hz : (a : ℝ) / (q * b : ℝ) ≤ z ∧
      z ≤ ((a : ℝ) + 1) / (q * b : ℝ)) :
    (p : ℝ) / q ≤ z ∧ z ≤ ((p : ℝ) + 1) / q := by
  have hlo : b * p ≤ a := by
    rw [← h]
    exact Nat.mul_div_le a b
  have hhi : a + 1 ≤ b * (p + 1) := by
    have := Nat.lt_mul_of_div_lt (by omega : a / b < p + 1) hb
    have hlt : a < b * (p + 1) := by simpa only [Nat.mul_comm] using this
    omega
  have hlo' : (b : ℝ) * p ≤ a := by exact_mod_cast hlo
  have hhi' : (a : ℝ) + 1 ≤ (b : ℝ) * ((p : ℝ) + 1) := by exact_mod_cast hhi
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  constructor
  · apply (div_le_iff₀ hq').2
    have := (div_le_iff₀ (mul_pos hq' hb')).1 hz.1
    nlinarith
  · apply (le_div_iff₀ hq').2
    have := (le_div_iff₀ (mul_pos hq' hb')).1 hz.2
    nlinarith

private theorem dyadicTimeCell_parent {d n : ℕ}
    (k : Fin (2 ^ (d * n))) (l : Fin (2 ^ (d * (n + 1))))
    (h : l.val / 2 ^ d = k.val) :
    dyadicTimeCell d (n + 1) l ⊆ dyadicTimeCell d n k := by
  intro t ht
  have hp := dyadic_interval_parent (2 ^ (d * n)) (2 ^ d) l.val k.val
    (by positivity) (by positivity) h t
  change (k.val : ℝ) / (2 ^ (d * n) : ℝ) ≤ t ∧
    t ≤ ((k.val : ℝ) + 1) / (2 ^ (d * n) : ℝ)
  have hinput : (l.val : ℝ) / ((2 ^ (d * n) * 2 ^ d : ℕ) : ℝ) ≤ t ∧
      t ≤ ((l.val : ℝ) + 1) / ((2 ^ (d * n) * 2 ^ d : ℕ) : ℝ) := by
    simpa [dyadicTimeCell, mul_add, pow_add] using ht
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    hp (by simpa only [Nat.cast_mul] using hinput)

private theorem dyadicCubeCell_parent' {d n : ℕ} (T : DyadicTraversal d)
    (k : Fin (2 ^ (d * n))) (l : Fin (2 ^ (d * (n + 1))))
    (h : l.val / 2 ^ d = k.val) (x : Fin d → ℝ)
    (hx : dyadicCubeCell T (n + 1) l x) : dyadicCubeCell T n k x := by
  intro i
  have hp := dyadic_interval_parent (2 ^ n) 2
    (T.cell (n + 1) l i).val (T.cell n k i).val
    (by positivity) (by omega) (T.nested n k l h i) (x i)
  change ((T.cell n k i).val : ℝ) / (2 ^ n : ℝ) ≤ x i ∧
    x i ≤ (((T.cell n k i).val : ℝ) + 1) / (2 ^ n : ℝ)
  have hinput : ((T.cell (n + 1) l i).val : ℝ) / ((2 ^ n * 2 : ℕ) : ℝ) ≤ x i ∧
      x i ≤ (((T.cell (n + 1) l i).val : ℝ) + 1) / ((2 ^ n * 2 : ℕ) : ℝ) := by
    simpa [dyadicCubeCell, pow_succ] using hx i
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    hp (by simpa only [Nat.cast_mul] using hinput)

/-- Given [a cube dimension](hyp:d), [a dyadic traversal](hyp:T), and [a point certified to lie
in the unit cube](hyp:x,hx), [a unit-interval parameter has compatible cells containing the point at every level](goal). -/
theorem DyadicTraversal.exists_parameter_for_cubePoint {d : ℕ}
    (T : DyadicTraversal d) (x : Fin d → ℝ) (hx : InUnitCube x) :
    ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ n : ℕ, ∃ k : Fin (2 ^ (d * n)),
        t ∈ dyadicTimeCell d n k ∧ dyadicCubeCell T n k x := by
  classical
  let F : ℕ → Set ℝ := fun n =>
    ⋃ k : Fin (2 ^ (d * n)),
      if dyadicCubeCell T n k x then dyadicTimeCell d n k else ∅
  have hclosed (n : ℕ) : IsClosed (F n) := by
    dsimp [F]
    apply isClosed_iUnion_of_finite
    intro k
    split
    · exact isClosed_Icc
    · exact isClosed_empty
  have hnonempty (n : ℕ) : (F n).Nonempty := by
    obtain ⟨k, hk⟩ := T.cubeCell_cover n x hx
    refine ⟨(k.val : ℝ) / (2 ^ (d * n) : ℝ), ?_⟩
    change _ ∈ ⋃ k : Fin (2 ^ (d * n)),
      if dyadicCubeCell T n k x then dyadicTimeCell d n k else ∅
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    simp only [if_pos hk, dyadicTimeCell, Set.mem_Icc]
    constructor
    · exact le_rfl
    · apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hstep (n : ℕ) : F (n + 1) ⊆ F n := by
    intro t ht
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp ht
    have hxl : dyadicCubeCell T (n + 1) l x := by
      by_contra h
      simp [h] at hl
    have htl : t ∈ dyadicTimeCell d (n + 1) l := by
      simpa [hxl] using hl
    have hpow : 2 ^ (d * (n + 1)) = 2 ^ (d * n) * 2 ^ d := by
      simp [mul_add, pow_add]
    let k : Fin (2 ^ (d * n)) :=
      ⟨l.val / 2 ^ d, (Nat.div_lt_iff_lt_mul (by positivity : 0 < 2 ^ d)).2
        (by rw [← hpow]; exact l.isLt)⟩
    have hparent : l.val / 2 ^ d = k.val := rfl
    have hxk := dyadicCubeCell_parent' T k l hparent x hxl
    change t ∈ ⋃ k : Fin (2 ^ (d * n)),
      if dyadicCubeCell T n k x then dyadicTimeCell d n k else ∅
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    simpa [hxk] using dyadicTimeCell_parent k l hparent htl
  have hsubset : F 0 ⊆ Set.Icc (0 : ℝ) 1 := by
    intro t ht
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
    have htk : t ∈ dyadicTimeCell d 0 k := by
      by_cases h : dyadicCubeCell T 0 k x
      · simpa [F, h] using hk
      · simp [h] at hk
    have hk0 : k.val = 0 := by
      have hklt := k.isLt
      simp only [mul_zero, pow_zero] at hklt
      omega
    simpa [dyadicTimeCell, hk0] using htk
  have hcompact : IsCompact (F 0) :=
    isCompact_Icc.of_isClosed_subset (hclosed 0) hsubset
  obtain ⟨t, ht⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hstep hnonempty hcompact hclosed
  refine ⟨t, hsubset ((Set.mem_iInter.mp ht) 0), ?_⟩
  intro n
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ((Set.mem_iInter.mp ht) n)
  by_cases hxk : dyadicCubeCell T n k x
  · exact ⟨k, by simpa [F, hxk] using hk, hxk⟩
  · simp [hxk] at hk

/-- Two cube points that lie together in a traversal cell at every dyadic
depth are equal. -/
theorem DyadicTraversal.eq_of_shared_cubeCells {d : ℕ}
    (T : DyadicTraversal d) (x y : Fin d → ℝ)
    (h : ∀ n : ℕ, ∃ k : Fin (2 ^ (d * n)),
      dyadicCubeCell T n k x ∧ dyadicCubeCell T n k y) : x = y := by
  funext i
  have hbound (n : ℕ) :
      x i - y i ≤ (1 : ℝ) / 2 ^ n ∧ y i - x i ≤ (1 : ℝ) / 2 ^ n := by
    obtain ⟨k, hx, hy⟩ := h n
    have hxi := hx i
    have hyi := hy i
    let a : ℝ := (T.cell n k i).val
    let q : ℝ := 2 ^ n
    have hq : 0 < q := by dsimp [q]; positivity
    change a / q ≤ x i ∧ x i ≤ (a + 1) / q at hxi
    change a / q ≤ y i ∧ y i ≤ (a + 1) / q at hyi
    have hadd : (a + 1) / q = a / q + 1 / q := by ring
    change x i - y i ≤ 1 / q ∧ y i - x i ≤ 1 / q
    constructor <;> linarith
  have hlim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n)
      Filter.atTop (nhds 0) := by
    convert tendsto_pow_atTop_nhds_zero_of_abs_lt_one
      (by norm_num : |(1 / 2 : ℝ)| < 1) using 1
    ext n
    simp [one_div, inv_pow]
  have hxy : x i - y i ≤ 0 :=
    ge_of_tendsto' hlim (fun n => (hbound n).1)
  have hyx : y i - x i ≤ 0 :=
    ge_of_tendsto' hlim (fun n => (hbound n).2)
  linarith

end Causalean.Mathlib.Topology.SpaceFillingCurve
