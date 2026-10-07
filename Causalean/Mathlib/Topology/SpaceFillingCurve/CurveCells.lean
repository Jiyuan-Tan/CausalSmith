module
public import Causalean.Mathlib.Topology.SpaceFillingCurve.Traversal

/-!
# Dyadic cells for the cube curve

The closed parameter intervals and closed cube cells attached to a coherent
traversal are the finite-scale localization data for its limiting curve.
-/

@[expose] public section

namespace Causalean.Mathlib.Topology.SpaceFillingCurve

/-- Given [a real cube point](hyp:x), [unit-cube membership](goal) is [the condition that every coordinate lies between zero and one](step:1). -/
def InUnitCube {d : ℕ} (x : Fin d → ℝ) : Prop :=
  ∀ i, x i ∈ Set.Icc (0 : ℝ) 1

/-- Given [two real cube points](hyp:x,y), [their squared Euclidean distance](goal) is [the sum of squared coordinate differences](step:1). -/
def sqEuclideanDist {d : ℕ} (x y : Fin d → ℝ) : ℝ :=
  ∑ i, (x i - y i) ^ 2

/-- Given [a dimension d, dyadic level n, and cell index k](hyp:d,n,k), [the dyadic time cell](goal) is [the closed parameter interval from k/2^(dn) to (k+1)/2^(dn)](step:1). -/
def dyadicTimeCell (d n : ℕ) (k : Fin (2 ^ (d * n))) : Set ℝ :=
  Set.Icc ((k.val : ℝ) / (2 ^ (d * n) : ℝ))
    (((k.val : ℝ) + 1) / (2 ^ (d * n) : ℝ))

/-- Given [a traversal, level n, cell index k, and point x](hyp:T,n,k,x), [membership in the dyadic cube cell](goal) is [the condition that each coordinate of x lies in the closed interval from c/2^n to (c+1)/2^n, where c is the matching integer coordinate of the k-th cell the traversal visits at level n](step:1). -/
def dyadicCubeCell {d : ℕ} (T : DyadicTraversal d) (n : ℕ)
    (k : Fin (2 ^ (d * n))) (x : Fin d → ℝ) : Prop :=
  ∀ i, x i ∈ Set.Icc
    (((T.cell n k i).val : ℝ) / (2 ^ n : ℝ))
    ((((T.cell n k i).val : ℝ) + 1) / (2 ^ n : ℝ))

/-- Given [a traversal, parameter, and cube point](hyp:T,t,x), [dyadic-cell-fiber membership](goal) is [membership in every geometric cell whose time interval contains the parameter](step:1). -/
def dyadicCellFiber {d : ℕ} (T : DyadicTraversal d)
    (t : ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ (n : ℕ) (k : Fin (2 ^ (d * n))),
    t ∈ dyadicTimeCell d n k → dyadicCubeCell T n k x

private theorem adjacent_dyadicCubeCell_nonempty {d : ℕ} (T : DyadicTraversal d)
    (n : ℕ) (k l : Fin (2 ^ (d * n))) (hkl : l.val = k.val + 1) :
    ∃ x : Fin d → ℝ, dyadicCubeCell T n k x ∧ dyadicCubeCell T n l x := by
  obtain ⟨j, hj, hs⟩ := T.adjacent n k l hkl
  let q : ℝ := (2 ^ n : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  let x : Fin d → ℝ := fun i =>
    max (((T.cell n k i).val : ℝ) / q) (((T.cell n l i).val : ℝ) / q)
  refine ⟨x, ?_, ?_⟩
  · intro i
    change ((T.cell n k i).val : ℝ) / q ≤ x i ∧
      x i ≤ (((T.cell n k i).val : ℝ) + 1) / q
    constructor
    · exact le_max_left _ _
    · dsimp [x]
      apply max_le
      · apply div_le_div_of_nonneg_right (by norm_num) hq.le
      · have hi : (T.cell n l i).val ≤ (T.cell n k i).val + 1 := by
          by_cases h : i = j
          · subst i; omega
          · rw [hs i h]; omega
        apply (div_le_div_iff_of_pos_right hq).2
        exact_mod_cast hi
  · intro i
    change ((T.cell n l i).val : ℝ) / q ≤ x i ∧
      x i ≤ (((T.cell n l i).val : ℝ) + 1) / q
    constructor
    · exact le_max_right _ _
    · dsimp [x]
      apply max_le
      · have hi : (T.cell n k i).val ≤ (T.cell n l i).val + 1 := by
          by_cases h : i = j
          · subst i; omega
          · rw [hs i h]; omega
        apply (div_le_div_iff_of_pos_right hq).2
        exact_mod_cast hi
      · apply div_le_div_of_nonneg_right (by norm_num) hq.le

private theorem time_cell_index_close (d n : ℕ) (t : ℝ)
    (l : Fin (2 ^ (d * n))) (ht : t ∈ dyadicTimeCell d n l) :
    l.val ≤ min ⌊(2 ^ (d * n) : ℝ) * t⌋₊ (2 ^ (d * n) - 1) ∧
      min ⌊(2 ^ (d * n) : ℝ) * t⌋₊ (2 ^ (d * n) - 1) ≤ l.val + 1 := by
  let q : ℕ := 2 ^ (d * n)
  have hq : (0 : ℝ) < (q : ℝ) := by dsimp [q]; positivity
  have hqn : 0 < q := by dsimp [q]; positivity
  dsimp [dyadicTimeCell] at ht
  have htl : (l.val : ℝ) / (q : ℝ) ≤ t := by
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using ht.1
  have htu : t ≤ ((l.val : ℝ) + 1) / (q : ℝ) := by
    simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using ht.2
  have hlo : (l.val : ℝ) ≤ (q : ℝ) * t := by
    have := (div_le_iff₀ hq).mp htl
    nlinarith
  have hhi : (q : ℝ) * t ≤ ((l.val + 1 : ℕ) : ℝ) := by
    have := (le_div_iff₀ hq).mp htu
    push_cast
    nlinarith
  have hfloorlo : l.val ≤ ⌊(q : ℝ) * t⌋₊ := Nat.le_floor hlo
  have hfloorhi : ⌊(q : ℝ) * t⌋₊ ≤ l.val + 1 := by
    calc
      ⌊(q : ℝ) * t⌋₊ ≤ ⌊((l.val + 1 : ℕ) : ℝ)⌋₊ := Nat.floor_mono hhi
      _ = l.val + 1 := Nat.floor_natCast _
  constructor
  · simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using
      (le_min hfloorlo (Nat.le_sub_one_of_lt l.isLt))
  · simpa only [q, Nat.cast_pow, Nat.cast_ofNat] using
      ((min_le_left _ _).trans hfloorhi)

private theorem subdivide_closed_interval (q b k : ℕ) (t : ℝ)
    (hq : 0 < q) (hb : 0 < b) (hk : k < q)
    (ht : (k : ℝ) / q ≤ t ∧ t ≤ ((k : ℝ) + 1) / q) :
    ∃ l : ℕ, l < q * b ∧ l / b = k ∧
      (l : ℝ) / (q * b : ℕ) ≤ t ∧ t ≤ ((l : ℝ) + 1) / (q * b : ℕ) := by
  let a : ℝ := (q * b : ℕ) * t
  let l : ℕ := min ⌊a⌋₊ ((k + 1) * b - 1)
  have hqb : (0 : ℝ) < (q * b : ℕ) := by exact_mod_cast Nat.mul_pos hq hb
  have hlow : ((k * b : ℕ) : ℝ) ≤ a := by
    have h := (div_le_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mp ht.1
    have hh := mul_le_mul_of_nonneg_right h (by exact_mod_cast hb.le : (0 : ℝ) ≤ b)
    dsimp [a]
    push_cast at hh ⊢
    nlinarith
  have hupp : a ≤ (((k + 1) * b : ℕ) : ℝ) := by
    have h := (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mp ht.2
    have hh := mul_le_mul_of_nonneg_right h (by exact_mod_cast hb.le : (0 : ℝ) ≤ b)
    dsimp [a]
    push_cast at hh ⊢
    nlinarith
  have hleft : k * b ≤ l := by
    dsimp [l]
    apply le_min
    · exact Nat.le_floor hlow
    · have hstep : k * b + 1 ≤ (k + 1) * b := by
        simpa [Nat.add_mul] using Nat.add_le_add_left hb (k * b)
      omega
  have hright : l < (k + 1) * b := by
    dsimp [l]
    have hpos : 0 < (k + 1) * b := Nat.mul_pos (by omega) hb
    omega
  have hqbound : l < q * b := by
    have : (k + 1) * b ≤ q * b := Nat.mul_le_mul_right b hk
    omega
  have hfloor : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le (hlow.trans' (by positivity))
  have ha : (l : ℝ) ≤ a := by
    exact (by exact_mod_cast (min_le_left ⌊a⌋₊ ((k + 1) * b - 1)) : (l : ℝ) ≤ ⌊a⌋₊).trans hfloor
  have hbnd : a ≤ (l : ℝ) + 1 := by
    by_cases h : ⌊a⌋₊ ≤ (k + 1) * b - 1
    · have hl : l = ⌊a⌋₊ := min_eq_left h
      rw [hl]
      exact (Nat.lt_floor_add_one a).le
    · have hl : l = (k + 1) * b - 1 := min_eq_right (by omega)
      rw [hl]
      have : 0 < (k + 1) * b := Nat.mul_pos (by omega) hb
      have hsub : (k + 1) * b - 1 + 1 = (k + 1) * b := by omega
      have hcast : (((k + 1) * b : ℕ) : ℝ) =
          (((k + 1) * b - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast hsub.symm
      exact hupp.trans_eq hcast
  refine ⟨l, hqbound, Nat.div_eq_of_lt_le hleft hright, ?_, ?_⟩
  · exact (div_le_iff₀ hqb).2 (by dsimp [a] at ha; nlinarith)
  · exact (le_div_iff₀ hqb).2 (by dsimp [a] at hbnd; nlinarith)

private theorem half_interval_subset (n a p : ℕ) (h : a / 2 = p) (x : ℝ)
    (hx : (a : ℝ) / (2 ^ (n + 1) : ℝ) ≤ x ∧
      x ≤ ((a : ℝ) + 1) / (2 ^ (n + 1) : ℝ)) :
    (p : ℝ) / (2 ^ n : ℝ) ≤ x ∧
      x ≤ ((p : ℝ) + 1) / (2 ^ n : ℝ) := by
  have hlo : 2 * p ≤ a := by omega
  have hhi : a + 1 ≤ 2 * (p + 1) := by omega
  have hlo' : (2 : ℝ) * p ≤ a := by exact_mod_cast hlo
  have hhi' : (a : ℝ) + 1 ≤ 2 * ((p : ℝ) + 1) := by exact_mod_cast hhi
  have hq : (0 : ℝ) < 2 ^ n := by positivity
  have hq' : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  constructor
  · apply (div_le_iff₀ hq).2
    have h := (div_le_iff₀ hq').mp hx.1
    rw [hpow] at h
    nlinarith
  · apply (le_div_iff₀ hq).2
    have h := (le_div_iff₀ hq').mp hx.2
    rw [hpow] at h
    nlinarith

private theorem dyadicCubeCell_parent {d : ℕ} (T : DyadicTraversal d)
    (n : ℕ) (k : Fin (2 ^ (d * n))) (l : Fin (2 ^ (d * (n + 1))))
    (h : l.val / 2 ^ d = k.val) (x : Fin d → ℝ)
    (hx : dyadicCubeCell T (n + 1) l x) : dyadicCubeCell T n k x := by
  intro i
  exact half_interval_subset n _ _ (T.nested n k l h i) (x i) (hx i)

private theorem time_cell_has_child (d n : ℕ) (t : ℝ)
    (k : Fin (2 ^ (d * n))) (ht : t ∈ dyadicTimeCell d n k) :
    ∃ l : Fin (2 ^ (d * (n + 1))),
      l.val / 2 ^ d = k.val ∧ t ∈ dyadicTimeCell d (n + 1) l := by
  have hpow : 2 ^ (d * (n + 1)) = 2 ^ (d * n) * 2 ^ d := by
    simp [mul_add, pow_add]
  have hq : 0 < 2 ^ (d * n) := by positivity
  have hb : 0 < 2 ^ d := by positivity
  have ht' : (k.val : ℝ) / (2 ^ (d * n) : ℕ) ≤ t ∧
      t ≤ ((k.val : ℝ) + 1) / (2 ^ (d * n) : ℕ) := by
    simpa only [dyadicTimeCell, Set.mem_Icc, Nat.cast_pow, Nat.cast_ofNat] using ht
  obtain ⟨l, hl, hdiv, hleft, hright⟩ :=
    subdivide_closed_interval (2 ^ (d * n)) (2 ^ d) k.val t hq hb k.isLt ht'
  let L : Fin (2 ^ (d * (n + 1))) := ⟨l, by simpa only [hpow] using hl⟩
  refine ⟨L, hdiv, ?_⟩
  change (l : ℝ) / (2 ^ (d * (n + 1)) : ℝ) ≤ t ∧
    t ≤ ((l : ℝ) + 1) / (2 ^ (d * (n + 1)) : ℝ)
  have hreal : (2 ^ (d * (n + 1)) : ℝ) =
      ((2 ^ (d * n) * 2 ^ d : ℕ) : ℝ) := by
    exact_mod_cast hpow
  rw [hreal]
  exact ⟨hleft, hright⟩

private theorem level_fiber_nonempty {d : ℕ} (T : DyadicTraversal d)
    (n : ℕ) (t : ℝ) :
    ∃ x : Fin d → ℝ, ∀ k : Fin (2 ^ (d * n)),
      t ∈ dyadicTimeCell d n k → dyadicCubeCell T n k x := by
  let q : ℕ := 2 ^ (d * n)
  have hq : 0 < q := by dsimp [q]; positivity
  let v : ℕ := min ⌊(q : ℝ) * t⌋₊ (q - 1)
  have hv : v < q := by dsimp [v]; omega
  let k : Fin q := ⟨v, hv⟩
  by_cases hz : v = 0
  · let x : Fin d → ℝ := fun i => ((T.cell n k i).val : ℝ) / (2 ^ n : ℝ)
    refine ⟨x, ?_⟩
    intro l htl
    have hclose := time_cell_index_close d n t l htl
    have hclose' : l.val ≤ v ∧ v ≤ l.val + 1 := by
      simpa only [v, q, Nat.cast_pow, Nat.cast_ofNat] using hclose
    have hl : l.val = k.val := by dsimp [k]; omega
    have heq : l = k := Fin.ext hl
    subst l
    intro i
    change ((T.cell n k i).val : ℝ) / (2 ^ n : ℝ) ≤ x i ∧
      x i ≤ (((T.cell n k i).val : ℝ) + 1) / (2 ^ n : ℝ)
    constructor
    · rfl
    · dsimp [x]
      apply div_le_div_of_nonneg_right (by norm_num)
      positivity
  · let p : Fin q := ⟨v - 1, by omega⟩
    have hpk : k.val = p.val + 1 := by dsimp [k, p]; omega
    obtain ⟨x, hpx, hkx⟩ := adjacent_dyadicCubeCell_nonempty T n p k hpk
    refine ⟨x, ?_⟩
    intro l htl
    have hclose := time_cell_index_close d n t l htl
    have hclose' : l.val ≤ v ∧ v ≤ l.val + 1 := by
      simpa only [v, q, Nat.cast_pow, Nat.cast_ofNat] using hclose
    by_cases hl : l.val = k.val
    · exact (Fin.ext hl : l = k) ▸ hkx
    · have hlp : l.val = p.val := by dsimp [k, p] at *; omega
      exact (Fin.ext hlp : l = p) ▸ hpx

/-- Every parameter in the unit interval has a point in all corresponding
closed dyadic cubes, including both cubes at a subdivision endpoint. -/
theorem dyadicCellFiber_nonempty {d : ℕ} (T : DyadicTraversal d)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x : Fin d → ℝ, dyadicCellFiber T t x := by
  let F : ℕ → Set (Fin d → ℝ) := fun n =>
    {x | ∀ k : Fin (2 ^ (d * n)),
      t ∈ dyadicTimeCell d n k → dyadicCubeCell T n k x}
  have hcellclosed (n : ℕ) (k : Fin (2 ^ (d * n))) :
      IsClosed {x : Fin d → ℝ | dyadicCubeCell T n k x} := by
    have heq : {x : Fin d → ℝ | dyadicCubeCell T n k x} =
        ⋂ i : Fin d, {x : Fin d → ℝ | x i ∈ Set.Icc
          (((T.cell n k i).val : ℝ) / (2 ^ n : ℝ))
          ((((T.cell n k i).val : ℝ) + 1) / (2 ^ n : ℝ))} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, dyadicCubeCell]
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
  have hclosed (n : ℕ) : IsClosed (F n) := by
    have heq : F n = ⋂ k : Fin (2 ^ (d * n)),
        {x : Fin d → ℝ | t ∈ dyadicTimeCell d n k → dyadicCubeCell T n k x} := by
      ext x
      simp only [F, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro k
    by_cases htk : t ∈ dyadicTimeCell d n k
    · simpa [htk] using hcellclosed n k
    · simp [htk]
  have hnonempty (n : ℕ) : (F n).Nonempty := by
    obtain ⟨x, hx⟩ := level_fiber_nonempty T n t
    exact ⟨x, hx⟩
  have hstep (n : ℕ) : F (n + 1) ⊆ F n := by
    intro x hx k htk
    obtain ⟨l, hdiv, htl⟩ := time_cell_has_child d n t k htk
    exact dyadicCubeCell_parent T n k l hdiv x (hx l htl)
  let k0 : Fin (2 ^ (d * 0)) := ⟨0, by simp⟩
  have ht0 : t ∈ dyadicTimeCell d 0 k0 := by
    simpa [dyadicTimeCell, k0] using ht
  have hsubset : F 0 ⊆ Set.Icc (fun _ : Fin d => (0 : ℝ)) (fun _ => 1) := by
    intro x hx
    have hcube := hx k0 ht0
    change (fun _ : Fin d => (0 : ℝ)) ≤ x ∧ x ≤ (fun _ => (1 : ℝ))
    constructor
    · intro i
      have hi := hcube i
      simpa [dyadicCubeCell, k0] using hi.1
    · intro i
      have hi := hcube i
      simpa [dyadicCubeCell, k0] using hi.2
  have hcompact : IsCompact (F 0) :=
    isCompact_Icc.of_isClosed_subset (hclosed 0) hsubset
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hstep hnonempty hcompact hclosed
  exact ⟨x, fun n k htk => (Set.mem_iInter.mp hx n) k htk⟩

/-- A localized cube map sends every closed dyadic parameter cell into its
corresponding closed geometric cube, simultaneously at every depth. -/
structure LocalizedCubeMap (d : ℕ) (T : DyadicTraversal d) where
  toFun : ℝ → Fin d → ℝ
  localizes : ∀ (n : ℕ) (k : Fin (2 ^ (d * n))) (t : ℝ),
    t ∈ dyadicTimeCell d n k → dyadicCubeCell T n k (toFun t)

/-- Given [a cube dimension](hyp:d) and [a coherent dyadic traversal](hyp:T),
[a map localized to its matching dyadic cube cells exists](goal). -/
theorem exists_localizedCubeMap_of_traversal (d : ℕ)
    (T : DyadicTraversal d) : Nonempty (LocalizedCubeMap d T) := by
  let H : ℝ → Fin d → ℝ := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) 1 then
      Classical.choose (dyadicCellFiber_nonempty T t ht)
    else fun _ => 0
  refine ⟨{ toFun := H, localizes := ?_ }⟩
  intro n k t ht
  have hpos : (0 : ℝ) < (2 ^ (d * n) : ℝ) := by positivity
  have hkle : ((k.val : ℝ) + 1) ≤ (2 ^ (d * n) : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt k.isLt)
  have htu : t ∈ Set.Icc (0 : ℝ) 1 := by
    change (k.val : ℝ) / (2 ^ (d * n) : ℝ) ≤ t ∧
      t ≤ ((k.val : ℝ) + 1) / (2 ^ (d * n) : ℝ) at ht
    constructor
    · exact (by positivity : 0 ≤ (k.val : ℝ) / (2 ^ (d * n) : ℝ)).trans ht.1
    · exact ht.2.trans ((div_le_iff₀ hpos).2 (by simpa using hkle))
  have hf := Classical.choose_spec (dyadicCellFiber_nonempty T t htu)
  change dyadicCubeCell T n k (H t)
  dsimp [H]
  rw [dif_pos htu]
  exact hf n k ht

end Causalean.Mathlib.Topology.SpaceFillingCurve
