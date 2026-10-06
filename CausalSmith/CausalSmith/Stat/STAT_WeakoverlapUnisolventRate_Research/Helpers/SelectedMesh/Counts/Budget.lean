module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Base
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.SelectedMesh.Counts.Asymptotics

/-! # Finite-family count budget for selected meshes -/
public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory
open scoped Classical

/-- The number of candidate treated microcells is the geometric count of
dyadic cubes times the fixed number of template cells. [For the stated inputs and conditions](hyp:d,n,m,β), [the asserted conclusion holds](goal). -/
lemma candidateTreatedCell_card (d n m : ℕ) (β : ℝ) :
    Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1))) =
      ∑ j ∈ meshIndices d n β, (2 ^ j) ^ d * (m + 1) ^ d := by
  classical
  simp only [Fintype.card_sigma, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_fin]
  exact Finset.sum_attach (meshIndices d n β)
    (fun j : ℕ => (2 ^ j) ^ d * (m + 1) ^ d)

/-- A finite candidate-family bound for setting the simultaneous deviation
budget. [For the stated inputs and conditions](hyp:d,n,m,β), [the asserted conclusion holds](goal). -/
lemma candidateTreatedCell_card_bound (d n m : ℕ) (β : ℝ) :
    Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1))) ≤
      (maxMeshIndex d n β + 1) *
        ((2 ^ maxMeshIndex d n β) ^ d * (m + 1) ^ d) := by
  rw [candidateTreatedCell_card]
  calc
    ∑ j ∈ meshIndices d n β, (2 ^ j) ^ d * (m + 1) ^ d ≤
        ∑ _j ∈ meshIndices d n β,
          (2 ^ maxMeshIndex d n β) ^ d * (m + 1) ^ d := by
      apply Finset.sum_le_sum
      intro j hj
      have hjle : j ≤ maxMeshIndex d n β := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp (by simpa [meshIndices] using hj))
      gcongr
      omega
    _ = _ := by simp [meshIndices]

/-- A logarithmic budget pays for the full finite family of candidate cells
and leaves an inverse-square failure probability. [For the stated inputs and conditions](hyp:d,n,β,hn), [the asserted conclusion holds](goal). -/
lemma selectedCount_log_budget (d n : ℕ) (β : ℝ) (hn : 2 ≤ n) :
    let M := Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) ×
          (Fin d → Fin (polynomialDegree β + 1)))
    let s := Real.log (2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2)
    0 < s ∧ 2 * (M : ℝ) * Real.exp (-s) ≤ (n : ℝ) ^ (-2 : ℝ) := by
  dsimp
  let M : ℕ := Fintype.card
    (Σ j : {j // j ∈ meshIndices d n β},
      (Fin d → Fin (2 ^ j.val)) ×
        (Fin d → Fin (polynomialDegree β + 1)))
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hx : 0 < 2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2 := by positivity
  have hx1 : 1 < 2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  constructor
  · exact Real.log_pos hx1
  · rw [Real.exp_neg, Real.exp_log hx]
    rw [Real.rpow_neg hn'.le]
    change 2 * (M : ℝ) * (2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2)⁻¹ ≤
      ((n : ℝ) ^ 2)⁻¹
    rw [← div_eq_mul_inv, inv_eq_one_div]
    rw [show (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ (2 : ℕ) by norm_num]
    apply (div_le_div_iff₀ hx (sq_pos_of_pos hn')).2
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ 2 from by norm_num) hM,
      sq_pos_of_pos hn']


/-- The largest candidate dyadic denominator is at most the sample size. [For the stated inputs and conditions](hyp:d,n,β,hn,hden), [the asserted conclusion holds](goal). -/
lemma selectedCount_index_pow_le (d n : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hden : 1 ≤ 2 * β + d) :
    (2 : ℝ) ^ maxMeshIndex d n β ≤ n := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn'
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let x : ℝ := Real.log n / Real.log 2 / (2 * β + d)
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hfloor : (maxMeshIndex d n β : ℝ) ≤ x := by
    simpa only [maxMeshIndex, x] using Nat.floor_le hx
  have hmul : Real.log 2 * (maxMeshIndex d n β : ℝ) ≤ Real.log n := by
    have h := mul_le_mul_of_nonneg_left hfloor hlog2.le
    have hq : 0 < 2 * β + (d : ℝ) := by linarith
    have : Real.log 2 * x = Real.log n / (2 * β + d) := by
      dsimp [x]
      field_simp
    rw [this] at h
    exact h.trans ((div_le_iff₀ hq).2 (by nlinarith))
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact (Real.exp_le_exp.mpr hmul).trans_eq (Real.exp_log (by positivity))

/-- The simultaneous-count family has a polynomial size bound. [For the stated inputs and conditions](hyp:d,n,m,β,hn,hden), [the asserted conclusion holds](goal). -/
lemma selectedCount_card_polynomial_bound (d n m : ℕ) (β : ℝ)
    (hn : 1 ≤ n) (hden : 1 ≤ 2 * β + d) :
    Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1))) ≤
      (n + 1) * (n ^ d * (m + 1) ^ d) := by
  have hpow : 2 ^ maxMeshIndex d n β ≤ n := by
    exact_mod_cast selectedCount_index_pow_le d n β hn hden
  have hj : maxMeshIndex d n β ≤ 2 ^ maxMeshIndex d n β := by
    induction maxMeshIndex d n β with
    | zero => simp
    | succ j ih =>
        have hp : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        simp only [pow_succ]
        omega
  calc
    Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1))) ≤
        (maxMeshIndex d n β + 1) *
          ((2 ^ maxMeshIndex d n β) ^ d * (m + 1) ^ d) :=
      candidateTreatedCell_card_bound d n m β
    _ ≤ (n + 1) * (n ^ d * (m + 1) ^ d) := by
      gcongr
      · omega

/-- The logarithm of the count family grows at most as an affine log sample size. [For the stated inputs and conditions](hyp:d,n,m,β,hn,hden), [the asserted conclusion holds](goal). -/
lemma selectedCount_log_card_bound (d n m : ℕ) (β : ℝ)
    (hn : 2 ≤ n) (hden : 1 ≤ 2 * β + d) :
    let M := Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1)))
    Real.log (2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2) ≤
      (d + 3 : ℝ) * Real.log n +
        Real.log (8 * ((m + 1 : ℝ) ^ d + 1)) := by
  dsimp
  let M : ℕ := Fintype.card
      (Σ j : {j // j ∈ meshIndices d n β},
        (Fin d → Fin (2 ^ j.val)) × (Fin d → Fin (m + 1)))
  have hcard : M ≤ (n + 1) * (n ^ d * (m + 1) ^ d) :=
    selectedCount_card_polynomial_bound d n m β (by omega) hden
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ (m + 1 : ℝ) ^ d := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hcast : (M : ℝ) ≤ ((n : ℝ) + 1) * ((n : ℝ) ^ d * (m + 1 : ℝ) ^ d) := by
    exact_mod_cast hcard
  have hN : (n : ℝ) + 1 ≤ 2 * n := by linarith
  have hpow : 1 ≤ (n : ℝ) ^ d := one_le_pow₀ hn1
  have hcore : (M : ℝ) + 1 ≤ 2 * (n : ℝ) * (n : ℝ)^d *
      ((m + 1 : ℝ)^d + 1) := by
    have hpart : ((n : ℝ) + 1) * ((n : ℝ)^d * (m + 1 : ℝ)^d) ≤
        (2 * (n : ℝ)) * ((n : ℝ)^d * (m + 1 : ℝ)^d) := by gcongr
    have hone : 1 ≤ (n : ℝ) * (n : ℝ)^d := by nlinarith
    nlinarith
  have hbound : 2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2 ≤
      8 * ((m + 1 : ℝ) ^ d + 1) * (n : ℝ) ^ (d + 3) := by
    rw [pow_add]
    have h := mul_le_mul_of_nonneg_right hcore (show (0 : ℝ) ≤ 2 * (n : ℝ)^2 by positivity)
    have h3 : (n : ℝ)^3 = (n : ℝ) * (n : ℝ)^2 := by ring
    rw [h3]
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ ((m + 1 : ℝ)^d + 1) by positivity)
      (show (0 : ℝ) ≤ (n : ℝ)^d * (n : ℝ)^3 by positivity)]
  have hlog := Real.log_le_log (by positivity : 0 < 2 * ((M : ℝ) + 1) * (n : ℝ) ^ 2) hbound
  have heq : Real.log (8 * ((m + 1 : ℝ) ^ d + 1) * (n : ℝ) ^ (d + 3)) =
      (d + 3 : ℝ) * Real.log n +
        Real.log (8 * ((m + 1 : ℝ) ^ d + 1)) := by
    rw [Real.log_mul (by positivity : 8 * ((m + 1 : ℝ)^d + 1) ≠ 0)
      (by positivity : (n : ℝ)^(d+3) ≠ 0), Real.log_pow]
    push_cast
    ring
  exact hlog.trans_eq heq


end CausalSmith.Stat.WeakOverlap
