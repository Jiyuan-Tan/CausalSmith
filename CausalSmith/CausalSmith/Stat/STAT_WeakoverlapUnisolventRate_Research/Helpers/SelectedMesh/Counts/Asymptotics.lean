module
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Elementary asymptotic budgets for selected counts -/
public section
namespace CausalSmith.Stat.WeakOverlap

/-- Every positive power eventually pays for a fixed multiple of the
logarithmic simultaneous-count budget. [For the stated inputs and conditions](hyp:A,p,hA,hp), [the asserted conclusion holds](goal). -/
lemma selectedCount_log_dominated (A p : ℝ) (hA : 0 ≤ A) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      A * Real.log (n : ℝ) ≤ (n : ℝ) ^ p := by
  have hp2 : 0 < p / 2 := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (p / 2))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp2).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (A * (2 / p))))
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hnbase : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_trans (Nat.le_max_right _ _) hn))
  have hpow : A * (2 / p) ≤ (n : ℝ) ^ (p / 2) :=
    hn₀ n (le_trans (Nat.le_max_left _ _) hn)
  have hlog := Real.log_natCast_le_rpow_div n hp2
  have hfactor : A * Real.log (n : ℝ) ≤
      (A * (2 / p)) * (n : ℝ) ^ (p / 2) := by
    have heq : (n : ℝ) ^ (p / 2) / (p / 2) =
        (2 / p) * (n : ℝ) ^ (p / 2) := by field_simp
    rw [heq] at hlog
    exact (mul_le_mul_of_nonneg_left hlog hA).trans_eq (by ring)
  calc
    A * Real.log (n : ℝ) ≤ (A * (2 / p)) * (n : ℝ) ^ (p / 2) := hfactor
    _ ≤ (n : ℝ) ^ (p / 2) * (n : ℝ) ^ (p / 2) := by gcongr
    _ = (n : ℝ) ^ p := by rw [← Real.rpow_add hnbase]; ring_nf

/-- A power also pays for an affine logarithmic union-bound budget. [For the stated inputs and conditions](hyp:A,B,p,hA,hp), [the asserted conclusion holds](goal). -/
lemma selectedCount_affine_log_dominated (A B p : ℝ)
    (hA : 0 ≤ A) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      A * Real.log (n : ℝ) + B ≤ (n : ℝ) ^ p := by
  obtain ⟨n₁, hn₁⟩ := selectedCount_log_dominated (2 * A) p (by positivity) hp
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ p)
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₂, hn₂⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (2 * B)))
  refine ⟨max n₁ n₂, ?_⟩
  intro n hn
  have hlog := hn₁ n (le_trans (Nat.le_max_left _ _) hn)
  have hpow := hn₂ n (le_trans (Nat.le_max_right _ _) hn)
  nlinarith

/-- A faster decaying power eventually lies below any fixed multiple of a
slower decaying one. This places the oracle width above the finest candidate
width when the effective dimension exceeds the ordinary dimension. [For the stated inputs and conditions](hyp:a,b,A,ha,hA), [the asserted conclusion holds](goal). -/
lemma selectedCount_power_gap (a b A : ℝ) (ha : a < b) (hA : 0 < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      2 * (n : ℝ) ^ (-b) ≤ A * (n : ℝ) ^ (-a) := by
  have hp : 0 < b - a := by linarith
  have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (b - a))
      Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (2 / A)))
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hnbase : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_trans (Nat.le_max_right _ _) hn))
  have hgap : 2 / A ≤ (n : ℝ) ^ (b - a) :=
    hn₀ n (le_trans (Nat.le_max_left _ _) hn)
  have hbpos : 0 < (n : ℝ) ^ (-b) := Real.rpow_pos_of_pos hnbase _
  have heq : (n : ℝ) ^ (b - a) * (n : ℝ) ^ (-b) =
      (n : ℝ) ^ (-a) := by
    rw [← Real.rpow_add hnbase]
    congr 1
    ring
  have h := mul_le_mul_of_nonneg_right hgap hbpos.le
  rw [div_mul_eq_mul_div, div_le_iff₀ hA] at h
  calc
    2 * (n : ℝ) ^ (-b) ≤ A *
        ((n : ℝ) ^ (b - a) * (n : ℝ) ^ (-b)) := by nlinarith
    _ = A * (n : ℝ) ^ (-a) := by rw [heq]

/-- A fixed multiple of a negative power is eventually at most one.  This
places a fixed enlargement of the oracle width below the coarsest mesh. [For the stated inputs and conditions](hyp:p,A,hp,hA), [the asserted conclusion holds](goal). -/
lemma selectedCount_power_eventually_le_one (p A : ℝ)
    (hp : 0 < p) (hA : 0 < A) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, A * (n : ℝ) ^ (-p) ≤ 1 := by
  obtain ⟨n₀, hn₀⟩ := selectedCount_power_gap 0 p (2 / A) hp (by positivity)
  refine ⟨n₀, ?_⟩
  intro n hn
  have h := hn₀ n hn
  have hAne : A ≠ 0 := ne_of_gt hA
  simp only [neg_zero, Real.rpow_zero, mul_one] at h
  calc
    A * (n : ℝ) ^ (-p) ≤ A * (1 / A) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      have hdiv : 2 * (n : ℝ) ^ (-p) ≤ 2 / A := by simpa using h
      have heq : 2 / A = 2 * (1 / A) := by ring
      linarith
    _ = 1 := by field_simp

/-- A positive fixed fraction of a power eventually pays for an affine
logarithmic budget. [For the stated inputs and conditions](hyp:A,B,p,R,hA,hp,hR), [the asserted conclusion holds](goal). -/
lemma selectedCount_affine_log_dominated_scaled (A B p R : ℝ)
    (hA : 0 ≤ A) (hp : 0 < p) (hR : 0 < R) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      A * Real.log (n : ℝ) + B ≤ R * (n : ℝ) ^ p := by
  obtain ⟨n₀, hn₀⟩ :=
    selectedCount_affine_log_dominated (A / R) (B / R) p
      (div_nonneg hA hR.le) hp
  refine ⟨n₀, ?_⟩
  intro n hn
  have h := hn₀ n hn
  have hmul := mul_le_mul_of_nonneg_left h hR.le
  calc
    A * Real.log (n : ℝ) + B =
        R * (A / R * Real.log (n : ℝ) + B / R) := by
      field_simp
    _ ≤ R * (n : ℝ) ^ p := hmul

/-- Choose a single oracle enlargement large enough for the effective
dimension mass inequality. [For the stated inputs and conditions](hyp:κ,p,hκ,hp), [the asserted conclusion holds](goal). -/
lemma selectedCount_oracle_enlargement (κ p : ℝ)
    (hκ : 0 < κ) (hp : 0 < p) :
    ∃ A : ℝ, 1 ≤ A ∧ 4 ≤ κ * A ^ p := by
  have ht : Filter.Tendsto (fun A : ℝ => A ^ p)
      Filter.atTop Filter.atTop := tendsto_rpow_atTop hp
  obtain ⟨A₀, hA₀⟩ := Filter.eventually_atTop.1
    (ht.eventually (Filter.eventually_ge_atTop (4 / κ)))
  let A := max 1 A₀
  have hA : 1 ≤ A := le_max_left _ _
  have hpow : 4 / κ ≤ A ^ p := hA₀ A (le_max_right _ _)
  refine ⟨A, hA, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hpow hκ.le
  calc
    4 = κ * (4 / κ) := by field_simp
    _ ≤ κ * A ^ p := hmul

/-- At an oracle-order width, the inverse-squared smoothness threshold
eventually dominates any affine logarithmic count budget. [For the stated inputs and conditions](hyp:A,β,q,U,V,hA,hβ,hq,hU), [the asserted conclusion holds](goal). -/
lemma selectedCount_oracle_inverse_log_budget
    (A β q U V : ℝ) (hA : 0 < A) (hβ : 0 < β) (hq : 0 < q)
    (hU : 0 ≤ U) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      U * Real.log (n : ℝ) + V ≤
        (A * (n : ℝ) ^ (-(1 : ℝ) / q)) ^ (-2 * β) := by
  have hp : 0 < 2 * β / q := by positivity
  have hR : 0 < A ^ (-2 * β) := Real.rpow_pos_of_pos hA _
  obtain ⟨n₀, hn₀⟩ :=
    selectedCount_affine_log_dominated_scaled U V (2 * β / q)
      (A ^ (-2 * β)) hU hp hR
  refine ⟨max n₀ 1, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one
      (Nat.le_trans (Nat.le_max_right _ _) hn))
  calc
    U * Real.log (n : ℝ) + V ≤
        A ^ (-2 * β) * (n : ℝ) ^ (2 * β / q) :=
      hn₀ n (le_trans (Nat.le_max_left _ _) hn)
    _ = (A * (n : ℝ) ^ (-(1 : ℝ) / q)) ^ (-2 * β) := by
      rw [Real.mul_rpow hA.le (Real.rpow_nonneg hnpos.le _)]
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      field_simp
end CausalSmith.Stat.WeakOverlap
