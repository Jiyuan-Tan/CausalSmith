module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Nonnegative chain weights for the factorial derivative bound

The increasing-chain argument for `factorial_derivatives`: fixed-size subset
products admit a factorial bound, shifted-Legendre weights sum to the square
of the basis dimension, and squared matrix entries bound coefficient-vector norms.
The identification of iterated polynomial differentiation with these chains
remains in `Kernel.lean`.
-/

public section
open scoped BigOperators
namespace CausalSmith.Stat.RdTruesideNoiseFrontier
/-- The constant and linear binomial terms are bounded by the full power. Given [the displayed inputs and assumptions](hyp:S,a,hS,ha,n), [the stated mathematical conclusion holds](goal). -/
lemma nonnegative_power_linear_terms_le (S a : ℝ) (hS : 0 ≤ S) (ha : 0 ≤ a) (n : ℕ) :
    S^(n+1) + (n+1 : ℝ)*a*S^n ≤ (S+a)^(n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm := mul_le_mul_of_nonneg_right ih (add_nonneg hS ha)
    have hp : 0 ≤ (n+1 : ℝ)*a^2*S^n := by positivity
    calc
      _ ≤ (S^(n+1) + (n+1 : ℝ)*a*S^n)*(S+a) := by
        simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
        nlinarith
      _ ≤ _ := by simpa only [pow_succ, Nat.add_assoc] using hm

/-- Splitting fixed-size subsets according to a newly inserted element gives
an exact recurrence for their weighted products. Given [the displayed inputs and assumptions](hyp:α,s,a,ha,w,r), [the stated mathematical conclusion holds](goal). -/
lemma subset_product_sum_insert {α : Type*} [DecidableEq α]
    (s : Finset α) (a : α) (ha : a ∉ s) (w : α → ℝ) (r : ℕ) :
    (∑ t ∈ (insert a s).powersetCard (r+1), ∏ i ∈ t, w i) =
      (∑ t ∈ s.powersetCard (r+1), ∏ i ∈ t, w i) +
      w a * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i) := by
  rw [Finset.powersetCard_succ_insert ha, Finset.sum_union]
  · rw [Finset.sum_image]
    · congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t ht
      exact Finset.prod_insert (fun hat => ha ((Finset.mem_powersetCard.mp ht).1 hat))
    · intro t ht u hu h
      have ht' : a ∉ t := fun hat => ha ((Finset.mem_powersetCard.mp ht).1 hat)
      have hu' : a ∉ u := fun hau => ha ((Finset.mem_powersetCard.mp hu).1 hau)
      simpa [ht', hu'] using congrArg (Finset.erase · a) h
  · apply Finset.disjoint_left.mpr
    intro t ht hi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hi
    exact ha ((Finset.mem_powersetCard.mp ht).1 (Finset.mem_insert_self a u))

/-- Each increasing chain contributes once to a fixed-size subset sum; its
factorial multiple is bounded by the full nonnegative power expansion. Given [the displayed inputs and assumptions](hyp:α,s,w,hw,r), [the stated mathematical conclusion holds](goal). -/
lemma subset_product_sum_factorial_bound {α : Type*}
    (s : Finset α) (w : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (r : ℕ) :
    (Nat.factorial r : ℝ) * (∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i) ≤
      (∑ i ∈ s, w i)^r := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty =>
    cases r with
    | zero => simp [Finset.powersetCard_zero]
    | succ r =>
      rw [Finset.powersetCard_eq_empty.mpr (by simp)]
      simp
  | @insert a s ha ih =>
    have hwa := hw a (Finset.mem_insert_self a s)
    have hws : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (Finset.mem_insert_of_mem hi)
    have hS : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hws
    cases r with
    | zero => simp [Finset.powersetCard_zero]
    | succ r =>
      rw [subset_product_sum_insert s a ha, Finset.sum_insert ha]
      have h0 := ih hws (r+1)
      have h1 := mul_le_mul_of_nonneg_left (ih hws r) (show 0 ≤ (r+1 : ℝ)*w a by positivity)
      have hsum := add_le_add h0 h1
      calc
        _ = (Nat.factorial (r+1) : ℝ) * (∑ t ∈ s.powersetCard (r+1), ∏ i ∈ t, w i) +
            (r+1 : ℝ)*w a*((Nat.factorial r : ℝ)*(∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i)) := by
          rw [Nat.factorial_succ]
          push_cast
          ring
        _ ≤ (∑ i ∈ s, w i)^(r+1) + (r+1 : ℝ)*w a*(∑ i ∈ s, w i)^r := hsum
        _ ≤ _ := by simpa [add_comm] using nonnegative_power_linear_terms_le _ _ hS hwa r
/-- Deleting restrictions on nonnegative chain weights bounds any retained
collection of distinct-index products by the total weight power divided by its factorial. Given [the displayed inputs and assumptions](hyp:α,s,w,hw,r,keep), [the stated mathematical conclusion holds](goal). -/
lemma filtered_subset_product_sum_le {α : Type*}
    (s : Finset α) (w : α → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (r : ℕ) (keep : Finset α → Prop) [DecidablePred keep] :
    (∑ t ∈ (s.powersetCard r).filter keep, ∏ i ∈ t, w i) ≤
      (∑ i ∈ s, w i)^r / (Nat.factorial r : ℝ) := by
  classical
  have hsub : (∑ t ∈ (s.powersetCard r).filter keep, ∏ i ∈ t, w i) ≤
      ∑ t ∈ s.powersetCard r, ∏ i ∈ t, w i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro t ht hnot
    exact Finset.prod_nonneg (fun i hi => hw i ((Finset.mem_powersetCard.mp ht).1 hi))
  apply hsub.trans
  rw [le_div_iff₀ (by positivity)]
  simpa only [mul_comm] using subset_product_sum_factorial_bound s w hw r

/-- The total shifted-Legendre endpoint weight is the square of the basis dimension. Given [the displayed inputs and assumptions](hyp:m), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_total_weight (m : ℕ) :
    (∑ i ∈ Finset.range (m+1), (2*(i : ℝ)+1)) = ((m : ℝ)+1)^2 := by
  have hs (n : ℕ) : (∑ i ∈ Finset.range n, (2*(i : ℝ)+1)) = (n : ℝ)^2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simpa using hs (m+1)

/-- The increasing-chain factor in the jth derivative matrix has the roadmap's
factorial bound, even after arbitrary parity and endpoint restrictions. Given [the displayed inputs and assumptions](hyp:m,j,keep), [the stated mathematical conclusion holds](goal). -/
lemma shiftedLegendre_chain_weight_bound (m j : ℕ)
    (keep : Finset ℕ → Prop) [DecidablePred keep] :
    (∑ t ∈ ((Finset.range (m+1)).powersetCard (j-1)).filter keep,
      ∏ i ∈ t, (2*(i : ℝ)+1)) ≤
      ((m : ℝ)+1)^(2*(j-1)) / (Nat.factorial (j-1) : ℝ) := by
  have h := filtered_subset_product_sum_le (Finset.range (m+1))
    (fun i => 2*(i : ℝ)+1) (by intro i hi; positivity) (j-1) keep
  rw [shiftedLegendre_total_weight, ← pow_mul] at h
  exact h

/-- The loss of one factorial index in the chain bound is absorbed by the
extra factor two per derivative, as in the last inequality of the roadmap. Given [the displayed inputs and assumptions](hyp:j,hj), [the stated mathematical conclusion holds](goal). -/
lemma derivative_chain_factorial_gain (j : ℕ) (hj : 1 ≤ j) :
    (2 : ℝ)^j / (Nat.factorial (j-1) : ℝ) ≤
      (4 : ℝ)^j / (Nat.factorial j : ℝ) := by
  have hnat (n : ℕ) : n ≤ 2^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
      omega
  have hreal : (j : ℝ) ≤ (2 : ℝ)^j := by exact_mod_cast hnat j
  have hfact : (Nat.factorial j : ℝ) = (j : ℝ)*(Nat.factorial (j-1) : ℝ) := by
    have hf := Nat.factorial_succ (j-1)
    rw [Nat.sub_add_cancel hj] at hf
    exact_mod_cast hf
  have hpow : (4 : ℝ)^j = (2 : ℝ)^j * (2 : ℝ)^j := by
    rw [← mul_pow]
    norm_num
  rw [div_le_div_iff₀ (by positivity) (by positivity), hfact, hpow]
  have h := mul_le_mul_of_nonneg_left hreal
    (show 0 ≤ (2 : ℝ)^j * (Nat.factorial (j-1) : ℝ) by positivity)
  nlinarith

/-- Bounding every squared matrix entry bounds its action by the squared
Frobenius norm; this is the coefficient-vector estimate in the roadmap. Given [the displayed inputs and assumptions](hyp:α,s,D,c), [the stated mathematical conclusion holds](goal). -/
lemma finite_matrix_square_action_bound {α : Type*} (s : Finset α)
    (D : α → α → ℝ) (c : α → ℝ) :
    (∑ k ∈ s, (∑ l ∈ s, D k l * c l)^2) ≤
      (∑ k ∈ s, ∑ l ∈ s, (D k l)^2) * (∑ l ∈ s, (c l)^2) := by
  calc
    _ ≤ ∑ k ∈ s, (∑ l ∈ s, (D k l)^2) * (∑ l ∈ s, (c l)^2) := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
        (f := fun l => (D k l)^2) (g := fun l => (c l)^2)
        (by intro l hl; positivity) (by intro l hl; positivity)
        (by intro l hl; simp [mul_pow])
    _ = _ := by rw [Finset.sum_mul]

/-- The separable endpoint weights in the chain entry bound give the full
basis-dimension factor after summing the squared matrix entries. Given [the displayed inputs and assumptions](hyp:α,s,D,c,w,A,hD), [the stated mathematical conclusion holds](goal). -/
lemma weighted_matrix_square_action_bound {α : Type*} (s : Finset α)
    (D : α → α → ℝ) (c w : α → ℝ) (A : ℝ)
    (hD : ∀ k ∈ s, ∀ l ∈ s, (D k l) ^ 2 ≤ A ^ 2 * w k * w l) :
    (∑ k ∈ s, (∑ l ∈ s, D k l * c l)^2) ≤
      A^2 * (∑ k ∈ s, w k)^2 * (∑ l ∈ s, (c l)^2) := by
  have hmass : (∑ k ∈ s, ∑ l ∈ s, (D k l)^2) ≤ A^2 * (∑ k ∈ s, w k)^2 := by
    calc
      _ ≤ ∑ k ∈ s, ∑ l ∈ s, A^2*w k*w l := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.sum_le_sum (fun l hl => hD k hk l hl)
      _ = _ := by simp_rw [← Finset.mul_sum]; rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  exact (finite_matrix_square_action_bound s D c).trans
    (mul_le_mul_of_nonneg_right hmass (Finset.sum_nonneg (fun l hl => sq_nonneg _)))

end CausalSmith.Stat.RdTruesideNoiseFrontier
