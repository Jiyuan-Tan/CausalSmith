module
public import Causalean.Stat.Concentration.BoundedVariation.DyadicGrid

/-!
# Lower dyadic approximation for continuous path controls

This module isolates the integer indexing and zero-control facts needed to
reconstruct a path from compatible dyadic quantile grids. The index chain
approximates every control value, including the right endpoint.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- If a real number x is [at least 0](hyp:hx0) and [at most 1](hyp:hx1),
then [there is a chain of dyadic indices i_k < 2^k, one per level k,
starting at 0, with each next index equal to twice its parent or one more,
such that x lies between i_k/2^k and (i_k + 1)/2^k at every level](goal).
-/
theorem exists_dyadic_lower_chain (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ i : ∀ k : ℕ, Fin (2 ^ k + 1),
      (i 0).val = 0 ∧
      (∀ k, (i k).val < 2 ^ k) ∧
      (∀ k, (i k).val / (2 ^ k : ℝ) ≤ x ∧
        x ≤ ((i k).val + 1) / (2 ^ k : ℝ)) ∧
      (∀ k, (i (k + 1)).val = 2 * (i k).val ∨
        (i (k + 1)).val = 2 * (i k).val + 1) := by
  let d (k : ℕ) := 2 ^ k
  let f (k : ℕ) := ⌊x * (d k : ℝ)⌋₊
  let v (k : ℕ) := min (f k) (d k - 1)
  have hdpos (k : ℕ) : 0 < d k := by simp [d]
  have hvlt (k : ℕ) : v k < d k := by
    dsimp [v]
    exact lt_of_le_of_lt (min_le_right ..) (Nat.sub_lt (hdpos k) (by decide))
  let i (k : ℕ) : Fin (2 ^ k + 1) :=
    ⟨v k, by have := hvlt k; dsimp [d] at this; omega⟩
  refine ⟨i, ?_, ?_, ?_, ?_⟩
  · have : v 0 = 0 := by simp [v, d]
    exact this
  · intro k
    exact hvlt k
  · intro k
    have hnonneg : 0 ≤ x * (d k : ℝ) := by positivity
    have hfloor : (f k : ℝ) ≤ x * (d k : ℝ) := Nat.floor_le hnonneg
    have hfloor' : x * (d k : ℝ) < (f k : ℝ) + 1 := Nat.lt_floor_add_one _
    have hdreal : (0 : ℝ) < (d k : ℝ) := by exact_mod_cast hdpos k
    suffices (v k : ℝ) / (d k : ℝ) ≤ x ∧
        x ≤ ((v k : ℝ) + 1) / (d k : ℝ) by
      simpa [i, d] using this
    by_cases htop : x = 1
    · have hv : v k = d k - 1 := by
        have hf : f k = d k := by simp [f, htop]
        simp [v, hf]
      rw [hv]
      have hdle : 1 ≤ d k := hdpos k
      have hcast : ((d k - 1 : ℕ) : ℝ) = (d k : ℝ) - 1 := by
        rw [Nat.cast_sub hdle]
        norm_num
      rw [htop, hcast]
      constructor
      · apply (div_le_iff₀ hdreal).2
        nlinarith
      · apply (le_div_iff₀ hdreal).2
        nlinarith
    · have hxlt : x < 1 := lt_of_le_of_ne hx1 htop
      have hf_lt : f k < d k := (Nat.floor_lt hnonneg).2 (by
        nlinarith [mul_lt_mul_of_pos_right hxlt hdreal])
      have hv : v k = f k := by simp [v, Nat.le_sub_one_of_lt hf_lt]
      rw [hv]
      constructor
      · apply (div_le_iff₀ hdreal).2
        nlinarith
      · apply (le_div_iff₀ hdreal).2
        linarith
  · intro k
    change v (k + 1) = 2 * v k ∨ v (k + 1) = 2 * v k + 1
    by_cases htop : x = 1
    · have hv (l : ℕ) : v l = d l - 1 := by
        have hf : f l = d l := by simp [f, htop]
        simp [v, hf]
      rw [hv k, hv (k + 1)]
      have hk : 1 ≤ d k := hdpos k
      have hk' : 1 ≤ d (k + 1) := hdpos (k + 1)
      have hd : d (k + 1) = 2 * d k := by simp [d, pow_succ, mul_comm]
      omega
    · have hxlt : x < 1 := lt_of_le_of_ne hx1 htop
      have hf_lt (l : ℕ) : f l < d l := by
        apply (Nat.floor_lt (by positivity : 0 ≤ x * (d l : ℝ))).2
        have hp : (0 : ℝ) < (d l : ℝ) := by exact_mod_cast hdpos l
        nlinarith [mul_lt_mul_of_pos_right hxlt hp]
      have hv (l : ℕ) : v l = f l := by
        simp [v, Nat.le_sub_one_of_lt (hf_lt l)]
      rw [hv k, hv (k + 1)]
      have hdiv : f (k + 1) / 2 = f k := by
        have h := Nat.mul_cast_floor_div_cancel (n := 2) (by decide)
          (x * (d k : ℝ))
        convert h using 1; simp [f, d, pow_succ, mul_comm, mul_left_comm]
      omega

/-- If [a scalar control path dominates the summed squared increments of
n paths over every ordered pair of times](hyp:henergy), then [for any two
times, in either order, the summed squared increments are at most the
absolute difference of the control values](goal).
-/
theorem controlled_path_error_le {n : ℕ} (w : Fin n → Path) (u : Path)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (s t : Time) :
    (∑ j, (w j t - w j s) ^ 2) ≤ |u t - u s| := by
  rcases le_total s t with hst | hts
  · exact (henergy s t hst).trans (le_abs_self _)
  · have h := henergy t s hts
    have hsq : (∑ j, (w j t - w j s) ^ 2) =
        ∑ j, (w j s - w j t) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsq]
    exact h.trans (le_abs_self _ |>.trans_eq (by rw [abs_sub_comm]))

/-- If [a scalar control path dominates the summed squared increments of
n paths over every ordered pair of times](hyp:henergy) and [the control
takes the same value at times s and t](hyp:hst), then [every one of the
paths takes the same value at s and t](goal).
-/
theorem controlled_path_eq_of_same_control {n : ℕ} (w : Fin n → Path)
    (u : Path)
    (henergy : ∀ s t : Time, s ≤ t →
      (∑ j, (w j t - w j s) ^ 2) ≤ u t - u s)
    (s t : Time) (hst : u s = u t) :
    ∀ j, w j s = w j t := by
  have hsum : (∑ j, (w j t - w j s) ^ 2) ≤ 0 := by
    simpa [hst] using controlled_path_error_le w u henergy s t
  intro j
  have hj : (w j t - w j s) ^ 2 ≤ 0 :=
    (Finset.single_le_sum (fun i _ => sq_nonneg (w i t - w i s))
      (Finset.mem_univ j)).trans hsum
  nlinarith [sq_nonneg (w j t - w j s)]

end Causalean.Stat.Concentration.BoundedVariation
