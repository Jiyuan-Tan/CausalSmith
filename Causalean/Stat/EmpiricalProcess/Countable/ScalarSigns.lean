module
public import Causalean.Stat.EmpiricalProcess.Countable.FiniteAverage
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Exact scalar fourth moments of finite signs

The finite Boolean average of a signed sum has fourth moment exactly three
times squared energy minus twice the sum of coefficient fourth powers. This
algebraic layer is independent of martingales and maximal estimates.
-/

@[expose] public section

open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- Flipping [one coordinate](hyp:j) is [an equivalence of finite Boolean sign
vectors](goal). -/
def signFlipEquiv {ι : Type*} [DecidableEq ι] (j : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun σ := Function.update σ j (!(σ j))
  invFun σ := Function.update σ j (!(σ j))
  left_inv σ := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hi]
  right_inv σ := by
    funext i
    by_cases hi : i = j
    · subst i
      simp
    · simp [Function.update_of_ne hi]

/-- Complementing [a Boolean value](hyp:b) [negates its scalar sign](goal). -/
theorem boolSign_not (b : Bool) :
    (if !b then (1 : ℝ) else -1) = -(if b then (1 : ℝ) else -1) := by
  cases b <;> norm_num

/-- Over [any finite coordinate type](hyp:ι), the unnormalized sum of [one
Boolean sign coordinate](hyp:j) [vanishes](goal). -/
theorem signCoordinate_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    (∑ σ : ι → Bool, if σ j then (1 : ℝ) else -1) = 0 := by
  classical
  have h := (signFlipEquiv j).sum_comp (fun σ => if σ j then (1 : ℝ) else -1)
  simp only [signFlipEquiv, Equiv.coe_fn_mk, Function.update_self, boolSign_not,
    Finset.sum_neg_distrib] at h
  linarith

/-- Over [any finite coordinate type](hyp:ι), the unnormalized product sum of
[two distinct Boolean sign coordinates](hyp:j,k,hjk) [vanishes](goal). -/
theorem signCoordinate_mul_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j k : ι) (hjk : j ≠ k) :
    (∑ σ : ι → Bool,
      (if σ j then (1 : ℝ) else -1) * (if σ k then (1 : ℝ) else -1)) = 0 := by
  classical
  have h := (signFlipEquiv j).sum_comp (fun σ =>
    (if σ j then (1 : ℝ) else -1) * (if σ k then (1 : ℝ) else -1))
  simp only [signFlipEquiv, Equiv.coe_fn_mk, Function.update_self,
    Function.update_of_ne hjk.symm, boolSign_not, neg_mul, Finset.sum_neg_distrib] at h
  linarith

/-- Over [any finite coordinate type](hyp:ι), every [real linear combination
of Boolean signs](hyp:a) has [unnormalized sum zero](goal). -/
theorem signLinear_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (∑ σ : ι → Bool, ∑ j, (if σ j then (1 : ℝ) else -1) * a j) = 0 := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, signCoordinate_sum, zero_mul, Finset.sum_const_zero]

/-- Over [any finite coordinate type](hyp:ι), the unnormalized [second moment
of a real linear combination of Boolean signs](hyp:a) [equals the number of
sign vectors times the coefficient energy](goal). -/
theorem signLinear_sq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (∑ σ : ι → Bool, (∑ j, (if σ j then (1 : ℝ) else -1) * a j) ^ 2) =
      (Fintype.card (ι → Bool) : ℝ) * ∑ j, a j ^ 2 := by
  classical
  simp_rw [pow_two, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rw [Finset.mul_sum])
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_comm]
  have hterm (k : ι) :
      (∑ σ : ι → Bool,
        ((if σ j then (1 : ℝ) else -1) * a j) *
          ((if σ k then (1 : ℝ) else -1) * a k)) =
        if k = j then (Fintype.card (ι → Bool) : ℝ) * (a j * a j) else 0 := by
    simp_rw [show ∀ σ : ι → Bool,
      ((if σ j then (1 : ℝ) else -1) * a j) *
          ((if σ k then (1 : ℝ) else -1) * a k) =
        ((if σ j then (1 : ℝ) else -1) * (if σ k then (1 : ℝ) else -1)) *
          (a j * a k) by
      intro σ
      ring, ← Finset.sum_mul]
    by_cases hk : k = j
    · subst k
      simp only [if_true]
      simp_rw [show ∀ b : Bool,
        (if b then (1 : ℝ) else -1) * (if b then (1 : ℝ) else -1) = 1 by
          intro b
          cases b <;> norm_num]
      simp
    · rw [if_neg hk, signCoordinate_mul_sum j k (Ne.symm hk), zero_mul]
  simp_rw [hterm]
  simp [pow_two]

/-- For [a real function of n + 1 Boolean signs](hyp:H), [its sum over all sign patterns equals the
sum, over the patterns of the remaining n signs, of its values with the first sign set to true and
to false](goal). -/
theorem signSum_succ {n : ℕ} (H : (Fin (n + 1) → Bool) → ℝ) :
    (∑ σ, H σ) = ∑ σ : Fin n → Bool, (H (Fin.cons true σ) + H (Fin.cons false σ)) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun z => H (Fin.cons z.1 z.2)) H (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib]

/-- For [n real coefficients](hyp:n,a), [summing over all 2^n sign patterns, the squared signed sum
of the coefficients totals 2^n times the sum of squared coefficients, and its fourth power totals
2^n times three times the squared sum of squares minus twice the sum of fourth powers](goal). -/
theorem signSum_moments (n : ℕ) (a : Fin n → ℝ) :
    (∑ σ : Fin n → Bool, (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^2) =
      (2 : ℝ)^n * (∑ j, a j^2) ∧
    (∑ σ : Fin n → Bool, (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4) =
      (2 : ℝ)^n * (3 * (∑ j, a j^2)^2 - 2 * ∑ j, a j^4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ih (fun j => a j.succ)
    constructor
    · rw [signSum_succ]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Bool.false_eq_true, if_true, if_false, one_mul, neg_one_mul]
      simp_rw [show ∀ s : ℝ, (a 0 + s)^2 + (-a 0 + s)^2 =
        2 * s^2 + 2 * (a 0)^2 by intro s; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [h.1, pow_succ]
      ring
    · rw [signSum_succ]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
        Bool.false_eq_true, if_true, if_false, one_mul, neg_one_mul]
      simp_rw [show ∀ s : ℝ, (a 0 + s)^4 + (-a 0 + s)^4 =
        2 * s^4 + 12 * (a 0)^2 * s^2 + 2 * (a 0)^4 by intro s; ring]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      rw [h.1, h.2, pow_succ]
      ring

/-- For [real coefficients](hyp:a), [the fourth moment of their finite Rademacher sum equals
exactly three times the squared sum of squared coefficients minus twice the sum of their fourth
powers](goal). -/
theorem signAverage_fourth_exact {n : ℕ} (a : Fin n → ℝ) :
    signAverage (fun σ => (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4) =
      3 * (∑ j, a j ^ 2)^2 - 2 * ∑ j, a j ^ 4 := by
  rw [signAverage, (signSum_moments n a).2]
  exact mul_div_cancel_left₀ _ (pow_ne_zero n (by norm_num))

end Causalean.Stat.EmpiricalProcess.Countable
