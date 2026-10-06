module
public import Causalean.Stat.EmpiricalProcess.Countable.Basic
public import Mathlib.Tactic.Positivity

/-!
# Algebra of finite sign averages

The exact finite uniform average is nonnegative, order preserving, and
linear. These bridges require no probability-space encoding of signs.
-/

public section

open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- If [a real function of sign vectors is nonnegative at every sign
vector](hyp:H,hH), then [its uniform sign average is nonnegative](goal). -/
theorem signAverage_nonneg {n : ℕ} (H : (Fin n → Bool) → ℝ)
    (hH : ∀ σ, 0 ≤ H σ) : 0 ≤ signAverage H := by
  exact div_nonneg (Finset.sum_nonneg (fun σ _ => hH σ)) (by positivity)

/-- If [a real function H of sign vectors is at most another such function
K at every sign vector](hyp:H,K,h), then [the sign average of H is at most
the sign average of K](goal). -/
theorem signAverage_mono {n : ℕ} (H K : (Fin n → Bool) → ℝ)
    (h : ∀ σ, H σ ≤ K σ) : signAverage H ≤ signAverage K := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun σ _ => h σ))
    (by positivity)

/-- [The sign average of a function of sign vectors](hyp:H) [multiplied
by a real constant](hyp:c) [equals the constant times its sign
average](goal). -/
theorem signAverage_mul_const {n : ℕ} (H : (Fin n → Bool) → ℝ) (c : ℝ) :
    signAverage (fun σ => H σ * c) = signAverage H * c := by
  simp only [signAverage, ← Finset.sum_mul, div_mul_eq_mul_div]

/-- [The sign average of a finite sum](hyp:s) [of functions of sign
vectors](hyp:H) [equals the sum of their sign averages](goal). -/
theorem signAverage_sum {n : ℕ} {κ : Type*} (s : Finset κ)
    (H : κ → (Fin n → Bool) → ℝ) :
    signAverage (fun σ => ∑ k ∈ s, H k σ) = ∑ k ∈ s, signAverage (H k) := by
  simp only [signAverage, Finset.sum_div]
  exact Finset.sum_comm

end Causalean.Stat.EmpiricalProcess.Countable
