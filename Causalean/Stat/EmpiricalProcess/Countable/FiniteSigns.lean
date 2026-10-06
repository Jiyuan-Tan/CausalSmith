module
public import Causalean.Stat.EmpiricalProcess.Countable.Doob
public import Causalean.Stat.EmpiricalProcess.Countable.PrefixProbability
public import Causalean.Stat.EmpiricalProcess.Countable.ScalarSigns
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Finite Rademacher fourth moments and prefix maxima

The scalar fourth moment is exactly 3*(sum a^2)^2 - 2*sum a^4.
Revealing independent Boolean signs gives a martingale, so the Doob bridge
controls the absolute prefix maximum by 256/27 times squared energy.
No maximal estimate is inferred merely from a scalar moment bound.
-/

public section

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Causalean.Stat.EmpiricalProcess.Countable

/-- For [a real coefficient vector a](hyp:a) and independent uniform
signs, [the sign-average fourth power of the maximal absolute prefix of the
signed sum is at most 256/81 times the sign-average fourth power of the
full signed sum](goal). -/
theorem signedPrefixMax_fourth_le_terminal {n : ℕ} (a : Fin n → ℝ) :
    signAverage (fun σ => signedPrefixMax a σ ^ 4) ≤
      (256 / 81 : ℝ) * signAverage
        (fun σ => (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4) := by
  have h4 (k : ℕ) (_hk : k ≤ n) :
      Integrable (fun σ => signedPrefixProcess a k σ ^ 4) (signLaw n) :=
    (signLaw_integral _).1
  have hd := (doob_fourth_maximal (signLaw n) (signRevealFiltration n)
    (signedPrefixProcess a) (signedPrefixProcess_martingale a) n h4).2
  have hmax (σ : Fin n → Bool) :
      (⨆ k : Fin (n + 1), |signedPrefixProcess a k σ|) = signedPrefixMax a σ := rfl
  simp_rw [hmax, signedPrefixProcess_terminal] at hd
  rw [(signLaw_integral (fun σ => signedPrefixMax a σ ^ 4)).2,
    (signLaw_integral (fun σ => (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4)).2] at hd
  exact hd

/-- For [a real coefficient vector a](hyp:a) and independent uniform
signs, [the sign-average fourth power of the maximal absolute prefix of the
signed sum is at most 256/27 times the square of the sum of squared
coefficients](goal), uniformly in the dimension. -/
theorem signedPrefixMax_fourth_le_energy {n : ℕ} (a : Fin n → ℝ) :
    signAverage (fun σ => signedPrefixMax a σ ^ 4) ≤
      (256 / 27 : ℝ) * (∑ j, a j ^ 2)^2 := by
  have hterm : signAverage
      (fun σ => (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4) ≤
        3 * (∑ j, a j ^ 2)^2 := by
    rw [signAverage_fourth_exact]
    have hnonneg : 0 ≤ ∑ j, a j ^ 4 :=
      Finset.sum_nonneg (fun j _ => by positivity)
    linarith
  calc
    _ ≤ (256 / 81 : ℝ) * signAverage
        (fun σ => (∑ j, (if σ j then (1 : ℝ) else -1) * a j)^4) :=
      signedPrefixMax_fourth_le_terminal a
    _ ≤ (256 / 81 : ℝ) * (3 * (∑ j, a j ^ 2)^2) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)
    _ = (256 / 27 : ℝ) * (∑ j, a j ^ 2)^2 := by ring

end Causalean.Stat.EmpiricalProcess.Countable
