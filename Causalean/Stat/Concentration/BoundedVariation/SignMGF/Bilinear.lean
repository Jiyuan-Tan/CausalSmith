module
public import Causalean.Stat.Concentration.BoundedVariation.SignMGF

/-! # Double Rademacher averages for finite matrices

This module bounds the exponential and nonnegative power moments of bilinear
forms in two independent finite Boolean sign vectors. The matrix may be banded
or fully non-diagonal.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.BoundedVariation.SignMGF

open scoped BigOperators

/-- Given [a finite real matrix](hyp:A) and [two Boolean sign vectors](hyp:σ,τ),
[the bilinear signed matrix sum](goal) is the sum of each entry
weighted by its row and column signs. -/
def bilinearSign {r c : ℕ} (A : Fin r → Fin c → ℝ)
    (σ : Fin r → Bool) (τ : Fin c → Bool) : ℝ :=
  ∑ j, (if τ j then (1 : ℝ) else -1) *
    ∑ i, A i j * (if σ i then (1 : ℝ) else -1)

/-- Given [a finite real matrix](hyp:A) and [a real scale](hyp:t), [the
double-sign exponential average is bounded by a Gaussian exponential whose
variance proxy is the sum of squared column ℓ1 norms](goal). -/
theorem bilinearSignMGF_le {r c : ℕ} (A : Fin r → Fin c → ℝ) (t : ℝ) :
    (∑ σ : Fin r → Bool, ∑ τ : Fin c → Bool,
      Real.exp (t * bilinearSign A σ τ)) /
        ((2 : ℝ) ^ r * (2 : ℝ) ^ c) ≤
      Real.exp (t ^ 2 / 2 * ∑ j : Fin c, (∑ i : Fin r, |A i j|) ^ 2) := by
  classical
  let B (σ : Fin r → Bool) (j : Fin c) : ℝ :=
    ∑ i, A i j * (if σ i then (1 : ℝ) else -1)
  let V : ℝ := ∑ j : Fin c, (∑ i : Fin r, |A i j|) ^ 2
  have hcol (σ : Fin r → Bool) (j : Fin c) :
      |B σ j| ≤ ∑ i : Fin r, |A i j| := by
    calc
      |B σ j| ≤ ∑ i : Fin r, |A i j * (if σ i then (1 : ℝ) else -1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin r, |A i j| := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [abs_mul]
        split_ifs <;> simp
  have hsq (σ : Fin r → Bool) :
      (∑ j : Fin c, (B σ j) ^ 2) ≤ V := by
    apply Finset.sum_le_sum
    intro j hj
    have h := pow_le_pow_left₀ (abs_nonneg (B σ j)) (hcol σ j) 2
    simpa only [sq_abs] using h
  have hσ (σ : Fin r → Bool) :
      (∑ τ : Fin c → Bool, Real.exp (t * bilinearSign A σ τ)) / (2 : ℝ) ^ c ≤
        Real.exp (t ^ 2 / 2 * V) := by
    calc
      _ = (∑ τ : Fin c → Bool,
          Real.exp (t * ∑ j, (if τ j then (1 : ℝ) else -1) * B σ j)) /
            (2 : ℝ) ^ c := rfl
      _ ≤ Real.exp (t ^ 2 / 2 * ∑ j, (B σ j) ^ 2) :=
        signMGF_le (B σ) t
      _ ≤ Real.exp (t ^ 2 / 2 * V) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (hsq σ) (by positivity)
  have hdenr : (0 : ℝ) < 2 ^ r := by positivity
  calc
    _ = (∑ σ : Fin r → Bool,
        (∑ τ : Fin c → Bool, Real.exp (t * bilinearSign A σ τ)) /
          (2 : ℝ) ^ c) / (2 : ℝ) ^ r := by
      rw [← Finset.sum_div]
      ring
    _ ≤ (∑ _σ : Fin r → Bool, Real.exp (t ^ 2 / 2 * V)) / (2 : ℝ) ^ r := by
      apply div_le_div_of_nonneg_right _ hdenr.le
      exact Finset.sum_le_sum (fun σ _ => hσ σ)
    _ = Real.exp (t ^ 2 / 2 * V) := by
      simp [Fintype.card_bool]

/-- Given [a finite real matrix](hyp:A) whose [total absolute coefficient
mass is at most one](hyp:hmass), [the double-sign average of the nonnegative
integer power of one plus its bilinear form is at most the corresponding
Gaussian bound](goal). -/
theorem bilinearSignPowAverage_le {r c n : ℕ} (A : Fin r → Fin c → ℝ)
    (hmass : ∑ j : Fin c, ∑ i : Fin r, |A i j| ≤ 1) :
    (∑ σ : Fin r → Bool, ∑ τ : Fin c → Bool,
      (1 + bilinearSign A σ τ) ^ n) /
        ((2 : ℝ) ^ r * (2 : ℝ) ^ c) ≤
      Real.exp ((n : ℝ) ^ 2 / 2 *
        ∑ j : Fin c, (∑ i : Fin r, |A i j|) ^ 2) := by
  classical
  have hbil (σ : Fin r → Bool) (τ : Fin c → Bool) :
      |bilinearSign A σ τ| ≤ ∑ j : Fin c, ∑ i : Fin r, |A i j| := by
    calc
      |bilinearSign A σ τ| ≤
          ∑ j : Fin c, |(if τ j then (1 : ℝ) else -1) *
            ∑ i, A i j * (if σ i then (1 : ℝ) else -1)| := by
        unfold bilinearSign
        exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin c,
          |∑ i : Fin r, A i j * (if σ i then (1 : ℝ) else -1)| := by
        apply Finset.sum_congr rfl
        intro j hj
        simp only [abs_mul]
        split_ifs <;> simp
      _ ≤ ∑ j : Fin c, ∑ i : Fin r, |A i j| := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          _ ≤ ∑ i : Fin r, |A i j * (if σ i then (1 : ℝ) else -1)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin r, |A i j| := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [abs_mul]
            split_ifs <;> simp
  have hpoint (σ : Fin r → Bool) (τ : Fin c → Bool) :
      (1 + bilinearSign A σ τ) ^ n ≤
        Real.exp ((n : ℝ) * bilinearSign A σ τ) := by
    have hnonneg : 0 ≤ 1 + bilinearSign A σ τ := by
      have habs := (hbil σ τ).trans hmass
      have hneg := neg_abs_le (bilinearSign A σ τ)
      linarith
    calc
      _ ≤ Real.exp (bilinearSign A σ τ) ^ n := by
        apply pow_le_pow_left₀ hnonneg
        simpa only [add_comm] using Real.add_one_le_exp (bilinearSign A σ τ)
      _ = Real.exp ((n : ℝ) * bilinearSign A σ τ) :=
        (Real.exp_nat_mul (bilinearSign A σ τ) n).symm
  calc
    _ ≤ (∑ σ : Fin r → Bool, ∑ τ : Fin c → Bool,
        Real.exp ((n : ℝ) * bilinearSign A σ τ)) /
          ((2 : ℝ) ^ r * (2 : ℝ) ^ c) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply Finset.sum_le_sum
      intro σ hσ
      exact Finset.sum_le_sum (fun τ hτ => hpoint σ τ)
    _ ≤ _ := bilinearSignMGF_le A n

end Causalean.Stat.Concentration.BoundedVariation.SignMGF
