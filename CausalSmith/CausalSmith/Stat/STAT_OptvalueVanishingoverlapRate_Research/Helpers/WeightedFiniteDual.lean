module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.WeightedBestApproximation

/-! # An optimal finite weighted moment annihilator

Alternating active residuals give finite Lagrange weights annihilating every
polynomial through degree K. Normalizing their weighted variation produces
the exact optimal dual gap from roadmap (4)--(5).
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality

/-- There is a finite weighted-normalized moment annihilator attaining the weighted approximation error exactly, rather than only its order lower bound. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hK,hM,hMhi,hε,hεhi), the [stated conclusion](goal) holds. -/
theorem weightedApproxError_finite_dual {K : ℕ} (hK : 2 ≤ K)
    {M ε : ℝ} (hM : 2 ≤ M) (hMhi : M ≤ (K : ℝ) ^ 2)
    (hε : 0 ≤ ε) (hεhi : ε ≤ 1 / 2) :
    ∃ (nodes weights : Fin (K + 2) → ℝ),
      (∀ i, nodes i ∈ Set.Icc 0 M) ∧
      (∀ j : ℕ, j ≤ K → ∑ i, weights i * nodes i ^ j = 0) ∧
      (∑ i, |weights i| * (1 + nodes i)) = 1 ∧
      |∑ i, weights i * phiEpsFormula ε (nodes i)| = weightedApproxError K M ε := by
  classical
  obtain ⟨p, nodes, o, hp, hmono, hmem, ho, he⟩ :=
    weightedApproxError_alternating_witness hK hM hMhi hε hεhi
  let w := normalizedLagrangeWeight nodes
  let D := ∑ i, |w i| * (1 + nodes i)
  have hw : ∑ i, |w i| = 1 := sum_abs_normalizedLagrangeWeight_eq_one hmono.injective
  have hD : 0 < D := by
    have hle : 1 ≤ D := by
      rw [← hw]
      apply Finset.sum_le_sum
      intro i _
      exact le_mul_of_one_le_right (abs_nonneg _) (by linarith [(hmem i).1])
    linarith
  have hpoly : ∑ i, w i * p.eval (nodes i) = 0 :=
    sum_normalizedLagrangeWeight_mul_eval_eq_zero hmono.injective hp
  have hpow (i : Fin (K + 2)) :
      (-1 : ℝ) ^ (K + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ) = (-1 : ℝ) ^ (K + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega)]
  have htarget : ∑ i, w i * phiEpsFormula ε (nodes i) =
      (o * (-1 : ℝ) ^ (K + 1) * weightedApproxError K M ε) * D := by
    calc
      _ = (∑ i, w i * (phiEpsFormula ε (nodes i) - p.eval (nodes i))) +
          ∑ i, w i * p.eval (nodes i) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, w i * (phiEpsFormula ε (nodes i) - p.eval (nodes i)) := by rw [hpoly, add_zero]
      _ = ∑ i, (o * (-1 : ℝ) ^ (K + 1) * weightedApproxError K M ε) *
          (|w i| * (1 + nodes i)) := by
        apply Finset.sum_congr rfl
        intro i _
        have hres := (div_eq_iff (show 1 + nodes i ≠ 0 from by linarith [(hmem i).1])).mp (he i)
        rw [hres]
        have halt : w i = (-1 : ℝ) ^ (K + 1 - (i : ℕ)) * |w i| :=
          normalizedLagrangeWeight_alternates hmono i
        conv_lhs => rw [halt]
        calc
          _ = o * ((-1 : ℝ) ^ (K + 1 - (i : ℕ)) * (-1 : ℝ) ^ (i : ℕ)) *
              weightedApproxError K M ε * (|w i| * (1 + nodes i)) := by ring
          _ = _ := by rw [hpow]
      _ = _ := by rw [← Finset.mul_sum]
  let v := fun i => w i / D
  refine ⟨nodes, v, hmem, ?_, ?_, ?_⟩
  · intro j hj
    simp only [v, div_mul_eq_mul_div, ← Finset.sum_div]
    rw [sum_normalizedLagrangeWeight_mul_pow_eq_zero hmono.injective hj, zero_div]
  · simp only [v, abs_div, abs_of_pos hD, div_mul_eq_mul_div, ← Finset.sum_div]
    exact div_self hD.ne'
  · have hE : 0 ≤ weightedApproxError K M ε := by
      obtain ⟨q, _, hq⟩ := weightedApproxError_attained K (M := M) (by linarith) ε
      rw [← hq]
      exact (weightedPolynomial_error_bound M ε (by linarith) q).1
    simp only [v, div_mul_eq_mul_div, ← Finset.sum_div, htarget]
    rw [mul_div_cancel_right₀ _ hD.ne', abs_mul, abs_mul, abs_pow,
      abs_neg, abs_one, one_pow, mul_one, abs_of_nonneg hE]
    rcases ho with rfl | rfl <;> simp

end CausalSmith.Stat.OptvalueVanishingoverlapRate
