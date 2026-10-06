module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Rate

/-!
# Finite scalar priors for the absolute-value cusp

This module packages the finite moment-matching priors needed for the paired
multinomial construction. The priors live on `[-1,1]`; their first several
moments agree, while their mean absolute values have an inverse-degree gap.
-/

@[expose] public section

namespace Causalean.Stat.Minimax.Multinomial.TwoSampleL1

open scoped BigOperators
open Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality
  Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality

/-- Two finite probability distributions on nodes in `[-1,1]` with matching
moments through degree `L` and separated mean absolute values. -/
structure ScalarMomentPriors (L : ℕ) where
  m : ℕ
  m_pos : 0 < m
  node : Fin m → ℝ
  node_mem : ∀ i, node i ∈ Set.Icc (-1 : ℝ) 1
  w₀ : Fin m → ℝ
  w₁ : Fin m → ℝ
  w₀_nonneg : ∀ i, 0 ≤ w₀ i
  w₁_nonneg : ∀ i, 0 ≤ w₁ i
  w₀_sum : ∑ i, w₀ i = 1
  w₁_sum : ∑ i, w₁ i = 1
  moments_eq : ∀ j : ℕ, j ≤ L →
    ∑ i, w₀ i * node i ^ j = ∑ i, w₁ i * node i ^ j
  abs_gap : (1 / 50 : ℝ) / (L : ℝ) ≤
    (∑ i, w₁ i * |node i|) - (∑ i, w₀ i * |node i|)

/-- Given [a positive moment degree](hyp:L,hL), [a pair of finite probability priors on the unit interval that match all moments through that degree but separate absolute moments](goal) exists. -/
theorem exists_scalarMomentPriors (L : ℕ) (hL : 0 < L) :
    Nonempty (ScalarMomentPriors L) := by
  classical
  obtain ⟨D⟩ := exists_finiteMomentDual (f := fun x : ℝ => |x|)
    (r := -1) (s := 1) (by norm_num)
    (continuous_abs.continuousOn) L
  let T : ℝ := ∑ i, D.weights i * |D.nodes i|
  let a : Fin (L + 2) → ℝ := fun i => if 0 ≤ T then D.weights i else -D.weights i
  have ha_abs (i : Fin (L + 2)) : |a i| = |D.weights i| := by
    simp only [a]
    split_ifs <;> simp
  have ha_sum_abs : ∑ i, |a i| = 1 := by
    simpa only [ha_abs] using D.weights_normalized
  have ha_mom (j : ℕ) (hj : j ≤ L) :
      ∑ i, a i * D.nodes i ^ j = 0 := by
    by_cases hT : 0 ≤ T
    · simpa only [a, if_pos hT] using D.moments_zero j hj
    · simp only [a, if_neg hT, neg_mul, Finset.sum_neg_distrib,
        D.moments_zero j hj, neg_zero]
  have ha_target : ∑ i, a i * |D.nodes i| =
      bestUniformApproxErrorAbs L := by
    have hD : |T| = bestUniformApproxErrorAbs L := by
      simpa only [T, bestUniformApproxErrorAbs, uniformApproxErrorAbs,
        bestUniformApproxError, uniformApproxError, intervalSupNorm,
        symmUnitInterval] using D.target_abs_eq
    by_cases hT : 0 ≤ T
    · simp only [a, if_pos hT]
      change T = bestUniformApproxErrorAbs L
      simpa only [abs_of_nonneg hT] using hD
    · have hneg : T ≤ 0 := le_of_lt (lt_of_not_ge hT)
      simp only [a, if_neg hT, neg_mul, Finset.sum_neg_distrib]
      change -T = bestUniformApproxErrorAbs L
      simpa only [abs_of_nonpos hneg] using hD
  have ha_sum : ∑ i, a i = 0 := by
    simpa only [pow_zero, mul_one] using ha_mom 0 (Nat.zero_le L)
  have hparts_abs :
      (∑ i, (a i)⁺) + (∑ i, (a i)⁻) = 1 := by
    rw [← Finset.sum_add_distrib]
    simpa only [posPart_add_negPart] using ha_sum_abs
  have hparts_diff :
      (∑ i, (a i)⁺) - (∑ i, (a i)⁻) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [posPart_sub_negPart] using ha_sum
  have hpos : ∑ i, 2 * (a i)⁺ = 1 := by
    rw [← Finset.mul_sum]
    linarith
  have hneg : ∑ i, 2 * (a i)⁻ = 1 := by
    rw [← Finset.mul_sum]
    linarith
  have hmoment (j : ℕ) (hj : j ≤ L) :
      ∑ i, (2 * (a i)⁻) * D.nodes i ^ j =
        ∑ i, (2 * (a i)⁺) * D.nodes i ^ j := by
    have h : ∑ i, ((2 * (a i)⁺) * D.nodes i ^ j -
        (2 * (a i)⁻) * D.nodes i ^ j) = 0 := by
      calc
        _ = 2 * ∑ i, a i * D.nodes i ^ j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            _ = 2 * ((a i)⁺ - (a i)⁻) * D.nodes i ^ j := by ring
            _ = 2 * (a i * D.nodes i ^ j) := by rw [posPart_sub_negPart]; ring
        _ = 0 := by rw [ha_mom j hj, mul_zero]
    rw [Finset.sum_sub_distrib] at h
    linarith
  have hgap : (1 / 50 : ℝ) / (L : ℝ) ≤
      ∑ i, (2 * (a i)⁺) * |D.nodes i| -
        ∑ i, (2 * (a i)⁻) * |D.nodes i| := by
    have htarget :
        ∑ i, (2 * (a i)⁺) * |D.nodes i| -
          ∑ i, (2 * (a i)⁻) * |D.nodes i| =
            2 * bestUniformApproxErrorAbs L := by
      calc
        _ = 2 * ∑ i, a i * |D.nodes i| := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i _
          calc
            _ = 2 * ((a i)⁺ - (a i)⁻) * |D.nodes i| := by ring
            _ = 2 * (a i * |D.nodes i|) := by rw [posPart_sub_negPart]; ring
        _ = 2 * bestUniformApproxErrorAbs L := by rw [ha_target]
    rw [htarget]
    calc
      (1 / 50 : ℝ) / (L : ℝ) = 2 * ((1 / 100 : ℝ) / (L : ℝ)) := by ring
      _ ≤ 2 * bestUniformApproxErrorAbs L := by
        gcongr
        exact bestUniformApproxErrorAbs_lower L hL
  exact ⟨{
    m := L + 2
    m_pos := by omega
    node := D.nodes
    node_mem := D.nodes_mem
    w₀ := fun i => 2 * (a i)⁻
    w₁ := fun i => 2 * (a i)⁺
    w₀_nonneg := fun i => mul_nonneg (by norm_num) (negPart_nonneg _)
    w₁_nonneg := fun i => mul_nonneg (by norm_num) (posPart_nonneg _)
    w₀_sum := hneg
    w₁_sum := hpos
    moments_eq := hmoment
    abs_gap := hgap }⟩

end Causalean.Stat.Minimax.Multinomial.TwoSampleL1
