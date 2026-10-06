module
public import CausalSmith.Stat.STAT_MarRareqLogfrontier_Research.Helpers.Certificate.PilotCorrection
public import Mathlib.Order.Interval.Finset.Nat

/-! The finite coefficient expansion and exact Chebyshev mean of the marked
factorial branch, including zero-arrival cells, in roadmap (8). -/

public section

open MeasureTheory ProbabilityTheory Set Finset Polynomial
open scoped NNReal ENNReal

namespace CausalSmith.Stat.MarRareqLogfrontier

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

attribute [local instance] markedObsLaw_isProbabilityMeasure

/-- Given [the specified inputs and assumptions](hyp:n,d,q), [the stated mathematical conclusion holds](goal). -/
-- @node: chebNeedle_eval_zero
lemma chebNeedle_eval_zero (n d : ℕ) (q : ℝ) :
    (chebNeedle n d q).eval 0 = 1 := by
  by_cases hb : needleBranch n d q
  · have hB : 0 < needleRadius n q := by
      unfold needleRadius
      have := hb.1
      positivity
    have hk : 0 < needleDegree n q := by
      unfold needleDegree
      exact Nat.floor_pos.mpr (by linarith [hb.1])
    let p : Polynomial ℝ := 1 - (Chebyshev.T ℝ (needleDegree n q : ℤ)).comp
      (C 1 - C (2 / needleRadius n q) * X)
    have hc : p.coeff 1 = (2 / needleRadius n q) * (needleDegree n q : ℝ)^2 := by
      have hder : p.coeff 1 = (derivative p).eval 0 := by
        rw [← coeff_zero_eq_eval_zero, coeff_derivative]
        norm_num
      rw [hder]
      simp [p, derivative_sub, derivative_comp, Chebyshev.derivative_T_eval_one]
    have hform : (chebNeedle n d q).eval 0 =
        (needleRadius n q / (2 * (needleDegree n q : ℝ)^2)) * p.coeff 1 := by
      simp [chebNeedle, hb, p, ← coeff_zero_eq_eval_zero, coeff_divX]
    rw [hform, hc]
    have hk0 : (needleDegree n q : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  · simp [chebNeedle, hb]

/-- Given [the specified inputs and assumptions](hyp:n,d,q,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: natDegree_one_sub_chebNeedle_le
lemma natDegree_one_sub_chebNeedle_le (n d : ℕ) (q : ℝ)
    (hb : needleBranch n d q) :
    (1 - chebNeedle n d q).natDegree ≤ needleDegree n q - 1 := by
  let a : Polynomial ℝ := C 1 - C (2 / needleRadius n q) * X
  have ha : a.natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le (by simp)
    exact (natDegree_C_mul_le _ _).trans (by simp)
  have hp : (1 - (Chebyshev.T ℝ (needleDegree n q : ℤ)).comp a).natDegree ≤
      needleDegree n q := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · simp
    · apply (natDegree_comp_le).trans
      rw [Chebyshev.natDegree_T]
      simp only [Int.natAbs_natCast]
      exact (Nat.mul_le_mul_left _ ha).trans_eq (Nat.mul_one _)
  have hQ : (chebNeedle n d q).natDegree ≤ needleDegree n q - 1 := by
    rw [chebNeedle, if_pos hb]
    apply (natDegree_C_mul_le _ _).trans
    rw [natDegree_divX_eq_natDegree_tsub_one]
    exact Nat.sub_le_sub_right hp 1
  exact (natDegree_sub_le _ _).trans (max_le (by simp) hQ)

/-- Given [the specified inputs and assumptions](hyp:n,d,q,t,hb), [the stated mathematical conclusion holds](goal). -/
-- @node: sum_needleCoeff_mul_pow
lemma sum_needleCoeff_mul_pow (n d : ℕ) (q t : ℝ)
    (hb : needleBranch n d q) :
    (∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), needleCoeff n d q v * t ^ v) =
      1 - (chebNeedle n d q).eval t := by
  classical
  let p := 1 - chebNeedle n d q
  have hp0 : p.coeff 0 = 0 := by
    simp [p, coeff_zero_eq_eval_zero, chebNeedle_eval_zero]
  have hk : 0 < needleDegree n q := by
    unfold needleDegree
    exact Nat.floor_pos.mpr (by linarith [hb.1])
  have hdeg : p.natDegree < needleDegree n q :=
    lt_of_le_of_lt (natDegree_one_sub_chebNeedle_le n d q hb) (Nat.sub_lt hk (by decide))
  have heval := Polynomial.eval_eq_sum_range' hdeg t
  rw [Nat.range_eq_Icc_zero_sub_one _ hk.ne'] at heval
  have hsum : (∑ v ∈ Finset.Icc 0 (needleDegree n q - 1), p.coeff v * t ^ v) =
      ∑ v ∈ Finset.Icc 1 (needleDegree n q - 1), p.coeff v * t ^ v := by
    symm
    apply Finset.sum_subset
    · intro v hv
      simp only [Finset.mem_Icc] at hv ⊢
      omega
    · intro v hv hn
      have hv0 : v = 0 := by
        simp only [Finset.mem_Icc] at hv hn
        omega
      simp [hv0, hp0]
  rw [hsum] at heval
  simp only [p, eval_sub, eval_one] at heval
  simpa only [needleCoeff, if_pos hb] using heval.symm

/-- Given [the specified inputs and assumptions](hyp:n,d,q,P,j), [the stated mathematical conclusion holds](goal). -/
-- @node: integral_markedPoissonFactorialBranch_eq_needle
lemma integral_markedPoissonFactorialBranch_eq_needle
    (n d : ℕ) (q : ℝ) (P : FullLaw d) (j : Cell d) :
    (∫ s, poissonFactorialBranch n d q j s
      ∂finitePoissonSampleLaw (markedObsLaw P) ((n : ℝ≥0) / 2)) =
      cellMean P j * (1 - (chebNeedle n d q).eval
        (streamSize n * arrivedCell P j)) := by
  classical
  let : IsProbabilityMeasure P.1 := P.2
  by_cases hb : needleBranch n d q
  · rw [integral_markedPoissonFactorialBranch, if_pos hb,
      ← sum_needleCoeff_mul_pow n d q _ hb, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    have hvpos : 1 ≤ v := (Finset.mem_Icc.mp hv).1
    have hpow : v - 1 + 1 = v := by omega
    by_cases hj : 0 < arrivedCell P j
    · rw [cellMean, if_pos hj]
      simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
      rw [show streamSize n * arrivedCell P j =
        ((n : ℝ) / 2) * (arrivedCell P j / 3) by unfold streamSize; ring, mul_pow]
      have ha0 := hj.ne'
      have ha : (arrivedCell P j / 3) ^ v =
          (arrivedCell P j / 3) ^ (v - 1) * (arrivedCell P j / 3) := by
        conv_lhs => rw [← hpow, pow_succ]
      rw [ha]
      field_simp
    · have hz : arrivedCell P j = 0 :=
        le_antisymm (le_of_not_gt hj) measureReal_nonneg
      have hone : P.1.real {r | inCell r j ∧ r.R = true ∧ r.Y = true} = 0 := by
        apply le_antisymm _ measureReal_nonneg
        calc
          _ ≤ arrivedCell P j := measureReal_mono
            (fun r hr ↦ ⟨hr.1, hr.2.1⟩) (measure_ne_top P.1 _)
          _ = 0 := hz
      simp [cellMean, hj, hone]
  · simp [integral_markedPoissonFactorialBranch, chebNeedle, hb]

end CausalSmith.Stat.MarRareqLogfrontier
