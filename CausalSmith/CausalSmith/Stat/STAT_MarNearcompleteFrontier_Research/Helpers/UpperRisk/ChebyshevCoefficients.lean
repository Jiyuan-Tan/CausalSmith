module
public import CausalSmith.Stat.STAT_MarNearcompleteFrontier_Research.Helpers.UpperRisk.ChebyshevRiskBounds
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm

/-!
# Coefficient growth of the light-cell Chebyshev correction

This module isolates the shifted Chebyshev recurrence and coefficient bound
behind equation (6) of the upper-risk proof.
-/

@[expose] public section

namespace CausalSmith.Stat.MarNearcompleteFrontier

open Causalean.Mathlib.Analysis.Approximation.Chebyshev

open Polynomial
open scoped BigOperators


private lemma sum_abs_coeff_le_polynomialCoeffOneNorm (p : ℝ[X]) (s : Finset ℕ) :
    (∑ i ∈ s, |p.coeff i|) ≤ polynomialCoeffOneNorm p := by
  classical
  change (∑ i ∈ s, |p.coeff i|) ≤ ∑ i ∈ p.support, |p.coeff i|
  have heq : (∑ i ∈ s ∩ p.support, |p.coeff i|) =
      ∑ i ∈ s, |p.coeff i| := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro i his hi
    have hnmem : i ∉ p.support := by
      intro hiSupport
      exact hi (Finset.mem_inter.mpr ⟨his, hiSupport⟩)
    simp only [Polynomial.mem_support_iff, ne_eq, not_not] at hnmem
    simp [hnmem]
  rw [← heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
    (fun i _ _ => abs_nonneg (p.coeff i))

private lemma polynomialCoeffOneNorm_C (c : ℝ) :
    polynomialCoeffOneNorm (Polynomial.C c) = |c| := by
  by_cases hc : c = 0
  · subst c
    simp [polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [polynomialCoeffOneNorm_range _ (m := 1) (by
      rw [Polynomial.natDegree_C]
      omega)]
    simp

private lemma polynomialCoeffOneNorm_divX_le (p : ℝ[X]) :
    polynomialCoeffOneNorm p.divX ≤ polynomialCoeffOneNorm p := by
  by_cases hp : p = 0
  · simp [hp, polynomialCoeffOneNorm,
      Causalean.Mathlib.Analysis.JacksonApproximation.polyCoeffL1]
  · rw [polynomialCoeffOneNorm_range p.divX
      (lt_of_le_of_lt Polynomial.natDegree_divX_le (Nat.lt_succ_self _)),
    polynomialCoeffOneNorm_range p (Nat.lt_succ_self _)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ']
    simp only [Polynomial.coeff_divX]
    have htop : p.coeff (p.natDegree + 1) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _)
    simp only [htop, abs_zero, add_zero]
    exact le_add_of_nonneg_right (abs_nonneg (p.coeff 0))

private lemma qPoly_comp_scale (n : ℕ) :
    (qPoly n).comp (Polynomial.C (polyThreshold n) * Polynomial.X) =
      ((1 - shiftedCheb (polyDegree n)).divX) *
        Polynomial.C (1 / (2 * (polyDegree n : ℝ) ^ 2)) := by
  have hB : polyThreshold n ≠ 0 := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    have he' : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hl : 0 < ell n := Real.log_pos (by simpa [ell] using he')
    unfold polyThreshold
    positivity
  let k := polyDegree n
  let B := polyThreshold n
  let p : ℝ[X] := 1 - (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (1 - Polynomial.C (2 / B) * Polynomial.X)
  have hB' : B ≠ 0 := by simpa [B] using hB
  have hscale :
      Polynomial.C (2 / B) * (Polynomial.C B * Polynomial.X) =
        Polynomial.C (2 : ℝ) * Polynomial.X := by
    ext j
    simp [Polynomial.coeff_C_mul]
    field_simp [hB']
  have hpcomp : p.comp (Polynomial.C B * Polynomial.X) =
      1 - shiftedCheb k := by
    unfold p shiftedCheb
    rw [Polynomial.sub_comp, Polynomial.one_comp]
    apply congrArg (fun q : ℝ[X] => 1 - q)
    rw [Polynomial.comp_assoc]
    apply congrArg (fun q : ℝ[X] =>
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp q)
    simp only [Polynomial.sub_comp, Polynomial.one_comp,
      Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
    rw [hscale]
  have hdivscale :
      Polynomial.C B * (p.divX.comp (Polynomial.C B * Polynomial.X)) =
        (p.comp (Polynomial.C B * Polynomial.X)).divX := by
    ext i
    simp only [Polynomial.coeff_C_mul, Polynomial.coeff_divX,
      Polynomial.comp_C_mul_X_coeff]
    rw [pow_succ]
    ring
  change (p.divX * Polynomial.C (B / (2 * (k : ℝ) ^ 2))).comp
      (Polynomial.C B * Polynomial.X) =
        ((1 - shiftedCheb k).divX) *
          Polynomial.C (1 / (2 * (k : ℝ) ^ 2))
  rw [Polynomial.mul_comp, Polynomial.C_comp]
  ext i
  have hi := congrArg (fun q : ℝ[X] => q.coeff i) hdivscale
  rw [hpcomp] at hi
  simp only [Polynomial.coeff_C_mul] at hi
  simp only [Polynomial.coeff_mul_C]
  rw [← hi]
  ring

-- @node: correctionCoeff_weighted_sum_le
/-- The coefficient budget of the light-cell correction is bounded by the
paper's exponential degree factor. Given [the specified input `n`](hyp:n), [the stated mathematical conclusion holds](goal). -/
lemma correctionCoeff_weighted_sum_le (n : ℕ) :
    (∑ v ∈ Finset.range (polyDegree n - 1),
      |correctionCoeff n (v + 1)| *
        (polyThreshold n) ^ (v + 1)) ≤
      (8 : ℝ) ^ (polyDegree n) := by
  let k := polyDegree n
  let B := polyThreshold n
  have hkNat : 1 ≤ k := by unfold k polyDegree; omega
  have hk : 0 < (k : ℝ) := by exact_mod_cast hkNat
  have hB : 0 < B := by
    have he : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
    have he' : 1 < Real.exp (1 : ℝ) + (n : ℝ) := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hl : 0 < ell n := Real.log_pos (by simpa [ell] using he')
    unfold B polyThreshold
    positivity
  let qB := (qPoly n).comp (Polynomial.C B * Polynomial.X)
  have hterm (v : ℕ) :
      |correctionCoeff n (v + 1)| * B ^ (v + 1) =
        |qB.coeff (v + 1)| := by
    simp only [correctionCoeff, Polynomial.coeff_sub, Polynomial.coeff_one,
      if_neg (by omega : v + 1 ≠ 0), zero_sub, abs_neg, qB,
      Polynomial.comp_C_mul_X_coeff, abs_mul, abs_pow, abs_of_pos hB]
  calc
    (∑ v ∈ Finset.range (k - 1),
        |correctionCoeff n (v + 1)| * B ^ (v + 1)) =
        ∑ v ∈ Finset.range (k - 1), |qB.coeff (v + 1)| := by
          apply Finset.sum_congr rfl
          intro v _
          exact hterm v
    _ ≤ polynomialCoeffOneNorm qB := by
      rw [show (∑ v ∈ Finset.range (k - 1), |qB.coeff (v + 1)|) =
          ∑ j ∈ (Finset.range (k - 1)).image (fun v => v + 1),
            |qB.coeff j| by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact Nat.add_right_cancel hab]
      exact sum_abs_coeff_le_polynomialCoeffOneNorm _ _
    _ = polynomialCoeffOneNorm
        (((1 - shiftedCheb k).divX) *
          Polynomial.C (1 / (2 * (k : ℝ) ^ 2))) := by
      rw [show qB = (qPoly n).comp
          (Polynomial.C (polyThreshold n) * Polynomial.X) by rfl,
        qPoly_comp_scale]
    _ ≤ polynomialCoeffOneNorm ((1 - shiftedCheb k).divX) *
          polynomialCoeffOneNorm (Polynomial.C (1 / (2 * (k : ℝ) ^ 2))) :=
      polynomialCoeffOneNorm_mul_le _ _
    _ ≤ (polynomialCoeffOneNorm (1 - shiftedCheb k)) *
          |1 / (2 * (k : ℝ) ^ 2)| := by
      rw [polynomialCoeffOneNorm_C]
      gcongr
      exact polynomialCoeffOneNorm_divX_le _
    _ ≤ (1 + (7 : ℝ) ^ k) * (1 / (2 * (k : ℝ) ^ 2)) := by
      have hc : polynomialCoeffOneNorm (1 - shiftedCheb k) ≤ 1 + 7 ^ k := by
        calc
          polynomialCoeffOneNorm (1 - shiftedCheb k) ≤
              polynomialCoeffOneNorm 1 + polynomialCoeffOneNorm (shiftedCheb k) :=
            polynomialCoeffOneNorm_sub_le _ _
          _ ≤ 1 + 7 ^ k := by
            rw [show (1 : ℝ[X]) = Polynomial.C 1 by simp, polynomialCoeffOneNorm_C]
            norm_num
            exact shiftedCheb_coeffL1_le k
      rw [abs_of_pos (by positivity : 0 < 1 / (2 * (k : ℝ) ^ 2))]
      gcongr
    _ ≤ (7 : ℝ) ^ k := by
      have hpow : 1 ≤ (7 : ℝ) ^ k := one_le_pow₀ (by norm_num)
      have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hkNat
      have hk2 : 1 ≤ (k : ℝ) ^ 2 := by nlinarith
      have hfrac : 1 / (2 * (k : ℝ) ^ 2) ≤ (1 : ℝ) / 2 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      calc
        (1 + (7 : ℝ) ^ k) * (1 / (2 * (k : ℝ) ^ 2)) ≤
            (1 + 7 ^ k) * (1 / 2) := by
          gcongr
        _ ≤ 7 ^ k := by nlinarith
    _ ≤ (8 : ℝ) ^ k := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) k

end CausalSmith.Stat.MarNearcompleteFrontier
