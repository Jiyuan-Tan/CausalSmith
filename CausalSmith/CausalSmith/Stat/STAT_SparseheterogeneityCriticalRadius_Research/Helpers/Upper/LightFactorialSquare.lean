module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.FKExpectation

/-! Algebraic cancellation in the light factorial second-moment kernel. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open scoped BigOperators

/-- Dividing the overlapping factorial product by the squared positive count
recovers the product of predecessor falling factorials. -/
lemma factorialOverlap_div_sq (N j q : ℕ) (hN : N ≠ 0) :
    factorialOverlap N j q / (N : ℝ) ^ 2 =
      (falling (N - 1) j : ℝ) * (falling (N - 1) q : ℝ) := by
  rw [factorialOverlap]
  norm_num only [Nat.cast_mul]
  rw [← audit_descFactorial_overlap, ← natCast_mul_falling_pred,
    ← natCast_mul_falling_pred]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  field_simp

lemma double_sum_square {ι : Type} [DecidableEq ι] (s : Finset ι)
    (c x y : ι → ℝ) :
    (∑ j ∈ s, ∑ q ∈ s,
      c j * c q * (x j * x q + y j * y q + 2 * x j * y q)) =
      (∑ j ∈ s, c j * (x j + y j)) ^ 2 := by
  let X : ℝ := ∑ q ∈ s, c q * x q
  let Y : ℝ := ∑ q ∈ s, c q * y q
  have hinner (j : ι) :
      (∑ q ∈ s, c j * c q * (x j * x q + y j * y q + 2 * x j * y q)) =
        c j * x j * X + c j * y j * Y + 2 * c j * x j * Y := by
    calc
      _ = ∑ q ∈ s, ((c j * x j) * (c q * x q) +
          (c j * y j) * (c q * y q) + (2 * c j * x j) * (c q * y q)) := by
        apply Finset.sum_congr rfl; intro q hq; ring
      _ = (∑ q ∈ s, (c j * x j) * (c q * x q)) +
          (∑ q ∈ s, (c j * y j) * (c q * y q)) +
          ∑ q ∈ s, (2 * c j * x j) * (c q * y q) := by
        simp only [Finset.sum_add_distrib]
      _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  simp_rw [hinner]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hx : (∑ j ∈ s, c j * x j) = X := rfl
  have hy : (∑ j ∈ s, c j * y j) = Y := rfl
  have hthird : (∑ j ∈ s, 2 * c j * x j * Y) =
      (∑ j ∈ s, 2 * c j * x j) * Y := by rw [Finset.sum_mul]
  rw [show (∑ j ∈ s, c j * x j * X) = X * X by rw [← Finset.sum_mul, hx],
    show (∑ j ∈ s, c j * y j * Y) = Y * Y by rw [← Finset.sum_mul, hy],
    show (∑ j ∈ s, 2 * c j * x j * Y) = 2 * X * Y by
      rw [hthird]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj; ring
      ]
  have hsum : (∑ j ∈ s, c j * (x j + y j)) = X + Y := by
    calc
      _ = (∑ j ∈ s, c j * x j) + ∑ j ∈ s, c j * y j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j hj; ring
      _ = _ := by rw [hx, hy]
  rw [hsum]
  ring

lemma factorialCorrectionSquare_eq_lightFactorialCoefficient_sq
    (n : ℕ) (rho : ℝ) (N0 N1 : ℕ) :
    factorialCorrectionSquare n rho N0 N1 =
      lightFactorialCoefficient n rho N0 N1 ^ 2 := by
  by_cases hz : N0 = 0 ∨ N1 = 0
  · simp [factorialCorrectionSquare, lightFactorialCoefficient, hz]
  · have h0 : N0 ≠ 0 := (not_or.mp hz).1
    have h1 : N1 ≠ 0 := (not_or.mp hz).2
    rw [factorialCorrectionSquare, lightFactorialCoefficient, if_neg hz, if_neg hz]
    simp_rw [factorialOverlap_div_sq N0 _ _ h0,
      factorialOverlap_div_sq N1 _ _ h1]
    let c : ℕ → ℝ := fun j => gCoeff (degree n rho) j /
      (lightScale n rho ^ (j + 1) * blockMean n ^ (j + 2))
    let x : ℕ → ℝ := fun j => (falling (N0 - 1) j : ℝ)
    let y : ℕ → ℝ := fun j => (falling (N1 - 1) j : ℝ)
    rw [show (∑ j ∈ Finset.range (degree n rho - 1),
        ∑ q ∈ Finset.range (degree n rho - 1),
          gCoeff (degree n rho) j * gCoeff (degree n rho) q /
            (lightScale n rho ^ (j + 1) * blockMean n ^ (j + 2) *
             lightScale n rho ^ (q + 1) * blockMean n ^ (q + 2)) *
            (x j * x q + y j * y q + 2 * x j * y q)) =
        ∑ j ∈ Finset.range (degree n rho - 1),
          ∑ q ∈ Finset.range (degree n rho - 1),
            c j * c q * (x j * x q + y j * y q + 2 * x j * y q) by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [c]
      ring]
    rw [show (∑ j ∈ Finset.range (degree n rho - 1),
        gCoeff (degree n rho) j * (x j + y j) /
          (lightScale n rho ^ (j + 1) * blockMean n ^ (j + 2))) =
        ∑ j ∈ Finset.range (degree n rho - 1), c j * (x j + y j) by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp only [c]
      ring]
    exact double_sum_square (Finset.range (degree n rho - 1)) c x y

lemma factorialCorrectionSquare_nonneg (n : ℕ) (rho : ℝ) (N0 N1 : ℕ) :
    0 ≤ factorialCorrectionSquare n rho N0 N1 := by
  rw [factorialCorrectionSquare_eq_lightFactorialCoefficient_sq]
  positivity

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
