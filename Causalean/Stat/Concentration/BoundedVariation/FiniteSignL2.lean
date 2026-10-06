module
public import Causalean.Stat.Concentration.BoundedVariation.FiniteSignMax

/-!
# Finite sign-space second-moment triangle inequality

The ordinary `L₂` triangle inequality on the finite uniform sign space is
stated in the sum-and-square notation used by the process estimates.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- For finitely many real functions on the sign patterns of length n,
[the uniform sign-average of the square of their sum is at most the square
of the sum of their individual root sign-average second moments](goal).
-/
theorem finite_sign_l2_sum_le {n m : ℕ}
    (F : Fin m → (Fin n → Bool) → ℝ) :
    (∑ σ : Fin n → Bool, (∑ k, F k σ) ^ 2) / (2 ^ n : ℝ) ≤
      (∑ k, Real.sqrt ((∑ σ : Fin n → Bool, (F k σ) ^ 2) /
        (2 ^ n : ℝ))) ^ 2 := by
  classical
  have hc : 0 < (2 ^ n : ℝ) := by positivity
  let v : Fin m → EuclideanSpace ℝ (Fin n → Bool) :=
    fun k => WithLp.toLp 2 (fun σ => F k σ / Real.sqrt (2 ^ n : ℝ))
  have hv (k : Fin m) :
      ‖v k‖ = Real.sqrt ((∑ σ : Fin n → Bool, (F k σ) ^ 2) / (2 ^ n : ℝ)) := by
    rw [EuclideanSpace.norm_eq]
    simp only [v, Real.norm_eq_abs, sq_abs]
    congr 1
    calc
      (∑ σ : Fin n → Bool, (F k σ / Real.sqrt (2 ^ n : ℝ)) ^ 2) =
          ∑ σ : Fin n → Bool, (F k σ) ^ 2 / (2 ^ n : ℝ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [div_pow, Real.sq_sqrt hc.le]
      _ = _ := by rw [Finset.sum_div]
  have hsum :
      ‖∑ k, v k‖ ^ 2 =
        (∑ σ : Fin n → Bool, (∑ k, F k σ) ^ 2) / (2 ^ n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [WithLp.ofLp_sum, v, Finset.sum_apply]
    calc
      _ = ∑ σ : Fin n → Bool,
          ((∑ k, F k σ) / Real.sqrt (2 ^ n : ℝ)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [Finset.sum_div]
      _ = ∑ σ : Fin n → Bool, (∑ k, F k σ) ^ 2 / (2 ^ n : ℝ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [div_pow, Real.sq_sqrt hc.le]
      _ = _ := by rw [Finset.sum_div]
  have htriangle := norm_sum_le (Finset.univ : Finset (Fin m)) v
  have hnonneg : 0 ≤ ∑ k, ‖v k‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hsquared : ‖∑ k, v k‖ ^ 2 ≤ (∑ k, ‖v k‖) ^ 2 := by
    nlinarith [norm_nonneg (∑ k, v k)]
  simpa only [hsum, hv] using hsquared

end Causalean.Stat.Concentration.BoundedVariation
