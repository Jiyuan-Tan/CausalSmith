module
public import Causalean.Stat.Concentration.BoundedVariation.FiniteSignL2

/-!
# Countable L₂ triangle inequality on finite sign space

This module passes the finite sign-space triangle inequality to a summable
sequence. It is independent of path variation and dyadic grids.
-/

public section

namespace Causalean.Stat.Concentration.BoundedVariation

/-- If, for [a series of real functions on the sign patterns of length n](hyp:F), [the root sign-average second
moments of its terms are summable](hyp:hR), then [the sign-average square
of the series is at most the square of the sum of those root second
moments](goal).
-/
theorem finite_sign_l2_tsum_le {n : ℕ} (F : ℕ → (Fin n → Bool) → ℝ)
    (hR : Summable (fun k =>
      Real.sqrt ((∑ σ : Fin n → Bool, (F k σ) ^ 2) / (2 ^ n : ℝ)))) :
    (∑ σ : Fin n → Bool, (∑' k, F k σ) ^ 2) / (2 ^ n : ℝ) ≤
      (∑' k, Real.sqrt ((∑ σ : Fin n → Bool, (F k σ) ^ 2) /
        (2 ^ n : ℝ))) ^ 2 := by
  classical
  have hc : 0 < (2 ^ n : ℝ) := by positivity
  let v : ℕ → EuclideanSpace ℝ (Fin n → Bool) :=
    fun k => WithLp.toLp 2 (fun σ => F k σ / Real.sqrt (2 ^ n : ℝ))
  have hv (k : ℕ) :
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
  have hvs : Summable v := by
    apply Summable.of_norm
    simpa only [hv] using hR
  have hcoord (σ : Fin n → Bool) :
      (∑' k, v k) σ = (∑' k, F k σ) / Real.sqrt (2 ^ n : ℝ) := by
    rw [← tsum_div_const]
    have h := hvs.map_tsum (EuclideanSpace.proj σ) (EuclideanSpace.proj σ).continuous
    simpa only [EuclideanSpace.coe_proj, v, PiLp.toLp_apply] using h
  have hsum :
      ‖∑' k, v k‖ ^ 2 =
        (∑ σ : Fin n → Bool, (∑' k, F k σ) ^ 2) / (2 ^ n : ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hcoord]
    calc
      (∑ σ : Fin n → Bool,
          ((∑' k, F k σ) / Real.sqrt (2 ^ n : ℝ)) ^ 2) =
          ∑ σ : Fin n → Bool, (∑' k, F k σ) ^ 2 / (2 ^ n : ℝ) := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [div_pow, Real.sq_sqrt hc.le]
      _ = _ := by rw [Finset.sum_div]
  have htriangle := norm_tsum_le_tsum_norm (by simpa only [hv] using hR : Summable fun k => ‖v k‖)
  have hnonneg : 0 ≤ ∑' k, ‖v k‖ := tsum_nonneg fun _ => norm_nonneg _
  have hsquared : ‖∑' k, v k‖ ^ 2 ≤ (∑' k, ‖v k‖) ^ 2 := by
    nlinarith [norm_nonneg (∑' k, v k)]
  simpa only [hsum, hv] using hsquared

end Causalean.Stat.Concentration.BoundedVariation
