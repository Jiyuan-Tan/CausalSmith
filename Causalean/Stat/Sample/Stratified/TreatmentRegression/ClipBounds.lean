module
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.Basic
public import Mathlib.Tactic.Linarith

/-! # Squared-error bounds for interval clipping

Clipping a real estimate to a symmetric interval contracts its squared error
at every target in that interval and bounds the error by four times the
squared interval radius. These deterministic facts require no sampling law.
-/

public section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open Set

/-- If [the clipping radius R is nonnegative](hyp:R,hR) and [the target θ lies in the interval
from −R to R](hyp:theta,htheta), then for [every real estimate t](hyp:t) [the squared error of
the clipped estimate about θ is at most the squared error of t about θ](goal).

Clipping to a symmetric interval never increases squared error relative
to a target contained in that interval. -/
lemma clip_sq_error_le (R t theta : ℝ) (hR : 0 ≤ R) (htheta : theta ∈ Icc (-R) R) :
    (clip R t - theta) ^ 2 ≤ (t - theta) ^ 2 := by
  rcases htheta with ⟨hlo, hhi⟩
  unfold clip
  by_cases hlow : t < -R
  · rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    nlinarith [sq_nonneg (t + R)]
  · by_cases hhigh : R < t
    · rw [min_eq_left hhigh.le, max_eq_right (by linarith)]
      nlinarith [sq_nonneg (t - R)]
    · rw [min_eq_right (le_of_not_gt hhigh), max_eq_right (le_of_not_gt hlow)]

/-- If [the clipping radius R is nonnegative](hyp:R,hR) and [the target θ lies in the interval
from −R to R](hyp:theta,htheta), then for [every real estimate t](hyp:t) [the squared error of the
clipped estimate about θ is at most 4R²](goal), irrespective of the un-clipped estimate. -/
lemma clip_sq_error_le_four (R t theta : ℝ) (hR : 0 ≤ R)
    (htheta : theta ∈ Icc (-R) R) : (clip R t - theta) ^ 2 ≤ 4 * R ^ 2 := by
  rcases htheta with ⟨hlo, hhi⟩
  have hcliplo : -R ≤ clip R t := le_max_left _ _
  have hcliphi : clip R t ≤ R := max_le (by linarith) (min_le_left _ _)
  have hdifflo : -(2 * R) ≤ clip R t - theta := by linarith
  have hdiffhi : clip R t - theta ≤ 2 * R := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hdiffhi) (sub_nonneg.mpr hdifflo)]

end Causalean.Stat.Sample.Stratified.TreatmentRegression
