module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.CountLaplace

/-! # Normalization of the selected-level quadratic tilt

The bounded outcome range keeps the binomial half-tilt in a compact interval.
Its linear lower bound yields the power envelope used in adaptation (8).
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- The half-tilt Laplace decrement has a uniform quadratic lower bound
throughout the bounded outcome deviation range. -/
-- @node: quadraticHalfTilt_lower
lemma quadraticHalfTilt_lower (c M : ℝ) (hc : 0 < c) (hM : 0 < M) :
    ∃ k : ℝ, 0 < k ∧ ∀ t : ℝ, 0 < t → t ≤ 2 * M →
      k * t ^ 2 / M ^ 2 ≤ 1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)) := by
  let k : ℝ := (1 - Real.exp (-(2 * c))) / 4
  have hk : 0 < k := by
    have hlt := Real.exp_lt_one_iff.mpr (show -(2 * c) < 0 by linarith)
    dsimp [k]
    positivity
  refine ⟨k, hk, ?_⟩
  intro t ht htM
  have hs : 0 ≤ c * t ^ 2 / M ^ 2 / 2 := by positivity
  have hsS : c * t ^ 2 / M ^ 2 / 2 ≤ 2 * c := by
    have ht2 : t ^ 2 ≤ 4 * M ^ 2 := by nlinarith
    have hdiv : c * t ^ 2 / M ^ 2 ≤ 4 * c := by
      apply (div_le_iff₀ (sq_pos_of_pos hM)).mpr
      nlinarith [mul_le_mul_of_nonneg_left ht2 hc.le]
    linarith
  have h := one_sub_exp_neg_lower_on_interval (2 * c)
    (c * t ^ 2 / M ^ 2 / 2) (by positivity) hs hsS
  have heq : (1 - Real.exp (-(2 * c))) / (2 * c) *
      (c * t ^ 2 / M ^ 2 / 2) = k * t ^ 2 / M ^ 2 := by
    dsimp [k]
    field_simp
    <;> ring
  rwa [heq] at h

/-- Negative powers reverse the half-tilt comparison, producing the
quadratic power envelope for the ranked Gamma bound. -/
-- @node: quadraticHalfTilt_inversePower_le
lemma quadraticHalfTilt_inversePower_le (c M q : ℝ)
    (hc : 0 < c) (hM : 0 < M) (hq : 0 < q) :
    ∃ k : ℝ, 0 < k ∧ ∀ t w : ℝ, 0 < t → t ≤ 2 * M → 0 < w →
      (w * (1 - Real.exp (-(c * t ^ 2 / M ^ 2 / 2)))) ^ (-q) ≤
        (w * (k * t ^ 2 / M ^ 2)) ^ (-q) := by
  obtain ⟨k, hk, hlower⟩ := quadraticHalfTilt_lower c M hc hM
  refine ⟨k, hk, ?_⟩
  intro t w ht htM hw
  exact Real.rpow_le_rpow_of_nonpos (by positivity)
    (mul_le_mul_of_nonneg_left (hlower t ht htM) hw.le) (by linarith)

end CausalSmith.Stat.GlobalTailDesignRobustCate
