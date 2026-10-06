module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.SelectedScaleSeries
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Estimators
public import Mathlib.Algebra.BigOperators.Intervals

/-! # Normalizing the selected-scale quadratic tail

At noise threshold `u M h₀^β`, the bandwidth `h₀ / 2^j` contributes
exactly the dyadic Gaussian series in adaptation roadmap (10). The sample
balance remains explicit, so the lemma applies to any analysis bandwidth.
-/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

/-- Refining a dyadic level divides its width by the corresponding power of two. -/
-- @node: dyadicWidth_add
lemma dyadicWidth_add (j₀ j : ℕ) :
    dyadicWidth (j₀ + j) = dyadicWidth j₀ / (2 : ℝ) ^ j := by
  unfold dyadicWidth
  rw [pow_add]
  ring

/-- The exponential part of the quadratic tail becomes the geometric
admissibility envelope after scaling the deviation by the analysis width. -/
-- @node: selectedScale_quadratic_exponent
lemma selectedScale_quadratic_exponent (h z u β : ℝ) (hh : 0 < h) (hz : 0 < z) :
    (u ^ 2 * h ^ (2 * β)) * (h / z) ^ (-(2 * β)) =
      u ^ 2 * z ^ (2 * β) := by
  rw [Real.div_rpow hh.le hz.le, Real.rpow_neg hh.le, Real.rpow_neg hz.le]
  have hp : h ^ (2 * β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh _)
  have hzp : z ^ (2 * β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz _)
  field_simp

/-- The ranked inverse-power term separates into the sample balance, the
tail parameter, and the geometric scale prefactor of roadmap (10). -/
-- @node: selectedScale_quadratic_power
lemma selectedScale_quadratic_power (w h z u β D q : ℝ)
    (hw : 0 < w) (hh : 0 < h) (hz : 0 < z) (hu : 0 < u) :
    (w * (h / z) ^ D * (u ^ 2 * h ^ (2 * β))) ^ (-q) =
      (w * h ^ (D + 2 * β)) ^ (-q) * u ^ (-(2 * q)) * z ^ (D * q) := by
  have hbase : w * (h / z) ^ D * (u ^ 2 * h ^ (2 * β)) =
      (w * h ^ (D + 2 * β)) * u ^ 2 / z ^ D := by
    rw [Real.div_rpow hh.le hz.le, Real.rpow_add hh]
    ring
  rw [hbase, Real.div_rpow (by positivity) (by positivity),
    Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_two,
    ← Real.rpow_mul hu.le, ← Real.rpow_mul hz.le]
  have heq : D * -q = -(D * q) := by ring
  rw [heq, Real.rpow_neg hz.le]
  have heq' : 2 * -q = -(2 * q) := by ring
  rw [heq']
  simp only [div_inv_eq_mul]

/-- The complete finite quadratic-tail sum has a Gaussian bound at the
analysis bandwidth, uniformly over the number of finer selected scales. -/
-- @node: selectedScale_quadratic_sum_gaussianTail
lemma selectedScale_quadratic_sum_gaussianTail (β D q c : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (hc : 0 < c) :
    ∃ G : ℝ, 0 < G ∧ ∀ (s : Finset ℕ) (w h M K u : ℝ),
      0 < w → 0 < h → 0 < M → 0 ≤ K → 1 ≤ u →
      (∑ j ∈ s, K * Real.exp (-c * (u * M * h ^ β) ^ 2 / M ^ 2 *
        (h / (2 : ℝ) ^ j) ^ (-(2 * β))) *
        (w * (h / (2 : ℝ) ^ j) ^ D *
          ((u * M * h ^ β) ^ 2 / M ^ 2)) ^ (-q)) ≤
      K * (w * h ^ (D + 2 * β)) ^ (-q) * G * Real.exp (-c * u ^ 2 / 2) := by
  obtain ⟨G, hG, htail⟩ := dyadicSelectedScaleSeries_gaussianTail (D * q) β q c hβ hq hc
  refine ⟨G, hG, ?_⟩
  intro s w h M K u hw hh hM hK hu
  have hu0 : 0 < u := by linarith
  have hnoise : (u * M * h ^ β) ^ 2 / M ^ 2 = u ^ 2 * h ^ (2 * β) := by
    rw [mul_comm 2 β, Real.rpow_mul hh.le, Real.rpow_two]
    field_simp
  have hterm (j : ℕ) :
      K * Real.exp (-c * (u * M * h ^ β) ^ 2 / M ^ 2 *
        (h / (2 : ℝ) ^ j) ^ (-(2 * β))) *
        (w * (h / (2 : ℝ) ^ j) ^ D * ((u * M * h ^ β) ^ 2 / M ^ 2)) ^ (-q) =
      (K * (w * h ^ (D + 2 * β)) ^ (-q)) *
        (u ^ (-(2 * q)) * (2 : ℝ) ^ ((j : ℝ) * (D * q)) *
          Real.exp (-c * u ^ 2 * (2 : ℝ) ^ (2 * β * j))) := by
    have hz : 0 < (2 : ℝ) ^ j := by positivity
    have hexp := selectedScale_quadratic_exponent h ((2 : ℝ) ^ j) u β hh hz
    have hp := selectedScale_quadratic_power w h ((2 : ℝ) ^ j) u β D q hw hh hz hu0
    have hexp' : -c * (u * M * h ^ β) ^ 2 / M ^ 2 *
        (h / (2 : ℝ) ^ j) ^ (-(2 * β)) =
        -c * u ^ 2 * ((2 : ℝ) ^ j) ^ (2 * β) := by
      have := congrArg (fun x : ℝ => -c * x) hexp
      rw [← hnoise] at this
      convert this using 1 <;> ring
    rw [hexp', hnoise, hp]
    have hpow (r : ℝ) : ((2 : ℝ) ^ j) ^ r = (2 : ℝ) ^ (r * j) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    rw [hpow, hpow, mul_comm (D * q) (j : ℝ)]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have h := mul_le_mul_of_nonneg_left (htail s u hu)
    (show 0 ≤ K * (w * h ^ (D + 2 * β)) ^ (-q) by positivity)
  simpa only [mul_assoc] using h

/-- Reindex the actual selector interval by the number of dyadic refinements
from the analysis level, retaining the same sample-balance factor. -/
-- @node: selectedScale_quadratic_interval_gaussianTail
lemma selectedScale_quadratic_interval_gaussianTail (β D q c : ℝ)
    (hβ : 0 < β) (hq : 0 < q) (hc : 0 < c) :
    ∃ G : ℝ, 0 < G ∧ ∀ (j₀ J : ℕ) (w M K u : ℝ),
      0 < w → 0 < M → 0 ≤ K → 1 ≤ u →
      (∑ j ∈ Finset.Icc j₀ J,
        K * Real.exp (-c * (u * M * (dyadicWidth j₀) ^ β) ^ 2 / M ^ 2 *
          (dyadicWidth j) ^ (-(2 * β))) *
          (w * (dyadicWidth j) ^ D *
            ((u * M * (dyadicWidth j₀) ^ β) ^ 2 / M ^ 2)) ^ (-q)) ≤
        K * (w * (dyadicWidth j₀) ^ (D + 2 * β)) ^ (-q) * G *
          Real.exp (-c * u ^ 2 / 2) := by
  obtain ⟨G, hG, htail⟩ := selectedScale_quadratic_sum_gaussianTail β D q c hβ hq hc
  refine ⟨G, hG, ?_⟩
  intro j₀ J w M K u hw hM hK hu
  have hinterval : Finset.Icc j₀ J = Finset.Ico j₀ (J + 1) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hinterval, Finset.sum_Ico_eq_sum_range]
  simp_rw [dyadicWidth_add]
  exact htail (Finset.range (J + 1 - j₀)) w (dyadicWidth j₀) M K u hw
    (by unfold dyadicWidth; positivity) hM hK hu

end CausalSmith.Stat.GlobalTailDesignRobustCate
