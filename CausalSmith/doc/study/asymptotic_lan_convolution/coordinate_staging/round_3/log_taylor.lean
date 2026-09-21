import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Logarithm Taylor bounds for LAN arrays

This module contains the analytic and probabilistic Taylor estimates used after a likelihood
ratio has been reduced to a sum of coordinate log likelihoods.  It is independent of any
particular density model.
-/

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory Topology

/-- On `[-1,1]`, the quadratic Taylor error of `2 log (1+w/2)` is bounded by `|w|³`. -/
theorem abs_two_mul_log_one_add_half_sub_quadratic_le_cube
    (w : ℝ) (hw : |w| ≤ 1) :
    |2 * Real.log (1 + w / 2) - w + (1 / 4 : ℝ) * w ^ 2| ≤ |w| ^ 3 := by
  have hrad : |-w / 2| < (1 : ℝ) := by
    rw [abs_div, abs_neg]
    norm_num
    linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := -w / 2) hrad 2
  norm_num [Finset.sum_range_succ] at h
  rw [abs_div, abs_neg] at h
  norm_num at h
  have h' :
      |(-w / 2) + (-w / 2) ^ 2 / 2 + Real.log (1 + w / 2)|
        ≤ (|w| / 2) ^ 3 / (1 - |w| / 2) := by
    convert h using 1 <;> ring
  have hden : (0 : ℝ) < 1 - |w| / 2 := by linarith [abs_nonneg w]
  have hscaled :
      2 * |(-w / 2) + (-w / 2) ^ 2 / 2 + Real.log (1 + w / 2)|
        ≤ |w| ^ 3 := by
    calc
      2 * |(-w / 2) + (-w / 2) ^ 2 / 2 + Real.log (1 + w / 2)|
          ≤ 2 * ((|w| / 2) ^ 3 / (1 - |w| / 2)) := by nlinarith
      _ ≤ |w| ^ 3 := by
        rw [← mul_div_assoc, div_le_iff₀ hden]
        have ha3 : 0 ≤ |w| ^ 3 := pow_nonneg (abs_nonneg w) _
        nlinarith [mul_nonneg ha3 (sub_nonneg.mpr hw)]
  calc
    |2 * Real.log (1 + w / 2) - w + (1 / 4 : ℝ) * w ^ 2|
        = 2 * |(-w / 2) + (-w / 2) ^ 2 / 2 + Real.log (1 + w / 2)| := by
          rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul]
          congr 1
          ring
    _ ≤ |w| ^ 3 := hscaled

/-- If [each row is a probability law](hyp:hP), [its log likelihood has the stated coordinate representation on the small-increment event](hyp:hidentity), [its quadratic sum converges in probability](hyp:hquadratic), and [its largest coordinate vanishes in probability](hyp:hmax), [the summed quadratic Taylor remainder converges in probability to zero](goal). -/
theorem sum_log_taylor_remainder_tendstoInProbability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : (n : ℕ) → Measure (Ω n)) (L : (n : ℕ) → Ω n → ℝ)
    (W : (n : ℕ) → Ω n → Fin n → ℝ) (q : ℝ)
    (hP : ∀ n, IsProbabilityMeasure (P n))
    (hidentity : ∀ n, ∀ᵐ x ∂P n, (∀ i, |W n x i| ≤ 1) →
      L n x = ∑ i, 2 * Real.log (1 + W n x i / 2))
    (hquadratic : TendstoInProbability P
      (fun n x => (∑ i, W n x i ^ 2)) q)
    (hmax : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P n
      {x | ∃ i, ε ≤ |W n x i|}) atTop (𝓝 0)) :
    TendstoInProbability P
      (fun n x => L n x - (∑ i, W n x i) +
        (1 / 4 : ℝ) * ∑ i, W n x i ^ 2) 0 := by
  intro ε hε
  let K : ℝ := |q| + 1
  have hK : 0 < K := by
    dsimp [K]
    linarith [abs_nonneg q]
  let δ : ℝ := min 1 (ε / (2 * K))
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min one_pos (div_pos hε (by positivity))
  have hδle : δ ≤ 1 := by exact min_le_left _ _
  have hδK : δ * K < ε := by
    have hle : δ ≤ ε / (2 * K) := min_le_right _ _
    have hmul : δ * K ≤ ε / 2 := by
      calc
        δ * K ≤ (ε / (2 * K)) * K :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hK)
        _ = ε / 2 := by field_simp
    linarith
  have hupper : Tendsto (fun n =>
      P n {x | ∃ i, δ ≤ |W n x i|} +
        P n {x | 1 ≤ |(∑ i, W n x i ^ 2) - q|}) atTop (𝓝 0) := by
    convert (hmax δ hδpos).add (hquadratic 1 one_pos) using 1 <;> simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupper
    (Eventually.of_forall fun n => bot_le) (Eventually.of_forall fun n => ?_)
  calc
    P n {x | ε ≤ |(L n x - (∑ i, W n x i) +
        (1 / 4 : ℝ) * ∑ i, W n x i ^ 2) - 0|}
        ≤ P n ({x | ∃ i, δ ≤ |W n x i|} ∪
          {x | 1 ≤ |(∑ i, W n x i ^ 2) - q|}) := by
            apply measure_mono_ae
            filter_upwards [hidentity n] with x hx
            intro hxrem
            change (∃ i, δ ≤ |W n x i|) ∨
              1 ≤ |(∑ i, W n x i ^ 2) - q|
            by_contra hbad
            push Not at hbad
            have hcoord : ∀ i, |W n x i| < δ := hbad.1
            have hsmall : ∀ i, |W n x i| ≤ 1 :=
              fun i => (hcoord i).le.trans hδle
            have hSlt : (∑ i, W n x i ^ 2) < K := by
              have habs : |(∑ i, W n x i ^ 2) - q| < 1 := hbad.2
              have hdifference :
                  (∑ i, W n x i ^ 2) - q < 1 :=
                (le_abs_self _).trans_lt habs
              have hq : q ≤ |q| := le_abs_self q
              dsimp [K]
              linarith
            have hrem :
                |L n x - (∑ i, W n x i) +
                    (1 / 4 : ℝ) * ∑ i, W n x i ^ 2| < ε := by
              rw [hx hsmall]
              calc
                |(∑ i, 2 * Real.log (1 + W n x i / 2)) -
                      (∑ i, W n x i) +
                      (1 / 4 : ℝ) * ∑ i, W n x i ^ 2|
                    = |∑ i, (2 * Real.log (1 + W n x i / 2) -
                        W n x i + (1 / 4 : ℝ) * W n x i ^ 2)| := by
                          congr 1
                          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                            Finset.mul_sum]
                _ ≤ ∑ i, |2 * Real.log (1 + W n x i / 2) -
                      W n x i + (1 / 4 : ℝ) * W n x i ^ 2| :=
                    Finset.abs_sum_le_sum_abs _ _
                _ ≤ ∑ i, δ * W n x i ^ 2 := by
                    apply Finset.sum_le_sum
                    intro i hi
                    refine (abs_two_mul_log_one_add_half_sub_quadratic_le_cube
                      (W n x i) ((hcoord i).le.trans hδle)).trans ?_
                    calc
                      |W n x i| ^ 3 = |W n x i| * W n x i ^ 2 := by
                        rw [← sq_abs]
                        ring
                      _ ≤ δ * W n x i ^ 2 :=
                        mul_le_mul_of_nonneg_right (hcoord i).le (sq_nonneg _)
                _ = δ * (∑ i, W n x i ^ 2) := by rw [Finset.mul_sum]
                _ < δ * K := mul_lt_mul_of_pos_left hSlt hδpos
                _ < ε := hδK
            change ε ≤ |L n x - (∑ i, W n x i) +
              (1 / 4 : ℝ) * ∑ i, W n x i ^ 2 - 0| at hxrem
            simp only [sub_zero] at hxrem
            exact not_lt_of_ge hxrem hrem
    _ ≤ P n {x | ∃ i, δ ≤ |W n x i|} +
          P n {x | 1 ≤ |(∑ i, W n x i ^ 2) - q|} :=
      measure_union_le _ _

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
