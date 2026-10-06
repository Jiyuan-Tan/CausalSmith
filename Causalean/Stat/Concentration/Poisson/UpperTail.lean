module
public import Causalean.Stat.Concentration.BoundedVariation.Variation
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A Poisson cap at four times the mean

The upper tail of a Poisson count with mean `n/4` beyond the fixed cap `n`
is bounded by a numerical exponential in `n`.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration.BoundedVariation
open scoped ENNReal NNReal

namespace Causalean.Stat.Concentration.Poisson

/-- [A natural cap](hyp:n) gives [an exponential upper bound for a Poisson count with one-quarter of that mean exceeding the cap](goal). -/
-- Use `poisson_upper_tail_mul_exp_le` with r=3, then show
-- `log 4 - 3/4 ≥ 1/2` and rearrange the positive exponential factor.
theorem poisson_quarter_mean_cap_tail (n : ℕ) :
    poissonMeasure ((n : ℝ≥0) / 4) {w : ℕ | n < w} ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) / 2)) := by
  let p := (poissonMeasure ((n : ℝ≥0) / 4)).real {w : ℕ | n < w}
  have hchernoff := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    ((n : ℝ≥0) / 4) n (r := 3) (by norm_num)
  have hlog : (5 / 4 : ℝ) ≤ Real.log 4 := by
    rw [Real.log_four_eq]
    have := Real.log_two_gt_d9
    linarith
  have hp : p ≤ Real.exp (-(n : ℝ) / 2) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hexp : 0 < Real.exp (-(3 : ℝ) * ((n : ℝ) / 4)) := Real.exp_pos _
    have hbound : p ≤ Real.exp ((-Real.log 4 + 3 / 4) * (n : ℝ)) := by
      apply le_of_mul_le_mul_right _ hexp
      calc
        p * Real.exp (-3 * ((n : ℝ) / 4)) ≤
            Real.exp (-Real.log 4 * (n : ℝ)) := by
          simpa [p, show (1 + 3 : ℝ) = 4 by norm_num, neg_mul] using hchernoff
        _ = Real.exp ((-Real.log 4 + 3 / 4) * (n : ℝ)) *
            Real.exp (-3 * ((n : ℝ) / 4)) := by
          rw [← Real.exp_add]
          congr 1
          ring
    calc
      p ≤ Real.exp ((-Real.log 4 + 3 / 4) * (n : ℝ)) := hbound
      _ ≤ Real.exp (-(n : ℝ) / 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_nonneg _)).mpr hp

/-- Under [a probability law](hyp:μ), [a cap](hyp:n), [a count with the stated Poisson law](hyp:M,hM), [a random continuous path and target path](hyp:Z,F), [a unit supremum bound on the target](hyp:hF), and [integrability of the original and capped squared losses](hyp:hZ,hcap), [capping increases squared supremum risk by at most the exponential cap tail](goal). -/
-- Split on `M ω ≤ n` pointwise. On overflow the capped loss is `‖F‖² ≤ 1`.
-- Integrate the pointwise comparison and transfer overflow probability using
-- `hM.measureReal_eq` and `poisson_quarter_mean_cap_tail`.
theorem poisson_cap_path_risk_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (M : Ω → ℕ) (hM : HasLaw M
      (poissonMeasure ((n : ℝ≥0) / 4)) μ)
    (Z : Ω → Path) (F : Path) (hF : ‖F‖ ≤ 1)
    (hZ : Integrable (fun ω => ‖Z ω - F‖ ^ 2) μ)
    (hcap : Integrable (fun ω =>
      ‖(if M ω ≤ n then Z ω else 0) - F‖ ^ 2) μ) :
    (∫ ω, ‖(if M ω ≤ n then Z ω else 0) - F‖ ^ 2 ∂μ) ≤
      (∫ ω, ‖Z ω - F‖ ^ 2 ∂μ) + Real.exp (-(n : ℝ) / 2) := by
  let s : Set Ω := {ω | n < M ω}
  have hs : NullMeasurableSet s μ := by
    exact hM.aemeasurable.nullMeasurableSet_preimage
      (show MeasurableSet {w : ℕ | n < w} by simpa only [Set.Ioi] using measurableSet_Ioi)
  have hind : Integrable (s.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const 1).indicator₀ hs
  have hpoint (ω : Ω) :
      ‖(if M ω ≤ n then Z ω else 0) - F‖ ^ 2 ≤
        ‖Z ω - F‖ ^ 2 + s.indicator (fun _ => (1 : ℝ)) ω := by
    by_cases h : M ω ≤ n
    · simp [h, s]
    · have hF2 : ‖F‖ ^ 2 ≤ (1 : ℝ) := by nlinarith [norm_nonneg F]
      have hz2 : 0 ≤ ‖Z ω - F‖ ^ 2 := sq_nonneg _
      simp only [if_neg h, zero_sub, norm_neg]
      rw [Set.indicator_of_mem (show ω ∈ s by simpa [s] using Nat.lt_of_not_ge h)]
      nlinarith
  have hmain := integral_mono hcap (hZ.add hind) hpoint
  have hint : (∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real s := by
    rw [integral_indicator₀ hs, setIntegral_const]
    simp
  change _ ≤ ∫ ω, ‖Z ω - F‖ ^ 2 + s.indicator (fun _ => (1 : ℝ)) ω ∂μ at hmain
  rw [integral_add hZ hind, hint] at hmain
  have htail := poisson_quarter_mean_cap_tail n
  have htailReal : (poissonMeasure ((n : ℝ≥0) / 4)).real {w : ℕ | n < w} ≤
      Real.exp (-(n : ℝ) / 2) :=
    (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_nonneg _)).mp htail
  have hsprob : μ.real s = (poissonMeasure ((n : ℝ≥0) / 4)).real {w : ℕ | n < w} := by
    simpa [s] using hM.measureReal_eq (p := fun w : ℕ => n < w)
      (show MeasurableSet {w : ℕ | n < w} by simpa only [Set.Ioi] using measurableSet_Ioi)
  rw [hsprob] at hmain
  exact hmain.trans (add_le_add_right htailReal _)

end Causalean.Stat.Concentration.Poisson
