module
public import Causalean.Mathlib.Probability.BernoulliMeasure

/-!
# Scalar Bernoulli divergence bounds

This module records a real Bernoulli KL formula and quadratic bounds used by
selected three-Bernoulli laws. The general coefficient depends on an interior
margin; the symmetric small-perturbation bound reuses the quarter-band result.
-/

@[expose] public section

noncomputable section

namespace Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL

/-- The [real Bernoulli KL expression](goal) compares a [success mean](hyp:p)
with a [reference success mean](hyp:q) through its success and failure cells:
`p · log(p/q) + (1 - p) · log((1 - p)/(1 - q))`, with the real logarithm.

It is the Kullback–Leibler divergence of Bernoulli(`p`) from Bernoulli(`q`) when `q` lies
strictly between zero and one and `p` lies in the unit interval. Outside that range the
formula is only an algebraic expression: the real logarithm and real division return zero
at zero, so a reference mean of zero or one gives a finite value where the divergence is
infinite. -/
def bernoulliKL (p q : ℝ) : ℝ :=
  p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))

/-- [Bernoulli KL is at most the squared difference divided by the squared
interior margin](goal) when [the margin is positive](hyp:hη0)
and [both means lie in the margin band](hyp:hp,hq).

The coefficient `η⁻²` is deliberately conservative: `log u ≤ u - 1` gives
`KL(p‖q) ≤ (p-q)²/(q(1-q))`, and both denominator factors are at least `η`.
-/
theorem bernoulliKL_le_inv_margin_sq {η p q : ℝ}
    (hη0 : 0 < η)
    (hp : p ∈ Set.Icc η (1 - η)) (hq : q ∈ Set.Icc η (1 - η)) :
    bernoulliKL p q ≤ (p - q) ^ 2 / η ^ 2 := by
  have hp0 : 0 < p := lt_of_lt_of_le hη0 hp.1
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hq0 : 0 < q := lt_of_lt_of_le hη0 hq.1
  have hq1 : 0 < 1 - q := by linarith [hq.2]
  have hlog₁ := Real.log_le_sub_one_of_pos (div_pos hp0 hq0)
  have hlog₂ := Real.log_le_sub_one_of_pos (div_pos hp1 hq1)
  have hden : η ^ 2 ≤ q * (1 - q) := by
    calc
      η ^ 2 = η * η := by ring
      _ ≤ q * (1 - q) :=
        mul_le_mul hq.1 (by linarith [hq.2]) hη0.le hq0.le
  have hqden : 0 < q * (1 - q) := mul_pos hq0 hq1
  have hηden : 0 < η ^ 2 := sq_pos_of_pos hη0
  unfold bernoulliKL
  calc
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
        p * (p / q - 1) + (1 - p) * ((1 - p) / (1 - q) - 1) :=
      add_le_add (mul_le_mul_of_nonneg_left hlog₁ hp0.le)
        (mul_le_mul_of_nonneg_left hlog₂ hp1.le)
    _ = (p - q) ^ 2 / (q * (1 - q)) := by
      field_simp
      ring
    _ ≤ (p - q) ^ 2 / η ^ 2 := by
      exact div_le_div_of_nonneg_left (sq_nonneg _) hηden hden

/-- [A symmetric Bernoulli perturbation has KL at most four times its squared
mean difference](goal) when [its displacement is at most `1/32`](hyp:ht).

Both means lie in `[1/4,3/4]`; apply the existing Causalean quarter-band
bound after unfolding `bernoulliKL`.
-/
theorem bernoulliKL_symmetric_le_four {t : ℝ} (ht : |t| ≤ 1 / 32) :
    bernoulliKL (1 / 2 + t) (1 / 2 - t) ≤
      4 * ((1 / 2 + t) - (1 / 2 - t)) ^ 2 := by
  have htlo : -(1 / 32 : ℝ) ≤ t := (abs_le.mp ht).1
  have hthi : t ≤ (1 / 32 : ℝ) := (abs_le.mp ht).2
  unfold bernoulliKL
  exact Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
    (by linarith) (by linarith) (by linarith) (by linarith)

end Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
