/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Bernstein concentration for a bounded design statistic

Chebyshev (`FiniteDesign.chebyshev`) controls a design statistic only polynomially.  For a *bounded*
statistic the tail is exponential, and this file records that sharper Bernstein bound for the
finite-design layer by descending to `D.toMeasure` and invoking the single-random-variable
sub-exponential machinery of `Causalean.Stat.Concentration`.  No independence is needed: a single
bounded, mean-zero statistic on the assignment space is sub-exponential under the design measure, so
its right tail — and, two-sidedly, its absolute deviation — decays like `exp(−ε²/·)`.
-/

module
public import Causalean.Stat.FiniteDesign.MeasureBridge
public import Causalean.Stat.Concentration.TailBounds.SharpBernstein

/-! # Bernstein concentration for a bounded design statistic

For a finite design `D` and a statistic `X` bounded by `c`, with design mean `0` and design
variance at most `v`, `bernstein_ge` gives the one-sided tail bound
`Pr[ε ≤ X] ≤ exp(−ε² / (2(2v + cε)))` and `bernstein_abs_ge` the two-sided bound
`Pr[ε ≤ |X|] ≤ 2·exp(−ε² / (2(2v + cε)))`.  These are exponentially sharper than the Chebyshev
bound `Var/ε²`, and are obtained from the measure-theoretic sub-exponential Chernoff bound through
the design-to-measure bridge. Their constant is a single-statistic sub-exponential proxy; the
independent-summand theorem `bernstein_sum_ge_of_iIndepFun` below has the sharp textbook constant.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Stat.Concentration


namespace Causalean
namespace Experimentation
namespace DesignBased
namespace FiniteDesign

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
variable (D : FiniteDesign Ω)

/-- A bounded, mean-zero statistic on a finite design is sub-exponential under the design measure,
with variance-proxy `2v` and scale `c`.  This is the finite-design instance of the Bernstein
sub-exponential lemma, obtained through the measure bridge. -/
lemma hasSubexponentialMGF_of_bounded (X : Ω → ℝ) {c v : ℝ} (hc : 0 ≤ c)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ v) :
    HasSubexponentialMGF X ⟨2 * v, by
      exact mul_nonneg (by norm_num) (le_trans (D.E_nonneg fun _ => sq_nonneg _) hvar)⟩
      ⟨c, hc⟩ D.toMeasure := by
  have hmean' : D.toMeasure[X] = 0 := (D.integral_toMeasure X).trans hmean
  have hvar' : D.toMeasure[fun ω => X ω ^ 2] ≤ v := by
    rw [D.integral_toMeasure (fun z => X z ^ 2)]
    have : D.E (fun z => X z ^ 2) = D.Var X := by rw [D.Var_eq X, hmean]; ring
    rw [this]; exact hvar
  have hv : 0 ≤ v := le_trans (D.E_nonneg fun _ => sq_nonneg _) hvar
  simpa only [Real.sq_sqrt hv] using
    bounded_hasSubexponentialMGF (σ := Real.sqrt v) hc (D.aemeasurable_toMeasure X) hmean'
      (Filter.Eventually.of_forall hbound) (by simpa only [Real.sq_sqrt hv] using hvar')

/-- **Sub-exponential-proxy tail for one bounded design statistic.** If a statistic is bounded by
`c`, has design mean `0`, and has design variance at most `v`, then it exceeds a nonnegative
threshold `ε` with probability at most `exp(−ε² / (2(2v + cε)))`. This is the older
single-statistic proxy constant; use `bernstein_sum_ge_of_iIndepFun` for independent summands and
the textbook Bernstein constant. -/
theorem bernstein_ge (X : Ω → ℝ) {c v ε : ℝ} (hc : 0 ≤ c)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ v) (hε : 0 ≤ ε) :
    D.Pr (fun z => ε ≤ X z) ≤ Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε))) := by
  have hsub := D.hasSubexponentialMGF_of_bounded X hc hmean hbound hvar
  have h := hsub.measure_ge_le hε
  rw [D.toMeasure_real_setOf (fun z => ε ≤ X z)] at h
  -- `((⟨_, _⟩ : ℝ≥0) : ℝ)` is definitionally the underlying real, so `exact` closes this
  -- at default transparency (`simpa`'s final check no longer unfolds it).
  exact h

/-- **Bernstein tail for a bounded design statistic (two-sided).** For a statistic `X` on a
finite design, suppose [the bound `c` is nonnegative](hyp:hc), [`X` has design mean `0`
](hyp:hmean), [`X` is bounded in absolute value by `c` everywhere](hyp:hbound), [the design
variance of `X` is at most `v`](hyp:hvar), and [the threshold `ε` is nonnegative](hyp:hε). Then
[the design probability that `X` deviates from `0` by at least `ε` in absolute value is at most
`2·exp(−ε²/(2(2v + cε)))`, twice the corresponding one-sided sub-exponential-proxy
bound](goal). -/
theorem bernstein_abs_ge (X : Ω → ℝ) {c v ε : ℝ} (hc : 0 ≤ c)
    (hmean : D.E X = 0) (hbound : ∀ z, |X z| ≤ c) (hvar : D.Var X ≤ v) (hε : 0 ≤ ε) :
    D.Pr (fun z => ε ≤ |X z|) ≤ 2 * Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε))) := by
  have hvarneg : D.Var (fun z => -X z) = D.Var X := by
    have he : (fun z => -X z) = (fun z => (-1 : ℝ) * X z) := by funext z; ring
    rw [he, D.Var_const_mul]; ring
  have hsub := D.hasSubexponentialMGF_of_bounded X hc hmean hbound hvar
  have hpos := D.hasSubexponentialMGF_of_bounded (v := v) (fun z => -X z) hc
    (by rw [D.E_neg, hmean, neg_zero]) (fun z => by simpa [abs_neg] using hbound z)
    (by simpa only [hvarneg] using hvar)
  have hup : D.toMeasure.real {ω | ε ≤ X ω - 0} ≤
      Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε))) := by
    simp only [sub_zero]
    exact hsub.measure_ge_le hε
  have hlow : D.toMeasure.real {ω | ε ≤ -X ω + 0} ≤
      Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε))) := by
    simp only [add_zero]
    exact hpos.measure_ge_le hε
  have h := measureReal_abs_dev_le_two_sided (μ := D.toMeasure) X 0
    (Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε))))
    (Real.exp (-ε ^ 2 / (2 * (2 * v + c * ε)))) ε hup hlow
  rw [D.Pr_eq_measureReal (fun z => ε ≤ |X z|)]
  simpa only [sub_zero, two_mul] using h

/-- **Sharp design-based Bernstein inequality for independent summands.** Given [a design
law](hyp:D), [a positive summand count](hyp:hn), and [summands](hyp:X) that are [independent under
that law](hyp:hindep), [centered in design expectation](hyp:hmean), [bounded above by the nonnegative
envelope `b`](hyp:hb,hupper), and have [second design moments at most the positive proxy
`σ²`](hyp:hsigma2,hsecond), then for [a nonnegative deviation `ε`](hyp:hε), [the design
probability that their sum exceeds `nε` is at most
`exp (−nε²/(2(σ²+bε/3)))`](goal). -/
theorem bernstein_sum_ge_of_iIndepFun {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    {b sigma2 ε : ℝ} (hb : 0 ≤ b) (hsigma2 : 0 < sigma2) (hε : 0 ≤ ε)
    (hindep : ProbabilityTheory.iIndepFun X D.toMeasure)
    (hmean : ∀ i, D.E (X i) = 0) (hupper : ∀ i z, X i z ≤ b)
    (hsecond : ∀ i, D.E (fun z => X i z ^ 2) ≤ sigma2) :
    D.Pr (fun z => (n : ℝ) * ε ≤ ∑ i, X i z) ≤
      Real.exp (-(n : ℝ) * ε ^ 2 / (2 * (sigma2 + b * ε / 3))) := by
  rw [D.Pr_eq_measureReal]
  apply Causalean.Stat.Concentration.bernstein_sum_ge hn hb hsigma2 hε hindep
    (fun i => measurable_of_finite (X i))
    (fun i => (D.memLp_toMeasure (X i) 1).integrable (by simp))
    (fun i => (D.memLp_toMeasure (fun z => X i z ^ 2) 1).integrable (by simp))
  · intro i
    rw [D.integral_toMeasure]
    exact hmean i
  · intro i
    exact Filter.Eventually.of_forall (hupper i)
  · intro i
    rw [D.integral_toMeasure]
    exact hsecond i

end FiniteDesign
end DesignBased
end Experimentation
end Causalean
