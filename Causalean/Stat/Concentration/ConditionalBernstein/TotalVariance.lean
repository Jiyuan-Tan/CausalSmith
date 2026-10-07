module
public import Causalean.Stat.Concentration.TailBounds.SharpBernstein

/-!
# Bernstein tails with a total second-moment budget

The existing `bernstein_sum_ge` uses a common variance proxy for all coordinates.
Here the budget is the sum of the individual second moments, so inactive histogram
coordinates contribute zero instead of inflating the budget to the full sample size.

Reference: Boucheron, Lugosi, and Bousquet, *Concentration Inequalities*, Theorem 3
(pp. 218–219), https://web.majunjielab.cn/usr/uploads/2024/07/1972749276.pdf.
The fetched authors' notes give the denominator `2 * (totalVariance + t / 3)`.
We use the convenient, slightly larger inverted radius `sqrt (2 * v * u) + u`.
-/

@[expose] public section

namespace Causalean.Stat.Concentration.ConditionalBernstein
open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The [Bernstein radius](goal) for a [total variance budget v](hyp:v) and an
[exponential-tail parameter u](hyp:u) is √(2 v u) + u. -/
noncomputable def bernsteinRadius (v u : ℝ) : ℝ := Real.sqrt (2 * v * u) + u

/-- The Bernstein radius is [nonnegative](goal) at any [nonnegative tail parameter](hyp:hu). -/
theorem bernsteinRadius_nonneg (v : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ bernsteinRadius v u := add_nonneg (Real.sqrt_nonneg _) hu

/-- [Independent measurable centered summands](hyp:hindep,hmeas,hmean),
[integrable with integrable squares](hyp:hint,hsqint) and [bounded above by one](hyp:hupper),
whose [total second moment is at most a positive budget](hyp:hsecond,hv), satisfy
[the upper Bernstein tail](goal) at any [nonnegative threshold](hyp:ht).

Use `centered_bounded_mgf_le` with each coordinate's own second moment and multiply
MGFs with `iIndepFun.mgf_sum`. Bound the sum of the moment budgets by `v`, then optimize
at `t / (v + t / 3)` as in `bernstein_sum_ge`. No positive sample size is required.
Applying the existing common-proxy theorem to all n coordinates would lose the cell count.
-/
theorem bernstein_sum_totalVariance_ge
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {v t : ℝ}
    (hv : 0 < v) (ht : 0 ≤ t)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hsqint : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hupper : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ 1)
    (hsecond : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | t ≤ ∑ i, X i ω} ≤ Real.exp (-t ^ 2 / (2 * (v + t / 3))) := by
  classical
  by_cases htzero : t = 0
  · subst t
    calc
      _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = _ := by simp
  by_cases hn : n = 0
  · subst n
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm htzero)
    have hempty : {ω | t ≤ ∑ i : Fin 0, X i ω} = ∅ := by
      ext ω
      simp [not_le.mpr htpos]
    rw [hempty]
    simp only [measureReal_empty]
    exact (Real.exp_pos _).le
  set d : ℝ := v + t / 3 with hd
  have hdpos : 0 < d := by dsimp [d]; positivity
  set lam : ℝ := t / d with hlam
  have hlam0 : 0 ≤ lam := div_nonneg ht hdpos.le
  have hlam3 : lam * 1 < 3 := by
    rw [mul_one, hlam, div_lt_iff₀ hdpos]
    dsimp [d]
    linarith
  have hexp (i : Fin n) : Integrable (fun ω => Real.exp (lam * X i ω)) μ := by
    refine Integrable.mono' (integrable_const (Real.exp lam))
      ((Real.measurable_exp.comp ((hmeas i).const_mul lam)).aestronglyMeasurable) ?_
    filter_upwards [hupper i] with ω hω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hmgfi (i : Fin n) : mgf (X i) μ lam ≤
      Real.exp (lam ^ 2 * (∫ ω, X i ω ^ 2 ∂μ) / (2 * (1 - lam / 3))) := by
    simpa using Causalean.Stat.Concentration.centered_bounded_mgf_le
      (b := 1) (by norm_num) hlam0 hlam3 (hmeas i).aemeasurable
      (hint i) (hsqint i) (hmean i) (hupper i) le_rfl
  have hden : 0 < 2 * (1 - lam / 3) := by linarith
  have hmgfsum : mgf (fun ω => ∑ i, X i ω) μ lam ≤
      Real.exp (lam ^ 2 * v / (2 * (1 - lam / 3))) := by
    simp only [← Finset.sum_apply]
    rw [hindep.mgf_sum hmeas Finset.univ]
    calc
      ∏ i, mgf (X i) μ lam ≤
          ∏ i, Real.exp (lam ^ 2 * (∫ ω, X i ω ^ 2 ∂μ) / (2 * (1 - lam / 3))) := by
        apply Finset.prod_le_prod
        · intro i _
          exact mgf_nonneg
        · intro i _
          exact hmgfi i
      _ = Real.exp (lam ^ 2 * (∑ i, ∫ ω, X i ω ^ 2 ∂μ) /
          (2 * (1 - lam / 3))) := by
        rw [← Real.exp_sum]
        congr 1
        rw [← Finset.sum_div, ← Finset.mul_sum]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsecond (sq_nonneg lam)) hden.le
  have hsumint : Integrable (fun ω => Real.exp (lam * (∑ i, X i ω))) μ := by
    simp only [← Finset.sum_apply]
    exact hindep.integrable_exp_mul_sum hmeas (s := Finset.univ) (fun i _ => hexp i)
  calc
    μ.real {ω | t ≤ ∑ i, X i ω} ≤
        Real.exp (-lam * t) * mgf (fun ω => ∑ i, X i ω) μ lam :=
      measure_ge_le_exp_mul_mgf t hlam0 hsumint
    _ ≤ Real.exp (-lam * t) * Real.exp (lam ^ 2 * v / (2 * (1 - lam / 3))) :=
      mul_le_mul_of_nonneg_left hmgfsum (Real.exp_pos _).le
    _ = Real.exp (-lam * t + lam ^ 2 * v / (2 * (1 - lam / 3))) := by
      rw [← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [hlam, hd]
      field_simp [ne_of_gt hv]
      nlinarith

/-- [Independent measurable centered summands](hyp:hindep,hmeas,hmean),
[integrable with integrable squares](hyp:hint,hsqint), [bounded in absolute value by one](hyp:habs),
and having [total second moment at most a nonnegative budget v](hyp:hsecond,hv), satisfy,
at a [nonnegative tail parameter u](hyp:hu), [the two-sided Bernstein bound: the
probability that the absolute value of their sum strictly exceeds √(2 v u) + u is at most
2 exp(−u)](goal).

For positive `v` and `u`, apply the upper-tail lemma to `X` and `-X` at the radius,
check `radius^2 ≥ 2*u*(v + radius/3)`, and take the union. At `u = 0` the probability
bound is trivial. At `v = 0`, nonnegativity of the second moments forces each summand
to vanish almost everywhere, so the strict failure event is null. Do not add `v > 0`.
-/
theorem bernstein_sum_totalVariance_abs_gt
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {X : Fin n → Ω → ℝ} {v u : ℝ}
    (hv : 0 ≤ v) (hu : 0 ≤ u)
    (hindep : iIndepFun X μ) (hmeas : ∀ i, Measurable (X i))
    (hint : ∀ i, Integrable (X i) μ)
    (hsqint : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (habs : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ 1)
    (hsecond : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    μ.real {ω | bernsteinRadius v u < |∑ i, X i ω|} ≤ 2 * Real.exp (-u) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hempty : {ω | bernsteinRadius v u < |∑ i : Fin 0, X i ω|} = ∅ := by
      ext ω
      simp [not_lt.mpr (bernsteinRadius_nonneg v hu)]
    rw [hempty]
    simp only [measureReal_empty]
    positivity
  by_cases hu0 : u = 0
  · subst u
    have hprob : μ.real {ω | bernsteinRadius v 0 < |∑ i, X i ω|} ≤ 1 := by
      calc
        _ ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
        _ = 1 := probReal_univ
    simp only [neg_zero, Real.exp_zero, mul_one]
    linarith
  by_cases hv0 : v = 0
  · subst v
    have hnonneg (i : Fin n) : 0 ≤ ∫ ω, X i ω ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg (X i ω))
    have hzero (i : Fin n) : ∫ ω, X i ω ^ 2 ∂μ = 0 := by
      have hle := Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
      exact le_antisymm (hle.trans hsecond) (hnonneg i)
    have hXzero (i : Fin n) : ∀ᵐ ω ∂μ, X i ω = 0 := by
      have hsqzero := (integral_eq_zero_iff_of_nonneg
        (fun ω => sq_nonneg (X i ω)) (hsqint i)).mp (hzero i)
      filter_upwards [hsqzero] with ω hω
      change X i ω ^ 2 = 0 at hω
      nlinarith
    have hall : ∀ᵐ ω ∂μ, ∀ i, X i ω = 0 :=
      (ae_all_iff).mpr hXzero
    have hnull : μ {ω | bernsteinRadius 0 u < |∑ i, X i ω|} = 0 := by
      have hae : ∀ᵐ ω ∂μ, ¬bernsteinRadius 0 u < |∑ i, X i ω| := by
        filter_upwards [hall] with ω hω
        simp [hω, not_lt.mpr (bernsteinRadius_nonneg 0 hu)]
      simpa only [not_not] using ae_iff.mp hae
    rw [(measureReal_eq_zero_iff).mpr hnull]
    positivity
  have hvpos : 0 < v := lt_of_le_of_ne hv (Ne.symm hv0)
  have hrnonneg : 0 ≤ bernsteinRadius v u := bernsteinRadius_nonneg v hu
  have hden : 0 < 2 * (v + bernsteinRadius v u / 3) := by positivity
  have hradius : 2 * u * (v + bernsteinRadius v u / 3) ≤
      bernsteinRadius v u ^ 2 := by
    have hsqrt := Real.sq_sqrt (show 0 ≤ 2 * v * u by positivity)
    have hsu : 0 ≤ Real.sqrt (2 * v * u) * u :=
      mul_nonneg (Real.sqrt_nonneg _) hu
    dsimp [bernsteinRadius]
    nlinarith [sq_nonneg u]
  have hexp : Real.exp (-bernsteinRadius v u ^ 2 /
      (2 * (v + bernsteinRadius v u / 3))) ≤ Real.exp (-u) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hden]
    nlinarith [hradius]
  have hupper (i : Fin n) : ∀ᵐ ω ∂μ, X i ω ≤ 1 :=
    (habs i).mono (fun ω hω => (le_abs_self _).trans hω)
  have hlower (i : Fin n) : ∀ᵐ ω ∂μ, -X i ω ≤ 1 :=
    (habs i).mono (fun ω hω => (neg_le_abs _).trans hω)
  have hpos := (bernstein_sum_totalVariance_ge hvpos hrnonneg hindep hmeas hint
    hsqint hmean hupper hsecond).trans hexp
  have hnegindep : iIndepFun (fun i ω => -X i ω) μ :=
    hindep.comp (fun _ x => -x) (fun _ => measurable_neg)
  have hnegsq (i : Fin n) : Integrable (fun ω => (-X i ω) ^ 2) μ := by
    simpa only [neg_sq] using hsqint i
  have hnegmean (i : Fin n) : ∫ ω, -X i ω ∂μ = 0 := by
    rw [integral_neg, hmean i, neg_zero]
  have hnegsecond : (∑ i, ∫ ω, (-X i ω) ^ 2 ∂μ) ≤ v := by
    simpa only [neg_sq] using hsecond
  have hneg := (bernstein_sum_totalVariance_ge hvpos hrnonneg hnegindep
    (fun i => (hmeas i).neg) (fun i => (hint i).neg) hnegsq hnegmean hlower
    hnegsecond).trans hexp
  calc
    μ.real {ω | bernsteinRadius v u < |∑ i, X i ω|} ≤
        μ.real ({ω | bernsteinRadius v u ≤ ∑ i, X i ω} ∪
          {ω | bernsteinRadius v u ≤ ∑ i, -X i ω}) := by
      refine measureReal_mono ?_ (by finiteness)
      intro ω hω
      change bernsteinRadius v u < |∑ i, X i ω| at hω
      rcases lt_abs.mp hω with hω | hω
      · exact Or.inl hω.le
      · exact Or.inr (by simpa only [Set.mem_ofPred_eq, Finset.sum_neg_distrib] using hω.le)
    _ ≤ μ.real {ω | bernsteinRadius v u ≤ ∑ i, X i ω} +
        μ.real {ω | bernsteinRadius v u ≤ ∑ i, -X i ω} := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (-u) := by linarith

end Causalean.Stat.Concentration.ConditionalBernstein
