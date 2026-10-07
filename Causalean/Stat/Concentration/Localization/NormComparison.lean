/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Localization.PeelingProbability
public import Causalean.Stat.Concentration.Localization.SquaredProcess

/-!
# Uniform comparison of empirical and population L² norms

Let F be a countable class of measurable functions bounded by b, let R_n(r) be the
Rademacher complexity of its star hull localized to L²(P)-norm at most r, and let
δ_n be the critical radius of r ↦ 512·b·R_n(r), the infimum of δ > 0 with
512·b·R_n(δ) ≤ δ². For every δ ≥ δ_n, with probability at least
1 − 4·exp(−n·δ²/(65536·b²)) over n independent draws from P, every f in the star
hull of F satisfies

    | ‖f‖_n² − ‖f‖²_{L²(P)} |  ≤  ‖f‖²_{L²(P)} / 2  +  δ² / 2,

where ‖f‖_n is the empirical L² norm. The event is the explicit measurable set
`populationNormComparisonEvent`; the constants are c₁ = 4 and c₂ = 1/65536. A
star-shaped class equals its star hull, so the statement covers star-shaped
classes directly. The proof bounds the ball of radius 2δ and the dyadic shells
2^k·δ < ‖f‖ ≤ 2^(k+1)·δ by `population_ball_bad_probability` and sums the failure
probabilities by `probability_dyadic_union_le`.

On the event, a function with ‖f‖_{L²(P)} ≤ r, r ≥ δ, has ‖f‖_n ≤ √2·r: localization
in the population norm transfers to localization in the empirical norm.

## Main definitions

* `populationNormComparisonEvent` — the comparison event.

## Main results

* `populationNormComparisonEvent_measurable` — the event is measurable.
* `populationNormComparisonEvent_compl_le` — its complement has probability at most
  4·exp(−n·δ²/(65536·b²)) for δ at least the critical radius.
* `populationNormComparison_two_sided` — on the event, ‖f‖_n² ≤ (3/2)·‖f‖² + δ²/2 and
  ‖f‖² ≤ 2·‖f‖_n² + δ².
* `population_localization_transfer` — the transfer to empirical radius √2·r.

References: Bartlett, Bousquet and Mendelson (2005), "Local Rademacher complexities",
Corollary 2.2 and Theorem 3.3; Wainwright (2019), *High-Dimensional Statistics*,
Theorem 14.1. The constants here are larger than in the references.
-/

@[expose] public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳]

/-- [The norm-comparison event](goal) for [a function class F](hyp:F) under [a law P](hyp:P),
at [sample size n](hyp:n) and [slack δ](hyp:δ), is the set of samples x₁,…,x_n on which every
f in the star hull of F satisfies |‖f‖_n² − ‖f‖²_{L²(P)}| ≤ ‖f‖²_{L²(P)}/2 + δ²/2, where
‖f‖_n is the empirical L² norm on the sample. -/
def populationNormComparisonEvent (P : Measure 𝒳) (F : ι → 𝒳 → ℝ)
    (n : ℕ) (δ : ℝ) : Set (Fin n → 𝒳) :=
  {S | ∀ f ∈ starHull F,
    |empiricalNorm S f ^ 2 -
      measureL2Dist P f (fun _ => 0) ^ 2| ≤
      measureL2Dist P f (fun _ => 0) ^ 2 / 2 + δ ^ 2 / 2}

/-- For [a law P](hyp:P), [a function class F](hyp:F), [a sample size n](hyp:n) and [a slack
δ](hyp:δ), [the norm-comparison event equals the intersection over the members f_i of F of the
events |‖f_i‖_n² − ‖f_i‖²_{L²(P)}| ≤ ‖f_i‖²_{L²(P)}/2 + δ²/2](goal).

Scaling a function by a number between 0 and 1 preserves the inequality, so it is enough to
impose it on the base class. -/
lemma populationNormComparisonEvent_eq_iInter
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) (n : ℕ) (δ : ℝ) :
    populationNormComparisonEvent P F n δ =
      ⋂ i, {S | |empiricalNorm S (F i) ^ 2 -
        measureL2Dist P (F i) (fun _ => 0) ^ 2| ≤
        measureL2Dist P (F i) (fun _ => 0) ^ 2 / 2 + δ ^ 2 / 2} := by
  ext S
  constructor
  · intro hS
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact fun i => hS (F i) (mem_starHull_self F i)
  · intro hS
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hS
    rintro f ⟨i, a, ha, ha1, rfl⟩
    change |empiricalNorm S (fun x => a * F i x) ^ 2 -
      measureL2Dist P (fun x => a * F i x) (fun _ => 0) ^ 2| ≤
      measureL2Dist P (fun x => a * F i x) (fun _ => 0) ^ 2 / 2 + δ ^ 2 / 2
    rw [empiricalNorm_const_mul, measureL2Dist_zero_const_mul,
      abs_of_nonneg ha]
    change |(a * empiricalNorm S (F i)) ^ 2 -
      (a * measureL2Dist P (F i) (fun _ => 0)) ^ 2| ≤
      (a * measureL2Dist P (F i) (fun _ => 0)) ^ 2 / 2 + δ ^ 2 / 2
    simp only [mul_pow]
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg a)]
    have ha2 : a ^ 2 ≤ 1 := by nlinarith
    have hscale := mul_le_mul_of_nonneg_left (hS i) (sq_nonneg a)
    have hslack := mul_le_mul_of_nonneg_right ha2 (sq_nonneg δ)
    nlinarith

/-- For [a law P](hyp:P), [a countable class F](hyp:F) of [measurable functions](hyp:hmeas),
[a sample size n](hyp:n) and [a slack δ](hyp:δ), [the norm-comparison event is a measurable
set of samples](goal). -/
lemma populationNormComparisonEvent_measurable [Countable ι]
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) (hmeas : ∀ i, Measurable (F i))
    (n : ℕ) (δ : ℝ) : MeasurableSet (populationNormComparisonEvent P F n δ) := by
  rw [populationNormComparisonEvent_eq_iInter]
  apply MeasurableSet.iInter
  intro i
  have hm : Measurable (fun S : Fin n → 𝒳 =>
      empiricalNorm S (F i)) := by
    unfold empiricalNorm
    fun_prop
  exact measurableSet_le ((hm.pow_const 2).sub measurable_const).abs measurable_const

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound), and
let R_n(r) be the Rademacher complexity of its star hull localized to L²(P)-norm at most r,
for [sample size n ≥ 1](hyp:n,hn). If [δ > 0](hyp:hδ) satisfies [the critical inequality
512·b·R_n(δ) ≤ δ²](hyp:hcritical), then [the probability, over n independent draws from P,
that some f in the star hull of F violates |‖f‖_n² − ‖f‖²_{L²(P)}| ≤ ‖f‖²_{L²(P)}/2 + δ²/2
is at most 4·exp(−n·δ²/(65536·b²))](goal). -/
lemma populationNormComparisonEvent_compl_le_of_critical_inequality
    [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b δ : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (hδ : 0 < δ) (n : ℕ) (hn : 0 < n)
    (hcritical : 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n δ ≤ δ ^ 2) :
    (Measure.pi (fun _ : Fin n => P)).real (populationNormComparisonEvent P F n δ)ᶜ ≤
      4 * Real.exp (-(n : ℝ) * δ ^ 2 / (65536 * b ^ 2)) := by
  classical
  let μ := Measure.pi (fun _ : Fin n => P)
  let D := fun r S => uniformDeviation n
    (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S
  let E := fun r => {S : Fin n → 𝒳 | (2 * r) ^ 2 / 8 < D (2 * r) S}
  let t := (n : ℝ) * δ ^ 2 / (65536 * b ^ 2)
  have hprob : ∀ r, δ ≤ r → μ.real (E r) ≤
      Real.exp (-(n : ℝ) * r ^ 2 / (65536 * b ^ 2)) := by
    intro r hr
    have hball := population_ball_bad_probability P F hmeas hb hbound hδ
      (r := 2 * r) (by linarith) n hn hcritical
    have hexp : -(n : ℝ) * (2 * r) ^ 2 / (262144 * b ^ 2) =
        -(n : ℝ) * r ^ 2 / (65536 * b ^ 2) := by ring
    simpa only [μ, E, D, hexp] using hball
  have hpow : ∀ k : ℕ, δ ≤ (2 : ℝ) ^ k * δ := by
    intro k
    have := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (n := k)
    nlinarith
  have hsubset : (populationNormComparisonEvent P F n δ)ᶜ ⊆
      E δ ∪ ⋃ k : ℕ, E ((2 : ℝ) ^ k * δ) := by
    intro S hS
    change ¬ (∀ f ∈ starHull F, _ ≤ _) at hS
    push Not at hS
    obtain ⟨f, hf, hbad⟩ := hS
    let q := measureL2Dist P f (fun _ => 0)
    have hq : 0 ≤ q := Real.sqrt_nonneg _
    by_cases hsmall : q ≤ δ
    · apply Set.mem_union_left
      have hdev := population_squaredNormDeviation_le P F hb.le hbound
        (by positivity : 0 ≤ 2 * δ) S hf (by dsimp [q] at hsmall; linarith)
      change (2 * δ) ^ 2 / 8 < D (2 * δ) S
      dsimp [D]
      nlinarith [sq_nonneg q]
    · have hlarge : δ < q := lt_of_not_ge hsmall
      obtain ⟨k, hlow, hupp⟩ := exists_nat_pow_near
        (show (1 : ℝ) ≤ q / δ by exact (le_div_iff₀ hδ).2 (by linarith))
        (by norm_num : (1 : ℝ) < 2)
      have hlow' : (2 : ℝ) ^ k * δ ≤ q := (le_div_iff₀ hδ).mp hlow
      have hupp' : q ≤ 2 * ((2 : ℝ) ^ k * δ) := by
        have := (div_lt_iff₀ hδ).mp hupp
        rw [pow_succ] at this
        nlinarith
      apply Set.mem_union_right
      apply Set.mem_iUnion.mpr
      refine ⟨k, ?_⟩
      have hdev := population_squaredNormDeviation_le P F hb.le hbound
        (by positivity : 0 ≤ 2 * ((2 : ℝ) ^ k * δ)) S hf hupp'
      have hsq : ((2 : ℝ) ^ k * δ) ^ 2 ≤ q ^ 2 :=
        (sq_le_sq₀ (by positivity) hq).2 hlow'
      change (2 * ((2 : ℝ) ^ k * δ)) ^ 2 / 8 < D _ S
      dsimp [D]
      dsimp [q] at hsq
      nlinarith [sq_nonneg δ]
  have hbase : μ.real (E δ) ≤ Real.exp (-t) := by
    simpa only [t, neg_div, neg_mul] using hprob δ le_rfl
  have hshell : ∀ k : ℕ, μ.real (E ((2 : ℝ) ^ k * δ)) ≤
      Real.exp (-((4 : ℝ) ^ k * t)) := by
    intro k
    have hexp : -(n : ℝ) * ((2 : ℝ) ^ k * δ) ^ 2 / (65536 * b ^ 2) =
        -((4 : ℝ) ^ k * t) := by
      dsimp [t]
      rw [mul_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul]
      norm_num
      ring
    simpa only [hexp] using hprob _ (hpow k)
  have htotal := probability_dyadic_union_le μ (E δ)
    (fun k => E ((2 : ℝ) ^ k * δ)) hbase hshell
  exact (measureReal_mono hsubset).trans
    (by simpa only [t, neg_div, neg_mul] using htotal)

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound), let
R_n(r) be the Rademacher complexity of its star hull localized to L²(P)-norm at most r for
[sample size n ≥ 1](hyp:n,hn), and let δ_n be the critical radius of r ↦ 512·b·R_n(r). For
[every δ ≥ δ_n](hyp:hradius), [with probability at least 1 − 4·exp(−n·δ²/(65536·b²)) over n
independent draws from P, every f in the star hull of F satisfies
|‖f‖_n² − ‖f‖²_{L²(P)}| ≤ ‖f‖²_{L²(P)}/2 + δ²/2](goal), where ‖f‖_n is the empirical L² norm.

This is the uniform norm comparison of Wainwright (2019), Theorem 14.1, with constants
c₁ = 4 and c₂ = 1/65536 and the critical inequality normalized as 512·b·R_n(δ) ≤ δ². -/
theorem populationNormComparisonEvent_compl_le [Nonempty ι] [Countable ι]
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b δ : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (n : ℕ) (hn : 0 < n)
    (hradius : criticalRadius (fun r => 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n r) ≤ δ) :
    (Measure.pi (fun _ : Fin n => P)).real (populationNormComparisonEvent P F n δ)ᶜ ≤
      4 * Real.exp (-(n : ℝ) * δ ^ 2 / (65536 * b ^ 2)) := by
  classical
  have hδ : 0 ≤ δ := (criticalRadius_nonneg _).trans hradius
  by_cases hδzero : δ = 0
  · subst δ
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_div, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  have hδpos : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδzero)
  let R := fun r => localRademacherComplexity F
    (fun f => measureL2Dist P f (fun _ => 0)) P id n r
  let ψ := fun r => 512 * b * R r
  have hR := population_localizedRademacher_isStarShapedEnvelope
    P F hmeas hb.le hbound n
  have hψ : IsStarShapedEnvelope ψ := by
    refine ⟨fun r hr => mul_nonneg (by positivity) (hR.1 r hr), ?_, ?_⟩
    · intro r₁ r₂ hr₁ hr
      exact mul_le_mul_of_nonneg_left (hR.2.1 r₁ r₂ hr₁ hr) (by positivity)
    · intro r₁ r₂ hr₁ hr
      simpa only [ψ, R, mul_div_assoc] using
        mul_le_mul_of_nonneg_left (hR.2.2 r₁ r₂ hr₁ hr)
          (show 0 ≤ 512 * b by positivity)
  have hbounded : ∀ r, R r ≤ b := by
    intro r
    have hint := (population_localizedRademacher_integrable
      P F hmeas (r := r) hb.le hbound n).2
    have hle := integral_mono hint (integrable_const b)
      (fun S => (empiricalRademacherComplexity_mem_Icc
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r)
        hb.le (fun p x => abs_starHullZeroOut_le_of_bound hbound p x) n S).2)
    simpa only [R, localRademacherComplexity, rademacherComplexity,
      Function.id_comp, integral_const, probReal_univ, smul_eq_mul, one_mul] using hle
  have hnonempty : ({r : ℝ | 0 < r ∧ ψ r ≤ r ^ 2} : Set ℝ).Nonempty := by
    refine ⟨32 * b, by positivity, ?_⟩
    have hle := mul_le_mul_of_nonneg_left (hbounded (32 * b))
      (show 0 ≤ 512 * b by positivity)
    dsimp [ψ]
    nlinarith [sq_nonneg b]
  have hcritical : ψ δ ≤ δ ^ 2 := by
    by_cases hcpos : 0 < criticalRadius ψ
    · have hlinear := starShapedEnvelope_homogeneity hψ hcpos hradius
        (criticalRadius_fp_of_isStarShapedEnvelope hψ hcpos)
      have hsq := mul_le_mul_of_nonneg_left hradius hδ
      nlinarith
    · have hclt : criticalRadius ψ < δ := by
        have hc := le_of_not_gt hcpos
        linarith
      obtain ⟨r, hr, hrδ⟩ := exists_lt_of_csInf_lt hnonempty hclt
      have hlinear := starShapedEnvelope_homogeneity hψ hr.1 hrδ.le hr.2
      have hsq := mul_le_mul_of_nonneg_left hrδ.le hδ
      nlinarith
  exact populationNormComparisonEvent_compl_le_of_critical_inequality
    P F hmeas hb hbound hδpos n hn hcritical

/-- For [a law P](hyp:P) and [a function class F](hyp:F), on [a sample in the norm-comparison
event with slack δ](hyp:hS), [every f in the star hull of F](hyp:hf) satisfies
[‖f‖_n² ≤ (3/2)·‖f‖²_{L²(P)} + δ²/2 and ‖f‖²_{L²(P)} ≤ 2·‖f‖_n² + δ²](goal), where ‖f‖_n is the
empirical L² norm. -/
theorem populationNormComparison_two_sided
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {n : ℕ} {δ : ℝ} {S : Fin n → 𝒳}
    (hS : S ∈ populationNormComparisonEvent P F n δ)
    {f : 𝒳 → ℝ} (hf : f ∈ starHull F) :
    empiricalNorm S f ^ 2 ≤
        (3 / 2 : ℝ) * measureL2Dist P f (fun _ => 0) ^ 2 +
        δ ^ 2 / 2 ∧
      measureL2Dist P f (fun _ => 0) ^ 2 ≤
        2 * empiricalNorm S f ^ 2 + δ ^ 2 := by
  have h := hS f hf
  constructor <;> linarith [le_abs_self
    (empiricalNorm S f ^ 2 -
      measureL2Dist P f (fun _ => 0) ^ 2),
    neg_le_abs (empiricalNorm S f ^ 2 -
      measureL2Dist P f (fun _ => 0) ^ 2)]

/-- For [a law P](hyp:P) and [a function class F](hyp:F), on [a sample in the norm-comparison
event with slack δ](hyp:hS), [every f in the star hull of F](hyp:hf) satisfies
[‖f‖_n² ≤ (3/2)·‖f‖²_{L²(P)} + δ²/2](goal), where ‖f‖_n is the empirical L² norm. -/
theorem populationNormComparison_empirical_sq_le
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {n : ℕ} {δ : ℝ} {S : Fin n → 𝒳}
    (hS : S ∈ populationNormComparisonEvent P F n δ)
    {f : 𝒳 → ℝ} (hf : f ∈ starHull F) :
    empiricalNorm S f ^ 2 ≤
      (3 / 2 : ℝ) * measureL2Dist P f (fun _ => 0) ^ 2 + δ ^ 2 / 2 :=
  (populationNormComparison_two_sided P F hS hf).1

/-- For [a law P](hyp:P) and [a function class F](hyp:F), on [a sample in the norm-comparison
event with slack δ](hyp:hS), [every f in the star hull of F](hyp:hf) satisfies
[‖f‖²_{L²(P)} ≤ 2·‖f‖_n² + δ²](goal), where ‖f‖_n is the empirical L² norm. -/
theorem populationNormComparison_population_sq_le
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {n : ℕ} {δ : ℝ} {S : Fin n → 𝒳}
    (hS : S ∈ populationNormComparisonEvent P F n δ)
    {f : 𝒳 → ℝ} (hf : f ∈ starHull F) :
    measureL2Dist P f (fun _ => 0) ^ 2 ≤
      2 * empiricalNorm S f ^ 2 + δ ^ 2 :=
  (populationNormComparison_two_sided P F hS hf).2

/-- For [a law P](hyp:P) and [a function class F](hyp:F), on [a sample in the norm-comparison
event with slack δ ≥ 0](hyp:hδ,hS), for [every radius r ≥ δ](hyp:hr), [each member of the
star hull of F localized to L²(P)-norm at most r](hyp:p) has [empirical L² norm at most
√2·r](goal). -/
theorem population_localization_transfer
    (P : Measure 𝒳) (F : ι → 𝒳 → ℝ) {n : ℕ} {δ r : ℝ} {S : Fin n → 𝒳}
    (hδ : 0 ≤ δ) (hr : δ ≤ r) (hS : S ∈ populationNormComparisonEvent P F n δ)
    (p : starHullParam ι) :
    empiricalNorm S
      (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r p) ≤
        Real.sqrt 2 * r := by
  classical
  have hr0 : 0 ≤ r := hδ.trans hr
  by_cases hp : measureL2Dist P (starHullEval F p) (fun _ => 0) ≤ r
  · have heq : starHullZeroOut F
        (fun f => measureL2Dist P f (fun _ => 0)) r p = starHullEval F p := by
      funext x
      simp [starHullZeroOut, hp]
    rw [heq]
    have hcomp := populationNormComparison_empirical_sq_le P F hS
      (starHullEval_mem_starHull F p)
    have hnorm0 : 0 ≤ measureL2Dist P (starHullEval F p) (fun _ => 0) :=
      Real.sqrt_nonneg _
    have hnormsq : measureL2Dist P (starHullEval F p) (fun _ => 0) ^ 2 ≤ r ^ 2 := by
      nlinarith
    have hδsq : δ ^ 2 ≤ r ^ 2 := by nlinarith
    have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hupper0 : 0 ≤ Real.sqrt 2 * r := mul_nonneg (Real.sqrt_nonneg _) hr0
    have hupper : (Real.sqrt 2 * r) ^ 2 = 2 * r ^ 2 := by
      rw [mul_pow, hsqrt]
    nlinarith [sq_nonneg
      (empiricalNorm S (starHullEval F p) +
        Real.sqrt 2 * r)]
  · have heq : starHullZeroOut F
        (fun f => measureL2Dist P f (fun _ => 0)) r p = (fun _ => 0) := by
      funext x
      simp [starHullZeroOut, hp]
    rw [heq]
    simpa [empiricalNorm] using
      mul_nonneg (Real.sqrt_nonneg 2) hr0

end Causalean.Stat.Concentration
