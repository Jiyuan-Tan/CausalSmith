/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.AffineEnvelope
public import Causalean.Stat.Concentration.Covering.VCLocalizedRegime.PopulationMassart
public import Causalean.Stat.Concentration.Localization.NormComparison

/-!
# Population-localized Rademacher envelope for finite-VC classes

Let F be a countable class of measurable functions bounded by b that factors
through Boolean labels of VC dimension at most d (`BinaryFactoredVCClass`), let
R_n(r) be the Rademacher complexity of its star hull localized to L²(P)-norm at
most r, and q = (d·log(n+1) + 1)/n. Nothing is assumed about empirical norms.

* `vcPopulationLocalizedRademacherUpperBound` — R_n(r) ≤ ψ(r) = 2·√q·r + 16·b·q for
  every r ≥ 0, as a `RademacherUpperBound`. This is the self-bounding inequality
  `vcPopulation_localizedRademacher_le`.
* `vcPopulationLocalizedEnvelope` — ψ is a star-shaped envelope, dominates R_n, and its
  critical radius r* satisfies r*² ≤ (32 + 128·b)·q.
* `vcPopulation_criticalRadius_sq_le_rate` — the critical radius δ_n of r ↦ 512·b·R_n(r),
  above which the uniform norm comparison holds, satisfies δ_n² ≤ 4194304·b²·q.
* `vcPopulation_localizedRademacher_above_floor` — a smaller intercept at large radii:
  R_n(r) ≤ 2·√q·r + b/n for r ≥ 2048·b·√q and d ≥ 1.

The refinement integrates over the norm-comparison event at slack 2048·b·√q, whose
complement has probability at most 1/n (`vcPopulation_comparison_floor`): on the
event, population localization at r transfers to empirical radius √2·r and Massart's
lemma gives 2·√q·r; off the event the complexity is at most b.

References: Bartlett, Bousquet and Mendelson (2005), "Local Rademacher complexities",
Corollary 3.7; Wainwright (2019), *High-Dimensional Statistics*, Chapter 14.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d ≥ 1](hyp:d,hd,Hvc). For [sample size
n ≥ 1](hyp:n,hn) and slack δ = 2048·b·√q, with q = (d·log(n+1) + 1)/n, [the event that every f
in the star hull of F satisfies |‖f‖_n² − ‖f‖²_{L²(P)}| ≤ ‖f‖²_{L²(P)}/2 + δ²/2 is measurable,
and its complement has probability at most 1/n over n independent draws from P](goal). -/
lemma vcPopulation_comparison_floor
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) :
    let δ := 2048 * b * Real.sqrt (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n)
    MeasurableSet (populationNormComparisonEvent P F n δ) ∧
      (Measure.pi (fun _ : Fin n => P)).real
        (populationNormComparisonEvent P F n δ)ᶜ ≤ 1 / (n : ℝ) := by
  let q : ℝ := ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n
  let δ : ℝ := 2048 * b * Real.sqrt q
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 < q := by dsimp [q]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsq : δ ^ 2 = 4194304 * b ^ 2 * q := by
    dsimp [δ]
    rw [mul_pow, mul_pow, Real.sq_sqrt hq.le]
    ring
  have hself := vcPopulation_localizedRademacher_le
    P F hmeas hb.le hbound hδ.le d n hn Hvc
  have hcritical : 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n δ ≤ δ ^ 2 := by
    calc
      _ ≤ 512 * b * (2 * Real.sqrt q * δ + 16 * b * q) :=
        mul_le_mul_of_nonneg_left hself (by positivity)
      _ = 2105344 * b ^ 2 * q := by
        dsimp [δ]
        calc
          _ = b ^ 2 * (2097152 * Real.sqrt q ^ 2 + 8192 * q) := by ring
          _ = _ := by rw [Real.sq_sqrt hq.le]; ring
      _ ≤ δ ^ 2 := by rw [hδsq]; nlinarith [mul_nonneg (sq_nonneg b) hq.le]
  have hprob := populationNormComparisonEvent_compl_le_of_critical_inequality
    P F hmeas hb hbound hδ n hn hcritical
  have hexponent : -(n : ℝ) * δ ^ 2 / (65536 * b ^ 2) =
      -64 * ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) := by
    rw [hδsq]
    dsimp [q]
    field_simp
    ring
  have hlarge : -64 * ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) ≤
      -Real.log ((n : ℝ) + 1) - 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hdR hlog]
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
  refine ⟨populationNormComparisonEvent_measurable P F hmeas n δ, ?_⟩
  calc
    _ ≤ 4 * Real.exp (-(n : ℝ) * δ ^ 2 / (65536 * b ^ 2)) := hprob
    _ ≤ 4 * Real.exp (-Real.log ((n : ℝ) + 1) - 4) := by
      rw [hexponent]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hlarge) (by norm_num)
    _ ≤ Real.exp 4 * Real.exp (-Real.log ((n : ℝ) + 1) - 4) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_pos _).le
    _ = 1 / ((n : ℝ) + 1) := by
      rw [← Real.exp_add]
      have heq : (4 : ℝ) + (-Real.log ((n : ℝ) + 1) - 4) =
          -Real.log ((n : ℝ) + 1) := by ring
      rw [heq, Real.exp_neg, Real.exp_log (by linarith : 0 < (n : ℝ) + 1)]
      simp only [one_div]
    _ ≤ 1 / (n : ℝ) := one_div_le_one_div_of_le hnR (by linarith)

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d ≥ 1](hyp:d,hd,Hvc), and let
q = (d·log(n+1) + 1)/n for [sample size n ≥ 1](hyp:n,hn). For [every radius
r ≥ 2048·b·√q](hyp:hr), [the Rademacher complexity R_n(r) of the star hull of F localized to
L²(P)-norm at most r satisfies R_n(r) ≤ 2·√q·r + b/n](goal).

The term b/n bounds the contribution of the samples outside the norm-comparison event. At
these radii it improves the intercept 16·b·q of `vcPopulation_localizedRademacher_le`. -/
lemma vcPopulation_localizedRademacher_above_floor
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d)
    (hr : 2048 * b * Real.sqrt
      (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) ≤ r) :
    localRademacherComplexity F (fun f => measureL2Dist P f (fun _ => 0)) P id n r ≤
      2 * Real.sqrt (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) * r + b / n := by
  classical
  let q : ℝ := ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n
  let δ : ℝ := 2048 * b * Real.sqrt q
  let μ := Measure.pi (fun _ : Fin n => P)
  let E := populationNormComparisonEvent P F n δ
  let G := populationLocalizedRepresentative P F r
  let c := 2 * Real.sqrt q * r
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hr0 : 0 ≤ r := hδ.trans hr
  obtain ⟨hE, hprob⟩ := vcPopulation_comparison_floor P F hmeas hb hbound d n hd hn Hvc
  have hEc : MeasurableSet Eᶜ := hE.compl
  have hrad (S : Fin n → 𝒳) (hS : S ∈ E) :
      empiricalL2Radius G S ≤ Real.sqrt 2 * r := by
    apply ciSup_le
    intro i
    let a : Set.Icc (0 : ℝ) 1 :=
      ⟨starHullZeroOutScaleCoeff F (fun f => measureL2Dist P f (fun _ => 0)) r i,
        starHullZeroOutScaleCoeff_nonneg F _ r i,
        starHullZeroOutScaleCoeff_le_one F _ r i⟩
    have ha : measureL2Dist P (starHullEval F (a, i)) (fun _ => 0) ≤ r :=
      populationLocalizedRepresentative_radius P F hr0 i
    have heq : starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r (a, i) = G i := by
      funext x
      simp only [starHullZeroOut, if_pos ha]
      rfl
    simpa only [heq] using population_localization_transfer P F hδ hr hS (a, i)
  have hon (S : Fin n → 𝒳) (hS : S ∈ E) :
      empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S ≤ c := by
    calc
      _ ≤ Real.sqrt (2 * q) * empiricalL2Radius G S :=
        population_massart_empirical_radius P F hb.le hbound d n hn Hvc S
      _ ≤ Real.sqrt (2 * q) * (Real.sqrt 2 * r) :=
        mul_le_mul_of_nonneg_left (hrad S hS) (Real.sqrt_nonneg _)
      _ = c := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        dsimp [c]
        calc
          _ = (Real.sqrt 2 ^ 2) * Real.sqrt q * r := by ring
          _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hi := (population_localizedRademacher_integrable P F hmeas (r := r) hb.le hbound n).2
  have hind : Integrable (Eᶜ.indicator (fun _ => b)) μ :=
    (integrable_const b).indicator hEc
  have hmajor (S : Fin n → 𝒳) :
      empiricalRademacherComplexity n
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r) S ≤
          c + Eᶜ.indicator (fun _ => b) S := by
    by_cases hS : S ∈ E
    · have hSc : S ∉ Eᶜ := by simpa using hS
      simpa only [Set.indicator_of_notMem hSc, add_zero] using hon S hS
    · rw [Set.indicator_of_mem (show S ∈ Eᶜ from hS)]
      have hle := (empiricalRademacherComplexity_mem_Icc
        (starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r)
        hb.le (fun p x => abs_starHullZeroOut_le_of_bound hbound p x) n S).2
      have hc : 0 ≤ c := by dsimp [c]; positivity
      linarith
  have hle := integral_mono hi ((integrable_const c).add hind) hmajor
  change localRademacherComplexity F _ P id n r ≤ c + b / n
  calc
    _ ≤ ∫ S, c + Eᶜ.indicator (fun _ => b) S ∂μ := by
      simpa only [localRademacherComplexity, rademacherComplexity,
        Function.id_comp, μ, Pi.add_apply] using hle
    _ = c + μ.real Eᶜ * b := by
      rw [integral_add (integrable_const c) hind, integral_indicator_const b hEc]
      simp [μ, smul_eq_mul]
    _ ≤ c + b / n := by
      have h := mul_le_mul_of_nonneg_right hprob hb.le
      change μ.real Eᶜ * b ≤ 1 / (n : ℝ) * b at h
      have heq : 1 / (n : ℝ) * b = b / n := by ring
      rw [heq] at h
      exact add_le_add le_rfl h


/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d](hyp:d,Hvc). For [sample size
n ≥ 1](hyp:n,hn), [the Rademacher complexity R_n(r) of the star hull of F localized to
L²(P)-norm at most r satisfies R_n(r) ≤ 2·√q·r + 16·b·q for every r ≥ 0, where
q = (d·log(n+1) + 1)/n](goal).

Localization is in the population norm; no bound on empirical norms is assumed. The envelope
is affine, as in Bartlett, Bousquet and Mendelson (2005), Corollary 3.7, and holds at every
radius by the self-bounding inequality `vcPopulation_localizedRademacher_le`. -/
theorem vcPopulationLocalizedRademacherUpperBound
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) :
    RademacherUpperBound F (fun f => measureL2Dist P f (fun _ => 0)) P id n
      (vcPopulationLocalizedPsi b d n) := by
  intro r hr
  exact vcPopulation_localizedRademacher_le P F hmeas hb hbound hr d n hn Hvc

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d](hyp:d,Hvc), and let
ψ(r) = 2·√q·r + 16·b·q with q = (d·log(n+1) + 1)/n for [sample size n ≥ 1](hyp:n,hn). Then
[ψ is a valid localized envelope with the d·log(n)/n critical-radius rate](goal): (1) [ψ is
star-shaped](step:1), (2) [the Rademacher complexity of the star hull of F localized to
L²(P)-norm at most r is at most ψ(r) for every r ≥ 0](step:2), and (3) [the critical radius r*
of ψ, the infimum of r > 0 with ψ(r) ≤ r², satisfies r*² ≤ (32 + 128·b)·q](step:3). -/
theorem vcPopulationLocalizedEnvelope
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) :
    IsStarShapedEnvelope (vcPopulationLocalizedPsi b d n) ∧
      RademacherUpperBound F (fun f => measureL2Dist P f (fun _ => 0)) P id n
        (vcPopulationLocalizedPsi b d n) ∧
      criticalRadius (vcPopulationLocalizedPsi b d n) ^ 2 ≤
        (32 + 128 * b) * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) := by
  exact ⟨vcPopulationLocalizedPsi_isStarShapedEnvelope hb d n,
    vcPopulationLocalizedRademacherUpperBound P F hmeas hb hbound d n hn Hvc,
    criticalRadius_vcPopulationLocalizedPsi_sq_le_rate hb d n⟩

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound) and
[factor through Boolean labels of VC dimension at most d](hyp:d,Hvc), and let R_n(r) be the
Rademacher complexity of its star hull localized to L²(P)-norm at most r, for [sample size
n ≥ 1](hyp:n,hn). Then [the critical radius δ_n of r ↦ 512·b·R_n(r), the infimum of δ > 0 with
512·b·R_n(δ) ≤ δ², satisfies δ_n² ≤ 4194304·b²·(d·log(n+1) + 1)/n](goal).

Every δ ≥ δ_n is admissible in the uniform norm comparison
`populationNormComparisonEvent_compl_le`. -/
theorem vcPopulation_criticalRadius_sq_le_rate
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (d n : ℕ) (hn : 0 < n)
    (Hvc : BinaryFactoredVCClass F d) :
    criticalRadius (fun r => 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n r) ^ 2 ≤
      4194304 * b ^ 2 * (((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n) := by
  let q : ℝ := ((d : ℝ) * Real.log ((n : ℝ) + 1) + 1) / n
  let δ : ℝ := 2048 * b * Real.sqrt q
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hq : 0 < q := by dsimp [q]; positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδsq : δ ^ 2 = 4194304 * b ^ 2 * q := by
    dsimp [δ]
    rw [mul_pow, mul_pow, Real.sq_sqrt hq.le]
    ring
  have hself := vcPopulation_localizedRademacher_le
    P F hmeas hb.le hbound hδ.le d n hn Hvc
  have hle : criticalRadius (fun r => 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n r) ≤ δ := by
    apply criticalRadius_le hδ
    calc
      _ ≤ 512 * b * (2 * Real.sqrt q * δ + 16 * b * q) :=
        mul_le_mul_of_nonneg_left hself (by positivity)
      _ = 2105344 * b ^ 2 * q := by
        dsimp [δ]
        calc
          _ = b ^ 2 * (2097152 * Real.sqrt q ^ 2 + 8192 * q) := by ring
          _ = _ := by rw [Real.sq_sqrt hq.le]; ring
      _ ≤ δ ^ 2 := by rw [hδsq]; nlinarith [mul_nonneg (sq_nonneg b) hq.le]
  have hc := criticalRadius_nonneg (fun r => 512 * b * localRademacherComplexity F
    (fun f => measureL2Dist P f (fun _ => 0)) P id n r)
  change _ ≤ 4194304 * b ^ 2 * q
  rw [← hδsq]
  nlinarith

end Causalean.Stat.Concentration
