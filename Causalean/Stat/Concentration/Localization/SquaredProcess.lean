/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Concentration.Localization.Bousquet
public import Causalean.Stat.Concentration.Localization.CountableReduction

/-!
# Squared localized processes: expectation and concentration

For a class F bounded by b, let G_r be the star hull of F localized to
L²(P)-norm at most r, and let Z_r = sup over g ∈ G_r of |(1/n) Σ_k g(x_k)² − ∫ g² dP|.
With R_n(r) the Rademacher complexity of G_r:

* symmetrization and contraction for the square (2b-Lipschitz on [−b, b]) give
  E Z_r ≤ 8·b·R_n(r);
* the squares have variance at most b²r², so Bousquet's inequality gives the
  variance-sensitive tail of Z_r, with exponent of order n·r²/b² (a bounded-differences
  inequality would only give order n·r⁴/b⁴);
* if 512·b·R_n(δ) ≤ δ² at some δ > 0, then, since R_n(r)/r is nonincreasing,
  P(Z_r > r²/8) ≤ exp(−n·r²/(262144·b²)) for every r ≥ δ, which bounds the failure
  probability on each dyadic shell.

Suprema are taken over the countable representative family of
`CountableReduction`, which attains the suprema over G_r.

## Main results

* `population_squareDeviation_expectation_le`, `population_squareDeviation_tail`
* `population_ball_bad_probability`

Reference: Bartlett, Bousquet and Mendelson (2005), "Local Rademacher complexities",
Corollary 2.2 and Appendix A.2. The reference parametrizes localization by the
squared radius; this file uses the L² radius throughout.
-/

public section

namespace Causalean.Stat.Concentration

open MeasureTheory

variable {𝒳 ι : Type*} [MeasurableSpace 𝒳] [Nonempty ι] [Countable ι]

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b ≥ 0](hyp:hb,hbound), and
let G_r be its star hull localized to L²(P)-norm at most r. For [a positive sample size
n](hyp:n,hn), [the expectation over n independent draws x₁,…,x_n from P of
sup over g ∈ G_r of |(1/n) Σ_k g(x_k)² − ∫ g² dP| is at most 8·b·R_n(r), where R_n(r) is the
Rademacher complexity of G_r](goal).

The supremum is written over the representative family, which attains it. -/
theorem population_squareDeviation_expectation_le
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (n : ℕ) (hn : 0 < n) :
    (∫ S, uniformDeviation n
        (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S
        ∂Measure.pi (fun _ : Fin n => P)) ≤
      8 * b * localRademacherComplexity F
        (fun f => measureL2Dist P f (fun _ => 0)) P id n r := by
  let G := populationLocalizedRepresentative P F r
  let sqG : ι → 𝒳 → ℝ := fun i x => G i x ^ 2
  have hGmeas : ∀ i, Measurable (G i) :=
    populationLocalizedRepresentative_measurable P F hmeas r
  have hGbound : ∀ i x, |G i x| ≤ b :=
    populationLocalizedRepresentative_bound P F hbound
  have hsqMeas : ∀ i, Measurable (sqG i) := fun i => (hGmeas i).pow_const 2
  have hsqBound : ∀ i x, |sqG i x| ≤ b ^ 2 := by
    intro i x
    simpa only [sqG, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (G i x)) (hGbound i x) 2
  have hsymm := uniform_deviation_expectation_le_two_smul_rademacher_complexity
    (μ := P) (f := sqG) hn id hsqMeas (sq_nonneg b) hsqBound
  let φ : ℝ → ℝ := fun x => (Causalean.Mathlib.Analysis.clipIcc (-b) b x) ^ 2
  have hφeq : ∀ i x, φ (G i x) = sqG i x := by
    intro i x
    simp [φ, sqG, Causalean.Mathlib.Analysis.clipIcc_neg_eq_self (hGbound i x)]
  have hcontractPoint : ∀ S,
      empiricalRademacherComplexity n sqG S ≤
        4 * b * empiricalRademacherComplexity n G S := by
    intro S
    have hc := empiricalRademacherComplexity_contraction_abs_of_bddAbove φ
      (clippedSquare_lipschitzAt0 hb) G hb hGbound n S
    have heq := empiricalRademacherComplexity_congr_sample n sqG
      (fun i x => φ (G i x)) S (fun i k => (hφeq i (S k)).symm)
    rw [heq]
    exact hc.trans_eq (by ring)
  have hGint : Integrable (fun S => empiricalRademacherComplexity n G S)
      (Measure.pi (fun _ : Fin n => P)) :=
    Integrable.of_mem_Icc 0 b
      (empiricalRademacherComplexity_measurable_countable G hGmeas n).aemeasurable
      (ae_of_all _ fun S => empiricalRademacherComplexity_mem_Icc G hb hGbound n S)
  have hsqInt : Integrable (fun S => empiricalRademacherComplexity n sqG S)
      (Measure.pi (fun _ : Fin n => P)) :=
    Integrable.of_mem_Icc 0 (b ^ 2)
      (empiricalRademacherComplexity_measurable_countable sqG hsqMeas n).aemeasurable
      (ae_of_all _ fun S =>
        empiricalRademacherComplexity_mem_Icc sqG (sq_nonneg b) hsqBound n S)
  have hcontractPop : rademacherComplexity n sqG P id ≤
      4 * b * rademacherComplexity n G P id := by
    simp only [rademacherComplexity, Function.id_comp]
    rw [← integral_const_mul]
    exact integral_mono hsqInt (hGint.const_mul _) hcontractPoint
  have hradEq : rademacherComplexity n G P id =
      localRademacherComplexity F
        (fun f => measureL2Dist P f (fun _ => 0)) P id n r := by
    unfold localRademacherComplexity rademacherComplexity
    simp only [Function.id_comp]
    apply integral_congr_ae
    exact ae_of_all _ fun S =>
      (population_empiricalRademacher_eq_representative P F hb hbound S).symm
  have hsymm' : (∫ S, uniformDeviation n sqG P id S
      ∂Measure.pi (fun _ : Fin n => P)) ≤ 2 * rademacherComplexity n sqG P id := by
    simpa [two_smul ℝ] using hsymm
  change (∫ S, uniformDeviation n sqG P id S
    ∂Measure.pi (fun _ : Fin n => P)) ≤ _
  calc
    _ ≤ 2 * rademacherComplexity n sqG P id := hsymm'
    _ ≤ 2 * (4 * b * rademacherComplexity n G P id) :=
      mul_le_mul_of_nonneg_left hcontractPop (by norm_num)
    _ = _ := by rw [hradEq]; ring

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound), let
G_r be its star hull localized to L²(P)-norm at most [r > 0](hyp:hr), and let Z be the
supremum over g ∈ G_r of |(1/n) Σ_k g(x_k)² − ∫ g² dP| for [n ≥ 1](hyp:n,hn) independent
draws from P. With M = 8·b·R_n(r), where R_n(r) is the Rademacher complexity of G_r, and
[every x > 0](hyp:hx), [P(Z ≥ M + 2·√((b²r² + 4·b²·M)·x/n) + 8·b²·x/n) ≤ exp(−x)](goal). -/
theorem population_squareDeviation_tail
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b r : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 < r) (n : ℕ) (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) :
    let M := 8 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n r
    (Measure.pi (fun _ : Fin n => P)).real
      {S | M + 2 * Real.sqrt ((b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n) +
          8 * b ^ 2 * x / n ≤ uniformDeviation n
            (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S} ≤
      Real.exp (-x) := by
  let G := populationLocalizedRepresentative P F r
  let sqG : ι → 𝒳 → ℝ := fun i x => G i x ^ 2
  let M := 8 * b * localRademacherComplexity F
    (fun f => measureL2Dist P f (fun _ => 0)) P id n r
  have hGmeas : ∀ i, Measurable (G i) :=
    populationLocalizedRepresentative_measurable P F hmeas r
  have hGbound : ∀ i x, |G i x| ≤ b :=
    populationLocalizedRepresentative_bound P F hbound
  have hsqMeas : ∀ i, Measurable (sqG i) := fun i => (hGmeas i).pow_const 2
  have hsqBound : ∀ i x, |sqG i x| ≤ b ^ 2 := by
    intro i x
    simpa only [sqG, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (G i x)) (hGbound i x) 2
  have hvariance : ∀ i, ProbabilityTheory.variance (sqG i) P ≤ (b * r) ^ 2 := by
    intro i
    have hsecondInt : Integrable (sqG i) P :=
      Integrable.of_mem_Icc 0 (b ^ 2) (hsqMeas i).aemeasurable
        (ae_of_all _ fun x => ⟨sq_nonneg _, (le_abs_self _).trans (hsqBound i x)⟩)
    have hfourthInt : Integrable (fun x => (sqG i x) ^ 2) P :=
      Integrable.of_mem_Icc 0 ((b ^ 2) ^ 2)
        ((hsqMeas i).pow_const 2).aemeasurable
        (ae_of_all _ fun x => ⟨sq_nonneg _, by
          simpa only [sq_abs] using
            pow_le_pow_left₀ (abs_nonneg (sqG i x)) (hsqBound i x) 2⟩)
    have hsecond : (∫ x, sqG i x ∂P) ≤ r ^ 2 := by
      have hrad := populationLocalizedRepresentative_radius P F hr.le i
      have hnonneg : 0 ≤ ∫ x, sqG i x ∂P := integral_nonneg fun x => sq_nonneg _
      have heq : measureL2Dist P (G i) (fun _ => 0) ^ 2 =
          ∫ x, sqG i x ∂P := by
        simpa only [measureL2Dist, sub_zero, sqG] using Real.sq_sqrt hnonneg
      rw [← heq]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hrad 2
    calc
      ProbabilityTheory.variance (sqG i) P ≤ ∫ x, (sqG i x) ^ 2 ∂P :=
        ProbabilityTheory.variance_le_expectation_sq (hsqMeas i).aestronglyMeasurable
      _ ≤ ∫ x, b ^ 2 * sqG i x ∂P := by
        apply integral_mono hfourthInt (hsecondInt.const_mul _)
        intro x
        simpa only [sqG, pow_two] using mul_le_mul_of_nonneg_right
          ((le_abs_self _).trans (hsqBound i x)) (sq_nonneg (G i x))
      _ = b ^ 2 * ∫ x, sqG i x ∂P := integral_const_mul _ _
      _ ≤ b ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hsecond (sq_nonneg b)
      _ = (b * r) ^ 2 := by ring
  have hM : 0 ≤ M := mul_nonneg (by positivity)
    (localRademacherComplexity_nonneg F _ P id n r)
  have htail := uniform_deviation_bousquet_tail_countable P sqG hsqMeas
    (b := b ^ 2) (r := b * r) (M := M) (by positivity) hsqBound
    (mul_pos hb hr) hvariance hM n hn
    (population_squareDeviation_expectation_le P F hmeas hb.le hbound n hn) hx
  simpa only [mul_pow] using htail

/-- Under [a probability law P](hyp:P), let [a nonempty countable class F](hyp:F) of
[measurable functions](hyp:hmeas) be [bounded in absolute value by b > 0](hyp:hb,hbound), let
G_r be its star hull localized to L²(P)-norm at most r, and R_n(r) the Rademacher complexity
of G_r for [sample size n ≥ 1](hyp:n,hn). If [δ > 0](hyp:hδ) satisfies [the critical
inequality 512·b·R_n(δ) ≤ δ²](hyp:hcritical), then for [every r ≥ δ](hyp:hr), [the
probability that sup over g ∈ G_r of |(1/n) Σ_k g(x_k)² − ∫ g² dP| exceeds r²/8 is at most
exp(−n·r²/(262144·b²))](goal). -/
lemma population_ball_bad_probability
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    (hmeas : ∀ i, Measurable (F i)) {b δ r : ℝ} (hb : 0 < b)
    (hbound : ∀ i x, |F i x| ≤ b) (hδ : 0 < δ) (hr : δ ≤ r)
    (n : ℕ) (hn : 0 < n)
    (hcritical : 512 * b * localRademacherComplexity F
      (fun f => measureL2Dist P f (fun _ => 0)) P id n δ ≤ δ ^ 2) :
    (Measure.pi (fun _ : Fin n => P)).real
      {S | r ^ 2 / 8 < uniformDeviation n
        (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S} ≤
      Real.exp (-(n : ℝ) * r ^ 2 / (262144 * b ^ 2)) := by
  let R : ℝ → ℝ := fun s => localRademacherComplexity F
    (fun f => measureL2Dist P f (fun _ => 0)) P id n s
  let M := 8 * b * R r
  let x := (n : ℝ) * r ^ 2 / (262144 * b ^ 2)
  have hr0 : 0 < r := hδ.trans_le hr
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : 0 < x := by dsimp [x]; positivity
  have hψ := population_localizedRademacher_isStarShapedEnvelope
    P F hmeas hb.le hbound n
  have hcross : R r * δ ≤ R δ * r :=
    (div_le_div_iff₀ hr0 hδ).mp (hψ.2.2 δ r hδ hr)
  have hscaled := mul_le_mul_of_nonneg_left hcross (by positivity : 0 ≤ 512 * b)
  have hcrit := mul_le_mul_of_nonneg_right hcritical hr0.le
  have hbig : δ * (512 * b * R r) ≤ δ * (r * δ) := by
    dsimp [R] at hscaled ⊢
    nlinarith [hscaled, hcrit]
  have hmean : M ≤ r * δ / 64 := by
    have h := le_of_mul_le_mul_left hbig hδ
    dsimp [M]
    nlinarith
  have hsmall : M ≤ r ^ 2 / 64 := by
    nlinarith [mul_le_mul_of_nonneg_left hr hr0.le]
  have hxterm : 8 * b ^ 2 * x / n = r ^ 2 / 32768 := by
    dsimp [x]
    field_simp
    ring
  have hins_eq : (b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n =
      r ^ 2 * (r ^ 2 + 4 * M) / 262144 := by
    dsimp [x]
    field_simp
  have hsqrt : Real.sqrt ((b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n) ≤
      r ^ 2 / 128 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    rw [hins_eq]
    nlinarith [mul_le_mul_of_nonneg_left hsmall (sq_nonneg r), sq_nonneg (r ^ 2)]
  have hthreshold : M + 2 * Real.sqrt
      ((b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n) + 8 * b ^ 2 * x / n ≤
      r ^ 2 / 8 := by
    rw [hxterm]
    nlinarith [sq_nonneg r]
  have htail := population_squareDeviation_tail P F hmeas hb hbound hr0 n hn hx
  change (Measure.pi (fun _ : Fin n => P)).real
    {S | M + 2 * Real.sqrt ((b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n) +
        8 * b ^ 2 * x / n ≤ uniformDeviation n
          (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S} ≤
    Real.exp (-x) at htail
  have hsubset : {S : Fin n → 𝒳 | r ^ 2 / 8 < uniformDeviation n
      (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S} ⊆
      {S | M + 2 * Real.sqrt ((b ^ 2 * r ^ 2 + 4 * b ^ 2 * M) * x / n) +
          8 * b ^ 2 * x / n ≤ uniformDeviation n
            (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S} := by
    intro S hS
    exact hthreshold.trans hS.le
  exact (measureReal_mono hsubset).trans (by simpa only [x, neg_div, neg_mul] using htail)

omit [Countable ι] in
/-- Under [a probability law P](hyp:P), let [a nonempty class F](hyp:F) be [bounded in
absolute value by b ≥ 0](hyp:hb,hbound) and let [r ≥ 0](hyp:hr). For [every sample
x₁,…,x_n](hyp:S) and [every f in the star hull of F](hyp:hf) with [‖f‖_{L²(P)} ≤ r](hyp:hfr),
[|‖f‖_n² − ‖f‖²_{L²(P)}| is at most the supremum of |(1/n) Σ_k g(x_k)² − ∫ g² dP| over the
representative family at radius r](goal), where ‖f‖_n is the empirical L² norm. -/
lemma population_squaredNormDeviation_le
    (P : Measure 𝒳) [IsProbabilityMeasure P] (F : ι → 𝒳 → ℝ)
    {b r : ℝ} (hb : 0 ≤ b)
    (hbound : ∀ i x, |F i x| ≤ b) (hr : 0 ≤ r)
    {n : ℕ} (S : Fin n → 𝒳) {f : 𝒳 → ℝ}
    (hf : f ∈ starHull F) (hfr : measureL2Dist P f (fun _ => 0) ≤ r) :
    |empiricalNorm S f ^ 2 -
      measureL2Dist P f (fun _ => 0) ^ 2| ≤
        uniformDeviation n
          (fun i x => (populationLocalizedRepresentative P F r i x) ^ 2) P id S := by
  classical
  obtain ⟨i, a, ha, ha1, rfl⟩ := hf
  let p : starHullParam ι := (⟨a, ha, ha1⟩, i)
  let H := starHullZeroOut F (fun f => measureL2Dist P f (fun _ => 0)) r
  have heq : H p = fun x => a * F i x := by
    funext x
    exact if_pos hfr
  have hHbound : ∀ p x, |H p x| ≤ b :=
    fun p x => abs_starHullZeroOut_le_of_bound hbound p x
  have hsqbound : ∀ p x, |H p x ^ 2| ≤ b ^ 2 := by
    intro p x
    simpa only [abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (H p x)) (hHbound p x) 2
  have hbdd : BddAbove (Set.range fun p : starHullParam ι =>
      |(n : ℝ)⁻¹ * ∑ k : Fin n, H p (S k) ^ 2 - ∫ x, H p x ^ 2 ∂P|) := by
    refine ⟨2 * b ^ 2, ?_⟩
    rintro _ ⟨p, rfl⟩
    have havg : |(n : ℝ)⁻¹ * ∑ k : Fin n, H p (S k) ^ 2| ≤ b ^ 2 := by
      simpa using absInner_le_of_bound (fun _ : Unit => fun x => H p x ^ 2)
        (sq_nonneg b) (fun _ x => hsqbound p x) n S (fun _ => ⟨1, by simp⟩) ()
    have hint : |∫ x, H p x ^ 2 ∂P| ≤ b ^ 2 := by
      simpa [Real.norm_eq_abs, Measure.real] using
        (norm_integral_le_of_norm_le_const
          (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hsqbound p x) :
          ‖∫ x, H p x ^ 2 ∂P‖ ≤ b ^ 2 * P.real Set.univ)
    exact (abs_sub _ _).trans (by linarith)
  have hle := le_ciSup hbdd p
  have hemp : empiricalNorm S (H p) ^ 2 =
      (n : ℝ)⁻¹ * ∑ k : Fin n, H p (S k) ^ 2 := by
    simpa only [empiricalNorm, one_div] using
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, H p (S k) ^ 2)
  have hpop : measureL2Dist P (H p) (fun _ => 0) ^ 2 = ∫ x, H p x ^ 2 ∂P := by
    simpa only [measureL2Dist, sub_zero] using
      Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (H p x))
  rw [← hemp, ← hpop, heq] at hle
  rw [← population_squareDeviation_eq_representative P F hb hbound hr S]
  exact hle

end Causalean.Stat.Concentration
