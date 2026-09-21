/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Localized uniform deviation

Assembles the **localized uniform deviation** bound: a high-probability,
radius-localized empirical-process inequality controlled by a critical radius.
The argument chains:

1. **Symmetrization** (`expectation_le_rademacher` from FoML).
2. **Critical radius** (`starShapedEnvelope_homogeneity`,
   `localRademacher_le_critical_radius`).
3. **Variance-sensitive concentration**
   (`uniform_deviation_bousquet_tail_countable`).

The regime carries the star-shaped envelope `ψ` directly on the centred loss
class instead of on a parameter class composed with a Lipschitz `φ`. Callers
that want to derive a loss-class envelope from a parameter-class envelope plus
a Lipschitz link should use the contraction infrastructure as a separate input
to this localized-deviation theorem.

The countable Bousquet step (3) needs no measurable maximizer: it is obtained
from finite truncations and monotone convergence of their suprema.

References:
* Bartlett, Bousquet, Mendelson, *Local Rademacher complexities*,
  Ann. Statist. 33 (2005) 1497–1537, Theorem 3.3.
* Wainwright, *High-Dimensional Statistics*, Cambridge 2019, Chapter 14.
-/

module
public import Causalean.Stat.Concentration.Rademacher.LocalRademacher
public import Causalean.Stat.Concentration.Rademacher.Symmetrization
public import Causalean.Stat.Concentration.Localization.Bousquet
public import FoML.Main

/-! # Localized Uniform Deviation

This file develops high-probability, localized empirical-process deviation
bounds for bounded classes of loss functions. It packages the boundedness and
star-shaped-envelope complexity assumptions, proves a critical-radius bound at
a fixed radius, and then obtains a uniform sharp bound by peeling. These results
provide the concentration component used by the library's statistical
estimation theory. -/

@[expose] public section

namespace Causalean
namespace Stat
namespace Concentration

open MeasureTheory ProbabilityTheory

section LocalizedRegime

/-- The localized regime packages the assumptions needed for a critical-radius
uniform-deviation bound over a bounded loss class: [a non-negative uniform
bound `b`](hyp:b,b_nonneg) such that [every loss in the class is bounded in absolute
value by `b` on the sample](hyp:bound), together with [a star-shaped envelope
`ψ`](hyp:ψ,ψ_isStarShapedEnvelope) that [upper-bounds the localized Rademacher complexity of the
class at every sample size](hyp:ψ_ub), and [a variance proxy controlled by the square of the
localization norm](hyp:variance_proxy).

    * `|F i (X ω)| ≤ b` is the envelope needed by Bousquet concentration on
      the centred loss class itself.
    * `ψ` is a star-shaped upper envelope on the population Rademacher
      complexity of `starHullZeroOut F norm r` (uniformly in `n`).

    The envelope `ψ` lives directly on the loss class. Callers wanting to
    derive a loss-class envelope from a parameter-class envelope plus a
    Lipschitz link can combine this regime with the contraction results in
    `Stat/Concentration/Rademacher/Contraction.lean`. -/
structure LocalizedRegime (Ω ι 𝒳 : Type*) [MeasurableSpace Ω]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳) where
  /-- Uniform bound on the loss class. -/
  b : ℝ
  /-- The bound is non-negative. -/
  b_nonneg : 0 ≤ b
  /-- The boundedness hypothesis: `|F i (X ω)| ≤ b` for all `i, ω`. -/
  bound : ∀ i ω, |F i (X ω)| ≤ b
  /-- Variance is controlled by the squared localization norm. -/
  variance_proxy : ∀ i, variance (fun ω => F i (X ω)) μ ≤ norm (F i) ^ 2
  /-- Star-shaped upper envelope on the localized Rademacher complexity,
      indexed by sample size `n` so that `ψ n` is the envelope at size `n`. -/
  ψ : ℕ → ℝ → ℝ
  /-- `ψ n` is a star-shaped envelope for every `n`. -/
  ψ_isStarShapedEnvelope : ∀ n, IsStarShapedEnvelope (ψ n)
  /-- For each `n`, `ψ n` upper-bounds the Rademacher complexity of
      the radius-`r` star-hull ball. -/
  ψ_ub : ∀ n, RademacherUpperBound F norm μ X n (ψ n)

end LocalizedRegime

section LocalizedUniformDeviation

variable {Ω ι 𝒳 : Type*} [MeasurableSpace Ω]

/-- **Localized uniform deviation.** Fix [a localized regime `R`](hyp:R) built from [measurable
losses `F i`](hyp:hF_meas) composed with [a measurable map `X`](hyp:hX), a confidence level [`δ` in
`(0,1]`](hyp:hδ,hδ'), [a sample size `n` at least 1](hyp:hn), and [nonnegative localization
norms](hyp:hnorm_nonneg). If [the radius `r` restricting the
class to `{i : norm (F i) ≤ r}` is at least the population critical radius `criticalRadius (R.ψ n)`,
itself positive](hyp:hr_lb,hcrit_pos), and [the star-hull Rademacher
process at radius `r` is almost-surely bounded and its empirical complexity
integrable](hyp:hrad_bdd,hrad_int), then [there is a measurable event of probability at least `1 −
δ` on which, simultaneously for every `i` with `norm (F i) ≤ r`, the empirical mean of `F i`
deviates from its population mean by at most `4rδₙ + 2√((r² + 8R.b rδₙ)log(1/δ)/n)
+ 8R.b log(1/δ)/n`, where `δₙ = criticalRadius (R.ψ n)`](goal).

    Under the `LocalizedRegime` bundle, with probability at least `1 - δ`
    over the sample, the empirical-vs-population deviation of `F i`
    is uniformly bounded for every `i` of `norm`-radius at most `r`,
    by the localized rate

        4rδ_n + 2√((r² + 8brδ_n) log(1/δ)/n) + 8b log(1/δ)/n,

    where `δ_n = criticalRadius R.ψ` is the population critical radius.

    Thus the stochastic slack scales with the localization radius rather than
    the global envelope, which is the feature needed by fast-rate peeling. -/
theorem localized_uniform_deviation
    [MeasurableSpace 𝒳] [Nonempty 𝒳] -- FoML measurability prerequisites for `F` and `X`.
    [Nonempty ι] [Countable ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hX : Measurable X) -- FoML tail-bound prerequisite for the composed class.
    (hF_meas : ∀ i, Measurable (F i)) -- Measurability of the localized class.
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (R : LocalizedRegime Ω ι 𝒳 F norm μ X) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (n : ℕ) (hn : 0 < n) {r : ℝ} (hr_lb : criticalRadius (R.ψ n) ≤ r)
    (hcrit_pos : 0 < criticalRadius (R.ψ n)) -- Needed by `starShapedEnvelope_homogeneity`.
    -- Boundedness needed for the bridge lemma's `BddAbove` hypothesis.
    (hrad_bdd : ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
      BddAbove (Set.range fun p : starHullParam ι =>
        |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
          starHullZeroOut F norm r p (S k)|))
    -- Integrability of the upper empirical Rademacher process; consumed by
    -- the bridge lemma `rademacherComplexity_zeroOut_le_starHullZeroOut`.
    (hrad_int : Integrable
      (fun ω : Fin n → Ω =>
        empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
      (Measure.pi (fun _ => μ))) :
    ∃ E : Set (Fin n → Ω), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι, norm (F i) ≤ r →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]|
          ≤ 4 * r * criticalRadius (R.ψ n)
            + 2 * Real.sqrt
                ((r ^ 2 + 8 * R.b * r * criticalRadius (R.ψ n)) *
                  Real.log (1 / δ) / n)
            + 8 * R.b * Real.log (1 / δ) / n := by
  -- Proof outline:
  -- 1. (Symmetrization) `expectation_le_rademacher` ⇒
  --    𝔼[uniformDeviation n F μ X (X ∘ ·)] ≤ 2 · rademacherComplexity n F μ X.
  -- 2. (Localization) For `i` with `norm (F i) ≤ r`,
  --    `(1, i) ∈ starHullParam ι` and `starHullZeroOut F norm r (1, i) = F i`.
  --    Hence the rademacher sup over `{i : norm (F i) ≤ r}` is dominated
  --    by `rademacherComplexity n (starHullZeroOut F norm r) μ X`.
  -- 3. (Critical radius) `R.ψ_ub n r` gives the star-hull
  --    Rademacher bound by `R.ψ r`.
  --    Past the critical radius, `starShapedEnvelope_homogeneity
  --    (R.ψ_isStarShapedEnvelope)` ⇒
  --    `R.ψ r ≤ r · criticalRadius R.ψ`.
  -- 4. Countable Bousquet concentration uses `Var (F i) ≤ r²` and the
  --    envelope `R.b` to control the deviation about its mean.
  -- 5. Combine the expectation and Bousquet bounds, retaining explicit constants.
  classical
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let fΩ : ι → Ω → ℝ := fun i ω => if norm (F i) ≤ r then F i (X ω) else 0
  have hf_meas : ∀ i, Measurable (fΩ i) := by
    intro i
    by_cases hi : norm (F i) ≤ r
    · simpa [fΩ, hi] using (hF_meas i).fun_comp hX
    · simp [fΩ, hi]
  have hf_bdd : ∀ i ω, |fΩ i ω| ≤ R.b := by
    intro i ω
    by_cases hi : norm (F i) ≤ r
    · simpa [fΩ, hi] using R.bound i ω
    · simpa [fΩ, hi] using R.b_nonneg
  have hcrit_nonneg : 0 ≤ criticalRadius (R.ψ n) := criticalRadius_nonneg (R.ψ n)
  have hr_nonneg : 0 ≤ r := le_trans hcrit_nonneg hr_lb
  have hr_pos : 0 < r := hcrit_pos.trans_le hr_lb
  have hf_variance : ∀ i, variance (fΩ i) μ ≤ r ^ 2 := by
    intro i
    by_cases hi : norm (F i) ≤ r
    · have hsquare : norm (F i) ^ 2 ≤ r ^ 2 := by
        nlinarith [hnorm_nonneg i]
      have hvar : variance (fΩ i) μ ≤ norm (F i) ^ 2 := by
        simpa [fΩ, hi] using R.variance_proxy i
      exact hvar.trans hsquare
    · have hzero : fΩ i = 0 := by funext ω; simp [fΩ, hi]
      rw [hzero, variance_zero]
      positivity
  by_cases hb0 : R.b = 0
  · refine ⟨Set.univ, MeasurableSet.univ, ?_, ?_⟩
    · rw [measure_univ]
      exact tsub_le_self
    · intro ω _ i hi
      have hzero : (fun ω' => F i (X ω')) = fun _ => (0 : ℝ) := by
        funext ω'
        have habs : |F i (X ω')| = 0 := by
          apply le_antisymm
          · simpa [hb0] using R.bound i ω'
          · exact abs_nonneg _
        exact abs_eq_zero.mp habs
      have hsample_zero : (Finset.univ.sum fun k : Fin n => F i (X (ω k))) = 0 := by
        simp [congrFun hzero]
      have hmean_zero : μ[fun ω' => F i (X ω')] = 0 := by
        simp [hzero]
      have hrc_nonneg : 0 ≤ r * criticalRadius (R.ψ n) :=
        mul_nonneg hr_nonneg hcrit_nonneg
      have hlog_nonneg : 0 ≤ Real.log (1 / δ) := by
        apply Real.log_nonneg
        rw [le_div_iff₀ hδ]
        simpa using hδ'
      calc
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]| = 0 := by
              simp [hsample_zero, hmean_zero]
        _ ≤ 4 * r * criticalRadius (R.ψ n)
            + 2 * Real.sqrt
                ((r ^ 2 + 8 * R.b * r * criticalRadius (R.ψ n)) *
                  Real.log (1 / δ) / n)
            + 8 * R.b * Real.log (1 / δ) / n := by
              positivity
  · have hb_pos : 0 < R.b := lt_of_le_of_ne R.b_nonneg (Ne.symm hb0)
    have hn_pos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    by_cases hδ_one : δ = 1
    · refine ⟨∅, MeasurableSet.empty, ?_, ?_⟩
      · simp [hδ_one]
      · simp
    have hδ_lt : δ < 1 := lt_of_le_of_ne hδ' hδ_one
    have hx : 0 < Real.log (1 / δ) := Real.log_pos (by
      rw [one_lt_div hδ]
      exact hδ_lt)
    have hrad_local :
        rademacherComplexity n
            (fun i ω => if norm (F i) ≤ r then F i (X ω) else 0) μ id
          ≤ R.ψ n r :=
      (rademacherComplexity_zeroOut_le_starHullZeroOut F norm μ X n
        (fun S σ => hrad_bdd S σ) hrad_int).trans (R.ψ_ub n r hr_nonneg)
    have hrad_crit :
        rademacherComplexity n fΩ μ id ≤ r * criticalRadius (R.ψ n) := by
      exact le_trans (by simpa [fΩ] using hrad_local)
        (starShapedEnvelope_homogeneity (R.ψ_isStarShapedEnvelope n) hcrit_pos hr_lb
          (criticalRadius_fp_of_isStarShapedEnvelope
            (R.ψ_isStarShapedEnvelope n) hcrit_pos))
    have hmean_le :
        ∫ s, uniformDeviation n fΩ μ id s ∂Measure.pi (fun _ : Fin n => μ) ≤
          2 * r * criticalRadius (R.ψ n) := by
      have hsymm := uniform_deviation_expectation_le_two_smul_rademacher_complexity
        (μ := μ) (n := n) (f := fΩ) hn id hf_meas R.b_nonneg hf_bdd
      calc
        ∫ s, uniformDeviation n fΩ μ id s ∂Measure.pi (fun _ : Fin n => μ) ≤
            2 • rademacherComplexity n fΩ μ id := by
          simpa [Function.comp_def] using hsymm
        _ ≤ 2 * (r * criticalRadius (R.ψ n)) := by
          simpa [two_nsmul] using
            mul_le_mul_of_nonneg_left hrad_crit (by norm_num : (0 : ℝ) ≤ 2)
        _ = 2 * r * criticalRadius (R.ψ n) := by ring
    let ε : ℝ :=
      2 * Real.sqrt
          ((r ^ 2 + 8 * R.b * r * criticalRadius (R.ψ n)) *
            Real.log (1 / δ) / n)
        + 8 * R.b * Real.log (1 / δ) / n
    have htail := uniform_deviation_bousquet_tail_countable μ fΩ hf_meas hb_pos hf_bdd
      hr_pos hf_variance (by positivity : 0 ≤ 2 * r * criticalRadius (R.ψ n)) n hn
      hmean_le hx
    have hproxy :
        r ^ 2 + 4 * R.b * (2 * r * criticalRadius (R.ψ n)) =
          r ^ 2 + 8 * R.b * r * criticalRadius (R.ψ n) := by ring
    rw [hproxy] at htail
    let bad : Set (Fin n → Ω) :=
      {ω | 2 * r * criticalRadius (R.ψ n) + ε ≤
        uniformDeviation n fΩ μ id (id ∘ ω)}
    let E : Set (Fin n → Ω) := badᶜ
    have hbad_meas : MeasurableSet bad := by
      exact measurableSet_le measurable_const
        ((uniformDeviation_measurable (n := n) (f := fΩ)
          (μ := μ) id hf_meas).comp measurable_id)
    have hE_meas : MeasurableSet E := hbad_meas.compl
    have hbad_le_delta : Measure.pi (fun _ : Fin n => μ) bad ≤ ENNReal.ofReal δ := by
      have hbad_toReal : (Measure.pi (fun _ : Fin n => μ) bad).toReal ≤ δ := by
        have hle_exp : (Measure.pi (fun _ : Fin n => μ)).real bad ≤
            Real.exp (-Real.log (1 / δ)) := by
          simpa [bad, ε, Function.comp_def, add_assoc] using htail
        calc
          (Measure.pi (fun _ : Fin n => μ) bad).toReal ≤
              Real.exp (-Real.log (1 / δ)) := hle_exp
          _ = δ := by
            rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1 / δ)]
            field_simp
      rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (le_of_lt hδ)]
      exact hbad_toReal
    have hE_prob : Measure.pi (fun _ : Fin n => μ) E ≥ 1 - ENNReal.ofReal δ := by
      dsimp [E]
      rw [measure_compl hbad_meas (measure_ne_top _ _), measure_univ]
      exact tsub_le_tsub_left hbad_le_delta 1
    refine ⟨E, hE_meas, hE_prob, ?_⟩
    intro ω hω i hi
    have hgood : ¬ (2 * r * criticalRadius (R.ψ n) + ε ≤
        uniformDeviation n fΩ μ id (id ∘ ω)) := by
      simpa [E, bad] using hω
    have hdev_lt :
        uniformDeviation n fΩ μ id ω < 2 * (r * criticalRadius (R.ψ n)) + ε := by
      have hnot : uniformDeviation n fΩ μ id ω <
          2 * r * criticalRadius (R.ψ n) + ε := by
        rw [not_le] at hgood
        simpa [Function.comp_def] using hgood
      simpa [mul_assoc] using hnot
    have hpoint_le_dev :
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ i (ω k))
          - μ[fun ω' => fΩ i (id ω')]|
          ≤ uniformDeviation n fΩ μ id ω := by
      dsimp [uniformDeviation]
      apply le_ciSup (f := fun j : ι =>
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))
          - μ[fun ω' => fΩ j (id ω')]|)
      rw [bddAbove_def]
      use 2 * R.b
      intro y hy
      rcases hy with ⟨j, rfl⟩
      have hsample :
          |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))| ≤ R.b := by
        calc
          _ = (n : ℝ)⁻¹ * |Finset.univ.sum fun k : Fin n => fΩ j (ω k)| := by
            rw [abs_mul, abs_of_nonneg]
            exact inv_nonneg.mpr (Nat.cast_nonneg _)
          _ ≤ (n : ℝ)⁻¹ * (Finset.univ.sum fun _ : Fin n => R.b) := by
            apply mul_le_mul_of_nonneg_left
            · exact Finset.abs_sum_le_sum_abs _ _ |>.trans
                (Finset.sum_le_sum fun k _ => hf_bdd j (ω k))
            · positivity
          _ = R.b := by
            simp
            field_simp [hn_pos.ne']
      have hmean : |μ[fun ω' => fΩ j (id ω')]| ≤ R.b := by
        calc
          _ ≤ ∫ ω', |fΩ j (id ω')| ∂μ := abs_integral_le_integral_abs
          _ ≤ ∫ _ω', R.b ∂μ := by
            apply integral_mono
            · exact Integrable.of_bound ((hf_meas j).abs.aestronglyMeasurable) R.b
                (by
                  filter_upwards with ω'
                  simpa [Real.norm_eq_abs] using hf_bdd j ω')
            · exact integrable_const R.b
            · intro ω'
              exact hf_bdd j ω'
          _ = R.b := by simp
      calc
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))
            - μ[fun ω' => fΩ j (id ω')]| ≤
            |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ j (ω k))|
              + |μ[fun ω' => fΩ j (id ω')]| := abs_sub _ _
        _ ≤ 2 * R.b := by linarith
    have hmain :
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => fΩ i (ω k))
          - μ[fun ω' => fΩ i (id ω')]|
          ≤ 4 * r * criticalRadius (R.ψ n) + ε := by
      have hpoint := hpoint_le_dev.trans (le_of_lt hdev_lt)
      have hrc_nonneg : 0 ≤ r * criticalRadius (R.ψ n) :=
        mul_nonneg hr_nonneg hcrit_nonneg
      nlinarith
    simpa [fΩ, hi, ε, add_assoc] using hmain

/-- **Sharp localized uniform deviation.** Fix [a localized regime `R`](hyp:R) built from
[measurable losses `F i`](hyp:hF_meas) composed with [a measurable map `X`](hyp:hX), a confidence
level [`δ` in `(0,1]`](hyp:hδ,hδ'), [a sample size `n` at least 1](hyp:hn), and [nonnegative
localization norms](hyp:hnorm_nonneg). Let `ρ` be
[a positive bound on the positive population critical radius](hyp:hcrit_le_ρ,hρ_pos,hcrit_pos),
and suppose [the star-hull Rademacher process is
almost-surely bounded and its empirical complexity integrable at every radius `r ≥
ρ`](hyp:hrad_bdd,hrad_int). If, further, [there is a peeling level `K` that covers the diameter cap
`Rmax ≤ ρ · 2^K` and whose Bousquet slack, consisting of a linear leading term
and the usual quadratic floor,
`2√((1+8R.b)log(2(K+1)/δ)/n) + 8R.b log(2(K+1)/δ)/(nρ)` is at most `ρ`](hyp:hδ_dom),
then [there is a measurable event of probability at least `1
− δ` on which, simultaneously for every `i` with `0 ≤ norm (F i) ≤ Rmax`, the empirical mean of `F
i` deviates from its population mean by at most `10 · ρ · norm (F i) + 5 · ρ²`](goal).

    This is a scalar `LocalizedRegime` adaptation of the peeling argument in
    Foster--Syrgkanis, *Orthogonal Statistical Learning* (arXiv:1901.09036,
    revised 2023), Lemma 14; that lemma's proof invokes Lemmas 11--13. It is not
    a verbatim formalization: this theorem takes a fixed sample size `n`, a
    diameter cap `Rmax`, and a caller-supplied critical-radius slack absorption
    hypothesis `hδ_dom`. The conclusion is uniform over the whole class with
    the sharp localized shape

        `O(ρ_n · norm(F i) + ρ_n²)`,

    where `ρ_n` is any caller-supplied upper bound on
    `criticalRadius (R.ψ n)`.  This form is convenient for downstream
    rate theorems whose public critical radius is an explicit upper bound
    rather than the exact fixed point.

    The caller is responsible for proving the Bousquet absorption condition in
    `hδ_dom`: a linear leading term (`√(x/n) ≲ ρ`) plus the usual quadratic
    floor (`ρ² ≳ R.b x/n`). -/
theorem localized_uniform_deviation_sharp
    [MeasurableSpace 𝒳] [Nonempty 𝒳]
    [Nonempty ι] [Countable ι]
    (F : ι → 𝒳 → ℝ) (norm : (𝒳 → ℝ) → ℝ)
    (μ : Measure Ω) (X : Ω → 𝒳)
    [IsProbabilityMeasure μ]
    (hX : Measurable X)
    (hF_meas : ∀ i, Measurable (F i))
    (hnorm_nonneg : ∀ i, 0 ≤ norm (F i))
    (R : LocalizedRegime Ω ι 𝒳 F norm μ X)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1)
    (n : ℕ) (hn : 0 < n)
    {ρ Rmax : ℝ}
    (hcrit_le_ρ : criticalRadius (R.ψ n) ≤ ρ)
    (hρ_pos : 0 < ρ)
    (hcrit_pos : 0 < criticalRadius (R.ψ n))
    (hrad_bdd : ∀ r : ℝ, ρ ≤ r →
      ∀ S : Fin n → 𝒳, ∀ σ : Signs n,
        BddAbove (Set.range fun p : starHullParam ι =>
          |(n : ℝ)⁻¹ * ∑ k : Fin n, (σ k : ℝ) *
            starHullZeroOut F norm r p (S k)|))
    (hrad_int : ∀ r : ℝ, ρ ≤ r →
      Integrable
        (fun ω : Fin n → Ω =>
          empiricalRademacherComplexity n (starHullZeroOut F norm r) (X ∘ ω))
        (Measure.pi (fun _ => μ)))
    (hδ_dom : ∃ K : ℕ,
      Rmax ≤ ρ * (2 : ℝ) ^ K ∧
      2 * Real.sqrt
          ((1 + 8 * R.b) * Real.log (2 * ((K : ℝ) + 1) / δ) / n)
        + 8 * R.b * Real.log (2 * ((K : ℝ) + 1) / δ) / (n * ρ)
        ≤ ρ) :
    ∃ E : Set (Fin n → Ω), MeasurableSet E ∧
      Measure.pi (fun _ => μ) E ≥ 1 - ENNReal.ofReal δ ∧
      ∀ ω ∈ E, ∀ i : ι,
        0 ≤ norm (F i) →
        norm (F i) ≤ Rmax →
        |(n : ℝ)⁻¹ * (Finset.univ.sum fun k : Fin n => F i (X (ω k)))
            - μ[fun ω' => F i (X ω')]|
          ≤ 10 * ρ * norm (F i) + 5 * ρ ^ 2 := by
  classical
  have hρ_nonneg : 0 ≤ ρ := le_of_lt hρ_pos
  obtain ⟨K, hK, hslack⟩ := hδ_dom
  let η : ℝ := δ / (2 * ((K : ℝ) + 1))
  have hη_pos : 0 < η := by
    have hden : 0 < 2 * ((K : ℝ) + 1) := by positivity
    exact div_pos hδ hden
  have hη_le_one : η ≤ 1 := by
    have hden_pos : 0 < 2 * ((K : ℝ) + 1) := by positivity
    have hden_ge_one : 1 ≤ 2 * ((K : ℝ) + 1) := by
      have hK_nonneg : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith
    dsimp [η]
    rw [div_le_iff₀ hden_pos]
    nlinarith [hδ']
  have hEk_per_shell :
      ∀ k : Fin (K + 1),
        ∃ E_k : Set (Fin n → Ω), MeasurableSet E_k ∧
          Measure.pi (fun _ : Fin n => μ) E_k ≥ 1 - ENNReal.ofReal η ∧
          ∀ ω ∈ E_k, ∀ i : ι,
            norm (F i) ≤ ρ * (2 : ℝ) ^ (k : ℕ) →
              |(n : ℝ)⁻¹ * (Finset.univ.sum fun j : Fin n => F i (X (ω j)))
                  - μ[fun ω' => F i (X ω')]|
                ≤ 5 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ := by
    intro k
    have hρ_le_shell : ρ ≤ ρ * (2 : ℝ) ^ (k : ℕ) := by
      have hpow_one : (1 : ℝ) ≤ (2 : ℝ) ^ (k : ℕ) :=
        one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
      simpa using mul_le_mul_of_nonneg_left hpow_one hρ_nonneg
    have hr_lb : criticalRadius (R.ψ n) ≤ ρ * (2 : ℝ) ^ (k : ℕ) :=
      hcrit_le_ρ.trans hρ_le_shell
    rcases localized_uniform_deviation F norm μ X hX hF_meas hnorm_nonneg R
        hη_pos hη_le_one n hn
        (r := ρ * (2 : ℝ) ^ (k : ℕ))
        hr_lb hcrit_pos
        (hrad_bdd (ρ * (2 : ℝ) ^ (k : ℕ)) hρ_le_shell)
        (hrad_int (ρ * (2 : ℝ) ^ (k : ℕ)) hρ_le_shell) with
      ⟨E_k, hE_k_meas, hE_k_prob, hE_k_bound⟩
    refine ⟨E_k, hE_k_meas, hE_k_prob, ?_⟩
    intro ω hω i hi
    have h := hE_k_bound ω hω i hi
    have hshell_nonneg : 0 ≤ ρ * (2 : ℝ) ^ (k : ℕ) := by positivity
    have hshell_pos : 0 < ρ * (2 : ℝ) ^ (k : ℕ) := by positivity
    have hcrit_le :
        4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (R.ψ n)
          ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ := by
      nlinarith [hcrit_le_ρ, hshell_nonneg]
    have hη_inv : 1 / η = 2 * ((K : ℝ) + 1) / δ := by
      dsimp [η]
      field_simp [ne_of_gt hδ]
    have hlog_nonneg :
        0 ≤ Real.log (2 * ((K : ℝ) + 1) / δ) := by
      apply Real.log_nonneg
      have hden : 0 < δ := hδ
      rw [le_div_iff₀ hden]
      nlinarith [hδ', (Nat.cast_nonneg K : (0 : ℝ) ≤ (K : ℝ))]
    have htail_slack' :
        2 * Real.sqrt
              (((ρ * (2 : ℝ) ^ (k : ℕ)) ^ 2 +
                8 * R.b * (ρ * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (R.ψ n)) *
                Real.log (2 * ((K : ℝ) + 1) / δ) / n)
            + 8 * R.b * Real.log (2 * ((K : ℝ) + 1) / δ) / n ≤
          (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ :=
      bousquet_shell_slack_le R.b_nonneg hρ_pos hρ_le_shell hcrit_le_ρ
        hlog_nonneg hn hslack
    calc
      |(n : ℝ)⁻¹ * (Finset.univ.sum fun j : Fin n => F i (X (ω j)))
          - μ[fun ω' => F i (X ω')]|
          ≤ 4 * (ρ * (2 : ℝ) ^ (k : ℕ)) * criticalRadius (R.ψ n)
              + 2 * Real.sqrt
                  (((ρ * (2 : ℝ) ^ (k : ℕ)) ^ 2 +
                    8 * R.b * (ρ * (2 : ℝ) ^ (k : ℕ)) *
                      criticalRadius (R.ψ n)) * Real.log (1 / η) / n)
              + 8 * R.b * Real.log (1 / η) / n := h
      _ ≤ 5 * (ρ * (2 : ℝ) ^ (k : ℕ)) * ρ := by
        rw [hη_inv]
        nlinarith [hcrit_le, htail_slack']
  let μπ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let Ek : Fin (K + 1) → Set (Fin n → Ω) := fun k => (hEk_per_shell k).choose
  let Etot : Set (Fin n → Ω) := ⋂ k, Ek k
  have hEk_meas : ∀ k, MeasurableSet (Ek k) := by
    intro k
    exact (hEk_per_shell k).choose_spec.1
  have hEtot_meas : MeasurableSet Etot := by
    exact MeasurableSet.iInter hEk_meas
  have hEk_compl_le : ∀ k, μπ ((Ek k)ᶜ) ≤ ENNReal.ofReal η := by
    intro k
    have hprob : μπ (Ek k) ≥ 1 - ENNReal.ofReal η :=
      (hEk_per_shell k).choose_spec.2.1
    have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal η + μπ (Ek k) := by
      simpa [add_comm] using (tsub_le_iff_right.mp hprob)
    rw [measure_compl (hEk_meas k) (measure_ne_top _ _), measure_univ]
    exact tsub_le_iff_right.mpr hone_le
  have hbad_subset : Etotᶜ ⊆ ⋃ k, (Ek k)ᶜ := by
    simp [Etot, Ek]
  have hbad_le : μπ (Etotᶜ) ≤ ENNReal.ofReal δ := by
    calc
      μπ (Etotᶜ) ≤ μπ (⋃ k, (Ek k)ᶜ) := measure_mono hbad_subset
      _ ≤ ∑ k : Fin (K + 1), μπ ((Ek k)ᶜ) :=
        measure_iUnion_fintype_le μπ fun k => (Ek k)ᶜ
      _ ≤ ∑ _k : Fin (K + 1), ENNReal.ofReal η := by
        exact Finset.sum_le_sum fun k _hk => hEk_compl_le k
      _ = (K + 1 : ℕ) * ENNReal.ofReal η := by simp
      _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ)) * ENNReal.ofReal η := by
        have hcoe :
            ((K : ENNReal) + 1) = ENNReal.ofReal ((K : ℝ) + 1) := by
          calc
            ((K : ENNReal) + 1)
                = ENNReal.ofReal (K : ℝ) + ENNReal.ofReal (1 : ℝ) := by simp
            _ = ENNReal.ofReal ((K : ℝ) + 1) :=
                (ENNReal.ofReal_add (Nat.cast_nonneg K) (by norm_num)).symm
        simpa [Nat.cast_add, Nat.cast_one] using
          congrArg (fun x => x * ENNReal.ofReal η) hcoe
      _ = ENNReal.ofReal (((K + 1 : ℕ) : ℝ) * η) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (((K + 1 : ℕ) : ℝ)))]
      _ = ENNReal.ofReal (δ / 2) := by
        congr 1
        dsimp [η]
        have hcast : (((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1) := by norm_num
        rw [hcast]
        field_simp
      _ ≤ ENNReal.ofReal δ := by
        exact ENNReal.ofReal_le_ofReal (by linarith [hδ])
  have hEtot_prob : μπ Etot ≥ 1 - ENNReal.ofReal δ := by
    rw [measure_compl hEtot_meas (measure_ne_top _ _), measure_univ] at hbad_le
    have hone_le : (1 : ENNReal) ≤ ENNReal.ofReal δ + μπ Etot :=
      tsub_le_iff_right.mp hbad_le
    exact tsub_le_iff_right.mpr (by simpa [add_comm] using hone_le)
  refine ⟨Etot, hEtot_meas, hEtot_prob, ?_⟩
  intro ω hω i hi_nonneg hi_diam
  have hShell_select :
      ∃ k₀ : Fin (K + 1),
        norm (F i) ≤ ρ * (2 : ℝ) ^ (k₀ : ℕ) ∧
        5 * (ρ * (2 : ℝ) ^ (k₀ : ℕ)) * ρ
          ≤ 10 * ρ * norm (F i) + 5 * ρ ^ 2 := by
    have htop : norm (F i) ≤ ρ * (2 : ℝ) ^ K := hi_diam.trans hK
    by_cases hsmall : norm (F i) ≤ ρ
    · let kzero : Fin (K + 1) := ⟨0, Nat.succ_pos K⟩
      refine ⟨kzero, ?_, ?_⟩
      · change norm (F i) ≤ ρ * (2 : ℝ) ^ (0 : ℕ)
        rw [pow_zero, mul_one]
        exact hsmall
      · change 5 * (ρ * (2 : ℝ) ^ (0 : ℕ)) * ρ
            ≤ 10 * ρ * norm (F i) + 5 * ρ ^ 2
        rw [pow_zero, mul_one]
        nlinarith [hρ_nonneg, hi_nonneg, sq_nonneg ρ]
    · let p : ℕ → Prop := fun j => norm (F i) ≤ ρ * (2 : ℝ) ^ j
      have hex : ∃ j, p j := ⟨K, htop⟩
      let j0 : ℕ := Nat.find hex
      have hj0_spec : p j0 := Nat.find_spec hex
      have hj0_pos : 0 < j0 := by
        by_contra hj0_not
        have hj0_zero : j0 = 0 := Nat.eq_zero_of_not_pos hj0_not
        have : norm (F i) ≤ ρ := by
          change norm (F i) ≤ ρ * (2 : ℝ) ^ j0 at hj0_spec
          rw [hj0_zero, pow_zero, mul_one] at hj0_spec
          exact hj0_spec
        exact hsmall this
      have hj0_le_K : j0 ≤ K := Nat.find_min' hex htop
      refine ⟨⟨j0, Nat.lt_succ_of_le hj0_le_K⟩, hj0_spec, ?_⟩
      have hprev_not : ¬ p (j0 - 1) := by
        have hlt : j0 - 1 < j0 := Nat.sub_one_lt (Nat.ne_of_gt hj0_pos)
        exact Nat.find_min hex hlt
      have hprev_lt : ρ * (2 : ℝ) ^ (j0 - 1) < norm (F i) := not_le.mp hprev_not
      have hr_le_normF : ρ * (2 : ℝ) ^ j0 ≤ 2 * norm (F i) := by
        have hj0_eq : j0 = (j0 - 1) + 1 := by omega
        have hpow : (2 : ℝ) ^ j0 = (2 : ℝ) ^ (j0 - 1) * 2 := by
          conv_lhs => rw [hj0_eq, pow_succ]
        rw [hpow]
        nlinarith
      nlinarith
  rcases hShell_select with ⟨k₀, hk₀_radius, hk₀_rate⟩
  have hY_in_Ek : ω ∈ Ek k₀ := Set.iInter_subset (fun k => Ek k) k₀ hω
  have hdev := (hEk_per_shell k₀).choose_spec.2.2 ω hY_in_Ek i hk₀_radius
  exact hdev.trans hk₀_rate

end LocalizedUniformDeviation

end Concentration
end Stat
end Causalean
