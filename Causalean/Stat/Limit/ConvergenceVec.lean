/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Vector convergence in distribution and vector Slutsky absorption

Companion to `Causalean/Stat/Limit/Convergence.lean`.  The scalar `Tendsto_dist`
predicate is hard-wired to `ℝ`-valued sequences; here we provide the
vector analogue `Tendsto_dist_vec` for sequences valued in a metric space
`E` (typically `EuclideanSpace ℝ (Fin d)`), together with the vector
Slutsky-absorption lemma needed by the multivariate Δ-method
(`Causalean/Stat/Inference/DeltaMethod.lean`) and the vector
asymptotic-normality corollary
(`Causalean/Stat/CLT/AsymptoticLinearityVec.lean`).

Mirrors `Tendsto_dist`, `Tendsto_dist.add_isLittleOp_one`, and
`Tendsto_dist.congr_ae` from the scalar file, replacing `|·|` with `‖·‖`
and `*` with `•` where needed.  The proofs port the scalar arguments
verbatim using `tendsto_iff_forall_lipschitz_integral_tendsto`
(Mathlib's portmanteau characterization in any pseudo-metric space) and
`tendstoInMeasure_iff_norm` (the `SeminormedAddCommGroup`-valued form of
convergence in measure).
-/

module
public import Causalean.Stat.Limit.Convergence
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Vector convergence in distribution

This module extends the scalar convergence-in-distribution interface to
metric-space-valued random variables.  The definition `Tendsto_dist_vec`
formulates weak convergence through pushforward probability measures, while
`Tendsto_dist_vec.add_isLittleOp_one`, `Tendsto_dist_vec.congr_ae`, and
`Tendsto_dist_vec.map_continuous` provide the vector Slutsky, a.e.-congruence,
and continuous-mapping rules used by multivariate CLT and delta-method
arguments.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory Filter Topology

/-! ## Vector convergence in distribution -/

/-- For [a measurable sample space](hyp:Ω) and [a pseudo-metric outcome space whose open sets
are measurable](hyp:E), [a sequence of random elements in the outcome space](hyp:Xn), [a
probability measure on that outcome space](hyp:Q), [a probability measure on the sample
space](hyp:μ), and
[a measurability argument that the definition no longer uses](hyp:_hXn), [convergence
in distribution of the sequence to the outcome-space probability measure](goal) means weak
convergence of its induced distributions.

Vector analogue of `Causalean.Stat.Tendsto_dist`; works for any pseudo-metric
space `E` whose open sets are measurable. -/
@[deprecated "Use Causalean.Stat.Modes.TendstoInLaw." (since := "2026-09-18")]
abbrev Tendsto_dist_vec {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (Xn : ℕ → Ω → E) (Q : Measure E) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (_hXn : ∀ n, AEMeasurable (Xn n) μ) : Prop :=
  Modes.TendstoInLaw (fun _ => μ) Xn atTop Q

/-- For [measurable row variables](hyp:Xn,hXn), [a target probability law](hyp:Q), and [a
fixed probability measure](hyp:μ), [vector convergence in distribution is equivalent to weak
convergence of the pushforward probability measures](goal). -/
lemma Tendsto_dist_vec_iff {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    (Xn : ℕ → Ω → E) (Q : Measure E) (μ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ) :
    Tendsto_dist_vec Xn Q μ hXn ↔
      Tendsto (β := ProbabilityMeasure E)
        (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
        (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) := by
  constructor
  · intro h
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using h.tendsto
  · intro h
    refine ⟨hXn, by fun_prop, ?_⟩
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using h

/-! ## Vector Slutsky absorption

If `Xn ⇒ Q` in distribution and `‖Yn − Xn‖ = o_p(1)`, then `Yn ⇒ Q`.
This is the vector analogue of `Tendsto_dist.add_isLittleOp_one` in
`AsymptoticLinearity.lean`; the proof ports verbatim using
`tendstoInMeasure_iff_norm` and the metric-space portmanteau
characterization. -/

/-- **Vector Slutsky absorption.** Suppose [`Xn` and `Yn` are `E`-valued sequences that are
measurable at every sample size](hyp:hXn,hYn), [`Xn` converges in distribution to a probability
measure `Q` on `E`](hyp:hX), and [the norm of the perturbation `‖Yn − Xn‖` is `o_p(1)`](hyp:hRem).
Then [`Yn` also converges in distribution to `Q`](goal).

Vector analogue of `Causalean.Stat.Tendsto_dist.add_isLittleOp_one` (file
`Causalean/Stat/CLT/AsymptoticLinearity.lean`). Used by the multivariate Δ-method
and by `IsAsymLinearVec.tendsto_dist_vec_of_normalizedSum`. -/
theorem Tendsto_dist_vec.add_isLittleOp_one
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Xn Yn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hRem : IsLittleOp (fun n ω => ‖Yn n ω - Xn n ω‖) (fun _ => (1 : ℝ)) μ) :
    Tendsto_dist_vec Yn Q μ hYn := by
  refine ⟨hYn, by fun_prop, ?_⟩
  have hX_tendsto :
      Tendsto (β := ProbabilityMeasure E)
        (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
        (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hX.tendsto
  have hXY : TendstoInMeasure μ (fun n ω => Yn n ω - Xn n ω) atTop (0 : Ω → E) := by
    rw [tendstoInMeasure_iff_norm]
    intro ε hε
    simpa [abs_of_nonneg] using hRem ε hε
  suffices ∀ (F : E → ℝ) (hF_bounded : ∃ (C : ℝ), ∀ x y, dist (F x) (F y) ≤ C)
      (hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n ↦ ∫ y, F y ∂(μ.map (Yn n))) atTop (𝓝 (∫ y, F y ∂Q)) by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using
      (tendsto_iff_forall_lipschitz_integral_tendsto.mpr this)
  rintro F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
  have hF_cont : Continuous F := hF_lip.continuous
  have hM_nonneg : 0 ≤ M := by
    simpa using hF_bounded (0 : E) (0 : E)
  obtain rfl | hL := eq_zero_or_pos L
  · simp only [LipschitzWith.zero_iff] at hF_lip
    specialize hF_lip (0 : E)
    simp only [← hF_lip, integral_const, smul_eq_mul]
    have h_prob n : IsProbabilityMeasure (μ.map (Yn n)) := Measure.isProbabilityMeasure_map (hYn n)
    simp
  simp_rw [Metric.tendsto_nhds, Real.dist_eq]
  suffices ∀ ε > 0, ∀ᶠ n in atTop, |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q| < L * ε by
    intro ε hε
    convert this (ε / L) (by positivity)
    field_simp
  intro ε hε
  have h_le n : |∫ y, F y ∂(μ.map (Yn n)) - ∫ y, F y ∂Q|
      ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q| := by
    refine (abs_sub_le (∫ y, F y ∂(μ.map (Yn n))) (∫ y, F y ∂(μ.map (Xn n)))
      (∫ y, F y ∂Q)).trans ?_
    gcongr
    have hFY_meas : AEStronglyMeasurable (fun x ↦ F (Yn n x)) μ :=
      (hF_cont.measurable.comp_aemeasurable (hYn n)).aestronglyMeasurable
    have hFX_meas : AEStronglyMeasurable (fun x ↦ F (Xn n x)) μ :=
      (hF_cont.measurable.comp_aemeasurable (hXn n)).aestronglyMeasurable
    have h_int_Y : Integrable (fun x ↦ F (Yn n x)) μ := by
      refine Integrable.of_bound hFY_meas (‖F (0 : E)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Yn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Yn n a)) (F 0)).trans hF_bounded
    have h_int_X : Integrable (fun x ↦ F (Xn n x)) μ := by
      refine Integrable.of_bound hFX_meas (‖F (0 : E)‖ + M) (ae_of_all _ fun a ↦ ?_)
      specialize hF_bounded (Xn n a) 0
      rw [← sub_le_iff_le_add']
      exact (abs_sub_abs_le_abs_sub (F (Xn n a)) (F 0)).trans hF_bounded
    have h_int_sub : Integrable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) μ :=
      (h_int_Y.sub h_int_X).norm
    have hD_aemeas : AEMeasurable (fun a ↦ ‖F (Yn n a) - F (Xn n a)‖) μ := by
      fun_prop
    rw [integral_map (hYn n) hF_cont.aestronglyMeasurable,
        integral_map (hXn n) hF_cont.aestronglyMeasurable,
      ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
    calc ‖∫ a, F (Yn n a) - F (Xn n a) ∂μ‖
    _ ≤ ∫ a, ‖F (Yn n a) - F (Xn n a)‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ a in {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)},
          ‖F (Yn n a) - F (Xn n a)‖ ∂μ
        + ∫ a in {x | L * (ε / 2) ≤ ‖F (Yn n x) - F (Xn n x)‖},
          ‖F (Yn n a) - F (Xn n a)‖ ∂μ := by
      symm
      simp_rw [← not_lt]
      refine integral_add_compl₀ ?_ h_int_sub
      exact nullMeasurableSet_lt hD_aemeas aemeasurable_const
    _ ≤ ∫ a in {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}, L * (ε / 2) ∂μ
        + ∫ a in {x | L * (ε / 2) ≤ ‖F (Yn n x) - F (Xn n x)‖}, M ∂μ := by
      gcongr ?_ + ?_
      · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
        · exact nullMeasurableSet_lt hD_aemeas aemeasurable_const
        · exact fun x hx ↦ hx.le
      · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a ↦ ?_
        rw [← dist_eq_norm]
        convert hF_bounded _ _
    _ = L * (ε / 2) * μ.real {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}
        + M * μ.real {ω | L * (ε / 2) ≤ ‖F (Yn n ω) - F (Xn n ω)‖} := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, Set.univ_inter,
        smul_eq_mul]
      ring
    _ ≤ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
      have hD_subset :
          {ω | L * (ε / 2) ≤ ‖F (Yn n ω) - F (Xn n ω)‖}
            ⊆ {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖} := by
        intro ω hω
        have hLip : ‖F (Yn n ω) - F (Xn n ω)‖ ≤ L * ‖Yn n ω - Xn n ω‖ := by
          simpa [dist_eq_norm] using hF_lip.dist_le_mul (Yn n ω) (Xn n ω)
        have hmul : (L : ℝ) * (ε / 2) ≤ (L : ℝ) * ‖Yn n ω - Xn n ω‖ :=
          hω.trans hLip
        exact le_of_mul_le_mul_left hmul (by exact_mod_cast hL)
      apply add_le_add
      · calc
          L * (ε / 2) * μ.real {x | ‖F (Yn n x) - F (Xn n x)‖ < L * (ε / 2)}
              ≤ L * (ε / 2) * 1 := by
                gcongr
                exact measureReal_le_one
          _ = L * (ε / 2) := by ring
      · exact mul_le_mul_of_nonneg_left
          (measureReal_mono hD_subset (measure_ne_top μ _)) hM_nonneg
  have h_tendsto :
      Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2)) := by
    suffices Tendsto (fun n ↦ L * (ε / 2) + M * μ.real {ω | ε / 2 ≤ ‖Yn n ω - Xn n ω‖}
        + |∫ y, F y ∂(μ.map (Xn n)) - ∫ y, F y ∂Q|) atTop (𝓝 (L * ε / 2 + M * 0 + 0)) by
      simpa
    refine (Tendsto.add ?_ (Tendsto.const_mul _ ?_)).add ?_
    · rw [mul_div_assoc]
      exact tendsto_const_nhds
    · simp only [tendstoInMeasure_iff_measureReal_norm, Pi.zero_apply, sub_zero] at hXY
      exact hXY (ε / 2) (by positivity)
    · have hXF : Tendsto (fun n ↦ ∫ y, F y ∂(μ.map (Xn n))) atTop (𝓝 (∫ y, F y ∂Q)) :=
        tendsto_iff_forall_lipschitz_integral_tendsto.mp hX_tendsto F
          ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      rw [tendsto_iff_dist_tendsto_zero] at hXF
      simpa only [Real.dist_eq] using hXF
  have h_lt : L * ε / 2 < L * ε := half_lt_self (by positivity)
  filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn using (h_le n).trans_lt hn

/-- Vector convergence in distribution is invariant under eventual a.e.
equality of the random variables.  Vector analogue of
`Tendsto_dist.congr_ae`. -/
theorem Tendsto_dist_vec.congr_ae
    {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {Xn Yn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hYn : ∀ n, AEMeasurable (Yn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn)
    (hXY : ∀ᶠ n in atTop, Xn n =ᵐ[μ] Yn n) :
    Tendsto_dist_vec Yn Q μ hYn := by
  refine ⟨hYn, by fun_prop, hX.tendsto.congr' ?_⟩
  filter_upwards [hXY] with n hn
  apply Subtype.ext
  exact Measure.map_congr hn

/-- Pushforward of `Tendsto_dist_vec` under a continuous map. Suppose [`Xn` is an `E`-valued
sequence, measurable at every sample size](hyp:hXn), [converging in distribution to a
probability measure `Q` on `E`](hyp:hX), and [`g : E → F` is continuous](hyp:hg). Then [the
composed sequence `g ∘ Xn` converges in distribution to the pushforward measure `Q.map
g`](goal).

Vector analogue / wrapper around
`MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`. -/
theorem Tendsto_dist_vec.map_continuous
    {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    {g : E → F} (hg : Continuous g)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun ω => g (Xn n ω)),
          Measure.isProbabilityMeasure_map
            (hg.measurable.aemeasurable.comp_aemeasurable (hXn n))⟩)
      atTop
      (𝓝 ⟨Q.map g, Measure.isProbabilityMeasure_map hg.measurable.aemeasurable⟩) := by
  have hgXn : ∀ n, AEMeasurable (fun ω => g (Xn n ω)) μ := fun n =>
    hg.measurable.aemeasurable.comp_aemeasurable (hXn n)
  letI : IsProbabilityMeasure (Q.map g) :=
    Measure.isProbabilityMeasure_map hg.measurable.aemeasurable
  have hX_tendsto :
      Tendsto (β := ProbabilityMeasure E)
        (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
        (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hX.tendsto
  have hpm := MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩)
    ⟨Q, ‹IsProbabilityMeasure Q›⟩ hX_tendsto hg
  refine hpm.congr' ?_
  filter_upwards with n
  apply Subtype.ext
  change Measure.map g (μ.map (Xn n)) = μ.map (fun ω => g (Xn n ω))
  rw [AEMeasurable.map_map_of_aemeasurable hg.measurable.aemeasurable (hXn n)]
  rfl

/-- **Continuous mapping at limit-almost-everywhere continuity points.** Suppose [`Xn` is
measurable at every sample size](hyp:hXn), [`Xn` converges in distribution to `Q`](hyp:hX),
[`g` is measurable](hyp:hgmeas), and [`g` is continuous at `Q`-almost every point](hyp:hg).
Then [the composed sequence `g ∘ Xn`
converges in distribution to the pushforward law `Q.map g`](goal).

This is the almost-everywhere-continuity form of the continuous mapping theorem (van der
Vaart, Theorem 2.3). -/
theorem Tendsto_dist_vec.map_continuous_ae
    {Ω E F : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [PseudoMetricSpace F] [MeasurableSpace F] [BorelSpace F]
    {Xn : ℕ → Ω → E} {Q : Measure E} [IsProbabilityMeasure Q]
    {g : E → F} (hgmeas : Measurable g) (hg : ∀ᵐ x ∂Q, ContinuousAt g x)
    (hXn : ∀ n, AEMeasurable (Xn n) μ)
    (hX : Tendsto_dist_vec Xn Q μ hXn) :
    Tendsto (β := ProbabilityMeasure F)
      (fun n =>
        ⟨μ.map (fun ω => g (Xn n ω)),
          Measure.isProbabilityMeasure_map
            (hgmeas.aemeasurable.comp_aemeasurable (hXn n))⟩)
      atTop
      (𝓝 ⟨Q.map g, Measure.isProbabilityMeasure_map hgmeas.aemeasurable⟩) := by
  have hX_tendsto :
      Tendsto (β := ProbabilityMeasure E)
        (fun n => ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hXn n)⟩) atTop
        (𝓝 ⟨Q, ‹IsProbabilityMeasure Q›⟩) := by
    simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hX.tendsto
  apply MeasureTheory.tendsto_of_forall_isClosed_limsup_le'
  intro C hC
  let A : Set E := g ⁻¹' C
  have hAmeas : MeasurableSet A := hC.measurableSet.preimage hgmeas
  have hnull : Q (closure A \ A) = 0 := by
    apply measure_mono_null _ (MeasureTheory.ae_iff.mp hg)
    intro x hx hcont
    apply hx.2
    change g x ∈ C
    exact by
      have hmem : g x ∈ closure C :=
        hcont.continuousWithinAt.mem_closure hx.1 (Set.mapsTo_preimage g C)
      simpa [hC.closure_eq] using hmem
  have hQA : Q (closure A) = Q A :=
    (measure_eq_measure_of_null_sdiff subset_closure hnull).symm
  have hclosed := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto
    (F := closure A) hX_tendsto isClosed_closure
  change Filter.limsup (fun n => (μ.map fun ω => g (Xn n ω)) C) atTop ≤ (Q.map g) C
  calc
    Filter.limsup
        (fun n => (μ.map fun ω => g (Xn n ω)) C) atTop ≤
        Filter.limsup (fun n => μ.map (Xn n) (closure A)) atTop := by
      apply Filter.limsup_le_limsup
      · filter_upwards with n
        change (μ.map (g ∘ Xn n)) C ≤ (μ.map (Xn n)) (closure A)
        rw [Measure.map_apply_of_aemeasurable
          (hgmeas.aemeasurable.comp_aemeasurable (hXn n)) hC.measurableSet]
        rw [Measure.map_apply_of_aemeasurable (hXn n) isClosed_closure.measurableSet]
        apply measure_mono
        intro ω hω
        exact subset_closure hω
      · exact isCoboundedUnder_le_of_le atTop fun _ => bot_le
      · apply isBoundedUnder_of
        refine ⟨1, fun n : ℕ => ?_⟩
        calc
          (μ.map (Xn n)) (closure A) ≤ (μ.map (Xn n)) Set.univ :=
            measure_mono (Set.subset_univ _)
          _ = 1 := by
            rw [Measure.map_apply_of_aemeasurable (hXn n) MeasurableSet.univ]
            simp
    _ ≤ Q (closure A) := by simpa [A] using hclosed
    _ = Q A := hQA
    _ = (Q.map g) C := by
      rw [Measure.map_apply hgmeas hC.measurableSet]

end Causalean.Stat
