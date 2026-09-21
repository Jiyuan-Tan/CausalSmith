/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Modes of stochastic convergence

This module gives one vocabulary for stochastic convergence that covers scalar and vector
statistics, triangular arrays, and finite-design rows.  Unlike Mathlib's fixed-space
`MeasureTheory.TendstoInMeasure`, `TendstoInProbability` permits both the probability space and
the limiting random variable to vary with the index.  `TendstoInLaw` exposes a probability law
itself as the distributional target.

## Using Mathlib's results

Mathlib's `Mathlib.MeasureTheory.Function.ConvergenceInDistribution` already supplies
`MeasureTheory.TendstoInDistribution.continuous_comp` (continuous mapping),
`MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` and its additive and
multiplicative Slutsky corollaries, `MeasureTheory.tendstoInDistribution_of_tendstoInMeasure_sub`
(converging together), and `MeasureTheory.TendstoInMeasure.tendstoInDistribution`.  The fixed-space
almost-sure-to-probability results remain in
`Mathlib.MeasureTheory.Function.ConvergenceInMeasure`.  They are intentionally not restated here.
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped BoundedContinuousFunction ENNReal NNReal Topology

namespace Causalean.Stat.Modes

/-- Given [a row measure](hyp:μ), [row random variables](hyp:X), [an index
filter](hyp:l), and [row limiting random variables](hyp:g), [convergence in probability](goal)
means that every positive extended-distance tail has row measure tending to zero along the
filter. -/
def TendstoInProbability {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [EDist E]
    (μ : (i : ι) → Measure (Ω i)) (X : (i : ι) → Ω i → E) (l : Filter ι)
    (g : (i : ι) → Ω i → E) : Prop :=
  ∀ ε, 0 < ε → Tendsto (fun i => μ i {ω | ε ≤ edist (X i ω) (g i ω)}) l (𝓝 0)

/-- For [a fixed measure](hyp:μ), [an indexed family of random variables](hyp:X), [a
filter](hyp:l), and [a fixed limiting random variable](hyp:g), [the hub's convergence in
probability is exactly Mathlib's convergence in measure](goal). -/
theorem tendstoInProbability_const_space {ι Ω E : Type*} [MeasurableSpace Ω] [EDist E]
    (μ : Measure Ω) (X : ι → Ω → E) (l : Filter ι) (g : Ω → E) :
    TendstoInProbability (fun _ => μ) X l (fun _ => g) ↔ TendstoInMeasure μ X l g :=
  Iff.rfl

private lemma tendstoInProbability_of_ne_top
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [EDist E] {μ : (i : ι) → Measure (Ω i)}
    {X g : (i : ι) → Ω i → E} {l : Filter ι}
    (h : ∀ ε, 0 < ε → ε ≠ ∞ →
      Tendsto (fun i => μ i {ω | ε ≤ edist (X i ω) (g i ω)}) l (𝓝 0)) :
    TendstoInProbability μ X l g := by
  intro ε hε
  by_cases hεtop : ε = ∞
  · have hOne := h 1 (by simp) (by simp)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hOne
      (fun _ => zero_le) ?_
    intro i
    simp only [hεtop]
    gcongr
    simp
  · exact h ε hε hεtop

private lemma tendstoInProbability_iff_dist
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [PseudoMetricSpace E] {μ : (i : ι) → Measure (Ω i)}
    {X g : (i : ι) → Ω i → E} {l : Filter ι} :
    TendstoInProbability μ X l g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => μ i {ω | ε ≤ dist (X i ω) (g i ω)}) l (𝓝 0) := by
  refine ⟨fun h ε hε => ?_, fun h => ?_⟩
  · convert! h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) with i ω
    rw [edist_dist, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  · refine tendstoInProbability_of_ne_top fun ε hε hεtop => ?_
    convert! h ε.toReal (ENNReal.toReal_pos hε.ne' hεtop) with i ω
    rw [edist_dist, ENNReal.le_ofReal_iff_toReal_le hεtop (by positivity)]

/-- For [row measures](hyp:μ), [seminormed-group-valued row variables](hyp:X), [a
filter](hyp:l), and [row limits](hyp:g), [convergence in probability is equivalent to every
positive norm-tail probability tending to zero](goal). -/
theorem tendstoInProbability_iff_norm
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E] (μ : (i : ι) → Measure (Ω i))
    (X : (i : ι) → Ω i → E) (l : Filter ι) (g : (i : ι) → Ω i → E) :
    TendstoInProbability μ X l g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => μ i {ω | ε ≤ ‖X i ω - g i ω‖}) l (𝓝 0) := by
  simpa only [dist_eq_norm_sub] using
    (tendstoInProbability_iff_dist (μ := μ) (X := X) (l := l) (g := g))

/-- For [finite row measures](hyp:μ), [seminormed-group-valued row variables](hyp:X), [a
filter](hyp:l), and [row limits](hyp:g), [convergence in probability is equivalent to the
real-valued measure of every positive norm tail tending to zero](goal). -/
theorem tendstoInProbability_iff_measureReal_norm
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [SeminormedAddCommGroup E] (μ : (i : ι) → Measure (Ω i))
    [∀ i, IsFiniteMeasure (μ i)]
    (X : (i : ι) → Ω i → E) (l : Filter ι) (g : (i : ι) → Ω i → E) :
    TendstoInProbability μ X l g ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun i => (μ i).real {ω | ε ≤ ‖X i ω - g i ω‖}) l (𝓝 0) := by
  rw [tendstoInProbability_iff_norm]
  congr! with ε hε
  simp_rw [measureReal_def,
    ENNReal.tendsto_toReal_zero_iff (fun i => measure_ne_top (μ i) _)]

/-- Given [row probability measures](hyp:μ), [row random variables](hyp:X), [an index
filter](hyp:l), and [a target probability law](hyp:Q), [convergence in law](goal) means weak
convergence of the row pushforward laws to that supplied law. -/
def TendstoInLaw {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : ι) → Ω i → E) (l : Filter ι) (Q : Measure E) [IsProbabilityMeasure Q] : Prop :=
  TendstoInDistribution X l (id : E → E) μ Q

/-- For [row probability measures](hyp:μ), [row random variables](hyp:X), [an index
filter](hyp:l), and [a target probability law](hyp:Q), [convergence in law is equivalent to row
measurability together with convergence of expectations of every bounded continuous real test
function](goal). -/
theorem tendstoInLaw_iff_boundedContinuous
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [OpensMeasurableSpace E]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : ι) → Ω i → E) (l : Filter ι) (Q : Measure E) [IsProbabilityMeasure Q] :
    TendstoInLaw μ X l Q ↔
      (∀ i, AEMeasurable (X i) (μ i)) ∧
        ∀ f : E →ᵇ ℝ,
          Tendsto (fun i => ∫ ω, f (X i ω) ∂μ i) l (𝓝 (∫ x, f x ∂Q)) := by
  constructor
  · intro h
    refine ⟨h.forall_aemeasurable, fun f => ?_⟩
    have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp h.tendsto f
    simpa only [ProbabilityMeasure.coe_mk,
      integral_map (h.forall_aemeasurable _) f.continuous.aestronglyMeasurable,
      integral_map measurable_id.aemeasurable f.continuous.aestronglyMeasurable,
      Function.comp_apply, id_eq] using ht
  · rintro ⟨hX, ht⟩
    refine ⟨hX, by fun_prop, ?_⟩
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    simpa only [ProbabilityMeasure.coe_mk,
      integral_map (hX _) f.continuous.aestronglyMeasurable,
      integral_map measurable_id.aemeasurable f.continuous.aestronglyMeasurable,
      Function.comp_apply, id_eq] using ht f

/-- For [row probability measures](hyp:μ), [row random variables](hyp:X), [an index
filter](hyp:l), and [a point defining the target Dirac law](hyp:c), if [the variables converge in
law to that Dirac law](hyp:h), then [they converge in probability to the point](goal). -/
theorem TendstoInLaw.tendstoInProbability_const
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E : Type*} [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : (i : ι) → Ω i → E) (l : Filter ι) (c : E)
    (h : TendstoInLaw μ X l (Measure.dirac c)) :
    TendstoInProbability μ X l (fun _ _ => c) := by
  intro ε hε
  let F : Set E := {x | ε ≤ edist x c}
  have hF : IsClosed F := by
    exact isClosed_le continuous_const
      (continuous_edist.comp (continuous_id.prodMk continuous_const))
  have hlimsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto hF
  have hcF : (Measure.dirac c).map (id : E → E) F = 0 := by
    rw [Measure.map_id, Measure.dirac_apply' c hF.measurableSet]
    simp [F, hε.ne']
  have hlimsup_zero :
      l.limsup (fun i => (μ i).map (X i) F) ≤ 0 := by
    simpa only [ProbabilityMeasure.coe_mk, hcF] using hlimsup
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hevent : ∀ᶠ i in l, (μ i).map (X i) F < δ :=
    ((Filter.limsup_le_iff
      (u := fun i => (μ i).map (X i) F) (x := (0 : ℝ≥0∞))).mp hlimsup_zero) δ hδ
  filter_upwards [hevent] with i hi
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable i) hF.measurableSet] at hi
  exact hi.le

/-- If [row random variables converge in probability to row limits](hyp:h) and [a map is
uniformly continuous](hyp:hf), then [applying that map to both the variables and limits preserves
convergence in probability](goal). -/
theorem TendstoInProbability.uniformContinuous_comp
    {ι : Type*} {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {μ : (i : ι) → Measure (Ω i)} {X g : (i : ι) → Ω i → E} {l : Filter ι}
    {f : E → F} (h : TendstoInProbability μ X l g) (hf : UniformContinuous f) :
    TendstoInProbability μ (fun i ω => f (X i ω)) l (fun i ω => f (g i ω)) := by
  intro ε hε
  obtain ⟨δ, hδ, hmap⟩ := EMetric.uniformContinuous_iff.mp hf ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h δ hδ)
    (fun _ => zero_le) ?_
  intro i
  refine measure_mono fun ω hω => ?_
  by_contra hnot
  exact (not_lt_of_ge hω) (hmap (lt_of_not_ge hnot))

end Causalean.Stat.Modes
