/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
module
public import Causalean.Stat.Coupling.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions


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
/-! ## Coupling-invariant convergence in probability

These results lift marginal convergence in probability to arbitrary couplings of
the row measures, and then apply a map that is continuous at the deterministic
limit.  They deliberately use no independence assumption.
-/

namespace Causalean.Stat.Modes

open Filter MeasureTheory Topology
open scoped ENNReal

universe u v

/-- Given [a coupling with prescribed marginals](hyp:hν) and [a set in the first
coordinate space](hyp:s), [the first-coordinate pullback has no more mass than
that set has under its first marginal](goal). -/
theorem first_preimage_le {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure (X × Y)} {μ : Measure X} {ρ : Measure Y}
    (hν : Causalean.Stat.IsCoupling ν μ ρ) (s : Set X) :
    ν (Prod.fst ⁻¹' s) ≤ μ s := by
  simpa only [hν.map_fst] using
    (Measure.le_map_apply (μ := ν) (f := Prod.fst) measurable_fst.aemeasurable s)

/-- Given [a coupling with prescribed marginals](hyp:hν) and [a set in the second
coordinate space](hyp:s), [the second-coordinate pullback has no more mass than
that set has under its second marginal](goal). -/
theorem second_preimage_le {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure (X × Y)} {μ : Measure X} {ρ : Measure Y}
    (hν : Causalean.Stat.IsCoupling ν μ ρ) (s : Set Y) :
    ν (Prod.snd ⁻¹' s) ≤ ρ s := by
  simpa only [hν.map_snd] using
    (Measure.le_map_apply (μ := ν) (f := Prod.snd) measurable_snd.aemeasurable s)

/-- Given [a coupling with prescribed marginals](hyp:hν) and [a measurable set in
the first coordinate space](hyp:hs), [the first-coordinate pullback has exactly
the mass assigned by the first marginal](goal). -/
theorem first_preimage_eq {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure (X × Y)} {μ : Measure X} {ρ : Measure Y}
    (hν : Causalean.Stat.IsCoupling ν μ ρ) {s : Set X}
    (hs : MeasurableSet s) : ν (Prod.fst ⁻¹' s) = μ s := by
  simpa only [hν.map_fst] using
    (Measure.map_apply (μ := ν) measurable_fst hs).symm

/-- Given [a coupling with prescribed marginals](hyp:hν) and [a measurable set in
the second coordinate space](hyp:hs), [the second-coordinate pullback has exactly
the mass assigned by the second marginal](goal). -/
theorem second_preimage_eq {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure (X × Y)} {μ : Measure X} {ρ : Measure Y}
    (hν : Causalean.Stat.IsCoupling ν μ ρ) {s : Set Y}
    (hs : MeasurableSet s) : ν (Prod.snd ⁻¹' s) = ρ s := by
  simpa only [hν.map_snd] using
    (Measure.map_apply (μ := ν) measurable_snd hs).symm

/-- Given [a coupling with prescribed marginals](hyp:hν), [first and second
observables](hyp:U,V), [their constant limits](hyp:a,b), and [a deviation
threshold](hyp:ε), [the pair's tail probability is bounded by the sum of the two
marginal tail probabilities](goal). -/
theorem pair_tail_le {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    {ν : Measure (X × Y)} {μ : Measure X} {ρ : Measure Y}
    (hν : Causalean.Stat.IsCoupling ν μ ρ)
    (U : X → E) (V : Y → F) (a : E) (b : F) (ε : ℝ≥0∞) :
    ν {p | ε ≤ edist (U p.1, V p.2) (a, b)} ≤
      μ {x | ε ≤ edist (U x) a} + ρ {y | ε ≤ edist (V y) b} := by
  calc
    ν {p | ε ≤ edist (U p.1, V p.2) (a, b)} ≤
        ν ((Prod.fst ⁻¹' {x | ε ≤ edist (U x) a}) ∪
          (Prod.snd ⁻¹' {y | ε ≤ edist (V y) b})) := by
      apply measure_mono
      intro p hp
      simpa only [Set.mem_union, Set.mem_preimage, Set.mem_ofPred_eq,
        Prod.edist_eq, le_max_iff] using hp
    _ ≤ ν (Prod.fst ⁻¹' {x | ε ≤ edist (U x) a}) +
          ν (Prod.snd ⁻¹' {y | ε ≤ edist (V y) b}) := measure_union_le _ _
    _ ≤ μ {x | ε ≤ edist (U x) a} + ρ {y | ε ≤ edist (V y) b} :=
      add_le_add (first_preimage_le hν _) (second_preimage_le hν _)

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [the two row observables](hyp:U,V),
[their constant limits](hyp:a,b), [an index filter](hyp:l), and [their two
marginal convergence-in-probability statements](hyp:hU,hV), [the paired
observables converge in probability to the pair of limits under every row
coupling](goal). -/
theorem pair_tendstoInProbability
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    {E F : Type*} [PseudoEMetricSpace E] [PseudoEMetricSpace F]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → E) (V : (i : ι) → Y i → F)
    (a : E) (b : F) (l : Filter ι)
    (hU : TendstoInProbability μ U l (fun _ _ => a))
    (hV : TendstoInProbability ρ V l (fun _ _ => b)) :
    TendstoInProbability ν
      (fun i p => (U i p.1, V i p.2)) l (fun _ _ => (a, b)) := by
  intro ε hε
  have hsum : Tendsto (fun i =>
      μ i {x | ε ≤ edist (U i x) a} + ρ i {y | ε ≤ edist (V i y) b}) l (𝓝 0) := by
    simpa using (hU ε hε).add (hV ε hε)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) (fun i => pair_tail_le (hν i) (U i) (V i) a b ε)

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [the two row observables](hyp:U,V),
[their constant limits](hyp:a,b), [an index filter](hyp:l), [a map continuous
at the limiting pair](hyp:hf), and [the two marginal convergence-in-probability
statements](hyp:hU,hV), [the map applied to the paired observable converges in probability,
along the filter and under the row couplings, to the map's value at the limiting pair](goal). -/
theorem map_tendstoInProbability
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → E) (V : (i : ι) → Y i → F)
    (a : E) (b : F) (l : Filter ι) (f : E × F → G)
    (hf : ContinuousAt f (a, b))
    (hU : TendstoInProbability μ U l (fun _ _ => a))
    (hV : TendstoInProbability ρ V l (fun _ _ => b)) :
    TendstoInProbability ν
      (fun i p => f (U i p.1, V i p.2)) l (fun _ _ => f (a, b)) := by
  have hpair := pair_tendstoInProbability μ ρ ν hν U V a b l hU hV
  intro ε hε
  obtain ⟨δ, hδ, hcont⟩ := (EMetric.continuousAt_iff.mp hf) ε hε
  have hδtail := hpair δ hδ
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδtail
    (fun _ => zero_le) (fun i => by
      apply measure_mono
      intro p hp
      exact le_of_not_gt (fun hlt => not_lt_of_ge hp (hcont hlt)))

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [the two row observables](hyp:U,V),
and [their marginal almost-everywhere measurability](hyp:hU,hV), [the paired
observable is almost-everywhere measurable under every row coupling](goal). -/
theorem aemeasurable_pair
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → E) (V : (i : ι) → Y i → F)
    (hU : ∀ i, AEMeasurable (U i) (μ i))
    (hV : ∀ i, AEMeasurable (V i) (ρ i)) :
    ∀ i, AEMeasurable (fun p : X i × Y i => (U i p.1, V i p.2)) (ν i) := by
  intro i
  have hfirst : AEMeasurable (fun p : X i × Y i => U i p.1) (ν i) := by
    have h : AEMeasurable (U i) ((ν i).map Prod.fst) := by
      rw [(hν i).map_fst]
      exact hU i
    exact h.comp_measurable measurable_fst
  have hsecond : AEMeasurable (fun p : X i × Y i => V i p.2) (ν i) := by
    have h : AEMeasurable (V i) ((ν i).map Prod.snd) := by
      rw [(hν i).map_snd]
      exact hV i
    exact h.comp_measurable measurable_snd
  exact hfirst.prodMk hsecond

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [the two row observables](hyp:U,V),
[a measurable map](hyp:f,hf), and [their marginal almost-everywhere
measurability](hyp:hU,hV), [the mapped paired observable is almost-everywhere
measurable under every row coupling](goal). -/
theorem aemeasurable_map
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    {E F G : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → E) (V : (i : ι) → Y i → F)
    (f : E × F → G) (hf : Measurable f)
    (hU : ∀ i, AEMeasurable (U i) (μ i))
    (hV : ∀ i, AEMeasurable (V i) (ρ i)) :
    ∀ i, AEMeasurable (fun p : X i × Y i => f (U i p.1, V i p.2)) (ν i) := by
  intro i
  exact hf.comp_aemeasurable
    (aemeasurable_pair μ ρ ν hν U V hU hV i)

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [the two row observables](hyp:U,V),
[their constant limits](hyp:a,b), [an index filter](hyp:l), [a measurable map
continuous at the limiting pair](hyp:f,hf,hfc), [marginal almost-everywhere
measurability](hyp:hUae,hVae), and [marginal convergence in probability](hyp:hU,hV),
[the mapped paired observable is almost-everywhere measurable and converges in
probability under every row coupling](goal). -/
theorem measurable_map_tendstoInProbability
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    {E F G : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
    [PseudoMetricSpace G] [MeasurableSpace E] [MeasurableSpace F]
    [MeasurableSpace G]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → E) (V : (i : ι) → Y i → F)
    (a : E) (b : F) (l : Filter ι) (f : E × F → G)
    (hf : Measurable f) (hfc : ContinuousAt f (a, b))
    (hUae : ∀ i, AEMeasurable (U i) (μ i))
    (hVae : ∀ i, AEMeasurable (V i) (ρ i))
    (hU : TendstoInProbability μ U l (fun _ _ => a))
    (hV : TendstoInProbability ρ V l (fun _ _ => b)) :
    (∀ i, AEMeasurable (fun p : X i × Y i => f (U i p.1, V i p.2)) (ν i)) ∧
      TendstoInProbability ν
        (fun i p => f (U i p.1, V i p.2)) l (fun _ _ => f (a, b)) := by
  exact ⟨aemeasurable_map μ ρ ν hν U V f hf hUae hVae,
    map_tendstoInProbability μ ρ ν hν U V a b l f hfc hU hV⟩

/-- Given [a numerator--denominator pair](hyp:p), [the total square-root-ratio
statistic with a zero fallback](goal) is [the ordinary square-root ratio for a
positive denominator and zero otherwise](step:1). -/
noncomputable def sqrtRatioFallback (p : ℝ × ℝ) : ℝ :=
  if 0 < p.2 then Real.sqrt (p.1 / p.2) else 0

/-- [The total square-root-ratio statistic with a zero fallback is Borel
measurable](goal). -/
theorem measurable_sqrtRatioFallback : Measurable sqrtRatioFallback := by
  change Measurable (fun p : ℝ × ℝ =>
    if 0 < p.2 then Real.sqrt (p.1 / p.2) else 0)
  exact Measurable.ite (measurableSet_Ioi.preimage measurable_snd)
    ((measurable_fst.div measurable_snd).sqrt) measurable_const

/-- Given [a strictly positive limiting denominator](hyp:hb), [the total
square-root-ratio statistic is continuous at the limiting numerator--denominator
pair](goal). -/
theorem continuousAt_sqrtRatioFallback {a b : ℝ} (hb : 0 < b) :
    ContinuousAt sqrtRatioFallback (a, b) := by
  have hc : ContinuousAt (fun p : ℝ × ℝ => Real.sqrt (p.1 / p.2)) (a, b) :=
    Real.continuous_sqrt.continuousAt.comp
      (continuousAt_fst.div continuousAt_snd (ne_of_gt hb))
  apply hc.congr_of_eventuallyEq
  filter_upwards [continuousAt_snd.eventually (Ioi_mem_nhds hb)] with p hp
  simp [sqrtRatioFallback, hp]

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling measures](hyp:ν),
[proof that each row is a coupling](hyp:hν), [row numerator and denominator
observables](hyp:U,V), [their limits](hyp:a,b), [a positive denominator limit](hyp:hb),
[an index filter](hyp:l), and [marginal convergence in probability](hyp:hU,hV),
[the total square-root ratio converges in probability under every row coupling](goal). -/
theorem sqrtRatioFallback_tendstoInProbability
    {ι : Type*} {X : ι → Type u} {Y : ι → Type v}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → ℝ) (V : (i : ι) → Y i → ℝ)
    (a b : ℝ) (hb : 0 < b) (l : Filter ι)
    (hU : TendstoInProbability μ U l (fun _ _ => a))
    (hV : TendstoInProbability ρ V l (fun _ _ => b)) :
    TendstoInProbability ν
      (fun i p => sqrtRatioFallback (U i p.1, V i p.2)) l
      (fun _ _ => Real.sqrt (a / b)) := by
  simpa [sqrtRatioFallback, hb] using
    (map_tendstoInProbability μ ρ ν hν U V a b l sqrtRatioFallback
      (continuousAt_sqrtRatioFallback hb) hU hV)

/-- Given [a numerator and denominator](hyp:a,b) with [a nonnegative
denominator](hyp:hb), [the total square-root-ratio statistic equals the ordinary
square-root ratio](goal). -/
lemma sqrtRatioFallback_eq_sqrt_div {a b : ℝ} (hb : 0 ≤ b) :
    sqrtRatioFallback (a, b) = Real.sqrt (a / b) := by
  by_cases hpos : 0 < b
  · simp [sqrtRatioFallback, hpos]
  · have hz : b = 0 := le_antisymm (not_lt.mp hpos) hb
    simp [sqrtRatioFallback, hz]

/-- For [row measures](hyp:μ), [real-valued row variables](hyp:U), [a constant
limit](hyp:a), and [an index filter](hyp:l), [convergence in probability is
equivalent to convergence to zero of every strict absolute-error tail](goal). -/
lemma tendstoInProbability_iff_strict_abs
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : (i : ι) → Measure (X i)) (U : (i : ι) → X i → ℝ)
    (a : ℝ) (l : Filter ι) :
    TendstoInProbability μ U l (fun _ _ => a) ↔
      ∀ δ : ℝ, 0 < δ →
        Tendsto (fun i => μ i {x | δ < |U i x - a|}) l (nhds 0) := by
  rw [tendstoInProbability_iff_norm]
  constructor
  · intro h δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h δ hδ) (fun _ => zero_le) ?_
    intro i
    refine measure_mono fun x hx => ?_
    change δ < |U i x - a| at hx
    change δ ≤ ‖U i x - a‖
    simpa only [Real.norm_eq_abs] using hx.le
  · intro h δ hδ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (h (δ / 2) (by positivity)) (fun _ => zero_le) ?_
    intro i
    refine measure_mono fun x hx => ?_
    change δ ≤ ‖U i x - a‖ at hx
    change δ / 2 < |U i x - a|
    simpa only [Real.norm_eq_abs] using (half_lt_self hδ).trans_le hx

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling
measures](hyp:ν), [proof that each row has the prescribed marginals](hyp:hν),
[row numerator and denominator observables](hyp:U,V), [their limits](hyp:a,b),
[a positive denominator limit](hyp:hb), [an index filter](hyp:l), [pointwise
nonnegativity of every denominator observable](hyp:hVnonneg), and [marginal
convergence in probability](hyp:hU,hV), [the ordinary square-root ratio
converges in probability under every row coupling](goal). -/
lemma coupled_sqrtRatio_tendstoInProbability
    {ι : Type*} {X : ι → Type*} {Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → ℝ) (V : (i : ι) → Y i → ℝ)
    (a b : ℝ) (hb : 0 < b) (l : Filter ι)
    (hVnonneg : ∀ i y, 0 ≤ V i y)
    (hU : TendstoInProbability μ U l (fun _ _ => a))
    (hV : TendstoInProbability ρ V l (fun _ _ => b)) :
    TendstoInProbability ν
      (fun i q => Real.sqrt (U i q.1 / V i q.2)) l
      (fun _ _ => Real.sqrt (a / b)) := by
  have h := sqrtRatioFallback_tendstoInProbability
    μ ρ ν hν U V a b hb l hU hV
  have hfun :
      (fun (i : ι) (q : X i × Y i) => sqrtRatioFallback (U i q.1, V i q.2)) =
        (fun (i : ι) (q : X i × Y i) => Real.sqrt (U i q.1 / V i q.2)) := by
    funext i q
    exact sqrtRatioFallback_eq_sqrt_div (hVnonneg i q.2)
  rw [← hfun]
  exact h

/-- Given [first and second row measures](hyp:μ,ρ), [row coupling
measures](hyp:ν), [proof that each row has the prescribed marginals](hyp:hν),
[row numerator and denominator observables](hyp:U,V), [their limits](hyp:a,b),
[a positive denominator limit](hyp:hb), [an index filter](hyp:l), [pointwise
nonnegativity of every denominator observable](hyp:hVnonneg), and [strict-tail
convergence of both marginals](hyp:hU,hV), [every strict absolute-error tail of
the ordinary square-root ratio tends to zero under the coupling](goal). -/
lemma coupled_sqrtRatio_tendsto_strict_abs
    {ι : Type*} {X : ι → Type*} {Y : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Y i)]
    (μ : (i : ι) → Measure (X i)) (ρ : (i : ι) → Measure (Y i))
    (ν : (i : ι) → Measure (X i × Y i))
    (hν : ∀ i, Causalean.Stat.IsCoupling (ν i) (μ i) (ρ i))
    (U : (i : ι) → X i → ℝ) (V : (i : ι) → Y i → ℝ)
    (a b : ℝ) (hb : 0 < b) (l : Filter ι)
    (hVnonneg : ∀ i y, 0 ≤ V i y)
    (hU : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => μ i {x | δ < |U i x - a|}) l (nhds 0))
    (hV : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => ρ i {y | δ < |V i y - b|}) l (nhds 0)) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i => ν i {q | δ <
        |Real.sqrt (U i q.1 / V i q.2) - Real.sqrt (a / b)|}) l (nhds 0) := by
  rw [← tendstoInProbability_iff_strict_abs]
  exact coupled_sqrtRatio_tendstoInProbability μ ρ ν hν U V a b hb l
    hVnonneg
    ((tendstoInProbability_iff_strict_abs μ U a l).2 hU)
    ((tendstoInProbability_iff_strict_abs ρ V b l).2 hV)

end Causalean.Stat.Modes
