module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Probability.CDF
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Uniform convergence of cumulative distribution functions

This module proves the deterministic finite-grid form of Pólya's theorem and applies
Portmanteau to probability measures on the real line.  Weak convergence to a law with a
continuous CDF then upgrades to uniform convergence of CDFs.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Topology

namespace Causalean.Stat

/-- A [real probability measure](hyp:μ) whose CDF is [continuous at a threshold](hyp:hcont) has
[zero probability at that threshold](goal). -/
theorem measure_singleton_eq_zero_of_continuousAt_cdf (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {t : ℝ} (hcont : ContinuousAt (cdf μ) t) : μ {t} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton,
    hcont.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- [Weak convergence of probability measures](hyp:hν) and [continuity of the limiting CDF at
the threshold](hyp:hcont) ensure that [the CDF values at that threshold converge](goal). -/
theorem tendsto_cdf_at_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs l (𝓝 ν)) {t : ℝ}
    (hcont : ContinuousAt (cdf (ν : Measure ℝ)) t) :
    Tendsto (fun i ↦ cdf (νs i : Measure ℝ) t) l
      (𝓝 (cdf (ν : Measure ℝ) t)) := by
  have hnull : ν (frontier (Iic t)) = 0 := by
    rw [frontier_Iic]
    exact (ProbabilityMeasure.null_iff_toMeasure_null ν {t}).2
      (measure_singleton_eq_zero_of_continuousAt_cdf _ hcont)
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto hν hnull
  simpa only [Function.comp_def, cdf_eq_real,
    ProbabilityMeasure.measureReal_eq_coe_coeFn] using
      ((NNReal.continuous_coe.tendsto (ν (Iic t))).comp h)

private theorem tendstoUniformly_of_monotone_of_tendsto_at_of_bounds
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ i, Monotone (F i)) (hF0 : ∀ i x, 0 ≤ F i x) (hF1 : ∀ i x, F i x ≤ 1)
    (hGmono : Monotone G) (hGcont : Continuous G)
    (hGbot : Tendsto G atBot (𝓝 0)) (hGtop : Tendsto G atTop (𝓝 1))
    (hpoint : ∀ t, Tendsto (fun i ↦ F i t) l (𝓝 (G t))) :
    TendstoUniformly F G l := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  let η := ε / 4
  have hη : 0 < η := div_pos hε (by norm_num)
  have h4η : 4 * η = ε := by dsimp [η]; ring
  obtain ⟨a, haG, ha0⟩ : ∃ a : ℝ, dist (G a) 0 < η ∧ a < 0 := by
    exact (((Metric.tendsto_nhds.1 hGbot) η hη).and (eventually_lt_atBot 0)).exists
  obtain ⟨b, hbG, h0b⟩ : ∃ b : ℝ, dist (G b) 1 < η ∧ 0 < b := by
    exact (((Metric.tendsto_nhds.1 hGtop) η hη).and (eventually_gt_atTop 0)).exists
  have hab : a ≤ b := (ha0.trans h0b).le
  have hcomp : IsCompact (Icc (a - 1) (b + 1)) := isCompact_Icc
  have huc : UniformContinuousOn G (Icc (a - 1) (b + 1)) :=
    hcomp.uniformContinuousOn_of_continuous hGcont.continuousOn
  obtain ⟨δ, hδ, hGδ⟩ := (Metric.uniformContinuousOn_iff.1 huc) η hη
  let r := min (δ / 3) (1 / 2 : ℝ)
  have hr : 0 < r := lt_min (div_pos hδ (by norm_num)) (by norm_num)
  have hrδ : 2 * r < δ := by
    have hle : r ≤ δ / 3 := min_le_left _ _
    nlinarith
  have hr1 : r ≤ 1 := by
    have hle : r ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ :=
    (isCompact_Icc.finite_cover_balls hr : ∃ t ⊆ Icc a b, t.Finite ∧
      Icc a b ⊆ ⋃ x ∈ t, Metric.ball x r)
  have hendpoints : ∀ c ∈ t, c - r ∈ Icc (a - 1) (b + 1) ∧
      c + r ∈ Icc (a - 1) (b + 1) := by
    intro c hc
    have hcI := ht_sub hc
    constructor <;> constructor <;> dsimp [Icc] at *
    · linarith [hcI.1]
    · linarith [hcI.2]
    · linarith [hcI.1]
    · linarith [hcI.2]
  have hosc : ∀ c ∈ t, dist (G (c - r)) (G (c + r)) < η := by
    intro c hc
    apply hGδ (c - r) (hendpoints c hc).1 (c + r) (hendpoints c hc).2
    rw [Real.dist_eq]
    have heq : |(c - r) - (c + r)| = 2 * r := by
      rw [show (c - r) - (c + r) = -(2 * r) by ring, abs_neg,
        abs_of_pos (mul_pos (by norm_num) hr)]
    rw [heq]
    exact hrδ
  have hmesh : ∀ᶠ i in l, ∀ c ∈ t,
      dist (F i (c - r)) (G (c - r)) < η ∧
      dist (F i (c + r)) (G (c + r)) < η := by
    rw [ht_fin.eventually_all]
    intro c hc
    exact ((Metric.tendsto_nhds.1 (hpoint (c - r))) η hη).and
      ((Metric.tendsto_nhds.1 (hpoint (c + r))) η hη)
  have haev : ∀ᶠ i in l, dist (F i a) (G a) < η :=
    (Metric.tendsto_nhds.1 (hpoint a)) η hη
  have hbev : ∀ᶠ i in l, dist (F i b) (G b) < η :=
    (Metric.tendsto_nhds.1 (hpoint b)) η hη
  filter_upwards [hmesh, haev, hbev] with i hi hia hib
  intro x
  rw [Real.dist_eq, abs_lt]
  have hG0 : 0 ≤ G x := hGmono.le_of_tendsto hGbot x
  have hG1 : G x ≤ 1 := hGmono.ge_of_tendsto hGtop x
  by_cases hxa : x < a
  · have hGa : G a < η := by
      simpa [Real.dist_eq, abs_of_nonneg (hGmono.le_of_tendsto hGbot a)] using haG
    rw [Real.dist_eq, abs_lt] at hia
    have hFxFa := hF i hxa.le
    have hGxGa := hGmono hxa.le
    constructor <;> linarith [hF0 i x]
  by_cases hbx : b < x
  · have hGb : 1 - η < G b := by
      rw [Real.dist_eq, abs_lt] at hbG
      linarith
    rw [Real.dist_eq, abs_lt] at hib
    have hFbFx := hF i hbx.le
    have hGbGx := hGmono hbx.le
    constructor <;> linarith [hF1 i x]
  have hxI : x ∈ Icc a b := ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩
  have hxcover := ht_cover hxI
  simp only [mem_iUnion] at hxcover
  obtain ⟨c, hc, hxc⟩ := hxcover
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hxc
  have hleft : c - r ≤ x := by linarith
  have hright : x ≤ c + r := by linarith
  have hi_c := hi c hc
  rw [Real.dist_eq, abs_lt, Real.dist_eq, abs_lt] at hi_c
  have hosc' := hosc c hc
  rw [Real.dist_eq,
    abs_of_nonpos (sub_nonpos.mpr (hGmono (by linarith : c - r ≤ c + r)))] at hosc'
  have hFlo := hF i hleft
  have hGlo := hGmono hleft
  have hFhi := hF i hright
  have hGhi := hGmono hright
  constructor <;> linarith

/-- [Monotonicity](hyp:hF,hGmono), [unit-interval bounds](hyp:hF0,hF1), [continuity](hyp:hGcont),
[zero and one tail limits](hyp:hGbot,hGtop), and [pointwise convergence](hyp:hpoint) together
imply [uniform convergence on the real line](goal). -/
theorem tendstoUniformly_of_monotone_of_tendsto_at
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ i, Monotone (F i)) (hF0 : ∀ i x, 0 ≤ F i x) (hF1 : ∀ i x, F i x ≤ 1)
    (hGmono : Monotone G) (hGcont : Continuous G)
    (hGbot : Tendsto G atBot (𝓝 0)) (hGtop : Tendsto G atTop (𝓝 1))
    (hpoint : ∀ t, Tendsto (fun i ↦ F i t) l (𝓝 (G t))) :
    TendstoUniformly F G l := by
  -- Given ε, choose finite tails where `G` is within ε of 0 and 1.  Uniform continuity of
  -- `G` on the compact middle interval supplies a finite ordered mesh with oscillation < ε.
  -- Pointwise convergence on that mesh is eventually simultaneous; monotonicity sandwiches
  -- every `F i x - G x` between neighboring mesh errors plus the oscillation allowance.
  exact tendstoUniformly_of_monotone_of_tendsto_at_of_bounds
    hF hF0 hF1 hGmono hGcont hGbot hGtop hpoint

/-- **Pólya's theorem.** [Weak convergence of real probability measures](hyp:hν) to a law with a
[continuous CDF](hyp:hcont) implies [uniform convergence of their CDFs on the real line](goal). -/
theorem tendstoUniformly_cdf_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs l (𝓝 ν)) (hcont : Continuous (cdf (ν : Measure ℝ))) :
    TendstoUniformly (fun i ↦ cdf (νs i : Measure ℝ)) (cdf (ν : Measure ℝ)) l := by
  apply tendstoUniformly_of_monotone_of_tendsto_at_of_bounds
    (fun i ↦ monotone_cdf (νs i : Measure ℝ))
    (fun i ↦ cdf_nonneg (νs i : Measure ℝ))
    (fun i ↦ cdf_le_one (νs i : Measure ℝ))
    (monotone_cdf (ν : Measure ℝ)) hcont
    (tendsto_cdf_atBot (ν : Measure ℝ)) (tendsto_cdf_atTop (ν : Measure ℝ))
  intro t
  exact tendsto_cdf_at_of_tendsto hν hcont.continuousAt

/-- The [Kolmogorov distance between two probability measures](goal) is [defined from the first
measure](hyp:μ) and [the second measure](hyp:ν) by [the supremum of their absolute CDF
differences over all thresholds](step:1). -/
noncomputable def cdfKolmogorov (μ ν : ProbabilityMeasure ℝ) : ℝ :=
  ⨆ t : ℝ, |cdf (μ : Measure ℝ) t - cdf (ν : Measure ℝ) t|

/-- [Any two probability measures](hyp:μ,hyp:ν) have [a nonnegative Kolmogorov distance](goal). -/
theorem cdfKolmogorov_nonneg (μ ν : ProbabilityMeasure ℝ) : 0 ≤ cdfKolmogorov μ ν := by
  have hb : BddAbove (range fun t : ℝ ↦
      |cdf (μ : Measure ℝ) t - cdf (ν : Measure ℝ) t|) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨t, rfl⟩
    rw [abs_le]
    constructor <;>
      linarith [cdf_nonneg (μ : Measure ℝ) t, cdf_le_one (μ : Measure ℝ) t,
        cdf_nonneg (ν : Measure ℝ) t, cdf_le_one (ν : Measure ℝ) t]
  exact (abs_nonneg (cdf (μ : Measure ℝ) 0 - cdf (ν : Measure ℝ) 0)).trans
    (le_ciSup hb 0)

/-- [Any two probability measures](hyp:μ,hyp:ν) have [a Kolmogorov distance no greater than
one](goal). -/
theorem cdfKolmogorov_le_one (μ ν : ProbabilityMeasure ℝ) : cdfKolmogorov μ ν ≤ 1 := by
  refine ciSup_le fun t ↦ ?_
  rw [abs_le]
  constructor <;>
    linarith [cdf_nonneg (μ : Measure ℝ) t, cdf_le_one (μ : Measure ℝ) t,
      cdf_nonneg (ν : Measure ℝ) t, cdf_le_one (ν : Measure ℝ) t]

/-- [Weak convergence of the first family](hyp:hν) and [of the second family](hyp:hν') to the
same law with [a continuous CDF](hyp:hcont) imply [that their Kolmogorov distance tends to
zero](goal). -/
theorem tendsto_cdfKolmogorov_of_tendsto {ι : Type*} {l : Filter ι}
    {νs νs' : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : Tendsto νs l (𝓝 ν)) (hν' : Tendsto νs' l (𝓝 ν))
    (hcont : Continuous (cdf (ν : Measure ℝ))) :
    Tendsto (fun i ↦ cdfKolmogorov (νs i) (νs' i)) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let η := ε / 4
  have hη : 0 < η := div_pos hε (by norm_num)
  have h4η : 4 * η = ε := by dsimp [η]; ring
  have hu := Metric.tendstoUniformly_iff.1 (tendstoUniformly_cdf_of_tendsto hν hcont)
  have hu' := Metric.tendstoUniformly_iff.1 (tendstoUniformly_cdf_of_tendsto hν' hcont)
  filter_upwards [hu η hη, hu' η hη] with i hi hi'
  have hbound : cdfKolmogorov (νs i) (νs' i) ≤ 2 * η := by
    refine ciSup_le fun t ↦ ?_
    calc
      |cdf (νs i : Measure ℝ) t - cdf (νs' i : Measure ℝ) t| =
          dist (cdf (νs i : Measure ℝ) t) (cdf (νs' i : Measure ℝ) t) :=
        (Real.dist_eq _ _).symm
      _ ≤ dist (cdf (νs i : Measure ℝ) t) (cdf (ν : Measure ℝ) t) +
          dist (cdf (ν : Measure ℝ) t) (cdf (νs' i : Measure ℝ) t) := dist_triangle _ _ _
      _ = dist (cdf (ν : Measure ℝ) t) (cdf (νs i : Measure ℝ) t) +
          dist (cdf (ν : Measure ℝ) t) (cdf (νs' i : Measure ℝ) t) := by
        rw [dist_comm (cdf (νs i : Measure ℝ) t)]
      _ ≤ 2 * η := by linarith [hi t, hi' t]
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (cdfKolmogorov_nonneg _ _)]
  linarith

end Causalean.Stat
