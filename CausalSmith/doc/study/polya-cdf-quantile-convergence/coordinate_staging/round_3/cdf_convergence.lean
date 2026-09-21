module
public import Causalean.Mathlib.Probability.GaussianMoments
public import Causalean.Mathlib.Probability.StdNormalCDF
public import Causalean.Stat.Quantile.Quantile
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# CDF and quantile convergence

This module proves Pólya's theorem for real probability measures: weak convergence to a
continuous distribution function gives uniform CDF convergence. It then derives convergence of
the existing lower generalized-inverse `quantile`, and identifies the quantile of every centered
nondegenerate Gaussian by the standard-normal probit.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped Topology

namespace Causalean.Stat

/-- Given [a probability measure on the real line](hyp:μ), if [its cumulative distribution
function is continuous at a threshold](hyp:hcont), [the measure assigns zero probability to that
threshold](goal). -/
theorem measure_singleton_eq_zero_of_continuousAt_cdf (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {t : ℝ} (hcont : ContinuousAt (cdf μ) t) : μ {t} = 0 := by
  rw [← measure_cdf μ, StieltjesFunction.measure_singleton,
    hcont.continuousWithinAt.leftLim_eq, sub_self, ENNReal.ofReal_zero]

/-- Given [weak convergence of real probability measures](hyp:hν) and [continuity of the limit
CDF at a threshold](hyp:hcont), [the approximating CDF values converge at that threshold](goal). -/
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

/-- Given [a family of monotone functions](hyp:hF) whose values stay
[between zero and one](hyp:hF0,hF1), [a continuous monotone limit](hyp:hGmono,hGcont) with
[limits zero and one at the two tails](hyp:hGbot,hGtop), and [pointwise convergence to that
limit](hyp:hpoint), [the convergence is uniform on the real line](goal). -/
theorem tendstoUniformly_of_monotone_of_tendsto_at
    {ι : Type*} {l : Filter ι} {F : ι → ℝ → ℝ} {G : ℝ → ℝ}
    (hF : ∀ i, Monotone (F i)) (hF0 : ∀ i x, 0 ≤ F i x) (hF1 : ∀ i x, F i x ≤ 1)
    (hGmono : Monotone G) (hGcont : Continuous G)
    (hGbot : Tendsto G atBot (𝓝 0)) (hGtop : Tendsto G atTop (𝓝 1))
    (hpoint : ∀ t, Tendsto (fun i ↦ F i t) l (𝓝 (G t))) :
    TendstoUniformly F G l := by
  exact tendstoUniformly_of_monotone_of_tendsto_at_of_bounds
    hF hF0 hF1 hGmono hGcont hGbot hGtop hpoint

/-- **Pólya's theorem.** Given [weak convergence of real probability measures](hyp:hν) to a law
with [a continuous cumulative distribution function](hyp:hcont), [their CDFs converge uniformly
on the real line](goal). -/
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

/-- Given [two probability measures on the real line](hyp:μ,ν), [their Kolmogorov CDF
distance](goal) is [the supremum of absolute CDF differences over all real thresholds](step:1). -/
noncomputable def cdfKolmogorov (μ ν : ProbabilityMeasure ℝ) : ℝ :=
  ⨆ t : ℝ, |cdf (μ : Measure ℝ) t - cdf (ν : Measure ℝ) t|

/-- Given [two probability measures on the real line](hyp:μ,ν), [their Kolmogorov CDF distance
is nonnegative](goal). -/
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

/-- Given [two probability measures on the real line](hyp:μ,ν), [their Kolmogorov CDF distance
is at most one](goal). -/
theorem cdfKolmogorov_le_one (μ ν : ProbabilityMeasure ℝ) : cdfKolmogorov μ ν ≤ 1 := by
  refine ciSup_le fun t ↦ ?_
  rw [abs_le]
  constructor <;>
    linarith [cdf_nonneg (μ : Measure ℝ) t, cdf_le_one (μ : Measure ℝ) t,
      cdf_nonneg (ν : Measure ℝ) t, cdf_le_one (ν : Measure ℝ) t]

/-- Given [weak convergence of each of two families of real probability measures to the same
law](hyp:hν,hν') whose [CDF is continuous](hyp:hcont), [their Kolmogorov CDF distance
converges to zero](goal). -/
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

/-- Given [a real-valued function](hyp:f) and [a reference point](hyp:q), [strict increase at
that point](goal) means [every lower point has a smaller value](step:1) and [every higher point
has a larger value](step:2). -/
def StrictlyIncreasingAt (f : ℝ → ℝ) (q : ℝ) : Prop :=
  (∀ x, x < q → f x < f q) ∧ (∀ x, q < x → f q < f x)

/-- Given [a real probability measure](hyp:μ), [an interior quantile level](hyp:hβ0,hβ1), and
[continuity of its CDF at the lower quantile](hyp:hcont), [the CDF at that quantile equals the
requested level](goal). -/
theorem cdf_quantile_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcont : ContinuousAt (cdf μ) (quantile μ β)) :
    cdf μ (quantile μ β) = β := by
  apply le_antisymm
  · by_contra hle
    have hβq : β < cdf μ (quantile μ β) := lt_of_not_ge hle
    have hev : ∀ᶠ x in 𝓝 (quantile μ β), β < cdf μ x :=
      hcont.eventually_const_lt hβq
    obtain ⟨x, hxq, hβx⟩ :=
      ((frequently_lt_nhds (quantile μ β)).and_eventually hev).exists
    have hqx : quantile μ β ≤ x :=
      (quantile_le_iff hβ0 hβ1).2 hβx.le
    exact (not_le_of_gt hxq) hqx
  · exact le_cdf_quantile hβ1

/-- Given [a family of real probability measures](hyp:μs),
[an interior quantile level](hyp:hβ0,hβ1), [a positive radius](hyp:hε), and [eventual CDF
brackets below and above that level](hyp:hleft,hright), [the corresponding lower quantiles
eventually lie in the closed ball with that radius](goal). -/
theorem eventually_quantile_mem_of_bracket {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μs i)] {β q ε : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε)
    (hleft : ∀ᶠ i in l, cdf (μs i) (q - ε) < β)
    (hright : ∀ᶠ i in l, β < cdf (μs i) (q + ε)) :
    ∀ᶠ i in l, quantile (μs i) β ∈ Metric.closedBall q ε := by
  filter_upwards [hleft, hright] with i hi_left hi_right
  have hεnonneg : 0 ≤ ε := hε.le
  have hlo : q - ε < quantile (μs i) β := by
    by_contra h
    have hβleft : β ≤ cdf (μs i) (q - ε) :=
      (quantile_le_iff hβ0 hβ1).1 (le_of_not_gt h)
    exact (not_le_of_gt hi_left) hβleft
  have hhi : quantile (μs i) β ≤ q + ε :=
    (quantile_le_iff hβ0 hβ1).2 hi_right.le
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith [hεnonneg]

/-- Given [an interior quantile level](hyp:hβ0,hβ1),
[uniform convergence of approximating CDFs](hyp:hunif), [continuity of the limiting CDF at its
lower quantile](hyp:hcont), and [strict increase there](hyp:hstrict), [the lower quantiles
converge to the limiting lower quantile](goal). -/
theorem tendsto_quantile_of_tendstoUniformly {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μs i)]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hunif : TendstoUniformly (fun i ↦ cdf (μs i)) (cdf μ) l)
    (hcont : ContinuousAt (cdf μ) (quantile μ β))
    (hstrict : StrictlyIncreasingAt (cdf μ) (quantile μ β)) :
    Tendsto (fun i ↦ quantile (μs i) β) l (𝓝 (quantile μ β)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcdf : cdf μ (quantile μ β) = β :=
    cdf_quantile_eq μ hβ0 hβ1 hcont
  have hlimit_left : cdf μ (quantile μ β - ε / 2) < β := by
    have h := hstrict.1 (quantile μ β - ε / 2) (by linarith)
    simpa only [hcdf] using h
  have hlimit_right : β < cdf μ (quantile μ β + ε / 2) := by
    have h := hstrict.2 (quantile μ β + ε / 2) (by linarith)
    simpa only [hcdf] using h
  have hu := Metric.tendstoUniformly_iff.1 hunif
  have hleft : ∀ᶠ i in l,
      cdf (μs i) (quantile μ β - ε / 2) < β := by
    have hgap : 0 < β - cdf μ (quantile μ β - ε / 2) :=
      sub_pos.mpr hlimit_left
    filter_upwards [hu _ hgap] with i hi
    have hdist := hi (quantile μ β - ε / 2)
    rw [Real.dist_eq, abs_lt] at hdist
    linarith
  have hright : ∀ᶠ i in l,
      β < cdf (μs i) (quantile μ β + ε / 2) := by
    have hgap : 0 < cdf μ (quantile μ β + ε / 2) - β :=
      sub_pos.mpr hlimit_right
    filter_upwards [hu _ hgap] with i hi
    have hdist := hi (quantile μ β + ε / 2)
    rw [Real.dist_eq, abs_lt] at hdist
    linarith
  have hbracket := eventually_quantile_mem_of_bracket
    (μs := μs) hβ0 hβ1 (half_pos hε) hleft hright
  filter_upwards [hbracket] with i hi
  rw [Metric.mem_closedBall] at hi
  linarith

/-- Given [weak convergence of real probability measures](hyp:hν),
[an interior quantile level](hyp:hβ0,hβ1), [a continuous limit CDF](hyp:hcont), and [strict
increase of that CDF at its lower quantile](hyp:hstrict), [the lower quantiles converge](goal). -/
theorem tendsto_quantile_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} {β : ℝ}
    (hν : Tendsto νs l (𝓝 ν)) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcont : Continuous (cdf (ν : Measure ℝ)))
    (hstrict : StrictlyIncreasingAt (cdf (ν : Measure ℝ))
      (quantile (ν : Measure ℝ) β)) :
    Tendsto (fun i ↦ quantile (νs i : Measure ℝ) β) l
      (𝓝 (quantile (ν : Measure ℝ) β)) := by
  exact tendsto_quantile_of_tendstoUniformly hβ0 hβ1
    (tendstoUniformly_cdf_of_tendsto hν hcont) hcont.continuousAt hstrict

/-- Given [a positive Gaussian variance](hyp:hv) and [a real threshold](hyp:x), [the CDF of
the centered Gaussian is the standard-normal CDF at the threshold divided by its standard
deviation](goal). -/
theorem cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) (x : ℝ) :
    cdf (gaussianReal 0 v) x =
      Causalean.Mathlib.stdNormalCDF (x / Real.sqrt (v : ℝ)) := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  rw [cdf_eq_real, Causalean.Mathlib.gaussianReal_eq_map_std]
  rw [MeasureTheory.map_measureReal_apply
    (f := fun z : ℝ => Real.sqrt (v : ℝ) * z + 0)
    (continuous_const.mul continuous_id |>.add continuous_const).measurable measurableSet_Iic]
  rw [show (fun z : ℝ => Real.sqrt (v : ℝ) * z + 0) ⁻¹' Set.Iic x =
      Set.Iic (x / Real.sqrt (v : ℝ)) by
    ext z
    simp only [Set.mem_preimage, Set.mem_Iic, add_zero]
    simpa only [mul_comm] using
      (le_div_iff₀ hs : z ≤ x / Real.sqrt (v : ℝ) ↔
        z * Real.sqrt (v : ℝ) ≤ x).symm]
  rw [← cdf_eq_real]
  rfl

/-- Given [a positive Gaussian variance](hyp:hv), [the CDF of the centered Gaussian is
continuous](goal). -/
theorem continuous_cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) :
    Continuous (cdf (gaussianReal 0 v)) := by
  rw [show cdf (gaussianReal 0 v) =
      Causalean.Mathlib.stdNormalCDF ∘ (fun x : ℝ => x / Real.sqrt (v : ℝ)) by
    funext x
    exact cdf_gaussianReal_zero hv x]
  exact Causalean.Mathlib.stdNormalCDF_continuous.comp (continuous_id.div_const _)

/-- Given [a positive Gaussian variance](hyp:hv), [the CDF of the centered Gaussian is strictly
increasing](goal). -/
theorem strictMono_cdf_gaussianReal_zero {v : NNReal} (hv : 0 < v) :
    StrictMono (cdf (gaussianReal 0 v)) := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  rw [show cdf (gaussianReal 0 v) =
      Causalean.Mathlib.stdNormalCDF ∘ (fun x : ℝ => x / Real.sqrt (v : ℝ)) by
    funext x
    exact cdf_gaussianReal_zero hv x]
  exact Causalean.Mathlib.stdNormalCDF_strictMono.comp (strictMono_id.div_const hs)

/-- Given [a positive Gaussian variance](hyp:hv) and [an interior probability level](hyp:hβ0,hβ1),
[the centered Gaussian lower quantile is its standard deviation times the standard-normal
probit](goal). -/
theorem quantile_gaussianReal_zero {v : NNReal} (hv : 0 < v) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) :
    quantile (gaussianReal 0 v) β =
      Real.sqrt (v : ℝ) * Causalean.Mathlib.probit β := by
  have hvR : 0 < (v : ℝ) := by exact_mod_cast hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.2 hvR
  have hcont := continuous_cdf_gaussianReal_zero hv
  have hquant :
      cdf (gaussianReal 0 v) (quantile (gaussianReal 0 v) β) = β :=
    cdf_quantile_eq _ hβ0 hβ1 hcont.continuousAt
  have hcand :
      cdf (gaussianReal 0 v)
          (Real.sqrt (v : ℝ) * Causalean.Mathlib.probit β) = β := by
    rw [cdf_gaussianReal_zero hv]
    rw [mul_div_cancel_left₀ _ hs.ne']
    exact Causalean.Mathlib.stdNormalCDF_probit hβ0 hβ1
  exact (strictMono_cdf_gaussianReal_zero hv).injective (hquant.trans hcand.symm)

end Causalean.Stat
