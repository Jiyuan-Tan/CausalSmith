module

public import Causalean.Stat.Quantile.CdfConvergence
public import Causalean.Stat.Quantile.Quantile

/-!
# Stability of lower quantiles

This module proves deterministic stability of the library's generalized-inverse quantile at a
point where the limiting CDF is continuous and strictly increasing.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Topology
open scoped Topology

namespace Causalean.Stat

/-- A [real function](hyp:f) is [strictly increasing at a point](goal) when [every point to its
left has a smaller value](step:1) and [every point to its right has a larger value](step:2), for
the [specified point](hyp:q). -/
def StrictlyIncreasingAt (f : ℝ → ℝ) (q : ℝ) : Prop :=
  (∀ x, x < q → f x < f q) ∧ (∀ x, q < x → f q < f x)

/-- A [probability measure](hyp:μ) at [an interior probability level](hyp:hβ0,hβ1) whose CDF is
[continuous at its quantile](hyp:hcont) has [CDF value equal to that level at the quantile](goal). -/
theorem cdf_quantile_eq_of_continuousAt (μ : Measure ℝ) [IsProbabilityMeasure μ] {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcont : ContinuousAt (cdf μ) (quantile μ β)) :
    cdf μ (quantile μ β) = β := by
  -- The quantile membership lemma gives `β ≤ F(q)`.  If strict, continuity gives a point just
  -- left of `q` whose CDF is still at least `β`, contradicting the defining infimum/Galois law.
  apply le_antisymm
  · by_contra hle
    have hβq : β < cdf μ (quantile μ β) := lt_of_not_ge hle
    have hev : ∀ᶠ x in 𝓝 (quantile μ β), β < cdf μ x :=
      hcont.eventually_const_lt hβq
    obtain ⟨x, hxq, hβx⟩ :=
      ((frequently_lt_nhds (quantile μ β)).and_eventually hev).exists
    have hqx : quantile μ β ≤ x :=
      (Causalean.Stat.quantile_le_iff hβ0 hβ1).2 hβx.le
    exact (not_le_of_gt hxq) hqx
  · exact Causalean.Stat.le_cdf_quantile hβ1

/-- [An interior probability level](hyp:hβ0,hβ1), [a positive radius](hyp:hε), and eventual CDF
[brackets below](hyp:hleft) and [above](hyp:hright) that level imply [that the approximating
quantiles eventually lie in the corresponding closed neighborhood](goal). -/
theorem eventually_quantile_mem_of_bracket {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μs i)] {β q ε : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hε : 0 < ε)
    (hleft : ∀ᶠ i in l, cdf (μs i) (q - ε) < β)
    (hright : ∀ᶠ i in l, β < cdf (μs i) (q + ε)) :
    ∀ᶠ i in l, quantile (μs i) β ∈ Metric.closedBall q ε := by
  -- The two directions of `Causalean.Stat.quantile_le_iff` yield
  -- `q - ε < quantile ≤ q + ε`, which is exactly the claimed closed-ball bound.
  filter_upwards [hleft, hright] with i hi_left hi_right
  have hlo : q - ε < quantile (μs i) β := by
    by_contra h
    have hβleft : β ≤ cdf (μs i) (q - ε) :=
      (Causalean.Stat.quantile_le_iff hβ0 hβ1).1 (le_of_not_gt h)
    exact (not_le_of_gt hi_left) hβleft
  have hhi : quantile (μs i) β ≤ q + ε :=
    (Causalean.Stat.quantile_le_iff hβ0 hβ1).2 hi_right.le
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  constructor <;> linarith [hε]

/-- [Uniform CDF convergence](hyp:hunif) at [an interior probability level](hyp:hβ0,hβ1), with
[continuity](hyp:hcont) and [strict increase](hyp:hstrict) at the limiting quantile, implies
[convergence of the approximating quantiles](goal). -/
theorem tendsto_quantile_of_tendstoUniformly {ι : Type*} {l : Filter ι}
    {μs : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μs i)]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1)
    (hunif : TendstoUniformly (fun i ↦ cdf (μs i)) (cdf μ) l)
    (hcont : ContinuousAt (cdf μ) (quantile μ β))
    (hstrict : StrictlyIncreasingAt (cdf μ) (quantile μ β)) :
    Tendsto (fun i ↦ quantile (μs i) β) l (𝓝 (quantile μ β)) := by
  -- First identify `F(q)=β`.  At `q±ε/2`, strict increase gives positive CDF gaps around β;
  -- uniform convergence eventually preserves the bracket.  The bracket lemma then gives a
  -- closed ε/2 bound, hence membership in the requested open ε-ball.
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcdf : cdf μ (quantile μ β) = β :=
    cdf_quantile_eq_of_continuousAt μ hβ0 hβ1 hcont
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

/-- [Weak convergence of probability measures](hyp:hν) to a law with [a continuous CDF](hyp:hcont)
implies, at [an interior probability level](hyp:hβ0,hβ1) where the CDF is [strictly increasing at
its quantile](hyp:hstrict), [convergence of the approximating quantiles](goal). -/
theorem tendsto_quantile_of_tendsto {ι : Type*} {l : Filter ι}
    {νs : ι → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} {β : ℝ}
    (hν : Tendsto νs l (𝓝 ν)) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hcont : Continuous (cdf (ν : Measure ℝ)))
    (hstrict : StrictlyIncreasingAt (cdf (ν : Measure ℝ))
      (quantile (ν : Measure ℝ) β)) :
    Tendsto (fun i ↦ quantile (νs i : Measure ℝ) β) l
      (𝓝 (quantile (ν : Measure ℝ) β)) := by
  -- Combine Pólya's theorem with uniform quantile convergence.
  exact tendsto_quantile_of_tendstoUniformly hβ0 hβ1
    (tendstoUniformly_cdf_of_tendsto hν hcont) hcont.continuousAt hstrict

end Causalean.Stat
