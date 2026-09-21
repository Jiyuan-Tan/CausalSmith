module
public import Causalean.Stat.Quantile.CDFBand
public import Causalean.Stat.Quantile.EmpiricalQuantile

/-!
# Simultaneous quantile bands by CDF inversion

This module inverts a uniform empirical-CDF band through the lower generalized
inverse.  Its headline confidence band is data-computable: on every covered
sample path, the unknown population quantile at an interior level `τ` lies
between the sample quantiles at `τ - ε` and `τ + ε`.  The reverse inclusion of
the sample quantile between shifted population quantiles is retained as a
supporting lemma.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Causalean.Stat

open Quantile.VCMcDiarmid

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {P : Measure ℝ}

/-- Given [a population law](hyp:P), [a band radius](hyp:ε), and [a quantile
level](hyp:τ), the [supporting population-quantile band](goal) is the interval from the
population quantile at `τ - ε` to the population quantile at `τ + ε`. -/
noncomputable def populationQuantileBand (P : Measure ℝ) (ε : ℝ) (τ : ℝ) : Set ℝ :=
  Icc (quantile P (τ - ε)) (quantile P (τ + ε))

/-- Given [an i.i.d. real sample](hyp:S), [a band radius](hyp:ε), [a sample
size](hyp:n), [an outcome](hyp:ω), and [a quantile level](hyp:τ), the [data-computable
quantile confidence band](goal) is the interval between the sample quantiles at `τ - ε`
and `τ + ε`. -/
noncomputable def IIDSample.quantileBand (S : IIDSample Ω ℝ μ P) (ε : ℝ) (n : ℕ)
    (ω : Ω) (τ : ℝ) : Set ℝ :=
  Icc (S.sampleQuantile (τ - ε) n ω) (S.sampleQuantile (τ + ε) n ω)

/-- Given [an i.i.d. real sample](hyp:S), [a confidence level](hyp:α), and [a sample
size](hyp:n), the [simultaneous quantile-band coverage event](goal) consists of outcomes
whose data-computable band contains the population quantile at every level for which both
shifted sample-quantile levels are interior. -/
def IIDSample.quantileBandCoverageEvent (S : IIDSample Ω ℝ μ P)
    (α : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ τ : ℝ, 0 < τ - vcMcDiarmidRadius α n → τ + vcMcDiarmidRadius α n < 1 →
    quantile P τ ∈ S.quantileBand (vcMcDiarmidRadius α n) n ω τ}

/-- **Quantile-band inversion.** Given [an i.i.d. real sample](hyp:S), [a nonnegative
uniform-CDF radius](hyp:hε), [a positive sample size](hyp:hn), [an outcome](hyp:ω), and
[a quantile level whose lower and upper shifts are interior](hyp:hτ_lower,hτ_upper), if
[the population CDF lies in the radius-`ε` empirical band at every threshold](hyp:hband),
then [the sample quantile lies between the population quantiles at `τ - ε` and
`τ + ε`](goal).

This is the generalized-inverse confidence-band argument; it uses the switching relation
for `IIDSample.sampleQuantile` and requires neither continuity nor strict increase of the
population CDF. -/
theorem IIDSample.sampleQuantile_mem_populationQuantileBand_of_cdfBand
    (S : IIDSample Ω ℝ μ P) [IsProbabilityMeasure P]
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 0 < n) (ω : Ω) {τ : ℝ}
    (hτ_lower : 0 < τ - ε) (hτ_upper : τ + ε < 1)
    (hband : ∀ x : ℝ,
      cdf P x ∈ Icc (S.empiricalCDF x n ω - ε) (S.empiricalCDF x n ω + ε)) :
    S.sampleQuantile τ n ω ∈ populationQuantileBand P ε τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hτ_lower (by linarith)
  have hτ1 : τ < 1 := lt_of_le_of_lt (by linarith) hτ_upper
  let qhat := S.sampleQuantile τ n ω
  have hFn_qhat : τ ≤ S.empiricalCDF qhat n ω :=
    (S.sampleQuantile_le_iff hn ω hτ0 hτ1 qhat).mp le_rfl
  have hband_qhat := hband qhat
  have hpop_qhat : τ - ε ≤ cdf P qhat := by
    exact le_trans (by linarith [hFn_qhat]) hband_qhat.1
  have hlower : quantile P (τ - ε) ≤ qhat :=
    quantile_le_of_le_cdf hτ_lower hpop_qhat
  let qupper := quantile P (τ + ε)
  have hpop_upper : τ + ε ≤ cdf P qupper := le_cdf_quantile hτ_upper
  have hband_upper := hband qupper
  have hFn_upper : τ ≤ S.empiricalCDF qupper n ω := by
    linarith [hpop_upper, hband_upper.2]
  have hupper : qhat ≤ quantile P (τ + ε) := by
    change S.sampleQuantile τ n ω ≤ qupper
    exact (S.sampleQuantile_le_iff hn ω hτ0 hτ1 qupper).mpr hFn_upper
  exact ⟨hlower, hupper⟩

/-- **Data-computable quantile-band inversion.** Given [an i.i.d. real sample](hyp:S),
[a nonnegative uniform-CDF radius](hyp:hε), [a positive sample size](hyp:hn),
[an outcome](hyp:ω), and [a quantile level whose lower and upper shifts are
interior](hyp:hτ_lower,hτ_upper), if [the population CDF lies in the radius-`ε`
empirical band at every threshold](hyp:hband), then [the population quantile at `τ` lies
between the sample quantiles at `τ - ε` and `τ + ε`](goal).

This is the library's elementary generalized-inverse consequence of the assumed
uniform CDF band. Both endpoints are functions of the observed data. -/
theorem IIDSample.quantile_mem_quantileBand_of_cdfBand
    (S : IIDSample Ω ℝ μ P) [IsProbabilityMeasure P]
    {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 0 < n) (ω : Ω) {τ : ℝ}
    (hτ_lower : 0 < τ - ε) (hτ_upper : τ + ε < 1)
    (hband : ∀ x : ℝ,
      cdf P x ∈ Icc (S.empiricalCDF x n ω - ε) (S.empiricalCDF x n ω + ε)) :
    quantile P τ ∈ S.quantileBand ε n ω τ := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hτ_lower (by linarith)
  have hτ1 : τ < 1 := lt_of_le_of_lt (by linarith) hτ_upper
  let q := quantile P τ
  have hpop_q : τ ≤ cdf P q := le_cdf_quantile hτ1
  have hband_q := hband q
  have hemp_q : τ - ε ≤ S.empiricalCDF q n ω := by
    linarith [hpop_q, hband_q.2]
  have hlower : S.sampleQuantile (τ - ε) n ω ≤ q :=
    (S.sampleQuantile_le_iff hn ω hτ_lower (by linarith) q).mpr hemp_q
  let qhat := S.sampleQuantile (τ + ε) n ω
  have hemp_qhat : τ + ε ≤ S.empiricalCDF qhat n ω :=
    (S.sampleQuantile_le_iff hn ω (by linarith) hτ_upper qhat).mp le_rfl
  have hband_qhat := hband qhat
  have hpop_qhat : τ ≤ cdf P qhat := by
    linarith [hemp_qhat, hband_qhat.1]
  have hupper : q ≤ S.sampleQuantile (τ + ε) n ω := by
    change quantile P τ ≤ qhat
    exact quantile_le_of_le_cdf hτ0 hpop_qhat
  exact ⟨hlower, hupper⟩

/-- **Simultaneous data-computable quantile confidence band from VC--McDiarmid.** Given
[an i.i.d. real sample](hyp:S), [a positive sample size](hyp:hn), and [a confidence level
between zero and one](hyp:hα,hα_one), [with probability at least `1 - α`, every unknown
population quantile whose VC--McDiarmid-shifted level remains in `(0,1)` lies between the
corresponding lower and upper sample quantiles](goal).

This is the library's elementary generalized-inverse consequence of its formally
proved VC--McDiarmid CDF band, not the sharper DKW--Massart band. -/
theorem IIDSample.quantileBand_coverage (S : IIDSample Ω ℝ μ P)
    [IsProbabilityMeasure P] {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hα_one : α ≤ 1) :
    μ (S.quantileBandCoverageEvent α n) ≥ 1 - ENNReal.ofReal α := by
  have hCDF := S.cdfBand_coverage hn hα hα_one
  exact hCDF.trans (measure_mono fun ω hω => by
    intro τ hτ_lower hτ_upper
    apply S.quantile_mem_quantileBand_of_cdfBand
      (vcMcDiarmidRadius_nonneg α n) hn ω hτ_lower hτ_upper
    intro x
    have hx := hω x
    change cdf P x ∈ Icc
      (max 0 (S.empiricalCDF x n ω - vcMcDiarmidRadius α n))
      (min 1 (S.empiricalCDF x n ω + vcMcDiarmidRadius α n)) at hx
    exact ⟨(le_max_right _ _).trans hx.1, hx.2.trans (min_le_right _ _)⟩)

end Causalean.Stat
