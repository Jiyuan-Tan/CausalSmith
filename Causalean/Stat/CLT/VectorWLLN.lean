/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Limit.ContinuousMapping
public import Causalean.Stat.Sample
public import Mathlib.Probability.StrongLaw

/-! # Banach-valued weak laws for iid sample means

This module extends the scalar weak law to integrable statistics taking values
in a separable Banach space.  It packages the normalized finite sum, proves its
measurability, derives convergence in measure from the Banach-valued strong
law, and records the corresponding `o_p(1)` norm statement used for empirical
Jacobian averages.
-/

@[expose] public section

namespace Causalean.Stat

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

variable {Ω X F : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {μ : Measure Ω} {P : Measure X}

namespace IIDSample

/-- For [an iid sample](hyp:S) and [a Banach-valued statistic](hyp:g), the
[vector sample mean](goal) is the normalized sum over the first `n` observations. -/
def sampleMeanVec (S : IIDSample Ω X μ P) (g : X → F) : ℕ → Ω → F :=
  fun n ω => (n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, g (S.Z i ω)

omit [CompleteSpace F] in
/-- For [an iid sample](hyp:S) and [a Banach-valued statistic](hyp:g) with [a
measurability witness](hyp:hg_meas), at each [sample size](hyp:n), [the vector
sample mean is measurable](goal). -/
@[fun_prop]
theorem measurable_sampleMeanVec (S : IIDSample Ω X μ P) {g : X → F}
    (hg_meas : Measurable g) (n : ℕ) :
    Measurable (S.sampleMeanVec g n) := by
  unfold sampleMeanVec
  exact (Finset.measurable_sum _ (fun i _ => hg_meas.comp (S.meas i))).const_smul _

/-- **Banach-valued weak law of large numbers.** For [an iid sample](hyp:S), if
[a Banach-valued statistic](hyp:g) is [measurable](hyp:hg_meas) and [integrable
under the population law](hyp:hg_int), then [its vector sample mean converges
in measure to its population mean](goal). -/
theorem sampleMeanVec_tendstoInMeasure
    (S : IIDSample Ω X μ P) {g : X → F}
    (hg_meas : Measurable g) (hg_int : Integrable g P) :
    TendstoInMeasure μ (S.sampleMeanVec g) atTop
      (fun _ => ∫ x, g x ∂P) := by
  have : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  have hg_int_sample : Integrable (fun ω => g (S.Z 0 ω)) μ := by
    have hg_int_map : Integrable g (μ.map (S.Z 0)) := by
      simpa [S.law] using hg_int
    exact hg_int_map.comp_measurable (S.meas 0)
  have hindep_iid :
      Pairwise (Function.onFun (fun x₁ x₂ => IndepFun x₁ x₂ μ)
        (fun i ω => g (S.Z i ω))) := by
    have hi : iIndepFun (fun i => g ∘ S.Z i) μ :=
      S.indep.comp (fun _ => g) (fun _ => hg_meas)
    intro i j hij
    exact hi.indepFun hij
  have hident :
      ∀ i, IdentDistrib (fun ω => g (S.Z i ω)) (fun ω => g (S.Z 0 ω)) μ μ := by
    intro i
    exact ((S.identDist i).symm.comp hg_meas)
  have hslln := ProbabilityTheory.strong_law_ae
    (fun i ω => g (S.Z i ω)) hg_int_sample hindep_iid hident
  have hint_eq : (∫ ω, g (S.Z 0 ω) ∂μ) = ∫ x, g x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hg_meas.aestronglyMeasurable, S.law]
  have hae : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => S.sampleMeanVec g n ω) atTop
        (𝓝 (∫ x, g x ∂P)) := by
    filter_upwards [hslln] with ω hω
    simpa [sampleMeanVec, hint_eq] using hω
  exact tendstoInMeasure_of_tendsto_ae
    (fun n => (S.measurable_sampleMeanVec hg_meas n).aestronglyMeasurable) hae

/-- For [an iid sample](hyp:S), if [a Banach-valued statistic](hyp:g) is
[measurable](hyp:hg_meas) and [integrable](hyp:hg_int), then [the norm of its
vector sample mean minus its population mean is `o_p(1)`](goal). -/
theorem sampleMeanVec_norm_sub_isLittleOp
    (S : IIDSample Ω X μ P) {g : X → F}
    (hg_meas : Measurable g) (hg_int : Integrable g P) :
    IsLittleOp
      (fun n ω => ‖S.sampleMeanVec g n ω - ∫ x, g x ∂P‖)
      (fun _ => (1 : ℝ)) μ := by
  have hvec := S.sampleMeanVec_tendstoInMeasure hg_meas hg_int
  have hprob : Tendsto_inProb
      (fun n ω => ‖S.sampleMeanVec g n ω - ∫ x, g x ∂P‖)
      (fun _ => 0) μ := by
    rw [Tendsto_inProb_iff]
    rw [tendstoInMeasure_iff_norm] at hvec ⊢
    simpa [Real.norm_eq_abs, abs_of_nonneg] using hvec
  exact hprob.isLittleOp_one

end IIDSample

end

end Causalean.Stat
