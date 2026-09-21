module

public import Causalean.Stat.Bootstrap.EfronResampling.MeanCLT.Basic
public import Causalean.Stat.Limit.WLLN
public import Mathlib.Probability.StrongLaw

/-!
# Almost-sure empirical conditions for the bootstrap mean CLT

This module derives the almost-sure convergence of the empirical mean and variance and the
Lindeberg tail condition using only a finite second moment.  The tail argument is organized
around the measurable squared-tail truncation below, so no moment above order two is assumed.
-/

@[expose] public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- For [an observation statistic](hyp:ψ), [a threshold](hyp:M), and [an observation](hyp:x),
[the squared tail](goal) is [the statistic's square retained only when its absolute value
exceeds the threshold](step:1). -/
def squaredTail (ψ : X → ℝ) (M : ℝ) (x : X) : ℝ :=
  (ψ x) ^ 2 * Set.indicator {y : X | M ≤ |ψ y|} (fun _ ↦ (1 : ℝ)) x

/-- For [an observation statistic](hyp:ψ), [its measurability](hyp:hψ), and [a finite population
second moment](hyp:hψ2), [the population expectations of its squared tails converge to zero as
the threshold diverges](goal). -/
theorem integral_squaredTail_tendsto_zero
    (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    Tendsto (fun M : ℝ ↦ ∫ x, squaredTail ψ M x ∂P) atTop (𝓝 0) := by
  have hmeas : ∀ M : ℝ, AEStronglyMeasurable (squaredTail ψ M) P := by
    intro M
    exact ((hψ.pow_const 2).mul
      (measurable_const.indicator (measurableSet_le measurable_const hψ.abs))).aestronglyMeasurable
  have hbound : ∀ M : ℝ, ∀ᵐ x ∂P, ‖squaredTail ψ M x‖ ≤ (ψ x) ^ 2 := by
    intro M
    filter_upwards with x
    by_cases hx : M ≤ |ψ x|
    · simp [squaredTail, hx]
    · simp [squaredTail, hx, sq_nonneg]
  have hpoint : ∀ᵐ x ∂P,
      Tendsto (fun M : ℝ ↦ squaredTail ψ M x) atTop (𝓝 0) := by
    filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop |ψ x|] with M hM
    simp [squaredTail, not_le.mpr hM]
  simpa using
    (tendsto_integral_filter_of_dominated_convergence
      (fun x ↦ (ψ x) ^ 2) (Eventually.of_forall hmeas)
      (Eventually.of_forall hbound) hψ2 hpoint)

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [the transformed sample mean converges almost
surely to its population mean](goal). -/
theorem sampleMean_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ S.sampleMean ψ n ω) atTop (𝓝 (∫ x, ψ x ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hmem : MemLp ψ 2 P :=
    (memLp_two_iff_integrable_sq hψ.aestronglyMeasurable).2 hψ2
  have hψint : Integrable ψ P := hmem.integrable (by norm_num)
  have hψint_sample : Integrable (fun ω ↦ ψ (S.Z 0 ω)) μ := by
    have hmap : Integrable ψ (μ.map (S.Z 0)) := by simpa [S.law] using hψint
    exact hmap.comp_measurable (S.meas 0)
  have hindep : Pairwise (Function.onFun (fun f g ↦ IndepFun f g μ)
      (fun i ω ↦ ψ (S.Z i ω))) := by
    have hi : iIndepFun (fun i ↦ ψ ∘ S.Z i) μ :=
      S.indep.comp (fun _ ↦ ψ) (fun _ ↦ hψ)
    intro i j hij
    exact hi.indepFun hij
  have hident : ∀ i, IdentDistrib (fun ω ↦ ψ (S.Z i ω))
      (fun ω ↦ ψ (S.Z 0 ω)) μ μ := by
    intro i
    exact ((S.identDist i).symm.comp hψ)
  have hslln := strong_law_ae_real
    (fun i ω ↦ ψ (S.Z i ω)) hψint_sample hindep hident
  have hint : (∫ ω, ψ (S.Z 0 ω) ∂μ) = ∫ x, ψ x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hψ.aestronglyMeasurable, S.law]
  filter_upwards [hslln] with ω hω
  unfold IIDSample.sampleMean
  simpa [hint, div_eq_mul_inv, mul_comm] using hω

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [the empirical second moment converges almost
surely to the population second moment](goal). -/
theorem sampleSecondMoment_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ S.sampleMean (fun x ↦ (ψ x) ^ 2) n ω) atTop
        (𝓝 (∫ x, (ψ x) ^ 2 ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let g : X → ℝ := fun x ↦ (ψ x) ^ 2
  have hg : Measurable g := hψ.pow_const 2
  have hg_sample : Integrable (fun ω ↦ g (S.Z 0 ω)) μ := by
    have hmap : Integrable g (μ.map (S.Z 0)) := by simpa [S.law, g] using hψ2
    exact hmap.comp_measurable (S.meas 0)
  have hindep : Pairwise (Function.onFun (fun f₁ f₂ ↦ IndepFun f₁ f₂ μ)
      (fun i ω ↦ g (S.Z i ω))) := by
    have hi : iIndepFun (fun i ↦ g ∘ S.Z i) μ :=
      S.indep.comp (fun _ ↦ g) (fun _ ↦ hg)
    intro i j hij
    exact hi.indepFun hij
  have hident : ∀ i, IdentDistrib (fun ω ↦ g (S.Z i ω))
      (fun ω ↦ g (S.Z 0 ω)) μ μ := by
    intro i
    exact ((S.identDist i).symm.comp hg)
  have hslln := strong_law_ae_real
    (fun i ω ↦ g (S.Z i ω)) hg_sample hindep hident
  have hint : (∫ ω, g (S.Z 0 ω) ∂μ) = ∫ x, g x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hg.aestronglyMeasurable, S.law]
  filter_upwards [hslln] with ω hω
  unfold IIDSample.sampleMean
  simpa [g, hint, div_eq_mul_inv, mul_comm] using hω

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [one common almost-sure event supports
strong-law convergence for every integer squared-tail truncation](goal). -/
theorem sampleSquaredTail_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ, ∀ M : ℕ,
      Tendsto (fun n ↦ S.sampleMean (squaredTail ψ M) n ω) atTop
        (𝓝 (∫ x, squaredTail ψ M x ∂P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  rw [ae_all_iff]
  intro M
  let g : X → ℝ := squaredTail ψ M
  have hg : Measurable g := by
    dsimp [g, squaredTail]
    exact (hψ.pow_const 2).mul
      (measurable_const.indicator (measurableSet_le measurable_const hψ.abs))
  have hgint : Integrable g P := by
    refine Integrable.mono hψ2 hg.aestronglyMeasurable ?_
    filter_upwards with x
    by_cases hx : (M : ℝ) ≤ |ψ x|
    · simp [g, squaredTail, hx]
    · simp [g, squaredTail, hx, sq_nonneg]
  have hg_sample : Integrable (fun ω ↦ g (S.Z 0 ω)) μ := by
    have hmap : Integrable g (μ.map (S.Z 0)) := by simpa [S.law] using hgint
    exact hmap.comp_measurable (S.meas 0)
  have hindep : Pairwise (Function.onFun (fun f₁ f₂ ↦ IndepFun f₁ f₂ μ)
      (fun i ω ↦ g (S.Z i ω))) := by
    have hi : iIndepFun (fun i ↦ g ∘ S.Z i) μ :=
      S.indep.comp (fun _ ↦ g) (fun _ ↦ hg)
    intro i j hij
    exact hi.indepFun hij
  have hident : ∀ i, IdentDistrib (fun ω ↦ g (S.Z i ω))
      (fun ω ↦ g (S.Z 0 ω)) μ μ := by
    intro i
    exact ((S.identDist i).symm.comp hg)
  have hslln := strong_law_ae_real
    (fun i ω ↦ g (S.Z i ω)) hg_sample hindep hident
  have hint : (∫ ω, g (S.Z 0 ω) ∂μ) = ∫ x, g x ∂P := by
    rw [← integral_map (S.meas 0).aemeasurable hg.aestronglyMeasurable, S.law]
  filter_upwards [hslln] with ω hω
  unfold IIDSample.sampleMean
  simpa [g, hint, div_eq_mul_inv, mul_comm] using hω

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [the plug-in empirical variance converges
almost surely to the population variance](goal). -/
theorem empiricalVar_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ S.empiricalVar ψ n ω) atTop
        (𝓝 (ProbabilityTheory.variance ψ P)) := by
  haveI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  haveI : IsProbabilityMeasure P := by
    rw [← S.law]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  have hmem : MemLp ψ 2 P :=
    (memLp_two_iff_integrable_sq hψ.aestronglyMeasurable).2 hψ2
  filter_upwards [sampleMean_tendsto_ae S ψ hψ hψ2,
    sampleSecondMoment_tendsto_ae S ψ hψ hψ2] with ω hmean hsecond
  rw [variance_eq_sub hmem]
  exact hsecond.sub (hmean.pow 2)

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [the centered empirical row's second moment
converges almost surely to the population variance](goal). -/
theorem centeredEmpiricalSecondMoment_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun n ↦ ∫ y, y ^ 2 ∂centeredEmpiricalLaw S ψ n ω)
        atTop (𝓝 (ProbabilityTheory.variance ψ P)) := by
  filter_upwards [empiricalVar_tendsto_ae S ψ hψ hψ2] with ω hvar
  apply hvar.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (integral_sq_centeredEmpiricalLaw_eq_empiricalVar hn S ψ hψ ω).symm

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a finite population second moment](hyp:hψ2), [each positive Lindeberg threshold has a
centered empirical second-moment tail that vanishes almost surely at the square-root sample-size
scale](goal). -/
theorem centeredEmpiricalLindeberg_tendsto_ae
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (hψ2 : Integrable (fun x ↦ (ψ x) ^ 2) P) :
    ∀ᵐ ω ∂μ, ∀ ε : ℝ, 0 < ε →
      Tendsto
        (fun n ↦ ∫ y in {y : ℝ | ε * Real.sqrt (n : ℝ) ≤ |y|}, y ^ 2
          ∂centeredEmpiricalLaw S ψ n ω)
        atTop (𝓝 0) := by
  filter_upwards [sampleMean_tendsto_ae S ψ hψ hψ2,
    sampleSquaredTail_tendsto_ae S ψ hψ hψ2] with ω hmean htails
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with n
    exact lt_of_lt_of_le ha (setIntegral_nonneg
      (measurableSet_le measurable_const measurable_id.abs) (fun _ _ ↦ sq_nonneg _))
  · intro δ hδ
    have htailNat : Tendsto
        (fun M : ℕ ↦ 4 * ∫ x, squaredTail ψ (M : ℝ) x ∂P) atTop (𝓝 0) := by
      convert ((integral_squaredTail_tendsto_zero ψ hψ hψ2).const_mul 4).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)) using 1 <;>
        simp [Function.comp_def]
    have hsmallEventually : ∀ᶠ M : ℕ in atTop,
        4 * ∫ x, squaredTail ψ (M : ℝ) x ∂P < δ :=
      htailNat.eventually (eventually_lt_nhds hδ)
    rcases eventually_atTop.1 hsmallEventually with ⟨M, hM⟩
    have hMsmall : 4 * ∫ x, squaredTail ψ (M : ℝ) x ∂P < δ := hM M le_rfl
    have hmeanBound : ∀ᶠ n : ℕ in atTop,
        |S.sampleMean ψ n ω| < |∫ x, ψ x ∂P| + 1 :=
      hmean.abs.eventually (eventually_lt_nhds (lt_add_one _))
    have hroot : Tendsto (fun n : ℕ ↦ ε * Real.sqrt (n : ℝ)) atTop atTop :=
      (Real.tendsto_sqrt_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hε
    have hthreshold : ∀ᶠ n : ℕ in atTop,
        2 * ((M : ℝ) + (|∫ x, ψ x ∂P| + 1)) ≤ ε * Real.sqrt (n : ℝ) :=
      hroot.eventually (eventually_ge_atTop _)
    have htailSmall : ∀ᶠ n : ℕ in atTop,
        4 * S.sampleMean (squaredTail ψ M) n ω < δ :=
      (htails M).const_mul 4 |>.eventually (eventually_lt_nhds hMsmall)
    filter_upwards [hmeanBound, hthreshold, htailSmall, eventually_ne_atTop 0]
      with n hnmean hnthreshold hntail hn
    have hthreshold' :
        2 * ((M : ℝ) + |S.sampleMean ψ n ω|) ≤ ε * Real.sqrt (n : ℝ) := by
      linarith
    have hdom :
        (∫ y in {y : ℝ | ε * Real.sqrt (n : ℝ) ≤ |y|}, y ^ 2
          ∂centeredEmpiricalLaw S ψ n ω) ≤
          4 * S.sampleMean (squaredTail ψ M) n ω := by
      have hA : MeasurableSet {y : ℝ | ε * Real.sqrt (n : ℝ) ≤ |y|} := by
        exact measurableSet_le measurable_const measurable_id.abs
      rw [setIntegral_sq_centeredEmpiricalLaw_eq_average hn S ψ ω
        (A := {y : ℝ | ε * Real.sqrt (n : ℝ) ≤ |y|}) hA]
      unfold IIDSample.sampleMean
      rw [← Fin.sum_univ_eq_sum_range
        (fun i ↦ squaredTail ψ M (S.Z i ω)) n]
      calc
        (n : ℝ)⁻¹ * ∑ i : Fin n,
            Set.indicator {y : ℝ | ε * Real.sqrt (n : ℝ) ≤ |y|}
              (fun y : ℝ ↦ y ^ 2) (ψ (S.Z i ω) - S.sampleMean ψ n ω)
            ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, 4 * squaredTail ψ M (S.Z i ω) := by
              apply mul_le_mul_of_nonneg_left
                (Finset.sum_le_sum fun i _ ↦ ?_) (by positivity)
              let x := ψ (S.Z i ω)
              let m := S.sampleMean ψ n ω
              by_cases hc : ε * Real.sqrt (n : ℝ) ≤ |x - m|
              · have hbig : 2 * ((M : ℝ) + |m|) ≤ |x - m| :=
                  hthreshold'.trans hc
                have htri : |x - m| ≤ |x| + |m| := abs_sub x m
                have haux : 2 * ((M : ℝ) + |m|) ≤ |x| + |m| :=
                  hbig.trans htri
                have hm_le : |m| ≤ |x| := by
                  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
                  linarith [abs_nonneg m]
                have hM_le : (M : ℝ) ≤ |x| := by
                  have hMnonneg : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
                  linarith [abs_nonneg m]
                have habs : |x - m| ≤ 2 * |x| := by linarith
                have hsquares : (x - m) ^ 2 ≤ 4 * x ^ 2 := by
                  have hs := (sq_le_sq₀ (abs_nonneg (x - m))
                    (by positivity : 0 ≤ 2 * |x|)).2 habs
                  rw [sq_abs] at hs
                  nlinarith [sq_abs x]
                simpa [x, m, squaredTail, hc, hM_le] using hsquares
              · by_cases ht : (M : ℝ) ≤ |x|
                · simp [x, m, squaredTail, hc, ht, sq_nonneg]
                · simp [x, m, squaredTail, hc, ht]
        _ = 4 * ((n : ℝ)⁻¹ * ∑ i : Fin n,
            squaredTail ψ M (S.Z i ω)) := by
              rw [← Finset.mul_sum]
              ring
    exact lt_of_le_of_lt hdom hntail

end

end Causalean.Stat
