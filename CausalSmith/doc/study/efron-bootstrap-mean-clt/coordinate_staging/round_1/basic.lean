module

public import Causalean.Stat.Bootstrap.EfronResampling.Basic
public import Causalean.Stat.Bootstrap.EfronResampling.Moments
public import Causalean.Stat.CLT.Lindeberg
public import Causalean.Stat.CLT.SampleFnEstimator
public import Causalean.Stat.Inference.VarianceEstimation

/-!
# Laws used in the Efron bootstrap CLT for a mean

This module defines the centered empirical row law, the conditional bootstrap law of the
root-sample-size mean, and the corresponding true sampling law.  The definitions are totalized
at sample size zero by a point mass at zero; every theorem identifying them with Efron's literal
bootstrap law assumes the genuine case `n ≠ 0`.
-/

@[expose] public section

namespace Causalean.Stat

open Causalean.Stat Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators ENNReal NNReal Topology

noncomputable section

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {μ : Measure Ω} {P : Measure X}

/-- For [an observation statistic](hyp:ψ), [observed data](hyp:x), and [a resample](hyp:xstar),
[the centered normalized bootstrap sum](goal) is [the resampled statistic sum after subtracting
the data mean and dividing by the square root of the sample size](step:1). -/
def centeredBootstrapSum {n : ℕ} (ψ : X → ℝ) (x xstar : Fin n → X) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i, (ψ (xstar i) - Causalean.Stat.finAverage (fun j ↦ ψ (x j)))

/-- With [a nonzero sample size](hyp:hn), [an observation statistic](hyp:ψ), [observed data](hyp:x),
and [a resample](hyp:xstar), [the normalized centered sum equals square-root sample size times
the difference of the resample and data averages](goal). -/
theorem centeredBootstrapSum_eq_sqrt_mul_finAverage_sub {n : ℕ} (hn : n ≠ 0)
    (ψ : X → ℝ) (x xstar : Fin n → X) :
    centeredBootstrapSum ψ x xstar = Real.sqrt (n : ℝ) *
      (Causalean.Stat.finAverage (fun i ↦ ψ (xstar i)) -
        Causalean.Stat.finAverage (fun i ↦ ψ (x i))) := by
  -- Expand both finite averages and `Finset.sum_sub_distrib`; use `Real.sq_sqrt` and `hn` to
  -- rewrite `√n / n` as `(√n)⁻¹`.
  unfold centeredBootstrapSum Causalean.Stat.finAverage
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg n)]

/-- For [an observation statistic](hyp:ψ), [its measurability](hyp:hψ), and [observed data](hyp:x),
[the centered normalized bootstrap sum is measurable as a function of the resample](goal). -/
theorem measurable_centeredBootstrapSum {n : ℕ} (ψ : X → ℝ) (hψ : Measurable ψ)
    (x : Fin n → X) : Measurable (centeredBootstrapSum ψ x) := by
  unfold centeredBootstrapSum
  fun_prop

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [a row index](hyp:n), and
[an outcome](hyp:ω), [the centered empirical row law](goal) is [the point mass at zero for the
zero row and otherwise the empirical law of transformed observations centered at their sample
mean](step:1). -/
def centeredEmpiricalLaw (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) (ω : Ω) : Measure ℝ :=
  if n = 0 then Measure.dirac 0
  else Causalean.Stat.empiricalMeasure
    (fun i : Fin n ↦ ψ (S.Z i ω) - S.sampleMean ψ n ω)

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [a row index](hyp:n), and
[an outcome](hyp:ω), [the centered empirical row law has total mass one](goal). -/
theorem centeredEmpiricalLaw_isProbabilityMeasure
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (centeredEmpiricalLaw S ψ n ω) := by
  -- Split on `n = 0`; use the dirac instance in the zero branch and
  -- `empiricalMeasure_isProbabilityMeasure` otherwise.
  by_cases hn : n = 0
  · subst n
    rw [centeredEmpiricalLaw, if_pos rfl]
    exact Measure.dirac.isProbabilityMeasure
  · rw [centeredEmpiricalLaw, if_neg hn]
    exact Causalean.Stat.empiricalMeasure_isProbabilityMeasure _ hn

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [a row index](hyp:n), and
[an outcome](hyp:ω), [the centered empirical row law carries its probability-measure instance](goal),
given by [the corresponding total-mass-one theorem](step:1). -/
instance centeredEmpiricalLaw.instIsProbabilityMeasure
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) (ω : Ω) :
    IsProbabilityMeasure (centeredEmpiricalLaw S ψ n ω) :=
  centeredEmpiricalLaw_isProbabilityMeasure S ψ n ω

/-- With [a nonzero row length](hyp:hn), [an iid sample](hyp:S), [an observation statistic](hyp:ψ),
and [an outcome](hyp:ω), [the centered empirical row law has mean zero](goal). -/
theorem integral_id_centeredEmpiricalLaw {n : ℕ} (hn : n ≠ 0)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (ω : Ω) :
    ∫ y, y ∂centeredEmpiricalLaw S ψ n ω = 0 := by
  -- Reduce the empirical integral to its finite average and cancel the sample mean.
  rw [centeredEmpiricalLaw, if_neg hn]
  unfold Causalean.Stat.empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    (f := fun y : ℝ ↦ y) _ (Nat.pos_of_ne_zero hn) measurable_id]
  unfold IIDSample.sampleMean
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsum : (∑ i : Fin n, ψ (S.Z i ω)) =
      ∑ i ∈ Finset.range n, ψ (S.Z i ω) :=
    Fin.sum_univ_eq_sum_range (fun i ↦ ψ (S.Z i ω)) n
  rw [hsum]
  field_simp
  ring

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [a row index](hyp:n), and
[an outcome](hyp:ω), [the identity has a finite second moment under the centered empirical row
law](goal). -/
theorem memLp_id_centeredEmpiricalLaw
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (n : ℕ) (ω : Ω) :
    MemLp id 2 (centeredEmpiricalLaw S ψ n ω) := by
  -- Both branches have finite support; unfold the empirical measure into its finite sum of
  -- dirac masses and use `memLp_finsetSum_measure`/the corresponding integrability criterion.
  rw [centeredEmpiricalLaw]
  split_ifs with hn
  · refine (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 ?_
    exact integrable_dirac' (stronglyMeasurable_id.pow 2) (by simp)
  · refine (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 ?_
    unfold Causalean.Stat.empiricalMeasure
      Causalean.Stat.Concentration.finiteSampleMeasure
    apply Integrable.smul_measure
    · rw [integrable_finsetSum_measure]
      intro i hi
      exact integrable_dirac' (stronglyMeasurable_id.pow 2) (by simp)
    · simp [hn]

/-- With [a nonzero row length](hyp:hn), [an iid sample](hyp:S), [an observation statistic](hyp:ψ),
[its measurability](hyp:hψ), and [an outcome](hyp:ω), [the centered empirical row's second
moment equals the plug-in empirical variance](goal). -/
theorem integral_sq_centeredEmpiricalLaw_eq_empiricalVar {n : ℕ} (hn : n ≠ 0)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ) (ω : Ω) :
    ∫ y, y ^ 2 ∂centeredEmpiricalLaw S ψ n ω = S.empiricalVar ψ n ω := by
  -- Unfold the nonzero row and use the finite empirical integral formula, then
  -- `IIDSample.empiricalVar_eq_centered`.
  rw [centeredEmpiricalLaw, if_neg hn]
  unfold Causalean.Stat.empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    (f := fun y : ℝ ↦ y ^ 2) _ (Nat.pos_of_ne_zero hn)
    (measurable_id.pow_const 2)]
  rw [IIDSample.empiricalVar_eq_centered]
  rw [Fin.sum_univ_eq_sum_range
    (fun i ↦ (ψ (S.Z i ω) - S.sampleMean ψ n ω) ^ 2) n]
  simp only [one_div]

/-- With [a nonzero row length](hyp:hn), [an iid sample](hyp:S), [an observation statistic](hyp:ψ),
[an outcome](hyp:ω), [a measurable set of values](hyp:A,hA), [the centered row's restricted
second moment equals its finite empirical average](goal). -/
theorem setIntegral_sq_centeredEmpiricalLaw_eq_average {n : ℕ} (hn : n ≠ 0)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (ω : Ω) (A : Set ℝ)
    (hA : MeasurableSet A) :
    ∫ y in A, y ^ 2 ∂centeredEmpiricalLaw S ψ n ω =
      (n : ℝ)⁻¹ * ∑ i : Fin n,
        Set.indicator A (fun y : ℝ ↦ y ^ 2)
          (ψ (S.Z i ω) - S.sampleMean ψ n ω) := by
  -- Write the set integral as the integral of an indicator and apply
  -- `Concentration.integral_finiteSampleMeasure`.
  rw [centeredEmpiricalLaw, if_neg hn]
  rw [← integral_indicator hA]
  unfold Causalean.Stat.empiricalMeasure
  rw [Causalean.Stat.Concentration.integral_finiteSampleMeasure
    (f := Set.indicator A (fun y : ℝ ↦ y ^ 2)) _
    (Nat.pos_of_ne_zero hn) ((measurable_id.pow_const 2).indicator hA)]
  simp only [one_div]

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
[a row index](hyp:n), and [an outcome](hyp:ω), [the conditional bootstrap law of the centered
normalized mean](goal) is [the point mass at zero for a zero row and otherwise the Efron
bootstrap pushforward](step:1). -/
def bootstrapMeanLaw (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (n : ℕ) (ω : Ω) : ProbabilityMeasure ℝ :=
  if hn : n = 0 then ⟨Measure.dirac 0, inferInstance⟩
  else
    ⟨Causalean.Stat.bootstrapLaw
        (centeredBootstrapSum ψ (S.sampleVector n ω)) (S.sampleVector n ω),
      Causalean.Stat.bootstrapLaw_isProbabilityMeasure _ _ hn
        (measurable_centeredBootstrapSum ψ hψ _)⟩

/-- With [a nonzero row length](hyp:hn), [an iid sample](hyp:S), [an observation statistic](hyp:ψ),
[its measurability](hyp:hψ), and [an outcome](hyp:ω), [the conditional mean-bootstrap law is
the underlying Efron bootstrap measure](goal). -/
theorem bootstrapMeanLaw_toMeasure {n : ℕ} (hn : n ≠ 0)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ) (ω : Ω) :
    (bootstrapMeanLaw S ψ hψ n ω : Measure ℝ) =
      Causalean.Stat.bootstrapLaw
        (centeredBootstrapSum ψ (S.sampleVector n ω)) (S.sampleVector n ω) := by
  -- Unfold `bootstrapMeanLaw`; the nonzero branch reduces definitionally.
  simp [bootstrapMeanLaw, hn]

/-- With [a nonzero row length](hyp:hn), [an iid sample](hyp:S), [an observation statistic](hyp:ψ),
[its measurability](hyp:hψ), and [an outcome](hyp:ω), [the conditional bootstrap mean law is
the normalized iid row-sum law of the centered empirical distribution](goal). -/
theorem bootstrapMeanLaw_eq_iidRowNormalizedSumLaw {n : ℕ} (hn : n ≠ 0)
    (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ) (ω : Ω) :
    bootstrapMeanLaw S ψ hψ n ω =
      Causalean.Stat.iidRowNormalizedSumLaw
        (fun m ↦ centeredEmpiricalLaw S ψ m ω) n := by
  -- Push each empirical draw through subtraction of the fixed sample mean, commute this
  -- coordinatewise map with `Measure.pi`, and finish with `Measure.map_map` and extensionality.
  apply ProbabilityMeasure.toMeasure_injective
  rw [bootstrapMeanLaw_toMeasure hn]
  change
    Causalean.Stat.bootstrapLaw
        (centeredBootstrapSum ψ (S.sampleVector n ω)) (S.sampleVector n ω) =
      (Measure.pi (fun _ : Fin n => centeredEmpiricalLaw S ψ n ω)).map
        (fun y => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y)
  rw [centeredEmpiricalLaw, if_neg hn]
  let g : X → ℝ := fun z => ψ z - S.sampleMean ψ n ω
  have hg : Measurable g := hψ.sub measurable_const
  have hemp :
      Causalean.Stat.empiricalMeasure
          (fun i : Fin n => g (S.sampleVector n ω i)) =
        (Causalean.Stat.empiricalMeasure (S.sampleVector n ω)).map g := by
    unfold Causalean.Stat.empiricalMeasure
      Causalean.Stat.Concentration.finiteSampleMeasure
    rw [Measure.map_smul]
    rw [Measure.map_finset_sum hg.aemeasurable]
    simp_rw [Measure.map_dirac' hg]
  let _ : IsProbabilityMeasure
      (Causalean.Stat.empiricalMeasure (S.sampleVector n ω)) :=
    Causalean.Stat.empiricalMeasure_isProbabilityMeasure _ hn
  change
    ((Measure.pi (fun _ : Fin n =>
      Causalean.Stat.empiricalMeasure (S.sampleVector n ω))).map
        (centeredBootstrapSum ψ (S.sampleVector n ω))) =
      (Measure.pi (fun _ : Fin n =>
        Causalean.Stat.empiricalMeasure
          (fun i : Fin n => g (S.sampleVector n ω i)))).map
        (fun y => (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y)
  rw [hemp]
  rw [← Measure.pi_map_pi (fun _ => hg.aemeasurable)]
  have hcoord : Measurable (fun x : Fin n → X => fun i => g (x i)) := by
    fun_prop
  have hnorm : Measurable
      (fun y : Fin n → ℝ =>
        (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y) :=
    measurable_const.mul (Causalean.Stat.measurable_iidRowSum n)
  rw [Measure.map_map (μ := Measure.pi (fun _ : Fin n =>
      Causalean.Stat.empiricalMeasure (S.sampleVector n ω)))
    (g := fun y : Fin n → ℝ =>
      (Real.sqrt (n : ℝ))⁻¹ * Causalean.Stat.iidRowSum n y)
    (f := fun x : Fin n → X => fun i => g (x i)) hnorm hcoord]
  congr 1
  have hmean :
      Causalean.Stat.finAverage
          (fun i : Fin n => ψ (S.sampleVector n ω i)) =
        S.sampleMean ψ n ω := by
    unfold Causalean.Stat.finAverage IIDSample.sampleVector IIDSample.sampleMean
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ ψ (S.Z i ω)) n]
  funext y
  unfold centeredBootstrapSum Causalean.Stat.iidRowSum g
  simp only [Function.comp_apply]
  rw [hmean]

/-- For [an iid sample](hyp:S), [an observation statistic](hyp:ψ), [its measurability](hyp:hψ),
and [a row index](hyp:n), [the true root-sample-size centered sampling law](goal) is [the
pushforward of the population experiment by the centered transformed sample mean](step:1). -/
def samplingMeanLaw (S : IIDSample Ω X μ P) (ψ : X → ℝ) (hψ : Measurable ψ)
    (n : ℕ) : ProbabilityMeasure ℝ := by
  letI : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  exact
    ⟨μ.map (fun ω ↦ Real.sqrt (n : ℝ) *
        (S.sampleMean ψ n ω - ∫ x, ψ x ∂P)),
      Measure.isProbabilityMeasure_map (by
        fun_prop : AEMeasurable (fun ω ↦ Real.sqrt (n : ℝ) *
          (S.sampleMean ψ n ω - ∫ x, ψ x ∂P)) μ)⟩

/-- For [an observation statistic](hyp:ψ) and [a population law](hyp:P), [the Gaussian limit
variance parameter](goal) is [the population variance represented as a nonnegative real](step:1). -/
def populationVariance (ψ : X → ℝ) (P : Measure X) : NNReal :=
  (ProbabilityTheory.variance ψ P).toNNReal

end

end Causalean.Stat
