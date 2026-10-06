module
public import Causalean.Stat.Quantile.CdfConvergence
public import Causalean.Stat.SampleSplit.KFold

/-! # Class-indexed scalar cross-fitting data

This module fixes an arbitrary, possibly sample-size-indexed class of laws, an
i.i.d. experiment under each law, a fixed finite fold split, and scalar oracle
and estimated scores. The estimator averages each observation exactly once.
All probabilistic rate assumptions are stated in downstream modules.
-/

@[expose] public section

namespace Causalean.Estimation.OrthogonalMoments.UniformInference

open MeasureTheory ProbabilityTheory Filter Topology Causalean.Stat

/-- A scalar cross-fitting problem consists of an i.i.d. sample under each law,
a fixed-fold partition, a law-specific mean-zero oracle score, and a foldwise
estimated score evaluated on held-out observations. The admissible laws may
depend on sample size. -/
structure Family (ι Ω Z : Type*) [MeasurableSpace Ω] [MeasurableSpace Z]
    (K : ℕ) where
  K_pos : 0 < K
  laws : ι → Measure Z
  sampleLaw : ι → Measure Ω
  sample : ∀ p, IIDSample Ω Z (sampleLaw p) (laws p)
  split : ∀ p, KFoldSplit (sample p) K
  lawClass : ℕ → Set ι
  target : ι → ℝ
  oracle : ι → Z → ℝ
  score : ℕ → ι → Fin K → Ω → Z → ℝ

namespace Family

variable {ι Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
  {K : ℕ} (F : Family ι Ω Z K)

/-- The oracle variance is the population second moment of the mean-zero
influence score under the indexed law. -/
noncomputable def oracleVar (p : ι) : ℝ :=
  ∫ z, (F.oracle p z) ^ 2 ∂F.laws p

/-- The oracle normalized empirical score is the sum over the first `n`
observations divided by `√n`. -/
noncomputable def oracleSum (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i ∈ Finset.range n, F.oracle p ((F.sample p).Z i ω)

/-- The cross-fitted estimator adds the average held-out estimated score to
the law-specific target. Each observation belongs to exactly one fold. -/
noncomputable def estimate (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  F.target p + (n : ℝ)⁻¹ *
    ∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
      F.score n p k ω ((F.sample p).Z i ω)

/-- The cross-fitted score mean is the average of all held-out estimated
scores, in the same weighting used by the estimator. -/
noncomputable def scoreMean (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ *
    ∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
      F.score n p k ω ((F.sample p).Z i ω)

/-- The empirical cross-fitted score variance is its second moment minus the
square of its empirical mean. -/
noncomputable def scoreVar (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  (n : ℝ)⁻¹ *
      (∑ k : Fin K, ∑ i ∈ (F.split p).fold n k,
        (F.score n p k ω ((F.sample p).Z i ω)) ^ 2) -
    (F.scoreMean n p ω) ^ 2

/-- The studentized statistic divides the root-sample-size estimator error
by the square root of the feasible cross-fitted score variance. -/
noncomputable def student (n : ℕ) (p : ι) (ω : Ω) : ℝ :=
  Real.sqrt (n : ℝ) * (F.estimate n p ω - F.target p) /
    Real.sqrt (F.scoreVar n p ω)

/-- A sequence of random quantities vanishes uniformly in probability over
the sample-size-indexed class when the supremum of its tail probabilities
vanishes at every positive threshold. -/
def UniformOP (X : ℕ → ι → Ω → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ⨆ (p : ι) (_hp : p ∈ F.lawClass n),
      F.sampleLaw p {ω | ε ≤ |X n p ω|}) atTop (𝓝 0)

/-- Uniform Kolmogorov convergence to the standard Gaussian means the
largest absolute distribution-function error over the law class and all
real thresholds tends to zero. -/
def UniformGaussian (X : ℕ → ι → Ω → ℝ) : Prop :=
  Tendsto (fun n => ⨆ (p : ι) (_hp : p ∈ F.lawClass n) (x : ℝ),
    ENNReal.ofReal
      |(F.sampleLaw p {ω | X n p ω ≤ x}).toReal -
        ((gaussianReal 0 1) (Set.Iic x)).toReal|) atTop (𝓝 0)

end Family
end Causalean.Estimation.OrthogonalMoments.UniformInference
