module
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Basic
public import Causalean.Estimation.OrthogonalMoments.UniformInference.EmpiricalScoreMoments
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldMoments
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldRates
public import Causalean.Estimation.OrthogonalMoments.UniformInference.FoldSquaredError
public import Causalean.Estimation.OrthogonalMoments.UniformInference.GaussianTransfer
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Inference
public import Causalean.Estimation.OrthogonalMoments.UniformInference.OracleNormal
public import Causalean.Estimation.OrthogonalMoments.UniformInference.ScoreMean
public import Causalean.Estimation.OrthogonalMoments.UniformInference.Studentization
public import Causalean.Estimation.OrthogonalMoments.UniformInference.VarianceConsistency

/-!
# Uniform cross-fitted scalar inference

Inference for a scalar cross-fitted estimator that is valid uniformly over a class of data laws
which may change with the sample size. Suppose that on training-measurable events whose failure
probability vanishes uniformly, each fold's estimated score is within a vanishing L² distance of
the oracle score and its mean drift is of smaller order than n^{-1/2}, and that the oracle score
is mean zero and bounded with variance bounded away from zero. Then √n times the estimation
error equals the normalized oracle score sum up to a uniformly negligible remainder, the
empirical score variance is uniformly consistent, the studentized estimator converges to the
standard normal in Kolmogorov distance uniformly over the class, and the two-sided Wald interval
has coverage converging to 1 − α uniformly.

## Contents

* `Basic` — the law class, the cross-fitted estimate, the score variance and the studentized
  statistic (`Family`, `UniformOP`, `UniformGaussian`).
* `FoldMoments`, `FoldRates`, `FoldSquaredError` — the conditions `RateConditions` and
  `uniform_asymptotic_linearity`.
* `OracleNormal`, `GaussianTransfer` — `OracleConditions`, the Berry–Esseen bound
  `oracle_berry_esseen`, and transfer of uniform normal approximation under a negligible
  perturbation.
* `ScoreMean`, `EmpiricalScoreMoments`, `VarianceConsistency` — `scoreVar_uniform_consistent`.
* `Studentization` — `student_uniformGaussian`.
* `Inference` — `wald_uniform_coverage`.
-/

public section
