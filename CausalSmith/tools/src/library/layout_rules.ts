/** Shared, repository-independent policy tables for the Causalean layout lint. */

/** A source directory may import only the same or a numerically lower layer. */
export const LAYER_PREFIXES: ReadonlyArray<readonly [prefix: string, layer: number]> = [
  ["Discovery", 9], ["ML", 8],
  ["Panel", 7], ["Experimentation", 7], ["Estimation", 6],
  ["PO/ID", 5], ["SCM/PartialID", 5], ["SCM/Examples", 5], ["SCM/ID", 5],
  ["PO/Conditioning", 4], ["PO/Analysis", 4],
  ["PO/Core", 3], ["PO/Assumptions", 3], ["PO/Bridge", 3], ["SCM/Do", 3], ["SCM/Factored", 3],
  ["Stat/Identification", 2], ["Stat/FiniteDesign", 2], ["Stat/Weighted", 2],
  ["Stat/LinearModel", 2], ["Stat", 2], ["SCM/Model", 2],
  ["Graph", 1], ["Mathlib", 0], ["Tactic", -1],
];

/** Deliberate namespace extensions that cannot be inferred from the file path. */
export const NAMESPACE_ALLOWLIST = [
  "Causalean.PartialID", "Causalean.SteinMethod", "Causalean.GaussMarkov",
  "Causalean.SWIGGraph", "Causalean.DAG", "Causalean.Graph", "MeasureTheory",
  "LinearMap", "ProbabilityTheory", "Set",
];

/** Mathlib top-level directories when the checked-out Mathlib package is unavailable. */
export const FALLBACK_MATHLIB_TOP_LEVEL = [
  "Algebra", "AlgebraicGeometry", "Analysis", "CategoryTheory", "Combinatorics",
  "Computability", "Condensed", "Control", "Data", "DifferentialGeometry", "Dynamics",
  "FieldTheory", "Geometry", "GroupTheory", "InformationTheory", "LinearAlgebra", "Logic",
  "MeasureTheory", "ModelTheory", "NumberTheory", "Order", "Probability", "RepresentationTheory",
  "RingTheory", "SetTheory", "Tactic", "Testing", "Topology",
];

export const MATHLIB_DIR_EXCEPTIONS = ["Optimization", "Algorithms"];

/** Stable seeds copied from the migration inventory. The lint never reads internal/. */
export const SEEDED_RUN_SLUGS = [
  "absolute-value-moment-prior-duality", "affine-polynomial-image-dimension",
  "affine-sign-cell-closure", "analytic-set-universal-measurability", "argument-principle-circle",
  "asymptotic-lan-convolution", "bernstein-szego-trig", "certified-finite-markov-expectation",
  "certified-normal-cdf-enclosure", "certified-contour-interval-arithmetic",
  "collinear-simultaneous-congruence-ambiguity", "conditional-marked-subsample-dkw",
  "constrained-quadratic-score-program", "converging-together-clt", "ehlich-zeller-mesh",
  "euclidean-radial-polynomial-vc-subgraph", "finite-density-ordered-local-markov",
  "finite-design-conditional-pushforward-rao-blackwell",
  "finite-family-independent-poisson-prefix-rao-blackwell", "finite-moment-near-gaussian-perturbation",
  "finite-perron-frobenius-positive-eigenvector", "finite-polynomial-alternation-duality",
  "finite-side-information-minimax-convergence", "finite-signed-moment-marked-poisson-mixture",
  "finite-squared-loss-minimax", "finite-stratum-marked-ratio-mse", "finite-dim-l1-linf-duality",
  "finite-marked-poisson-partition", "hilbert-empirical-mean-concentration",
  "holder-pointwise-l1-interpolation", "johnson-kneser-spectral-decomposition",
  "kl-density-tilt-expansion", "l2-residual-quadratic-projection", "martingale-array-clt",
  "measure-preserving-condindep-domain-transport", "monotone-window-deque-correctness",
  "observation-dependent-van-trees-ac", "order-four-jackson-tensor-approximation",
  "paired-poisson-histogram-rao-blackwell", "pairwise-affine-simultaneous-congruence-stability",
  "parametric-rational-integral-analyticity", "poisson-add-one-poincare",
  "poisson-self-normalized-bad-event-moments", "product-loss-monotone-coupling",
  "random-design-weighted-hoeffding", "random-scale-unequal-two-pool-poisson-minimax-transfer",
  "real-valued-vc-subgraph-covering", "superpop-network-hac-consistency",
  "superpop-network-mean-clt", "support-localized-moment-matched-mixture",
  "symmetric-tensor-pencil-local-inverse", "variance-adaptive-vc-expected-maximal",
  "weighted-circular-tube-side-mass-packing",
];

/** Basenames paired with the seeded slugs in the migration inventory. */
export const SEEDED_RUN_BASENAMES = [
  "AbsoluteValueMomentPriorDuality", "AffineSignCellClosure", "AnalyticSetUniversalMeasurability",
  "ArgumentPrincipleCircle", "AsymptoticLanConvolution", "BernsteinSzegoTrig",
  "CertifiedContourIntervalArithmetic", "CertifiedFiniteMarkovExpectation", "CertifiedNormalCDFEnclosure",
  "CollinearAmbiguity", "ConditionalMarkedSubsampleDkw", "ConvergingTogether", "DomainTransport",
  "EhlichZellerMesh", "EuclideanRadialPolynomial", "FiniteDensity", "FiniteDimL1LinfDuality",
  "FiniteFamily", "FiniteMarkedPoissonPartition", "FiniteMomentNearGaussianPerturbation",
  "FinitePerronFrobeniusPositiveEigenvector", "FinitePolynomialAlternationDuality", "FiniteRaoBlackwell",
  "FiniteSideInformation", "FiniteSignedMomentMarkedPoissonMixture", "FiniteSquaredLoss",
  "FiniteStratumMarkedRatioMse", "HACConsistency", "HilbertEmpiricalMean", "HolderInterpolation",
  "IndependentPoissonPrefix", "JacksonApproximation", "JohnsonKneser", "KlDensityTiltExpansion",
  "MartingaleArray", "MeanCLT", "MomentMatchedMixture", "MonotoneWindowDeque",
  "ObservationDependentVanTrees", "OrderedLocalMarkov", "PairedPoissonHistogram", "PairwiseAffine",
  "ParametricRationalIntegralAnalyticity", "PoissonAddOnePoincare", "PoissonSelfNormalized",
  "PolynomialImageDimension", "ProductLossMonotoneCoupling", "RandomDesignWeightedHoeffding",
  "RandomScaleMinimaxTransfer", "RealValuedVCSubgraph", "ResidualQuadratic", "ScoreProgram",
  "SymmetricTensorPencil", "VarianceAdaptiveVCExpectedMaximal", "WeightedCircularTube",
];
