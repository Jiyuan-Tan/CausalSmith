# Quantitative symmetric-tensor pencil local inverse

Develop a reusable, axiom-clean Lean theorem for stable recovery of a finite symmetric rank-one tensor decomposition by the tensor-pencil method.

For two decompositions
\[
T=\sum_{j=1}^n \lambda_j c_j^{\otimes(2d+q)},\qquad
T'=\sum_{j=1}^n \lambda'_j (c'_j)^{\otimes(2d+q)},
\]
assume unit Euclidean columns, coefficient magnitudes in `[kappa, Lambda]`, positive contraction-probe loadings at least `sigma`, least singular value at least `sigma` for both lifted direction matrices, and pairwise separation at least `sigma` of the pencil ratios formed by two unit probes. Under a sufficiently small Frobenius perturbation of `T`, prove that the columns of the two factor matrices can be matched by a permutation and bounded linearly in Frobenius norm by the tensor perturbation.

The useful substrate should expose the complete quantitative chain needed by applications: norm control for tensor contractions, conditioning of the lifted factor matrix, perturbation of the simultaneous-congruence/generalized-eigenvalue pencil, gap-based matching of spectral projectors, recovery and normalization of rank-one lifted directions, and permutation-aligned recovery of the original columns. It may state a general explicit constant assembled from these bounds; applications must be able to specialize it to concrete positive constants such as `eta = kappa * sigma^(q+2)`, `chi = sqrt n / sigma`, and the resulting local radius and Lipschitz factor.

Use only Mathlib, Causalean, and study-local prerequisites. Do not import any `CausalSmith/*_Research` module. Existing relevant substrate includes `opNorm_sub_le_of_approximate_simultaneous_congruence`, `Causalean.Mathlib.Analysis.SingularValueWeyl`, and `Causalean.Mathlib.Analysis.RectangularSignalSingularValues`; current searches found no theorem covering tensor contraction, spectral-projector recovery, and permutation-aligned factor control together.
