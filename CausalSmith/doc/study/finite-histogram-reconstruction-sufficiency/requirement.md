# Substrate requirement: finite-histogram-reconstruction-sufficiency

## Goal
Build axiom-clean reusable finite-histogram sufficiency infrastructure: reconstruct an ordered finite Poisson sample from its finite-alphabet count vector by a parameter-independent Markov kernel uniform on the histogram fiber, and expose the TV and prior-predictive transport lemmas needed to use this reconstruction under mixtures.

## Provides (API contract)
- `histogramReconstructionKernel`: for every finite measurable alphabet `X`, a Markov kernel from count vectors `X → ℕ` to finite variable-length ordered samples, uniform on `HistogramFiber c` and supported on samples with histogram `c`.
- An exact reconstruction theorem: composing `histogramReconstructionKernel` with the independent Poisson count law for probability law `P` and intensity `lambda` equals `finitePoissonSampleLaw P lambda`.
- A fixed-total/multinomial reconstruction theorem if it is a useful intermediate/public specialization.
- A public generic `tvDist_bind_le`/data-processing theorem for applying a common Markov kernel.
- A prior-predictive commutation theorem (`kernel_comp_priorPredictive` or a directly usable equivalent).
- A paired-product corollary: applying reconstruction independently to two count experiments over possibly unequal finite alphabets and intensities does not increase total variation.

## Statement / milestones
For finite measurable `X`, probability measure `P`, and `lambda : ℝ≥0`, prove the exact law identity
`independentPoissonCountLaw P lambda ∘ₖ histogramReconstructionKernel = finitePoissonSampleLaw P lambda`.
The kernel must be independent of `P` and `lambda`. Prove its support/count identity on every nonempty histogram fiber. Then prove common-kernel TV contraction, commutation with prior-predictive mixing, and the paired reconstruction/product contraction theorem for unequal alphabets and intensities.

## Standard reference
Finite multinomial sufficiency and Poisson splitting: conditional on a finite histogram, an iid ordered sample is uniform over all sequences in its histogram fiber; Markov kernels contract total variation.

## Intended reuse
`STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research/Helpers/CommonMarginalTransfer.lean` will reindex its `RawPoissonCounts` laws into paired labeled/auxiliary count laws, reconstruct ordered prior-predictive laws through the common kernel, bound ordered TV by the existing recipe count-TV certificate, and instantiate `randomScale_twoFuzzy_minimax_lower_transfer`. The substrate must remain paper-independent and support unequal finite alphabets and intensities.

## May assume / must derive
May assume finite alphabets with their measurable singleton structure, probability laws, and standard kernel/measurability instances. Must derive normalization/uniformity of histogram fibers, exact reconstruction in law, parameter independence of the kernel, TV data processing, prior-predictive commutation, and paired-product transport. All declarations must contain zero `sorry` and introduce no axioms.

## Non-goals (optional)
Do not import any CausalSmith paper module. Do not use deterministic canonical ordering: it has the wrong conditional law. Do not specialize to the ATE paper's count reindexing or constants.

## Known building blocks (optional)
`Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Basic` exposes `HistogramFiber`, its nonemptiness, and the finite Poisson count-fiber decomposition. `Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.Risk` contains related count-law facts. `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition` supplies finite Poisson sample laws. `Causalean.Stat.Minimax.TotalVariation` supplies TV infrastructure. Same-fiber product-weight constancy currently appears privately in `FixedRisk.lean`, `countLaw_restrict_histogramTotal_eq` privately in `Risk.lean`, and a generic `tvDist_bind_le` privately in `FiniteSignedMomentMarkedPoissonMixture/MarkedPoisson.lean`; promote/reprove paper-independent versions as appropriate.
