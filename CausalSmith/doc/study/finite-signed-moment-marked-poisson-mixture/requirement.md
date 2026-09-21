# Substrate requirement: finite-signed-moment-marked-poisson-mixture

## Goal
Build axiom-clean reusable Causalean substrate turning a normalized finite signed moment-dual certificate into probability priors and a label-gated marked-Poisson mixture bound.

## Provides (API contract)
- From finitely many real nodes and signed weights with sum absolute weights one and moments zero through degree `L` (hence total signed mass zero), construct a finite signed measure `sigma`, prove `sigma.variation` is a probability measure, expose a measurable polar sign `h` with `|h| = 1` variation-a.e., and construct the two Jordan probability measures with equal moments through `L` and the requested target-separation orientation.
- For positive `a` and support in `[a / kappa, B]`, construct the zero-inflated probability measure `nu = |sigma|` weighted by `a / (p + a)` plus the residual atom at zero; prove support, `E_nu p = a * integral p / (p + a) d|sigma|`, `E_nu p^2 <= B * E_nu p`, and iid finite-product support/moment/variance identities.
- Define a paper-independent one-coordinate marked Poisson experiment with latent `p`, treated mass `s = epsilon * (p + a)`, homogeneous binary outcome mark determined by `h`, auxiliary treated and aggregate control counts; prove that equality through moment degree `L` makes its two prior-predictive laws agree when the labeled treated count is zero and gives `TV <= C * u * a * rho^L` whenever `(u + v) * B <= b * L`.
- Expose composition with finite iid product priors and `tvDist_pi_iid_le`, giving `k` times the one-coordinate bound.

## Statement / milestones
First realize the finite signed certificate as variation plus polar sign and normalized Jordan priors. Next build and analyze the zero-inflated prior, including its support, first/second moments, and finite iid-product identities. Then define the generic marked-Poisson observation law and prove the zero-labeled-count cancellation and geometric one-coordinate TV estimate from moment matching. Finally tensorize the TV estimate to finite iid products. APIs must cover `u = 0` or `v = 0` when `u + v > 0`.

## Standard reference
Finite signed-measure Jordan decomposition and polar representation; zero-inflated mixtures; Poisson marking/thinning; moment-matched mixture bounds via exponential-series tails; tensorization of total variation for finite product measures.

## Intended reuse
The immediate consumer is `CommonMarginalPrior` in `stat_semisupervised_discrete_ate_annotation_frontier/v1`, which will instantiate the generic package and separately build the reservoir/rare-cell `DiscreteLaw` normalization and `rawPoissonLaw` kernel identification. The API should also support future finite moment-matching lower bounds with marked Poisson observations.

## May assume / must derive
May assume the normalized finite signed moment certificate, positive `a`, the stated compact support interval, finite index types, and the bandwidth inequality `(u + v) * B <= b * L`. May reuse `Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.Alternation`, `Causalean.Stat.Minimax.MomentMatchedMixture.SupportLocalized`, `Causalean.Stat.Minimax.MomentMatchedMixture.Product`, `Mathlib.MeasureTheory.VectorMeasure.Variation.Basic`, `Mathlib.MeasureTheory.VectorMeasure.WithDensity`, and `Mathlib.Probability.Distributions.Poisson.Basic`. Must derive every construction and bound listed above. All public declarations must contain zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import `CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research` or any `CausalSmith.Substrate` module. Do not introduce the paper-specific `DiscreteLaw` type, reservoir normalization, rare-cell bookkeeping, or raw experiment-kernel identification.
