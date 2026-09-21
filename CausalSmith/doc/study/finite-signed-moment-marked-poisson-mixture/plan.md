## Done
- Ground truth: `Certificate.lean`, `ZeroInflated.lean`, `AggregatePoisson.lean`, and `Product.lean` contain no `sorry`, `admit`, or axiom declarations.
- `AggregatePoisson.lean`: geometric exponential-tail, Jordan square-root-tail, and aggregate TV bounds are closed.
- `MarkedPoisson.lean`: law/kernel APIs, predictive probability, zero-labeled-count cancellation, and the geometric corollary are closed.
- Verified `lake build CausalSmith.Substrate.FiniteSignedMomentMarkedPoissonMixture.Main`; it succeeds (3115 jobs) with exactly one intentional `sorry`.
- Searched the Causalean index for Poisson Palm/thinning, countable TV, kernel contraction, and moment-matched mixtures. Reusable aggregate-mixture and tensorization APIs exist, but no direct Palm lemma was found.
- Fetched and inspected the LaTeX source of Han–Jiao–Weissman, arXiv:1802.08405, for the Poissonization and moment-matching conventions.

## Remaining
- `MarkedPoisson.lean`: `NormalizedFiniteSignedMomentCertificate.tvDist_markedPoissonPredictive_le_palm_aggregate`.

## Blocked
- None. The remaining proof must formalize the discrete singleton-mass/Palm calculation and Poisson thinning contraction.

## Decisions
- Keep the genuine bound `TV ≤ u * ε * a * aggregate-TV`, including `u = 0` and `v = 0` when `u+v>0`; the point-mass calculation supports this exact constant.
- Dispatch one filler because this is the first direct attempt at the remaining theorem. If it returns multiple substantive blockers, split countable-TV, Palm reindexing, and Poisson-thinning helpers into dependency-ordered modules next round.
- Preserve the current experiment and certificate APIs; do not import paper modules or other substrate trees.