## Done
- `Definitions.lean`: implemented prefix rank/agreement, reveal sigma-algebras and filtration, explicit finite prefix conditional expectation, martingale-difference predicate, both predictable variations, fourth-moment errors, Kolmogorov expressions, and the explicit `HeydeBrownFourthMomentPremise`; zero sorries.
- `Identifications.lean`: closed product-measure, finite-fourth-moment, second-moment, and pointwise-CDF bridges.
- Verified `lake build CausalSmith.Substrate.FiniteDesignHeydeBrownBridge.Main`: succeeds with exactly seven sorry warnings and no errors.

## Remaining
- `Identifications.lean`: `prefixCondExp_ae_eq_condExp`, `aestronglyMeasurable_reveal_of_prefixCondExp_eq`, `condExp_ae_eq_zero_of_prefixCondExp_eq_zero`, `finitePredictableVariation_ae_eq_measurePredictableVariation`, `finiteKolmogorovExpr_eq_measureKolmogorovExpr`, `finiteFourthMomentError_eq_measureFourthMomentError`.
- `Main.lean`: `finiteDesign_heydeBrown_fourthMoment`.

## Blocked
- The Project Euclid primary PDF (DOI 10.1214/aoms/1177696722) was located through Crossref but blocked by its anti-bot page. Accessible later literature confirms the source-matched `p=2` error and exponent `1/5`; this does not block the adapter.

## Decisions
- Prefix conditional expectation is an explicit hidden-coordinate weighted sum, valid even when coordinate designs have zero-mass atoms; identification with Mathlib conditional expectation is therefore almost everywhere.
- `IsPrefixMartingaleDifference` packages both pre-reveal centering and post-reveal adaptedness, which are jointly necessary for a genuine martingale-difference application.
- The external inequality is a proposition passed explicitly to the specialization theorem; no axiom or research-module dependency was introduced.
- Kolmogorov distance uses `sSup (Set.range ...)`, allowing exact equality of the finite and measure-theoretic interfaces.