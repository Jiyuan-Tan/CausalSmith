# Substrate requirement: measurable-finite-side-information-minimax-bridge

## Goal
Extend the reusable finite-side-information minimax substrate with a measurable-procedure comparison layer connecting finite-coordinate procedures to globally measurable bounded estimators.

## Provides (API contract)
- Continuity, hence Borel measurability, of `conditionalAverageProcedure` in its `FinitePmf` argument for finite labeled and finite nonempty side alphabets.
- A measurable clipped extension of a continuous bounded procedure on the finite probability simplex to the ambient finite real coordinate table.
- Finite-product integral equals `productProbability` finite-sum risk identities for PMFs and product measures.
- Reusable minimax comparison and reindexing lemmas under a surjective continuous parameter map, sufficient to squeeze a measurable exact-table minimax value between `exactSideMinimaxValue` and every `empiricalSideMinimaxValue`.

## Statement / milestones
Show that conditional averaging of a bounded empirical procedure is polynomial and continuous in the finite side-law coordinates. Extend continuous interval-valued simplex procedures measurably to the ambient coordinate space, clipping back to the action interval. Prove exact finite-sum forms for risks under finite product PMFs/measures. Establish infimum/supremum comparison and reindexing across a continuous surjection of compact parameter spaces, yielding the squeeze needed to combine measurable exact-table risk with `closedSimplex_finiteSideInfo_minimax_tendsto`.

## Standard reference
Standard finite statistical decision theory: conditional averaging/Rao–Blackwellization, polynomial dependence of finite expectations on PMF coordinates, measurable extension from closed subsets of Euclidean space, and minimax reindexing under surjective parameterizations.

## Intended reuse
The immediate consumer is `known_marginal_limit` in `stat_semisupervised_discrete_ate_annotation_frontier/v1`. The API must compose directly with `closedSimplex_finiteSideInfo_minimax_tendsto` while remaining paper-independent.

## May assume / must derive
May assume finite alphabets, nonempty side alphabet, a compact/closed simplex parameter set, continuous probability coordinates and bounded continuous target, and standard Borel structures on finite Euclidean coordinate spaces. Must derive conditional-average continuity/measurability, clipped measurable extension, product integral/sum identities, and the surjective minimax squeeze. All public results must have zero `sorry`, use no `admit`, and introduce no axioms.

## Non-goals (optional)
Do not import any `CausalSmith/*_Research` module. Do not parameterize the paper's `DiscreteLaw`, `ClassLaw`, `ModelClass`, overlap constraints, `ateFunctional`, `annotationLaw`, or `knownMarginalRisk`; those are run-local specialization work after promotion. Do not alter the existing convergence theorem or weaken comparison to an assumption.

## Known building blocks (optional)
Reuse the promoted `Causalean.Stat.Minimax.FiniteSideInformation` modules, especially `Experiments`, `Risk`, `Approximation`, `Main`, and `SimplexSpecialization`; Mathlib finite-sum continuity, finite product measures, measurable extension/clipping, compactness, and order/infimum APIs should supply supporting primitives.
