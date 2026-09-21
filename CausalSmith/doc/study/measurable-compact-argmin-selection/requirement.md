# Substrate requirement: measurable-compact-argmin-selection

## Goal
Provide a reusable measurable nearest-point/argmin selector for a fixed nonempty compact subset of a finite-dimensional Euclidean space.

## Provides (API contract)
- `borelMeasurable_compact_argmin_selector`: for a nonempty compact action set `K` in finite-dimensional Euclidean space and a jointly Borel objective continuous in the action, expose a Borel measurable selector attaining the minimum whenever the standard measurable-extrema hypotheses hold.
- `borelMeasurable_nearestPoint_selector`: specialize the preceding result to squared Euclidean distance from a parameter point to `K`, returning a Borel measurable `π` with `π x ∈ K` and `dist x (π x) = inf_{y∈K} dist x y`.

## Statement / milestones
For a nonempty compact `K ⊆ EuclideanSpace ℝ ι` with finite `ι`, prove existence of a Borel measurable nearest-point selector on the ambient Euclidean space. If a faithful general compact-action measurable-argmin theorem can be built economically from available Mathlib measurable-multifunction machinery, expose it too; otherwise the nearest-point theorem is the required milestone. The selector must be total, attain the minimum exactly, and require no uniqueness or convexity.

## Standard reference
Brown and Purves (1973), *Measurable Selections of Extrema*, Annals of Statistics 1(5), Corollary 1, DOI 10.1214/aos/1176342510. The primary-source statement gives a Borel measurable exact minimizer on the set where the infimum is attained; compactness and continuity ensure attainment here.

## Intended reuse
The CausalSmith run `stat_proxy_effectlaw_eigencollision_frontier/v1` needs a Borel nearest-summary selector over a nonempty compact finite-dimensional summary closure. The result should be paper-agnostic and reusable for minimum-distance estimators, compact identified sets, and measurable projection rules.

## May assume / must derive
May assume finite-dimensional Euclidean ambient/action spaces, nonempty compactness of `K`, and standard Borel structures. Must derive exact minimum attainment, membership in `K`, totality, and Borel measurability of the selected rule. Do not assume a unique minimizer, convexity, or a measurable selector as an axiom.

## Non-goals (optional)
Universal measurable selection for arbitrary set-valued maps, infinite-dimensional actions, approximate selectors, and paper-specific summary-space definitions are out of scope.

## Known building blocks (optional)
Use existing compactness/continuity/minimum-attainment facts and any available measurable graph or finite-dimensional Borel infrastructure. Causalean's elementary interval/random-set selectors may provide patterns, but do not introduce a paper-module import.
