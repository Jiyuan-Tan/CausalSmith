## Done
- `Flattening.lean`: all flattening equivalences, finite-product transports, nested/flat measure-preserving theorems, and update identities are proved.
- Replaced the duplicate `CausalSmith.Substrate.PoissonAddOnePoincare.Tensorization` dependency with canonical `Causalean.Mathlib.Probability.PoissonAddOnePoincare.Tensorization`; all three modules now open the canonical namespace.
- `PolynomialGrowth.lean`: scalar Poisson powers, total-count moments, polynomial-growth `MemLp 2`, both add-one closures, and the bundled closure theorem are proved.
- `Factorization.lean`: flattened-coordinate and cellwise product/square factorization identities plus product `MemLp 2` closure are proved.
- Searched the Causalean index and inspected the canonical tensorization source to confirm declaration names, namespace, and hypotheses.
- Verified `lake build CausalSmith.Substrate.NestedPairedPoissonProductMoments`: success (3115 jobs), with zero errors and zero `sorry`; remaining output is linter warnings only.
- Audited the new module tree: no `sorry`, `admit`, `axiom`, `extern`, old namespace opening, or forbidden external CausalSmith dependency remains.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep `nestedPairedPoissonFlattening` oriented from nested samples to the flat Sigma-indexed vector, with the inverse exposed separately.
- Measure polynomial growth using the total of both counts across all cells; one bound supplies `L²` closure for the statistic and every coordinate add-one increment.
- Expose factorization through both arbitrary flattened-coordinate factors and ergonomic first/second cell factors.
- Use the promoted Causalean tensorization module as the sole source of `poissonPi`, `nestedPairedPoissonMeasure`, and add-one definitions; no duplicate CausalSmith substrate dependency is retained.