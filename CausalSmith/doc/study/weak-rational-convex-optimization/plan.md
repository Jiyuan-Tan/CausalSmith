## Done
- Ground truth verified: `lake build CausalSmith.Substrate.WeakRationalConvexOptimization.Main` succeeds (2387 jobs), with exactly three `sorry` warnings and no errors.
- `Basic.lean`, `LinearOracle.lean`, `CenteredContraction.lean`, `MembershipStrengthening.lean`, `StrengthenedMembershipDecision.lean`, `RadialBoundarySearch.lean`, `LinearFoundation.lean`, and `Main.lean` are closed.
- Library-first Causalean and Mathlib searches found no reusable weak-membership/ellipsoid implementation.
- Fetched the primary GLS source and confirmed Lemma 4.3.4's exact distance-dependent cut and Theorem 4.3.13's outer-feasible, erosion-only conclusion.
- Added `VeryWeakSeparation.lean` with the faithful GLS 4.3.4 outcome, actual-call trace, resource record, and reciprocal-slope accounting; `ShallowCutEllipsoid.lean` now imports it.

## Remaining
- `VeryWeakSeparation.lean`: prove `gls_very_weak_separation_traced`.
- `ShallowCutEllipsoid.lean`: prove `gls_shallow_cut_ellipsoid_traced` after the very-weak-separation layer closes.
- `Foundation.lean`: prove `gls_weak_rational_convex_optimization_foundation` through the bounded-epigraph/value-oracle reduction.

## Blocked
- The shallow-cut and nonlinear foundations remain downstream of genuine algorithmic infrastructure and should not be retried before `gls_very_weak_separation_traced` closes.
- No dependency supplies GLS 4.3.4, shallow-cut ellipsoid iteration, or rational trace/bit accounting.

## Decisions
- Decomposed the shallow-cut monolith at the next dependency-ordered GLS layer rather than redispatching it unchanged.
- Dispatch one filler on `gls_very_weak_separation_traced`; all open obligations share one import chain, so parallel fillers would interfere.
- Preserve the exact GLS dichotomy: outer membership or a nonzero rational normal satisfying the distance-dependent cut. Charge `beta.den` numerically because GLS 4.3.4 is polynomial in the magnitude of `1/beta`, not its encoding length.
- Continue requiring executable rational data, actual oracle traces, uniform polynomial bounds, and no density witnesses, invented usage, axioms, or paper-specific imports.