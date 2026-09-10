## Done

- Ground truth (round 3): direct `lake env lean` on `Saddle.lean` and `lake build CausalSmith.Substrate.FiniteSquaredLossMinimax.Saddle` both succeed; source grep finds no `sorry`, `admit`, `native_decide`, or declared axiom.
- Axiom audit: `convexified_risk_game_has_saddle`, `saddle_value_eq_minimaxValue`, and `finite_bounded_squared_loss_has_saddle` use only `propext`, `Classical.choice`, and `Quot.sound`.
- `Core.lean`: procedure/risk API, nonnegativity, feasible-set nonemptiness/convexity/compactness, risk continuity and compact attainable image, prior-simplex and `FiniteDesign.E` bridges.
- `Mixing.lean`: conditional design/action mixing, squared-loss Jensen risk bound, convex-hull recovery by an ordinary procedure, and compactness of the finite-dimensional risk hull via Caratheodory.
- `Saddle.lean`: Sion saddle attainment, equality with Causalean `minimaxValue`, and the exported attaining minimax procedure/least-favorable-prior theorem.
- Library search rechecked Causalean minimax bridges. Primary source fetched: Sion (1958), Theorem 3.4 has the compact-convex, semicontinuous quasi-concave/convex minimax hypotheses used here.

## Remaining

- None.

## Blocked

- None.

## Decisions

- Preserve the general hypotheses: no normalization of `P`, no nonemptiness of `X r`, and no target bounds; only `P >= 0`, `l <= u`, and nonempty finite state/design types are needed.
- Keep Causalean's `FiniteDesign`, `FiniteDesign.E`, and `Causalean.Stat.minimaxValue`; `Procedure` only packages the required design/rule pair.
- The compact convex risk hull plus conditional Jensen recovery is the finite-dimensional bridge to Mathlib Sion. No subagents are needed because the verified tree is review-ready.
