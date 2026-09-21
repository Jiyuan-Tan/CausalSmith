## Done
- Ground-truth audit confirms `Product.lean`, `Compression.lean`, `VerticalStack.lean`, and `API.lean` contain zero `sorry`, `admit`, or custom `axiom` declarations.
- `Product.lean` proves `le_singularValues_of_subspace`, both least-singular-value norm bounds, `singularValues_product_adjoint_lower_bound`, and the thin real-matrix transpose corollary.
- `Compression.lean` proves all-index zero-extended singular-value invariance under an isometry onto `range M†`, plus the last-index adapter.
- `VerticalStack.lean` proves the stack Gram identity and all-index monotonicity against either component.
- Required Causalean and Mathlib searches found the reusable min–max support in `Causalean.Mathlib.Analysis.SingularValueWeyl`; no direct existing theorem subsumes the three contracts. No specific primary source was named to fetch.
- Live LSP diagnostics and direct source elaboration succeed. `lake build CausalSmith.Substrate.RectangularSignalSingularValues.API` succeeds; remaining messages are non-fatal unused-variable/deprecation warnings.
- `#print axioms` for every exported theorem reports only `propext`, `Classical.choice`, and `Quot.sound`.

## Remaining
- None.

## Blocked
- None.

## Decisions
- Keep Mathlib's zero-extended `LinearMap.singularValues` API and the all-index compression/stack results.
- Restrict the adjoint lower bound to `range B`; no ambient injectivity of `B†` is assumed.
- Represent vertical stacks in `WithLp 2 (F₀ × F₁)` to obtain the Hilbert direct-sum norm.
- The statements meet the requested rectangular/full-rank generality without paper-specific imports or strengthened assumptions.