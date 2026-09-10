## Done
- Ground-truth audit found the target directory absent; no prior declarations or partial proofs existed.
- Created `Product.lean`, `Compression.lean`, `VerticalStack.lean`, and umbrella `API.lean`; the targeted API build succeeds with only `sorry` warnings.
- Searched the Causalean index and Mathlib LeanSearch. Reused the promoted singular-value min--max support from `Causalean.Mathlib.Analysis.SingularValueWeyl`; Mathlib has no direct theorem for these three contracts.
- The scaffold directly states the rank-sized rectangular product bound, all-index orthonormal compression invariance, and all-index vertical-stack monotonicity; it also includes a real-matrix product corollary and the stack Gram identity.

## Remaining
- `Product.lean`: `le_singularValues_of_subspace`, `least_singularValue_mul_norm_le`, `least_singularValue_mul_norm_le_adjoint_on_range`, `singularValues_product_adjoint_lower_bound`, and `Matrix.singularValues_mul_mul_transpose_lower_bound`.
- `Compression.lean`: `singularValues_comp_linearIsometry_of_range_eq_adjoint_range`; the last-index adapter is already proved from it.
- `VerticalStack.lean`: `verticalStack_adjoint_comp_self`, `singularValues_le_verticalStack_left`, and `singularValues_le_verticalStack_right`.

## Blocked
- No hard blocker. Compression will require comparing the Gram spectrum on `range M†` with the compressed Gram operator; Mathlib's singular-value API is currently eigenbasis-based and sparse.

## Decisions
- Use zero-extended `LinearMap.singularValues` throughout.
- Treat the ambient adjoint only on `range B`; never assume `B†` is injective on its ambient domain.
- Model a vertical stack in `WithLp 2 (F₀ × F₁)`, not the ordinary product norm, so the codomain has the Hilbert direct-sum norm and a valid inner-product-space instance.
- Keep the three proof files mutually independent (each imports only stable library modules) so fillers may work concurrently without overlapping import closures.
