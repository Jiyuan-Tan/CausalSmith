# Rectangular product and signal-subspace singular values

## Route

`substrate-build:study`

## Downstream blocker

`CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observed_vmw_margin_inclusion`
remains a visible `sorry`. The promoted finite-cell conditional-moment bridge supplies the required
probability primitives, but the theorem's armwise, basis-compressed, and vertically stacked
`k`-th-singular-value conclusions need general spectral results that are absent from Mathlib and the
current Causalean substrate.

## Required paper-agnostic substrate

Develop reusable finite-dimensional real linear-map or matrix theorems covering the following.

1. **Rectangular full-rank product lower bound.** For full-column-rank maps/matrices
   `A : Fin k → Fin m`, `B : Fin k → Fin n`, and a core map `D : Fin k → Fin k`, prove a lower bound
   for the last nonzero singular value of

   ```text
   A * D * Bᵀ
   ```

   by the product of the least singular values/lower moduli of `A`, `D`, and `B`. The result must
   handle the fact that `Bᵀ` is not injective on the ambient `Fin n` space; the lower bound is on its
   rank-`k` signal subspace/nonzero spectrum. A version stated through `LinearMap.singularValues
   (k - 1)` is preferred and must handle zero-extension/index side conditions explicitly.

2. **Orthonormal signal-basis compression.** If `V : Fin k → Fin n` has orthonormal columns and its
   range equals the row space/range of the adjoint of a rank-`k` rectangular map `M`, prove that

   ```text
   singularValues (M ∘ V) (k - 1) = singularValues M (k - 1).
   ```

   An equivalent theorem identifying all nonzero singular values under the partial isometry is
   acceptable. State the row-space/range hypothesis in standard `LinearMap.range`/adjoint terms so a
   thin local adapter can consume it.

3. **Vertical-stack monotonicity.** For compatible rectangular maps `M0,M1`, prove that the `k`-th
   singular value of their vertical/direct-sum stack is at least that of either component (or provide
   the squared Gram-operator eigenvalue monotonicity theorem from which this follows directly).

The API may be factored through Courant--Fischer/min--max, lower moduli on subspaces, Gram operators,
or partial isometries, but the exported corollaries must be directly usable for finite real matrices.

## Expected location and constraints

Place the implementation under a paper-agnostic `Causalean/Mathlib/Analysis/` module (slug suggestion:
`RectangularProductSingularValues`). Do not import any `*_Research` module or mention `UCVMWModel`,
proxy moments, latent weights, `SignalBasis`, or the paper's summary objects. Standard axioms only;
no `sorry`, `admit`, custom axiom, or theorem weakening.

After promotion, F will provide thin local adapters from `RectMatrix`/`matrixCLM`, translate
`SignalBasis.orthonormal` and `SignalBasis.SpansSignal`, and apply the product theorem to
`referenceFeature * latentArmWeights * targetFeature.transpose`.

## Search and substantiality receipts

- Causalean concept/type/goal retrieval found only the promoted normalized cross-moment theorem and
  the local `singular_value_variational_lower`, which assumes injectivity on the entire domain.
- Mathlib LeanSearch/Loogle traces found no Courant--Fischer theorem or equivalent rectangular-product
  singular-value result.
- Existing indexed singular-value Weyl controls additive perturbations and does not solve product,
  row-space compression, or stacking.
- A direct composition is invalid because `Bᵀ` is noninjective on its ambient domain. A sound proof
  must restrict to `range B`, establish partial-isometry invariance, and use min--max/Gram spectral
  monotonicity. This is substantial reusable linear-algebra infrastructure.

## Existing progress to preserve

- Preserve `two_class_witness_valid` and `Helpers/WitnessValidity.lean`, now proved and targeted-build
  clean.
- Preserve the promoted `FiniteCellConditionalMomentBridge` import and the persistent F3 adapter
  directive; its probabilistic APIs remain required.
- Preserve the promoted indexed singular-value Weyl theorem and local wrapper.
