## Done
- `Kernel.lean`: parameter-independent uniform-fibre PMF/kernel, Markov instance, singleton mass, histogram support, and histogram pushforward identity are proved.
- `CountLaw.lean`: independent singleton-cell Poisson product law, probability instance, and `finitePoissonSampleLaw_map_histogram` are proved.
- `GenericTransport.lean`: `tvDist_bind_le` and `kernel_comp_priorPredictive` are proved.
- `PairedTransport.lean`: paired kernel now uses Mathlib's equivalent `Kernel.parallelComp`, with the required composition lemmas imported.
- Ground truth: targeted `lake build ...Main` succeeds; LSP reports no errors. Exactly four `sorry`s remain.

## Remaining
- `Reconstruction.lean`: `multinomialHistogramLaw_comp_reconstruction`; `independentPoissonCountLaw_comp_reconstruction`.
- `PairedTransport.lean`: `pairedIndependentPoissonCountLaw_comp_reconstruction`; `tvDist_paired_finitePoissonSampleLaw_le_counts`.

## Blocked
- None.

## Decisions
- Dispatch two fillers on disjoint files; paired transport may rely on the reconstruction theorem while its proof is being closed.
- Reprove generic fibre-weight/restriction facts locally rather than importing `FixedRisk.lean` or `Risk.lean`; their private prototypes were inspected only as canonical guidance.
- Use `finitePoissonSampleLaw_restrict_count_eq` for Poisson reassembly and `Measure.prod_comp_left`/`prod_comp_right` plus `Kernel.parallelComp` for paired reconstruction.
- No external paper was named; the canonical Lean library sources and Mathlib search results were inspected. No paper/research module is imported.