# Substrate requirement: finite-density-ordered-local-markov

## Goal
Build a reusable ordered local-Markov conditional-independence theorem for finite DAG density factorizations.

## Provides (API contract)
- A theorem for `Causalean.Graph.FiniteDensity.Factorization` stating that, in any topological order, coordinate `i` is conditionally independent of predecessors outside a set `A`, given the coordinates in `A`, whenever `A` contains every parent of `i`.
- The result in `ProbabilityTheory.CondIndepFun` form, or an equally reusable sigma-algebra-level form with a direct `CondIndepFun` corollary.
- Measurability lemmas for the finite-coordinate projection maps used in the theorem.
- A specialization that applies directly to `Causalean.Graph.FiniteDensity.UnitCubeFactorization` and `unitCubeReference` without extra paper-specific assumptions.

## Statement / milestones
Let `V` be finite, `G : Causalean.DAG V`, and let a family of normalized measurable local densities relative to coordinate reference measures define a `FiniteDensity.Factorization` and its induced joint measure. For a topological order, vertex `i`, predecessor set `Pred(i)`, and `A ⊆ Pred(i)` with `G.parents i ⊆ A`, prove

`coordinate i ⟂ projection (Pred(i) \\ A) | projection A`

under the factorized joint measure. If the arbitrary-`A` result is awkward, first prove local Markov conditional on all parents, then derive the predecessor-superset form with reusable weak-union/decomposition lemmas. Use the existing elimination/marginalization API, especially `Factorization.ancestralMarginal_eq`. All central declarations must be sorry-free and axiom-clean.

## Standard reference
This is the ordered local Markov property for a Bayesian network: a distribution factorizing according to a DAG makes each variable conditionally independent of its earlier nonparents given its parents. Standard treatments establish equivalence between DAG factorization and local/ordered Markov properties for densities.

## Intended reuse
The immediate consumer is the parent-pruning chain in `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.exact_ratio_decoder`, where `A` is a proposed parent set containing the true parents and the remaining predecessors must be conditionally irrelevant. The API belongs in `Causalean.Graph.FiniteDensity` and should support unrelated finite-density Bayesian-network formalizations.

## May assume / must derive
May assume a finite vertex type, standard Borel coordinate spaces, sigma-finite coordinate reference measures, a DAG and topological order, and the existing hypotheses packaged by `FiniteDensity.Factorization`, including normalized measurable local densities and the induced factorized joint measure.

Must derive conditional independence from factorization. Must not assume a local-Markov or conditional-independence premise, import any `CausalSmith/*_Research` module, add a paper-specific bridge, or package the decoder/parent-pruning conclusion itself as substrate. The UnitCube specialization must follow from the existing `UnitCubeFactorization` data without additional model assumptions.

## Non-goals (optional)
Do not formalize general d-separation completeness, causal minimality, parent recovery, rank reconstruction, or the paper's exact decoder. Do not add positivity assumptions beyond those already intrinsic to the chosen finite-density factorization API unless the theorem genuinely requires them and the UnitCube specialization discharges them internally.

## Known building blocks (optional)
- `Causalean.Graph.FiniteDensity.Main`
- `Causalean.Graph.FiniteDensity.Cube`
- `Causalean.Mathlib.CondIndep`
- `Factorization.ancestralMarginal_eq`
- Mathlib conditional-expectation, product-measure, and coordinate-projection APIs
