# Holistic revision pass 2

- mode: reframe
- source digest before: `02195f98badb5f37141e9042a2da467f47c981deeaa6bc740fffcc2c5fb68b16`
- source digest after: `1e9cf49d3a7229a19095ffb6e6067e0582602ece1dc504cd2e5b66c627f8e156`

## Reviser report

Implemented the P5 prose revision in the authored sources.

Changed:
- [front_matter.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/front_matter.tex)
- [sections/02_setup_and_assumptions.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/sections/02_setup_and_assumptions.tex)
- [sections/04_confidence_sets_cluster_reports_and_ordered_weights.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/sections/04_confidence_sets_cluster_reports_and_ordered_weights.tex)
- [sections/05_lower_bounds_and_sharp_rates.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/sections/05_lower_bounds_and_sharp_rates.tex)
- [sections/06_discussion_extensions_and_open_questions.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/sections/06_discussion_extensions_and_open_questions.tex)
- [sections/09_appendix_c_proofs_and_verification_note.tex](<repo-root>/CausalSmith/doc/presentation/stat_proxy_effectlaw_eigencollision_frontier_v1/.p5_revision_workspace/sections/09_appendix_c_proofs_and_verification_note.tex)

Addressed:
- narrowed verification prose and added commit, Lean/toolchain/dependency metadata, build command, and source-file manifest;
- fixed repeated verification sentence in the introduction;
- reframed “computable” confidence-set prose as fixed-dimensional exact-real finite representation;
- corrected the cluster threshold wording to \(4\rho_{n,\alpha}\), with \(\rho_{n,\alpha}\) reserved for association/interval expansion;
- added a worked two-class collision table from the existing witness;
- clarified duplicate empirical-summary and KL displays as distinct anchored renderings.

Declined or partial due to hard P5 boundaries:
- `definition-order-duplication`: moving/deleting the early definitions and duplicate anchored definitions requires upstream outline/formal-layer changes.
- `cluster-report-observability`: splitting `def:cluster-report` would rewrite a frozen anchored algorithm body. I added surrounding sample-facing/theorem-side prose instead.
- `singular-value-indexing`: zero-based occurrences inside frozen statements and Lean-audited proof displays remain; I added a verification-note translation and kept editable reader-facing prose one-based.
- `verification-scope-metadata`: the appendix/source-side claim is fixed, but the generated author footnote is not present in editable `front_matter.tex` and `paper.tex` is derived/protected.

Verification:
- `lake -d ../../../../ build CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research` succeeded.
- Source scan found no `\ref`, `\eqref`, or `\autoref`.
- LaTeX begin/end environment balance check passed.
- Lean build emitted existing style/deprecation warnings in Lean files; no errors.
