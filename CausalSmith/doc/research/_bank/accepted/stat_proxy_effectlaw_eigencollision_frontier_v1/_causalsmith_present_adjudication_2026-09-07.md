# Presentation adjudication — 2026-09-07

## P1 notation ownership

The first P1 notation review found 24 undefined-symbol groups. The symbols were not new mathematical content: they were already realized by Lean declarations, but their graph nodes were hidden helpers or setup prose and therefore supplied no reader-facing definition before first use.

Fixed by promoting concise Lean-backed definition nodes for the observed margin, latent masses and means, latent effects, proxy feature matrices, effect radius and gap, population moments, concentration radius, atomic-law class, ordered masses, factorization-preserving path, atom floor, structured-lattice constant and program, finite-net program, and published VMW regimes. The outline notation table now designates those nodes as the authoritative homes and places them at the beginning of the setup section.

Bank edits: `graph.json` gained the promoted presentation nodes. Presentation edits: `outline.md` gained their notation-home rows and setup placement. No Lean source, research theorem statement, proof, pipeline source, or prompt was changed.

## P1 component mapping

The statement audit found that the hidden helper node `aux_quotientLaw` used an unqualified declaration name, although the source contains the unique declaration `CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.QuotientFunctionalCalculus.quotientLaw` in `Helpers/QuotientFunctionalCalculus.lean`. Patched that graph pointer and the corresponding `crosswalk_full.json` entry; preserved the prior crosswalk as `formalization/crosswalk_full.json.bak`.

## P1 statement-audit convergence

P1 later exposed an audit/notation oscillation for `def:published-vmw-regimes` and `def:wasserstein-confidence-set`: the statement auditor produced Lean-faithful bodies, but the next notation pass regenerated them from older graph prose. The graph statements are now synchronized to the auditor-approved bodies. The VMW environment describes only the opaque fields actually carried by `PublishedVMWScopeHandle`; the confidence-set environment retains the exact summary-inversion and `AtomFloor`/Wasserstein definitions while omitting the unsupported transport-union representation.

## P1 checkpoint approval

Auto-mode checkpoint review approved the outline and frozen layer: the section progression is coherent, all 82 formal blocks have nonempty identifiers and bodies, `notation_review.json` is clean with no advisories, and the synthesized notation owners occur before the theorem-level uses they support. The bibliography preserves the P0-verified identifiers and documented metadata caveats. No ballast review was emitted.

## P2 ballast adjudication

Acknowledged the two same-class minimax propositions as delivered sharp-rate headline benchmarks and the published-VMW converse-transfer theorem as the delivered scope bridge from the explicit witnesses to publication-level comparator classes. Their lack of downstream proof consumers is expected because each is a terminal synthesis/scope result, not motivation-only apparatus.

## P1 v2 notation-order adjudication

The rewritten P1 planner rebuilt the outline and refreshed all legacy frozen bodies, then exposed deterministic definition-before-use defects. The full-data-law symbol \(P\) is now owned by the earlier `def:observed-margin`, while the observed variables \(T,X,Z,Y\) and their dimensions are owned by `def:observed-record-space`; the regenerated outline records the remaining full-data carrier primitives as a notation gap for synthesis. The generic tail probability \(\eta\) is introduced by `lem:uniform-summary-concentration`, which is placed before its first theorem-level consumer. No mathematical claim, Lean source, pipeline source, or prompt changed.

## P1 v2 checkpoint approval

Auto-mode review approved the regenerated outline and formal layer. `notation_review.json` is converged (`ok: true`), the 113 formal blocks have unique nonempty identifiers and bodies, all 88 Lean-judged graph environments are faithful and frozen, the outline has conventional introduction/related-work/setup/results/lower-bound/discussion/appendix progression, and no motivation-only object was placed in `objs:`. The 27 `xref-missing` advisories concern graph `statement-uses` edges whose mathematical content is stated inline or belongs in proofs, not missing assumptions. The 62 `notation-mutual-definition` advisories are acknowledged as conservative order diagnostics over shared ambient symbols and local binders (for example generic \(X,\xi,\lambda,a,c,\omega\)); the semantic notation review reports no remaining undefined, wrong-reference, or mismatch blocker. The existing ballast acknowledgements cover the three terminal benchmark/scope results.

## P2 second-promotion adjudication

Granted `--promote-again` after the first promotion round because the residual proof audit identifies genuinely uncited, Lean-backed derivations: the combined structured-lattice rounding/feasibility certificate, the sharp divided-difference functional-calculus bound, monotone-transport optimality for the displayed Wasserstein equality, the outcome-weighted observable-moment factorization, and the visible-cell displacement and uniform floor calculations for the local path. These are citable-step gaps appropriate for promotion. The simultaneous notation-shadowing, hard-coded-reference, closure-description, and proof-route findings are rendering defects and are not grounds for promotion; they remain assigned to the P2 proof rerendering loop.

## P1 promoted-layer checkpoint approval

Auto-mode review approved the post-promotion P1 layer after repairing two mechanical defects: the attaining Kantorovich--Rubinstein helper now points to the run-local, type-checked wrapper `krPotential_attains_with_normalization` in `Helpers/StructuredLatticeFunctionalCalculus.lean`, and a stray display closer was removed from the frozen compressed-spectral-certificate body. The observed-record definition was also placed before the empirical-summary primitives so \(T,X,Z,Y\) are owned before use. The resulting `formal_layer.json` has 124 unique, nonempty blocks; all promoted Lean-backed bodies are judged faithful; the eight promoted helpers are placed together in the proof-ledger appendix; and all 51 verified bibliography entries remain. The notation review converged (`ok: true`). Its two `notation-unresolved` advisories are accepted with explicit scope: \(p^{\uparrow}(\xi)\) is the represented-law extension characterized by `lem:ordered-masses-measure-invariance`, distinct by argument type from the model-law target \(p^{\uparrow}(P)\); and \(\widehat D_n(s)\) is the thresholded summary functional, while the no-argument \(\widehat D_n\) is its empirical evaluation at \(\widehat S_n\). The remaining 39 mutual-definition advisories are conservative shared-symbol diagnostics and do not put an undefined symbol before its semantic home.

## P2 supervisor-granted additional promotion

The supervisor granted exactly one additional `--promote-again` round after the two-round halt. Promotion is limited to the residual citable-step gaps: (1) the `model_realDiagonalization_certificate` / `ThinSignalFactorization.diagonalization_conditionNumber_le` route for `thm:gap-free-positive-measure-modulus`; (2) `AmbientOperatorBridge.model_summary_ambient_bounds` together with the rank/threshold facts for `prop:polynomial-net-law-estimator`; and (3) the coordinate-box inclusion, signal-space projection argument, and collision-safe `complete_projectorLaw_eq` route for `thm:polynomial-net-law-estimator`. The remaining singular-value indexing, closure description, missing paper environment/hypothesis, symbol/model translation, attribution, and route mismatches are rendering defects and are not promotion targets.
