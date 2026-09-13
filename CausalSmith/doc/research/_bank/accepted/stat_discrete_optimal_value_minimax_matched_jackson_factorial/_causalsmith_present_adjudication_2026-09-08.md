# Presentation adjudication — 2026-09-08

## P1 checkpoint

- Re-entered the rewritten P1 from the accepted bank graph after removing the legacy P1 cache and partial artifacts from the live presentation bundle. The obsolete files were preserved under `internal/mill/scratch/mill-w09/legacy_p1_20260908T060058Z/` and were not reused.
- Corrected notation homes in `outline.md`: the full-data law `P` is introduced with fixed overlap, while `K_d`, `b_x`, and `r_x` are introduced with the Jackson-kernel environment. This breaks two genuine definition cycles without changing any mathematical claim.
- Reviewed the regenerated outline, 30-node frozen graph layer plus 12 synthesized definitions, section ordering, and bibliography. The plan has front-matter motivation, early related work, setup before results, upper and lower arguments before appendices, and no standard-literature-only note object requiring removal.
- Accepted the `prop:parent-reduction` `xref-missing` advisory. Its displayed `\mathfrak R_{n,d,\epsilon}` is already defined globally by `def:minimax-risk` in the setup section and is unambiguous in the later discussion section; forcing another cross-reference would add no mathematical information.
- P1's Lean-aware judge converged after four render/review iterations and marked all 30 graph-backed environment bodies faithful.

## Bank edits

- P1 persisted audit-faithful `nl.frozen_body` values for 30 graph nodes.
- This adjudication record was added.

## Presentation edits

- Rebuilt `outline.md`, `formal_layer.tex`, `notation_review.json`, and P1 caches from the rewritten P1 implementation.
- Manually corrected four notation-home rows in `outline.md` as described above.

## P2 ballast review

- Retained and acknowledged `thm:consistency-and-parametric-boundaries`: the theorem is a delivered scientific consequence translating the matched rate into consistency and parametric-boundary regimes.
- Retained and acknowledged `prop:parent-reduction`: the proposition is the formal lineage benchmark promised in the Discussion and distinguishes the matched theorem from the archived predecessor on the same model class.

## P2 provider-capacity escalation

- P2 generated all eight narrative sections and all eleven Lean-backed proof files. Its content-keyed proof-audit cache contains eleven entries, so the completed work is resumable without rerendering the paper from scratch.
- Four cache-preserving invocations terminated on the same transient provider response: `ERROR: Selected model is at capacity. Please try a different model.` The failures occurred after substantial cached progress in each invocation; no earlier P-stage was rerolled.
- At lease return, five audit entries are faithful and six remain non-faithful/incomplete (`thm:matched-minimax-frontier`, `thm:jackson-factorial-upper`, `thm:consistency-and-parametric-boundaries`, `lem:simultaneous-jackson-certificate`, `lem:centered-factorial-pilot-control`, and `lem:dense-moment-matching-lower`, with the exact current issues in `proof_audit_cache.json`). P2 has not reached its checkpoint.
- Exact resume command from `CausalSmith/tools/`: `source scripts/node_env.sh && npx tsx bin/causalsmith.ts present stat_discrete_optimal_value_minimax_matched jackson_factorial --resume`.
- Durable invocation logs are under `<workspace>/_orch_logs/` with prefix `mill-w09_stat_discrete_optimal_value_minimax_matched_jackson_factorial_present_p2_`.

## P2 second-promotion adjudication and P1 cap block

- Granted `--promote-again` after checking the frozen `lem:centered-factorial-pilot-control` statement and its Lean source. The residual `[missing-step]` was a genuinely citable formal result: `canonicalPilot_noiseToRadius_le` is a named lemma in `Helpers/PilotControl.lean` and is used directly by `Helpers/PilotControlPointwise.lean`. This was not an omitted conclusion or a rendering-only defect.
- Promotion round 2 added four paper nodes: `lem:jackson-tensor-extraction`, `lem:jackson-convolution-modulus`, `lem:good-pilot-radius-sum`, and `lem:jackson-normalized-coefficient-envelope`.
- The required P1 delta pass exhausted its six-iteration cap. Verbatim terminal receipt:

  `causalsmith: P1 loop did not converge in 6 iterations (latest layer persisted to formal_layer.tex; renders/reviews/synthesis/verdicts are cached — fix the blocking input and re-run): [xref-dangling] lem:jackson-tensor-extraction lem:jackson-tensor-extraction: \\cref{obj:synth_18} is not a statement-uses dependency of lem:jackson-tensor-extraction; [xref-dangling] lem:jackson-tensor-extraction lem:jackson-tensor-extraction: \\cref{obj:synth_17} is not a statement-uses dependency of lem:jackson-tensor-extraction; [xref-missing-assumption] lem:jackson-tensor-extraction lem:jackson-tensor-extraction: depends on ass:fixed-overlap (statement-uses) but never references \\cref{obj:ass:fixed-overlap}; [xref-dangling] prop:equal-propensity-l1-reduction prop:equal-propensity-l1-reduction: \\cref{obj:synth_6} is not a statement-uses dependency of prop:equal-propensity-l1-reduction`
- The latest layer, promotion graph, synthesized definitions, proof files, and content-keyed caches remain persisted. No pipeline code or prompt was edited.
- Exact resume command from `CausalSmith/tools/`: `source scripts/node_env.sh && npx tsx bin/causalsmith.ts present stat_discrete_optimal_value_minimax_matched jackson_factorial --resume`.
- Durable cap log: `<workspace>/_orch_logs/mill-w09_stat_discrete_optimal_value_minimax_matched_jackson_factorial_present_p2_promote_again_20260908T164121Z.log`.

## P1 re-entry after promotion-round-2 pipeline repair

- Re-entered P1 from the preserved cache under the current P-stage code, without deleting any artifact and without `--refresh-frozen-bodies`.
- The Lean-aware equivalence pass converged and persisted seven newly faithful promoted-node bodies. The dense-construction repair was re-audited against its declaration-local Lean scope and the final cache verdict is faithful.
- Checkpoint review found that dependency ordering had moved the Jackson estimator, dense construction, and pilot-control lemma into Setup. Following the P1 rule that a bad move means a bad notation home, corrected the homes for the full-data law, observed atom coordinates, Jackson degree and polynomial evaluation variable, dense-law parameters, tensor convolution, and centered factorial-lift variables; no environment was hand-reordered.
- The 21 `xref-missing` advisories are accepted only where the dependency is already defined globally and unambiguous; the notation cycles and result-home advisory remain subject to the cache-preserving P1 recheck after the home corrections.

## P1 ordering pipeline-bug escalation

- Cache-preserving replay after the home corrections converged in three iterations with all judged environments faithful and only advisories, but reproduced the same section-hoisting defect: `def:jackson-factorial-estimator`, `def:dense-moment-matching-construction`, `lem:jackson-convolution-modulus`, and `lem:centered-factorial-pilot-control` remain in Setup, while the analytic and lower-bound appendices have lost those prerequisites.
- Suspected cause: `tools/src/presentation/p1_order.ts:222-244`. `sectionObjs` reconstructs `origIndex` from the already-rewritten live `outline.md` and then assigns `min(own, following)`, so environments can only migrate earlier and a later corrected notation home can never restore them to their authored section. The mutated output is trusted as the original section baseline on every `--from P1` replay.
- Minimal reproduction from `CausalSmith/tools/`: edit only the incorrect notation homes in the live `outline.md`, then run `source scripts/node_env.sh && npx tsx bin/causalsmith.ts present stat_discrete_optimal_value_minimax_matched jackson_factorial --from P1`; P1 reports `loop: converged in 3 iter(s)` and returns the outline checkpoint, but the four environments above remain under Setup.
- Verbatim convergence receipt: `[causalsmith P1] +405s review iter 3: 29 finding(s) (0 actionable) — clean`; `[causalsmith P1] +405s loop: converged in 3 iter(s); 30 advisory`; `[causalsmith P1] +406s Lean judge: all judged envs faithful (2 body/bodies frozen onto the graph)`.
- Durable replay log: `<workspace>/_orch_logs/mill-w09_stat_discrete_optimal_value_minimax_matched_jackson_factorial_present_fromP1_homefix_20260908T183500Z.log`. No files were deleted, no frozen bodies were refreshed, and no P-stage code or prompt was edited.

## P1 authored-section audit after section-baseline fix

- Independently compared all 36 graph-backed objects in the fixed re-entry's `home_objs:` baseline with their resolved `objs:` section. All 36 occur exactly once, but seven are in the wrong authored section: `def:jackson-kernel`, `def:jackson-factorial-estimator`, and `def:l1-embedding` moved from Main results to Setup and assumptions; `lem:jackson-tensor-extraction`, `lem:jackson-convolution-modulus`, and `lem:centered-factorial-pilot-control` moved from Appendix: Analytic ingredients for the upper bound to Setup and assumptions; and `def:dense-moment-matching-construction` moved from Appendix: Moment matching and lower-bound details to Setup and assumptions.
- This is not a within-section prerequisite reorder. It bunches estimator, appendix, and lower-bound environments into Setup, contradicting both the authored section briefs and the operator's checkpoint requirement. The P1 checkpoint is therefore not approved and P2 was not resumed.
- Current code evidence: `tools/src/presentation/p1_order.ts:195-219` computes a single flat repaired order and assigns each graph environment `min(own, following)` at lines 202-210, explicitly changing its section when a dependency repair moved it earlier. `tools/src/presentation/stages/p1_plan.ts:1083-1086` feeds that flattened order into `sectionObjs` and persists the reassignment as `objs:`. The fixed `home_objs:` re-entry baseline at `p1_order.ts:222-228` now recovers authored homes, but the later `sectionObjs` pass still discards them for these seven objects.
- Minimal reproduction requires no rerun and no model call: in the current bundle run `awk`/a parser over `outline.md`, map every graph id on `home_objs:` to its section and compare it with the same id on `objs:`. The comparison reports 36 authored graph objects, 36 resolved graph objects, and the seven mismatches listed above. Re-running P1 is prohibited by the stop rule because this fixed re-entry already reproduced the defect.
- No artifact was deleted, no frozen body was refreshed, and no pipeline or prompt file was edited.
