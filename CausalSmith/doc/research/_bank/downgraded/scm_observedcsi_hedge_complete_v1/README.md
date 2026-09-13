---
qid: scm_observedcsi_hedge_complete
spec: v1
topic: "Complete state-specific identification under observed-context CSIs. In finite positive semi-Markovian DAGs, require every CSI activation variable to be observed and substitute the fixed treatment/outcome assignments before partitioning contexts. Construct a terminating sound-and-complete procedure returning either an arithmetic observed-cell formula for P_x(y), or a verified observed LC-certificate: an activation-refining partition, CSI-authorized deletion traces, SUCCESS ID-Qfunc derivations or OBSTRUCTION rooted C-forest pairs for every relevant c-component, and two global positive algebraic CPT tables indexed by the input CSI row-equality quotient that induce the same P(V) but different queries. Prove global shared-row gluing, total formula recovery or a genuine forest obstruction, and finite complexity; generic real-algebraic decision without the context/C-forest characterization does not count. Use Chen-Darwiche 2026, Tikka et al. 2019, and Mokhtarian et al. 2022 as anchors, and Y0 as the software consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The observed-context restriction removes an exact hidden-activation obstruction. Global CSI CPT rows reduce to connected equality classes, and fixed-nuisance binary-sink countermodels reduce exactly to a rational row-space/nullspace test. Two positive rational examples were checked, with query gaps 1/30 and 3/200. Active pruning, shared-row identification, cancellation, positive denominators, fixed cardinalities, and empty-trace decoration were attacked; saturated local-forest reasoning fails, but the literal partial-trace/global-witness certificate survives. UNRESOLVED BOTTLENECK: Prove the finite global context-factor dichotomy: exhaustive sound reductions must yield a total arithmetic formula or partial-trace rooted-forest obstructions admitting jointly positive shared-row countermodels, without the forests becoming merely decorative generic algebraic witnesses. EARLY KILL TEST: Reproduce the five-node active-deletion example where the pruned graph has no hedge but the empty trace has one, then test a local bow whose target becomes identified through an observed reference context; failure to reject the false local countermodel, or inability to link the surviving forest to query separation, forces a pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_observedcsi_hedge_complete.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The advertised complete state-specific identification procedure is not delivered: the theorem that would make the finite search exhaustive and complete is explicitly left open."
  - "The binary-sink results prove only that an already accepted row-space certificate is sound; they do not show that every unidentified query in that slice produces such a certificate."
  - "The two rational examples validate boundary behavior but do not establish a general forest-to-obstruction characterization."
reusable_artifacts:
  - discovery/solve_oeq_global_context_factor_dichotomy.json
  - discovery/solve_thm_binary_sink_certificate_soundness.json
  - discovery/solve_prop_adversarial_trace_boundaries.json
  - discovery/solve_thm_root_control_class_bridge.json
  - discovery/core.json
seeds_burned: []
proof_attempt_summary: |
  The run replaced a circular countermodel certificate with a graph/CSI-derived
  affine nullspace construction and established a sound fixed-nuisance binary-sink
  slice, positive rational witnesses, and a careful observed-root comparator bridge.
  It did not prove that residual forests always yield a jointly positive shared-row
  kernel direction, nor the converse recovery theorem needed for total termination.
  Local SUCCESS-grammar and activation-cell defects remain repairable, but repairing
  them would not lift the achieved incremental result to the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 18967795
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 18967795
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# scm_observedcsi_hedge_complete / v1 — Downgraded

**Topic.** Complete state-specific identification under observed-context CSIs. In finite positive semi-Markovian DAGs, require every CSI activation variable to be observed and substitute the fixed treatment/outcome assignments before partitioning contexts. Construct a terminating sound-and-complete procedure returning either an arithmetic observed-cell formula for P_x(y), or a verified observed LC-certificate: an activation-refining partition, CSI-authorized deletion traces, SUCCESS ID-Qfunc derivations or OBSTRUCTION rooted C-forest pairs for every relevant c-component, and two global positive algebraic CPT tables indexed by the input CSI row-equality quotient that induce the same P(V) but different queries. Prove global shared-row gluing, total formula recovery or a genuine forest obstruction, and finite complexity; generic real-algebraic decision without the context/C-forest characterization does not count. Use Chen-Darwiche 2026, Tikka et al. 2019, and Mokhtarian et al. 2022 as anchors, and Y0 as the software consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The observed-context restriction removes an exact hidden-activation obstruction. Global CSI CPT rows reduce to connected equality classes, and fixed-nuisance binary-sink countermodels reduce exactly to a rational row-space/nullspace test. Two positive rational examples were checked, with query gaps 1/30 and 3/200. Active pruning, shared-row identification, cancellation, positive denominators, fixed cardinalities, and empty-trace decoration were attacked; saturated local-forest reasoning fails, but the literal partial-trace/global-witness certificate survives. UNRESOLVED BOTTLENECK: Prove the finite global context-factor dichotomy: exhaustive sound reductions must yield a total arithmetic formula or partial-trace rooted-forest obstructions admitting jointly positive shared-row countermodels, without the forests becoming merely decorative generic algebraic witnesses. EARLY KILL TEST: Reproduce the five-node active-deletion example where the pruned graph has no hedge but the empty trace has one, then test a local bow whose target becomes identified through an observed reference context; failure to reject the false local countermodel, or inability to link the surviving forest to query separation, forces a pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_observedcsi_hedge_complete.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The advertised complete state-specific identification procedure is not delivered: the theorem that would make the finite search exhaustive and complete is explicitly left open.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

<!-- Free-form context: what makes this entry interesting, what should be
re-derived vs. re-used, links to follow-on runs. Fill in by hand after the
scaffold is generated. -->
