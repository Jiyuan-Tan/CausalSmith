---
qid: scm_signedtransport_switchbudget_bounds
spec: v1
topic: "Graph-budget sharp counterfactual envelopes under bounded failures of context-independent inverse transport. Fix a finite-horizon shared-order scalar triangular SCM on a finite parent-context grid, mutually independent uniform ranks, rational continuous strictly increasing piecewise-affine conditional quantiles, rational-box factual evidence, and bounded rational piecewise-polynomial payoff. Put an orientation gate on every reachable mechanism-context cell; connect grid-neighbor cells in H and impose TV_H(s)≤K. Characterize attained sharp endpoint hulls for the conditional intervention payoff, zero-budget point recovery, nesting, exact Boolean-polynomial/polyhedral-integration computation with complexity or hardness bounds, and simultaneous DKW-projection inference. Report the smallest K changing each DoFlow or CausalSim decision without claiming K is identified. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Common factual ranks reduce each counterfactual reflection to products of factual and rollout orientation gates. Integrating the rational piecewise model gives an orientation-independent Boolean polynomial of degree at most twice the number of nonintervened mechanisms; an augmented factor graph then supports budgeted tree-decomposition optimization. Exact checks recovered the two-context sign-flip envelope and four-cell path endpoint pairs (-1/5,-1/5), (-1/5,2/5), (-3/10,2/5), and (-3/10,1/2) for K=0,1,2,3. Destructive checks covered disconnected graphs, non-strict nesting, changing downstream contexts, cycles, vacuous unconditional queries, ineffective encodings, zero cells, and small evidence probabilities; no matching literature collision surfaced. UNRESOLVED BOTTLENECK: Prove a terminating certified DKW outer-projection algorithm that preserves shared quantile reuse, changing context cells, payoff discontinuities, and the conditioning denominator, and contracts pointwise to the sharp endpoints. EARLY KILL TEST: Compare enumeration, polynomial compilation, and shrinking DKW enclosures on the four-cell witness and a two-stage rational example with a context switch and threshold payoff; excluded exact values or persistent noncontraction require pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_signedtransport_switchbudget_bounds.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - >-
    Exact finite rational grids, quantile splines, and payoffs are instrumental symbolic restrictions, and “externally validating” exact membership is not a credible real-data justification; either frame the work strictly as exact computation for supplied symbolic SCMs or add a quantified approximation/misspecification transfer.
  - >-
    The fiber constrains sup_x|F'_v-\widehat F_v| for every cell although \widehat F_v is undefined when n_v=0; define an empty-cell convention making that constraint explicitly vacuous.
  - >-
    “Relevant true-law cell” is not defined; replace it with an explicit set such as \mathcal V_+(Q)=\{v:P_{obs}(Q)(c_v)>0\} and state the convergence event over that set.
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/gaps.json
  - reviews/angle0_v6.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Discovery produced a field-rated exact symbolic SCM proposal with a repaired primitive orientation characterization, a legal four-cell path witness and complete endpoint enumeration, a typed alternative-law fiber, stagewise DKW conditioning, and a theorem-by-theorem novelty audit. Six D-0.5 revisions exhausted the cap because the reviewer continued to require either stricter supplied-symbolic-input framing or a new approximation/misspecification transfer theorem; the latter would materially expand the fixed topic. No derivation or Lean formalization began, and the remaining empty-cell and positive-visitation definitions are explicitly preserved as local retry work.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 39569698
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 39569698
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# scm_signedtransport_switchbudget_bounds / v1 — Downgraded

**Topic.** Graph-budget sharp counterfactual envelopes under bounded failures of context-independent inverse transport. Fix a finite-horizon shared-order scalar triangular SCM on a finite parent-context grid, mutually independent uniform ranks, rational continuous strictly increasing piecewise-affine conditional quantiles, rational-box factual evidence, and bounded rational piecewise-polynomial payoff. Put an orientation gate on every reachable mechanism-context cell; connect grid-neighbor cells in H and impose TV_H(s)≤K. Characterize attained sharp endpoint hulls for the conditional intervention payoff, zero-budget point recovery, nesting, exact Boolean-polynomial/polyhedral-integration computation with complexity or hardness bounds, and simultaneous DKW-projection inference. Report the smallest K changing each DoFlow or CausalSim decision without claiming K is identified. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Common factual ranks reduce each counterfactual reflection to products of factual and rollout orientation gates. Integrating the rational piecewise model gives an orientation-independent Boolean polynomial of degree at most twice the number of nonintervened mechanisms; an augmented factor graph then supports budgeted tree-decomposition optimization. Exact checks recovered the two-context sign-flip envelope and four-cell path endpoint pairs (-1/5,-1/5), (-1/5,2/5), (-3/10,2/5), and (-3/10,1/2) for K=0,1,2,3. Destructive checks covered disconnected graphs, non-strict nesting, changing downstream contexts, cycles, vacuous unconditional queries, ineffective encodings, zero cells, and small evidence probabilities; no matching literature collision surfaced. UNRESOLVED BOTTLENECK: Prove a terminating certified DKW outer-projection algorithm that preserves shared quantile reuse, changing context cells, payoff discontinuities, and the conditioning denominator, and contracts pointwise to the sharp endpoints. EARLY KILL TEST: Compare enumeration, polynomial compilation, and shrinking DKW enclosures on the four-cell witness and a two-stage rational example with a context switch and threshold payoff; excluded exact values or persistent noncontraction require pivot or stop. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_signedtransport_switchbudget_bounds.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 revision cap 6 exhausted: exact-rational applicability objection repeated after certified-surrogate scoping; remaining empty-cell and positive-visitation definitions are local, with no distinct in-scope root repair.

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
