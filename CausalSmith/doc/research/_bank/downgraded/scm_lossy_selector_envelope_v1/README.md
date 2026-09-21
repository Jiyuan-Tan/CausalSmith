---
qid: scm_lossy_selector_envelope
spec: v1
topic: "Calibrated selector envelopes for lossy causal abstractions. Let C be a finite pre-treatment context and X a finite micro-action in the fiber of macro intervention h. Assume p(c)>0, aggregate implementation shares r(x)>0, and Bernoulli micro-interventional means mu(c,x) are identified, but joint deployment logs are unavailable. The macro implementation uses independent selector noise with unknown s(x|c), and gamma(c,x)=p(c)s(x|c) has margins p and r. Prove that the compatible macro mean set is exactly {sum gamma(c,x)mu(c,x): gamma has margins p,r}; construct one common finite response SCM and compatible residual projection realizing every gamma in this explicitly free-selector Definition-6 class. Compute endpoints by min/max-cost flow, prove point identification iff all alternating mu contrasts vanish on the effective support graph, and return endpoint SCM selector certificates. With fixed finite support and positive margins, derive joint directional derivatives and pointwise simultaneous numerical-delta inference when p,r,mu are estimated together and optimal faces may be nonunique. Explicitly exclude the stronger claim that all selectors preserve one fixed canonical Equation-11 L3 map. Consumer: the Béal-Latouche PDX precision-medicine analysis when a target deployment provides tumor-profile frequencies and aggregate drug shares but not their joint allocation; report whether superiority to its control remains uniform over the sharp interval. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh derivation obtained the exact selector-mixture formula, a common Bernoulli-response SCM realizing every margin-compatible coupling through independent selector noise, a structural compatible-residual projection, endpoint attainment, and the effective-support alternating-cycle iff. For the equal-margin two-context witness it derived theta(t)=1/4+(6/5)t on 0<=t<=1/2, hence the sharp interval [1/4,17/20]. Both endpoints and a nonunique-face derivative check were recomputed numerically; 13,824 finite residual/intervention diagrams satisfied the structural compatibility identity. Destructive checks separated this free-selector Definition-6 class from the stronger fixed canonical Equation-11 L3 map, handled forced-zero support edges, and found no exact query collision. Generic transport optimization and estimated-cost directional inference are acknowledged supporting machinery. UNRESOLVED BOTTLENECK: Complete the conditional numerical-delta convergence proof for simultaneous pointwise endpoint inference when margins and micro-response means are jointly estimated and both primal and dual optimal faces are nonunique. EARLY KILL TEST: Encode both endpoint selectors in the two-context, three-action partial-projection model and verify every Definition-6 structural diagram, then compute the common baseline canonical Equation-11 selector; pivot if the intended class requires both endpoints to preserve that one fixed canonical L3 map. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_lossy_selector_envelope.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The core delivers the standard finite transport image and selector-by-selector SCM attainment, but omits the proposal-headlined effective-support alternating-cycle point-identification iff and endpoint flow-certificate theorem; its own honest scope confirms this weaker kernel."
  - "The flagship negative result targets a note-defined Hong--Li-style implementation rather than a specifically identified published estimator/workflow, and its sole witness has collapsing response variance with no nondegenerate observable-law or perturbation-stable generic-class certificate; this is a novelty revise with a subfield ceiling."
  - "The exact selector interval is standard finite transportation geometry, while the SCM result only realizes that geometry inside the note's explicitly free, selector-specific abstraction class and does not preserve a common canonical Layer-3 map."
reusable_artifacts:
  - path: discovery/solve_thm_response_boundary_failure_bl_approximation.json
    kind: counterexample
    one_line: "A sound singleton triangular-array construction showing zero asymptotic coverage for the note-defined paired empirical-influence multiplier numerical-delta procedure under collapsing response variance."
  - path: discovery/core.json
    kind: lp_setup
    one_line: "The validated incremental graph for selector-specific SCM attainment, the standard finite transport image, directional LP sensitivity, and the projected primitive-confidence-region fallback."
seeds_burned: []
proof_attempt_summary: |
  The run attempted a field-level sharp selector-envelope and changing-support inference package. The effective-support cycle criterion and endpoint flow-certificate kernel were retracted when they were not discharged; the repaired incremental record instead retains sound selector-specific SCM attainment, standard transport geometry, and a sharp but boundary-degenerate zero-coverage diagnostic with an honest projection fallback. A future retry would need a response-interior uniform coverage theorem plus either a genuine rare-margin converse or a concrete comparative rate/width advantage.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 45797635
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 45797635
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# scm_lossy_selector_envelope / v1 — Downgraded

**Topic.** Calibrated selector envelopes for lossy causal abstractions. Let C be a finite pre-treatment context and X a finite micro-action in the fiber of macro intervention h. Assume p(c)>0, aggregate implementation shares r(x)>0, and Bernoulli micro-interventional means mu(c,x) are identified, but joint deployment logs are unavailable. The macro implementation uses independent selector noise with unknown s(x|c), and gamma(c,x)=p(c)s(x|c) has margins p and r. Prove that the compatible macro mean set is exactly {sum gamma(c,x)mu(c,x): gamma has margins p,r}; construct one common finite response SCM and compatible residual projection realizing every gamma in this explicitly free-selector Definition-6 class. Compute endpoints by min/max-cost flow, prove point identification iff all alternating mu contrasts vanish on the effective support graph, and return endpoint SCM selector certificates. With fixed finite support and positive margins, derive joint directional derivatives and pointwise simultaneous numerical-delta inference when p,r,mu are estimated together and optimal faces may be nonunique. Explicitly exclude the stronger claim that all selectors preserve one fixed canonical Equation-11 L3 map. Consumer: the Béal-Latouche PDX precision-medicine analysis when a target deployment provides tumor-profile frequencies and aggregate drug shares but not their joint allocation; report whether superiority to its control remains uniform over the sharp interval. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh derivation obtained the exact selector-mixture formula, a common Bernoulli-response SCM realizing every margin-compatible coupling through independent selector noise, a structural compatible-residual projection, endpoint attainment, and the effective-support alternating-cycle iff. For the equal-margin two-context witness it derived theta(t)=1/4+(6/5)t on 0<=t<=1/2, hence the sharp interval [1/4,17/20]. Both endpoints and a nonunique-face derivative check were recomputed numerically; 13,824 finite residual/intervention diagrams satisfied the structural compatibility identity. Destructive checks separated this free-selector Definition-6 class from the stronger fixed canonical Equation-11 L3 map, handled forced-zero support edges, and found no exact query collision. Generic transport optimization and estimated-cost directional inference are acknowledged supporting machinery. UNRESOLVED BOTTLENECK: Complete the conditional numerical-delta convergence proof for simultaneous pointwise endpoint inference when margins and micro-response means are jointly estimated and both primal and dual optimal faces are nonunique. EARLY KILL TEST: Encode both endpoint selectors in the two-context, three-action partial-projection model and verify every Definition-6 structural diagram, then compute the common baseline canonical Equation-11 selector; pivot if the intended class requires both endpoints to preserve that one fixed canonical L3 map. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_lossy_selector_envelope.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Final math referee PASS established a sound incremental record, but delivered tier=incremental is below floor=field and paper_score_ceiling 4.3 < 7.4; the original cycle/flow-certificate kernel remains unfulfilled.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The final D0.5 math referee passed with no findings after bounded repair commit
`199cbd02a2c0709840970c298801edd352a1c51b2b1eca72ee65b8eb7bc87f11`.
The remaining decision findings concern proposal faithfulness and novelty, not
the correctness of the retained incremental claims. No formalization stage ran.
