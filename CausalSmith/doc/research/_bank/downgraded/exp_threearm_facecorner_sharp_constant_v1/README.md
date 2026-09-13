---
qid: exp_threearm_facecorner_sharp_constant
spec: v1
topic: "Exact three-arm face/corner second-order minimax constant and allocation frontier for binary finite-population contrasts. For arbitrary binary complete schedules and every assignment law independent of them, compare unrestricted minimax squared-error risk with iid q*=(1/2,1/4,1/4) for contrast (1,-1/2,-1/2). Prove both deficits from 1/n converge after n^(4/3) scaling to the same explicit Airy constant; derive the arm-labelled stratified face/corner decision experiment from the exact eight-type orbit game; and construct matching finite-n estimators and complete-schedule priors. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the eight-type tangent program yields V(theta,eta)=max(|theta|/2,|eta|/4), a half-wedge Airy operator, a label-preserving half-effect prior, and an allocation-regularizing broad-prior mixture; exact arithmetic reproduces the n=3 label gap. UNRESOLVED BOTTLENECK: close the singular eta=0 experiment and finite-orbit bridge with uniform upper/lower remainders. EARLY KILL TEST: verify the posterior-target coefficient and uniform allocation square completion. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_threearm_facecorner_sharp_constant.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The advertised uniform singular face/corner experiment bridge remains open; the delivered result is the global sharp value expansion and local iid allocation frontier for one fixed three-arm contrast."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The note proves matched global second-order minimax expansions through a schedule-uniform estimator and an all-design Bayes lower bound, but it does not prove the stronger fiberwise liminf/recovery comparison posed in oeq:uniform-singular-bridge; the framing accurately leaves that comparison open."
  - "The contribution is confined to one labelled three-arm contrast and common bounded outcome intervals, with no general multi-arm characterization or substantive application demonstrating the practical magnitude of the second-order gain."
  - "The package remains confined to one fixed three-arm contrast and does not present the advertised exact n=3 label-gap computation or numerical finite-sample certificates, limiting its significance for a leading econometrics journal."
reusable_artifacts:
  - "discovery/core.json — audited graph for the global sharp Airy-value expansion, bounded endpoint transfer, local iid allocation frontier, and corrected orbit symmetrization."
  - "discovery/solve_thm_sharp_face_corner_expansion.json — retained sharp-constant proof attempt and construction details."
  - "discovery/solve_thm_local_allocation_frontier.json — corrected allocation-frontier argument, including the unbounded non-divergent subsequence case."
  - "discovery/solve_thm_bounded_local_allocation_frontier_corollary.json — bounded-outcome endpoint-transfer specialization."
seeds_burned: []
proof_attempt_summary: |
  The run derived and repeatedly audited a common global second-order Airy constant, matching schedule-uniform and all-design Bayes bounds, exact bounded-endpoint transfer, and the local iid allocation frontier. It repaired the Airy remainder, Van Trees dependency, allocation subsequence case, and assignment-conditioned orbit symmetrization, leaving the resulting global value package mathematically sound. The promised uniform fiberwise face/corner experiment bridge remains open, so the fixed-contrast result did not clear the field novelty floor and was banked at subfield.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21635289
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21635289
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_threearm_facecorner_sharp_constant / v1 — Downgraded

**Topic.** Exact three-arm face/corner second-order minimax constant and allocation frontier for binary finite-population contrasts. For arbitrary binary complete schedules and every assignment law independent of them, compare unrestricted minimax squared-error risk with iid q*=(1/2,1/4,1/4) for contrast (1,-1/2,-1/2). Prove both deficits from 1/n converge after n^(4/3) scaling to the same explicit Airy constant; derive the arm-labelled stratified face/corner decision experiment from the exact eight-type orbit game; and construct matching finite-n estimators and complete-schedule priors. PRESOLVE EVIDENCE REQUIRING VERIFICATION: the eight-type tangent program yields V(theta,eta)=max(|theta|/2,|eta|/4), a half-wedge Airy operator, a label-preserving half-effect prior, and an allocation-regularizing broad-prior mixture; exact arithmetic reproduces the n=3 label gap. UNRESOLVED BOTTLENECK: close the singular eta=0 experiment and finite-orbit bridge with uniform upper/lower remainders. EARLY KILL TEST: verify the posterior-target coefficient and uniform allocation square completion. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_threearm_facecorner_sharp_constant.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: tier=subfield below floor=field and not salvageable in scope; final dependency-closure audit PASS, with the raw math objection adjudicated as notation ambiguity rather than a mathematical defect.

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
