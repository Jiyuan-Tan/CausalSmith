---
qid: stat_welfare_budgeted_width_frontier
spec: v2
topic: "Corrected gap-sensitive welfare-budgeted honest-width envelope for the targeting gain in an adaptive contextual experiment. Fix delta in (0,1/4), the Hölder-margin class, a P-independent benchmark policy, and the participant-welfare budget. Define W_{T,delta}(rho) over all non-anticipating designs and all honest interval procedures. Determine the complete frontier up to constants with a procedure-free converse and an attaining adaptive design/interval; optimize fixed-gap and Hölder-local subclasses, retain the compulsory rho^(-1/2) obstruction, and derive rather than assume all other branches, feasibility boundaries, and flattening thresholds. Exact formulas remain answer-open. PRESOLVE EVIDENCE REQUIRING VERIFICATION: packed bumps suggest feasibility T^(1-p), oracle width T^(-q), and a fixed-gap rho^(-1/2) branch. UNRESOLVED BOTTLENECK: a uniform budget-saturating exploration lemma. EARLY KILL TEST: the d=1,beta=1,alpha=1/5 Gaussian construction near rho=T^(3/5)."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Accepted proposal promised the complete field-tier Hölder-margin frontier, all phase transitions, and an attaining law-independent adaptive design/connected honest interval; the result proved only the fixed-gap rho^-1/2 edge and a necessary baselinewise occupation lower relaxation, leaving the central explicit-rate, saturation, and realization claims open."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised complete Hölder--margin width frontier is replaced by an implicit one-sided occupation-relaxation lower bound: no explicit full-class branches or thresholds, and no law-independent attaining design and honest interval, are delivered."
  - "The suggested saturation/common-realization upgrade restates the unresolved kernel and supplies no concrete proof route for d=1, beta=1, alpha=1/5, rho proportional to T^(3/5)."
reusable_artifacts:
  - "discovery/core.json: baseline-indexed occupation-measure relaxation, its weak dual, the coverage-to-information converse, and target-separating Gaussian bump family."
  - "discovery/solve_thm_fixed_gap_frontier.json: exact fixed-gap rho^(-1/2) honest-width edge and its adaptive construction."
  - "discovery/solve_oeq_complete_width_frontier.json: attempted full-frontier proof and the unresolved saturation/common-realization boundary."
  - "state.json: accepted proposal, literature map, seed ranking, and primary-source verification receipts."
seeds_burned:
  - index: 0
    one_liner: "seed:complete-honest-width-frontier"
    reason: "The selected complete-honest-width-frontier angle exhausted three D0 solve rounds; its proposed saturation/common-realization upgrade restated the unresolved kernel without a concrete proof route for the mandatory d=1, beta=1, alpha=1/5, rho proportional to T^(3/5) case."
proof_attempt_summary: |
  The run proved two-direction exposure, class nonemptiness, an all-design
  coverage-to-information converse, the fixed-gap rho^(-1/2) frontier, and a
  rigorous baseline-indexed occupation lower relaxation. It failed because the
  promised full Hölder--margin rate, phase transitions, saturation, and one
  law-independent attaining design with a connected honest interval remained
  open; the required early-kill regime had no concrete proof route.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 69455378
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# stat_welfare_budgeted_width_frontier / v2 — Failed

**Topic.** Corrected gap-sensitive welfare-budgeted honest-width envelope for the targeting gain in an adaptive contextual experiment. Fix delta in (0,1/4), the Hölder-margin class, a P-independent benchmark policy, and the participant-welfare budget. Define W_{T,delta}(rho) over all non-anticipating designs and all honest interval procedures. Determine the complete frontier up to constants with a procedure-free converse and an attaining adaptive design/interval; optimize fixed-gap and Hölder-local subclasses, retain the compulsory rho^(-1/2) obstruction, and derive rather than assume all other branches, feasibility boundaries, and flattening thresholds. Exact formulas remain answer-open. PRESOLVE EVIDENCE REQUIRING VERIFICATION: packed bumps suggest feasibility T^(1-p), oracle width T^(-q), and a fixed-gap rho^(-1/2) branch. UNRESOLVED BOTTLENECK: a uniform budget-saturating exploration lemma. EARLY KILL TEST: the d=1,beta=1,alpha=1/5 Gaussian construction near rho=T^(3/5).

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The promised complete Hölder–margin width frontier was replaced by an implicit one-sided occupation-relaxation lower bound: no explicit full-class branches or thresholds, and no law-independent attaining design and honest interval, are delivered.

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
