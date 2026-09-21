---
qid: exp_heterovar_bae_dominance_frontier
spec: v1
topic: "Universal heteroskedastic dominance of late batched arm elimination: for every K>=3 and every finite positive known Gaussian variance vector, compare a fully specified proportional two-batch eliminate-one design with the variance-aware static allocation maximizing the worst equal-gap pair exponent; prove strict instancewise error-exponent improvement for every unique-best mean vector, compute C_h by one-dimensional piecewise-quadratic projections, eta=min_i w_i/(1-w_i), rho=(1+eta)/(C+eta), and gain G=C(1+eta)/(C+eta)>1, establish the exact finite-branch Gaussian exponent and matching elimination/terminal witnesses within the proportional family, and supply a conservative finite-T Chernoff certificate for successive-elimination software and heteroskedastic multi-arm fundraising experiments. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Presolve analytically derived C_h=min_{t>=0}[t^2/(2v_h)+sum_{j!=h}(sqrt(2(v_h+v_j))-t)_+^2/(2v_j)]>1, the lower-bound multiplier G, and whole-positive-orthant dominance; equal-variance, severe-imbalance, near-tie, K=2, and (1,1,4) regimes were checked, with the latter giving G approximately 1.044815499855. UNRESOLVED BOTTLENECK: Independently prove finite-branch Gaussian LDP equality and terminal-branch attainment showing G is the exact optimal worst-instance multiplier within the proportional two-batch family, including branch coupling and rounding. EARLY KILL TEST: Recompute the K=3 variance (1,1,4) best-elimination and terminal-comparison witnesses in exact algebraic arithmetic; stop if either contradicts the projection or coupling formula. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_heterovar_bae_dominance_frontier.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Promised universal heteroskedastic dominance at field tier, but delivered exact dominance and optimality only within the proportional top-m two-batch family; unrestricted allocation optimality remains open."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The exact exponent, matching worst-instance witnesses, timing optimum, and survivor-count optimization are proved only for the proportional top-m two-batch family relative to the variance-aware GNA static comparator; optimality over unrestricted first-stage and branch-specific allocations remains open."
  - "The finite-T result is only a mean-dependent union-bound certificate, not finite-sample dominance or a guarantee computable from known variances alone."
  - "The narrow known-Gaussian setting, absence of practical evaluation, and unresolved unrestricted-design saddle keep the package below flagship level and constrain its leading-econometrics-journal score."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - reviews/review_general.json
  - orchestrator/decision_log.jsonl
seeds_burned:
  - index: 0
    one_liner: "Exact finite-branch large deviations for a proportional two-batch eliminate-one rule"
    reason: "Angle 0 was maximized through a top-m extension; the remaining unrestricted multi-survivor saddle is a new research barrier, not a bounded repair."
proof_attempt_summary: |
  The run proved the exact finite-branch exponent and rounding invariance for proportional
  top-m two-batch designs, matching best-exclusion and terminal witnesses, optimal timing and
  survivor count, and the common-variance √K elbow with gain tending to two. The field-tier
  claim collapsed at unrestricted-design optimality: arbitrary first-stage and branch-specific
  allocations destroy the fixed projection geometry and scalar survivor-expansion converse.
  What remains is a new allocation-uniform saddle certificate or an exact superior
  nonproportional construction, rather than a bounded repair of the completed derivation.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 14645161
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 14645161
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# exp_heterovar_bae_dominance_frontier / v1 — Downgraded

**Topic.** Universal heteroskedastic dominance of late batched arm elimination: for every K>=3 and every finite positive known Gaussian variance vector, compare a fully specified proportional two-batch eliminate-one design with the variance-aware static allocation maximizing the worst equal-gap pair exponent; prove strict instancewise error-exponent improvement for every unique-best mean vector, compute C_h by one-dimensional piecewise-quadratic projections, eta=min_i w_i/(1-w_i), rho=(1+eta)/(C+eta), and gain G=C(1+eta)/(C+eta)>1, establish the exact finite-branch Gaussian exponent and matching elimination/terminal witnesses within the proportional family, and supply a conservative finite-T Chernoff certificate for successive-elimination software and heteroskedastic multi-arm fundraising experiments. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Presolve analytically derived C_h=min_{t>=0}[t^2/(2v_h)+sum_{j!=h}(sqrt(2(v_h+v_j))-t)_+^2/(2v_j)]>1, the lower-bound multiplier G, and whole-positive-orthant dominance; equal-variance, severe-imbalance, near-tie, K=2, and (1,1,4) regimes were checked, with the latter giving G approximately 1.044815499855. UNRESOLVED BOTTLENECK: Independently prove finite-branch Gaussian LDP equality and terminal-branch attainment showing G is the exact optimal worst-instance multiplier within the proportional two-batch family, including branch coupling and rounding. EARLY KILL TEST: Recompute the K=3 variance (1,1,4) best-elimination and terminal-comparison witnesses in exact algebraic arithmetic; stop if either contradicts the projection or coupling formula. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_heterovar_bae_dominance_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: exact proportional top-m frontier is sound and complete, but unrestricted first-stage and branch-specific allocation optimality remains open; paper_score_ceiling 6.7 < 7.4 field floor.

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
