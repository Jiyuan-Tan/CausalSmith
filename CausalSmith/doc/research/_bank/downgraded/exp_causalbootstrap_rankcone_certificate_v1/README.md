---
qid: exp_causalbootstrap_rankcone_certificate
spec: v1
topic: "Characterize the universal rank-preservation covariance boundary for least-favourable potential-outcome completion under balanced randomization, with the presolve capsule embedded in this queued entry."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The delivered oracle covariance classifications do not resolve polynomial recognition or sharp hardness for admissible nonexchangeable kernels, do not characterize binary-witness completeness/minimal alphabet, and do not provide feasible marginal estimation or coverage."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves an exact graph-Laplacian criterion for a prespecified scalarized oracle covariance loss and a two-opposite-columns classification for universal Loewner dominance under uniform fixed-count assignment."
  - "The practically broader nonexchangeable-kernel problem receives only factorial/exponential enumeration through generic copositivity tests, with recognition complexity and the witness alphabet left open."
  - "The package also assumes oracle knowledge of every armwise potential-outcome marginal and supplies neither feasible marginal estimation nor an inference or coverage theorem, limiting its econometric usefulness relative to the causal-bootstrap framing."
  - "Resolve the computational core of general-balanced-kernel: give a polynomial-time exact recognition algorithm for rational admissible balanced kernels, or a sharp hardness result paired with a nontrivial tractable subclass, and determine whether binary witnesses are complete."
reusable_artifacts:
  - "discovery/core.json — audited arbitrary-positive-count rank-cone iff, Loewner boundary, fixed-count covariance identity, and balanced-kernel copositivity graph"
  - "discovery/writeup.tex — synchronized mathematical derivation and Aronow–Green–Lee finite-design comparison"
  - "discovery/solve_thm_finite_copositivity_characterization.json — exact finite copositivity/eigenspace certificate construction for admissible balanced kernels"
  - "discovery/solve_oeq_general_balanced_kernel.json — attempted computational-core analysis and residual witness-alphabet obstruction"
  - "reviews/review_general.json — cold tier assessment, paper-score ceiling, and bounded-upgrade statement"
  - "orchestrator/decision_log.jsonl — PR adjudications, maximality audit, source normalization checks, and terminal receipts"
seeds_burned:
  - index: 0
    one_liner: "Graph-Laplacian rank cone and Loewner boundary"
    reason: "The graph-Laplacian/Loewner angle passed mathematics but remained incremental after maximal fixed-count strengthening; the field-tier computational and witness-completeness core stayed open."
proof_attempt_summary: |
  The run proved exact graph-Laplacian and Loewner classifications for uniform fixed-count multi-arm designs, including optional unassigned units, a sharp 2/N regret identity, binary necessity witnesses, and exact recovery of the finite Aronow–Green–Lee oracle design. It also reduced the nonexchangeable balanced-kernel branch to finite copositivity and exact algebraic certification. The field claim collapsed because this general branch still needs polynomial recognition or admissibility-preserving hardness, a tractable subclass, and binary-witness completeness or a least-alphabet theorem; feasible marginal estimation and coverage remain a separate statistical extension.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 59581051
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 59581051
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_causalbootstrap_rankcone_certificate / v1 — Downgraded

**Topic.** Characterize the universal rank-preservation covariance boundary for least-favourable potential-outcome completion under balanced randomization, with the presolve capsule embedded in this queued entry.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the sound package incremental below the field floor and found no bounded in-scope repair: the polynomial-recognition-or-sharp-hardness and binary-witness-completeness upgrades require genuinely new mathematics.

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
