---
qid: stat_minimax_annealed_assignment
spec: v1
topic: "Solve minimax annealed causal assignment with known target-population cell masses and capacity, lambda_n=kappa/sqrt(n), and a fixed-dimensional Gaussian contact experiment. Characterize the scalar reverse-KL minimax rule, its least-favorable prior, strict plug-in risk gap, certified computation, and temperature limits. Then solve the weighted multivariate capacity problem by recursive exposed-face Gaussian experiments, proving compatible minimax maps, polynomial certified risk/map approximation, and strict separation from coordinatewise linear-logit shrinkers. Finally derive the observed-data causal LAN lower bound and an exactly capacity-feasible cross-fitted learner with estimated covariance, expanding-local attainment, and honest policy/welfare confidence sets. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent presolve derived the scalar posterior-Bayes identity delta(z)=expit(E[H|Z=z]/kappa), nonrandomized minimax existence, essential uniqueness, symmetry, monotonicity, strict shrinkage, and a proper least-favorable prior whose support must be locally finite, countably infinite, and unbounded in both directions. Interval calculations certify that at kappa=1 the plug-in worst risk exceeds that of expit(0.8Z) by more than 0.0141. It also derived projected Gaussian experiments on every exposed capacity face, lower bounds from face risks, and an upper bound forcing risk to vanish with residual capacity. The corrected four-arm Bernoulli path has Fisher information one, and known target masses make exact population capacity feasible. UNRESOLVED BOTTLENECK: Prove compatible minimax extensions across nested exposed faces, essential multivariate uniqueness, polynomial certified value and expected-KL map recovery, strict separation from every common positive scaling, and covariance-stable expanding-local causal attainment. EARLY KILL TEST: Solve the three-cell equal-mass, half-capacity problem with contact covariance diag(1,4), certify all six edge extensions, and test normal rays, tangential offsets, and near-wall directions; pivot if face limits are incompatible or the coupled optimum lies in the declared diagonal class. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_minimax_annealed_assignment.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "The final proposal was mathematically clean and field-tier but failed D-0.5 because its survey omitted and did not distinguish the directly relevant Bhattacharya-Dupas capacity-constrained assignment comparator."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "N-thin-survey — Add BhattacharyaDupas2012, a directly relevant published capacity-constrained treatment-assignment comparator identified in SunadaIzumi2025s related-work discussion, and distinguish its plug-in/inference target from the reverse-KL worst-risk game."
reusable_artifacts:
  - "discovery/proto_core.json — final framed Gaussian capacity geometry and theorem/OEQ specification"
  - "discovery/proposal.tex — final human-readable proposal"
  - "reviews/reviews.jsonl — six-round D-0.5 review and novelty record"
seeds_burned:
  - index: 0
    one_liner: "seed:face-compatible-global-minimax"
    reason: "Angle 0 exhausted six revisions and was explicitly given up after the second validity gate; further retry was unauthorized and switch would evade the cap."
proof_attempt_summary: |
  Six proposal revisions developed a framed Gaussian capacity geometry with explicit
  transported face experiments, a scalar reverse-KL saddle, compatible global-minimax
  obligations, a Helmert-framed three-cell certificate, and a causal LAN program. The
  final reviewer found no soundness or source-characterization defect and retained a
  field assessment, but returned NO-PASS for one unresolved survey-comparison omission;
  the authorized retry budget was exhausted, so no Lean formalization was attempted.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 32472226
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 32472226
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# stat_minimax_annealed_assignment / v1 — Failed

**Topic.** Solve minimax annealed causal assignment with known target-population cell masses and capacity, lambda_n=kappa/sqrt(n), and a fixed-dimensional Gaussian contact experiment. Characterize the scalar reverse-KL minimax rule, its least-favorable prior, strict plug-in risk gap, certified computation, and temperature limits. Then solve the weighted multivariate capacity problem by recursive exposed-face Gaussian experiments, proving compatible minimax maps, polynomial certified risk/map approximation, and strict separation from coordinatewise linear-logit shrinkers. Finally derive the observed-data causal LAN lower bound and an exactly capacity-feasible cross-fitted learner with estimated covariance, expanding-local attainment, and honest policy/welfare confidence sets. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent presolve derived the scalar posterior-Bayes identity delta(z)=expit(E[H|Z=z]/kappa), nonrandomized minimax existence, essential uniqueness, symmetry, monotonicity, strict shrinkage, and a proper least-favorable prior whose support must be locally finite, countably infinite, and unbounded in both directions. Interval calculations certify that at kappa=1 the plug-in worst risk exceeds that of expit(0.8Z) by more than 0.0141. It also derived projected Gaussian experiments on every exposed capacity face, lower bounds from face risks, and an upper bound forcing risk to vanish with residual capacity. The corrected four-arm Bernoulli path has Fisher information one, and known target masses make exact population capacity feasible. UNRESOLVED BOTTLENECK: Prove compatible minimax extensions across nested exposed faces, essential multivariate uniqueness, polynomial certified value and expected-KL map recovery, strict separation from every common positive scaling, and covariance-stable expanding-local causal attainment. EARLY KILL TEST: Solve the three-cell equal-mass, half-capacity problem with contact covariance diag(1,4), certify all six edge extensions, and test normal rays, tangential offsets, and near-wall directions; pivot if face limits are incompatible or the coupled optimum lies in the declared diagonal class. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_minimax_annealed_assignment.md

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 final verdict NO-PASS after angle 0 exhausted six revisions; remaining flag: N-thin-survey — Add BhattacharyaDupas2012 and distinguish its plug-in/inference target from the reverse-KL worst-risk game.

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
