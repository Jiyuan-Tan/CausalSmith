---
qid: pid_mot_highdim_minimax_frontier
spec: v1
topic: "Exact high-dimensional multiworld transport risk and honest endpoint length. In a balanced K=K_N arm triangular array with total N, m=N/K observations per arm and m→∞, fixed d>4, and arbitrary arm marginals supported on the Euclidean unit ball, let L(P)=K^(-2) inf over all K-couplings of E||sum_k Z_k||². Determine the exact all-K minimax absolute-error rate and the minimax expected excess length of uniformly honest one-sided lower confidence bounds, proving matching all-estimator lower bounds and a computable empirical-MOT/dual-certificate procedure; expose every K and logarithmic transition rather than assuming the published plug-in rate. Preserve L as a second-moment endpoint, not the centered variance endpoint. Include the legal K=3,d=5 hypercube parity witness and audit Gao–Ge–Qian's STAR scholarship-incentive plug-in tightening under declared scaling or balanced subsampling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: randomized extreme-point marginal-preserving rounding derives sup_P K²[L(P)−||average marginal means||²]=min(K,d); arbitrary-subset optimal-support exchanges plus vector balancing give sum-support diameter at most 2√min(K,d), supporting the improved upper N^(-1/2)+min{min(K,d)/K²,C_d K^(-1)(N/K)^(-2/d)} and proving root-N minimax estimation and honest one-sided excess length for K≳N^(1/4). Finite MOT and rounding checks found no counterexample; two-margin embeddings, joint mixability, Bernoulli knots, and fixed-d orthogonal saturation were tested. UNRESOLVED BOTTLENECK: settle aggregate complexity of the K dual potentials by a simultaneous-marginal indistinguishable family whose endpoint separation survives every rematching, or prove a sharper shared-geometric upper bound; this must also resolve the fixed-K logarithmic gap and honest one-sided converse. EARLY KILL TEST: reconstruct the geometric and interpolation lemmas, then certify K=3,…,8,d=5 hard families against every rematching column; a counterexample kills the upper mechanism, while failure of both a matching lower construction and sharper aggregate bound leaves the full-frontier claim unfinished. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_mot_highdim_minimax_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proposed exact all-K minimax and honest-length frontier is not derived: this node leaves the small-ratio rate functions, simultaneous all-rematching lower family, and ordered converse open, while the core proves only the positive-lower-ratio root-N region."
  - "Prove a simultaneous-arm indistinguishability lower bound matching the improved upper rate throughout the ratio-to-zero regime, including the exact fixed-K logarithms and an ordered version yielding the matching honest one-sided excess-length converse."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_dimension_dependent_root_n_frontier.json
  - discovery/solve_thm_certified_computation.json
  - discovery/solve_oeq_exact_all_k_frontier.json
  - discovery/solve_prop_hypercube_parity.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned: []
proof_attempt_summary: |
  D0 proved the sharp residual envelope and optimal-sum-diameter geometry, a
  dimension-dependent root-N region, honest mean/plugin lower bounds, and a rational
  certified finite-MOT procedure; the math referee accepted these claims and sources.
  Attempts via simultaneous-margin finite-support families, two-margin reductions,
  parity and orthogonal witnesses, and a sharper aggregate dual-process bound did not
  close the exact small-ratio frontier or its ordered one-sided converse. A future
  re-raise needs a genuinely new rematching-resistant lower family or shared-geometric
  upper theorem, not another reframe of the current partial package.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 37760678
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 37760678
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_mot_highdim_minimax_frontier / v1 — Downgraded

**Topic.** Exact high-dimensional multiworld transport risk and honest endpoint length. In a balanced K=K_N arm triangular array with total N, m=N/K observations per arm and m→∞, fixed d>4, and arbitrary arm marginals supported on the Euclidean unit ball, let L(P)=K^(-2) inf over all K-couplings of E||sum_k Z_k||². Determine the exact all-K minimax absolute-error rate and the minimax expected excess length of uniformly honest one-sided lower confidence bounds, proving matching all-estimator lower bounds and a computable empirical-MOT/dual-certificate procedure; expose every K and logarithmic transition rather than assuming the published plug-in rate. Preserve L as a second-moment endpoint, not the centered variance endpoint. Include the legal K=3,d=5 hypercube parity witness and audit Gao–Ge–Qian's STAR scholarship-incentive plug-in tightening under declared scaling or balanced subsampling. PRESOLVE EVIDENCE REQUIRING VERIFICATION: randomized extreme-point marginal-preserving rounding derives sup_P K²[L(P)−||average marginal means||²]=min(K,d); arbitrary-subset optimal-support exchanges plus vector balancing give sum-support diameter at most 2√min(K,d), supporting the improved upper N^(-1/2)+min{min(K,d)/K²,C_d K^(-1)(N/K)^(-2/d)} and proving root-N minimax estimation and honest one-sided excess length for K≳N^(1/4). Finite MOT and rounding checks found no counterexample; two-margin embeddings, joint mixability, Bernoulli knots, and fixed-d orthogonal saturation were tested. UNRESOLVED BOTTLENECK: settle aggregate complexity of the K dual potentials by a simultaneous-marginal indistinguishable family whose endpoint separation survives every rematching, or prove a sharper shared-geometric upper bound; this must also resolve the fixed-K logarithmic gap and honest one-sided converse. EARLY KILL TEST: reconstruct the geometric and interpolation lemmas, then certify K=3,…,8,d=5 hard families against every rematching column; a counterexample kills the upper mechanism, while failure of both a matching lower construction and sharper aggregate bound leaves the full-frontier claim unfinished. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_mot_highdim_minimax_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The exact all-K minimax and honest-length frontier is not derived: the small-ratio rates, simultaneous all-rematching lower family, and ordered converse remain open, while the sound core proves only the positive-lower-ratio root-N region.

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
