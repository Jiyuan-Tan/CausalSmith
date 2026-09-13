---
qid: panel_ferrers_cholesky_frontier
spec: v1
topic: "Signal-aware oracle-adaptation modulus for dependent causal-panel completion on Ferrers masks. Observe one Gaussian rank-r panel Y=M+sigma L_N Z L_T' on a deterministic Ferrers mask with nonvanishing complete slabs, fixed-rank incoherent M, bounded slab Gram geometry, and unknown separable covariance whose inverse-Cholesky factors have bounded spectra and matched row-and-column polynomial tails. For a diffuse missing-cell causal target psi_W(M), define the truth-specific covariance-minimum tangent-balancing score and the minimax L2 distance from all feasible observed-data statistics to its oracle linearization. Derive a primitive target-sensitive necessary-and-sufficient adaptation condition retaining the unavoidable mean-tangent learning cost; construct an observable same-panel residual and tangent-balanced score, feasible variance calibration, and uniform Wald coverage on the adaptation region; and prove matching legal Gaussian lower experiments plus the non-oracle risk frontier outside it. Consumers are Ben-Michael and Feller's right-to-carry reanalysis and Choi-Yuan's SEC Tick Size Pilot analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An exact rank-one loading-class minimax theorem was derived: for post-period weights h, oracle-reproduction risk is comparable to sigma sqrt((||h||^2+1/m)/m) min(1,sigma/(a sqrt(n))); an observable unknown-signal tangent-balanced statistic attains it with feasible variance calibration. Exact known-separable-covariance profiling gives temporal information J=S_x P_T+S_b P_C and agrees with direct GLS checks below 1.2e-15. Matched-tail and paired-loading counterexamples were checked, while no published collision was verified. UNRESOLVED BOTTLENECK: Prove a primitive uniform target-sensitive L2 bound for the joint adaptive-score and rank-curvature remainder when both factor spaces and both nonparametric innovation factors are estimated from the same Ferrers panel, with a matching legal posterior-risk lower experiment. EARLY KILL TEST: On the half-by-half L mask with unknown rank-one row/time directions and unknown nonstationary exact-one-banded innovations, derive the same-panel residual-score remainder and matching posterior lower experiment for both one-period and full-rectangle averages; pivot if this requires supplied factor directions, an independent panel, or stronger covariance regularity. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ferrers_cholesky_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: REVISE
tier_at_derivation: NA
proposal_promise_gap: "Field-level novelty remained credible, but four D-0.5 revisions did not produce a mathematically well-posed selector/frontier/lower-experiment architecture."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The advertised observable criterion invokes derivative and covariant-Hessian norms defined only for the truth-indexed experiment Theta_q(P), g_q, and K_q, but gives no fitted experiment or formula that maps (tilde M_a, Chat_aq) to the required charts and norms; hence Crit_n and qhat are not fully specified measurable maps."
  - "Delta_P infimizes over every 0<=q_N<N and 0<=q_T<T, whereas the implemented selector searches only q_N<=floor(b_N/4), q_T<=floor(b_T/4); no assumption or theorem relates that restricted candidate set to the unrestricted frontier used on the right-hand side."
  - "The theorem and lower-product construction require a 'relative-interior sequence' and epsilon_leg(P,q)>0, but neither the ambient tail-class topology nor the relative-interior condition ensuring a positive legal radius is defined."
reusable_artifacts:
  - discovery/proto_core.json
  - discovery/proposal.tex
  - reviews/angle0_v1.json
  - reviews/angle0_v2.json
  - reviews/angle0_v3.json
  - reviews/angle0_v4.json
  - orchestrator/decision_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  Four D-0.5 proposal versions attempted to define the field-level oracle-adaptation
  frontier, first through scoped repairs and finally through a whole-core audit of
  domains, dimensions, ordering, parameters, and citations. The proposal retained
  credible novelty, but the attaining selector was still not a determinate measurable
  statistic, its optimization domain did not match the oracle frontier, and the lower
  experiment did not establish legal perturbations inside the model class. No Lean
  formalization was started because the mathematical specification never cleared D-0.5.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 29131788
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 29131788
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# panel_ferrers_cholesky_frontier / v1 — Failed

**Topic.** Signal-aware oracle-adaptation modulus for dependent causal-panel completion on Ferrers masks. Observe one Gaussian rank-r panel Y=M+sigma L_N Z L_T' on a deterministic Ferrers mask with nonvanishing complete slabs, fixed-rank incoherent M, bounded slab Gram geometry, and unknown separable covariance whose inverse-Cholesky factors have bounded spectra and matched row-and-column polynomial tails. For a diffuse missing-cell causal target psi_W(M), define the truth-specific covariance-minimum tangent-balancing score and the minimax L2 distance from all feasible observed-data statistics to its oracle linearization. Derive a primitive target-sensitive necessary-and-sufficient adaptation condition retaining the unavoidable mean-tangent learning cost; construct an observable same-panel residual and tangent-balanced score, feasible variance calibration, and uniform Wald coverage on the adaptation region; and prove matching legal Gaussian lower experiments plus the non-oracle risk frontier outside it. Consumers are Ben-Michael and Feller's right-to-carry reanalysis and Choi-Yuan's SEC Tick Size Pilot analysis. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An exact rank-one loading-class minimax theorem was derived: for post-period weights h, oracle-reproduction risk is comparable to sigma sqrt((||h||^2+1/m)/m) min(1,sigma/(a sqrt(n))); an observable unknown-signal tangent-balanced statistic attains it with feasible variance calibration. Exact known-separable-covariance profiling gives temporal information J=S_x P_T+S_b P_C and agrees with direct GLS checks below 1.2e-15. Matched-tail and paired-loading counterexamples were checked, while no published collision was verified. UNRESOLVED BOTTLENECK: Prove a primitive uniform target-sensitive L2 bound for the joint adaptive-score and rank-curvature remainder when both factor spaces and both nonparametric innovation factors are estimated from the same Ferrers panel, with a matching legal posterior-risk lower experiment. EARLY KILL TEST: On the half-by-half L mask with unknown rank-one row/time directions and unknown nonstationary exact-one-banded innovations, derive the same-panel residual-score remainder and matching posterior lower experiment for both one-period and full-rectangle averages; pivot if this requires supplied factor directions, an independent panel, or stronger covariance regularity. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ferrers_cholesky_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** REVISE

**Stage 0.5 verdict.** NA

**Banking reason.** Same load-bearing construction defects persist after a concrete whole-core root retry: the feasible selector is not a specified measurable map, the lower experiment has no defined positive legal radius, and the oracle/feasible bandwidth domains disagree.

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
