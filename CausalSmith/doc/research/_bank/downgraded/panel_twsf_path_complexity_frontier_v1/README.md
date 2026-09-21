---
qid: panel_twsf_path_complexity_frontier
spec: v1
topic: "Simultaneous selected-training TWSF conditional-mean bands with a variance-share Gaussian-complexity frontier. Condition on latent factors and assignments in balanced, strongly identified fixed-rank panels with independent homoskedastic Gaussian cell errors, deterministic direct and recursive training cells, one common terminal W block and forecast origin, and selected-design recovery through H. Derive stacked orthogonal scores and observable positive-semidefinite Gram covariance estimates; prove uniform feasible multiplier-band coverage when (kappa+1)epsilon+(kappa+1)^2t+d tends to zero, with explicit PCR/Riesz/Jacobian rates admitting H=floor(n^(1/8)). Let nu_min be the minimum standardized variance share of independent direct lead responses. Prove bounded recursive complexity and direct complexity comparable to 1+sqrt(nu_min log(2H)) on the declared fixed-rank class. On the persistent all-ones subclass, prove kappa_rec tends to sqrt(2/pi), kappa_dir/sqrt(log H) tends to one, and probability and expected maximum-width lower bounds for uniformly honest rectangles centered at the direct leading Gaussian estimator. Consumer: mlsynth TWSF path ribbons and Shen's NFL-stadium conditional-mean paths; exclude prediction bands and unrestricted-estimator minimax claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The stacked S12/S13 score and Gram-covariance formulas were derived. On the legal common-origin all-ones sequence, alpha*=1_L/L, J_ell'1=c_ell1, ||g_ell||^2=1/L+O(H/L^2), direct independent variance share is 1/(2+3/n), kappa_rec approaches sqrt(2/pi), and kappa_dir/sqrt(log H) approaches one. A conditional Gaussian event and sixteen-term remainder ledger yield epsilon_rec=O(H log(nH)/sqrt(n)+H^2 log(nH)/n) and normalized correlation error O_p(H^2 sqrt(log(nH)/n)), so H=n^(1/8) is nonempty. Checks covered selected-training failure, vanishing shares, singular correlations, studentization, long horizons, prediction shocks, randomized widths, and prior-art collapse. UNRESOLVED BOTTLENECK: Package the displayed events into one class-uniform conditional probability bound with constants depending only on declared class radii, independently auditing spectral perturbation and exceptional-event conventions. EARLY KILL TEST: Reproduce the three-piece perturbation bound for qhat_ell=Zhat_dagger Jhat_ell' W' betahat and the actual-PCR relative covariance rate on the all-ones sequence; pivot if an order-one normalized term or oracle W/Jacobian is required. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_twsf_path_complexity_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The 16-term recursive ledger drops the normal-equation terms d_{p,ell}^T r_beta and d_{q,ell}^T r_a, where r_beta=(I-P_Y)\\bar y and r_a=(I-P_Z)\\bar z_rec; neither ass:unit-recovery nor ass:recursive-recovery sets these response projection residuals to zero."
  - "The same omission invalidates the proof that the pooled residual estimator consistently estimates sigma squared, because the unit-response residual sum of squares can contain an order-n signal component."
  - "The highly specialized Gaussian, exact-rank, disjoint-block setting and the lower bound's restriction to the prescribed Gaussian center further limit the projected leading-journal contribution."
  - "Position CCK (2013), CCK (2014 Bands), and Armstrong--Kolesar (2018), or remove them from the bibliography."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_complexity_frontier.tex
  - discovery/solve_thm_persistent_limits.tex
  - discovery/solve_thm_centered_rectangle_width.tex
  - discovery/solve_thm_relative_gram_rate.tex
  - discovery/vcs/rendered_main
seeds_burned: []
proof_attempt_summary: |
  Discovery derived exact Gaussian-score complexity comparisons, persistent all-ones limits,
  a centered-rectangle width lower bound, and proposed feasible simultaneous bands for selected-training
  TWSF paths. The feasible-coverage spine collapsed because the recursive expansion omitted first-order
  projection-residual rotation terms and the pooled variance estimator could retain order-one signal
  contamination. The narrower complexity results remain reusable, but repairing coverage inside the
  specialized Gaussian/exact-rank/disjoint-block class cannot plausibly reach the field novelty floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 39658899
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 39658899
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# panel_twsf_path_complexity_frontier / v1 — Downgraded

**Topic.** Simultaneous selected-training TWSF conditional-mean bands with a variance-share Gaussian-complexity frontier. Condition on latent factors and assignments in balanced, strongly identified fixed-rank panels with independent homoskedastic Gaussian cell errors, deterministic direct and recursive training cells, one common terminal W block and forecast origin, and selected-design recovery through H. Derive stacked orthogonal scores and observable positive-semidefinite Gram covariance estimates; prove uniform feasible multiplier-band coverage when (kappa+1)epsilon+(kappa+1)^2t+d tends to zero, with explicit PCR/Riesz/Jacobian rates admitting H=floor(n^(1/8)). Let nu_min be the minimum standardized variance share of independent direct lead responses. Prove bounded recursive complexity and direct complexity comparable to 1+sqrt(nu_min log(2H)) on the declared fixed-rank class. On the persistent all-ones subclass, prove kappa_rec tends to sqrt(2/pi), kappa_dir/sqrt(log H) tends to one, and probability and expected maximum-width lower bounds for uniformly honest rectangles centered at the direct leading Gaussian estimator. Consumer: mlsynth TWSF path ribbons and Shen's NFL-stadium conditional-mean paths; exclude prediction bands and unrestricted-estimator minimax claims. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The stacked S12/S13 score and Gram-covariance formulas were derived. On the legal common-origin all-ones sequence, alpha*=1_L/L, J_ell'1=c_ell1, ||g_ell||^2=1/L+O(H/L^2), direct independent variance share is 1/(2+3/n), kappa_rec approaches sqrt(2/pi), and kappa_dir/sqrt(log H) approaches one. A conditional Gaussian event and sixteen-term remainder ledger yield epsilon_rec=O(H log(nH)/sqrt(n)+H^2 log(nH)/n) and normalized correlation error O_p(H^2 sqrt(log(nH)/n)), so H=n^(1/8) is nonempty. Checks covered selected-training failure, vanishing shares, singular correlations, studentization, long horizons, prediction shocks, randomized widths, and prior-art collapse. UNRESOLVED BOTTLENECK: Package the displayed events into one class-uniform conditional probability bound with constants depending only on declared class radii, independently auditing spectral perturbation and exceptional-event conventions. EARLY KILL TEST: Reproduce the three-piece perturbation bound for qhat_ell=Zhat_dagger Jhat_ell' W' betahat and the actual-PCR relative covariance rate on the all-ones sequence; pivot if an order-one normalized term or oracle W/Jacobian is required. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_twsf_path_complexity_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field and NOT salvageable in scope; the central feasible-coverage argument omits projection-residual terms.

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
