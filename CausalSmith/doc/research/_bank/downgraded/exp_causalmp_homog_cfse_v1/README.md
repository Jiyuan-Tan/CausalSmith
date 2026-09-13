---
qid: exp_causalmp_homog_cfse
spec: v1
topic: "Homogeneous Causal-MP fluctuation state evolution with feasible TTE-path bands. For fixed T>=3, observe Y,W,X from Y_{i,t+1}=sum_j(1/N+sigma G_ij/sqrt(N))g_beta(Y_jt,W_{j,t+1},X_j)+epsilon_it, where one iid Gaussian G matrix is unobserved and reused over time, treatments are independent Bernoulli with known probabilities bounded from 0 and 1, innovations are iid Gaussian, and finite-dimensional C3 g_beta has the required moment bounds. Under full-rank mean moments and a rank-two variance design based on distinct observable message energies, derive rather than assume the joint root-N CLT for the empirical means, second moments, and score moments. Construct the homogeneous CFSE covariance Gamma_T, observable estimators of beta,sigma^2,tau^2 from mean and variance regressions, plug-in counterfactual-path covariance, and simultaneous Gaussian-max bands for the population-limit all-treated-minus-none-treated TTE path. Use the affine T=3 witness g(y,w)=0.5y+w, p=(0.25,0.75,0.25), sigma^2=tau^2=1, whose message-energy design has det(X'X)=10191/8192. The public CausalMP CFEEstimator in full-population, n_batch=1, ridge_alpha=0 configuration is the software consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact adaptive Gaussian conditioning yields a finite recursion retaining reuse of the same matrix. T=1 and T=2 influence functions were derived; structural residual covariances reduce to C=sigma^2 K+tau^2 I, 2(C Hadamard C), and a zero mixed block. In the witness, consecutive root-N mean fluctuations have covariance 19/16, including reuse contribution 7/32, and exact-conditioned simulations at N=128 and 1024 agree diagnostically. Degenerate designs, redundant queries, variance boundaries, fixed ridge bias, and current neighboring literature were checked without an affirmative obstruction or collision. UNRESOLVED BOTTLENECK: Prove the fixed-T adaptive empirical-recursion linearization lemma with jointly o_p(N^-1/2) row-averaged Taylor remainders for messages, Gram products, and scores, including deletion and continuity at zero message pivots. EARLY KILL TEST: At T=3, evaluate the differentiated recursion for the affine witness and for g(y,w)=0.5y+w+0.1tanh(y); verify residual blocks C, 2(C Hadamard C), and zero mixed covariance against direct reused-matrix simulations. A persistent discrepancy or nonvanishing scaled remainder stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_causalmp_homog_cfse.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The load-bearing adaptive-linearization proof remains too compressed at its delicate point: it introduces an unspecified finite collection of integrands and asserts a common b_N D_{N,t}^2 bound without explicitly deriving the recursive envelope products and uniform second-order remainder bounds."
  - "The package supplies only an affine algebraic witness, not the advertised nonlinear early-kill simulation or a reproducible implementation check against the public CFEEstimator."
  - "The narrow model scope, abbreviated core remainder argument, and limited practical evidence cap the projected leading-journal score despite the field-level joint CLT and inference result."
  - "The declared Z^\\circ variables are independent of primitive rows but not of G; the claimed conditional-iid Gaussian kernel is therefore not entailed (declare them fresh and independent of G, or formulate the bridge on an independent extension)."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/gaps.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  Discovery repaired the deleted-pivot nonregularity by restricting the theorem to
  uniformly all-active open families, established an explicit finite-N reused-G
  bridge and an adaptive-linearization theorem, and audited the affine T=3 witness
  with q=(1/2,85/64,159/128), determinant 10191/8192, and reuse covariance 7/32.
  The final package remained below the field floor because its homogeneous fixed-T
  scope and compressed uniform remainder proof capped the score at 6.8; the fresh
  auxiliary-Gaussian independence declaration and related-work relevance also remain
  local repair debt.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31545507
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31545507
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_causalmp_homog_cfse / v1 — Downgraded

**Topic.** Homogeneous Causal-MP fluctuation state evolution with feasible TTE-path bands. For fixed T>=3, observe Y,W,X from Y_{i,t+1}=sum_j(1/N+sigma G_ij/sqrt(N))g_beta(Y_jt,W_{j,t+1},X_j)+epsilon_it, where one iid Gaussian G matrix is unobserved and reused over time, treatments are independent Bernoulli with known probabilities bounded from 0 and 1, innovations are iid Gaussian, and finite-dimensional C3 g_beta has the required moment bounds. Under full-rank mean moments and a rank-two variance design based on distinct observable message energies, derive rather than assume the joint root-N CLT for the empirical means, second moments, and score moments. Construct the homogeneous CFSE covariance Gamma_T, observable estimators of beta,sigma^2,tau^2 from mean and variance regressions, plug-in counterfactual-path covariance, and simultaneous Gaussian-max bands for the population-limit all-treated-minus-none-treated TTE path. Use the affine T=3 witness g(y,w)=0.5y+w, p=(0.25,0.75,0.25), sigma^2=tau^2=1, whose message-energy design has det(X'X)=10191/8192. The public CausalMP CFEEstimator in full-population, n_batch=1, ridge_alpha=0 configuration is the software consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact adaptive Gaussian conditioning yields a finite recursion retaining reuse of the same matrix. T=1 and T=2 influence functions were derived; structural residual covariances reduce to C=sigma^2 K+tau^2 I, 2(C Hadamard C), and a zero mixed block. In the witness, consecutive root-N mean fluctuations have covariance 19/16, including reuse contribution 7/32, and exact-conditioned simulations at N=128 and 1024 agree diagnostically. Degenerate designs, redundant queries, variance boundaries, fixed ridge bias, and current neighboring literature were checked without an affirmative obstruction or collision. UNRESOLVED BOTTLENECK: Prove the fixed-T adaptive empirical-recursion linearization lemma with jointly o_p(N^-1/2) row-averaged Taylor remainders for messages, Gram products, and scores, including deletion and continuity at zero message pivots. EARLY KILL TEST: At T=3, evaluate the differentiated recursion for the affine witness and for g(y,w)=0.5y+w+0.1tanh(y); verify residual blocks C, 2(C Hadamard C), and zero mixed covariance against direct reused-matrix simulations. A persistent discrepancy or nonvanishing scaled remainder stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_causalmp_homog_cfse.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: paper_score_ceiling 6.8 < 7.2; fixed-horizon homogeneous Gaussian regular-interior CFSE is sound but below the field novelty floor, with no bounded in-scope change that raises the tier.

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
