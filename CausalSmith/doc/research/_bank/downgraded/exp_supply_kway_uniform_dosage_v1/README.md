---
qid: exp_supply_kway_uniform_dosage
spec: v1
topic: "Exact shared-supply product dosage for all low-order Fourier interactions. Fix p>=2, 1<=k<=p, 0<L<=p, coefficient bound B, and positive bounded homoskedastic noise variance. Independently draw Z_i~Bernoulli(d_i) with sum_i d_i<=L, put X_i=2Z_i-1, and use the fixed dosage-independent basis phi_S(X)=product_{i in S}X_i for every |S|<=k, including the intercept. For Sigma_k(d)=E_d[phi phiT] and Phi_k(d)=trace(Sigma_k(d)^(-1)), prove that u=min(L/p,1/2) uniquely minimizes Phi, with exact value sum_{j=0}^k binom(p,j)r(u)^j for r(v)=1/[2v(1-v)]-1 and global certificate Phi_k(d)-Phi_k(u1)>=8 sum_{h=0}^{k-1}binom(p-1,h)||d-u1||_2^2. Prove exact maximum leverage mu*=sum_{j=0}^k binom(p,j)[(1-u)/u]^j, the necessary rank-deficiency probability at least (1-u^k)^n from a missing chosen k-fold activation, and explicit two-sided expected-risk bounds plus uniform fixed-dimensional oracle attainment for known-Sigma spectral-threshold OLS. Credit Schwabe--Wong (1999) for the downward-closed product-design trace identity and Shyamal--Zhang--Uhler PFED (2025) for the modern product-Bernoulli model and additive limited-supply theorem. Do not claim finite-n minimax design optimality, dependent or fixed-count assignment, growing dimension, or vanishing-supply uniformity. Yao et al. Nature Biotechnology 2024 is an idealized high-MOI interaction-screen consumer only under independent delivery and the stated regression model. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The fixed-basis triangular change to product-orthonormal features yields the elementary-symmetric trace exactly. A fresh presolve derived Hessian(Phi)>=16 sum_{h<k}binom(p-1,h)I, making the stated stability coefficient sharp at half dosage, and re-derived exact leverage, the activation-polynomial null vector, conditional OLS covariance, fallback bias, and Chernoff risk sandwich. Fourteen exact Gram/leverage models, fourteen exact rank-null checks, 700 deterministic optimizer/curvature checks, and finite-support risk enumeration passed. The beta=0 enumeration shows finite-sample truncated risk can lie below population A-risk, confirming the exclusion of finite-n oracle optimality. Focused source checks found the classical identity and PFED's additive-only theorem but no identical shared-supply package. UNRESOLVED BOTTLENECK: Independently verify the whitened-Gram matrix-Chernoff constant and the unconditional risk decomposition including the spectral-fallback bias term under the stated conditional-noise assumptions. EARLY KILL TEST: Reconstruct and invert the p=3,k=2 fixed-basis Gram matrices at d=(1/3,1/3,1/3) and d=(1/4,1/3,5/12), recover traces 151/16 and 4259/420, and verify the log-curvature identity; failure should stop the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_supply_kway_uniform_dosage.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The proposal promised a subfield-level constrained corollary, but the mill's field floor required a broader leading-journal contribution; finite-n dosage minimaxity remained explicitly open and out of scope."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - >-
    The main delivered result is exact population A-optimality for the fixed
    low-order Fourier basis under independent product-Bernoulli dosage, not
    finite-sample optimal-design or minimax optimality; the latter remains
    explicitly open in oeq:finite-minimax-frontier.
  - >-
    The extension beyond the classical trace identity is a clean but
    specialized symmetric optimization, with the leverage, rank-obstruction,
    and concentration results remaining confined to fixed dimension, fixed
    positive supply, homoskedasticity, and independent delivery.
  - >-
    D0.5.G projected paper-score gate: paper_score_ceiling 6.4 < 7.4, so the
    graded tier 'field' is capped at 'incremental'.
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_uniform_optimum.tex
  - discovery/solve_prop_exact_leverage.tex
  - discovery/solve_thm_risk_sandwich.tex
  - discovery/solve_thm_oracle_attainment.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery derived and panel-checked the exact shared-supply population
  optimizer, stability certificate, leverage and rank obstruction, and a
  fixed-threshold O(n^-1) oracle-risk expansion; the math panel reported no
  findings and the cited sources were verified. The package collapsed only at
  the field-novelty gate: it remains a narrow fixed-dimensional specialization,
  while the tier-moving finite-sample dosage/minimax frontier is unproved and
  explicitly outside scope.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 10183306
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 10183306
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# exp_supply_kway_uniform_dosage / v1 — Downgraded

**Topic.** Exact shared-supply product dosage for all low-order Fourier interactions. Fix p>=2, 1<=k<=p, 0<L<=p, coefficient bound B, and positive bounded homoskedastic noise variance. Independently draw Z_i~Bernoulli(d_i) with sum_i d_i<=L, put X_i=2Z_i-1, and use the fixed dosage-independent basis phi_S(X)=product_{i in S}X_i for every |S|<=k, including the intercept. For Sigma_k(d)=E_d[phi phiT] and Phi_k(d)=trace(Sigma_k(d)^(-1)), prove that u=min(L/p,1/2) uniquely minimizes Phi, with exact value sum_{j=0}^k binom(p,j)r(u)^j for r(v)=1/[2v(1-v)]-1 and global certificate Phi_k(d)-Phi_k(u1)>=8 sum_{h=0}^{k-1}binom(p-1,h)||d-u1||_2^2. Prove exact maximum leverage mu*=sum_{j=0}^k binom(p,j)[(1-u)/u]^j, the necessary rank-deficiency probability at least (1-u^k)^n from a missing chosen k-fold activation, and explicit two-sided expected-risk bounds plus uniform fixed-dimensional oracle attainment for known-Sigma spectral-threshold OLS. Credit Schwabe--Wong (1999) for the downward-closed product-design trace identity and Shyamal--Zhang--Uhler PFED (2025) for the modern product-Bernoulli model and additive limited-supply theorem. Do not claim finite-n minimax design optimality, dependent or fixed-count assignment, growing dimension, or vanishing-supply uniformity. Yao et al. Nature Biotechnology 2024 is an idealized high-MOI interaction-screen consumer only under independent delivery and the stated regression model. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The fixed-basis triangular change to product-orthonormal features yields the elementary-symmetric trace exactly. A fresh presolve derived Hessian(Phi)>=16 sum_{h<k}binom(p-1,h)I, making the stated stability coefficient sharp at half dosage, and re-derived exact leverage, the activation-polynomial null vector, conditional OLS covariance, fallback bias, and Chernoff risk sandwich. Fourteen exact Gram/leverage models, fourteen exact rank-null checks, 700 deterministic optimizer/curvature checks, and finite-support risk enumeration passed. The beta=0 enumeration shows finite-sample truncated risk can lie below population A-risk, confirming the exclusion of finite-n oracle optimality. Focused source checks found the classical identity and PFED's additive-only theorem but no identical shared-supply package. UNRESOLVED BOTTLENECK: Independently verify the whitened-Gram matrix-Chernoff constant and the unconditional risk decomposition including the spectral-fallback bias term under the stated conditional-noise assumptions. EARLY KILL TEST: Reconstruct and invert the p=3,k=2 fixed-basis Gram matrices at d=(1/3,1/3,1/3) and d=(1/4,1/3,5/12), recover traces 151/16 and 4259/420, and verify the log-curvature identity; failure should stop the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_supply_kway_uniform_dosage.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The main delivered result is exact population A-optimality in a narrow fixed-dimensional product-Bernoulli model, not finite-sample optimal-design or minimax optimality; D0.5.G capped it at incremental with paper-score ceiling 6.4 below the 7.4 field cutoff.

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
