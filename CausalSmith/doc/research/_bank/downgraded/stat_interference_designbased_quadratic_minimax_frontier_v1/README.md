---
qid: stat_interference_designbased_quadratic_minimax_frontier
spec: v1
topic: "Design-based quadratic minimax frontier for interference specification tests. For fixed known minimum-degree-two repeated-motif graphs, iid Bernoulli(1/2) assignment, and bounded schedules y_i(z)=beta_i1+beta_i2z_i+beta_i3T_i(z), test H0:beta_i3=0 against spillover RMS rho. Optimize Q_w=n^-1sum_iw_i(T_i)Y_i^2, prove attainment and the correct conditional-variance Sion dual, and establish rho*=V_quad^1/4 up to constants with exact worst-null calibration and an all-test converse. Gao et al. arXiv:2605.09726 own the estimator and upper bound; Tiwari--Basu arXiv:2608.22890 own validity and simulations, not local minimax power. Consumer: LinkedIn's Bernoulli feed-ranking arm. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The moment equations make Q exactly unbiased for rho^2 because Z_i is independent of T_i. Finite-dimensional coercivity follows from sparse legal baseline schedules, so Sion applies to integral Var_Z(Q_w|beta)dPi, not mixture-law variance. For disjoint triangles, w=(8,-8,8); enumeration gives Var(Q)=64/n at beta_i1=1 and the bounded-outcome envelope gives V_quad<=192/n. The null f_a versus alternative f_(aT_i) construction factors conditional on assignment; h0 proportional to cos^8 has boundary order eight, symmetric shifts cancel first order, and direct analysis numerically supports H^2(f_a,f_(at))<=Ca^4 uniformly. Searches found no matching local minimax theorem and repo neighbors target estimation, ambiguity, or confidence intervals. UNRESOLVED BOTTLENECK: Prove the uniform shifted-support Hellinger lemma and convert its product bound into the composite all-test lower bound with constants matching the repeated-motif V_quad comparison. EARLY KILL TEST: First formalize the Hellinger bound, Sion compactification, and complete triangle enumeration; pivot or stop if Hellinger is quadratic, the dual requires variance under a mixed observation law, or the triangle scale fails."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Uniform shifted-support cancellation/SOS certificate and machine-readable quantifier-elimination certificates for exact motif constants are missing."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The load-bearing uniform bound (5) is asserted after an unspecified rational-function cancellation: neither the numerator nor a checkable certificate is supplied, so the claimed all-t shifted-support L2 second-derivative bound (and hence the explicit Hellinger constant) cannot be reproduced from the declared dependencies."
  - "The K3 and C4 upper bounds rest entirely on asserted QE implications (4) and (7), but the projection polynomials, isolating/sign data, or an independently checkable certificate are absent; the displayed witnesses establish only lower bounds, not v_K3 and v_C4."
  - "What is securely delivered is unbiased quadratic estimation, attainment and duality of the finite variance game, calibration by exhaustive semialgebraic enumeration in principle, and an upper detection rate for disjoint repeated motifs—not the claimed matched minimax frontier."
reusable_artifacts:
  - "discovery/core.json — versioned theorem graph with the finite variance game, Sion dual, calibration construction, and small-motif maximality audit."
  - "discovery/writeup.tex — derivation note containing the reusable finite assignment-table and conditional-variance setup."
  - "discovery/gaps.json — literature/open-problem map for interference specification testing."
  - "reviews/review_math.json — precise certificate failures that a retry must discharge."
seeds_burned:
  - index: 0
    one_liner: "seed:fourth-root-frontier"
    reason: "The repeated-motif field angle retained sound finite-game duality and an upper detection result, but its all-test converse and exact K3/C4 constants were not independently certified."
proof_attempt_summary: |
  The run built and discharged a finite repeated-motif conditional-variance game, its attained dual, a nuisance-maximized calibration route, and a small-motif maximality audit showing no strict weight gain for maximum degree at most three or for K5. The matched all-test converse failed audit because the shifted-support Hellinger step omitted its symbolic cancellation certificate, while the advertised exact K3/C4 constants omitted machine-checkable quantifier-elimination certificates. A retry should preserve the finite-game substrate and focus only on those certificates before reclaiming the field-tier frontier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31042407
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31042407
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# stat_interference_designbased_quadratic_minimax_frontier / v1 — Downgraded

**Topic.** Design-based quadratic minimax frontier for interference specification tests. For fixed known minimum-degree-two repeated-motif graphs, iid Bernoulli(1/2) assignment, and bounded schedules y_i(z)=beta_i1+beta_i2z_i+beta_i3T_i(z), test H0:beta_i3=0 against spillover RMS rho. Optimize Q_w=n^-1sum_iw_i(T_i)Y_i^2, prove attainment and the correct conditional-variance Sion dual, and establish rho*=V_quad^1/4 up to constants with exact worst-null calibration and an all-test converse. Gao et al. arXiv:2605.09726 own the estimator and upper bound; Tiwari--Basu arXiv:2608.22890 own validity and simulations, not local minimax power. Consumer: LinkedIn's Bernoulli feed-ranking arm. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The moment equations make Q exactly unbiased for rho^2 because Z_i is independent of T_i. Finite-dimensional coercivity follows from sparse legal baseline schedules, so Sion applies to integral Var_Z(Q_w|beta)dPi, not mixture-law variance. For disjoint triangles, w=(8,-8,8); enumeration gives Var(Q)=64/n at beta_i1=1 and the bounded-outcome envelope gives V_quad<=192/n. The null f_a versus alternative f_(aT_i) construction factors conditional on assignment; h0 proportional to cos^8 has boundary order eight, symmetric shifts cancel first order, and direct analysis numerically supports H^2(f_a,f_(at))<=Ca^4 uniformly. Searches found no matching local minimax theorem and repo neighbors target estimation, ambiguity, or confidence intervals. UNRESOLVED BOTTLENECK: Prove the uniform shifted-support Hellinger lemma and convert its product bound into the composite all-test lower bound with constants matching the repeated-motif V_quad comparison. EARLY KILL TEST: First formalize the Hellinger bound, Sion compactification, and complete triangle enumeration; pivot or stop if Hellinger is quadratic, the dual requires variance under a mixed observation law, or the triangle scale fails.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G: delivered tier incremental below field floor; the advertised matched all-test frontier lacks checkable shifted-support and QE certificates.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The maximality pass is informative even without the field claim: it records why the smallest non-degree-two motifs do not demonstrate a strict optimization gain over Gao et al.'s weight. Any re-raise should reuse that negative result and search only genuinely new maximum-degree-at-least-four motif families after closing the two certificate gaps above.
