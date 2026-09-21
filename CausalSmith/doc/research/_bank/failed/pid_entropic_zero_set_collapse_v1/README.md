---
qid: pid_entropic_zero_set_collapse
spec: v1
topic: "Entropic zero-set collapse and certified recovery of finite OT moment identified sets. Let two fixed finite alphabets have observed marginals p,q bounded below by eta, let pi range over Pi(p,q), let theta range over a computably covered compact set, and define D0(theta)=min_pi ||sum_ij pi_ij phi_ij(theta)|| for a bounded moment table with a known modulus and a nonempty sharp set Theta0 satisfying a displayed separation exponent kappa. Prove that adding epsilon KL(pi||p tensor q) yields D_epsilon=min_pi{||m_theta(pi)||+epsilon KL} and, for every epsilon>0, exact zero membership iff the product coupling satisfies the moment. Derive the pointwise first-order penalty as minimum KL over D0-minimizing couplings. Construct certified Sinkhorn primal-dual and rational-repair brackets L_a<=D0<=U_a with uniform gap at most a and finite polynomial work in fixed dimensions, then combine them with multinomial confidence events to give finite-sample simultaneous outer coverage of Theta0 and separation-based Hausdorff control on that same event. Credit Franguridi--Liu arXiv:2512.18084v3 for the regularized OT estimator and bootstrap, and generic entropy and criterion-set theory; exclude unconditional two-sided root-rate recovery and the refuted directional-face frontier. Their UAS attrition/refreshment workflow is the consumer, but its published contour is not characterized without a code audit. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The fresh presolve rederived D_epsilon=min_pi{||m_theta(pi)||+epsilon KL}, exact product-coupling zero-set collapse, and the fixed-instance J=min KL expansion. It solved the binary benefit-share case where [1/2,1] collapses to {3/4}, plus a vector tied-face case. It derived certified original-value brackets, exact marginal repair, an O(a^(-5)) exact-arithmetic per-query stopping bound, marginal stability, and finite-cell simultaneous coverage and Hausdorff control. A reproducible check covered 21 binary cases and 4,500 Sinkhorn iterates over 15 positive 3-by-3 problems against LP values. Destructive checks reproduced the current v3 entropy-normalization error, excluded the false face-bias and unconditional-rate claims, handled zero empirical cells by support reduction, and found no exact qid or theorem collision at the accepted tier. UNRESOLVED BOTTLENECK: Prove the finite-precision lemma giving polynomial total bit work for outward Sinkhorn dual evaluation and exact rational marginal repair, including accumulated-update, positivity, denominator-length, and exp/log precision budgets. EARLY KILL TEST: On the rational binary witness and a tied positive 3-by-3 table, construct outward dual enclosures and exact repairs as a decreases; stop or change the computation theorem if valid original-value brackets cannot be preserved with polynomial precision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_entropic_zero_set_collapse.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "The proposed finite-width Sinkhorn certificate is dominated by exact rational min-cost-flow certification, so it does not establish the required field-level computational or verification advantage."
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "N-thin-survey — Tier=subfield below novelty_target=field: the survey omits exact rational min-cost-flow/transport certification (notably Orlin1993), so the stated certificate output has no demonstrated advantage over an established exact primal-dual route; a field claim needs a Sinkhorn-specific asymptotic, verification, or causal-decision advantage."
  - "Exact rational minimum-cost flow already gives a stronger zero-width primal-dual certificate; the current assumptions provide no variable-dimension, parallel, or repeated-query regime proving a Sinkhorn-specific resource advantage."
reusable_artifacts:
  - "discovery/proto_core.json — final reviewed field-tier proposal attempt."
  - "discovery/proto_core.json.next — producer's explicit needs-pivot result under the exact-flow comparator directive."
  - "discovery/gaps.json — persisted proposal gaps and comparator audit."
  - "reviews/angle0_v1.json and reviews/angle0_v2.json — reviewer evidence across both revisions."
seeds_burned:
  - index: 0
    one_liner: "seed:finite-precision-certificate"
    reason: "The sole supported angle exhausted after two revisions; remaining seeds were unsupported, refuted, or subsumed and switching would change the root claim."
proof_attempt_summary: |
  Discovery attempted to turn the positive-temperature zero-set correction and certified
  Sinkhorn brackets into a field-tier computational certification result. The decisive
  comparison collapsed: exact rational min-cost flow already supplies a stronger zero-width
  primal-dual certificate in the stated fixed-dimensional regime. A viable follow-on would
  require a genuinely different regime with a proved Sinkhorn-specific asymptotic, parallel,
  amortized, or repeated-query advantage; that would be a new root claim rather than a revision.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 8666339
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 8666339
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# pid_entropic_zero_set_collapse / v1 — Failed

**Topic.** Entropic zero-set collapse and certified recovery of finite OT moment identified sets. Let two fixed finite alphabets have observed marginals p,q bounded below by eta, let pi range over Pi(p,q), let theta range over a computably covered compact set, and define D0(theta)=min_pi ||sum_ij pi_ij phi_ij(theta)|| for a bounded moment table with a known modulus and a nonempty sharp set Theta0 satisfying a displayed separation exponent kappa. Prove that adding epsilon KL(pi||p tensor q) yields D_epsilon=min_pi{||m_theta(pi)||+epsilon KL} and, for every epsilon>0, exact zero membership iff the product coupling satisfies the moment. Derive the pointwise first-order penalty as minimum KL over D0-minimizing couplings. Construct certified Sinkhorn primal-dual and rational-repair brackets L_a<=D0<=U_a with uniform gap at most a and finite polynomial work in fixed dimensions, then combine them with multinomial confidence events to give finite-sample simultaneous outer coverage of Theta0 and separation-based Hausdorff control on that same event. Credit Franguridi--Liu arXiv:2512.18084v3 for the regularized OT estimator and bootstrap, and generic entropy and criterion-set theory; exclude unconditional two-sided root-rate recovery and the refuted directional-face frontier. Their UAS attrition/refreshment workflow is the consumer, but its published contour is not characterized without a code audit. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The fresh presolve rederived D_epsilon=min_pi{||m_theta(pi)||+epsilon KL}, exact product-coupling zero-set collapse, and the fixed-instance J=min KL expansion. It solved the binary benefit-share case where [1/2,1] collapses to {3/4}, plus a vector tied-face case. It derived certified original-value brackets, exact marginal repair, an O(a^(-5)) exact-arithmetic per-query stopping bound, marginal stability, and finite-cell simultaneous coverage and Hausdorff control. A reproducible check covered 21 binary cases and 4,500 Sinkhorn iterates over 15 positive 3-by-3 problems against LP values. Destructive checks reproduced the current v3 entropy-normalization error, excluded the false face-bias and unconditional-rate claims, handled zero empirical cells by support reduction, and found no exact qid or theorem collision at the accepted tier. UNRESOLVED BOTTLENECK: Prove the finite-precision lemma giving polynomial total bit work for outward Sinkhorn dual evaluation and exact rational marginal repair, including accumulated-update, positivity, denominator-length, and exp/log precision budgets. EARLY KILL TEST: On the rational binary witness and a tied positive 3-by-3 table, construct outward dual enclosures and exact repairs as a decreases; stop or change the computation theorem if valid original-value brackets cannot be preserved with polynomial precision. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_entropic_zero_set_collapse.md.

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** Exact rational minimum-cost flow already gives a stronger zero-width primal-dual certificate; the current assumptions provide no variable-dimension, parallel, or repeated-query regime proving a Sinkhorn-specific resource advantage.

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
