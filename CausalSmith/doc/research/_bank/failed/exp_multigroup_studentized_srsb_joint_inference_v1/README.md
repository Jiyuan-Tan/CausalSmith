---
qid: exp_multigroup_studentized_srsb_joint_inference
spec: v1
topic: "Studentized sequential rerandomization for joint spillover and carryover inference. In even-G partial-interference groups observed over two-period blocks, randomize half the groups to each of two saturation levels using a predictable soft-rerandomization kernel applied to the exactly standardized complete-randomization imbalance, then assign fixed treatment counts within groups. For bounded nonanticipating lag-one potential outcomes and logged conditional inclusion probabilities, prove exact joint HT unbiasedness for direct and spillover effects, derive a root-GB martingale/combinatorial CLT, construct an observable conservative 2-by-2 studentizer and simultaneous Wald coverage, and prove Omega_RR=Omega_CR-(1-v_eta,kappa)P with the displayed standard-normal tilt constant and P the limiting projection covariance. Use the projection criterion to characterize every strictly improved contrast and retain the Yu--Ma--Liu/Bojinov--Shephard market experiment as a prospective design consumer, not a retrospective growing-G validation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Complement symmetry gives exact conditional saturation propensities 1/2. The block score decomposes into a balanced-sign component and conditionally centered within-group noise with zero cross covariance and exactly unchanged within-group covariance. An observable estimator has conditional expectation equal to the block covariance plus a deterministic PSD completion. Exact enumeration over 1,536 legal assignments verified unbiasedness and this matrix identity; a genuinely adaptive alternating-block family has imbalance variances 53/16 and 29/16, positive-definite projection gain, and one common standardized tilt constant. Current neighboring anchors did not supply the joint theorem. UNRESOLVED BOTTLENECK: Prove Lemma G, a history-uniform finite-population Gaussian approximation for the balanced-sign two-vector score and standardized scalar imbalance that transfers soft-tilt-weighted quadratic moments even with singular score covariance. EARLY KILL TEST: Complete Lemma G first via random perfect matchings for bounded three-vector arrays; any legal triangular-array counterexample to its weighted second-moment approximation stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multigroup_studentized_srsb_joint_inference.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "li_zhao_martingale_clt is false as stated, due to a reciprocal threshold error"
  - "The correct cutoff is epsilon*sqrt(V_T), which changes the frozen .tex claim"
reusable_artifacts:
  - "Causalean.Stat.CLT.MartingaleArray.Main (promoted, sorry-free generic martingale-array CLT substrate)"
  - "discovery/writeup.tex (source claim and the fourth-moment route that can support a corrected rerun)"
seeds_burned: []
proof_attempt_summary: |
  A reusable martingale-array CLT was built, reviewed, promoted, and independently
  axiom-audited. Instantiating it exposed that the frozen Li--Zhao lemma uses the
  reciprocal Lindeberg cutoff epsilon/sqrt(V_T): a one-increment Rademacher array
  satisfies the displayed premises while its normalized sum stays Rademacher.
  The headline CLT remains retryable after correcting the source cutoff and can
  use the already-promoted fourth-moment corollary directly.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 99863432
  pipeline_claude_tokens: 6815171
  total_tokens_consumed: null
banked_on: "2026-09-06"
---

# exp_multigroup_studentized_srsb_joint_inference / v1 — Failed

**Topic.** Studentized sequential rerandomization for joint spillover and carryover inference. In even-G partial-interference groups observed over two-period blocks, randomize half the groups to each of two saturation levels using a predictable soft-rerandomization kernel applied to the exactly standardized complete-randomization imbalance, then assign fixed treatment counts within groups. For bounded nonanticipating lag-one potential outcomes and logged conditional inclusion probabilities, prove exact joint HT unbiasedness for direct and spillover effects, derive a root-GB martingale/combinatorial CLT, construct an observable conservative 2-by-2 studentizer and simultaneous Wald coverage, and prove Omega_RR=Omega_CR-(1-v_eta,kappa)P with the displayed standard-normal tilt constant and P the limiting projection covariance. Use the projection criterion to characterize every strictly improved contrast and retain the Yu--Ma--Liu/Bojinov--Shephard market experiment as a prospective design consumer, not a retrospective growing-G validation. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Complement symmetry gives exact conditional saturation propensities 1/2. The block score decomposes into a balanced-sign component and conditionally centered within-group noise with zero cross covariance and exactly unchanged within-group covariance. An observable estimator has conditional expectation equal to the block covariance plus a deterministic PSD completion. Exact enumeration over 1,536 legal assignments verified unbiasedness and this matrix identity; a genuinely adaptive alternating-block family has imbalance variances 53/16 and 29/16, positive-definite projection gain, and one common standardized tilt constant. Current neighboring anchors did not supply the joint theorem. UNRESOLVED BOTTLENECK: Prove Lemma G, a history-uniform finite-population Gaussian approximation for the balanced-sign two-vector score and standardized scalar imbalance that transfers soft-tilt-weighted quadratic moments even with singular score covariance. EARLY KILL TEST: Complete Lemma G first via random perfect matchings for bounded three-vector arrays; any legal triangular-array counterexample to its weighted second-moment approximation stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_multigroup_studentized_srsb_joint_inference.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** The cited martingale CLT has the reciprocal Lindeberg cutoff epsilon*V_T^(-1/2); a Rademacher triangular array satisfies its premises but not its Gaussian conclusion.

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
