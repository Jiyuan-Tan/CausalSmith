---
qid: eid_latentk_variance_fiber
spec: v2
topic: "Parameterized-complexity frontier for latent-K Gaussian innovation-variance fibers. Input a rational positive-definite covariance faithful to an undirected no-collider forest and K; define each component-root signature by its exact Gaussian regression residual variances. Completely classify whether a root tuple with at most K distinct labels exists, conjecturally by a faithful rational W[1]-hardness reduction with a linear-K ETH lower bound, while accepting a twin-star-resistant f(K) polynomial algorithm if that is the correct answer. Extend the classification to uniqueness and two-witness recovery. For a supplied component order, prove the exact (K+1)2^q polynomial DP and a matching q lower bound, where q is the maximum set of labels recurring across a cut. Use Gaussian covariance-confidence-region projection for orientation and total-effect inference. Consumer: SEMgraph's bottom-up equal-error-variance mode. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived root-union and root-locus characterizations, polynomial dictionary verification, a d^K polynomial algorithm when components have size at most d, and a faithful independent two-node covariance block whose identical two-root signature transfers nonemptiness to two-witness recovery while preserving q. The ordered q-DP matched exhaustive enumeration on 83 forests and 14,800 budget/order checks. Destructive work confirmed that common-center star set-cover gadgets have a cheap universal witness, varying centers introduces costly complementary labels, and Gaussian signatures obey product and rational-square constraints; no collision was found. UNRESOLVED BOTTLENECK: Build a faithful rational Gaussian selector-and-compatibility realization with linear parameter budget and no unintended internal-root witnesses, or derive a symbolic K-FPT invariant that avoids such a reduction. EARLY KILL TEST: Exhaustively enumerate one three-choice selector and one compatibility gadget, verifying exact intended root tuples, rational positive-definite faithful covariance, and bounded auxiliary-label cost; any cheap unintended witness kills that reduction template. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_latentk_variance_fiber.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Unrestricted K-Fiber feasibility and uniqueness classification and the matching recurrence-width lower bound remain open; only restricted algorithms and supporting structural results were delivered."
reusable: solver_blocked
reraise_status: unknown
gap_reasons:
  - "The proposed unrestricted latent-K classification (FPT or faithful linear-budget hardness) remains an open question; the delivered bounded-d and supplied-order algorithms are a strictly weaker kernel and must be positioned as such rather than as resolution of that frontier."
  - "no theorem determines whether unrestricted K-Fiber is FPT or parameterized-hard."
reusable_artifacts:
  - discovery/writeup.tex
  - discovery/core.json
  - discovery/solve_thm_bounded_choice.tex
  - discovery/solve_thm_ordered_dp.tex
  - reviews/angle0_v2.json
seeds_burned: []
proof_attempt_summary: |
  The run repaired and proved the rational tree-covariance realization criterion, root-locus structure, a bounded-component d^K algorithm, a refined supplied-order dynamic program, and a two-valued total-effect fiber theorem. The attempted selector/compatibility reductions failed because common-center gadgets admit a cheap universal witness while varying centers create complementary labels, and no twin-star-resistant FPT invariant emerged. Unrestricted feasibility and uniqueness in K, plus the matching recurrence-width lower bound, therefore remain open and cannot be replaced by the restricted results.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 16239064
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 16239064
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_latentk_variance_fiber / v2 — Failed

**Topic.** Parameterized-complexity frontier for latent-K Gaussian innovation-variance fibers. Input a rational positive-definite covariance faithful to an undirected no-collider forest and K; define each component-root signature by its exact Gaussian regression residual variances. Completely classify whether a root tuple with at most K distinct labels exists, conjecturally by a faithful rational W[1]-hardness reduction with a linear-K ETH lower bound, while accepting a twin-star-resistant f(K) polynomial algorithm if that is the correct answer. Extend the classification to uniqueness and two-witness recovery. For a supplied component order, prove the exact (K+1)2^q polynomial DP and a matching q lower bound, where q is the maximum set of labels recurring across a cut. Use Gaussian covariance-confidence-region projection for orientation and total-effect inference. Consumer: SEMgraph's bottom-up equal-error-variance mode. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Derived root-union and root-locus characterizations, polynomial dictionary verification, a d^K polynomial algorithm when components have size at most d, and a faithful independent two-node covariance block whose identical two-root signature transfers nonemptiness to two-witness recovery while preserving q. The ordered q-DP matched exhaustive enumeration on 83 forests and 14,800 budget/order checks. Destructive work confirmed that common-center star set-cover gadgets have a cheap universal witness, varying centers introduces costly complementary labels, and Gaussian signatures obey product and rational-square constraints; no collision was found. UNRESOLVED BOTTLENECK: Build a faithful rational Gaussian selector-and-compatibility realization with linear parameter budget and no unintended internal-root witnesses, or derive a symbolic K-FPT invariant that avoids such a reduction. EARLY KILL TEST: Exhaustively enumerate one three-choice selector and one compatibility gadget, verifying exact intended root tuples, rational positive-definite faithful covariance, and bounded auxiliary-label cost; any cheap unintended witness kills that reduction template. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_latentk_variance_fiber.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposed unrestricted latent-K classification remains open; the delivered bounded-component and supplied-order algorithms are a strictly weaker substituted kernel.

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
