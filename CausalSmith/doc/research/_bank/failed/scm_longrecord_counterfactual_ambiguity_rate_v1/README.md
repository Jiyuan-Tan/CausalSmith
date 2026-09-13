---
qid: scm_longrecord_counterfactual_ambiguity_rate
spec: v1
topic: "For finite-state, finite-action stationary iid-response SCMs with a known nominal controlled transition law whose positive cells are at least epsilon, fixed factual and alternative policies, an arbitrary observation map, bounded rewards, and a nominal target-policy Poisson solution of span at most B, study the sharp interval of the same unit's conditional counterfactual average reward after a factual record of length T. Prove an explicit C(d,k,epsilon,B)/sqrt(T) upper bound on the expected interval diameter uniformly over the complete compatible canonical-response polytope, without imposing a lower bound on response masses or contraction of every conditional counterfactual kernel. Prove sharpness using the legal full-support binary feedback construction, give attained exact finite response-program endpoints, and provide honest simultaneous confidence-fiber coverage when the nominal transition law is estimated from independent calibration data. Do not claim recordwise shrinkage or apply the result to absorbing targets that violate the Poisson condition. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A conditional Poisson decomposition yields an explicit O(sqrt(log T/T)) whole-class bound; all 28 binary antipodal segments admit a uniform expected-diameter bound of 180/sqrt(T) by endpoint linearity, Abel-Doob arguments, and integrable geometric-Walsh derivative energy; exact checks validate the positive feedback witness, hidden-HMM recursion, and derivative identities. UNRESOLVED BOTTLENECK: Prove the root-T martingale-family maximal inequality uniformly over the entire higher-dimensional response polytope; the solved edges do not control arbitrary mixtures. EARLY KILL TEST: Analyze the explicit synchronizer/two-permutation triangle over its full two-dimensional parameter square and either prove a T-independent root-T bound or exhibit a legal T-dependent selection with divergent normalized width; conditional-positivity assumptions do not pass. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_longrecord_counterfactual_ambiguity_rate.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The promised complete-fiber root-T expected-diameter theorem is not delivered: this node proves only O(sqrt(log T/T)) while leaving the root-T maximal inequality open; either resolve that obligation or reframe the proposal around the weaker proved kernel."
reusable_artifacts:
  - "discovery/solve_thm_legal_triangle_and_universal_logarithmic_bound.json — sound whole-fiber O(sqrt(log T/T)) bound and legal triangle boundary control."
  - "discovery/solve_thm_binary_sharpness.json — full-support binary Omega(1/sqrt(T)) lower obstruction."
  - "discovery/solve_prop_stationary_shared_response_endpoints.json — attained exact finite response-program endpoints."
  - "discovery/solve_thm_confidence_fiber.json — simultaneous confidence-fiber containment."
  - "discovery/solve_oeq_polytope_maximal_inequality.json — recorded failed route and remaining full-interior/all-faces maximal-inequality obligation."
seeds_burned: []
proof_attempt_summary: |
  D0 established exact endpoints, confidence-fiber containment, a legal triangle with root-T boundary
  control, a binary root-T lower obstruction, and a complete-fiber O(sqrt(log T/T)) upper bound.
  The attempted predictable-scale and face-localization routes did not control the triangle interior
  or arbitrary mixtures uniformly, so the promised complete-polytope root-T upper bound remained open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 43668086
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 43668086
  total_tokens_consumed: null
banked_on: "2026-09-08"
---

# scm_longrecord_counterfactual_ambiguity_rate / v1 — Failed

**Topic.** For finite-state, finite-action stationary iid-response SCMs with a known nominal controlled transition law whose positive cells are at least epsilon, fixed factual and alternative policies, an arbitrary observation map, bounded rewards, and a nominal target-policy Poisson solution of span at most B, study the sharp interval of the same unit's conditional counterfactual average reward after a factual record of length T. Prove an explicit C(d,k,epsilon,B)/sqrt(T) upper bound on the expected interval diameter uniformly over the complete compatible canonical-response polytope, without imposing a lower bound on response masses or contraction of every conditional counterfactual kernel. Prove sharpness using the legal full-support binary feedback construction, give attained exact finite response-program endpoints, and provide honest simultaneous confidence-fiber coverage when the nominal transition law is estimated from independent calibration data. Do not claim recordwise shrinkage or apply the result to absorbing targets that violate the Poisson condition. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A conditional Poisson decomposition yields an explicit O(sqrt(log T/T)) whole-class bound; all 28 binary antipodal segments admit a uniform expected-diameter bound of 180/sqrt(T) by endpoint linearity, Abel-Doob arguments, and integrable geometric-Walsh derivative energy; exact checks validate the positive feedback witness, hidden-HMM recursion, and derivative identities. UNRESOLVED BOTTLENECK: Prove the root-T martingale-family maximal inequality uniformly over the entire higher-dimensional response polytope; the solved edges do not control arbitrary mixtures. EARLY KILL TEST: Analyze the explicit synchronizer/two-permutation triangle over its full two-dimensional parameter square and either prove a T-independent root-T bound or exhibit a legal T-dependent selection with divergent normalized width; conditional-positivity assumptions do not pass. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_longrecord_counterfactual_ambiguity_rate.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@thm:legal-triangle-and-universal-logarithmic-bound: the complete-fiber theorem proves only O(sqrt(log T/T)) while the promised complete-polytope C(d,k,epsilon,B)/sqrt(T) bound remains open.

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
