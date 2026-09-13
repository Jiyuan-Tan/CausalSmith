---
qid: pid_seqavg_waterfill_inference
spec: v1
topic: "For i.i.d. O=(L0,A0,L1,A1,Y), binary treatments, bounded outcomes, overlap, and the fixed regime (1,1), impose Tan-compatible sequential propensity-ratio normalizations and Zhang--Zhao marginal-history second-moment budgets. Prove that the compatible-full-law counterfactual-mean set is a compact interval exactly equal to the convex perspective program in w1=h1 and w0=h0h1, that conditional projection restores the required h0(L0,Y) factorization, and that both endpoints have compatible attaining full laws. Derive the exact two-global-price conditional clipped-affine root dual, including zero-price and unit-budget faces. On compact regular budget regions construct cross-fitted one-step endpoint processes with a joint uniform Gaussian multiplier band; extend bands by the deterministic outcome range and monotonicity to obtain honest full-calibration-ray breakdown inversion at ties, flat crossings, and absent crossings, without claiming shrinking Gaussian inference on excluded faces or inference for learned dynamic regimes. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional projection preserves the objective and normalizations while lowering the perspective budget, L^(4/3) by L2 compactness yields attainment, the corrected finite grid has regular primal-dual gaps at most 6.4e-13 and inactive-face certificates at most 5e-16, and optimized-value derivative checks support an influence function with both propensity-floor corrections. UNRESOLVED BOTTLENECK: Prove the uniform quadratic held-out mean-bias bound, score continuity, and conditional-root operator stability for the explicit cross-fitted influence function, including both propensity floors and the global-price/root perturbations. EARLY KILL TEST: On the specified finite two-baseline, two-intermediate-history, three-outcome law with active clipping at both stages, independently perturb every observed-law component and compare certified constrained-value derivatives with influence-function covariances, then jointly perturb nuisances and prices; any reproducible derivative mismatch or linear held-out bias kills the inference spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_seqavg_waterfill_inference.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: "The proposed uniform endpoint process remained unproved because the nuisance-perturbed joint-root operator and its valid positivity-preserving derivative domain were never specified."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The nuisance-indexed operator \\(\\mathcal F^{\\widetilde\\beta}\\) is never constructed: the core does not specify which entries of the heterogeneous \\(\\widetilde\\beta\\) replace which arguments of \\(\\mathcal F\\), so its Frechet derivative and uniform modulus are not determinate objects."
  - "Its condition quantifies over \\(\\mathcal B_\\beta(\\delta)\\), but the only declared localized set is \\(\\mathcal B_\\beta^+(\\delta)\\); use one declared positivity-preserving domain consistently."
  - "Once the regular-ray simultaneous band is granted, membership of \\(g_P\\) in the class defining \\(C_b\\) and hence \\(\\kappa_b^\\star\\in C_b\\) is exactly the containment observation built into def:full-ray-inversion; demote it to a corollary or add a non-definitional statistical contribution."
reusable_artifacts:
  - "discovery/gaps.json — verified literature/open-problem map."
  - "discovery/proto_core.json — final transported-perspective program and two-price proposal coordinates; inference claims remain unvalidated."
  - "reviews/angle0_v1.json through reviews/angle0_v5.json — complete defect and comparator history for avoiding repeated formulations."
seeds_burned:
  - index: 0
    one_liner: "sequential-perspective-sharpness"
    reason: "Five same-angle revisions, including one validity-gate-authorized root repair, left the inference operator undefined and repeated definitional/redundant claims."
proof_attempt_summary: |
  Five D-0.5 revisions developed the two-decision transported-perspective sharpness proposal,
  conditional projection, endpoint attainment, and a clipped-affine two-price dual. The inference
  spine collapsed because the final core still did not construct its nuisance-perturbed root
  operator or a coherent positivity-preserving derivative domain; its advertised full-ray result
  also remained deterministic containment rather than a separate theorem. A future attempt must
  define that operator and prove its orthogonality/remainder theory before making uniform-in-budget
  inference claims, while incorporating the Jin--Ren--Zhou f-sensitivity comparator.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 29882670
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 29882670
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# pid_seqavg_waterfill_inference / v1 — Failed

**Topic.** For i.i.d. O=(L0,A0,L1,A1,Y), binary treatments, bounded outcomes, overlap, and the fixed regime (1,1), impose Tan-compatible sequential propensity-ratio normalizations and Zhang--Zhao marginal-history second-moment budgets. Prove that the compatible-full-law counterfactual-mean set is a compact interval exactly equal to the convex perspective program in w1=h1 and w0=h0h1, that conditional projection restores the required h0(L0,Y) factorization, and that both endpoints have compatible attaining full laws. Derive the exact two-global-price conditional clipped-affine root dual, including zero-price and unit-budget faces. On compact regular budget regions construct cross-fitted one-step endpoint processes with a joint uniform Gaussian multiplier band; extend bands by the deterministic outcome range and monotonicity to obtain honest full-calibration-ray breakdown inversion at ties, flat crossings, and absent crossings, without claiming shrinking Gaussian inference on excluded faces or inference for learned dynamic regimes. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional projection preserves the objective and normalizations while lowering the perspective budget, L^(4/3) by L2 compactness yields attainment, the corrected finite grid has regular primal-dual gaps at most 6.4e-13 and inactive-face certificates at most 5e-16, and optimized-value derivative checks support an influence function with both propensity-floor corrections. UNRESOLVED BOTTLENECK: Prove the uniform quadratic held-out mean-bias bound, score continuity, and conditional-root operator stability for the explicit cross-fitted influence function, including both propensity floors and the global-price/root perturbations. EARLY KILL TEST: On the specified finite two-baseline, two-intermediate-history, three-outcome law with active clipping at both stages, independently perturb every observed-law component and compare certified constrained-value derivatives with influence-function covariances, then jointly perturb nuisances and prices; any reproducible derivative mismatch or linear held-out bias kills the inference spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_seqavg_waterfill_inference.md.

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** The nuisance-indexed operator F^{tilde beta} is never constructed, so its Frechet derivative and uniform modulus are not determinate objects; the D-0.5 revision cap was exhausted.

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
