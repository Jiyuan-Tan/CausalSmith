---
qid: eid_crl_coverratio_mmd_genericity
spec: v1
topic: "Generic characteristic-kernel cover-ratio recovery from one unknown-target perfect intervention per latent node. For every finite labeled DAG G and derivative-sign vector s, work in the relative product C2 topology on positive normalized C3 conditional mechanisms and perfect-intervention densities on [0,1], with faithful observational law and arbitrary shared C2 diffeomorphic mixing. With observable ratios R_i=dP^i/dP^0 and D_ji the Gaussian-kernel MMD between Law_0(R_i) and Law_j(R_i), prove that positive D_ji on every ancestral cover is open dense in every nonempty DAG/sign stratum. Derive the ancestral order from the ratio graph, componentwise coordinates by conditional ranks, the target assignment and exact faithful DAG by parent pruning, plus sample-split MMD confidence edges and conditional-CDF coordinate rates. Use the certified 1->2 plus isolated-3 witness with p2(y|x)=1+0.1(2x-1)(2y-1) and q_i(z)=4exp(4z)/(exp(4)-1). ROPES is the protocol consumer only after adopting a compliant positive common-support intervention generator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Normalized affine interpolation toward a sparse edge witness preserves normalization globally and positivity, fixed derivative signs, and faithfulness locally. The direct-edge second-moment contrast is analytic and nonzero at the endpoint, so its zeros are isolated; this derives open-dense direct-edge separation and therefore characteristic-kernel cover separation. The sparse witness has an analytic moment gap above 3e-4 and Gaussian MMD above 5e-8. Exact faithful cancellation families, isolated nodes, multiple roots, forks, colliders, opposite parent effects, redundant edges, and disconnected admissibility strata were checked; no current-literature collision was found. UNRESOLVED BOTTLENECK: Prove uniform conditional-CDF coordinate rates when both response thresholds and conditioning covariates are estimated log-density ratios on an explicitly bounded Holder subclass. EARLY KILL TEST: Independently verify the analytic moment-integral identity along the normalized affine path from the exact cancellation example to the sparse witness, including preservation of finite positive faithfulness and derivative-sign margins near its start. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_crl_coverratio_mmd_genericity.md."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - Causalean/Mathlib/MeasureTheory/Integral/UniformConvergence.lean
  - Causalean/Mathlib/MeasureTheory/UnitInterval/OpenPos.lean
  - Causalean/Mathlib/Topology/UniformConvergence/Affine.lean
seeds_burned: []
proof_attempt_summary: |
  The run proved the generic cover-separation, exact ratio-decoder, sparse-witness,
  and sample-split confidence-edge results with no remaining proof debt. It required
  reusable Gaussian moment-recovery substrate plus paper-local conditional-independence,
  faithfulness, analytic-path, and RKHS concentration bridges. The stronger uniform
  conditional-CDF coordinate-rate frontier remains outside the accepted theorem package.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 856387909
  pipeline_claude_tokens: 31269221
  pipeline_tokens_consumed: 887657130
  total_tokens_consumed: null
banked_on: "2026-09-09"
paper_score: 6.6
paper_score_rationale: "The paper contains a substantial and apparently novel population identification result, but its publication case is weakened by a stale verification record, an incompletely specified decoder outside its theorem domain, and a manuscript architecture that obscures the contribution."
---

# eid_crl_coverratio_mmd_genericity / v1 — Accepted

**Topic.** Generic characteristic-kernel cover-ratio recovery from one unknown-target perfect intervention per latent node. For every finite labeled DAG G and derivative-sign vector s, work in the relative product C2 topology on positive normalized C3 conditional mechanisms and perfect-intervention densities on [0,1], with faithful observational law and arbitrary shared C2 diffeomorphic mixing. With observable ratios R_i=dP^i/dP^0 and D_ji the Gaussian-kernel MMD between Law_0(R_i) and Law_j(R_i), prove that positive D_ji on every ancestral cover is open dense in every nonempty DAG/sign stratum. Derive the ancestral order from the ratio graph, componentwise coordinates by conditional ranks, the target assignment and exact faithful DAG by parent pruning, plus sample-split MMD confidence edges and conditional-CDF coordinate rates. Use the certified 1->2 plus isolated-3 witness with p2(y|x)=1+0.1(2x-1)(2y-1) and q_i(z)=4exp(4z)/(exp(4)-1). ROPES is the protocol consumer only after adopting a compliant positive common-support intervention generator. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Normalized affine interpolation toward a sparse edge witness preserves normalization globally and positivity, fixed derivative signs, and faithfulness locally. The direct-edge second-moment contrast is analytic and nonzero at the endpoint, so its zeros are isolated; this derives open-dense direct-edge separation and therefore characteristic-kernel cover separation. The sparse witness has an analytic moment gap above 3e-4 and Gaussian MMD above 5e-8. Exact faithful cancellation families, isolated nodes, multiple roots, forks, colliders, opposite parent effects, redundant edges, and disconnected admissibility strata were checked; no current-literature collision was found. UNRESOLVED BOTTLENECK: Prove uniform conditional-CDF coordinate rates when both response thresholds and conditioning covariates are estimated log-density ratios on an explicitly bounded Holder subclass. EARLY KILL TEST: Independently verify the analytic moment-integral identity along the normalized affine path from the exact cancellation example to the sparse witness, including preservation of finite positive faithfulness and derivative-sign margins near its start. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_crl_coverratio_mmd_genericity.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** Supervisor-approved field-tier acceptance after clean F5, matched dual F4 reviews, full build, source scan, and axiom audit.

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
