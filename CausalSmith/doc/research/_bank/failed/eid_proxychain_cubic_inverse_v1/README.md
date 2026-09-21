---
qid: eid_proxychain_cubic_inverse
spec: v1
topic: "Rational cubic identification and correction of the one-proxy LvLiNGAM boundary. Observe iid X=(X1,X2,X3) from X=(I-B)^(-1)(gamma H+D_s xi), where B is one of six labeled positive two-edge chains, edge coefficients and global loadings lie in [1/4,3/4], residual scales lie in [3/4,5/4], and the four independent centered sources have support in [-2,2], variance one and third cumulant in [1/2,1]. Prove that C3 alone globally identifies the chain and both coefficients: the unique rank-two cubic slice identifies the root, its signed kernel identifies the middle, and explicit adjugate contractions recover both edges with uniform denominator bounds. On the exact Tramontano-Kivva-Salehkaleybar-Drton-Kiyavash one-proxy graph, reproduce and saturate the released Macaulay2 elimination, reconcile Theorem 3.6, and characterize genuine nonidentification versus removable chart failures outside the positive chamber. Prove covariance-only opposite-chain overlap on a nonempty open set. Give a constant-time rational algorithm and bounded-data moment-inversion confidence set with uniform finite-sample coverage and root-n diameter on denominator-separated subclasses, without requiring nonsingular influence covariance. Consumer: replace the fourth-cumulant proxy branch in CEId-from-Moments by a certified cubic branch on the positive-skew class, with ambiguity warnings on the audited failure divisor. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent algebra derived M_a=hx gg'+r dd', kernel k=(-uz,z+vy,-y), N=hxr(uyz,-y(z+vy),y^2), W=-hxrt yz(0,1,v), and the rational edge formulas; it also derived slice determinants and uniform denominators. Exact arithmetic recovered u=1/2,v=2/5 in the legal Bernoulli witness, 1,200 numerical relabelings passed, and an interior reversal-symmetric covariance witness had an invertible nuisance Jacobian. The released covariance equations and 60 cubic residual equations were reconstructed; a linear elimination certificate and localized generic degree one were derived. Hoeffding moment rectangles yielded honest inversion and root-n diameter without covariance inversion. Same-box twins, scaling, source permutations, graph-transpose conventions, zero denominators, negative-sign failures, singular moment covariance, bounded-source realizability were checked; no correction or collision was found. UNRESOLVED BOTTLENECK: Classify all real coefficient/order fibers outside the positive box, especially intersections of rank and denominator hypersurfaces, separating genuine ambiguity from removable adjugate-chart failures. EARLY KILL TEST: Run the pinned Macaulay2 file, reduce beta*W_b-W_c against its full elimination ideal, and localize at W_b; a nonzero remainder or retained generic second full-system root stops the correction claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_proxychain_cubic_inverse.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The promised outside-positive-chamber all-intersection real-fiber atlas was replaced by a principal-chart inverse plus two boundary examples; prop:analytic-full-ideal-membership also has undefined nu for u, and the Figure 3 target-coordinate equality is not established."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The unrestricted one-proxy third-order boundary is not fully corrected: the note proves generic identification of beta only on the localized chart where W_2^{el} is nonzero, while the exceptional divisor and its real fibers remain open."
  - "Stage 0.5 (typed) finding outside D0.R core-edit scope — kernel_substituted@oeq:real-fiber-atlas."
  - "Undefined \\nu should be u in prop:analytic-full-ideal-membership."
  - "The Figure 3 convention T=2, Y=3, hence b_{Y,T}=beta=(B_pi)_{32}, is not established."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_global_cubic_inverse.tex
  - discovery/solve_thm_covariance_overlap.tex
  - discovery/solve_thm_honest_inversion.tex
  - discovery/solve_thm_localized_full_ideal_reaudit.tex
seeds_burned: []
proof_attempt_summary: |
  D0 derived a rational cubic inverse on a principal real semialgebraic chart, a
  positive-box quantitative corollary, covariance-only overlap, and a theoretical
  finite-sample inversion route. The field-level promise collapsed because the
  exceptional all-intersection real-fiber atlas remained open and would require a
  substantive new derivation. Two local correctness defects also remained in proved
  nodes, so the current artifact could not be banked as a sound subfield downgrade.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 90938283
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 90938283
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_proxychain_cubic_inverse / v1 — Failed

**Topic.** Rational cubic identification and correction of the one-proxy LvLiNGAM boundary. Observe iid X=(X1,X2,X3) from X=(I-B)^(-1)(gamma H+D_s xi), where B is one of six labeled positive two-edge chains, edge coefficients and global loadings lie in [1/4,3/4], residual scales lie in [3/4,5/4], and the four independent centered sources have support in [-2,2], variance one and third cumulant in [1/2,1]. Prove that C3 alone globally identifies the chain and both coefficients: the unique rank-two cubic slice identifies the root, its signed kernel identifies the middle, and explicit adjugate contractions recover both edges with uniform denominator bounds. On the exact Tramontano-Kivva-Salehkaleybar-Drton-Kiyavash one-proxy graph, reproduce and saturate the released Macaulay2 elimination, reconcile Theorem 3.6, and characterize genuine nonidentification versus removable chart failures outside the positive chamber. Prove covariance-only opposite-chain overlap on a nonempty open set. Give a constant-time rational algorithm and bounded-data moment-inversion confidence set with uniform finite-sample coverage and root-n diameter on denominator-separated subclasses, without requiring nonsingular influence covariance. Consumer: replace the fourth-cumulant proxy branch in CEId-from-Moments by a certified cubic branch on the positive-skew class, with ambiguity warnings on the audited failure divisor. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent algebra derived M_a=hx gg'+r dd', kernel k=(-uz,z+vy,-y), N=hxr(uyz,-y(z+vy),y^2), W=-hxrt yz(0,1,v), and the rational edge formulas; it also derived slice determinants and uniform denominators. Exact arithmetic recovered u=1/2,v=2/5 in the legal Bernoulli witness, 1,200 numerical relabelings passed, and an interior reversal-symmetric covariance witness had an invertible nuisance Jacobian. The released covariance equations and 60 cubic residual equations were reconstructed; a linear elimination certificate and localized generic degree one were derived. Hoeffding moment rectangles yielded honest inversion and root-n diameter without covariance inversion. Same-box twins, scaling, source permutations, graph-transpose conventions, zero denominators, negative-sign failures, singular moment covariance, bounded-source realizability were checked; no correction or collision was found. UNRESOLVED BOTTLENECK: Classify all real coefficient/order fibers outside the positive box, especially intersections of rank and denominator hypersurfaces, separating genuine ambiguity from removable adjugate-chart failures. EARLY KILL TEST: Run the pinned Macaulay2 file, reduce beta*W_b-W_c against its full elimination ideal, and localize at W_b; a nonzero remainder or retained generic second full-system root stops the correction claim. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_proxychain_cubic_inverse.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 found kernel_substituted@oeq:real-fiber-atlas; the field promise remains open, and two proved claims retain unresolved correctness defects.

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
