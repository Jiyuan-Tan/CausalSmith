---
qid: pid_imperfectiv_sharp_cone
spec: v1
topic: "Aggregate-support pruning and boundary-safe sharp correlation-cone envelopes for imperfect-IV effects. Observe i.i.d. finite-valued treatment and instrument cells with bounded potential outcomes, consistency, SDC or SDC+LEI, and Ban-Kedagni aggregate support equality Supp(Y_d|D=d)=Supp(Y_d|D!=d)=[l_d,u_d], with no cross-arm restriction. For each sign branch form the compact missing-cell completion polytope and define tau as the maximum total interior slack. Prove a branch admits aggregate-support completion iff tau>0; unrestricted nonnegative-cone duals give its sharp arm-mean closure, and conditional product coupling gives the sharp ATE closure. Compute feasibility, tau, and endpoints by finite LPs or certified two-dimensional cone-arrangement enumeration. Prove the supplied rational four-cell example has sharp closure [711/1100,911/1100], strictly inside the published normalized outer union. For the explicit three-cell SDC family, prove disappearance of a branch makes the mean and ATE set maps Hausdorff-discontinuous and yields a 0.15 two-point minimax Hausdorff-risk lower bound. Construct a Hoeffding projection region over cell masses and bounded outcome-mass moments with finite-sample simultaneous coverage of the whole exact set. Credit Ban-Kedagni for validity and earlier cone discussion, Park for the different MIV+MTR problem, and generic mathematical-program inference; do not claim an LEI boundary from the SDC witness, clustered/covariate inference, empirical sign reversal, or unrestricted contraction. Ban-Kedagni NLSYM and Zhanhan Yu PM2.5 applications are same-population-restriction consumers whose reported object changes from a valid normalized outer region to the exact support-filtered set with a boundary diagnostic. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh derivations reduced each branch to a bounded completion polytope, proved unrestricted-cone endpoint duality and aggregate BOS eligibility iff tau>0, constructed full-support endpoint approximations, and established simultaneous arm completion by conditional product coupling. Exact rational and LP calculations recovered [711/1100,911/1100] versus [0.496024,0.872824]; 72 further primal-dual arrangement checks passed. The three-cell SDC experiment was enumerated on both arms, its tilted density was shown positive for |epsilon|<3/110, and total-variation control yielded the 0.15 two-point Hausdorff-risk bound. Structural zeros, empty branches, ties, degenerate LEI variance, and score scaling were checked; no specific support-pruned collision was found. UNRESOLVED BOTTLENECK: No theorem-critical bottleneck remains at subfield scope; production work must certify exact feasibility and tau=0 decisions near degeneracy while preserving the fixed-grid, aggregate-support, and SDC-only boundary claims. EARLY KILL TEST: Recompute the three-cell branches at epsilon=-0.001,0,0.001 and both product-coupled arms; stop if an implementation retains mean 0.3 at epsilon=0 under aggregate BOS, claims uniform shrinking along positive epsilon_n=o(1/n), or labels this witness as LEI. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_imperfectiv_sharp_cone.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "They do not deliver the adaptive contracting procedure or matching general boundary rate posed in oeq:boundary-adaptive-inference, and the statistical lower result is confined to a constructed SDC two-point experiment."
  - "The leading-journal score is constrained by the fixed finite grid, known support endpoints, conservative binary-treatment inference, and absence of an actual reanalysis demonstrating how much the support-filtered set changes the cited applications."
  - "The TL;DR's phrase 'covers the whole exact set' slightly overstates the theorem, which covers the sharp closure of an identified set that need not itself be closed under exact-support restrictions."
reusable_artifacts:
  - "discovery/core.json — proved theorem graph, including the support-eligibility LP, all-arm transfer, parametric strictness family, and root-n boundary theorem"
  - "discovery/solve_thm_support_eligibility.tex — empty-polytope-safe eligibility/slack argument"
  - "discovery/solve_prop_rational_certificates.tex — exact rational witness and certificate construction"
  - "discovery/solve_thm_boundary_root_n_minimax.tex — exact chi-square tensorization and known-pair root-n minimax result"
seeds_burned:
  - index: 0
    one_liner: "seed-exact-support-cone"
    reason: "The accepted angle produced sound subfield mathematics but could not reach the field floor without solving the open adaptive-inference crux, broadening the model, or adding an application reanalysis."
proof_attempt_summary: |
  The run proved the finite-grid aggregate-support pruning and sharp-closure package, including all-arm transfer, a robust strict-improvement family, exact rational certificates, and a known-pair root-n boundary minimax result. Correctness and decision referees passed, but the field-tier claim collapsed at the novelty gate because the adaptive contracting procedure and general boundary rate remain open, inference is conservative and specialized, and no cited application was reanalyzed. The sound package is retained at subfield tier for a future re-raise that solves the adaptive OEQ or materially broadens the model or empirical analysis.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 17441578
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 17441578
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# pid_imperfectiv_sharp_cone / v1 — Downgraded

**Topic.** Aggregate-support pruning and boundary-safe sharp correlation-cone envelopes for imperfect-IV effects. Observe i.i.d. finite-valued treatment and instrument cells with bounded potential outcomes, consistency, SDC or SDC+LEI, and Ban-Kedagni aggregate support equality Supp(Y_d|D=d)=Supp(Y_d|D!=d)=[l_d,u_d], with no cross-arm restriction. For each sign branch form the compact missing-cell completion polytope and define tau as the maximum total interior slack. Prove a branch admits aggregate-support completion iff tau>0; unrestricted nonnegative-cone duals give its sharp arm-mean closure, and conditional product coupling gives the sharp ATE closure. Compute feasibility, tau, and endpoints by finite LPs or certified two-dimensional cone-arrangement enumeration. Prove the supplied rational four-cell example has sharp closure [711/1100,911/1100], strictly inside the published normalized outer union. For the explicit three-cell SDC family, prove disappearance of a branch makes the mean and ATE set maps Hausdorff-discontinuous and yields a 0.15 two-point minimax Hausdorff-risk lower bound. Construct a Hoeffding projection region over cell masses and bounded outcome-mass moments with finite-sample simultaneous coverage of the whole exact set. Credit Ban-Kedagni for validity and earlier cone discussion, Park for the different MIV+MTR problem, and generic mathematical-program inference; do not claim an LEI boundary from the SDC witness, clustered/covariate inference, empirical sign reversal, or unrestricted contraction. Ban-Kedagni NLSYM and Zhanhan Yu PM2.5 applications are same-population-restriction consumers whose reported object changes from a valid normalized outer region to the exact support-filtered set with a boundary diagnostic. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Fresh derivations reduced each branch to a bounded completion polytope, proved unrestricted-cone endpoint duality and aggregate BOS eligibility iff tau>0, constructed full-support endpoint approximations, and established simultaneous arm completion by conditional product coupling. Exact rational and LP calculations recovered [711/1100,911/1100] versus [0.496024,0.872824]; 72 further primal-dual arrangement checks passed. The three-cell SDC experiment was enumerated on both arms, its tilted density was shown positive for |epsilon|<3/110, and total-variation control yielded the 0.15 two-point Hausdorff-risk bound. Structural zeros, empty branches, ties, degenerate LEI variance, and score scaling were checked; no specific support-pruned collision was found. UNRESOLVED BOTTLENECK: No theorem-critical bottleneck remains at subfield scope; production work must certify exact feasibility and tau=0 decisions near degeneracy while preserving the fixed-grid, aggregate-support, and SDC-only boundary claims. EARLY KILL TEST: Recompute the three-cell branches at epsilon=-0.001,0,0.001 and both product-coupled arms; stop if an implementation retains mean 0.3 at epsilon=0 under aggregate BOS, claims uniform shrinking along positive epsilon_n=o(1/n), or labels this witness as LEI. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_imperfectiv_sharp_cone.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the sound delivered package subfield with paper_score_ceiling 6.6 below the field floor 7.4 and salvageable=false.

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
