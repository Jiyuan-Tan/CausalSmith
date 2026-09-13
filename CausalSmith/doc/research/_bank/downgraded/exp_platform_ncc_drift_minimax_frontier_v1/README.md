---
qid: exp_platform_ncc_drift_minimax_frontier
spec: v1
topic: "Sharp design-based borrowing frontier for nonconcurrent platform controls under bounded calendar drift. Fix ordered enrollment blocks with bounded fixed potential outcomes, a shared control, a focal arm available only on a proper block window, and known history-predictable propensities that are positive exactly on available arms. Target the window-weighted finite-population arm-versus-control contrast under a total-variation budget Gamma on fixed control block means. Characterize up to universal constants the minimax worst-case expected length among all uniformly honest randomization intervals; construct a finite-convex-program predictable-AIPW borrowing rule and bias-aware martingale interval attaining it; prove a matching all-interval randomization lower bound; and give an optimizer-based necessary-and-sufficient condition for strict improvement over concurrent-only inference, including Gamma=0 full borrowing and the vacuous-drift concurrent-only regime. Consumer: the NCC R package and Bofill Roig et al.'s ACTT calibration. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact cumulative-sum dual for the worst-case drift bias: for normalized block weights, summation by parts reduces the total-variation support function to a finite linear program in cumulative weight discrepancies, with an explicit extremal drift witness. Combining this bias with predictable bounded-martingale variation yields a finite SOCP-type upper frontier. In the three-block symmetric witness, borrowing weight x has bias x Gamma and randomization standard deviation 2M(1-x)/sqrt(n), displaying the expected borrowing phase change. Boundary checks covered Gamma=0, vacuous drift, small concurrent samples, small propensities, deterministic external controls, and parameter-diameter saturation; no literature collision was found. UNRESOLVED BOTTLENECK: Construct fuzzy priors on fixed schedules that obey the TV constraint almost surely and control the sequential observed-data likelihood ratio, thereby matching the optimized clipped bias-martingale radius uniformly for arbitrary history-adaptive propensities. EARLY KILL TEST: For three blocks with one- or two-unit block sizes and outcomes on {-M,0,M}, enumerate every assignment path and solve the exact uniformly honest variable-length-interval LP. Stop or pivot if its minimax length is not within a uniform constant of the proposed convex frontier, or if it borrows where the claimed concurrent-only modulus equality holds."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The delivered theory gives a sharp masked-history lower certificate and AIPW upper construction, but no matching all-kernel minimax frontier or necessary-and-sufficient all-kernel borrowing criterion."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "kernel_substituted at thm:adaptive-minimax-sandwich-sharp-mask because the promised matching frontier became a candid sandwich+separation"
  - "paper_score_ceiling 5.8 < field threshold 7.2"
  - "The fixed-floor converse is false as stated."
reusable_artifacts:
  - "discovery/core.json — accepted D0 theorem graph, including the sharp continuum-mask lower certificate and rare-history separation"
  - "discovery/solve_prop_three_block_kill_test.json — exact three-block finite experiment and primal/dual certificate"
  - "discovery/solve_thm_honest_upper_frontier.json — predictable-AIPW upper construction and bounded-drift optimization"
  - "discovery/solve_oeq_adaptive_all_interval_converse.json — attempted all-interval converse and the unresolved comparison boundary"
seeds_burned:
  - index: 0
    one_liner: "known-gamma-minimax-borrowing-frontier"
    reason: "The sole accepted proposal angle converged to a sound sandwich-and-separation result, not the promised matching field-level minimax frontier."
proof_attempt_summary: |
  The run proved a finite-sample predictable-AIPW upper bound, an optimized observed-law lower envelope,
  a sharp continuum-mask certificate, and a rare-history separation showing that the AIPW radius need not
  match unrestricted minimax interval length. The promised matching all-kernel frontier collapsed: even a
  common propensity floor can allow L*=0 while the clipped AIPW radius is 2M, so the proposed finite-constant
  converse is false in the stated class. A narrower regime with additional information/reachability structure
  would need genuinely new theory rather than a bounded repair.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 58159270
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 58159270
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# exp_platform_ncc_drift_minimax_frontier / v1 — Downgraded

**Topic.** Sharp design-based borrowing frontier for nonconcurrent platform controls under bounded calendar drift. Fix ordered enrollment blocks with bounded fixed potential outcomes, a shared control, a focal arm available only on a proper block window, and known history-predictable propensities that are positive exactly on available arms. Target the window-weighted finite-population arm-versus-control contrast under a total-variation budget Gamma on fixed control block means. Characterize up to universal constants the minimax worst-case expected length among all uniformly honest randomization intervals; construct a finite-convex-program predictable-AIPW borrowing rule and bias-aware martingale interval attaining it; prove a matching all-interval randomization lower bound; and give an optimizer-based necessary-and-sufficient condition for strict improvement over concurrent-only inference, including Gamma=0 full borrowing and the vacuous-drift concurrent-only regime. Consumer: the NCC R package and Bofill Roig et al.'s ACTT calibration. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived the exact cumulative-sum dual for the worst-case drift bias: for normalized block weights, summation by parts reduces the total-variation support function to a finite linear program in cumulative weight discrepancies, with an explicit extremal drift witness. Combining this bias with predictable bounded-martingale variation yields a finite SOCP-type upper frontier. In the three-block symmetric witness, borrowing weight x has bias x Gamma and randomization standard deviation 2M(1-x)/sqrt(n), displaying the expected borrowing phase change. Boundary checks covered Gamma=0, vacuous drift, small concurrent samples, small propensities, deterministic external controls, and parameter-diameter saturation; no literature collision was found. UNRESOLVED BOTTLENECK: Construct fuzzy priors on fixed schedules that obey the TV constraint almost surely and control the sequential observed-data likelihood ratio, thereby matching the optimized clipped bias-martingale radius uniformly for arbitrary history-adaptive propensities. EARLY KILL TEST: For three blocks with one- or two-unit block sizes and outcomes on {-M,0,M}, enumerate every assignment path and solve the exact uniformly honest variable-length-interval LP. Stop or pivot if its minimax length is not within a uniform constant of the proposed convex frontier, or if it borrows where the claimed concurrent-only modulus equality holds.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 math PASS, but paper_score_ceiling 5.8 is below the 7.2 field threshold; the proposed fixed-floor converse is false in scope.

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
