---
qid: exp_private_sate_design_game
spec: v1
topic: "Exact finite-sample locally private SATE design game. For N>=4 labeled units with arbitrary binary potential-outcome schedules, complete randomization of exactly m treated units, and a common noninteractive epsilon-local-DP channel protecting (W,Yobs), jointly minimize worst-schedule expected cardinality among randomized exact 1-alpha confidence sets for the finite-population SATE. Prove schedule-orbit reduction and sufficiency of the fourteen nonconstant four-input staircase patterns; formulate fixed-channel confidence inference as an exact primal-dual LP and common-channel optimization as an attained degree-N polynomial game; develop algebraic or positive-tolerance global certificates; and characterize the parameter cells and actual boundaries where a balanced design with randomized response after a nontrivial binary partition is globally optimal. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivations give the orbit generating-function kernel, fourteen-output Blackwell refinement, fixed-channel LP, and polynomial-dual global lower bounds. Independent exact reruns certify a nonbinary exclusion interval [999.9,1000.1], disprove the convex-utility shortcut, and bracket the unrestricted N=4, alpha=2/5, lambda=1000 value in [2.58227914,2.58228508], with every optimizer balanced for lambda>=1000; no exact literature collision was found, while consumer translation requires a hidden-assignment protocol. UNRESOLVED BOTTLENECK: Make the simultaneous lower certificate attain equality at a specified optimizing channel and continue it across a nontrivial parameter cell to identify an actual boundary of the balanced-binary equality set. EARLY KILL TEST: Reproduce the full fourteen-weight N=4 global bracket within 1e-5 and 100000 channel cells; this passed in one cell using 2,825,761 exact vertex-tensor bounds, so the next kill test is failure of optimizer-attaining certificate extraction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_private_sate_design_game.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "No attaining Gamma_J, nonempty balanced-binary equality cell, algebraically isolated frontier, adjacent sign certificate, or active-set transition was supplied after the dedicated construct-and-determine round."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised equality-cell and actual phase-boundary result is replaced by a conditional certificate schema and a nonbinary exclusion interval; no attaining Gamma_J, nonempty equality cell, or frontier is supplied."
  - "The unrestricted optimum at lambda=1000 is only bracketed within 5.94e-6, so no minimizing channel is identified, while the certificate-characterization theorem is conditional on precisely the optimizer-attaining global certificate that is not supplied."
  - "The named rational tables and four checkers are absent from both core.json dependencies and the run directory, so the headline numerical results are not reproducible."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_oeq_actual_balanced_binary_boundary.json
  - discovery/solve_tex/solve_oeq_actual_balanced_binary_boundary.tex
  - discovery/solve_thm_certificate_characterization.json
  - discovery/solve_thm_certified_nonbinary_regime.json
  - reviews/review_general.json
  - reviews/review_math.json
  - reviews/review_rubric.json
seeds_burned: []
proof_attempt_summary: |
  The run proved the finite orbit/Blackwell reduction, fixed-channel LP formulation,
  polynomial attainment, an N=4 balance ray, and a narrow nonbinary exclusion interval.
  A dedicated construct-and-determine round could not turn the conditional certificate
  schema into an optimizer-attaining balanced-binary cell or actual boundary: the exact
  global lower certificate remained 297/50000000 below the feasible upper value. The
  sound remainder is incremental, while reproducibility and one LP citation claim also
  remain incomplete as recorded above.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 18409245
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 18409245
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_private_sate_design_game / v1 — Downgraded

**Topic.** Exact finite-sample locally private SATE design game. For N>=4 labeled units with arbitrary binary potential-outcome schedules, complete randomization of exactly m treated units, and a common noninteractive epsilon-local-DP channel protecting (W,Yobs), jointly minimize worst-schedule expected cardinality among randomized exact 1-alpha confidence sets for the finite-population SATE. Prove schedule-orbit reduction and sufficiency of the fourteen nonconstant four-input staircase patterns; formulate fixed-channel confidence inference as an exact primal-dual LP and common-channel optimization as an attained degree-N polynomial game; develop algebraic or positive-tolerance global certificates; and characterize the parameter cells and actual boundaries where a balanced design with randomized response after a nontrivial binary partition is globally optimal. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact derivations give the orbit generating-function kernel, fourteen-output Blackwell refinement, fixed-channel LP, and polynomial-dual global lower bounds. Independent exact reruns certify a nonbinary exclusion interval [999.9,1000.1], disprove the convex-utility shortcut, and bracket the unrestricted N=4, alpha=2/5, lambda=1000 value in [2.58227914,2.58228508], with every optimizer balanced for lambda>=1000; no exact literature collision was found, while consumer translation requires a hidden-assignment protocol. UNRESOLVED BOTTLENECK: Make the simultaneous lower certificate attain equality at a specified optimizing channel and continue it across a nontrivial parameter cell to identify an actual boundary of the balanced-binary equality set. EARLY KILL TEST: Reproduce the full fourteen-weight N=4 global bracket within 1e-5 and 100000 channel cells; this passed in one cell using 2,825,761 exact vertex-tensor bounds, so the next kill test is failure of optimizer-attaining certificate extraction. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_private_sate_design_game.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The promised optimizer-attaining equality cell and actual phase boundary were not established; the exact unrestricted lower certificate remained 297/50000000 below the feasible upper value, leaving only an incremental reduction, balance ray, and nonbinary exclusion result.

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
