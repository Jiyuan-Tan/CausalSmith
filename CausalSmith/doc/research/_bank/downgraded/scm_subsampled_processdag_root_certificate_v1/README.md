---
qid: scm_subsampled_processdag_root_certificate
spec: v1
topic: "Graph-recursive formula-or-ambiguity certificates for fine-grid causal transfers from subsampled Gaussian process DAGs. Let X_t=A X_{t-1}+ε_t be a stable stationary Gaussian VAR(1) with positive diagonal innovation covariance and a supplied labeled lower-triangular cross-variable DAG; observe only Y_s=X_{ms}. From the identified coarse transition B=A^m and coarse innovation covariance, give a terminating sound-and-complete certificate for a queried transfer h_uv(z)=A_vu z/(1−A_vv z). Prove graph-recursive generic point identification for odd m through divided differences, the unavoidable same-law symmetry (A,D)↦(−A,D) and transfer ambiguity for even m, and a real-closed-field/CAD fallback that projects every singular compatible fiber jointly onto (A_vu,A_vv), returning either one rational transfer or two attained stable witnesses. Add Wald bands on an explicit regular class and globally honest inversion of a coarse lag-moment confidence region without branch selection. Credit classical Smith/Higham triangular-root recursion and the subsampling work of Gong et al., Tank–Fox–Shojaie, Hyttinen et al., and Gersing–Sögner–Deistler; frame Gong et al.'s Temperature–Ozone example only as a conditional m=2 Gaussian ambiguity audit under an externally defensible ordering. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the graph path expansion (A^m)_vu=A_vu C_m(A_vv,A_uu)+R, proved C_m positive off (0,0) for odd m and zero exactly at opposite persistences for even m, and verified the three-node rational witness including its indirect-path remainder. It derived the open singular fiber |a|<sqrt(q2/q1), the global even-factor sign obstruction, and the exact polynomial test for equality of full transfers. Zero diagonals, absent edges, open fibers, covariance filtering, zero-edge transfers, input encoding, branch mergers, and current collisions were checked. UNRESOLVED BOTTLENECK: Prove and calibrate an explicit uniform Gaussian quadratic-form confidence region for overlapping stationary lag moments on the compact stable class, with finite-sample constants and rational outward rounding, so semialgebraic inversion has advertised global coverage. EARLY KILL TEST: Exact CAD on d=2,m=3 with B=0 and diagonal Q must return two interior transfer-distinct witnesses, and every nonzero-edge d=2,m=2 case must retain the global sign pair; any singleton, endpoint-only witness, or lost sign pair stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_subsampled_processdag_root_certificate.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The field-tier promise was not met: the archived discovery note still has a false even-m nonemptiness iff, misstates Q as real closed, and carries equality-only adaptive ballast; bounded cleanup would not overcome the structural subfield ceiling."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "missing-odd-factor-hypothesis@lem:derivative-separated-class-nonempty"
  - "ballast@def:adaptive-calibration-handle, ballast@thm:adaptive-calibration-fallback, ballast@thm:adaptive-calibration-literal-answer"
  - "paper_score_ceiling 6.7 < 7.4"
  - "salvageable=false; no improvement_directive or ceiling_directive"
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_prop_singular_open_fiber.tex
  - discovery/solve_thm_even_sign_ambiguity.tex
  - discovery/solve_thm_target_corridor_identification.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery derived triangular root recursion, open singular-fiber witnesses,
  even-factor sign ambiguity, graph-local identification, and full-circle Wald
  inference. D0.5 found the archived note unclean: its derivative-separated-class
  nonemptiness iff omits oddness, it incorrectly names Q as real closed, and its
  equality-only adaptive branch is ballast. Bounded cleanup would not lift the
  structural subfield ceiling created by supplied order, known sampling factor,
  fixed dimension, recursion-defined separation, and no implementation/application.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26186002
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26186002
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# scm_subsampled_processdag_root_certificate / v1 — Downgraded

**Topic.** Graph-recursive formula-or-ambiguity certificates for fine-grid causal transfers from subsampled Gaussian process DAGs. Let X_t=A X_{t-1}+ε_t be a stable stationary Gaussian VAR(1) with positive diagonal innovation covariance and a supplied labeled lower-triangular cross-variable DAG; observe only Y_s=X_{ms}. From the identified coarse transition B=A^m and coarse innovation covariance, give a terminating sound-and-complete certificate for a queried transfer h_uv(z)=A_vu z/(1−A_vv z). Prove graph-recursive generic point identification for odd m through divided differences, the unavoidable same-law symmetry (A,D)↦(−A,D) and transfer ambiguity for even m, and a real-closed-field/CAD fallback that projects every singular compatible fiber jointly onto (A_vu,A_vv), returning either one rational transfer or two attained stable witnesses. Add Wald bands on an explicit regular class and globally honest inversion of a coarse lag-moment confidence region without branch selection. Credit classical Smith/Higham triangular-root recursion and the subsampling work of Gong et al., Tank–Fox–Shojaie, Hyttinen et al., and Gersing–Sögner–Deistler; frame Gong et al.'s Temperature–Ozone example only as a conditional m=2 Gaussian ambiguity audit under an externally defensible ordering. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The score-blind presolve derived the graph path expansion (A^m)_vu=A_vu C_m(A_vv,A_uu)+R, proved C_m positive off (0,0) for odd m and zero exactly at opposite persistences for even m, and verified the three-node rational witness including its indirect-path remainder. It derived the open singular fiber |a|<sqrt(q2/q1), the global even-factor sign obstruction, and the exact polynomial test for equality of full transfers. Zero diagonals, absent edges, open fibers, covariance filtering, zero-edge transfers, input encoding, branch mergers, and current collisions were checked. UNRESOLVED BOTTLENECK: Prove and calibrate an explicit uniform Gaussian quadratic-form confidence region for overlapping stationary lag moments on the compact stable class, with finite-sample constants and rational outward rounding, so semialgebraic inversion has advertised global coverage. EARLY KILL TEST: Exact CAD on d=2,m=3 with B=0 and diagonal Q must return two interior transfer-distinct witnesses, and every nonzero-edge d=2,m=2 case must retain the global sign pair; any singleton, endpoint-only witness, or lost sign pair stops the launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_subsampled_processdag_root_certificate.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 cold tier verdict: subfield; paper_score_ceiling 6.7 < 7.4 field floor; salvageable=false, with no bounded improvement directive.

## Key files

- `state.json` — pipeline state at banking (`banked: true`).
- `discovery/proposal.tex` — final proposal version.
- `discovery/writeup.tex` — derivation note (if Stage 0 ran).
- `reviews/reviews.jsonl` — per-round reviewer log (Stage -0.5 and Stage 0.5).
- `reviews/` — per-version reviewer JSON files (if present).

## Notes

The CAD citation was lawfully verified against arXiv:1401.0647v2, p. 2, §1.1;
the published DOI is 10.1007/s11786-014-0191-z. This entry is retained as
below-floor research evidence and must not be described as a clean sound final
note unless the unresolved defects listed above are repaired.
