---
qid: exp_pairdiscordance_minimax_design
spec: v1
topic: "Sharp minimax design under bounded pair mismatch. For N=2J labeled units in known pairs with binary fixed potential outcomes and at most s armwise-discordant pairs, optimize jointly over every assignment law and every measurable SATE estimator. Characterize the complete invariant optimal-design face by a polynomial-size orbit game and matching least-favourable-prior dual; give iff certificates for paired, iid-Bernoulli, canonical-mixture, essentially noncanonical, and unique optima. Prove J R*(J,s_J) converges to min(rho,1/2) when s_J/J tends to rho, all-mixed concentration below rho=1/2, and the first-order envelope of o(J^-1)-optimal invariant procedures, while exact finite-minimizer selection is posed as the open J^(2/3)-critical, J^(-4/3)-residual Gamma-limit problem. Supply exact finite randomization-test inversion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rational enumeration at J=2,s=1 finds a noncanonical procedure with worst risk below 0.09065 while a dual prior forces every paired/Bernoulli mixture above 0.09102. A shrinking five-type prior, van Trees bound, empirical-SATE transfer, and hard-budget conditioning derive the sharp first-order value min(rho,1/2), with endpoint and degeneracy checks surviving. UNRESOLVED BOTTLENECK: characterize which first-order optimal limiting measures are limits of exact finite minimizers for rho>=1/2, including critical-sequence and smaller-order selection. EARLY KILL TEST: rerun the rational certificate, enumerate J=2,3,4 for every s, and optimize the full finite optimal faces; pivot if exact optimizer selection cannot be distinguished from first-order optimality. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_pairdiscordance_minimax_design.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The exact finite result characterizes optimal designs through a very large orbit-game feasibility system rather than an analytic description of the optimizers, limiting its direct practical use."
  - "The strict noncanonical advantage is proved only for J=2, s=1 and only against the paper-defined paired–Bernoulli segment, so it does not establish a general superiority pattern."
  - "The advertised J^{-4/3} residual functional, Gamma limit, and exact-selection contact set remain open, as the framing acknowledges, and therefore contribute no established second-order frontier."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_noncanonical_separation.json
  - discovery/solve_thm_first_order_face.json
  - discovery/solve_oeq_exact_selection.json
seeds_burned: []
proof_attempt_summary: |
  The derivation established the finite orbit-game primal/dual correspondence, an exact
  J=2,s=1 noncanonical rational certificate, the sharp first-order risk and limiting
  optimal face, and exact randomization-test inversion. It did not obtain an analytic
  optimizer description, a cross-J noncanonical-superiority theorem, or the proposed
  J^{-4/3} Gamma limit and exact-minimizer contact set; those require new research and
  leave the package at subfield rather than field novelty.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 35463007
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 35463007
  total_tokens_consumed: null
banked_on: "2026-09-12"
---

# exp_pairdiscordance_minimax_design / v1 — Downgraded

**Topic.** Sharp minimax design under bounded pair mismatch. For N=2J labeled units in known pairs with binary fixed potential outcomes and at most s armwise-discordant pairs, optimize jointly over every assignment law and every measurable SATE estimator. Characterize the complete invariant optimal-design face by a polynomial-size orbit game and matching least-favourable-prior dual; give iff certificates for paired, iid-Bernoulli, canonical-mixture, essentially noncanonical, and unique optima. Prove J R*(J,s_J) converges to min(rho,1/2) when s_J/J tends to rho, all-mixed concentration below rho=1/2, and the first-order envelope of o(J^-1)-optimal invariant procedures, while exact finite-minimizer selection is posed as the open J^(2/3)-critical, J^(-4/3)-residual Gamma-limit problem. Supply exact finite randomization-test inversion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Exact rational enumeration at J=2,s=1 finds a noncanonical procedure with worst risk below 0.09065 while a dual prior forces every paired/Bernoulli mixture above 0.09102. A shrinking five-type prior, van Trees bound, empirical-SATE transfer, and hard-budget conditioning derive the sharp first-order value min(rho,1/2), with endpoint and degeneracy checks surviving. UNRESOLVED BOTTLENECK: characterize which first-order optimal limiting measures are limits of exact finite minimizers for rho>=1/2, including critical-sequence and smaller-order selection. EARLY KILL TEST: rerun the rational certificate, enumerate J=2,3,4 for every s, and optimize the full finite optimal faces; pivot if exact optimizer selection cannot be distinguished from first-order optimality. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_pairdiscordance_minimax_design.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the sound delivered package subfield below the fixed field floor (paper_score_ceiling 7.2 < 7.4), with no bounded in-scope repair; field requires new research on analytic optimizer structure, cross-J superiority, or the J^-4/3 exact-minimizer Gamma limit.

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
