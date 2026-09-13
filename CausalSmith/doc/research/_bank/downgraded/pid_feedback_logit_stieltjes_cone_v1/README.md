---
qid: pid_feedback_logit_stieltjes_cone
spec: v1
topic: "Exact joint-response Stieltjes cone for continuous-heterogeneity feedback logit. Let c=exp(theta)>0 and u=exp(alpha) in (0,infinity); fix the full positive sixteen-cell T=2 binary-logit law while initial assignment and feedback may depend arbitrarily on alpha. Prove that the sharp joint slope/APE set is exactly represented by eight joint (X1,r0,r1) response-type measures and a finite open-half-line quartic Stieltjes lift: 56 auxiliary variables with eight 3x3 and eight augmented 4x4 PSD blocks for weak probabilities, and 64 variables with eight additional 6x6 common-Hankel-range blocks for strict positivity. Prove forward/reverse legal-kernel reconstruction, sharp fixed-c infimum/supremum endpoints with separate attainment tests, terminating algebraic membership/projection for algebraic inputs, exact multinomial whole-set coverage, and fixed-c endpoint consistency only on relative-interior attainable laws. Closest work: Bonhomme-Dano-Graham 2023 gives the sharp infinite-dimensional feedback program and grid computation; DGKR 2026 lacks the separate unrestricted feedback kernel. Consumer: replace support-grid robustness bounds in the Arellano-Carrasco PSID predetermined-children labor-participation design. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Eight measures with densities h_x g_x0(r0) g_x1(r1) preserve one unconditional law and admit Radon-Nikodym reconstruction; the common quartic denominator leaves five bounded moments per type. Independent rank-by-rank checks support the augmented positive-half-line Stieltjes certificate and equal-Hankel-range common-support criterion. Exact arithmetic verifies a positive c=2 witness with Delta=3/20 and every stated PSD block, and destructive checks cover zero/one/two/full-rank, escape-to-infinity, c=1 rank loss, nonattainment, and weak-infeasibility regimes. UNRESOLVED BOTTLENECK: No unresolved theorem step remains within the stated scope; continuity at strictly positive relative-boundary laws and joint consistency through c=1 are explicitly excluded extensions. EARLY KILL TEST: Reconstruct legal positive-node measures on zero-only, zero-plus-positive, one-node, two-node, and full-rank moment inputs, checking both augmented range conditions and common support whenever all eight Hankel ranges agree; any feasible lifted vector without a legal feedback reconstruction kills the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_feedback_logit_stieltjes_cone.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The identification theorem has field-level substance, but the delivered package is capped at subfield because inference is limited to conservative whole-set inversion and fixed-c relative-interior consistency, boundary/rank-change inference remains open, and no solver, atom extraction, numerical stability study, support-grid comparison, or empirical PSID implementation is delivered."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_exact_feedback_cone.json
  - discovery/solve_thm_fixed_slope_endpoints.json
  - discovery/solve_prop_whole_set_coverage.json
  - discovery/solve_prop_c_one_sanity.json
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the all-laws weak/strict finite Stieltjes-cone representation,
  reverse legal-kernel reconstruction, sharp slope--APE envelope, algebraic
  membership claims, and conservative whole-set inference; both D0.5 math and
  decision panels passed after six cited sources were independently attested.
  The result missed the field floor because its implemented delivery stops short
  of boundary/rank-change inference, a certified solver and atom extractor,
  numerical support-grid comparisons, and an empirical PSID application.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24404590
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 24404590
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# pid_feedback_logit_stieltjes_cone / v1 — Downgraded

**Topic.** Exact joint-response Stieltjes cone for continuous-heterogeneity feedback logit. Let c=exp(theta)>0 and u=exp(alpha) in (0,infinity); fix the full positive sixteen-cell T=2 binary-logit law while initial assignment and feedback may depend arbitrarily on alpha. Prove that the sharp joint slope/APE set is exactly represented by eight joint (X1,r0,r1) response-type measures and a finite open-half-line quartic Stieltjes lift: 56 auxiliary variables with eight 3x3 and eight augmented 4x4 PSD blocks for weak probabilities, and 64 variables with eight additional 6x6 common-Hankel-range blocks for strict positivity. Prove forward/reverse legal-kernel reconstruction, sharp fixed-c infimum/supremum endpoints with separate attainment tests, terminating algebraic membership/projection for algebraic inputs, exact multinomial whole-set coverage, and fixed-c endpoint consistency only on relative-interior attainable laws. Closest work: Bonhomme-Dano-Graham 2023 gives the sharp infinite-dimensional feedback program and grid computation; DGKR 2026 lacks the separate unrestricted feedback kernel. Consumer: replace support-grid robustness bounds in the Arellano-Carrasco PSID predetermined-children labor-participation design. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Eight measures with densities h_x g_x0(r0) g_x1(r1) preserve one unconditional law and admit Radon-Nikodym reconstruction; the common quartic denominator leaves five bounded moments per type. Independent rank-by-rank checks support the augmented positive-half-line Stieltjes certificate and equal-Hankel-range common-support criterion. Exact arithmetic verifies a positive c=2 witness with Delta=3/20 and every stated PSD block, and destructive checks cover zero/one/two/full-rank, escape-to-infinity, c=1 rank loss, nonattainment, and weak-infeasibility regimes. UNRESOLVED BOTTLENECK: No unresolved theorem step remains within the stated scope; continuity at strictly positive relative-boundary laws and joint consistency through c=1 are explicitly excluded extensions. EARLY KILL TEST: Reconstruct legal positive-node measures on zero-only, zero-plus-positive, one-node, two-node, and full-rank moment inputs, checking both augmented range conditions and common support whenever all eight Hankel ranges agree; any feasible lifted vector without a legal feedback reconstruction kills the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_feedback_logit_stieltjes_cone.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** The identification theorem has field-level substance, but the delivered package is capped at subfield because inference is limited and no solver, numerical comparison, or empirical implementation is delivered.

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
