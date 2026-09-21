---
qid: exp_halfsum_orbit_frontier
spec: v2
topic: "Rectangular all-resolution common-half-sum frontier for exact two-sided-market randomization inference. For independently and uniformly half-randomized populations B and S of sizes 2n_B and 2n_S, optimize F(a,b)=sum_l a_l b_l over covering paired rectangular partitions with at least R common half-sum assignments. For every R>=4, prove that when n_B,n_S>=4R every optimizer belongs to the explicit finite residual catalog C_R with residual totals at most 2R; derive the exact affine phase formula and all equality cases, and give certified finite enumeration below the threshold. Construct the constant-incidence Z-then-P sampler and exact one-sided inversion under the sharp constant total-effect null using null-adjusted focal outcomes. Keep weak-null, two-sided-95-percent-at-R=20, power-optimality, and unrestricted-biclique claims out of scope. Consumer: Ye et al. Management Science 2023 Platform O experiment, which independently randomized unequal user-view and ad populations with balanced treatment/control within each experimental side. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A two-stage concentration proof was derived: a unit-residual benchmark forces buyer residual A<=R, and a support-preserving residual-copy competitor gives (n_B-2A+1)D<=(n_B-1)A and D<2A<=2R. Exact catalog, incidence, inversion, aspect-ratio, and threshold audits found no counterexample; small-margin universal uniqueness, raw-outcome conditioning, and ordinary two-sided 95-percent inversion at support 20 were checked and excluded. UNRESOLVED BOTTLENECK: Independently verify H(a,b')=H(a) for the residual-copy competitor and the positive-loss inequality without assuming an ordering of seller coordinates. EARLY KILL TEST: Reproduce the 136 residual-copy checks and all 2,628 feasible C_4 targets at (n_B,n_S)=(16,17); any support-loss counterexample or outside-catalog optimizer stops the field launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_halfsum_orbit_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: true-negative
gap_reasons:
  - "The proved contribution is an exact frontier only within the covering paired-rectangle class, not among unrestricted bicliques or statistically power-optimal conditioning events."
  - "Maximizing retained focal-dyad count is never connected by a theorem or practical study to power, confidence-bound width, or another inferential performance criterion."
  - "The all-resolution answer is a potentially enormous finite catalog maximum rather than a tractable closed-form characterization, and no runtime or practically relevant catalog computation is delivered beyond the R=4 case and small audits."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_affine_frontier.json
  - discovery/solve_thm_constant_incidence.json
  - discovery/solve_thm_finite_fallback.json
  - discovery/solve_prop_r4_reduction.json
  - discovery/solve_thm_strict_equal_block_delta.json
  - discovery/gaps.json
seeds_burned: []
proof_attempt_summary: |
  The run verified the residual-copy inequality, finite affine catalog, R=4 reduction,
  constant-incidence sampler, and exact one-sided inversion; both final mathematical
  panels passed with no findings. A bounded same-scope salvage added all-R dominance
  over the published equal-square subclass and the exact R=4 least-divisor gap, but a
  fresh general referee still capped the package at incremental because no power/width
  theorem, unrestricted-biclique result, or tractable general-R computation was proved.
  Universal unit-residual purification remains an explicitly unresolved crux.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 13094190
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 13094190
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_halfsum_orbit_frontier / v2 — Downgraded

**Topic.** Rectangular all-resolution common-half-sum frontier for exact two-sided-market randomization inference. For independently and uniformly half-randomized populations B and S of sizes 2n_B and 2n_S, optimize F(a,b)=sum_l a_l b_l over covering paired rectangular partitions with at least R common half-sum assignments. For every R>=4, prove that when n_B,n_S>=4R every optimizer belongs to the explicit finite residual catalog C_R with residual totals at most 2R; derive the exact affine phase formula and all equality cases, and give certified finite enumeration below the threshold. Construct the constant-incidence Z-then-P sampler and exact one-sided inversion under the sharp constant total-effect null using null-adjusted focal outcomes. Keep weak-null, two-sided-95-percent-at-R=20, power-optimality, and unrestricted-biclique claims out of scope. Consumer: Ye et al. Management Science 2023 Platform O experiment, which independently randomized unequal user-view and ad populations with balanced treatment/control within each experimental side. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A two-stage concentration proof was derived: a unit-residual benchmark forces buyer residual A<=R, and a support-preserving residual-copy competitor gives (n_B-2A+1)D<=(n_B-1)A and D<2A<=2R. Exact catalog, incidence, inversion, aspect-ratio, and threshold audits found no counterexample; small-margin universal uniqueness, raw-outcome conditioning, and ordinary two-sided 95-percent inversion at support 20 were checked and excluded. UNRESOLVED BOTTLENECK: Independently verify H(a,b')=H(a) for the residual-copy competitor and the positive-loss inequality without assuming an ordering of seller coordinates. EARLY KILL TEST: Reproduce the 136 residual-copy checks and all 2,628 feasible C_4 targets at (n_B,n_S)=(16,17); any support-loss counterexample or outside-catalog optimizer stops the field launch. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_halfsum_orbit_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G grades the mathematically sound landed graph incremental at 6.3 below the field floor 7.4, with salvageable=false after the strongest same-scope rescue and final maximality audit.

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
