---
qid: stat_selfnormal_mixedkernel_complete
spec: v1
topic: "Classify every nonzero nonconstant homogeneous polynomial denominator D on Sym₃ satisfying 2 tr((G_D(Σ)Σ)^2)=cD(Σ)^2 for c>0. Prove, without degree or nonresonance restrictions, that D is a scalar product of nonnegative integer powers of determinants along one nested rational flag, by establishing global kernel-line constancy for the mixed rank-two branch through adjugate-translation rigidity and cone monotonicity. Give an exact rational-coefficient recognition, exponent, and flag-recovery certificate. Credit Tamano's flag sufficiency, Sym₂ converse, spectral reduction, and determinant stripping. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Differentiating det G=0 in its adjugate direction and using Hessian symmetry gives dG[adj G]=0. The resulting polynomial derivation annihilates G, adj G, and the mixed residue E, so finite Taylor expansion makes E constant on each adjugate ray. Positive-semidefinite gradients, homogeneity, and Loewner ordering then bound every parallel polynomial ray above and below, forcing one fixed global kernel and closing Tamano's remaining mixed branch. Exact symbolic checks passed for flag powers, determinant stripping, a nonnested failure, rational flag recovery, and the resonant deformation Eε=x³(xy-u²)³+ε det(X)x⁶, whose residual is exactly 12ε²x¹²det(X)². UNRESOLVED BOTTLENECK: The informal universal proof still needs independent verification of the finite adjugate-translation step, its symmetric-coordinate conventions, the two-sided cone-order bound, and every imported reduction from Tamano. Software integration and finite-sample inference are not established. EARLY KILL TEST: Recompute dG[adj G] with half-weighted off-diagonal gradients, then seek a homogeneous polynomial with positive-semidefinite rank-two gradient and moving kernel; either a missing derivative term or such a counterexample kills the spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_selfnormal_mixedkernel_complete.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "Statistical payoff remains denominator-only with no causal-ratio inference or implemented recognizer; generic rank <= d-2 remains open."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "Its statistical payoff is confined to an exact pivot and confidence set for a primitive denominator supported on at most three supplied directions; it establishes no inference result for the causal ratio itself."
  - "The package supplies no implemented recognizer, complexity analysis, or new worked causal certificate demonstrating that the unrestricted cases occur and matter beyond the cited front-door example."
  - "The dimension-free theorem handles only the positive-gradient corank-one branch, leaving generic rank at most d-2 entirely open, so it does not provide a general higher-dimensional classification framework."
reusable_artifacts:
  - "discovery/solve_tex/solve_thm_positive_gradient_kernel_rigidity.tex — adjugate-translation and cone-monotonicity proof, including the corank-one dimension-general extension."
  - "discovery/solve_tex/solve_thm_rational_recognition.tex — exact rational recognition and flag-recovery certificate derivation."
  - "discovery/core.json — maximized dependency graph with the ambient rank-at-most-three compression audit and explicit higher-dimensional residual question."
seeds_burned:
  - index: 0
    one_liner: "sym3-global-kernel-rigidity"
    reason: "The sole maximized angle passed mathematical/decision review but remained incremental after the corank-one extension; no field-tier salvage directive remained."
proof_attempt_summary: |
  The run closed Tamano's unrestricted Sym3 mixed rank-two branch by proving a fixed-kernel rigidity theorem from adjugate translation and cone monotonicity, and strengthened the argument to the positive-gradient corank-one branch in every dimension. It also derived an exact rational recognition certificate and extended the denominator audit through rank-at-most-three ambient compression. The mathematics survived review, but the field claim collapsed on scope: the payoff is denominator-only, lacks an implemented recognizer or a new unrestricted causal example, and leaves the generic rank-at-most-d-minus-two higher-dimensional branch open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 38952463
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 38952463
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# stat_selfnormal_mixedkernel_complete / v1 — Downgraded

**Topic.** Classify every nonzero nonconstant homogeneous polynomial denominator D on Sym₃ satisfying 2 tr((G_D(Σ)Σ)^2)=cD(Σ)^2 for c>0. Prove, without degree or nonresonance restrictions, that D is a scalar product of nonnegative integer powers of determinants along one nested rational flag, by establishing global kernel-line constancy for the mixed rank-two branch through adjugate-translation rigidity and cone monotonicity. Give an exact rational-coefficient recognition, exponent, and flag-recovery certificate. Credit Tamano's flag sufficiency, Sym₂ converse, spectral reduction, and determinant stripping. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Differentiating det G=0 in its adjugate direction and using Hessian symmetry gives dG[adj G]=0. The resulting polynomial derivation annihilates G, adj G, and the mixed residue E, so finite Taylor expansion makes E constant on each adjugate ray. Positive-semidefinite gradients, homogeneity, and Loewner ordering then bound every parallel polynomial ray above and below, forcing one fixed global kernel and closing Tamano's remaining mixed branch. Exact symbolic checks passed for flag powers, determinant stripping, a nonnested failure, rational flag recovery, and the resonant deformation Eε=x³(xy-u²)³+ε det(X)x⁶, whose residual is exactly 12ε²x¹²det(X)². UNRESOLVED BOTTLENECK: The informal universal proof still needs independent verification of the finite adjugate-translation step, its symmetric-coordinate conventions, the two-sided cone-order bound, and every imported reduction from Tamano. Software integration and finite-sample inference are not established. EARLY KILL TEST: Recompute dG[adj G] with half-weighted off-diagonal gradients, then seek a homogeneous polynomial with positive-semidefinite rank-two gradient and moving kernel; either a missing derivative term or such a counterexample kills the spine. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_selfnormal_mixedkernel_complete.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Score ceiling 6.2 is below the field threshold 7.2; meets_floor=false, salvageable=false, and improvement_directive=null.

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
