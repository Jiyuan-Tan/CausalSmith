---
qid: panel_pebble_singular_frontier
spec: v1
topic: "Pebble-certified rank-two counterfactual recovery and singular-margin upper guarantees. Fix finite T,C, rank two, deterministic untreated masks S_c with |S_c|>=3 and positive cohort shares; impose bounded positive loading covariances, local signal eigengaps, factor/loadings, conditional homoskedastic outcome-uncorrelated errors, and a common 4+delta moment radius. Replace each mask by |S_c|-2 anchor triples. Prove that the published rank-two count certificate is sufficient for all missing cohort-time untreated means to be complete-observed-law functionals, while certificate failure implies generic factor-plane ambiguity only and does not imply causal-target nonidentification under the frozen primitives. Give the O(Tm) background pebble certificate and the strict O3 containment witness for masks 123,145,256,346. For relation singular margin s in [s_N,2s_N], prove the radius-adaptive covariance-PCA squared-risk upper bound min{1,4 b_lambda^2,K/(N s_N^2)} and uniformly honest profile-inversion rectangle upper half-width min{b_lambda,C_alpha min(1,1/(sqrt(N)s_N))}; N s_N^2 divergence is sufficient but not necessary for consistency. Record the legal tight-radius zero-target family and nonempty-shell counterexample as obstructions to universal identification converses, positive minimax/width lower frontiers, and a necessary consistency threshold. A frontier-scale testing pair on a separately justified quantitatively nondegenerate subclass remains open and is not assumed."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposal promised a causal-identification iff and sharp positive minimax/honest-width lower frontiers. Discovery proved only certificate-pass sufficiency, failure-side factor-plane ambiguity, and radius-adaptive upper guarantees; a legal tight-radius family makes the causal target identically zero and defeats the converses."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "It does not deliver the advertised identification iff: certificate failure is explicitly shown not to imply causal-target nonidentification under the stated class."
  - "Likewise, the results named a singular or minimax frontier have no positive risk converse, honest-width converse, or necessary consistency threshold; the proved rate statements are achievable upper guarantees only."
  - "Because the combinatorial certificate is published background and the new causal transport is a direct covariance-eigenspace reconstruction under spherical errors, the remaining contribution is useful but too narrow and incomplete for the field floor."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_pebble_full_law.tex
  - discovery/solve_thm_four_mask_early_kill_negative.tex
  - discovery/solve_lem_tight_moment_radius_forces_zero_means.tex
  - discovery/solve_thm_honest_rectangle.tex
  - discovery/solve_thm_minimax_frontier.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery verified the published generic rank-two projection certificate, derived the
  observed-law reconstruction and strict O3-containment witness, and established
  radius-adaptive PCA risk and honest-rectangle upper guarantees. The intended converse
  and matching lower frontiers collapsed because an allowed tight-radius family has an
  identically zero causal target even when the certificate fails and singular shells are
  nonempty. A future specification would need independently motivated quantitative
  nondegeneracy, rather than adding it here to assume the missing deformation.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 34254570
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 34254570
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# panel_pebble_singular_frontier / v1 — Downgraded

**Topic.** Pebble-certified rank-two counterfactual recovery and singular-margin upper guarantees. Fix finite T,C, rank two, deterministic untreated masks S_c with |S_c|>=3 and positive cohort shares; impose bounded positive loading covariances, local signal eigengaps, factor/loadings, conditional homoskedastic outcome-uncorrelated errors, and a common 4+delta moment radius. Replace each mask by |S_c|-2 anchor triples. Prove that the published rank-two count certificate is sufficient for all missing cohort-time untreated means to be complete-observed-law functionals, while certificate failure implies generic factor-plane ambiguity only and does not imply causal-target nonidentification under the frozen primitives. Give the O(Tm) background pebble certificate and the strict O3 containment witness for masks 123,145,256,346. For relation singular margin s in [s_N,2s_N], prove the radius-adaptive covariance-PCA squared-risk upper bound min{1,4 b_lambda^2,K/(N s_N^2)} and uniformly honest profile-inversion rectangle upper half-width min{b_lambda,C_alpha min(1,1/(sqrt(N)s_N))}; N s_N^2 divergence is sufficient but not necessary for consistency. Record the legal tight-radius zero-target family and nonempty-shell counterexample as obstructions to universal identification converses, positive minimax/width lower frontiers, and a necessary consistency threshold. A frontier-scale testing pair on a separately justified quantitatively nondegenerate subclass remains open and is not assumed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** review_general.json: meets_floor=false, tier=incremental, paper_score_ceiling=5.4 < ceiling_for_field=7.4, salvageable=false; the legal tight-radius family has mu identically zero, so the advertised iff and universal positive lower frontiers are false under the frozen assumptions.

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
