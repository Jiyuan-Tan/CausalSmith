---
qid: eid_robust_backshift_uniform_distance
spec: v1
topic: "Minimax Environment-Distance Theorem for corruption-robust BACKSHIFT. Observe m covariance slots, with an honest design H of size h=m-c satisfying Sigma_e=D^{-1}(Omega+diag(s_e))D^{-T}; D has the standard BACKSHIFT normalization and stability rule, Omega is invariant PSD and may be nondiagonal, and s_e>=0. The other c slots are arbitrary PSD. Define delta_H=min_{k<l}[h-max_L #{e in H:(s_ek,s_el) lies on affine line L}]. Prove that delta_H>c guarantees uniqueness for every c-slot contamination, and prove the matching minimax converse by a positive-definite ambiguity witness on the invariant-noise interior. Derive the exact generic maximum-collinearity formula and the exact sparse-support deletion threshold. Define the set-theoretic subset-consensus recovery map and confidence union over arbitrary nonempty positive-definite covariance regions, and prove the QE-free simultaneous-coverage implication. Under explicit declarative affine-separation, normalization-slack, covariance-interiority, conditioning, and scale bounds on every feasible candidate, prove only a non-effective compactness-based existence of a positive local radius and linear contraction if this analytic statement remains sound. Treat executable real quantifier elimination, exact generated semialgebraic union codes, terminating release/abstain decisions, rational empty/singleton/multiple classification, an effectively computed radius, normalization-chart automation, and a corruption-aware CRAN implementation as one unresolved open-ended future program; no such executable or effective interface is claimed here."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - Causalean/Mathlib/MeasureTheory/PolynomialZeroLocus.lean
  - Causalean/Discovery/LinearDisentanglement/CollinearAmbiguity/Main.lean
  - Causalean/Discovery/LinearDisentanglement/Quantitative/PairwiseAffine/Stability.lean
  - Causalean/Discovery/LinearDisentanglement/Quantitative/CompactExclusion.lean
seeds_burned: []
proof_attempt_summary: |
  The run proved the sharp replacement-radius equivalence, both ambiguity directions,
  the generic and sparse-support frontiers, confidence-union coverage, and the stated
  non-effective four-margin contraction with no added assumptions or proof placeholders.
  Three reusable matrix substrates were coordinated into Causalean during F3, and F7
  additionally promoted the finite-dimensional polynomial zero-locus nullity lemmas;
  executable quantifier elimination and software release logic remain explicitly outside
  the delivered theorem claims.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 279641447
  pipeline_claude_tokens: 33045394
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# eid_robust_backshift_uniform_distance / v1 — Accepted

**Topic.** Minimax Environment-Distance Theorem for corruption-robust BACKSHIFT. Observe m covariance slots, with an honest design H of size h=m-c satisfying Sigma_e=D^{-1}(Omega+diag(s_e))D^{-T}; D has the standard BACKSHIFT normalization and stability rule, Omega is invariant PSD and may be nondiagonal, and s_e>=0. The other c slots are arbitrary PSD. Define delta_H=min_{k<l}[h-max_L #{e in H:(s_ek,s_el) lies on affine line L}]. Prove that delta_H>c guarantees uniqueness for every c-slot contamination, and prove the matching minimax converse by a positive-definite ambiguity witness on the invariant-noise interior. Derive the exact generic maximum-collinearity formula and the exact sparse-support deletion threshold. Define the set-theoretic subset-consensus recovery map and confidence union over arbitrary nonempty positive-definite covariance regions, and prove the QE-free simultaneous-coverage implication. Under explicit declarative affine-separation, normalization-slack, covariance-interiority, conditioning, and scale bounds on every feasible candidate, prove only a non-effective compactness-based existence of a positive local radius and linear contraction if this analytic statement remains sound. Treat executable real quantifier elimination, exact generated semialgebraic union codes, terminating release/abstain decisions, rational empty/singleton/multiple classification, an effectively computed radius, normalization-chart automation, and a corruption-aware CRAN implementation as one unresolved open-ended future program; no such executable or effective interface is claimed here.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** CKPT 2 approved: sharp replacement-radius characterization and field-tier delivery independently verified with a full build, source re-elaboration, zero forbidden placeholders, and no custom axioms.

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
