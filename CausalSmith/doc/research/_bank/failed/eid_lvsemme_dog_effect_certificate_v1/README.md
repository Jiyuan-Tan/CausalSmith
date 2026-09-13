---
qid: eid_lvsemme_dog_effect_certificate
spec: v1
topic: "Necessary-and-sufficient DOG-invariant total-effect certification under simultaneous latent confounding and measurement error. In Yang et al.'s canonical separable, minimal, rank-faithful linear LV-SEM-ME with known observation labels, characterize the complete pairwise total-effect image over every minimum-edge DOG model; prove the normalized-column projection, singleton minor iff, attaining countermodels, polynomial global minimum-completion algorithm, and confidence-region inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact reductions, witnesses, destructive checks, and all remaining gaps are recorded in <repo-root>/internal/presolve_drafts/eid_lvsemme_dog_effect_certificate.md. UNRESOLVED BOTTLENECK: polynomial constrained minimum completion under coupled downstream cancellations. EARLY KILL TEST: recover and certify the recorded faithful 12-edge plateau optimum."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The promised unrestricted polynomial global minimum-completion algorithm is not delivered: the paper substitutes promise-NP/FP^NP bounds plus a fixed-width restriction."
  - "The unrestricted deterministic complexity remains open."
  - "The complete effect image is conditional on membership in the unknown global argmin, so it does not provide the advertised executable certificate."
reusable_artifacts:
  - discovery/solve_lem_plateau_certificate.json
  - discovery/solve_thm_comp_edge_promise_np.json
  - discovery/solve_thm_complete_effect_image.json
  - discovery/core.json
  - discovery/writeup.tex
seeds_burned: []
proof_attempt_summary: |
  The run derived normalized-column joint effect images, a q+1 sharpness construction,
  promise-NP/FP^NP bounds, and fixed-block-width tractability, and it certified a
  13-edge local-descent trap with a 12-edge coupled optimum. It did not produce the
  mandatory unrestricted polynomial rational-bit optimizer for global and prescribed-pair
  completion; neither the plateau nor the restricted algorithm supplies such a result.
  A faithful successor would need a complete polynomial algorithm or an exact
  promise-preserving hardness reduction before reusing the conditional image theory.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 31788995
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 31788995
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_lvsemme_dog_effect_certificate / v1 — Failed

**Topic.** Necessary-and-sufficient DOG-invariant total-effect certification under simultaneous latent confounding and measurement error. In Yang et al.'s canonical separable, minimal, rank-faithful linear LV-SEM-ME with known observation labels, characterize the complete pairwise total-effect image over every minimum-edge DOG model; prove the normalized-column projection, singleton minor iff, attaining countermodels, polynomial global minimum-completion algorithm, and confidence-region inference. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact reductions, witnesses, destructive checks, and all remaining gaps are recorded in <repo-root>/internal/presolve_drafts/eid_lvsemme_dog_effect_certificate.md. UNRESOLVED BOTTLENECK: polynomial constrained minimum completion under coupled downstream cancellations. EARLY KILL TEST: recover and certify the recorded faithful 12-edge plateau optimum.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** terminal:laundering — the promised unrestricted polynomial global and prescribed-pair minimum-completion algorithm is not delivered; the manuscript substitutes promise-NP/FP^NP bounds and fixed-width enumeration.

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
