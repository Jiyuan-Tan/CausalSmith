---
qid: stat_dp_cate_common_support_hypercube_frontier
spec: v1
topic: "Construct finite-sample replacement-DP honest confidence intervals for the pointwise Hölder CATE at an interior anchor under overlap, bounded common-support outcomes, and positive local design density. On the concrete uniform-design attainable subclass, build a fully private higher-order local learner with privatized nuisance pilots and localized linear and quadratic moments; prove an unrestricted-finite-rank remainder bound, a transcript-wise nonempty clipped interval, and an optimized expected-length upper phase separating privacy-free, ordinary private-regression, and higher-order global-sensitivity terms. On the unchanged full class, prove the ordinary γ-smooth honest-length lower bound and the fixed-dimensional β-smooth private direct-regression upper bound, and state the resulting nonsharp full-class and attainable-class brackets, including a public selector between the two attainable upper constructions. Keep the exact full-class nuisance/private-Gram confidence frontier open; no matched full-class phase is claimed."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The exact full-class honest-length frontier remains open: no proved coupling or stabilized higher-order full-class release decides whether gamma, q, or private-Gram privacy costs are minimax necessary."
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The advertised research objective is the exact private pointwise-CATE frontier on the unchanged full class, but the proved full-class result is only a nonsharp bracket between an ordinary γ-smooth two-law lower bound and a β-smooth direct-regression upper bound."
  - "The phase-sensitive higher-order interval is proved only on P_att, whose known uniform design is a genuine law-side restriction, and its ordinary lower bound does not establish that either the q-branch or the private-Gram branch is necessary."
  - "Replace the uniform-design Lebesgue projector and globally sensitive quadratic Gram release with a private density-weighted, locally stabilized construction on P_full."
reusable_artifacts:
  - "discovery/core.json — sound typed graph for the attainable higher-order interval, full-class direct interval, and nonsharp brackets"
  - "discovery/solve_lem_localized_score_concentration_unrestricted_rank.json — GLZ/undecoupling unrestricted-rank concentration derivation"
  - "discovery/solve_thm_honest_private_pointwise_interval_unrestricted_rank.json — clipped-center nonempty honest private interval chain"
  - "discovery/solve_prop_full_class_nonsharp_length_bracket.json — same-class lower/direct-upper bracket"
  - "discovery/gaps.json — literature map and the surviving exact-frontier research gap"
seeds_burned:
  - index: 0
    one_liner: "S1: matched central-private pointwise CATE phase"
    reason: "The paired-microcell q<gamma angle is incompatible with gamma-Hölder CATE smoothness; its invalid transport step is not revived."
proof_attempt_summary: |
  The first angle attempted a paired-microcell q=α+β private lower frontier, but the construction's CATE perturbation violated γ-Hölder smoothness when q<γ, so that seed was burned rather than laundered. The switched angle proved a fully private higher-order honest interval on a concrete attainable uniform-design subclass, an unrestricted-upper-rank concentration/remainder chain, a transcript-wise nonempty clipped release, and nonsharp full/attainable-class expected-length brackets. What remains is the exact full-class frontier: it needs either a density-weighted stabilized higher-order estimator with uniform privacy/remainder control or a matching private coupling/tracing converse.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 95097930
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 95097930
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_dp_cate_common_support_hypercube_frontier / v1 — Downgraded

**Topic.** Construct finite-sample replacement-DP honest confidence intervals for the pointwise Hölder CATE at an interior anchor under overlap, bounded common-support outcomes, and positive local design density. On the concrete uniform-design attainable subclass, build a fully private higher-order local learner with privatized nuisance pilots and localized linear and quadratic moments; prove an unrestricted-finite-rank remainder bound, a transcript-wise nonempty clipped interval, and an optimized expected-length upper phase separating privacy-free, ordinary private-regression, and higher-order global-sensitivity terms. On the unchanged full class, prove the ordinary γ-smooth honest-length lower bound and the fixed-dimensional β-smooth private direct-regression upper bound, and state the resulting nonsharp full-class and attainable-class brackets, including a public selector between the two attainable upper constructions. Keep the exact full-class nuisance/private-Gram confidence frontier open; no matched full-class phase is claimed.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** D0.5 math review passed, but the typed review remained non-converging at a 7.3 subfield ceiling below the 7.8 field floor; closing the full-class frontier requires a new stabilized estimator or private coupling converse.

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
