---
qid: exp_mlupdate_reuse_minimax_design
spec: v1
topic: "Sharp minimax trial panels for reusable causal validation of deterministic ML updates. Fix finite covariate cells with known positive weights, finite deterministic candidate and future policy libraries with known scores, a budget, bounded outcomes, a neutral action, and nondecreasing Gamma-Lipschitz nonneutral mean responses. Prove sharp intervals with common endpoint SCMs, the exact prospective weighted nearest-matching-score width, a certified budget-optimal rational MILP panel, and simultaneous finite-sample interval coverage. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact reductions and bounded enumerations are recorded in <repo-root>/internal/presolve_drafts/exp_mlupdate_reuse_minimax_design.md. UNRESOLVED BOTTLENECK: formalize and implement the rational branch-tree optimality certificate. EARLY KILL TEST: independent three-cell, five-arm exact LP/enumeration comparison."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The note proves an exact worst-identified-width design result, not a minimax statistical-risk characterization."
  - "Its scope is confined to fixed finite libraries with known scores, a prespecified global Lipschitz constant, and deterministic policies, with no robustness to score estimation or expanding libraries."
  - "The certificate contribution reduces in general to exhaustive enumeration and an exponential branch tree, while the polynomial-size case assumes a feasible panel already attaining every coordinatewise full-library minimum."
  - "The inference layer consists of conservative primitive-cell concentration bands and does not address allocation choice, so the single small rational audit provides insufficient practical evidence for a leading-journal score above the mid-six range."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_width_identity.json
  - discovery/solve_thm_sharp_common_endpoints.json
  - discovery/solve_thm_chen_oberst_no_lipschitz_sharpness.json
  - discovery/solve_prop_certificate_sound_complete.json
  - discovery/solve_thm_design_based_coverage.json
seeds_burned: []
proof_attempt_summary: |
  Discovery derived exact finite-library action-score width identities, common compatible endpoint
  constructions, a Chen--Oberst no-Lipschitz limit and finite-score saturation path, exact rational
  panel certificates, and simultaneous assignment-based coverage; the mathematics and cited-source
  audit passed. The contribution nevertheless collapsed at the field novelty gate because its minimax
  object is prospective identified-set diameter rather than statistical risk, its general certificate
  is exponential, and its inference fixes allocation. A field-tier successor needs a genuinely new
  axis such as joint panel/allocation risk optimization or robustness to estimated or expanding scores.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 19764501
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 19764501
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# exp_mlupdate_reuse_minimax_design / v1 — Downgraded

**Topic.** Sharp minimax trial panels for reusable causal validation of deterministic ML updates. Fix finite covariate cells with known positive weights, finite deterministic candidate and future policy libraries with known scores, a budget, bounded outcomes, a neutral action, and nondecreasing Gamma-Lipschitz nonneutral mean responses. Prove sharp intervals with common endpoint SCMs, the exact prospective weighted nearest-matching-score width, a certified budget-optimal rational MILP panel, and simultaneous finite-sample interval coverage. PRESOLVE EVIDENCE REQUIRING VERIFICATION: exact reductions and bounded enumerations are recorded in <repo-root>/internal/presolve_drafts/exp_mlupdate_reuse_minimax_design.md. UNRESOLVED BOTTLENECK: formalize and implement the rational branch-tree optimality certificate. EARLY KILL TEST: independent three-cell, five-arm exact LP/enumeration comparison.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** Mathematical validity and citation verification pass, but the fixed finite known-score interval-diameter design remains structurally incremental and cannot meet the field floor without a new research axis.

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
