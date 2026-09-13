---
qid: exp_attrition_chamber_frontier
spec: v1
topic: "Exact attrition-robust randomization inference for an explicitly weighted fixed-count assignment support: under a sharp additive null, arbitrary treatment-indexed observation indicators, and Wilcoxon treated-rank sums with midranks, characterize the supremum exact upper-tail p-value over all legal missing-outcome completions by a complete weak-order chamber complex. Prove unconditional finite-sample validity, an explicit O((2n+1)^k n|Omega| poly(bits)) algorithm with a linear one-missing sweep, O(n^2) additive-effect inversion, and NP-completeness of EXPLICIT-MAX-TAIL for variable k by an explicit rational weighted-support CLIQUE reduction. Include the constrained six-unit non-extreme-completion witness, the equality-face witness, and a conditional saved-support corollary for a prospective cvcrand rank option on prespecified cluster endpoints; do not claim hardness for uniform balance-generated supports or unchanged cptest applicability. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two independent presolves derived weak-order attainment and oracle-tail domination for arbitrary treatment-indexed masks; reconstructed the fixed-k and k=1 algorithms and finite effect inversion; and supplied a polynomial-size CLIQUE reduction whose guard, vertex, and edge weights force exactly an s-vertex lowest tied block. Exact scripts checked 210 graph/target instances through k=4, 1,536 weighted observation schedules, 120 one-missing sweeps, 145 inversion intervals, the 3/4-versus-1 constrained-support witness, and a case where equality faces raise 8/9 to 1. Current literature checks locate arbitrary-missing WMW tests and tie warnings but no supplied-design chamber optimizer or explicit-support hardness result. The cvcrand source confirms a generated support and a distinct residual-contrast test; only a new prespecified-endpoint rank option is claimed. UNRESOLVED BOTTLENECK: Machine-check the midrank subset-sum equality lemma and its lowest-tied-block consequence used by the CLIQUE converse. EARLY KILL TEST: Re-run internal/mill/scratch/mill-w10/verify_exp_attrition_chamber_p1.py, requiring the equality-face result and every small CLIQUE equivalence; for any cvcrand adapter, enumerate sharp-null rejection mass and reject conditioning on survivors or the selected row. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_attrition_chamber_frontier.md"
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: null
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The computational frontier is limited to XP versus variable-k NP-completeness for explicitly listed rationally weighted supports; FPT versus W[1]-hardness and uniform balance-generated supports remain open."
  - "The projected paper score is constrained by this narrow computational scope and by the absence of power, informativeness, or applied evidence showing when the worst-case envelope is useful rather than vacuous."
  - "redundant-assumption@thm:additive-effect-inversion"
  - "positioning_incomplete@thm:weak-order-attainment"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_prop_six_unit_nonextreme.json
  - discovery/solve_thm_explicit_max_tail_np_complete.json
  - discovery/solve_thm_fixed_k_algorithm.json
  - discovery/solve_tex/solve_thm_explicit_max_tail_np_complete.tex
  - discovery/solve_tex/solve_thm_fixed_k_algorithm.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery derived the equality-inclusive weak-order maximum, unconditional validity,
  fixed-k and one-missing algorithms, effect inversion, an explicit-support CLIQUE
  reduction, and a succinct-CRE coefficient evaluator; two statement repairs were
  independently adjudicated and merged. D0.5 nevertheless capped the package at
  subfield (6.8) because it does not resolve FPT versus W[1]-hardness or complexity for
  uniform/generated supports and lacks power or applied-informativeness evidence.
  No counterexample was found, but the math and positioning panels still requested one
  redundant-assumption cleanup and targeted literature positioning, so the banked note
  is a research artifact rather than a formally verified result.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 13734604
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 13734604
  total_tokens_consumed: null
banked_on: "2026-09-13"
---

# exp_attrition_chamber_frontier / v1 — Downgraded

**Topic.** Exact attrition-robust randomization inference for an explicitly weighted fixed-count assignment support: under a sharp additive null, arbitrary treatment-indexed observation indicators, and Wilcoxon treated-rank sums with midranks, characterize the supremum exact upper-tail p-value over all legal missing-outcome completions by a complete weak-order chamber complex. Prove unconditional finite-sample validity, an explicit O((2n+1)^k n|Omega| poly(bits)) algorithm with a linear one-missing sweep, O(n^2) additive-effect inversion, and NP-completeness of EXPLICIT-MAX-TAIL for variable k by an explicit rational weighted-support CLIQUE reduction. Include the constrained six-unit non-extreme-completion witness, the equality-face witness, and a conditional saved-support corollary for a prospective cvcrand rank option on prespecified cluster endpoints; do not claim hardness for uniform balance-generated supports or unchanged cptest applicability. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Two independent presolves derived weak-order attainment and oracle-tail domination for arbitrary treatment-indexed masks; reconstructed the fixed-k and k=1 algorithms and finite effect inversion; and supplied a polynomial-size CLIQUE reduction whose guard, vertex, and edge weights force exactly an s-vertex lowest tied block. Exact scripts checked 210 graph/target instances through k=4, 1,536 weighted observation schedules, 120 one-missing sweeps, 145 inversion intervals, the 3/4-versus-1 constrained-support witness, and a case where equality faces raise 8/9 to 1. Current literature checks locate arbitrary-missing WMW tests and tie warnings but no supplied-design chamber optimizer or explicit-support hardness result. The cvcrand source confirms a generated support and a distinct residual-contrast test; only a new prespecified-endpoint rank option is claimed. UNRESOLVED BOTTLENECK: Machine-check the midrank subset-sum equality lemma and its lowest-tied-block consequence used by the CLIQUE converse. EARLY KILL TEST: Re-run internal/mill/scratch/mill-w10/verify_exp_attrition_chamber_p1.py, requiring the equality-face result and every small CLIQUE equivalence; for any cvcrand adapter, enumerate sharp-null rejection mass and reject conditioning on survivors or the selected row. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/exp_attrition_chamber_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G graded the delivered package subfield with paper_score_ceiling 6.8 below the 7.4 field floor and salvageable=false; FPT/W[1], generated-support complexity, and applied informativeness remain unresolved, with local redundant-assumption and positioning findings unrepaired.

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
