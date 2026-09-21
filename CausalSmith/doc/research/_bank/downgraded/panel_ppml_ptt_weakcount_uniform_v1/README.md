---
qid: panel_ppml_ptt_weakcount_uniform
spec: v1
topic: "Deterministic–randomized honest-interval frontier for sparse staggered Poisson proportional effects. Fix T at least 3, alpha in (0,.1), observed cohort shares bounded below, and exact independent cohort-time Poisson totals with intensity kappa, normalized time effects, bounded positive exposure masses, and treated multipliers in [1/2,3]. The target is the counterfactual-share weighted proportional effect in [-1/2,2]. Define worst-nuisance minimax expected-length functions for deterministic connected intervals and randomized interval kernels measurable from shares and counts. Prove the exact low-intensity deterministic value, characterize every optimizer and least-favorable configuration, establish the strict randomized gap, and keep the all-untreated-zero restriction as a separate comparison. For arbitrary compact intensity ranges, construct finite count-box and endpoint-grid mixed-integer primal certificates with matching integer lower witnesses and outward error bounds; derive the high-intensity efficient-Gaussian minimax bridge. Credit Moreau–Kastler for the imputed PTT workflow, Martin and Wooldridge for regular fixed-T inference, and generic weak-ratio theory. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivations recovered the three intensity extrema, exact small-intensity deterministic values, observed-share optimizer allowances, randomized zero-information limit, all-intensity zero-atom lower bound, finite integer witness property, and fixed-design Poisson polynomial separation. Arithmetic checks covered T=3 through 12, untreated-zero versus denominator-zero events, integrality gaps, endpoint contacts, count tails, and Gaussian variance examples; no exact collision was found. UNRESOLVED BOTTLENECK: Prove an effective finite covering of the observed-share simplex by uniformly honest finite-grid policy regions, including nominal-coverage contacts, target-endpoint strata, compact intensity variation, and matching integer lower certificates with the full error budget. EARLY KILL TEST: At T=3, alpha=.05, intensity=.01, reproduce the small-count witness and certify a globally honest observed-share deterministic primal and integer lower certificate within .05 using count box K=2 and endpoint mesh .01; any relaxation, sampled-grid check, or fixed-share-only certificate fails. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ppml_ptt_weakcount_uniform.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The early-kill finite certificate was proved, but the general terminating share-and-intensity-uniform rational-polyhedral refinement through equality contacts remains open; the randomized LAN interval-kernel transfer is also not established."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "Stage 0.5 (typed) BELOW NOVELTY FLOOR (triage, round 0) — D0.5.G tier=incremental < floor=field (target=field) and NOT salvageable in scope."
  - "Reaching field requires resolving oeq:uniform-certificate by proving terminating share-and-intensity-uniform rational-polyhedral refinement through nominal-coverage and endpoint equality contacts and producing a nontrivial certificate; this is contribution-redefining/unbounded, not a scoped same-topic repair."
  - "missing-kernel-transfer@thm:gaussian-bridge — length tightness does not control rescaled endpoint locations, so the randomized LAN-to-Gaussian kernel transfer remains incomplete."
  - "bank_comparator_omitted@def:causal-functional-setup — accepted bank result panel_ppml_forbidden_comparison_v1 already proves the positive counterfactual-share population ratio identity and is not explicitly distinguished."
  - "Saying the randomized low-intensity frontier is determined overstates the proved finite-intensity bracket and limiting constant."
reusable_artifacts:
  - "discovery/core.json — final graph, including the exact T=3 early-kill certificate, low-intensity frontier, zero-atom lower bound, finite reduction, and fixed-design separation lemma."
  - "discovery/solve_lem_fixed_design_separation.{json,tex} — closure-continuation repair for discontinuous target-membership strata and strict outward comparison."
  - "discovery/solve_thm_finite_reduction.{json,tex} — count truncation, endpoint rounding, and integrality-preserving finite witness construction."
  - "discovery/gaps.json — literature and prior-proposal map for sparse-Poisson honest interval problems."
seeds_burned:
  - index: 0
    one_liner: "uniform-continuum-certificate"
    reason: "The sole pursued angle exhausted its bounded field-tier scope; reaching field requires the contribution-redefining uniform equality-contact certificate theorem."
proof_attempt_summary: |
  The run derived exact low-intensity and zero-atom results, a finite truncation/rounding reduction,
  a corrected semialgebraic fixed-design separation lemma, and a complete T=3 early-kill certificate
  with an explicit integral incumbent and branch record. It collapsed at D0.5 because these results
  were judged incremental and the field-level total uniform certificate through equality contacts
  remained open; independently, the randomized Gaussian-bridge proof did not control escaping
  rescaled interval endpoints, so the bank preserves that soundness gap rather than claiming closure.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 22517653
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 22517653
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# panel_ppml_ptt_weakcount_uniform / v1 — Downgraded

**Topic.** Deterministic–randomized honest-interval frontier for sparse staggered Poisson proportional effects. Fix T at least 3, alpha in (0,.1), observed cohort shares bounded below, and exact independent cohort-time Poisson totals with intensity kappa, normalized time effects, bounded positive exposure masses, and treated multipliers in [1/2,3]. The target is the counterfactual-share weighted proportional effect in [-1/2,2]. Define worst-nuisance minimax expected-length functions for deterministic connected intervals and randomized interval kernels measurable from shares and counts. Prove the exact low-intensity deterministic value, characterize every optimizer and least-favorable configuration, establish the strict randomized gap, and keep the all-untreated-zero restriction as a separate comparison. For arbitrary compact intensity ranges, construct finite count-box and endpoint-grid mixed-integer primal certificates with matching integer lower witnesses and outward error bounds; derive the high-intensity efficient-Gaussian minimax bridge. Credit Moreau–Kastler for the imputed PTT workflow, Martin and Wooldridge for regular fixed-T inference, and generic weak-ratio theory. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Independent derivations recovered the three intensity extrema, exact small-intensity deterministic values, observed-share optimizer allowances, randomized zero-information limit, all-intensity zero-atom lower bound, finite integer witness property, and fixed-design Poisson polynomial separation. Arithmetic checks covered T=3 through 12, untreated-zero versus denominator-zero events, integrality gaps, endpoint contacts, count tails, and Gaussian variance examples; no exact collision was found. UNRESOLVED BOTTLENECK: Prove an effective finite covering of the observed-share simplex by uniformly honest finite-grid policy regions, including nominal-coverage contacts, target-endpoint strata, compact intensity variation, and matching integer lower certificates with the full error budget. EARLY KILL TEST: At T=3, alpha=.05, intensity=.01, reproduce the small-count witness and certify a globally honest observed-share deterministic primal and integer lower certificate within .05 using count box K=2 and endpoint mesh .01; any relaxation, sampled-grid check, or fixed-share-only certificate fails. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_ppml_ptt_weakcount_uniform.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5 normalized the note to incremental (score ceiling 5.3 below the field floor 7.4) and found no bounded field-reaching repair; the unresolved Gaussian kernel-transfer gap, accepted-bank comparator omission, and randomized-frontier overstatement are preserved explicitly.

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
