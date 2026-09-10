---
qid: exp_bandit_random_qv_studentization_frontier
spec: v1
topic: "K1 prove stable basin-mixed normality for bounded adaptive IPW-Z scores under a finite tail attractor and uniform attraction modulus. K2 prove realized-QV studentization uniformly pivotal. K3 prove a deterministic sandwich valid for a contrast at every nominal level iff its variance is basin-invariant. K4 prove validity for all contrasts iff V_J is deterministic. Include the Guo-Xu two-basin witness and HeartSteps consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional predictable QV convergence Q_T/T to V_J gives the martingale stable-limit spine. Bounded scores support uniform Lindeberg, and realized minus predictable QV should be negligible, so same-path studentization removes the mixture. Identifiability of centered Gaussian scale mixtures yields necessity at every nominal level; one-level accidental coverage is excluded. Positive basin masses, eigenvalue bounds, attraction tails, and a Cesaro policy-error modulus make the class falsifiable. Separatrix uniformity remains unchecked. Equal scalar variances with unequal covariance matrices verify why contrastwise and matrixwise statements must remain distinct here. UNRESOLVED BOTTLENECK: Convert the attraction and Cesaro assumptions into one uniform triangular-array modulus sufficient for stable convergence, inverse-QV control, and matching near-separatrix bounds in the exact recursion. EARLY KILL TEST: Analyze and simulate the no-intercept recursion from states approaching the basin boundary. Pivot to margin-restricted inference if attraction tails are not uniform; stop if realized-QV t-statistics fail in either attained basin."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REVISE
proposal_promise_gap: "tier_genuinely_below"
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "The finite-attractor mixed-normal and pivotality results assume finite tail selection and a vanishing uniform Cesaro-attraction modulus; these load-bearing dynamics are not established for the Guo--Xu recursion, and the HeartSteps discussion is only a consumer interpretation."
  - "The deterministic-sandwich iff statements are conditional scale-mixture identification and polarization results, leaving the unverified recursion-to-class bridge as the specific obstacle to field tier."
  - "It does not characterize validity on Saco's published variance-growth class, so the framing of an inference frontier or exact temporal boundary overstates a sufficient condition plus one violating witness."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/d0_working.json
  - discovery/proof_archive/
  - formalization/plan.json
  - graph.json
seeds_burned: []
proof_attempt_summary: |
  Discovery discharged all 19 obligations (14 proved and five source-attested cited interfaces), including the bounded Saco counterexample, early-stabilization repair, conditional finite-attractor mixture/pivot results, sandwich characterizations, and the four-mode Guo--Xu obstruction. Formalization reached F2.5 and forced several source-faithfulness repairs, but the final cold novelty review found that field tier still requires a separate proof of Guo--Xu switching-layer escape, compact-uniform attraction, and a bridge from the published Gaussian recursion to the bounded causal-score setting. The current conditional result is sound at subfield tier; it was banked for a future re-raised run rather than weakening the field floor.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 559856553
  pipeline_claude_tokens: 68809382
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# exp_bandit_random_qv_studentization_frontier / v1 — Downgraded

**Topic.** K1 prove stable basin-mixed normality for bounded adaptive IPW-Z scores under a finite tail attractor and uniform attraction modulus. K2 prove realized-QV studentization uniformly pivotal. K3 prove a deterministic sandwich valid for a contrast at every nominal level iff its variance is basin-invariant. K4 prove validity for all contrasts iff V_J is deterministic. Include the Guo-Xu two-basin witness and HeartSteps consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: Conditional predictable QV convergence Q_T/T to V_J gives the martingale stable-limit spine. Bounded scores support uniform Lindeberg, and realized minus predictable QV should be negligible, so same-path studentization removes the mixture. Identifiability of centered Gaussian scale mixtures yields necessity at every nominal level; one-level accidental coverage is excluded. Positive basin masses, eigenvalue bounds, attraction tails, and a Cesaro policy-error modulus make the class falsifiable. Separatrix uniformity remains unchecked. Equal scalar variances with unequal covariance matrices verify why contrastwise and matrixwise statements must remain distinct here. UNRESOLVED BOTTLENECK: Convert the attraction and Cesaro assumptions into one uniform triangular-array modulus sufficient for stable convergence, inverse-QV control, and matching near-separatrix bounds in the exact recursion. EARLY KILL TEST: Analyze and simulate the no-intercept recursion from states approaching the basin boundary. Pivot to margin-restricted inference if attraction tails are not uniform; stop if realized-QV t-statistics fail in either attained basin.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REVISE

**Banking reason.** Cold referee: the field lift needs separate switching-layer, compact-uniform hitting/escape, and Gaussian-to-bounded bridge theory; the current conditional result is sound at subfield tier.

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
