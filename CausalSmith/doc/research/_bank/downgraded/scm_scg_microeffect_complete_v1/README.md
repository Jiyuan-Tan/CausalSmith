---
qid: scm_scg_microeffect_complete
spec: v1
topic: "Sound-and-complete lagged micro-effect identification from latent-confounded summary time-series graphs. Fix a finite observed coordinate set, lag bound L, directed/bidirected summary H, X,Y,gamma and x. Quantify over every positive finite-alphabet strictly stationary order-L time-homogeneous semi-Markovian SCM with acyclic instantaneous slices and exact summary H. Construct a terminating graph-native TID-SCG procedure that either outputs one finite-cylinder do-free functional valid for every compatible SCM or a finite lag-switch-hedge certificate constructing two compatible stationary SCMs with the same entire observed process law and unequal P(Y_0|do(X_-gamma=x)). Prove soundness, completeness and an explicit termination bound through a lag-robust intrinsic-district transducer; refinement enumeration, generic QE and tautological model gluing do not qualify. Add cylinder plug-in and HAC delta-method inference under positivity and geometric beta-mixing. Consumer: EasyRCA lag-specific anomaly-transmission ranking under hidden confounding. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An independent-shift construction preserves whole-process observational equality, intervention separation, lag bounds, positivity and exact summaries when lifting finite collisions; an acyclic directed-summary subclass reduces to one ordinary ID call on at most n(nL+1) ancestral vertices. The repaired XOR witness gives 19/50 versus 31/50, and a separate positive stationary lag-switch pair has identical observed process laws but effects 13/50 versus 1/2. Checks show raw quotienting need not preserve fixability and per-refinement ID is insufficient. UNRESOLVED BOTTLENECK: Prove a bounded uniform fixing normal form whose states either compile one universal finite-cylinder arithmetic functional or extract two positive temporal-role SCMs, including disagreement between individually identifiable refinements. EARLY KILL TEST: For |V|<=3 and L=1, test the proposed states and rewrites on the front-door witness, the offset-sensitive fixing counterexample and the stationary lag-switch pair; pivot if the procedure accepts the collision, rejects front-door, conflates offsets or needs unrestricted elimination. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_scg_microeffect_complete.md"
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: not_reusable
reraise_status: unknown
gap_reasons:
  - "kernel_substituted@thm:tid-dichotomy; promised complete dichotomy replaced by sound SUCCESS/FAIL/UNKNOWN partial dispatcher"
  - "No bounded faithful same-topic repair; restoring completeness requires the acknowledged offset-sensitive uniform normal form and arbitrary-role fixed-alphabet stationary countermodel extraction, already attempted without success."
  - "positioning@thm:frontdoor-frontier (regression witness, not independent advance)"
  - "related_work@thm:cylinder-hac (standard inference transport)"
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_tid_dichotomy.tex
  - discovery/solve_thm_cylinder_hac.tex
  - discovery/d0_escalation_log.jsonl
seeds_burned: []
proof_attempt_summary: |
  The run attempted an offset-sensitive finite-state fixing procedure with a fixed-alphabet stationary countermodel extractor, then added source-verified Assaad adjustment and front-door success branches and a saturated-ADMG ID branch. The general extractor collapsed because residual witnesses can assign multiple temporal roles to one coordinate, while role restriction, alphabet enlargement, or assuming the final model pair changes or assumes the crux. What remains is a sound terminating SUCCESS/FAIL/UNKNOWN certifier, one explicit stationary whole-law collision, and conditional HAC/ranking consequences, graded incremental rather than field.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 51463849
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 51463849
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# scm_scg_microeffect_complete / v1 — Downgraded

**Topic.** Sound-and-complete lagged micro-effect identification from latent-confounded summary time-series graphs. Fix a finite observed coordinate set, lag bound L, directed/bidirected summary H, X,Y,gamma and x. Quantify over every positive finite-alphabet strictly stationary order-L time-homogeneous semi-Markovian SCM with acyclic instantaneous slices and exact summary H. Construct a terminating graph-native TID-SCG procedure that either outputs one finite-cylinder do-free functional valid for every compatible SCM or a finite lag-switch-hedge certificate constructing two compatible stationary SCMs with the same entire observed process law and unequal P(Y_0|do(X_-gamma=x)). Prove soundness, completeness and an explicit termination bound through a lag-robust intrinsic-district transducer; refinement enumeration, generic QE and tautological model gluing do not qualify. Add cylinder plug-in and HAC delta-method inference under positivity and geometric beta-mixing. Consumer: EasyRCA lag-specific anomaly-transmission ranking under hidden confounding. PRESOLVE EVIDENCE REQUIRING VERIFICATION: An independent-shift construction preserves whole-process observational equality, intervention separation, lag bounds, positivity and exact summaries when lifting finite collisions; an acyclic directed-summary subclass reduces to one ordinary ID call on at most n(nL+1) ancestral vertices. The repaired XOR witness gives 19/50 versus 31/50, and a separate positive stationary lag-switch pair has identical observed process laws but effects 13/50 versus 1/2. Checks show raw quotienting need not preserve fixability and per-refinement ID is insufficient. UNRESOLVED BOTTLENECK: Prove a bounded uniform fixing normal form whose states either compile one universal finite-cylinder arithmetic functional or extract two positive temporal-role SCMs, including disagreement between individually identifiable refinements. EARLY KILL TEST: For |V|<=3 and L=1, test the proposed states and rewrites on the front-door witness, the offset-sensitive fixing counterexample and the stationary lag-switch pair; pivot if the procedure accepts the collision, rejects front-door, conflates offsets or needs unrestricted elimination. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_scg_microeffect_complete.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@thm:tid-dichotomy: promised complete dichotomy replaced by sound SUCCESS/FAIL/UNKNOWN partial dispatcher; D0.5.G graded incremental with paper_score_ceiling 4.7 below the field floor 7.4.

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
