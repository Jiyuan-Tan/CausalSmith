---
qid: eid_mixdag_budget_count_frontier
spec: v1
topic: "Characterize the adaptive minimax number N*(n,K,d,tau,s) of size-at-most-s stochastic hard interventions needed to recover the oriented union of true edges across K DAG components with union indegree at most d and mixture-ancestor cyclic complexity at most tau. A query returns the complete barred-copy d-separation relation in the I-mixture DAG, with the observational oracle free and I-mixture faithfulness as the population bridge. Derive an explicit universal-factor frontier over every feasible s, legal full-oracle transcript lower pairs, and exact formulas for directed-tree mixtures and the cycle-free-ancestor class. Upper bounds must exploit emergent-path parent blocking, not merely replay CADIM or an unevaluated decision-tree recursion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For Delta=V, the complete CI oracle reduces to surviving descendant sets of targeted roots; 15,600 exhaustive three-node and 76,800 randomized four-node CI checks found no discrepancy. Degree-preserving parent-swap adversaries support feasibility thresholds s=d for cycle-free ancestors and s=min(d+1,n-1) once cyclic complexity one is allowed. Exact supported slices are N*=3 for three-node two-tree mixtures at s>=2, N*=n for cycle-free indegree-one mixtures at s=1, and N*=n at the dense endpoint; twelve positive-rational fixtures passed 6,272 exact probability CI checks. UNRESOLVED BOTTLENECK: Prove matching all-parameter adaptive count bounds by making enough blocker requirements coexist on a legal baseline transcript, or show how adaptation exploits their incompatibility, and complete the arbitrary-tree/cycle-free formulas. EARLY KILL TEST: Independently exhaust the four-node K=2,d<=2,tau<=1,Delta=V full barred-copy oracle, starting with the d=2 parent-swap pair, over every size-two target and conditioning set; any distinguishing answer or failure of simultaneous faithful rational realization stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_mixdag_budget_count_frontier.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The proposed explicit universal-factor N*(n,K,d,tau,s) frontier and exact general directed-tree/cycle-free formulas remain open; only feasibility, a blocker-cover upper bound, transcript tools, and three exact slices were established."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The headline all-parameter, evaluable universal-factor frontier remains explicitly to-prove; the delivered feasibility threshold, cover upper bound, and supported slices are a strictly weaker kernel."
  - "The all-parameter constant-factor frontier and general structured-class formulas remain open."
  - "The load-bearing all-parameter step remains coexistence of blocker requirements on one legal baseline transcript."
reusable_artifacts:
  - discovery/core.json
  - discovery/solve_thm_exact_supported_slices.json
  - discovery/writeup.tex
  - reviews/angle0_v1.json
  - reviews/angle0_v2.json
seeds_burned: []
proof_attempt_summary: |
  Discovery established the exact intervention-size feasibility boundary, a parent-blocking
  cover upper bound, legal full-oracle transcript and faithful-realization tools, and three
  exact supported slices. The matching all-parameter adaptive converse collapsed because the
  blocker requirements could not be made to coexist on one legal capped baseline; consequently
  the promised universal frontier and general tree/cycle-free formulas remain open.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 21853615
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 21853615
  total_tokens_consumed: null
banked_on: "2026-09-11"
---

# eid_mixdag_budget_count_frontier / v1 — Failed

**Topic.** Characterize the adaptive minimax number N*(n,K,d,tau,s) of size-at-most-s stochastic hard interventions needed to recover the oriented union of true edges across K DAG components with union indegree at most d and mixture-ancestor cyclic complexity at most tau. A query returns the complete barred-copy d-separation relation in the I-mixture DAG, with the observational oracle free and I-mixture faithfulness as the population bridge. Derive an explicit universal-factor frontier over every feasible s, legal full-oracle transcript lower pairs, and exact formulas for directed-tree mixtures and the cycle-free-ancestor class. Upper bounds must exploit emergent-path parent blocking, not merely replay CADIM or an unevaluated decision-tree recursion. PRESOLVE EVIDENCE REQUIRING VERIFICATION: For Delta=V, the complete CI oracle reduces to surviving descendant sets of targeted roots; 15,600 exhaustive three-node and 76,800 randomized four-node CI checks found no discrepancy. Degree-preserving parent-swap adversaries support feasibility thresholds s=d for cycle-free ancestors and s=min(d+1,n-1) once cyclic complexity one is allowed. Exact supported slices are N*=3 for three-node two-tree mixtures at s>=2, N*=n for cycle-free indegree-one mixtures at s=1, and N*=n at the dense endpoint; twelve positive-rational fixtures passed 6,272 exact probability CI checks. UNRESOLVED BOTTLENECK: Prove matching all-parameter adaptive count bounds by making enough blocker requirements coexist on a legal baseline transcript, or show how adaptation exploits their incompatibility, and complete the arbitrary-tree/cycle-free formulas. EARLY KILL TEST: Independently exhaust the four-node K=2,d<=2,tau<=1,Delta=V full barred-copy oracle, starting with the d=2 parent-swap pair, over every size-two target and conditioning set; any distinguishing answer or failure of simultaneous faithful rational realization stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_mixdag_budget_count_frontier.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** kernel_substituted@oeq:universal-frontier — The headline all-parameter, evaluable universal-factor frontier remains explicitly to-prove; the delivered feasibility threshold, cover upper bound, and supported slices are a strictly weaker kernel.

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
