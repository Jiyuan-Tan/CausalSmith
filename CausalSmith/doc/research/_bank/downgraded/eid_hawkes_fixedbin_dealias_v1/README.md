---
qid: eid_hawkes_fixedbin_dealias
spec: v1
topic: "Exact fixed-bin recovery of acyclic Hawkes graphs from two covariance lags. For a stationary labeled multivariate linear Hawkes process with known bin width Delta, positive baselines, a common unknown exponential decay, nonnegative zero-diagonal acyclic excitation matrix, and at least one edge, prove that the mean plus Gamma_1 and Gamma_2 identify beta, every edge amplitude, and the baselines. Establish Gamma_k=exp((A-beta I)(k-1)Delta)J^2K, im Gamma_1=im A, recovery of beta from the restricted transition, exact finite nilpotent-log deconvolution, and edge recovery from the antisymmetric covariance jump. Cover singular A, repeated poles, disconnected components, and zero-edge nonidentification; derive rank-adaptive consistent estimation, support recovery, and simultaneous graph confidence sets. Consumer: Qiao et al.'s metropolitan cellular-alarm logs recorded at 1–9 second resolution. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived K=A(2 beta I-A)Q with Q positive definite and A_ij=max(K_ij-K_ji,0)/lambda_j; a covariance-only Gamma_0,Gamma_1,Gamma_2 corollary also emerged. Recovery passed 400 random/adversarial DAGs (p=2–9, worst error 8.31e-10), 24 independent bin-integral checks, and 207 three-node alias searches. UNRESOLVED BOTTLENECK: Complete a basis-invariant HAC/rank-truncation delta-method proof with explicit conditioning margins and independently audit the two-lag algebra. EARLY KILL TEST: Reproduce diamond and proportional-row cases by independent quadrature; any legal violation of im Gamma_1=im A or the recovered covariance limit kills the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_hawkes_fixedbin_dealias.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons:
  # TODO: paste verbatim reviewer phrases identifying which Conjecture
  # collapsed and why. Source: eid_hawkes_fixedbin_dealias_v1_reviews.jsonl and any
  # *_oneshot_stage0_5_*.txt files in this directory.
reusable_artifacts:
  # TODO: list LP setup / operator / witness / literature_map /
  # counterexample paths inside this directory that future runs should
  # lift rather than re-derive.
seeds_burned: []
proof_attempt_summary: |
  TODO: 2-3 sentence epitaph — what was attempted, what collapsed, what remains.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 134254589
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-05"
---

# eid_hawkes_fixedbin_dealias / v1 — Downgraded

**Topic.** Exact fixed-bin recovery of acyclic Hawkes graphs from two covariance lags. For a stationary labeled multivariate linear Hawkes process with known bin width Delta, positive baselines, a common unknown exponential decay, nonnegative zero-diagonal acyclic excitation matrix, and at least one edge, prove that the mean plus Gamma_1 and Gamma_2 identify beta, every edge amplitude, and the baselines. Establish Gamma_k=exp((A-beta I)(k-1)Delta)J^2K, im Gamma_1=im A, recovery of beta from the restricted transition, exact finite nilpotent-log deconvolution, and edge recovery from the antisymmetric covariance jump. Cover singular A, repeated poles, disconnected components, and zero-edge nonidentification; derive rank-adaptive consistent estimation, support recovery, and simultaneous graph confidence sets. Consumer: Qiao et al.'s metropolitan cellular-alarm logs recorded at 1–9 second resolution. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived K=A(2 beta I-A)Q with Q positive definite and A_ij=max(K_ij-K_ji,0)/lambda_j; a covariance-only Gamma_0,Gamma_1,Gamma_2 corollary also emerged. Recovery passed 400 random/adversarial DAGs (p=2–9, worst error 8.31e-10), 24 independent bin-integral checks, and 207 three-node alias searches. UNRESOLVED BOTTLENECK: Complete a basis-invariant HAC/rank-truncation delta-method proof with explicit conditioning margins and independently audit the two-lag algebra. EARLY KILL TEST: Reproduce diamond and proportional-row cases by independent quadrature; any legal violation of im Gamma_1=im A or the recovered covariance limit kills the theorem. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_hawkes_fixedbin_dealias.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** Operator stop: sound point-process identifiability, but no causal anchor. Zero occurrences of do/intervention/confounding/causal-sufficiency/potential-outcome in the core; none of its 20 assumptions is causal; all 19 references are point-process, time-series or matrix-analysis. Recovering G(A) is Granger-style structure identification whose causal reading needs a causal-sufficiency assumption the paper never states and a literature it never cites.

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
