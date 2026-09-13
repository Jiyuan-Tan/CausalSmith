---
qid: scm_functional_support_hedge_complete
spec: v1
topic: "For finite latent-variable causal DAGs with specified observed alphabets, known qualitative functional nodes W, observed support literals Pi, and named x,y, construct FID-S(G,W,Pi,x,y): a terminating graph/support algorithm returning inconsistency, a support-valid formula for P_x(y), or two finite compatible models with identical observed law and unequal target. Prove completeness via a bounded functional-support hedge grammar and support-preserving latent lifting theorem, with explicit certificate/search and rational witness bit-size bounds. Preserve latent-root independence and structural zeros; do not substitute generic real elimination, constrained arithmetic-circuit testing, or the fully observed special case for the latent headline. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A complete fully observed criterion was derived: on every admissible support, identification is equivalent to agreement of deterministic completions sharing observationally reached CPT rows; disagreement yields common-support rational pairs with denominator at most 8nm and target gap at least 3/4, while agreement gives a guarded g-formula. Exact Fraction checks covered 744 realizable supports, 8,928 query/support cases, and 458 constructed NONID pairs; inconsistent clauses, absent treatment support, intervention-exposed rows, cancellation, and the supported bow were tested, with no current-paper collision found. UNRESOLVED BOTTLENECK: Prove the latent lifting theorem that every residual failure yields a bounded local response obstruction extending to two full independent-latent models with the same observed law/support and different target, and conversely yields a support-valid formula; derive its obstruction grammar and global rational certificate bounds. EARLY KILL TEST: Exhaust the binary graph U->A,B; V->A,C; A->B->C with independent U,V over its 4,096 deterministic skeletons and all observed supports of size at most four for P_{A=a}(C=c); any nonextendable proposed certificate, wrong formula, or proved real separating fiber without a rational pair stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_functional_weakpositivity_complete.md"
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "kernel_substituted"
reusable: solver_blocked
reraise_status: retry
gap_reasons:
  - "The latent FID-S trichotomy promised by the proposal is not delivered: this node expressly leaves the grammar, latent independent-source lift, rational witnesses, formula reconstruction, and global bounds open, while the proved kernel is restricted to the fully observed case and an abstract conditional ID embedding."
  - "The headline algorithmic-identification deliverable has no executable production system, terminal-certificate syntax, or computable formula/witness output; construction handles and an open-ended question cannot supply the required support-valid FID-S map."
reusable_artifacts:
  - "discovery/core.json — verified statement graph, citation attestations, and literature map"
  - "discovery/writeup.tex — fully observed completion frontier, support oracle, supported-bow witness, and abstract classical-ID compiler theorem"
  - "discovery/proto_core.json — flagship latent-lifting specification and exact support/rational-certificate requirements"
seeds_burned: []
proof_attempt_summary: |
  The run corrected the comparator literature, verified eight cited lemmas from official sources, and proved a finite support oracle, a tunable fully observed completion frontier, a supported-bow separating pair, and an abstract classical-ID compiler theorem. It did not construct the advertised latent FID-S grammar or prove the independent-source latent lift, rational equal-law witness theorem, converse formula reconstruction, certificate syntax, kill-instance audit, or global bounds. The D0.5 panel and an independent validity gate therefore classified the claimed latent kernel as substituted rather than merely incomplete at a lower novelty tier.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 26686819
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 26686819
  total_tokens_consumed: null
banked_on: "2026-09-10"
---

# scm_functional_support_hedge_complete / v1 — Failed

**Topic.** For finite latent-variable causal DAGs with specified observed alphabets, known qualitative functional nodes W, observed support literals Pi, and named x,y, construct FID-S(G,W,Pi,x,y): a terminating graph/support algorithm returning inconsistency, a support-valid formula for P_x(y), or two finite compatible models with identical observed law and unequal target. Prove completeness via a bounded functional-support hedge grammar and support-preserving latent lifting theorem, with explicit certificate/search and rational witness bit-size bounds. Preserve latent-root independence and structural zeros; do not substitute generic real elimination, constrained arithmetic-circuit testing, or the fully observed special case for the latent headline. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A complete fully observed criterion was derived: on every admissible support, identification is equivalent to agreement of deterministic completions sharing observationally reached CPT rows; disagreement yields common-support rational pairs with denominator at most 8nm and target gap at least 3/4, while agreement gives a guarded g-formula. Exact Fraction checks covered 744 realizable supports, 8,928 query/support cases, and 458 constructed NONID pairs; inconsistent clauses, absent treatment support, intervention-exposed rows, cancellation, and the supported bow were tested, with no current-paper collision found. UNRESOLVED BOTTLENECK: Prove the latent lifting theorem that every residual failure yields a bounded local response obstruction extending to two full independent-latent models with the same observed law/support and different target, and conversely yields a support-valid formula; derive its obstruction grammar and global rational certificate bounds. EARLY KILL TEST: Exhaust the binary graph U->A,B; V->A,C; A->B->C with independent U,V over its 4,096 deterministic skeletons and all observed supports of size at most four for P_{A=a}(C=c); any nonextendable proposed certificate, wrong formula, or proved real separating fiber without a rational pair stops or pivots the run. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/scm_functional_weakpositivity_complete.md

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The latent FID-S trichotomy promised by the proposal is not delivered: its grammar, independent-source lift, rational witnesses, converse reconstruction, certificate syntax, kill audit, and global bounds remain open.

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
