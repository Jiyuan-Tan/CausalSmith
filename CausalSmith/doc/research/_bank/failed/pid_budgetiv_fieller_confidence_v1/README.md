---
qid: pid_budgetiv_fieller_confidence
spec: v1
topic: "Weak-first-stage robust confidence complexes for BudgetIV. In the fixed-p scalar constant-effect model with independent two-sample instruments, jointly Gaussian reduced-form pairs (betaYhat_j,betaXhat_j) with known positive-definite within-pair covariance, arbitrarily weak first stages, and Penn et al.'s fixed nested magnitude-count pleiotropy budgets, define the whole-set complex C_alpha by projecting the exact joint Gaussian ellipsoid through betaY−theta betaX in Gamma. Prove uniform coverage of the entire population identified set. Derive the separable standardized band-cost formula, exact nested-quota min-cost flow, exchange-cycle structural partition, and certified polynomial root isolation enumerating every interval and ray. Prove the trimmed first-stage generic tail criterion, lexicographic polynomial resolution of cutoff-equality cases, impossibility of uniformly honest bounded complexes under local weak instruments, and joint endpoint limits/component recovery only on separated positive-width regular faces. Consumer: the 48-pair GWAS study where MR-Egger conclusions changed under SNP recoding. Distinguish BudgetIV quota/topology coverage from Schlemper–Moreira and VIPER validification. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived M(theta) as the minimum nested-quota sum of squared standardized distances to violation bands, an O_K(p^(K+1)) exchange-cycle partition, degree-at-most-2p boundary polynomials, and a trimmed first-stage tail limit with lexicographic equality-case resolution. Checks included 80 quota/exhaustive comparisons, 12 correlated-block quadratic programs, 40 directional tails, 126 structural cells, tied thresholds, zero first stages, and tangencies. UNRESOLVED BOTTLENECK: Implement the exchange-cycle partition and complete boundary-isolation certificate, then prove exact agreement with exhaustive semialgebraic assignment inversion on all small rational cases. EARLY KILL TEST: Test 100 rational instances with p≤6,K≤2 and require identical components, singleton points, endpoints, and rays; any omission fails the computational kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_budgetiv_fieller_confidence.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: NO-PASS
tier_at_derivation: NA
proposal_promise_gap: null
reusable: unknown
reraise_status: retry
gap_reasons:
  - "The model is called an independent two-sample experiment while allowing arbitrary within-pair covariance B_j; genuinely independent exposure and outcome GWAS summaries have B_j=0, so either impose B_j=0 or rename and define a correlated/overlapping-summary Gaussian experiment."
  - "The core calls Gamma the published BudgetIV class but permits b1=0 and weakly increasing budgets, whereas Penn et al.'s published BudgetIV definition requires 0<b1<⋯<bK; impose those inequalities or explicitly rename this as a generalized redundant-tier extension."
reusable_artifacts:
  - "discovery/proto_core.json — field-rated quota-flow/confidence-complex proposal after the paired-summary model-scope repair; a retry should first impose the strict published BudgetIV budget domain."
  - "reviews/angle0_v1.json through reviews/angle0_v5.json — complete revision history and anti-rotation evidence."
seeds_burned:
  - index: 0
    one_liner: "quota-flow whole-set confidence complex"
    reason: "Angle 0 exhausted the five-revision anti-rotation cap; the validity gate rejected retrying or switching merely to escape the editorial cap."
proof_attempt_summary: |
  Angle 0 developed a field-rated exact-Gaussian quota-envelope and certified
  inversion proposal, resolving successive sanity, domain, q-versus-q-plus,
  exact-arithmetic, and paired-summary model-scope defects. The fifth review
  found a new published-BudgetIV budget-domain mismatch after a whole-core
  audit, so the anti-rotation cap terminated the run before Stage D0 or any Lean
  proof attempt. The mathematical kernel was not refuted; a future retry should
  begin with 0 < b1 < ⋯ < bK and preserve the paired-summary terminology.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 24255595
  pipeline_claude_tokens: 0
  total_tokens_consumed: null
banked_on: "2026-09-07"
---

# pid_budgetiv_fieller_confidence / v1 — Failed

**Topic.** Weak-first-stage robust confidence complexes for BudgetIV. In the fixed-p scalar constant-effect model with independent two-sample instruments, jointly Gaussian reduced-form pairs (betaYhat_j,betaXhat_j) with known positive-definite within-pair covariance, arbitrarily weak first stages, and Penn et al.'s fixed nested magnitude-count pleiotropy budgets, define the whole-set complex C_alpha by projecting the exact joint Gaussian ellipsoid through betaY−theta betaX in Gamma. Prove uniform coverage of the entire population identified set. Derive the separable standardized band-cost formula, exact nested-quota min-cost flow, exchange-cycle structural partition, and certified polynomial root isolation enumerating every interval and ray. Prove the trimmed first-stage generic tail criterion, lexicographic polynomial resolution of cutoff-equality cases, impossibility of uniformly honest bounded complexes under local weak instruments, and joint endpoint limits/component recovery only on separated positive-width regular faces. Consumer: the 48-pair GWAS study where MR-Egger conclusions changed under SNP recoding. Distinguish BudgetIV quota/topology coverage from Schlemper–Moreira and VIPER validification. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolver derived M(theta) as the minimum nested-quota sum of squared standardized distances to violation bands, an O_K(p^(K+1)) exchange-cycle partition, degree-at-most-2p boundary polynomials, and a trimmed first-stage tail limit with lexicographic equality-case resolution. Checks included 80 quota/exhaustive comparisons, 12 correlated-block quadratic programs, 40 directional tails, 126 structural cells, tied thresholds, zero first stages, and tangencies. UNRESOLVED BOTTLENECK: Implement the exchange-cycle partition and complete boundary-isolation certificate, then prove exact agreement with exhaustive semialgebraic assignment inversion on all small rational cases. EARLY KILL TEST: Test 100 rational instances with p≤6,K≤2 and require identical components, singleton points, endpoints, and rays; any omission fails the computational kernel. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/pid_budgetiv_fieller_confidence.md.

**Novelty target.** field

**Stage -0.5 verdict.** NO-PASS

**Stage 0.5 verdict.** NA

**Banking reason.** D-0.5 angle 0 exhausted five revisions after reviewer REVISE; v5 remained field with S=0 N=0 C=1 but found a new rotating published-BudgetIV budget-domain coherence defect after the whole-core audit.

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
