---
qid: panel_loading_transition
spec: v1
topic: "General-r transition-honest counterfactual-entry inference under strong donor factors. For each n observe mutually independent Gaussian blocks X=A+E, R=u+e, C=v+f with known variance, known fixed rank r, singular values of A of order n, fixed incoherence and bounded entries, u in row(A), and v in col(A); the missing untreated mean is theta=u A^+ v and neither target loading is bounded away from zero. Construct an explicit donor-only truncated-SVD interval and prove uniform asymptotic coverage, expected length within a fixed constant of w(P)=sigma sqrt(||uA^+||^2+||A^+v||^2)+sigma^2||A^+||_F, oracle Gaussian length along every sequence where the second-order term is negligible relative to the first, and a matching local KL-neighborhood length lower bound at interior sequences. Compute the interval by fixed-dimensional Gaussian minimum-distance inversion or a certified analytic outer formula plus an observable donor-error allowance and bounded spectral-gate fallback. Credit Yan--Wainwright arXiv:2401.13665 for the panel expansion and Bei--Navjeevan arXiv:2602.07377 for general first-order-degeneracy inference; the narrow new object is the complete general-r strong-donor panel transfer and all-sequence length theorem. Xia--Yan--Wainwright arXiv:2412.09482 and CAST are the same-question consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh derivation obtained the exact conditional Gaussian experiment after donor-only SVD and the sandwich identity V^T X_r^+ U=(MM^T)(U^T X_r V)^(-1)(LL^T), giving an explicit n^(-2)/n^(-3) perturbation bound. A fixed observable allowance was shown to have uniform failure probability at most exp(-n/2)+3(e+n)^(-6) and expected allowance divided by w(P) at most K[log(e+n)/sqrt(n)+log^2(e+n)/n]. The presolve re-derived general-r coverage, transition-order expected length, every-diverging-sequence oracle length, and the two-point/four-corner local lower bound; it also derived an analytic outer interval that avoids nonlinear endpoint optimization. Rank-two calculations checked repeated singular values, cancellation, zero loadings, and spectral failures; current-source checks found no complete-package collision. UNRESOLVED BOTTLENECK: Prove certified finite-precision implementation theorem C: outward SVD, cutoff, and spectral-gate errors must preserve coverage while their extra expected length is o(w(P)) uniformly. EARLY KILL TEST: Certify the analytic outer interval for the rank-two repeated-singular-value donor with outward error o(1/n) uniformly from zero through B sqrt(n) loading norms and a valid uncertain-gate fallback; stop or change construction if joint zero or arbitrarily slow divergence breaks the budget. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_loading_transition.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "No sharp minimax constant across the transition regime; narrow square one-target known-rank homoskedastic Gaussian subclass; abstract certified arithmetic lacks a deployed implementation/application; related_work_incomplete@thm:uniform-coverage remains as a literature-positioning caveat."
reusable: not_reusable
reraise_status: re-raise
gap_reasons:
  - "It does not establish a sharp transition-regime minimax constant: away from first-order dominance, the upper and lower results contain unrelated constants."
  - "The scope remains a canonical square one-target Gaussian subclass with known rank, variance, exact span membership, and strong factors, limiting its importance relative to broadly applicable panel-inference results."
  - "The certified-computation result concerns an abstract arbitrary-exponent directed-arithmetic model with exact-dyadic controls, and the package supplies no implemented certificate, simulation, or application."
  - "Unrepaired caveat: related_work_incomplete@thm:uniform-coverage."
reusable_artifacts:
  - "discovery/core.json — audited theorem graph, including the donor-conditional bilinear reduction and transition upper/lower bounds."
  - "discovery/writeup.tex — complete mathematical derivation and certified-arithmetic recurrence."
  - "discovery/proto_core.json — proposal seeds, literature map, comparator receipts, and scope caveats."
  - "reviews/review_math.json — passing mathematical review and Yan--Wainwright citation check."
seeds_burned:
  - index: 0
    one_liner: "seed:transition-entry"
    reason: "Selected transition-entry lane is mathematically sound but structurally capped at subfield under the fixed field floor."
proof_attempt_summary: |
  The run proved the square one-target strong-donor transition package: uniform coverage through joint zero, expected length of order a_n+b_n, a local honest converse, the first-order oracle constant, and a certified finite-precision transfer. Independent audits repaired the Yan--Wainwright class embedding and the numerical error recurrence. D0.5 nevertheless capped the result at subfield because it lacks a sharp constant across the full transition regime, remains confined to a narrow Gaussian subclass, and has no deployed implementation or application; one related-work finding also remains unrepaired.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 40740867
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 40740867
  total_tokens_consumed: null
banked_on: "2026-09-15"
---

# panel_loading_transition / v1 — Downgraded

**Topic.** General-r transition-honest counterfactual-entry inference under strong donor factors. For each n observe mutually independent Gaussian blocks X=A+E, R=u+e, C=v+f with known variance, known fixed rank r, singular values of A of order n, fixed incoherence and bounded entries, u in row(A), and v in col(A); the missing untreated mean is theta=u A^+ v and neither target loading is bounded away from zero. Construct an explicit donor-only truncated-SVD interval and prove uniform asymptotic coverage, expected length within a fixed constant of w(P)=sigma sqrt(||uA^+||^2+||A^+v||^2)+sigma^2||A^+||_F, oracle Gaussian length along every sequence where the second-order term is negligible relative to the first, and a matching local KL-neighborhood length lower bound at interior sequences. Compute the interval by fixed-dimensional Gaussian minimum-distance inversion or a certified analytic outer formula plus an observable donor-error allowance and bounded spectral-gate fallback. Credit Yan--Wainwright arXiv:2401.13665 for the panel expansion and Bei--Navjeevan arXiv:2602.07377 for general first-order-degeneracy inference; the narrow new object is the complete general-r strong-donor panel transfer and all-sequence length theorem. Xia--Yan--Wainwright arXiv:2412.09482 and CAST are the same-question consumer. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A fresh derivation obtained the exact conditional Gaussian experiment after donor-only SVD and the sandwich identity V^T X_r^+ U=(MM^T)(U^T X_r V)^(-1)(LL^T), giving an explicit n^(-2)/n^(-3) perturbation bound. A fixed observable allowance was shown to have uniform failure probability at most exp(-n/2)+3(e+n)^(-6) and expected allowance divided by w(P) at most K[log(e+n)/sqrt(n)+log^2(e+n)/n]. The presolve re-derived general-r coverage, transition-order expected length, every-diverging-sequence oracle length, and the two-point/four-corner local lower bound; it also derived an analytic outer interval that avoids nonlinear endpoint optimization. Rank-two calculations checked repeated singular values, cancellation, zero loadings, and spectral failures; current-source checks found no complete-package collision. UNRESOLVED BOTTLENECK: Prove certified finite-precision implementation theorem C: outward SVD, cutoff, and spectral-gate errors must preserve coverage while their extra expected length is o(w(P)) uniformly. EARLY KILL TEST: Certify the analytic outer interval for the rank-two repeated-singular-value donor with outward error o(1/n) uniformly from zero through B sqrt(n) loading norms and a valid uncertain-gate fallback; stop or change construction if joint zero or arbitrarily slow divergence breaks the budget. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/panel_loading_transition.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5: delivered tier subfield below the field floor; paper_score_ceiling 7 < 7.4 and salvageable=false.

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
