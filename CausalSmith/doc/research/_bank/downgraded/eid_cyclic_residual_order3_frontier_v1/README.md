---
qid: eid_cyclic_residual_order3_frontier
spec: v1
topic: "Fix the three-variable cyclic SEM X1=aX2+eps1, X2=bX1+cX3+eps2, X3=dX2+eps3 with abcd nonzero and 1-ab-cd nonzero. Disturbances are centered, non-Gaussian, have finite third moments, satisfy eps1 independent of eps3 and the path connected-set Markov plus Tramontano-Drton-Etesami independence-genericity conditions; eps2 may depend arbitrarily on both outer disturbances. The information input is the observed cumulant tensor through order K in {2,3}; the query is only (a,d). For candidate (alpha,delta), define residual cross-cumulants F11, F21 and F12. Construct the explicit observed-cumulant chart D and prove that D nonzero makes their complex common zero set the singleton (a,d), with a rational inverse from the linear first subresultant of two observable cubics. On a nonempty covariance-regular locus, construct a smooth one-dimensional legal order-two fiber for (a,d), proving the least identifying order is three; also prove the full observed law retains a two-dimensional (b,c) fiber. Estimate (a,d) by feasible overidentified GMM on a compact sixth-Wasserstein regular subclass with quantitative chart, Jacobian and influence-covariance margins, and derive a uniformly valid sandwich ellipse. Explicitly distinguish Draisma-Kuhnt-Zwiernik, Jiang, Mesters-Zwiernik, Ribot-Seigal-Zwiernik and the banked general cumulant-transfer obstruction. Consumer: a prospective BayCausal/WIHS extension may report outer coefficients as robust under an independently justified overlapping-cycle/path-dependence motif while leaving central coefficients as a sensitivity fiber; do not claim its published disjoint-cycle theorem already covers this motif. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The residual covariance equation eliminates delta as t(alpha)/l(alpha); substituting into F21 and F12 gives two observable cubics P and Q. On the nonzero chart, their first subresultant is linear, yielding a=-s0/s1 and d=t(a)/l(a). Exact expansion verifies the legal exponential-source witness, all chart factors, the singleton residual ideal, a rank-two Jacobian, 100 fresh rational perturbations, and a nonlinear-middle stress case. A five-source construction realizes every nearby positive-definite path covariance with independent non-Gaussian endpoints, producing a one-dimensional order-two query fiber; an explicit residual shear preserves a two-dimensional full-law central-coefficient fiber. Literature checks found no query-specific cyclic order-three inverse. UNRESOLVED BOTTLENECK: Prove uniform asymptotic linearity of feasible optimally weighted GMM on the stated compact sixth-moment class, including centered third-cumulant influence functions, covariance estimation, separation, and margin diagnostics. EARLY KILL TEST: Implement the fixed cubic subresultant using only observed tensors with the true mechanism hidden; reproduce both witness families and exact covariance twins on a rational neighborhood. Stop if a nontrue common root survives with D nonzero, specialization fails, or the covariance realization leaves the legal model. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_cyclic_residual_order3_frontier.md."
novelty_target: field
banked_novelty_tier: incremental
tier_at_proposal: ACCEPT
tier_at_derivation: REJECT
proposal_promise_gap: "The delivered theorem proves D!=0 only at one witness and a local neighborhood, not on an open-dense or full-measure legal subclass."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The delivered identification theorem recovers (a,d) only on the sufficient chart D != 0, while the scope of that chart is established by one explicit witness and a local neighborhood rather than a genericity or broad-class result."
  - "Consequently, the least-identifying-order theorem is confined to a nonempty regular intersection and does not establish a model-wide order-three frontier."
  - "The fixed-motif scope, unquantified prevalence of the identifying chart, and lack of practical evidence keep the contribution below the field floor."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_lem_observable_cubic_reduction.tex
  - discovery/solve_thm_central_full_law_fiber.tex
seeds_burned: []
proof_attempt_summary: |
  Discovery proved the chart-conditional rational recovery of the outer coefficients, the legal order-two covariance fiber, the central-coefficient full-law fiber, and totalized uniform GMM/sandwich results. The field claim collapsed at novelty review because D != 0 was established only at an explicit witness and locally, leaving no generic or broad-class order-three frontier. A re-raised topic would need a legal five-source subclass and an open-dense or full-measure nonvanishing theorem for D, followed by a generic minimality headline.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 17128246
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 17128246
  total_tokens_consumed: null
banked_on: "2026-09-14"
---

# eid_cyclic_residual_order3_frontier / v1 — Downgraded

**Topic.** Fix the three-variable cyclic SEM X1=aX2+eps1, X2=bX1+cX3+eps2, X3=dX2+eps3 with abcd nonzero and 1-ab-cd nonzero. Disturbances are centered, non-Gaussian, have finite third moments, satisfy eps1 independent of eps3 and the path connected-set Markov plus Tramontano-Drton-Etesami independence-genericity conditions; eps2 may depend arbitrarily on both outer disturbances. The information input is the observed cumulant tensor through order K in {2,3}; the query is only (a,d). For candidate (alpha,delta), define residual cross-cumulants F11, F21 and F12. Construct the explicit observed-cumulant chart D and prove that D nonzero makes their complex common zero set the singleton (a,d), with a rational inverse from the linear first subresultant of two observable cubics. On a nonempty covariance-regular locus, construct a smooth one-dimensional legal order-two fiber for (a,d), proving the least identifying order is three; also prove the full observed law retains a two-dimensional (b,c) fiber. Estimate (a,d) by feasible overidentified GMM on a compact sixth-Wasserstein regular subclass with quantitative chart, Jacobian and influence-covariance margins, and derive a uniformly valid sandwich ellipse. Explicitly distinguish Draisma-Kuhnt-Zwiernik, Jiang, Mesters-Zwiernik, Ribot-Seigal-Zwiernik and the banked general cumulant-transfer obstruction. Consumer: a prospective BayCausal/WIHS extension may report outer coefficients as robust under an independently justified overlapping-cycle/path-dependence motif while leaving central coefficients as a sensitivity fiber; do not claim its published disjoint-cycle theorem already covers this motif. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The residual covariance equation eliminates delta as t(alpha)/l(alpha); substituting into F21 and F12 gives two observable cubics P and Q. On the nonzero chart, their first subresultant is linear, yielding a=-s0/s1 and d=t(a)/l(a). Exact expansion verifies the legal exponential-source witness, all chart factors, the singleton residual ideal, a rank-two Jacobian, 100 fresh rational perturbations, and a nonlinear-middle stress case. A five-source construction realizes every nearby positive-definite path covariance with independent non-Gaussian endpoints, producing a one-dimensional order-two query fiber; an explicit residual shear preserves a two-dimensional full-law central-coefficient fiber. Literature checks found no query-specific cyclic order-three inverse. UNRESOLVED BOTTLENECK: Prove uniform asymptotic linearity of feasible optimally weighted GMM on the stated compact sixth-moment class, including centered third-cumulant influence functions, covariance estimation, separation, and margin diagnostics. EARLY KILL TEST: Implement the fixed cubic subresultant using only observed tensors with the true mechanism hidden; reproduce both witness families and exact covariance twins on a rational neighborhood. Stop if a nontrue common root survives with D nonzero, specialization fails, or the covariance realization leaves the legal model. STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/eid_cyclic_residual_order3_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** REJECT

**Banking reason.** D0.5.G tier=incremental < floor=field and projected paper_score_ceiling 6.1 < 7.4; not salvageable in scope without a new generic D!=0 theorem and headline re-anchor.

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
