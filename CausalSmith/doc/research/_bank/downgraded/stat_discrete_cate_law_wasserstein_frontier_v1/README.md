---
qid: stat_discrete_cate_law_wasserstein_frontier
spec: v1
topic: "Sharp all-regime recovery of the population CATE law with unrestricted high-dimensional discrete confounders. Observe n iid (X,A,Y), X in [d], binary A and Y, under consistency, conditional exchangeability, and known fixed overlap epsilon in (0,1/2). Cell masses are arbitrary and unknown; propensities and both outcome regressions are unknown, with no smoothness, positive mass floor, effect separation, or exclusion of ties. The target G_P=sum_{x:p_x>0} p_x delta_(mu_1x-mu_0x) is the population law of conditional mean effects. Determine, up to epsilon-only constants and uniformly over n>=1,d>=2, inf_Ghat sup_P E[W1(Ghat,G_P)^2]. Construct one explicit computable probability-valued estimator and a matching all-estimator converse, deriving consistency and parametric-risk boundaries; leave the exact rate open. The full sparse-to-dense frontier is the kernel: a dense-regime theorem alone, a scalar-functional collection, or a one-sided bound is insufficient. Novelty must survive Vinayak-Kong-Kakade paired-binomial change-law estimation and Lee-Bacak-Kennedy fixed heterogeneous trial counts by handling unknown mass-weighted observational sampling. Consumer: categorical-profile CATE-distribution analyses motivated by Mizuguchi-Sawamura's dexamethasone/PONV study. This does not identify individual potential-outcome differences or validate zero-atom claims from W1 alone. Delegate estimator algebra and tuning, retaining the original law class. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A separated-atom hypercube keeps the observed experiments close while moving the CATE law in Wasserstein distance. Together with a total cellwise plug-in construction, the presolve reports a matching risk of order d/n when n is at least d cubed, on the original unrestricted model. An independently checked eight-cell instance has positive probabilities, exact neighboring transport cost 1/512, and n-sample KL approximately 0.063. This shows why the scalar optimal-value rate cannot simply be transplanted. A mass-weighted Lipschitz extension and a deterministic positive grouped moment-reconstruction certificate provide a route beyond this regime. Paired-binomial law recovery and fixed heterogeneous trial-count estimation are existing precedents; grouping alone is not novelty. These derivations and comparisons require independent verification.\nUNRESOLVED BOTTLENECK: Control and optimize the joint moment-estimation process uniformly over all Lipschitz test functions under arbitrary unknown cell masses and propensities, and prove a matching converse in the remaining sample-size/category regimes. The dense result alone does not complete the promised paper.\nEARLY KILL TEST: Test the proposed joint reconstruction certificate, with exact factorial covariances, on the explicit separated-atom hypercube and on two effect clusters with unknown unequal masses and propensities at both overlap boundaries. It must respect the d/n dense lower bound and deliver a concrete nontrivial clustered bound without known-weight assumptions or discarded null cells; a contradictory scalar-rate certificate must be abandoned, and an affirmative exact-class generic collision or obstruction should stop or pivot the run.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_cate_law_wasserstein_frontier.md."
novelty_target: field
banked_novelty_tier: subfield
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "Exact sparse-to-dense minimax rate, computable probability-valued attaining estimator, and matching same-class converse remain open; the grouped reconstruction object is only a blueprint."
reusable: unknown
reraise_status: re-raise
gap_reasons:
  - "The proposal's full sparse-to-dense rho(n,d) frontier with a constructed probability-valued estimator and matching converse is still an explicit to-prove obligation; the delivered dense frontier and logarithmic bracket are a strictly weaker kernel."
  - "The grouped reconstruction procedure is merely a blueprint, so it supplies neither the promised improved estimator nor an achievable sparse-regime rate."
  - "The delivered dense theorem, coarse bracket, and parametric-risk boundary constitute a companion result rather than the field-level full-frontier contribution named in the brief."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_all_regime_bracket.tex
  - discovery/solve_thm_all_regime_bracket.json
  - reviews/review_math.json
  - reviews/review_rubric.json
  - reviews/review_general.json
seeds_burned: []
proof_attempt_summary: |
  Two D0 solve rounds established the dense d/n frontier, an all-regime factor-log(ed)
  bracket, a four-regime lower-benchmark phase diagram, and the bounded-category
  parametric-risk boundary. The grouped positive moment reconstruction could not be
  upgraded from a blueprint to a uniformly controlled probability-valued estimator,
  and no matching converse selected the exact sparse/transitional rate. The exact
  frontier therefore remains open; no Lean formalization was started.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 12230013
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 12230013
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_discrete_cate_law_wasserstein_frontier / v1 — Downgraded

**Topic.** Sharp all-regime recovery of the population CATE law with unrestricted high-dimensional discrete confounders. Observe n iid (X,A,Y), X in [d], binary A and Y, under consistency, conditional exchangeability, and known fixed overlap epsilon in (0,1/2). Cell masses are arbitrary and unknown; propensities and both outcome regressions are unknown, with no smoothness, positive mass floor, effect separation, or exclusion of ties. The target G_P=sum_{x:p_x>0} p_x delta_(mu_1x-mu_0x) is the population law of conditional mean effects. Determine, up to epsilon-only constants and uniformly over n>=1,d>=2, inf_Ghat sup_P E[W1(Ghat,G_P)^2]. Construct one explicit computable probability-valued estimator and a matching all-estimator converse, deriving consistency and parametric-risk boundaries; leave the exact rate open. The full sparse-to-dense frontier is the kernel: a dense-regime theorem alone, a scalar-functional collection, or a one-sided bound is insufficient. Novelty must survive Vinayak-Kong-Kakade paired-binomial change-law estimation and Lee-Bacak-Kennedy fixed heterogeneous trial counts by handling unknown mass-weighted observational sampling. Consumer: categorical-profile CATE-distribution analyses motivated by Mizuguchi-Sawamura's dexamethasone/PONV study. This does not identify individual potential-outcome differences or validate zero-atom claims from W1 alone. Delegate estimator algebra and tuning, retaining the original law class. PRESOLVE EVIDENCE REQUIRING VERIFICATION: A separated-atom hypercube keeps the observed experiments close while moving the CATE law in Wasserstein distance. Together with a total cellwise plug-in construction, the presolve reports a matching risk of order d/n when n is at least d cubed, on the original unrestricted model. An independently checked eight-cell instance has positive probabilities, exact neighboring transport cost 1/512, and n-sample KL approximately 0.063. This shows why the scalar optimal-value rate cannot simply be transplanted. A mass-weighted Lipschitz extension and a deterministic positive grouped moment-reconstruction certificate provide a route beyond this regime. Paired-binomial law recovery and fixed heterogeneous trial-count estimation are existing precedents; grouping alone is not novelty. These derivations and comparisons require independent verification.
UNRESOLVED BOTTLENECK: Control and optimize the joint moment-estimation process uniformly over all Lipschitz test functions under arbitrary unknown cell masses and propensities, and prove a matching converse in the remaining sample-size/category regimes. The dense result alone does not complete the promised paper.
EARLY KILL TEST: Test the proposed joint reconstruction certificate, with exact factorial covariances, on the explicit separated-atom hypercube and on two effect clusters with unknown unequal masses and propensities at both overlap boundaries. It must respect the d/n dense lower bound and deliver a concrete nontrivial clustered bound without known-weight assumptions or discarded null cells; a contradictory scalar-rate certificate must be abandoned, and an affirmative exact-class generic collision or obstruction should stop or pivot the run.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_discrete_cate_law_wasserstein_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposal's full sparse-to-dense frontier with a constructed probability-valued estimator and matching converse remains an explicit to-prove obligation; the delivered dense frontier and logarithmic bracket are a strictly weaker kernel.

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
