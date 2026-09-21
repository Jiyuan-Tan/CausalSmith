---
qid: stat_semisupervised_discrete_ate_annotation_frontier
spec: v1
topic: "When unlabeled treatment records rescue causal estimation: the sharp annotation frontier. Fix known 0<epsilon<1/2. Observe n>=1 independent labeled records (X,A,Y) distributed as P and m>=0 independent unlabeled records (X,A) distributed as its SAME marginal P_XA, independent of the labeled sample. X is in the known alphabet [d], d>=2; A and Y are binary. All cell probabilities p_x>=0 summing to one are allowed, including null cells; epsilon<=e_x=P(A=1|X=x)<=1-epsilon on occupied cells; mu_ax=P(Y=1|A=a,X=x) is unrestricted in [0,1]. Neither p nor e is known. No smoothness, sparsity, effect homogeneity, outcome surrogacy, or minimum cell mass is assumed. Consistency and conditional exchangeability identify tau(P)=sum_x p_x(mu_1x-mu_0x). The target population is shared by both samples, and missing outcomes are by independent random labeling, not selected enrollment. Determine, up to constants depending only on epsilon, the minimax MSE R_epsilon(n,m,d)=inf_T sup_P E_(P^n x P_XA^m)[(T-tau(P))^2] over all measurable estimators, uniformly for n>=1,m>=0,d>=2. Exhibit a numerical rate r_epsilon(n,m,d) with no unspecified optimization over unknown laws, prove a total computable estimator attaining it and a matching lower bound in the same observation experiment for every regime. Derive necessary and sufficient growth conditions for R->0 and R=O(1/n) along arbitrary n->infinity sequences m_n,d_n. The sharp tradeoff must include the m=0 frontier, the finite-m transition, and the limiting known-propensity benchmark. Leave the exact rate formula open; do not obtain it by substituting n+m for n in the supervised rate. The new theorem is the unequal-information approximation/variance and indistinguishability frontier: outcome-bearing moments have n observations, while treatment/mass information has n+m. Consumer: Cheng, Ananthakrishnan and Cai, Biometrics 2021, Robust and efficient semi-supervised estimation of average treatment effects with application to electronic health records data, Sections 2.1 and 4 (https://pmc.ncbi.nlm.nih.gov/articles/PMC7758040/). Their IBD comparative-effectiveness study observes treatment/covariates in all records but validates outcomes through random chart review. The frontier supplies a baseline-only discrete-adjustment benchmark for choosing additional chart labels versus acquiring treatment-covariate records when working nuisance models are not trusted. It does not claim efficiency with their post-treatment surrogates or validate that data set under an unrestricted discrete model. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived an inverse-count baseline and a mixed Chebyshev approximation linear in outcome-bearing masses, allowing one labeled factor and many treatment-only factorial factors. A signed prior preserves the entire marginal distribution of cell masses and propensities while changing conditional outcome marks; auxiliary-only observations then agree exactly, and the joint likelihood discrepancy requires labeled observations. Symbolic polynomial identities, ten finite-atom priors and nine joint-likelihood checks passed. The suggested rate min{1,1/n+[d/((n+m)log(en))]^2} remains conjectural; the original problem stays answer-open. Known-propensity, m=0, d=2, null-cell and large-m boundaries were checked, without claiming the complete theorem.\nUNRESOLVED BOTTLENECK: Prove the Section 4 uniform hybrid-risk lemma, including false-light polynomial tails, branch-mean variance and mass-weighted summation without dimension or m/n leakage. The lower-prior normalization, fixed-sample transfers and every G1-G8 gap also require independent proof.\nEARLY KILL TEST: At epsilon=1/4 check both sides of the pilot threshold and whether exponential count tails absorb outside-region polynomial growth uniformly. Recheck the joint-prior likelihood and normalization cost. If these fail, restart the answer derivation within the original model rather than asserting the proposed rate or substituting a weaker theorem.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_semisupervised_discrete_ate_annotation_frontier.md."
novelty_target: field
banked_novelty_tier: field
tier_at_proposal: ACCEPT
tier_at_derivation: PASS
proposal_promise_gap: null
reusable: unknown
reraise_status: unknown
gap_reasons: []
reusable_artifacts:
  - Causalean.Mathlib.Probability.PilotSelection
  - Causalean.Mathlib.Probability.Poisson.InverseMoments
  - Causalean.Mathlib.Probability.Poisson.Moments
  - Causalean.Stat.Concentration.Poisson.Threshold
  - Causalean.Stat.Minimax.FiniteSideInformation
  - Causalean.Stat.Minimax.FiniteSideInformation.Measurable
  - Causalean.Mathlib.Probability.PoissonAddOnePoincare
  - Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix
  - Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
  - Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer
seeds_burned: []
proof_attempt_summary: |
  The run proved the sharp semisupervised annotation frontier by combining a hybrid
  polynomial estimator upper bound with a common-marginal fuzzy-prior converse.
  Three reusable Poisson-prefix/Rao--Blackwell transfers and finite-side-information
  minimax infrastructure were built along the way; the final Lean development has no
  remaining proof debt or added assumptions.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 430799131
  pipeline_claude_tokens: 22954356
  pipeline_tokens_consumed: 453753487
  total_tokens_consumed: null
banked_on: "2026-09-16"
paper_score: 7.2
paper_score_rationale: "The paper delivers a significant sharp minimax result with faithful formal statements, but its publication case is weakened by an unstated load-bearing lower-bound input, proof-led organization, and several misleading presentation choices."
---

# stat_semisupervised_discrete_ate_annotation_frontier / v1 — Accepted

**Topic.** When unlabeled treatment records rescue causal estimation: the sharp annotation frontier. Fix known 0<epsilon<1/2. Observe n>=1 independent labeled records (X,A,Y) distributed as P and m>=0 independent unlabeled records (X,A) distributed as its SAME marginal P_XA, independent of the labeled sample. X is in the known alphabet [d], d>=2; A and Y are binary. All cell probabilities p_x>=0 summing to one are allowed, including null cells; epsilon<=e_x=P(A=1|X=x)<=1-epsilon on occupied cells; mu_ax=P(Y=1|A=a,X=x) is unrestricted in [0,1]. Neither p nor e is known. No smoothness, sparsity, effect homogeneity, outcome surrogacy, or minimum cell mass is assumed. Consistency and conditional exchangeability identify tau(P)=sum_x p_x(mu_1x-mu_0x). The target population is shared by both samples, and missing outcomes are by independent random labeling, not selected enrollment. Determine, up to constants depending only on epsilon, the minimax MSE R_epsilon(n,m,d)=inf_T sup_P E_(P^n x P_XA^m)[(T-tau(P))^2] over all measurable estimators, uniformly for n>=1,m>=0,d>=2. Exhibit a numerical rate r_epsilon(n,m,d) with no unspecified optimization over unknown laws, prove a total computable estimator attaining it and a matching lower bound in the same observation experiment for every regime. Derive necessary and sufficient growth conditions for R->0 and R=O(1/n) along arbitrary n->infinity sequences m_n,d_n. The sharp tradeoff must include the m=0 frontier, the finite-m transition, and the limiting known-propensity benchmark. Leave the exact rate formula open; do not obtain it by substituting n+m for n in the supervised rate. The new theorem is the unequal-information approximation/variance and indistinguishability frontier: outcome-bearing moments have n observations, while treatment/mass information has n+m. Consumer: Cheng, Ananthakrishnan and Cai, Biometrics 2021, Robust and efficient semi-supervised estimation of average treatment effects with application to electronic health records data, Sections 2.1 and 4 (https://pmc.ncbi.nlm.nih.gov/articles/PMC7758040/). Their IBD comparative-effectiveness study observes treatment/covariates in all records but validates outcomes through random chart review. The frontier supplies a baseline-only discrete-adjustment benchmark for choosing additional chart labels versus acquiring treatment-covariate records when working nuisance models are not trusted. It does not claim efficiency with their post-treatment surrogates or validate that data set under an unrestricted discrete model. PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derived an inverse-count baseline and a mixed Chebyshev approximation linear in outcome-bearing masses, allowing one labeled factor and many treatment-only factorial factors. A signed prior preserves the entire marginal distribution of cell masses and propensities while changing conditional outcome marks; auxiliary-only observations then agree exactly, and the joint likelihood discrepancy requires labeled observations. Symbolic polynomial identities, ten finite-atom priors and nine joint-likelihood checks passed. The suggested rate min{1,1/n+[d/((n+m)log(en))]^2} remains conjectural; the original problem stays answer-open. Known-propensity, m=0, d=2, null-cell and large-m boundaries were checked, without claiming the complete theorem.
UNRESOLVED BOTTLENECK: Prove the Section 4 uniform hybrid-risk lemma, including false-light polynomial tails, branch-mean variance and mass-weighted summation without dimension or m/n leakage. The lower-prior normalization, fixed-sample transfers and every G1-G8 gap also require independent proof.
EARLY KILL TEST: At epsilon=1/4 check both sides of the pilot threshold and whether exponential count tails absorb outside-region polynomial growth uniformly. Recheck the joint-prior likelihood and normalization cost. If these fail, restart the answer derivation within the original model rather than asserting the proposed rate or substituting a weaker theorem.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_semisupervised_discrete_ate_annotation_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** PASS

**Banking reason.** CKPT 2 supervisor approved the clean field-tier F5 result with zero proof debt and axiom-clean headline/support theorems.

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
