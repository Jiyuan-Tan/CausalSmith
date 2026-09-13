---
qid: stat_corrupted_ate_overlap_nuisance_frontier
spec: v1
topic: "The statistical price of corrupted records under weak causal overlap. Fix d>=1, alpha,beta,kappa>0, L>=4. Clean observations O=(X,A,Y) lie in [0,1]^d x {0,1} x [0,1]. Under P, X is exactly uniform, e(x)=P(A=1|X=x)=x_1^kappa u(x), u in H^alpha(L) with 1/4<=u<=1/2, and mu_a(x)=E[Y|X=x,A=a] in H^beta(L) with 1/4<=mu_a<=3/4. Conditional outcome laws otherwise unrestricted. H^s(L) bounds all partial derivatives through m=ceil(s)-1 by L and order-m derivatives have (s-m)-Holder seminorm <=L under sup norm. At the boundary x_1=0, mu_1 is its unique continuous extension, not an independently identified conditional value. Clean consistency and conditional exchangeability identify theta(P)=integral_[0,1]^d (mu_1-mu_0) dx. Observe n>=2 iid records from R=(1-epsilon)P+epsilon Q, with known 0<=epsilon<=1/10 and Q any probability law on the same record space; Q may corrupt all three fields. Estimator knows d,alpha,beta,kappa,L,epsilon and clean covariate design, but not P,Q,u,mu_a. Fixed nonzero epsilon entails irreducible ambiguity; do not claim point identification of theta from R. For every fixed d,alpha,beta,kappa,L above and jointly for all n>=2 and 0<=epsilon<=1/10, determine an explicit deterministic evaluable rate rho(n,epsilon;d,alpha,beta,kappa,L), including logarithms at regime boundaries, such that c*rho <= inf_T sup_(P,Q) E_((1-epsilon)P+epsilon Q)^n |T-theta(P)| <= C*rho, over all Borel data-only estimators and exactly the declared clean-law/contamination class. Constants c,C may depend on the fixed class parameters but not n,epsilon. Supply a total finite computable attaining estimator with stated computation, and matching same-experiment converses. Derive the joint clean-functional, overlap and contamination transitions from primitives; resolve whether clean risk and the ATE total-variation modulus can be attained simultaneously or whether nuisance learning incurs an additional interaction penalty. Neither the max formula, an interaction, nor an exponent is assumed. A whole-law TV estimation bound, oracle known-nuisance rate, one-point contamination modulus or unmatched clipping bound alone does not discharge the kernel. Consumer: Sasaki and Ura (2022), Average treatment effect estimates robust to the limited overlap problem: robustate, Stata Journal, and its right-heart-catheterization analysis. The result separates robustness to limited overlap from robustness to corrupted records and provides an error-radius and trimming/boundary-correction benchmark when a fraction of records is unreliable. This is a theoretical benchmark on a known-design boundary class, not a claim that the published parametric-propensity workflow satisfies this class or that its actual data are corrupted. https://journals.sagepub.com/doi/10.1177/1536867X221106402 PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derives the clean-ATE total-variation modulus delta^((beta+1)/(beta+kappa+1)), including changing propensity. On the full d=1, alpha=beta=1, kappa=2 class, unknown-nuisance cell means with variable widths and boundary extrapolation give the matched candidate rate n^(-2/5)+sqrt(epsilon). The draft supplies population bias, arbitrary full-record contamination, random-denominator and empty-cell arguments; exact witness and dyadic calculations were checked. These are unverified derivations, not the general theorem. A projected nuisance-product identity isolates the potential fast-functional gain, but naive pair correction incurs an explicit epsilon^2 times kernel-diagonal bias under concentrated contamination. Current comparisons did not identify a full-frontier collision; a 2024 robust-functional conference talk remains a literature lead to resolve.\nUNRESOLVED BOTTLENECK: Construct a finite robust projected correction with nuisance pilots and Gram matrix learned from corrupted records at resolutions above stable local occupancy, or prove a matching interaction penalty; complete the same-class converse and transition logarithms.\nEARLY KILL TEST: Test the proposed correction on the exact finite-cell slab with a point contaminant and then diffuse contamination within one fine cell. Without a proved bound preserving the clean high-resolution gain or a matched interaction lower bound, abandon that estimator route. The solved Lipschitz regime must remain a consistency check.\nSTRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_corrupted_ate_overlap_nuisance_frontier.md."
novelty_target: field
banked_novelty_tier: unknown
tier_at_proposal: ACCEPT
tier_at_derivation: NA
proposal_promise_gap: "The frozen all-parameter robust ATE frontier, including higher-dimensional nuisance interactions and equality-surface logarithms, was replaced by a sound one-dimensional beta=1 alpha>=1 slice."
reusable: unknown
reraise_status: true-negative
gap_reasons:
  - "The proposal promised an explicit matched frontier on every declared (d, alpha, beta, kappa) class, but the derived contribution is limited to d=1, beta=1, alpha>=1 and leaves all other coordinates as this open question."
  - "The unresolved coordinates are d>1, beta!=1, or alpha<1, including their interactions and every logarithm on the remaining equality surfaces."
reusable_artifacts:
  - discovery/core.json
  - discovery/writeup.tex
  - discovery/solve_thm_ate_tv_modulus.json
  - discovery/solve_thm_lipschitz_calibration.json
  - discovery/solve_lem_lipschitz_lower_pair.json
seeds_burned: []
proof_attempt_summary: |
  The run derived and referee-checked a finite dyadic estimator with matching clean and Huber-collision lower bounds for d=1, beta=1, alpha>=1 and every kappa>0, including the kappa=1 logarithmic elbow. It also retained a general ATE total-variation modulus and projected-bias identity. The frozen kernel nevertheless required the explicit matched frontier for every d, alpha, beta, and kappa; robust high-resolution nuisance/Gram estimation, matching converses, interactions, and equality-surface logarithms remain unproved, so D0.5 classified the narrowed result as kernel substitution.
token_usage:
  complete: false
  orchestrator_tokens: null
  pipeline_codex_tokens: 27453433
  pipeline_claude_tokens: 0
  pipeline_tokens_consumed: 27453433
  total_tokens_consumed: null
banked_on: "2026-09-09"
---

# stat_corrupted_ate_overlap_nuisance_frontier / v1 — Failed

**Topic.** The statistical price of corrupted records under weak causal overlap. Fix d>=1, alpha,beta,kappa>0, L>=4. Clean observations O=(X,A,Y) lie in [0,1]^d x {0,1} x [0,1]. Under P, X is exactly uniform, e(x)=P(A=1|X=x)=x_1^kappa u(x), u in H^alpha(L) with 1/4<=u<=1/2, and mu_a(x)=E[Y|X=x,A=a] in H^beta(L) with 1/4<=mu_a<=3/4. Conditional outcome laws otherwise unrestricted. H^s(L) bounds all partial derivatives through m=ceil(s)-1 by L and order-m derivatives have (s-m)-Holder seminorm <=L under sup norm. At the boundary x_1=0, mu_1 is its unique continuous extension, not an independently identified conditional value. Clean consistency and conditional exchangeability identify theta(P)=integral_[0,1]^d (mu_1-mu_0) dx. Observe n>=2 iid records from R=(1-epsilon)P+epsilon Q, with known 0<=epsilon<=1/10 and Q any probability law on the same record space; Q may corrupt all three fields. Estimator knows d,alpha,beta,kappa,L,epsilon and clean covariate design, but not P,Q,u,mu_a. Fixed nonzero epsilon entails irreducible ambiguity; do not claim point identification of theta from R. For every fixed d,alpha,beta,kappa,L above and jointly for all n>=2 and 0<=epsilon<=1/10, determine an explicit deterministic evaluable rate rho(n,epsilon;d,alpha,beta,kappa,L), including logarithms at regime boundaries, such that c*rho <= inf_T sup_(P,Q) E_((1-epsilon)P+epsilon Q)^n |T-theta(P)| <= C*rho, over all Borel data-only estimators and exactly the declared clean-law/contamination class. Constants c,C may depend on the fixed class parameters but not n,epsilon. Supply a total finite computable attaining estimator with stated computation, and matching same-experiment converses. Derive the joint clean-functional, overlap and contamination transitions from primitives; resolve whether clean risk and the ATE total-variation modulus can be attained simultaneously or whether nuisance learning incurs an additional interaction penalty. Neither the max formula, an interaction, nor an exponent is assumed. A whole-law TV estimation bound, oracle known-nuisance rate, one-point contamination modulus or unmatched clipping bound alone does not discharge the kernel. Consumer: Sasaki and Ura (2022), Average treatment effect estimates robust to the limited overlap problem: robustate, Stata Journal, and its right-heart-catheterization analysis. The result separates robustness to limited overlap from robustness to corrupted records and provides an error-radius and trimming/boundary-correction benchmark when a fraction of records is unreliable. This is a theoretical benchmark on a known-design boundary class, not a claim that the published parametric-propensity workflow satisfies this class or that its actual data are corrupted. https://journals.sagepub.com/doi/10.1177/1536867X221106402 PRESOLVE EVIDENCE REQUIRING VERIFICATION: The presolve derives the clean-ATE total-variation modulus delta^((beta+1)/(beta+kappa+1)), including changing propensity. On the full d=1, alpha=beta=1, kappa=2 class, unknown-nuisance cell means with variable widths and boundary extrapolation give the matched candidate rate n^(-2/5)+sqrt(epsilon). The draft supplies population bias, arbitrary full-record contamination, random-denominator and empty-cell arguments; exact witness and dyadic calculations were checked. These are unverified derivations, not the general theorem. A projected nuisance-product identity isolates the potential fast-functional gain, but naive pair correction incurs an explicit epsilon^2 times kernel-diagonal bias under concentrated contamination. Current comparisons did not identify a full-frontier collision; a 2024 robust-functional conference talk remains a literature lead to resolve.
UNRESOLVED BOTTLENECK: Construct a finite robust projected correction with nuisance pilots and Gram matrix learned from corrupted records at resolutions above stable local occupancy, or prove a matching interaction penalty; complete the same-class converse and transition logarithms.
EARLY KILL TEST: Test the proposed correction on the exact finite-cell slab with a point contaminant and then diffuse contamination within one fine cell. Without a proved bound preserving the clean high-resolution gain or a matched interaction lower bound, abandon that estimator route. The solved Lipschitz regime must remain a consistency check.
STRONGEST-FORM DRAFT (unverified, gaps listed inside): <repo-root>/internal/presolve_drafts/stat_corrupted_ate_overlap_nuisance_frontier.md.

**Novelty target.** field

**Stage -0.5 verdict.** ACCEPT

**Stage 0.5 verdict.** NA

**Banking reason.** The proposal promised an explicit matched frontier on every declared (d, alpha, beta, kappa) class, but the derived contribution is limited to d=1, beta=1, alpha>=1 and leaves all other coordinates open.

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
