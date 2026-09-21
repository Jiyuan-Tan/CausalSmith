# Substrate requirement: martingale-array-clt

## Goal
Provide a reusable scalar central limit theorem for square-integrable martingale-difference triangular arrays under predictable-variance normalization and a Lindeberg condition.

## Provides (API contract)
- `martingaleArrayCLT`: for a real-valued row-wise martingale-difference triangular array, convergence of the row predictable quadratic variation to one in probability plus the conditional Lindeberg condition implies convergence in distribution of the row sum to the standard normal law.
- Supporting declarations should expose the minimum reusable bridges needed to instantiate the theorem from bounded fourth moments and deterministic/predictable variance convergence, without assuming independence of increments.

## Statement / milestones
For each row n, let `(X n k)` be real-valued, adapted to a filtration `(F n k)`, square-integrable, and satisfy `E[X n k | F n (k-1)] = 0`. If the sum over k of `E[(X n k)^2 | F n (k-1)]` converges in probability to 1, and for every ε > 0 the sum over k of `E[(X n k)^2 1{|X n k| > ε} | F n (k-1)]` converges in probability to 0, then the sum over k of `X n k` converges in distribution to `N(0,1)`. Finite row lengths may vary with n. Include a corollary deriving conditional Lindeberg from a uniform vanishing fourth-moment sum or another comparably reusable Lyapunov condition if this can be proved without strengthening the main theorem.

## Standard reference
Li and Zhao (2026), arXiv:2602.21998, Appendix lemma `martingale_clt`; standard martingale triangular-array CLTs in Hall and Heyde, *Martingale Limit Theory and Its Application*.

## Intended reuse
The immediate consumer is `thm:joint-design-clt` in `exp_multigroup_studentized_srsb_joint_inference`, followed by a finite-dimensional Cramér–Wold lift and simultaneous Wald coverage. The substrate must remain independent of that experiment, its group/block types, and all research-run modules; it should apply to general scalar finite-row martingale arrays, including singular downstream vector covariance handled after scalar projection.

## May assume / must derive
May assume standard measure-theoretic probability objects already available in Mathlib/Causalean, including conditional expectation, filtrations, convergence in probability/distribution, and the standard normal law. Must derive the CLT conclusion from the martingale-difference, predictable-variance, and Lindeberg hypotheses without introducing a new axiom, `sorry`, an opaque theorem assumption, or an independence hypothesis. Paper-specific centering, moment bounds, covariance stabilization, and Cramér–Wold calculations are not part of this substrate.

## Non-goals (optional)
Do not formalize sequential rerandomization, Horvitz–Thompson estimators, vector-valued martingale CLTs, stable convergence, rates, Berry–Esseen bounds, or functional invariance principles.

## Known building blocks (optional)
Reuse Mathlib martingale/conditional-expectation infrastructure and Causalean's existing convergence-in-distribution and multivariate Cramér–Wold interfaces where appropriate. Existing independent-summand or dependency-graph CLTs may be reused only if their hypotheses are actually derived; they may not replace the martingale theorem with an independence assumption.
