# Substrate requirement: parametric-rational-integral-analyticity

## Goal
Provide a reusable real-analyticity theorem for compactly supported one-parameter integrals whose integrand is a finite-degree polynomial in the parameter divided by an affine denominator.

Let `K` be compact, `μ` a finite measure supported on `K`, and let `d t x = (1 - t) * a x + t * b x`. Assume there is an open set `O : Set ℝ` on which `d t x` is uniformly bounded away from zero for `x ∈ K`. Let `P t x` be polynomial in `t` of fixed finite degree, with coefficient functions measurable and integrable (or uniformly bounded on `K`). Prove that `t ↦ ∫ x in K, P t x / d t x ∂μ` is `AnalyticOnNhd ℝ O`, or expose an equivalent pointwise API.

## Provides (API contract)
- A theorem accepting compact support or finite-measure plus uniform coefficient bounds.
- An affine-denominator specialization with an explicit uniform nonvanishing hypothesis on `O × K`.
- Closure under finite sums/products sufficient for vector-valued finite-coordinate applications, if available without materially enlarging the development.
- A local corollary: at any `t₀` where the affine denominator is uniformly nonzero on `K`, the integral is analytic in a neighborhood of `t₀`.

The exact binder order and auxiliary definitions may follow Mathlib conventions. A theorem stated via power-series representation is acceptable if accompanied by the `AnalyticAt`/`AnalyticOnNhd` corollary.

## Statement / milestones
1. Prove local uniform nonvanishing of an affine denominator from a supplied uniform lower bound on `O × K`.
2. Obtain a locally uniform geometric-series expansion for its reciprocal.
3. Multiply by the finite polynomial numerator and justify termwise integration under the finite measure.
4. Package the resulting power series as `AnalyticAt ℝ` and then `AnalyticOnNhd ℝ O`.
5. Verify a scalar compact-interval example.

## Standard reference
This is the standard theorem on parameter-dependent integrals of locally uniformly convergent analytic families, specialized to rational functions with poles uniformly separated from a compact integration domain. Standard references include differentiation/integration of power series and holomorphic/real-analytic parameter integrals in graduate real or complex analysis texts.

## Intended reuse
The immediate consumer is a paper-local affine perturbation whose contrast is an integral of a polynomial numerator divided by an affine density denominator. The result should remain general enough for other compactly supported parametric likelihood-ratio and moment integrals.

## May assume / must derive
May assume compactness of `K`, finiteness of `μ`, measurability/integrability or uniform bounds for the coefficient functions, openness of `O`, and an explicit uniform positive lower bound for the denominator on `O × K`.

Must derive analyticity of the integrated function from those primitives. It must not assume analyticity of the integral itself, termwise integration as an axiom, or any paper-specific separation conclusion.

## Known building blocks (optional)
- `Mathlib.Analysis.Analytic.Basic`
- `Mathlib.Analysis.Analytic.Constructions`
- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- compactness and finite-measure integration APIs
- geometric-series analyticity for reciprocal affine functions
- dominated convergence and termwise integration for locally uniformly summable power series

Search first for existing analytic-under-integral or locally uniform power-series integration results and reuse them where possible. No research-folder prerequisite needs extraction.

## Non-goals (optional)
- Do not import `CausalSmith.ExactID.*_Research` or mention causal graphs, mechanisms, interventions, contrast functions, MMD, or separation.
- Do not prove the paper's `analytic_edge_perturbation` or `generic_cover_separation` theorem.
- Do not construct the paper's positivity neighborhood or prove openness of its strata.
- Do not change any paper theorem statement or add assumptions.

The neutral study module must build with zero `sorry`, `admit`, errors, or nonstandard axioms. `#print axioms` for the primary theorem may report only standard Lean/Mathlib axioms. A small neutral scalar example should instantiate the result.
