# Substrate requirement: asymptotic LAN and scalar convolution bound

## Goal
Build reusable Lean infrastructure connecting finite-dimensional i.i.d. quadratic-mean differentiability to local asymptotic normality, and LAN regularity plus a canonical gradient to the scalar convolution/variance lower bound.

## Provides (API contract)
- A general local-experiment / log-likelihood-ratio object sufficient to state LAN for finite-dimensional parameter directions.
- `iidDQM_implies_LAN` (name may be adapted to library conventions): an i.i.d. quadratic-mean differentiable family with square-integrable score has the LAN log-likelihood-ratio expansion and information matrix given by the score second moment.
- `regular_convolution_limit` (name may be adapted): in a finite-dimensional LAN experiment, a scalar estimator regular under local alternatives and a pathwise-differentiable scalar target with canonical-gradient pairing has a weak limit equal to the efficient centered Gaussian convolved with a residual law.
- `regular_asymptoticVariance_ge_gradientNormSq` (name may be adapted): whenever that regular limit has a finite variance, its variance is at least the squared L2 norm of the canonical gradient.

## Statement / milestones
1. Define the smallest general interface for a sequence of local experiments, likelihood ratios, weak convergence, and LAN. It must not mention RMST, survival analysis, or a paper-run type.
2. From a finite-dimensional i.i.d. DQM expansion with score `s : Ω → ℝ^k`, prove the local log-likelihood ratio at `h / sqrt n` is the score sum minus `1/2 * hᵀ I h` plus an `o_P(1)` remainder, with `I = E[s sᵀ]`.
3. State and prove the scalar convolution theorem at the level actually needed by downstream papers: LAN, regularity under each fixed local direction, and canonical-gradient representation imply that every estimator limit factors as `N(0, ‖D‖₂²) * R` for some residual probability law `R`.
4. Derive the finite-variance lower bound `Var(limit) ≥ ‖D‖₂²` as a separate easy-to-instantiate theorem.
5. Supply compatibility lemmas that let a paper's own finite collection of DQM submodels and tangent-density proof instantiate the generic results without redefining the asymptotic framework.

The study may choose an equivalent characteristic-function, probability-kernel, or distributional formulation if that is the narrowest sound Lean API. All declarations must be axiom-clean and contain no `sorry`.

## Standard reference
van der Vaart, *Asymptotic Statistics* (1998), Theorem 7.2 (DQM of an i.i.d. parametric model implies LAN) and Theorem 25.20 (Convolution Theorem), scalar specialization.

## Intended reuse
Immediate consumer: `stat_rmst_endpoint_weighted_efficiency/v1`, nodes `lem:iid-dqm-implies-lan`, `lem:semiparametric-convolution-bound`, `thm:canonical-gradient-efficiency`, and `thm:uniform-endpoint-efficiency`. Future semiparametric-efficiency papers should be able to reuse the same API. The consumer will prove its own smooth in-class submodels, DQM expansions, tangent density, score continuity, and estimator regularity.

## May assume / must derive
May assume standard measure-theoretic regularity explicitly represented in the API: domination, measurability, square-integrability, normalization, nonsingularity when required, tightness/existence of the stated weak limits, and the paper-supplied DQM and regularity hypotheses.

Must derive the LAN implication from the DQM interface, the Gaussian convolution factorization from the LAN/regularity/canonical-gradient interface, and the variance inequality from that factorization. Do not assume the desired convolution or variance conclusion under another name.

## Non-goals (optional)
Do not formalize RMST, censoring/event martingales, the RMST paper's four smooth submodel families, or its tangent-density argument. Do not weaken the result to Hilbert-space projection geometry alone: the downstream citation requires estimator weak-limit convolution and its variance corollary. Do not introduce paper-named declarations or import any `CausalSmith.*_Research` module.

## Known building blocks (optional)
`Causalean.Estimation.Efficiency.PathwiseGradient.RegularSubmodel` and `Causalean.Estimation.Efficiency.TangentProjection` provide path/gradient and Hilbert projection geometry; `TangentProjection.effBound_le_normSq` is useful but does not itself give the estimator-limit convolution result. Reuse Mathlib probability/distribution/CLT and characteristic-function infrastructure where suitable.
