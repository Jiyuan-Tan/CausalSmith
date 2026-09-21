# Substrate requirement: common-design-marked-laws

## Goal
Build reusable probability calculus for common-design marked observations: conditional-mean-zero weighted sums under finite product laws and chi-squared divergence disintegration through a shared design marginal.

## Provides (API contract)
- `condExp_eq_of_integral_preimage_eq`: identify a conditional expectation from equality of integrals over every measurable design preimage.
- `product_weighted_centered_l1_le`: for a finite i.i.d. product of bounded marked observations with design-conditional mean m, bound the expected absolute value of a design-measurable weighted centered sum by one half times the square root of the expected sum of squared weights.
- `attachKernel` and `one_add_chiSqDiv_attachKernel`: construct a retained-design marked law from a common base and a probability kernel, and express one plus chi-squared divergence as the base integral of the conditional one-plus-chi-squared divergences.
- `chiSqDiv_map_measurableEquiv` and `chiSqDiv_twoPointMean_centerHalf`: invariance under measurable equivalence and the explicit centered Bernoulli/two-point chi-squared formula needed to instantiate the kernel theorem.

## Statement / milestones
1. Let design : Omega -> D be measurable under a probability measure mu. If integrable Y and m have equal integrals on `design ⁻¹ S` for every measurable S and m is measurable with respect to the comap sigma-algebra, prove `mu[Y | comap design] =ᵐ m`. State the exact integrability/measurability hypotheses required by Mathlib conditional expectation uniqueness.
2. For P on observations Omega, measurable design D, bounded outcome Y in [0,1], and a measurable design regression mD with `condExp Y given D = mD ∘ D`, prove under `Measure.pi (fun _ : Fin N => P)` that every suitably measurable design-vector-dependent weight array w satisfies `integral z, |sum i, w (D ∘ z) i * (Y (z i) - mD (D (z i)))| <= (1/2) * sqrt (integral z, sum i, (w (D ∘ z) i)^2)`. The scaffolder may expose natural integrability or bounded-weight premises. Derive vanishing cross terms from product independence/conditional centering and the 1/4 conditional variance bound from Y in [0,1].
3. For a probability base measure m and measurable probability kernels kappa, eta with pointwise absolute continuity and the required finite/integrability hypotheses, define the law retaining x and drawing mark y from the kernel. Prove `1 + chiSqDiv (attachKernel m kappa) (attachKernel m eta) = integral x, (1 + chiSqDiv (kappa x) (eta x)) dm`. Provide inequality variants if they remove avoidable finiteness premises.
4. Prove chiSqDiv invariance under a measurable equivalence and evaluate the two-point/Bernoulli mark law centered at 1/2: for |u| < 1/2, `chiSqDiv (twoPointMean (1/2+u)) (twoPointMean (1/2)) = 4*u^2` (or the orientation/algebraically equivalent formula compatible with the existing Bernoulli law). Ensure the result composes with `one_add_chiSqDiv_pi_iid_general`.

## Standard reference
Milestone 1 is the standard uniqueness characterization of conditional expectation by integrals over the conditioning sigma-algebra. Milestone 2 is the conditional-mean-zero weighted-sum variance identity plus Cauchy-Schwarz and the Bernoulli-range variance bound 1/4. Milestone 3 is the Radon-Nikodym/Fubini disintegration identity for order-2 Renyi or chi-squared divergence of two marked laws sharing their base marginal; milestone 4 is its elementary two-point specialization. These are standard probability and information-theory facts, not paper-specific causal claims.

## Intended reuse
The immediate consumer is `CausalSmith.Stat.LmtpThresholdAtomFrontier.clamp_minimax_risk`. The weighted-sum result controls the total-Gram estimator noise for arbitrary model laws from the model set-integral regression tie. The kernel chi-squared result controls explicit global and localized Bernoulli regression alternatives sharing a polynomial-thinning design and then tensorizes over n observations. The APIs should also apply to random-design regression and marked-law lower bounds outside this paper.

## May assume / must derive
May assume probability measures, measurability, explicit integrability/boundedness, pointwise kernel probability, kernel absolute continuity, and any clearly stated finiteness condition needed for exact chi-squared equality. Must derive conditional expectation from measurable-set integral identities, the disappearance of cross terms under the product law, the 1/4 variance factor for [0,1] outcomes, the retained-base kernel divergence formula, measurable-equivalence invariance, and the two-point formula. Do not assume the desired risk bound or divergence identity as a premise.

## Non-goals (optional)
Do not construct ClampLaw witnesses, prove Holder/Taylor membership, calculate threshold separations, analyze bandwidths, manipulate sInf/sSup minimax definitions, or prove the final research theorem. No research module may be imported.

## Known building blocks (optional)
Proposed imports: `Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic`, `Mathlib.MeasureTheory.Measure.GiryMonad`, `Causalean.Mathlib.MeasureTheory.IntegralBind`, `Causalean.Stat.Minimax.ChiSquared`, `Causalean.Stat.Minimax.MarkovKernelTransport`, and finite-product independence/integration APIs. Existing `one_add_chiSqDiv_pi_iid_general` handles the later iid tensorization but not shared-base kernel disintegration. Existing conditional-expectation APIs provide uniqueness primitives but no design-dependent weighted finite-product L1 theorem. Research-folder prerequisites already built and axiom-clean are `Helpers/MinimaxBump.lean`, `Helpers/MinimaxWitness.lean`, and `Helpers/MinimaxLaw.lean`; the study must not import them. After promotion, the paper must still extend HolderRegression rectangle ties to the design sigma-algebra, certify the explicit laws and smooth bump, instantiate the generic results, evaluate separations/bandwidth bounds, and assemble the minimax order sandwich.
