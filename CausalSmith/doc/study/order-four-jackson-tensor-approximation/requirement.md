# Substrate requirement: order-four Jackson tensor approximation

## Goal
Build a reusable, paper-neutral Lean package for the normalized fourth-power Jackson kernel, its quantitative first- and second-moment bounds, finite tensor convolution, extraction as algebraic polynomials, and a dimension-four coefficient envelope.

## Provides (API contract)
The promoted package should expose a coherent public API equivalent to the following; exact names may change to fit Causalean conventions.

- A one-dimensional raw order-four Jackson kernel, its normalizing constant, and the normalized kernel, parameterized by a positive integer order `K`.
- Continuity, measurability/integrability, nonnegativity, evenness, and unit-mass facts for the normalized kernel on a standard period interval.
- A cosine/trigonometric degree bound of order `2 * (K - 1)` for that kernel.
- Quantitative normalized moment estimates with universal constants: `integral |t| J_K(t) dt <= C₁ / K` and `integral t^2 J_K(t) dt <= C₂ / K^2`.
- A converse representation theorem turning a finite even trigonometric polynomial into an ordinary real polynomial in `cos t`, with a usable degree bound and evaluation identity.
- A finite-dimensional tensor-product version, including extraction to `MvPolynomial` and an evaluation identity after the cosine/affine coordinate change.
- Tensor convolution/Fubini lemmas for continuous or bounded measurable functions on a product period box, including positivity, preservation of constants, and the local Lipschitz approximation estimate obtained from the first moments.
- Affine center/radius reparameterization from a rectangle to normalized coordinates, with explicit hypotheses preventing division by zero.
- For fixed dimension four, a coefficient `l1`-norm envelope for the extracted algebraic polynomial of the form `C * A^K` (or a stronger explicit exponential bound) when the convolved function is uniformly bounded. The constants must be universal and the result must expose the degree/support bound needed by downstream multinomial estimation.

## Statement / milestones
1. Define the raw periodic kernel `jraw K t = (sin (K*t/2) / sin (t/2))^4`, with the removable singularities handled explicitly, and prove the facts needed to integrate it on `[-pi, pi]`.

2. Prove the raw mass has order `K^3`: there are universal positive constants bounding its integral above and below by constant multiples of `K^3`. Normalize by this mass and prove nonnegativity, evenness, continuity/integrability, and unit mass.

3. Prove universal normalized moment estimates `E_{J_K}|t| <= C₁/K` and `E_{J_K}(t^2) <= C₂/K^2`. Elementary sine bounds and interval decompositions are acceptable, but the final theorem may not assume these estimates as axioms or hypotheses.

4. Prove that the kernel is an even finite trigonometric polynomial with frequency bounded by `2*(K-1)`. Develop the converse step needed downstream: every finite even cosine polynomial has an ordinary polynomial representation in `cos t`; prove the degree and evaluation statements rather than assuming them.

5. Form the finite tensor kernel and establish the relevant product integration/Fubini identities. For a bounded locally Lipschitz function `f` on a product box, show that convolution with the tensor kernel is an algebraic polynomial after the coordinate change and that its error is bounded by the Lipschitz constant times the sum of the one-dimensional first moments (with an optional second-order refinement using the second moments).

6. Prove support/degree control for the extracted tensor polynomial. In dimension four, bound its monomial coefficient `l1` norm by `C * A^K * ||f||_infty`, for fixed universal `C,A > 0`. A quantitatively stronger explicit bound is acceptable. This must be a theorem derived from the cosine/Chebyshev expansion, not a supplied coefficient-envelope hypothesis.

7. Package the affine center/radius substitution used to move between a nondegenerate rectangle in `R^4` and normalized coordinates. State all positivity/nondegeneracy assumptions explicitly and prove the resulting evaluation, degree, approximation, and coefficient-envelope corollaries.

## Standard reference
The analytic construction is standard Jackson approximation theory; suitable references include DeVore and Lorentz, *Constructive Approximation*, and Rivlin, *An Introduction to the Approximation of Functions*. The Lean development must provide its own proofs and may use existing Mathlib Fourier, integration, polynomial, Chebyshev, and finite-product infrastructure.

## Intended reuse
The immediate consumer is the upper-bound proof for estimating an unrestricted optimal-policy value over four-probability cells. It needs a degree-`O(K)` polynomial approximation on each pilot rectangle, an error of order local Lipschitz scale divided by `K`, and an exponential-in-`K` coefficient envelope. The promoted substrate must remain independent of that causal/statistical application and should be reusable for fixed finite-dimensional polynomial approximation.

## May assume / must derive
May assume standard Mathlib/Causalean facts about Lebesgue integration, interval integrals, finite products, trigonometric identities, polynomials, multivariate polynomials, and Chebyshev polynomials.

Must derive all Jackson-specific mass and moment bounds, trigonometric degree statements, converse even-trigonometric-to-algebraic extraction, tensor convolution identities, approximation bounds, and coefficient envelopes. Do not replace any of these deliverables by a structure field, class field, axiom, cited hypothesis, or caller-supplied assumption.

## Non-goals
- Do not import or mention research modules, `globalCellValue`, `Cell`, `Rectangle`, causal identification, estimators, minimax risk, Poissonization, or the Cai/Jiao-Han-Weissman lower bounds.
- Do not prove the paper-specific estimator theorem or choose the paper's tuning constants.
- Do not hide analytic obligations behind an abstract approximation certificate whose fields are exactly the required conclusions.

## Known building blocks
Prefer existing Mathlib/Causalean APIs for interval integrals, product measures, finite sums/products, `Polynomial`, `MvPolynomial`, trigonometric identities, and Chebyshev polynomials. If those APIs are insufficient, add small paper-neutral helper lemmas in the same substrate closure.

## Extraction boundary
Develop and review the study implementation in its normal study location. Promote the complete paper-neutral dependency closure into `CausalSmith/CausalSmith/Substrate/OrderFourJacksonTensorApproximation/`. Keep only thin application-specific wrappers in the research proof. Promotion must preserve a clean import boundary: the promoted module must not import anything under the research run.
