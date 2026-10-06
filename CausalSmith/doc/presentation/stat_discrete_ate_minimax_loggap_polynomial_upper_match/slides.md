# Estimating Average Treatment Effects With Many Categories

Rare covariate categories need not prevent accurate estimation of an average treatment effect.

---

## Research question

We observe \(n\) independent units with binary treatment \(A\), binary outcome \(Y\), and an adjustment covariate with \(d\) categories. Treatment probabilities and outcome means can vary arbitrarily across categories.

The standard rule estimates each category’s treatment–control contrast and weights it by empirical prevalence.

- Its all-category estimate is \(\sum_{k=1}^{d}\widehat h_k\), where \(\widehat h_k\) is the empirical ratio contribution shown on “Heavy categories,” evaluated using the full sample.
- An unobserved treatment arm contributes zero.
- Zeng et al. (2024) show that regression, inverse probability weighting, and doubly robust estimators coincide with this rule when categorywise quantities are fitted on the same sample.

Their worst-case mean-squared error has scale \(d^2/n^2+1/n\), and consistency requires \(d/n\to0\).

Can estimating the average directly improve on estimating every category’s contrast?

---

## Key idea

Use ratios for abundant categories and polynomial estimates for sparse categories’ contributions to the average.

Let \(\pi_k\) be the treatment probability in category \(k\). **Fixed overlap** means \(\epsilon\le\pi_k\le1-\epsilon\): both arms have positive population probability within every relevant category.

For fixed \(0<\epsilon<1/2\), we attain the mean-squared-error scale

\[
r_{n,d}:=\frac1n+\frac{d^2}{n^2(\log n)^2},
\]

where \(r_{n,d}\) combines ordinary sampling error with the cost of many categories.

The guarantee holds for \(n\ge N_\epsilon\) and \(0<d\le\rho_\epsilon n\log n\), with constants depending only on overlap.

The polynomial estimates use counts without dividing by an observed treatment-arm count. This repairs the sparse-category failure of empirical ratios.

---

## Example

At exact randomization, \(\pi_k=1/2\) in every category. Outcome means can still differ arbitrarily across categories.

\[
\widehat\tau_{\mathrm{ctr}}
=
\frac1n\sum_{i=1}^n
2(2A_i-1)\left(Y_i-\frac12\right).
\]

The centered estimator \(\widehat\tau_{\mathrm{ctr}}\) averages outcomes centered at one-half, with opposite signs for treatment and control.

For every positive \(n,d\), its worst-case mean-squared error is at most \(1/n\); minimax error is at least \(1/(100n)\).

Known randomization removes the need to estimate category treatment probabilities. With unknown probabilities, how can sparse categories still contribute useful information?

---

## Model

We observe independent, identically distributed units \(O_i=(X_i,A_i,Y_i)\) from a law \(P\), with \(X_i\in\{1,\ldots,d\}\).

For category \(k\):

- \(p_k=P(X=k)\) is its population prevalence.
- \(\mu_{ak}=E_P[Y\mid A=a,X=k]\) is its outcome mean in arm \(a\).
- \(q_{aky}=P(A=a,X=k,Y=y)\) is a joint treatment–outcome mass.
- \(q_k=(q_{0k0},q_{0k1},q_{1k0},q_{1k1})\) collects its four masses.

\[
\tau(P)
=
\sum_{k=1}^{d}\phi(q_k).
\]

The target \(\tau(P)\) adds the contributions \(\phi(q_k)=p_k(\mu_{1k}-\mu_{0k})\): prevalence times the treatment–control contrast.

Small prevalence limits a category’s contribution even when its contrast is difficult to estimate.

---

## Assumptions

Every category with \(p_k>0\) satisfies

\[
\epsilon \le \pi_k \le 1-\epsilon .
\]

Overlap guarantees population support for both arms. A finite sample can still contain no observations from one arm.

The statistical result allows arbitrary category prevalences and outcome means, without smoothness or sparsity connecting categories.

For \(\tau(P)\) to be the causal ATE, additionally require:

- **Consistency:** \(Y=Y(A)\); the recorded outcome is the potential outcome under the treatment received.
- **Conditional exchangeability:** \((Y(0),Y(1))\perp A\mid X\); treatment carries no additional information about potential outcomes within a category.

In the randomized example, \(\epsilon=1/2\) forces every \(\pi_k=1/2\).

---

## Main result

Let \(\mathcal E_{n,d,\epsilon}\) be the class of iid sample laws satisfying overlap. The notation \(P^{\otimes n}\) means \(n\) independent draws from \(P\).

The minimax risk \(\mathsf R_{n,d,\epsilon}\) is the smallest worst-case mean-squared error attainable by any estimator.

@informal thm:sharp-minimax-fixed-interior: For fixed \(0<\epsilon<1/2\), \(n\ge N_\epsilon\), and \(0<d\le\rho_\epsilon n\log n\), hybrid worst-case MSE is at most \(C_\epsilon r_{n,d}\), and minimax MSE is at least \(a_\epsilon r_{n,d}\).

\[
a_\epsilon r_{n,d}
\le
\mathsf R_{n,d,\epsilon}
\le
\sup_{P^{\otimes n}\in\mathcal E_{n,d,\epsilon}}
E_P\!\left[\left(\widehat\tau_n^{\mathrm{hyb}}-\tau(P)\right)^2\right]
\le
C_\epsilon r_{n,d}.
\]

Here \(\widehat\tau_n^{\mathrm{hyb}}\) is our ratio–polynomial estimator. The positive constants \(a_\epsilon,C_\epsilon,\rho_\epsilon\) and cutoff \(N_\epsilon\) depend only on overlap.

Its upper bound matches the lower bound for every estimator, improving the category term by a squared logarithmic factor over standard ratios.

---

## Heavy categories

Split the sample in half: the pilot half selects categories, and the independent estimation half estimates their contributions.

Let \(m_0,m_1\) be the split sizes and \(L=\log(en)\). A category is **heavy** when its pilot count exceeds \(256L\); the remaining categories are **light**.

For heavy categories, retain the standard ratio contribution:

\[
\widehat h_k
=
\frac{N_k^{(1)}}{m_1}
\left\{
\frac{N^{(1)}_{1k1}}{N^{(1)}_{1k}}\mathbf1\{N^{(1)}_{1k}>0\}
-
\frac{N^{(1)}_{0k1}}{N^{(1)}_{0k}}\mathbf1\{N^{(1)}_{0k}>0\}
\right\}.
\]

Superscript \(1\) denotes estimation-half counts: \(N_k^{(1)}\) is the category total, \(N_{ak}^{(1)}\) its arm total, and \(N_{ak1}^{(1)}\) its outcome-one count.

This computes empirical prevalence times empirical contrast, setting an empty arm’s contribution to zero.

Pilot abundance and overlap control missing-arm error. The improvement comes from changing what we do with light categories.

---

## Light categories

Consider one light category with four population masses \(u=(u_{00},u_{01},u_{10},u_{11})\) and an unknown treatment probability.

Write \(s_a(u)=u_{a0}+u_{a1}\) for arm mass, \(s(u)=s_0(u)+s_1(u)\) for total mass, and \(t_a(u)=u_{a1}\) for outcome-one mass.

Its contribution is \(\phi(u)=s(u)[t_1(u)/s_1(u)-t_0(u)/s_0(u)]\).

Replace the reciprocals by a polynomial:

\[
P_{M,B}(u)
=
\frac{s(u)t_1(u)}B
G_M\!\left(\frac{s_1(u)}B\right)
-
\frac{s(u)t_0(u)}B
G_M\!\left(\frac{s_0(u)}B\right).
\]

Here \(B\) bounds light-category mass, \(M\) controls degree, and \(G_M\) supplies the reciprocal approximation. The expression computes an approximation to the category’s mass-weighted contrast.

We approximate the contribution to the average, allowing small categories to tolerate inaccurate conditional contrasts.

---

## Polynomial construction

Let \(T_M\) be the degree-\(M\) Chebyshev polynomial, characterized by \(T_M(\cos\theta)=\cos(M\theta)\).

\[
H_M(x)=\frac{1-T_M(1-2x)}{2M^2},
\qquad
E_M(x)=\frac{H_M(x)}{x},
\qquad
G_M(x)=\frac{1-E_M(x)}{x},
\]

These formulas construct the reciprocal approximation \(G_M\). The quotients extend to polynomials at zero.

For positive \(x\), \(xG_M(x)=1-E_M(x)\): \(E_M\) measures the error from replacing the reciprocal.

Under overlap and \(s(u)\le B\), the contribution error is at most \(2B/(\epsilon M^2)\).

For our light category, overlap keeps each arm’s mass at least an \(\epsilon\) fraction of total mass. This converts reciprocal error into an absolute contribution error that shrinks quadratically with degree.

---

## Unbiased polynomial estimation

Expand the approximating polynomial:

\[
P_{M,B}(u)=\sum_{|r|\le M}c_ru^r.
\]

Here \(r\) lists the four cell exponents, \(|r|\) is total degree, \(u^r\) is their monomial, and \(c_r\) is its coefficient.

Estimate it from counts:

\[
\widehat P_k
=
\sum_{|r|\le M}
c_r
\frac{\prod_{a,y}(N^{(1)}_{aky})_{r_{ay}}}{(m_1)_{|r|}}.
\]

The falling factorial \((z)_t=z(z-1)\cdots(z-t+1)\), with \((z)_0=1\), counts ordered choices of distinct observations. Its normalization estimates each population monomial without bias.

Thus \(E_P[\widehat P_k]=P_{M,B}(q_k)\): sampling adds noise without adding approximation bias.

This approximation-and-moment strategy follows Jiao et al. (2015).

Return to the light category with unknown treatment probability.

The factor \(s(u)t_1(u)\) includes the monomial \(u_{01}u_{11}\): control outcome-one mass times treated outcome-one mass.

Its unbiased estimate is \(N^{(1)}_{0k1}N^{(1)}_{1k1}/(m_1)_2\).

- The numerator counts pairs of distinct observations, one from each outcome-one cell.
- The denominator counts all ordered pairs in the estimation half.
- If the treated arm is unobserved, this term equals zero and remains defined.

Every term of \(\widehat P_k\) works this way. The denominators depend on sample size and degree, rather than the observed arm counts.

Across repeated samples, these terms recover the polynomial’s population value. The procedure estimates a contribution without first recovering an accurate treatment probability or conditional contrast.

---

## Logarithmic bias improvement

The degree and mass scale are calibrated together:

\[
M(n)=\max\{2,\lfloor\alpha_0L\rfloor\},\qquad B(n)=b_0L/m_1.
\]

Here \(\alpha_0\) is a fixed small numerical constant, \(b_0=4096\), and \(L=\log(en)\). These choices are the same for every overlap level.

With high probability, pilot-light categories have \(p_k\le B/4\). Classification errors receive a separate mean-square bound.

- Per-category approximation error is at most \(2B/(\epsilon M^2)\).
- With \(B\) proportional to \(\log n/n\) and \(M\) proportional to \(\log n\), this is of order \(1/(n\log n)\).
- Summing over at most \(d\) categories and squaring gives the category term \(d^2/(n^2(\log n)^2)\).

The remaining question is whether estimating a growing-degree polynomial costs too much sampling variance.

---

## Sampling cost per category

Let \(\bar P_k=P_{M,B}(q_k)\) be the polynomial’s population value.

For a light category satisfying \(p_k+4M/m_1\le B\) and \(4M^2\le m_1\),

\(\operatorname{Var}_P(\widehat P_k)\le8(\mathrm e+1)(B6^M)^2\).

Why does the bound contain a small mass factor \(B^2\)?

- Coefficients of \(G_M\) can grow exponentially: their absolute sum at arguments at most one is bounded by \(6^M\).
- A degree-\(j+2\) contribution has coefficient scale \(B^{-j-1}\), but its count moments supply powers of the small cell masses.
- Falling-factorial normalization cancels the corresponding sample-size powers.
- When two observation tuples share observations, the moment bound inflates each cell mass by at most \(M/m_1\). The mass condition keeps the scaled arguments within one.

These ingredients leave a second-moment scale \((B6^M)^2\). Small category mass offsets coefficient growth.

---

## Aggregate sampling variance

Condition on the pilot and consider its selected categories with \(p_k\le B/4\). Independence of the estimation half makes this a fixed set.

Categories share a multinomial sample, so covariance also matters. For distinct light categories, covariance is at most \(8M^2(B6^M)^2/m_1\).

Consequently, their aggregate sampling variance is at most

\(C\{d+d^2M^2/m_1\}(B6^M)^2\),

where \(C\) is a numerical constant.

The small degree constant ensures, for sufficiently large \(n\), \((6^{2M})^2L^6\le n\). Exponential coefficient growth is therefore affordable:

- The diagonal term is at most \(C d/(n^{3/2}L)\), bounded by \(C\{1/n+d^2/(n^2L^2)\}\).
- The covariance term is at most \(C d^2L/n^{5/2}\), bounded by \(C d^2/(n^2L^2)\).

Logarithmic degree improves bias while keeping aggregate sampling fluctuations within the target risk scale.

---

## Putting the pieces together

Let \(\widehat{\mathcal H}_n\) and \(\widehat{\mathcal L}_n\) denote the pilot-selected heavy and light sets.

\[
\widehat T_{\mathcal H}
=
\sum_{k\in\widehat{\mathcal H}_n}\widehat h_k,
\qquad
\widehat T_{\mathcal L}
=
\sum_{k\in\widehat{\mathcal L}_n}\widehat P_k.
\]

These are the heavy ratio total and light polynomial total.

\[
\widehat\tau_n^{\mathrm{hyb}}
=
\max\{-1,\min(1,\widehat T_{\mathcal H}+\widehat T_{\mathcal L})\}.
\]

Clipping keeps the estimate within the ATE’s feasible range and cannot increase squared error.

Heavy-category error, light approximation bias, light sampling variance, and pilot classification errors are all controlled at the target mean-square scale.

The matching lower bound from Zeng et al. (2024) establishes optimality.

---

## Further results

- **Computation:** the estimator can be evaluated from split counts in at most \(K\,d\,M(n)^4\) arithmetic and comparison operations, for a universal constant \(K\).
- **Near randomization:** for every positive \(n,d\) and \(0<\epsilon\le1/2\), the centered estimator’s worst-case mean-squared error is at most \(1/n+4(1/2-\epsilon)^2\).

The randomized example is the endpoint of the second bound: when every \(\pi_k=1/2\), its category penalty vanishes.

---

## Open questions

What is the matching minimax lower envelope when overlap varies with sample size, \(\epsilon=\epsilon_n\), especially near exact randomization?

Our fixed-interior theorem establishes the sharp rate for each fixed \(0<\epsilon<1/2\) in its calibrated range. The randomized endpoint has parametric risk for every positive \(d\).

A matching lower envelope for varying overlap would characterize the transition between these regimes.

---

## Takeaways

- For fixed \(0<\epsilon<1/2\), \(n\ge N_\epsilon\), and \(0<d\le\rho_\epsilon n\log n\), minimax mean-squared error has scale \(r_{n,d}=1/n+d^2/(n^2(\log n)^2)\).
- Ratios handle abundant categories. Sparse categories use polynomial contribution estimates whose factorial moments are unbiased; small masses and a small logarithmic degree control their sampling cost.
- Within this range, parametric accuracy extends to \(d=O(\sqrt n\log n)\), and consistency holds exactly when \(d=o(n\log n)\).

---

## Appendix: Sharp fixed-interior minimax rate

Matching risk bounds establish the optimal scale, its parametric regime, and its consistency threshold for each fixed interior overlap level.

@formal thm:sharp-minimax-fixed-interior

---

## Appendix: Overlap adaptive hybrid envelope

One statement gives computation, universal hybrid tuning, the oracle comparison, and the near-randomization and endpoint guarantees.

@formal thm:overlap-adaptive-universal-hybrid
