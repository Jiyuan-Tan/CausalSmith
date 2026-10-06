# Measuring Full Adoption From Partial Rollout

When an experiment stops before everyone is treated, choosing when to measure can control the uncertainty from estimating full adoption.

---

## Motivation

- With interference, a unit’s outcome can depend on other units’ treatment assignments.
- We want the mean outcome change between nobody treated and everybody treated.
- The rollout reaches only a treated fraction \(q<1\).
- Subtracting the baseline from the final measurement estimates the partial-rollout contrast.

Cortez et al. (2022) show how bounded-order interactions can make full-adoption effects identifiable through polynomial extrapolation.

**How should we measure a partial rollout to estimate full adoption precisely?**

---

## Research question

Suppose the mean response is a polynomial of degree at most \(\beta\), where \(\beta\) is the maximum order.

A natural approach measures at \(\beta+1\) equally spaced fractions and extrapolates the fitted polynomial:

\[
p^{\mathrm{eq}}(\beta,q)_j=\frac{qj}{\beta},
\qquad j=0,\ldots,\beta .
\]

Here \(p^{\mathrm{eq}}_j\) is the treated fraction at measurement \(j\); \(q\) is the final fraction.

- Interpolation gives an unbiased estimate. That alone does not control how strongly its weights amplify noise.
- Cortez-Rodriguez et al. (2024) study clustering to reduce variance for polynomial rollout estimation.
- Choosing measurement fractions is an optimal-design problem, as in Kiefer and Wolfowitz (1959).

**Which fractions control the variance cost of extrapolation?**

---

## Key idea

Place more measurements near both endpoints of the observed interval.

These **Chebyshev-Lobatto fractions** control polynomial growth between measurements. Extrapolation beyond the interval still has an unavoidable cost.

- Choose weights that recover the target for every polynomial of degree at most \(\beta\).
- Among those weights, minimize the sum of their absolute values.
- With more than the minimum number of measurements, Chebyshev-Lobatto placement attains the unavoidable exponential variance amplification up to constants.

This conclusion uses a static polynomial mean, correct round expectations, a common variance bound, and a budget bounded away from full adoption.

---

## Half-rollout example

At \(q=0.5\), measurements cover only \([0,0.5]\), while the target includes the response at one.

The Chebyshev-Lobatto measurement fractions are

\[
p^{\mathrm{Ch}}_j(k,q)
=
\frac{q}{2}\left\{1-\cos\left(\frac{\pi j}{k}\right)\right\}.
\]

Here \(k\) is the number of rollout intervals, giving \(k+1\) measurements; \(j=0,\ldots,k\) indexes them. The superscript \(\mathrm{Ch}\) names this schedule.

- At this budget, the schedule starts at zero, ends at \(0.5\), and concentrates measurements near both endpoints.
- The variance-amplification base is approximately \(5.83\).
- The matching bounds raise that base to \(2\beta\), up to constants.

The design controls what happens inside the observed half; it cannot eliminate extrapolation to one.

---

## Model

For an outcome law \(P\), let \(m_P(u)\) be the expected population mean at treated fraction \(u\).

\[
m_P(u)=\sum_{\ell=0}^{\beta} a_{P,\ell}u^\ell
\]

The coefficients \(a_{P,\ell}\) describe the response curve. This restriction holds throughout \([0,1]\), including the unobserved endpoint.

Our target is

\[
\tau_P=m_P(1)-m_P(0)=\sum_{\ell=1}^{\beta} a_{P,\ell}.
\]

Thus \(\tau_P\) adds the nonconstant coefficients; the intercept cancels.

At measurement fraction \(p_j\), we observe the population mean \(\bar Y_j\). We require \(\mathbb E_\pi[\bar Y_j]=m_P(p_j)\), where \(\pi\) denotes rollout randomization.

**Static consistency:** outcomes depend on current assignments, including others’ assignments, with no separate dependence on earlier rollout steps.

---

## Assumptions

**Common variance envelope:** every round satisfies

\[
\operatorname{Var}_\pi(\bar Y_j)\le \frac{\sigma_0^2}{n}.
\]

Here \(n\) is population size, and \(\sigma_0^2\ge0\) sets the common variance scale. It incorporates outcome magnitudes and dependence across units.

- Cross-round covariances are otherwise unrestricted, provided they form a valid covariance matrix.
- Admissible schedules, denoted \(S_{k,q}\), start at zero, increase strictly, and end at \(q\).
- **Budget cap:** \(0<q\le q_{\max}<1\), keeping full adoption outside the observed interval.
- **Oversampling:** \(k\ge c\beta\), with fixed \(c>1\), gives more than the minimum \(\beta+1\) measurements.

Let \(\mathcal P_\beta\) denote laws satisfying static consistency, polynomiality, correct round expectations, and the variance envelope.

For the half-rollout example, polynomiality must hold beyond \(0.5\), all the way to one. Bounded-order interference motivates this restriction; we impose it.

---

## Unbiased estimation

Estimate the full-adoption contrast with

\[
\hat\tau_{w,p}=\sum_{j=0}^k w_j\bar Y_j,
\]

where \(w_j\) is the weight on measurement \(j\), and \(p\) is the schedule.

The weights must recover the contrast for every polynomial term:

\[
W_\beta(p)
=
\left\{
w\in\mathbb R^{k+1}:
\sum_{j=0}^k w_j p_j^0=0
\ \text{and}\
\sum_{j=0}^k w_j p_j^\ell=1
\ \text{for every } \ell=1,\ldots,\beta
\right\}.
\]

Here \(W_\beta(p)\) is the set of polynomial-exact weights.

- The first equation removes the intercept; \(p_j^0\) means one.
- Each remaining equation recovers one nonconstant coefficient’s contribution to \(\tau_P\).
- Distinct nodes and \(k\ge\beta\) guarantee that these weights exist.

These equations deliver unbiasedness. What determines their variance?

---

## Variance cost

Large positive and negative weights can cancel in the expected estimate while magnifying noise.

@informal thm:tv-envelope-design: Under the rollout law restrictions, \(1\le\beta\le k\), \(\sigma_0^2\ge0\), and an admissible schedule, polynomial-exact weights exist, are unbiased, and obey a variance bound sharp over the covariance envelope.

For every polynomial-exact weight vector,

\[
\operatorname{Var}_\pi\!\left(\sum_{j=0}^k w_j\bar Y_j\right)
\le
\frac{\sigma_0^2}{n}\left(\sum_{j=0}^k |w_j|\right)^2 .
\]

Estimator variance is bounded by the common round variance times the squared sum of absolute weights.

**Why absolute values?** The envelope permits covariance signs that align with the weight signs. A valid covariance matrix attains this bound.

Unbiasedness constrains signed sums; variance control requires small absolute sums.

---

## Design objective

First choose the least costly polynomial-exact weights at a fixed schedule:

\[
A_\beta(p)
=
\inf_{w\in W_\beta(p)}
\left(\sum_{j=0}^k |w_j|\right)^2.
\]

Here \(A_\beta(p)\) is the smallest worst-case variance multiplier available at schedule \(p\).

Then choose measurement fractions:

\[
M_{\beta,k,q}
=
\inf_{p\in S_{k,q}} A_\beta(p).
\]

Here \(M_{\beta,k,q}\) is the best multiplier across all admissible schedules with \(k+1\) measurements and budget \(q\).

Multiplying by \(\sigma_0^2/n\) gives the optimal worst-case variance over all valid covariance matrices satisfying the round variance envelope.

---

## Main result

@informal thm:chebyshev-minimax: For \(\beta\ge1\), \(k\ge c\beta\), fixed \(c>1\), and \(0<q\le q_{\max}<1\), Chebyshev-Lobatto schedules attain the smallest worst-case variance amplification up to constants depending only on \(c,q_{\max}\).

\[
C_-(q_{\max})
\left(\frac{(1+\sqrt{1-q})^2}{q}\right)^{2\beta}
\le
M_{\beta,k,q}
\le
C_+(c,q_{\max})
\left(\frac{(1+\sqrt{1-q})^2}{q}\right)^{2\beta}.
\]

The positive constants \(C_-\) and \(C_+\) are independent of \(q,\beta,k\); their arguments show what they depend on.

- Every admissible schedule faces the lower bound.
- Chebyshev-Lobatto placement attains the upper bound.
- Chebyshev-Lobatto placement attains the unavoidable exponential rate up to constants.

At \(q=0.5\), with a fixed cap \(q_{\max}\ge0.5\) below one, the common base is approximately \(5.83\).

Why does measurement placement control this cost?

---

## Hidden polynomial growth

The weight problem has an equivalent polynomial interpretation:

\[
\inf_{w\in W_\beta(p)} \sum_{j=0}^k |w_j|
=
\sup\left\{
|r(1)-r(0)|:
r\in\mathbb R[x],\ \deg(r)\le \beta,\ \max_{0\le j\le k}|r(p_j)|\le 1
\right\}.
\]

Here \(r\) is a test polynomial of degree at most \(\beta\); \(\mathbb R[x]\) denotes real polynomials.

The right side asks: **How large can the full-adoption contrast be while every measured value stays within one?**

- A large hidden contrast forces large absolute weights.
- Choosing fractions therefore means controlling polynomial growth that measurements fail to constrain.

In the half-rollout example, we bound \(r\) at measurement fractions in \([0,0.5]\), but its contrast involves \(r(1)\).

---

## Between measurements

Measurements must first control the polynomial throughout the observed interval.

Using the Chebyshev-Lobatto mesh inequality, oversampling with \(k\ge c\beta\), \(c>1\), gives

\[
 |R(x)|
 \le
 K(c)
 \max_{0\le j\le k}\left|R\!\left(-\cos\!\left(\frac{\pi j}{k}\right)\right)\right|.
\]

Here \(R\) is a polynomial of degree at most \(\beta\), \(x\in[-1,1]\), and \(K(c)\) is a finite constant depending only on the oversampling ratio.

- Rescaling \([0,q]\) to \([-1,1]\) sends the measurement fractions to the nodes inside the maximum.
- Small values at those nodes imply small values everywhere in the observed interval, up to \(K(c)\).
- Oversampling supplies control between measurements.

For the half-rollout example, this step controls the entire interval \([0,0.5]\). How much growth remains outside it?

---

## Beyond the observed interval

Under the same rescaling, full adoption becomes the exterior point \(x_q=2/q-1>1\).

Its growth factor is \(\lambda(q)=x_q+\sqrt{x_q^2-1}\).

For polynomials bounded throughout the rescaled interval,

\[
\text{for every real polynomial }R\text{ with }\deg(R)\le \beta
\text{ and }\sup_{x\in[-1,1]}|R(x)|\le 1,\qquad
|R(x_q)-R(-1)|\le C(q_{\max})\,\lambda(q)^\beta,
\]

Here \(R(-1)\) corresponds to baseline and \(R(x_q)\) to full adoption. The constant \(C(q_{\max})\) depends only on the budget cap.

- The mesh inequality controls the observed interval.
- This bound controls the remaining endpoint extrapolation.
- The dual identity converts endpoint growth into absolute-weight size; squaring gives variance amplification.

The growth factor equals the main result’s base, \((1+\sqrt{1-q})^2/q\).

---

## Unavoidable amplification

A polynomial bounded throughout \([0,q]\) satisfies the measurement restriction for **every** schedule.

The Chebyshev polynomial \(T_\beta\), of degree \(\beta\), supplies such a polynomial after rescaling. Its endpoint contrast is at least \(T_\beta(x_q)-1\).

\[
T_\beta(x_q)-1\ge c(q_{\max})\,\lambda(q)^\beta .
\]

This lower bound uses a positive constant \(c(q_{\max})\), distinct from the oversampling ratio \(c\).

- Every placement inside the rollout interval admits this test polynomial.
- The dual identity forces absolute-weight size at least proportional to \(\lambda(q)^\beta\).
- Squaring gives the matching variance-amplification lower bound.

The unavoidable cost comes from extrapolation. Chebyshev-Lobatto placement prevents additional uncontrolled growth between measurements.

---

## Rollout variance guarantee

The envelope solution also supplies an upper bound when covariance comes from the rollout itself.

@informal lem:exact-chebyshev-rate-feasible: Under the rollout law restrictions, \(\sigma_0^2\ge0\), \(\beta\ge1\), \(c>1\), \(0<q\le q_{\max}<1\), and \(k=\lceil c\beta\rceil\), Chebyshev-Lobatto placement supplies the following worst-case rollout variance upper bound.

\[
\inf_{w\in W_\beta(p^{\mathrm{Ch}}(k,q))}
\sup_{P\in\mathcal P_\beta}
\operatorname{Var}_\pi\!\left(\sum_{j=0}^k w_j\bar Y_j\right)
\le
\frac{\sigma_0^2}{n}\,
C_+(c,q_{\max})
\left(\frac{(1+\sqrt{1-q})^2}{q}\right)^{2\beta},
\]

This bounds the infimum worst-case rollout variance over polynomial-exact weights on the Chebyshev-Lobatto schedule. The ceiling rounds the interval count upward.

The reason is direct: rollout covariance satisfies the envelope, so the envelope upper bound applies.

---

## Open questions

- **Covariance-specific optimality:** Does Chebyshev-Lobatto placement minimize worst-case variance under the covariance restrictions of a specified nested rollout? A matching lower bound remains open.
- **Clustered rollouts:** How should measurement placement account for cluster size and dependence within clusters?
- **Mixed designs:** How should fractions be chosen jointly with saturation, encouragement, or exposure-based randomization?

---

## Takeaways

- A static degree-\(\beta\) mean curve over \([0,1]\), with correct round expectations, makes the full-adoption contrast estimable through polynomial-exact weights.
- Under the common variance envelope, the squared sum of absolute weights is the sharp worst-case variance multiplier.
- With \(k\ge c\beta\), \(c>1\), and \(0<q\le q_{\max}<1\), Chebyshev-Lobatto placement controls growth between measurements and attains the unavoidable exponential amplification up to constants.

---

## Appendix: Variance envelope design

Polynomial-exact weights are unbiased, and their squared absolute-weight sum gives the sharp worst-case variance over the diagonal covariance envelope.

@formal thm:tv-envelope-design

---

## Appendix: Chebyshev minimax amplification

With oversampling and budgets bounded away from one, Chebyshev-Lobatto schedules attain matching minimax amplification bounds up to constants.

@formal thm:chebyshev-minimax

---

## Appendix: Rollout variance feasibility

Under the rollout law restrictions, Chebyshev-Lobatto placement supplies the stated exponential upper bound for worst-case rollout variance.

@formal lem:exact-chebyshev-rate-feasible
