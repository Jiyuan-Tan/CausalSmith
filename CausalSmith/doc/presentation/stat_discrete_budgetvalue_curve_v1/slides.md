# Estimating Treatment Value Across Budgets

Estimate the best population outcome achievable at every treatment capacity, even when covariate cells are rare and treatment effects tie.

---

## Motivation

A practitioner wants to compare what treatment can achieve at different capacities.

The natural approach estimates treatment effects within covariate cells, ranks the cells, and plugs those estimates into the optimal-value calculation.

- Rare cells produce noisy effect estimates.
- Near a treatment threshold, small errors change rankings.
- Taking positive parts or maxima of noisy estimates introduces bias.

Feng et al. (2026) derive plug-in value-process asymptotics under regular decision-boundary and process-convergence conditions.

How accurately can we estimate the entire capacity curve while allowing rare cells and exact ties?

---

## Key idea

Replace estimated rankings with a treatment-price calculation.

At each price, estimate control value plus the positive treatment gains remaining after paying that price. Minimizing over prices recovers each capacity value.

Our construction combines three pieces:

- Local polynomial approximation reduces nonlinear bias.
- Unbiased count statistics estimate the polynomial’s powers.
- A common construction across prices controls the entire random path.

With independent sampling, consistency, conditional exchangeability, and fixed treatment overlap, minimax squared largest-error risk has order \(\min\{1,d/[n\log(ed)]\}\).

Here \(n\) is sample size and \(d\) is the known number of covariate cells. One estimated price process delivers this precision across all budgets.

---

## Example

Create \(k\) pairs of cells. Pair \(i\) has population mass \(r_i\), divided equally between its two cells; pair masses sum to one.

Treatment probability is \(1/2\). Control outcome means are \(1/4\), and treatment outcome means are \(1/2+\theta_i\) and \(1/2-\theta_i\), with \(\theta_i\in[-1/8,1/8]\).

At half capacity, treat the better cell in each pair. Either cell can be selected when they tie.

Let \(V_b(P)\) denote the best mean outcome at capacity \(b\) under population law \(P\).

\[
V_{1/2}(P)
=\frac38+\frac12\sum_{i=1}^k r_i|\theta_i|
=\frac18+F_P\!\left(\frac14\right),
\qquad
V_1(P)=\frac12.
\]

Half-capacity value depends on absolute contrasts, while full-capacity value is constant. The price process \(F_P\), defined below, contains this absolute-value problem at price \(1/4\).

---

## Model

An observed record is \(O=(X,A,Y)\): covariate cell, binary treatment, and binary outcome. Potential outcomes are \(Y(0)\) and \(Y(1)\).

For cell \(j\), let \(p_j\) be its population mass, \(\mu_{aj}\) its potential-outcome mean under arm \(a\), and \(\tau_j=\mu_{1j}-\mu_{0j}\) its treatment effect.

A policy treats fraction \(\pi_j\) of cell \(j\). The feasible class \(\Pi_b(P)\) requires \(\sum_j p_j\pi_j\le b\).

With \(B(P)\) denoting mean outcome under universal control, the target is

\[
V_b(P)=B(P)+\max_{\pi\in\Pi_b(P)}\sum_{j=1}^d p_j\pi_j\tau_j,
\qquad
V(P)=\bigl(V_b(P):b\in I\bigr).
\]

The maximum adds the largest feasible treatment gain to control value. The curve collects these population optima over a budget interval \(I\).

---

## Assumptions

- **Independent sampling:** the \(n\) records are independent draws from the same population.
- **Consistency:** \(Y=Y(A)\); the recorded outcome is the potential outcome under received treatment.
- **Conditional exchangeability:** \((Y(0),Y(1))\perp A\mid X\); within a cell, treatment selection does not depend on potential outcomes.
- **Fixed overlap:** treatment probability \(e_j=P(A=1\mid X=j)\) satisfies, in every occupied cell,

\[
\epsilon\le e_j\le 1-\epsilon.
\]

The fixed parameter \(\epsilon\in(0,1/2)\) keeps both treatment arms possible. These conditions identify both cell outcome means.

Call this causal class \(\mathcal M_{d,\epsilon}\). Cell masses can be arbitrarily small, and effects can tie.

In the paired example, treatment probability \(1/2\) satisfies overlap; potential outcomes are generated independently of treatment within cells.

---

## Main result

Choose \(b_0\in[0,1/2]\) and let \(I=[b_0,1-b_0]\).

Our loss squares the largest error over \(I\), then takes expectation. The minimax risk \(\mathfrak R_{n,d,\epsilon,b_0}^{\mathrm{curve}}\) selects the best estimator against the hardest law in \(\mathcal M_{d,\epsilon}\).

@informal thm:matched-curve-frontier: With independent sampling, consistency, conditional exchangeability, and fixed \(0<\epsilon<1/2\), for all \(n\ge1,d\ge2,b_0\in[0,1/2]\), minimax squared supremum risk is of order \(\min\{1,d/[n\log(ed)]\}\).

\[
c_\epsilon\min\left\{1,\frac{d}{n\log(ed)}\right\}
\le \mathfrak R_{n,d,\epsilon,b_0}^{\mathrm{curve}}
\le C_\epsilon\min\left\{1,\frac{d}{n\log(ed)}\right\}.
\]

The positive constants \(c_\epsilon,C_\epsilon\) depend only on overlap. A specified polynomial-and-factorial estimator attains the upper bound.

- \(b_0=0\): simultaneous precision from zero to full capacity.
- \(b_0=1/2\): precision at half capacity alone.

In the paired example, half capacity already supplies the matching difficulty despite constant full-capacity value.

---

## Treatment prices

A shadow price \(\lambda\in[0,1]\) charges \(\lambda\) per treatment.

Define \(F_P(\lambda)=B(P)+\sum_j p_j(\tau_j-\lambda)_+\), where \((x)_+=\max\{x,0\}\). This retains only treatment gains exceeding the charge.

\[
V_b(P)=\inf_{0\le\lambda\le1}\{b\lambda+F_P(\lambda)\}.
\]

The term \(b\lambda\) adds back the price of available capacity.

Every feasible allocation’s gain is bounded by its treatment charges plus the positive gains remaining after those charges.

A threshold allocation attains that bound: treat above the price, split treatment within ties, and use price zero when all positive-effect cells fit.

In the paired example, price \(1/4\) separates effects \(1/4+|\theta_i|\) and \(1/4-|\theta_i|\).

The remaining statistical problem is estimating \(F_P\) uniformly over prices.

---

## Observed cell contributions

For cell \(j\), \(q_j\) contains the four observed masses \(q_{ay,j}=P(X=j,A=a,Y=y)\).

For a generic four-vector \(u\), \(s_a(u)\) is its arm-\(a\) mass and \(s(u)\) its total mass.

\[
g_a(u)=\frac{s(u)u_{a1}}{\max\{s_a(u),\epsilon s(u)\}},
\qquad
f_\lambda(u)=g_0(u)+\bigl[g_1(u)-g_0(u)-\lambda s(u)\bigr]_+,
\qquad
F_P(\lambda)=\sum_{j=1}^d f_\lambda(q_j).
\]

Under our assumptions, \(g_a(q_j)=p_j\mu_{aj}\). Thus \(f_\lambda(q_j)\) is the cell’s control contribution plus its positive gain after charging.

The denominator stabilizes arm-mean calculations on noisy mass vectors.

Substituting empirical masses still applies a nonlinear function to noise. In the paired example, this is the difficulty of estimating \(|\theta_i|\) near zero.

---

## Pilot localization

For \(d\ge16\) and \(n\ge d/L\), use the polynomial construction, with \(L=\log(ed)\).

Separate counts choose the approximation region and estimate the polynomial there.

In the ideal count experiment, pilot counts \(N'_{\zeta j}\) and evaluation counts \(N_{\zeta j}\) are mutually independent Poisson variables with means \(mq_{\zeta j}\).

Here \(\zeta=(a,y)\) indexes the four treatment-outcome categories \(\mathcal Z=\{0,1\}^2\), and \(m=n/8\).

\[
\delta=\frac Lm,\qquad
c_{\zeta j}=\frac{N'_{\zeta j}}m,\qquad
h_{\zeta j}=H_0\left\{\sqrt{c_{\zeta j}\delta}+\delta\right\},
\]

The pilot location \(c_{\zeta j}\) estimates the mass; \(h_{\zeta j}\) is its uncertainty width; \(H_0\) is a fixed multiplier.

Extend each location by its width, truncating the lower endpoint at zero. These intervals form a rectangle with center \(c_j^0\) and coordinate radii \(R_{\zeta j}\).

The approximation region adapts to uncertainty even when a cell is barely observed.

---

## Endpoint-sensitive approximation

On the pilot rectangle, approximate \(f_\lambda\) by a polynomial \(P_\lambda\) of order \(K\), a small multiple of \(L=\log(ed)\).

Write \(a_\zeta=c^0_\zeta-R_\zeta\) and \(b_\zeta=c^0_\zeta+R_\zeta\) for the coordinate interval’s endpoints. Here \(b_\zeta\) is an endpoint, distinct from the treatment budget \(b\).

For a mass vector \(y\) inside the rectangle, the approximation bound is

\(\bigl|P_\lambda(y)-f_\lambda(y)\bigr|\le C_\epsilon\sum_{\zeta\in\mathcal Z}\left\{\sqrt{(y_\zeta-a_\zeta)(b_\zeta-y_\zeta)}/K+R_\zeta/K^2\right\}\).

The first term uses distances to **both endpoints**. The second is a residual smoothing error.

When \(a_\zeta=0\), the first term becomes \(\sqrt{y_\zeta(b_\zeta-y_\zeta)}/K\).

A broad interval therefore need not imply a large error at a tiny true mass. At mass zero, the endpoint-distance term vanishes.

---

## Rare-cell bias

A radius-only approximation bound would assign the same error throughout a pilot interval. Endpoint sensitivity recognizes a rare mass’s position near zero.

On successful localization, the endpoint-distance product is controlled by the true coordinate mass times \(L/m\).

Dividing its square root by \(K\), with \(K\) proportional to \(L\), produces a mass-sensitive error.

After polynomial estimation and clipping, the absolute cell bias at every price is at most

\[
C_\epsilon\left\{\sqrt{\frac{p_j}{nL}}+\frac{1}{nL}\right\}.
\]

Here \(p_j\) is the cell’s total mass; \(C_\epsilon\) depends only on overlap.

The first term shrinks with cell mass. The second remains even at zero mass.

In a rare pair, the approximation recognizes small population weight rather than charging the entire pilot width as bias.

---

## Unbiased polynomial powers

For an evaluation count \(N\sim\operatorname{Pois}(mq)\), center \(z\), and integer power \(h\ge0\), define

\[
U_h(N;z)
=
\sum_{t=0}^h {h\choose t}(-z)^{h-t}\frac{(N)_t}{m^t},
\qquad
(N)_t=N(N-1)\cdots(N-t+1),
\qquad
(N)_0=1.
\]

The falling factorial \((N)_t/m^t\) has expectation \(q^t\). Consequently, \(E[U_h(N;z)]=(q-z)^h\).

Replace each centered polynomial power by this unbiased statistic.

Conditional on the pilot, centers and polynomial coefficients are fixed. Independent evaluation coordinates make products of these replacements unbiased too.

Polynomial estimation therefore adds no nonlinear plug-in bias before clipping.

Jiao et al. (2015) develop polynomial approximation with unbiased count statistics for discrete functionals.

---

## Cell estimator

Expand the local polynomial in normalized centered powers, then replace those powers with their unbiased statistics:

\[
Z_j(\lambda)
=
f_\lambda(c_j^0)+
\sum_{\alpha\in\{0,\ldots,D\}^4}
\beta_{j,\alpha}(\lambda)
\prod_{\zeta\in\mathcal Z}
\frac{U_{\alpha_\zeta}(N_{\zeta j};c^0_{\zeta j})}
{R_{\zeta j}^{\alpha_\zeta}},
\]

The construction has three pieces:

- \(f_\lambda(c_j^0)\): the contribution at the pilot center.
- \(\beta_{j,\alpha}(\lambda)\): coefficients of the polynomial correction.
- The product: unbiased estimates of normalized centered powers.

The four-component index \(\alpha\) specifies the powers; \(D=2(K-1)\) bounds the degree in each coordinate.

Conditional on the pilot, \(E[Z_j(\lambda)\mid N']=P_{j,\lambda}(q_j)\), where \(N'\) denotes all pilot counts.

The random powers stay fixed across prices. How do we also keep their coefficients from moving too much?

---

## Common smoothing across prices

Use the **same positive averaging operator at every price**:

\[
P_{j,\lambda}(c_j^0+R_j\odot\cos\vartheta)
=
\int_{[-\pi,\pi]^4}
f_\lambda\!\left(c_j^0+R_j\odot\cos(\vartheta+t)\right)
\prod_{\zeta\in\mathcal Z}J_K(t_\zeta)\,dt,
\]

This smooths the four mass coordinates, expressed through angles \(\vartheta\); \(t\) shifts those angles, and \(\odot\) means coordinatewise multiplication. The Jackson weights \(J_K\) are nonnegative and integrate to one. Price \(\lambda\) is **not** smoothed.

Total variation is a path’s accumulated movement over prices. Its bounded-variation norm adds that movement to its magnitude at price zero.

The cell paths obey \(\|f_{\cdot}(u)-f_{\cdot}(v)\|_{BV([0,1])}\le C_\epsilon\|u-v\|_1\), where \(\|u-v\|_1\) sums coordinate differences.

Every smoothed mass vector lies in the same rectangle. Positive averaging cannot exceed the average bound on initial magnitude and accumulated movement.

Thus the polynomial paths retain this control; converting them to coefficients gives a controlled envelope proportional to the sum \(S_j=\sum_\zeta R_{\zeta j}\) of pilot radii.

---

## Noise control

Normalization by pilot radii controls the growing polynomial powers.

On successful localization, \(q_{\zeta j}/(mR_{\zeta j}^{\,2})\leq1/L\). The conditional second moment of a normalized power of degree \(h\) is at most \(e^{h^2/L}\).

Choosing \(K=\max\{2,\lfloor L/512\rfloor\}\) balances approximation improvement against coefficient and power growth.

Clip each correction \(Z_j-f_\cdot(c_j^0)\) at magnitude \(d^{1/4}S_j\), producing \(T_j\); clipping cannot increase its total variation.

Let \(G_j\) be successful localization: \(|c_{\zeta j}-q_{\zeta j}|\le h_{\zeta j}/4\) in every coordinate. Define the **uncentered** restricted error path by \(W_j^{\mathrm{good}}(\lambda)=\mathbf1_{G_j}\{T_j(\lambda)-f_\lambda(q_j)\}\).

\[
\mathbb E\|W_j^{\mathrm{good}}\|_{BV([0,1])}^2
 \leq c\,d^{1/16}v_j^2.
\]

Here \(v_j=\sqrt{p_jL/m}+L/m\) measures pilot uncertainty, and \(c\) depends only on overlap.

This bounds the whole cell path’s magnitude and movement, not merely its variance at one price.

---

## Uniform aggregation

Write \(W_j=W_j^{\mathrm{good}}\). Center it by subtracting its pointwise mean path \(\mathbb EW_j\).

For these independent continuous cell paths, the uniform inequality is

\[
\mathbb E\left\|\sum_{j=1}^{d}\bigl(W_j-\mathbb EW_j\bigr)\right\|_\infty^2
\leq 16384\sum_{j=1}^{d}
\mathbb E\left[\bigl(\|W_j\|_\infty+\operatorname{TV}_{[0,1]}(W_j)\bigr)^2\right].
\]

The left side takes the largest centered error over **all prices** before squaring and averaging. The symbol \(\operatorname{TV}_{[0,1]}\) denotes total variation.

The right side charges each cell for its height and all its movement along the price interval. That movement budget controls peaks wherever they occur.

Independence makes these **squared path budgets add** in the maximal inequality. Fixed-price variance addition alone would not deliver this conclusion.

Since \(\sum_jp_j=1\), \(\sum_jv_j^2\leq2L/m+2d(L/m)^2\). In the branch \(n\ge d/L\), inserting the cell bounds yields at most a constant times \(d/(nL)\).

---

## From counts to records

The uniform centered bound combines with two remaining terms:

- Summed bias has squared order at most \(d/(nL)\), using \(\sum_j\sqrt{p_j}\le\sqrt d\).
- Failed localizations have exponentially small weighted envelopes; clipping controls their contribution.

Together they bound the ideal price-process risk by \(C_\epsilon d/(nL)\).

To implement the count construction, draw \(M\sim\operatorname{Pois}(n/4)\), randomly permute the \(n\) records, retain \(M\) when \(M\le n\), and independently mark them pilot or evaluation with equal probability. Use the zero process when \(M>n\).

Before the cap, Poisson marking gives the independent counts at scale \(m=n/8\).

\[
\widehat F(\lambda)
=
E\!\left\{\widetilde F^{\mathrm{cap}}(\lambda)\mid O^{(n)}\right\}.
\]

Here \(\widetilde F^{\mathrm{cap}}\) sums the clipped cell estimates. Averaging over auxiliary randomness conditional on the actual sample cannot increase expected squared supremum error; the cap adds a controlled tail term.

---

## Recovering the curve

The Jackson–factorial estimator reports

\[
\widehat V_b^{\mathrm{JF}}
=
\Pi_{[0,1]}
\left(
\min_{0\leq\lambda\leq1}
\{b\lambda+\widehat F(\lambda)\}
\right),
\qquad b\in I.
\]

The superscript names the polynomial-and-count construction; \(\Pi_{[0,1]}\) truncates the value to \([0,1]\).

\[
\sup_{b\in[0,1]}
\left|
\inf_{0\le\lambda\le1}\{b\lambda+\widehat F(\lambda)\}
-V_b(P)
\right|
\le
\sup_{\lambda\in[0,1]}
\left|\widehat F(\lambda)-F_P(\lambda)\right|.
\]

A uniform perturbation of price values changes every minimum by at most that perturbation. Truncation cannot increase error.

Thus one accurate price process controls every budget, including one selected after viewing the curve.

For \(d<16\), empirical masses suffice. For \(d\ge16\) and \(n<d/L\), report the constant curve \(1/2\). These branches complete the all-sample upper bound.

---

## Distance inside treatment value

Return to the paired example. Let \(R,S\) be probability distributions on \(k\) categories.

Choose \(r_i=(R_i+S_i)/2\) and \(\theta_i=(R_i-S_i)/[8(R_i+S_i)]\), with contrast zero when the denominator vanishes.

\[
V_{1/2}(P_{R,S})=\frac38+\frac1{32}\|R-S\|_1,
\qquad V_1(P_{R,S})=\frac12,
\]

Here \(P_{R,S}\) is the resulting causal law; \(\|R-S\|_1\) sums absolute category-probability differences.

There is an exact conversion from \(n\) draws from each source to \(n\) causal records. Select either source equally, retain its category, and draw cell sign and treatment independently with equal probabilities. Control mean is \(1/4\); treated means use opposite sign shifts for the two sources.

Mixing sources within a category produces exactly the paired treatment means.

A half-capacity estimator would therefore estimate distributional distance: subtract \(3/8\) and multiply by \(32\).

---

## Moment matching

The lower bound uses the same absolute-value difficulty that polynomial approximation addresses in the estimator.

Let \(\ell\) be a positive moment order. The lemma used in the converse constructs two contrast distributions \(\nu_0,\nu_1\) on \([-1,1]\) whose moments agree through degree \(\ell\), but whose mean absolute contrasts differ.

Let \(\mathcal E_\ell\) denote the smallest uniform error when approximating \(|x|\) on \([-1,1]\) by a polynomial of degree at most \(\ell\).

\[
\int|x|\,d\nu_1(x)-\int|x|\,d\nu_0(x)
=2\mathcal E_\ell\ge\frac1{50\ell}.
\]

The integral averages absolute contrast under each distribution.

Matched moments imply agreement on **every polynomial expectation** through degree \(\ell\). Absolute value retains a discrepancy that those polynomials cannot resolve.

The construction uses signed weights that cancel low-degree polynomials, then splits their positive and negative parts into probability distributions.

The upper bound approximates the nonsmooth target by polynomials. The converse exploits the error that low-degree polynomials must leave behind.

---

## Sharpness

Jiao et al. (2018) supply the distance lower bound for \(1\le n\le k^2\). For \(n>k^2\), use small contrasts around a uniform distribution.

With \(h=\lfloor k/2\rfloor\), moment order \(\ell\) proportional to \(\log k\), and \(\xi=\sqrt{h\ell/(200n)}\),

\[
R_{i,\pm}=\frac1{2h},\qquad
S_{i,\pm}(z)=\frac{1\pm\xi z_i}{2h},
\qquad
\|R-S(z)\|_1=\frac{\xi}{h}\sum_{i=1}^h|z_i|.
\]

Here \(z_i\in[-1,1]\) is a normalized contrast. The target averages absolute contrasts, just as half-capacity value does in the example.

Moment matching cancels low-order terms in the count-likelihood comparison. The remaining tail is small, so the two sample laws are hard to distinguish.

Independent contrasts concentrate the targets; their squared mean separation has order \(k/[n\log(ek)]\). Accurate estimation would distinguish the sample laws, contradicting the testing bound.

@informal thm:capacity-active-lower: Under independent sampling and fixed \(0<\epsilon<1/2\), every half-capacity estimator has worst-case risk at least \(c_\epsilon\min\{1,d/[n\log(ed)]\}\) for all \(n\ge1,d\ge2\), even with positive effects, binding capacity, and \(V_1(P)=1/2\).

Every symmetric budget interval contains half capacity, so this coordinate supplies the curve lower bound.

---

## Open questions

- How does risk behave at budgets that shrink with sample size?
- Can we construct adaptive simultaneous confidence bands and control welfare regret of estimated allocations?
- How many Monte Carlo draws suffice to approximate the exact conditional average while preserving its guarantee?
- What changes when covariate cells are learned from data or treatment has multiple arms?

---

## Takeaways

- Under independent sampling, consistency, conditional exchangeability, and fixed overlap, the entire capacity curve has minimax squared largest-error risk of order \(\min\{1,d/[n\log(ed)]\}\), allowing rare cells and exact ties.
- Endpoint-sensitive approximation reduces bias; factorial powers estimate polynomials without plug-in bias. Common positive smoothing controls price-path movement, and the maximal inequality aggregates independent cell paths uniformly.
- Price minima transfer process accuracy to every budget. Half capacity carries the matching difficulty through absolute contrasts, even when full-capacity value is constant.

---

## Appendix: Matched curve minimax frontier

The complete result matches upper and lower risk bounds on every symmetric budget interval.

@formal thm:matched-curve-frontier

---

## Appendix: Uniform budget-curve upper bound

The specified Jackson–factorial estimator attains the simultaneous curve-risk upper bound.

@formal thm:curve-upper

---

## Appendix: Capacity-active risk lower bound

Every half-capacity estimator faces the lower bound even with positive effects and fixed full-capacity value.

@formal thm:capacity-active-lower

---

## Appendix: Open questions

- Risk at budgets that shrink with sample size.
- Adaptive simultaneous confidence bands and welfare regret of estimated allocations.
- Computational guarantees for approximating the exact conditional average, including Monte Carlo draw counts and approximation error.
- Covariate alphabets learned from data and allocation across multiple treatment arms.
