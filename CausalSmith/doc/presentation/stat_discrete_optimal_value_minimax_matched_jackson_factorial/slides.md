# Estimating the Value of Optimal Treatment

We estimate the average outcome attainable by choosing the better treatment in each covariate group, even when there are many groups.

---

## Motivation

A practitioner wants to know how much treatment tailored to observed characteristics could achieve.

Let \(x\) index \(d\) covariate groups, \(p_x\) be a group’s population share, and \(\mu_{ax}\) its outcome mean under treatment \(a\in\{0,1\}\).

\[
\Psi(\mathbb P)=\Psi(\mathbf q)
:=
\sum_{x=1}^d p_x\max_{a\in\{0,1\}}\mu_{ax}.
\]

This averages the better treatment’s mean across groups. Here \(\mathbb P\) is the observed distribution and \(\mathbf q\) its treatment–outcome probability table.

Zeng et al. (2024) study linear treatment-specific means with categorical covariates. Maximizing within each group adds the difficulty of deciding which mean is larger.

---

## Standard approach

Estimate both arm means, select the larger estimate, and average.

\[
\widehat V_{n,d}^{\mathrm{ER}}
=
\sum_{x=1}^d \widehat p_x \max_{a\in\{0,1\}}\widehat\mu_{ax}.
\]

Here \(\widehat p_x\) is the sample group share; \(\widehat\mu_{ax}\) is successes divided by observations in group \(x\), arm \(a\).

- Near a tie, maximizing selects positive sampling noise.
- Across many groups, these errors accumulate.
- Small arm counts also make the estimated means unstable.

Jiao et al. (2018) study the closest statistical analogue: sums of absolute differences between categorical probabilities.

How accurately can we estimate the optimal value when \(d\) grows with sample size \(n\)?

---

## Key idea

Approximate each group’s maximum contribution by a local polynomial, then estimate the polynomial’s powers without moment bias.

Our **Jackson factorial estimator** combines a polynomial formed by weighted averaging with count statistics that estimate its terms unbiasedly.

@informal thm:matched-minimax-frontier: For independent, identically distributed binary-treatment, binary-outcome data with fixed overlap, an explicit estimator attains minimax squared-risk order \(\min\{1,d/[n\log(ed)]\}\) for every \(n\geq1,d\geq2\).

“Minimax” means the smallest worst-case mean-squared error over the model.

The method estimates the value without first choosing whichever arm looks better in the sample.

---

## Example

Take equally common groups and balanced treatment assignment:

\[
p_x=\frac1d,
\qquad
\pi_x=\frac12,
\qquad
\mu_{1x}=\frac{1+\theta_x}{2},
\qquad
\mu_{0x}=\frac{1-\theta_x}{2},
\]

Here \(\pi_x\) is the probability of treatment \(1\), and \(\theta_x\in[-1/2,1/2]\) is the treatment-effect contrast.

\[
\Psi\{\operatorname{Obs}(P_\theta^{\mathrm{dense}})\}
=
\frac12+\frac{1}{2d}\sum_{x=1}^d|\theta_x|.
\]

Here \(P_\theta^{\mathrm{dense}}\) denotes this potential-outcome model; \(\operatorname{Obs}\) extracts its observed distribution.

The target is one half plus an average absolute contrast. At \(\theta_x=0\), an empirical absolute contrast turns sampling noise into an apparent treatment benefit.

The construction must estimate this absolute-value corner accurately.

---

## Model

Observe \(n\) independent, identically distributed triples \(O_i=(X_i,A_i,Y_i)\): categorical covariates, binary treatment, and binary outcome.

Each group has four probabilities \(q_{ay,x}=\mathbb P(X=x,A=a,Y=y)\):

\[
q_{a1,x}
=
p_x\pi_x^a(1-\pi_x)^{1-a}\mu_{ax},
\qquad
q_{a0,x}
=
p_x\pi_x^a(1-\pi_x)^{1-a}(1-\mu_{ax}),
\]

These give success and failure probabilities for each arm. Write \(q_x=(q_{00,x},q_{01,x},q_{10,x},q_{11,x})\).

**Fixed overlap** guarantees population representation of both arms in every occupied group:

\[
\epsilon\leq \pi_x \leq 1-\epsilon ,
\]

The constant \(0<\epsilon<1/2\) stays fixed. Group shares and propensities are unknown; exact ties are allowed.

Our balanced example satisfies this condition.

---

## Causal interpretation

Let \(Y(a)\) be the potential outcome under arm \(a\), and let \(P\) govern observed and potential outcomes.

\[
V^\star(P)
=
E_P\!\left[
\max_{a\in\{0,1\}}
E_P\{Y(a)\mid X\}
\right].
\]

This is the outcome attainable by choosing the better potential-outcome mean within each group.

- **Consistency:** \(Y=Y(A)\); we observe the potential outcome under the received treatment.
- **Conditional exchangeability:** \(Y(a)\perp A\mid X\); within a group, assignment carries no further information about that potential outcome.

Together with fixed overlap, these give

\[
V^\star(P)=\Psi\{\operatorname{Obs}(P)\}.
\]

Every observed law in our model also has such a causal completion: draw Bernoulli potential outcomes with means \(\mu_{ax}\), draw treatment independently of them given \(X\), and set \(Y=Y(A)\).

Thus all observed distributions used for the statistical lower bound remain available under the causal assumptions.

---

## Main result

Let \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) be the binary observed model with fixed overlap, \(\mathfrak R_{n,d,\epsilon}\) its minimax squared risk, and \(L_d=\log(ed)\).

With universal tuning, the Jackson factorial estimator \(\widehat V_{n,d}^{\mathrm{JF}}\) satisfies

\[
c_\epsilon \min\left\{1,\frac{d}{nL_d}\right\}
\leq
\mathfrak R_{n,d,\epsilon}
\leq
\sup_{\mathbb P\in\mathcal D_{d,\epsilon}^{\mathrm{obs}}}
E_{\mathbb P^{\otimes n}}\!\left[
  \left(\widehat V_{n,d}^{\mathrm{JF}}-\Psi(\mathbb P)\right)^2
\right]
\leq
C_\epsilon \min\left\{1,\frac{d}{nL_d}\right\}.
\]

Here \(\mathbb P^{\otimes n}\) denotes \(n\) independent observations; positive constants \(c_\epsilon,C_\epsilon\) depend only on overlap.

For every \(n\geq1,d\geq2\), the estimator’s worst-case squared error matches the difficulty facing every estimator. Causal minimax risk is identical because the observed distributions and identified targets coincide.

In our example, this uniformly bounds error in estimating the average absolute contrast, including exact zeros.

---

## Stable cell contributions

We approximate a function of observable probabilities, protecting the unknown arm denominators first.

For a candidate table \(u\), let \(s_a(u)=u_{a0}+u_{a1}\) be arm mass and \(s(u)=s_0(u)+s_1(u)\) total mass.

\[
g_{a,\epsilon}(u)
:=
\frac{s(u)u_{a1}}{\max\{s_a(u),\epsilon s(u)\}},
\qquad a\in\{0,1\},
\]

This computes an arm’s contribution with a denominator bounded below by its overlap share. Let \(\bar f_\epsilon(u)=\max_a g_{a,\epsilon}(u)\), with value zero at the origin.

\[
\Psi(\mathbb P)=\sum_{x=1}^d \bar f_\epsilon(q_x).
\]

On population tables satisfying overlap, this preserves the target exactly. On other nonnegative tables, it controls sensitivity to changes in the four probabilities.

We can therefore approximate on rectangles that include noisy tables outside the overlap restriction.

---

## Independent count tables

A random sample size makes counts in distinct treatment–outcome categories independent.

Draw an auxiliary inclusion count:

\[
M\sim\operatorname{Pois}(n/4).
\]

Here \(M\) determines how many observations enter the randomized construction. Mark each included observation with an independent fair coin: one outcome sends it to the pilot, the other to evaluation.

In the uncapped experiment, Poisson sampling and splitting produce mutually independent counts \(N'_{\jmath,x}\) and \(N_{\jmath,x}\), each with mean \(m q_{\jmath,x}\), where \(m=n/8\).

The index \(\jmath\in\mathcal J\) labels the four treatment–outcome coordinates.

The fixed-sample implementation uses the first \(M\) of the \(n\) observations when \(M\leq n\), and sets its randomized output to zero otherwise. We average out this randomization after constructing the estimate.

---

## Pilot localization

The pilot locates the unknown table; the independent evaluation counts estimate the polynomial.

\[
c_{\jmath,x}
=
\frac{N'_{\jmath,x}}{m},
\qquad
h_{\jmath,x}
=
H_0
\left\{
\sqrt{\frac{c_{\jmath,x}L_d}{m}}
+
\frac{L_d}{m}
\right\}.
\]

Here \(c_{\jmath,x}\) is the pilot frequency; \(h_{\jmath,x}\) is its uncertainty width, inflated by a fixed constant \(H_0\).

Use endpoints \(\ell_{\jmath,x}=\max\{0,c_{\jmath,x}-h_{\jmath,x}\}\) and \(u_{\jmath,x}=c_{\jmath,x}+h_{\jmath,x}\). Their product forms rectangle \(Q_x\).

Let \(b_x\) and \(r_x\) be its coordinate centers and radii.

The square-root term adapts to count noise. The additive term keeps the rectangle useful even when a pilot count is zero.

---

## A finite polynomial

Jackson smoothing is weighted averaging that retains only finitely many trigonometric terms.

- Write each rectangle coordinate as its center plus its radius times the cosine of an angle.
- Average over angle shifts using normalized weights \(J_{K_d}(t)=c_{K_d}\{\sin(K_dt/2)/\sin(t/2)\}^{4}\). Here \(t\) is a shift and \(c_{K_d}\) normalizes the weights.
- This kernel is a finite sum of sine and cosine terms. Averaging removes frequencies above \(2(K_d-1)\).
- The result is even in each angle. Each retained cosine term is a polynomial in that angle’s cosine.

Returning to the original coordinates therefore gives a finite polynomial \(P_{x,K_d}\) approximating \(\bar f_\epsilon\).

Use order \(K_d=\max\{2,\lfloor\kappa L_d\rfloor\}\), with a sufficiently small fixed \(\kappa>0\). Each coordinate degree is at most \(2(K_d-1)\).

---

## Accuracy near boundaries

The approximation is especially accurate near a rectangle face.

\[
\left|P_{x,K}(v)-\bar f_\epsilon(v)\right|
\le
C_\epsilon
\sum_{\jmath\in\mathcal J}
\left\{
\frac{\sqrt{(v_{\jmath}-\ell_{\jmath,x})(u_{\jmath,x}-v_{\jmath})}}{K}
+
\frac{r_{\jmath,x}}{K^2}
\right\}.
\]

This bounds the approximation error at a table \(v\in Q_x\); \(K=K_d\).

The first term depends on distances to the two faces in each coordinate. The second depends on the coordinate radius.

At a zero coordinate on the zero face, the first term vanishes. Only radius divided by \(K^2\) remains.

This matters because many groups may be empty: their additive pilot widths must not create a large aggregate bias.

---

## Unbiased polynomial terms

Inserting empirical frequencies into powers creates moment bias. Falling factorials remove it.

For an evaluation count \(N\), pilot-chosen center \(z\), and nonnegative integer power \(h\), define

\[
U_h(N;z)
=
\sum_{t=0}^h
\binom ht
(-z)^{h-t}
\frac{(N)_t}{m^t}.
\]

Here \((N)_t\) multiplies \(t\) descending factors; \((N)_0=1\). Conditional on the pilot, \(U_h\) has expectation \((q-z)^h\), where \(q\) is the count’s population probability.

Expand \(P_{x,K_d}(v)\) in centered, radius-normalized powers. Denote its coefficients by \(\gamma_{x,\alpha}\); \(\alpha\) records the four powers.

| Polynomial term | Count replacement |
|---|---|
| \(\gamma_{x,\alpha}\prod_{\jmath}((v_{\jmath}-b_{\jmath,x})/r_{\jmath,x})^{\alpha_{\jmath}}\) | \(\gamma_{x,\alpha}\prod_{\jmath}U_{\alpha_{\jmath}}(N_{\jmath,x};b_{\jmath,x})/r_{\jmath,x}^{\alpha_{\jmath}}\) |

Independent evaluation coordinates make each product unbiased. Summing gives the cell estimate \(Z_x\), whose conditional expectation is \(P_{x,K_d}(q_x)\). The constant term is included automatically because \(U_0=1\).

---

## The example revisited

In the balanced example, the observable probabilities are affine functions of the contrast:

- \(q_{11,x}=q_{00,x}=(1+\theta_x)/(4d)\).
- \(q_{10,x}=q_{01,x}=(1-\theta_x)/(4d)\).

Restrict the actual local Jackson polynomial to this table. It becomes a polynomial in \(\theta_x\) approximating the cell contribution \((1+|\theta_x|)/(2d)\).

Its powers are estimated through counts rather than through an estimated absolute contrast.

For example, a term containing \((q_{11,x}-b_{11,x})^2\) uses

\(U_2(N_{11,x};b_{11,x})=N_{11,x}(N_{11,x}-1)/m^2-2b_{11,x}N_{11,x}/m+b_{11,x}^2.\)

Its conditional expectation is exactly that centered square. Using \(N_{11,x}^2\) instead would add Poisson sampling variance.

At a tie, the approximation has controlled error, while factorial replacement avoids adding the moment bias of empirical powers.

---

## Aggregate bias

Unbiased polynomial evaluation leaves approximation error as the principal bias.

After clipping the cell estimate to limit extreme evaluations, the resulting statistic \(T_x^{\mathrm{JF}}\) satisfies

\[
\left|
\mathbb E T_x^{\mathrm{JF}}-\bar f_\epsilon(q_x)
\right|
\le
C_\epsilon
\left\{
\sqrt{\frac{p_x}{mL_d}}+\frac{1}{mL_d}
\right\},
\]

This bounds each cell’s bias by its population share \(p_x\). The first term comes from count uncertainty divided by logarithmic approximation order; the second uses the improved accuracy at zero faces.

Since shares sum to one, \(\sum_x\sqrt{p_x}\leq\sqrt d\).

Thus the square-root terms aggregate on the scale \(\sqrt{d/(mL_d)}\), and the additive terms on the scale \(d/(mL_d)\). In the polynomial branch, \(n\geq d/L_d\) and \(m=n/8\), so squared aggregate bias is at most a constant times \(d/(nL_d)\).

For equally common groups, all \(d\) square-root contributions are equal.

---

## Degree and variability

Higher powers cost variance, so logarithmic degree needs a small multiplier.

The coefficient bound is
\(\sum_{\alpha\in\mathcal A_x}|\gamma_{x,\alpha}|\leq A^K(1+\epsilon^{-1})\sum_{\jmath\in\mathcal J}r_{\jmath,x}\),
where \(\mathcal A_x\) indexes the polynomial terms and \(A\) is universal.

Dividing centered powers by the pilot radii measures them on their uncertainty scale. With \(K=K_d\) and sufficiently small \(\kappa\), coefficient and factorial-moment growth give

\[
\operatorname{Var}(T_x^{\mathrm{JF}})
\le
C_\epsilon d^{1/16}
\left\{
\frac{p_x L_d}{m}+\frac{L_d^2}{m^2}
\right\},
\]

This is the resulting variance bound for each clipped cell estimate.

Cells are independent in the uncapped Poisson experiment. Summing replaces the shares by one and contributes \(d\) copies of the second term.

For \(n\geq d/L_d\), the resulting variance is at most a constant times \(d/(nL_d)\): the available factor \(d\) absorbs \(d^{1/16}\) and the logarithmic factors.

---

## Fixed-sample estimator

Clip each \(Z_x\) around the pilot-based contribution to limit extreme count statistics. Sum the clipped cells and project onto \([0,1]\), the range of the target, obtaining \(\widetilde V\).

Average over the auxiliary inclusion count and fair-coin split:

\[
\widehat V_{n,d}^{\mathrm{JF}}
=
E\!\left[
\widetilde V
\mid
O_1,\ldots,O_n
\right],
\]

This returns a deterministic estimator from the original \(n\) observations. Conditional averaging cannot increase squared error; the inclusion-count safeguard preserves the risk order.

- For \(d<D_0\), use the empirical-ratio estimator.
- For \(d\geq D_0\) and \(n<d/L_d\), output \(1/2\).
- Otherwise, use the polynomial construction.

Here \(D_0\) is a fixed alphabet cutoff. Bias and variance bounds establish the upper side of the main result.

---

## Moment matching

Why can no estimator do better? Return to the balanced example with sufficiently large \(d\) and \(n>d^2\).

Choose \(K=K_d^{\mathrm{lb}}=2\lceil4L_d\rceil\), and two symmetric probability distributions \(\nu_{0,K},\nu_{1,K}\) on \([-1,1]\) whose moments agree through degree \(K\), but

\[
\int_{-1}^1 |t|\,d\nu_{1,K}(t)
-
\int_{-1}^1 |t|\,d\nu_{0,K}(t)
=
2E_K .
\]

Here \(E_K\) is the smallest uniform error of a degree-\(K\) polynomial approximation to \(|t|\). The approximation input has \(E_K\asymp1/K\).

Draw contrasts independently from one distribution and multiply them by amplitude \(a_{n,d}\), with \(a_{n,d}^2=K_d^{\mathrm{lb}}d/(128n)\).

Matching moments hides the low-order likelihood terms while leaving different average absolute contrasts. This approximation–moment connection follows Cai and Low (2011).

---

## Quantitative lower bound

The two contrast priors have mean-value separation

\(\Delta_{n,d}^{\mathrm{dense}}=a_{n,d}E_{K_d^{\mathrm{lb}}}.\)

Here \(\Delta_{n,d}^{\mathrm{dense}}\) measures how far apart their mean optimal values are.

Amplitude squared is proportional to \(K_d^{\mathrm{lb}}d/n\); approximation error is proportional to \(1/K_d^{\mathrm{lb}}\). Therefore,

\((\Delta_{n,d}^{\mathrm{dense}})^2\asymp \frac{K_d^{\mathrm{lb}}d}{n}\frac{1}{(K_d^{\mathrm{lb}})^2}=\frac{d}{nK_d^{\mathrm{lb}}}.\)

The observation mixtures have total-variation distance at most \(1/16\): no event’s probability differs by more than that amount. Under either prior, the target lies within \(\Delta_{n,d}^{\mathrm{dense}}/4\) of its own mean with probability at least \(7/8\).

An estimate much more accurate than this separation would distinguish two observation distributions that are nearly indistinguishable. Consequently,

\[
c_\epsilon(\Delta_{n,d}^{\mathrm{dense}})^2
\leq
\mathfrak R^{\mathrm{Pois}}_{2n,d,\epsilon},
\qquad
c_\epsilon\frac{d}{nK_d^{\mathrm{lb}}}
\leq
\mathfrak R^{\mathrm{Pois}}_{2n,d,\epsilon},
\]

The right side is minimax risk with Poisson sample size of mean \(2n\). Using the first \(n\) observations when available transfers this obstruction to fixed samples; the shortfall probability is negligible here. Since \(K_d^{\mathrm{lb}}\) is proportional to \(L_d\), this gives the required logarithmic lower bound.

---

## Remaining sample-size regimes

A categorical-distance problem supplies the lower bound outside the dense construction.

For probability vectors \(\mathbf P,\mathbf Q\) over the groups, encode
\(q_{11,x}=q_{00,x}=P_x/4\) and \(q_{10,x}=q_{01,x}=Q_x/4\). This has propensity \(1/2\) and

\[
\Psi(\mathbb P)=\frac12+\frac14\sum_{x\in[d]} |P_x-Q_x|.
\]

The sum is their \(L_1\) distance: total absolute probability difference.

An exact randomized transformation converts paired draws from \(\mathbf P,\mathbf Q\) into our observed triples. A more accurate value estimator would therefore give a more accurate distance estimator.

| Range | Source of the lower bound |
|---|---|
| \(n<d/L_d\) | Distance estimation gives a constant obstruction. |
| \(d/L_d\leq n\leq d^2\) | The distance bound gives the required \(d/(nL_d)\) scale. |
| \(n>d^2\), large \(d\) | Dense moment matching gives that scale. |
| Bounded \(d\) | The lower bound has the usual \(n^{-1}\) scale. |

Together these cover every \(n\geq1,d\geq2\).

---

## Further results

Keep overlap fixed and let \(d_n\geq2\) denote alphabet size as sample size grows.

- Uniform consistency is possible exactly when \(d_n=o\{n\log(en)\}\).
- Parametric squared-risk order \(n^{-1}\) is possible exactly when \(d_n=O(1)\).
- Both boundaries apply to observed-value and identified causal-value estimation.

@informal thm:consistency-and-parametric-boundaries: For independent, identically distributed binary data with fixed overlap and any sequence \(d_n\geq2\), observed and causal minimax risks vanish iff \(d_n=o\{n\log(en)\}\), and have \(n^{-1}\) order iff \(d_n=O(1)\).

---

## Open questions

Along sequences with \(d\to\infty\) and \(d/\{n\log(ed)\}\to0\), does the normalized risk

\[
\frac{n\log(ed)}{d}\mathfrak R_{n,d,\epsilon}
\]

converge to a finite positive limit?

This divides out the established risk order and asks for its leading constant.

Can an estimator attain that constant by rescaling local tables according to count noise and optimizing polynomial bias and variance?

---

## Takeaways

- Under consistency, conditional exchangeability, and fixed overlap, the attainable causal value equals the population average of the better arm’s conditional mean.
- Local polynomial approximation controls the treatment-effect corner; factorial counts estimate polynomial terms without moment bias. Accuracy near zero faces and a carefully chosen degree let the errors aggregate safely.
- The explicit estimator attains minimax squared-risk order \(\min\{1,d/[n\log(ed)]\}\). Moment matching and categorical-distance comparisons show why every estimator faces the same difficulty.

---

## Appendix: Jackson factorial risk bound

Universal tuning gives a uniform finite-sample squared-risk upper bound for the explicit estimator.

@formal thm:jackson-factorial-upper

---

## Appendix: Global minimax lower bound

Every estimator faces the same risk order somewhere in the fixed-overlap observed model.

@formal thm:all-estimator-lower

---

## Appendix: Matched minimax frontier

The constructive upper bound and all-estimator lower bound match, and causal minimax risk equals observed minimax risk.

@formal thm:matched-minimax-frontier

---

## Appendix: Consistency and parametric boundaries

Alphabet growth determines exactly when uniform consistency and parametric squared-risk order are possible.

@formal thm:consistency-and-parametric-boundaries
