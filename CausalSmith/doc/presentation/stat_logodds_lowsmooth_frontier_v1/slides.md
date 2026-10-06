# Honest Inference for Causal Log Odds

The size of a treatment effect determines how much a rough baseline risk limits the precision of a valid confidence interval.

---

## Motivation

We observe a covariate \(X\), binary treatment \(A\), and binary outcome \(Y\).

A practitioner wants an interval for \(\theta\): the same treatment–control difference in conditional log odds at every covariate value.

- Baseline outcome risk can vary sharply with \(X\).
- Treatment assignment can vary more smoothly.
- Precision may depend on whether the effect is close to zero.

Tan (2019) shows that proximity to zero changes efficiency comparisons for logistic coefficient estimation.

How does proximity to zero change attainable precision when baseline risk is rough?

---

## Research question

A standard approach estimates nuisance functions, solves an adjusted score equation, and reports a normal confidence interval.

Besides baseline log odds, the score uses a treatment probability conditional on the outcome: \(P(A=1\mid X=x,Y=y)\), for a fixed outcome value \(y\).

This function centers the treatment part of the adjusted score within that outcome stratum. The propensity \(P(A=1\mid X=x)\) instead averages over outcomes.

Liu et al. (2021) obtain root-\(n\) normal inference under their regularity conditions, uniform consistency, and \(L^2\) errors \(o_P(n^{-1/4})\) for both nuisance fits.

Our low-smoothness class does not guarantee those conditions. Remaining approximation bias must enter the confidence bounds.

**How short can a 90% interval be, including near zero effect, while covering throughout this class?**

---

## Key idea

Homogeneity recovers the effect from an observable numerator and denominator.

Estimate their integrated products separately, include approximation bias in both confidence bounds, and invert them together.

Under known uniform scalar design and our bounded homogeneous logistic model, optimal expected length has profile

\[
n^{-\min\{1/2,\,2(\alpha+\beta)/(2\alpha+2\beta+1)\}}
+r\,n^{-4\beta/(4\beta+1)}.
\]

Here \(n\) is sample size. Public exponents \(\alpha,\beta\) measure propensity and baseline-risk smoothness, with \(0<\beta<1/4\) and \(\beta<\alpha\le1\).

The radius \(r\in[0,1/2]\) bounds effect magnitude where length is evaluated.

Numerator uncertainty remains at zero effect; denominator uncertainty contributes in proportion to effect size. One interval achieves this profile across all radii.

---

## Example

Consider the fair-treatment null law \(P_{\mathrm{null}}\): uniform \(X\), treatment probability one half, and both arm risks one half.

\[
e(P_{\mathrm{null}},x)=\mu_0(P_{\mathrm{null}},x)
=\mu_1(P_{\mathrm{null}},x)=\frac12,
\qquad
g(P_{\mathrm{null}},x)=\nu(P_{\mathrm{null}},x)
=\theta(P_{\mathrm{null}})=0,
\]

Here \(e\) is treatment probability; \(\mu_0,\mu_1\) are control and treated risks; \(g,\nu\) are treatment and control-risk log odds.

Our observable coordinates give \(C(P_{\mathrm{null}})=0\) and \(S(P_{\mathrm{null}})=1/16\). The recovered effect is \(\theta(P)=\log\{1+C(P)/S(P)\}\).

When the numerator is zero, changing the denominator leaves the recovered effect at zero.

Numerator sampling uncertainty still remains.

---

## Model

The sample \(\mathcal O=(O_1,\ldots,O_n)\) contains independent records \(O_i=(X_i,A_i,Y_i)\) from law \(P\). The scalar covariate has known uniform law \(\lambda\) on \([0,1]\).

Write \(e(P,x)=P(A=1\mid X=x)\) and \(\mu_a(P,x)=P(Y=1\mid A=a,X=x)\).

Their relevant logits are

\[
g(P,x)=\operatorname{logit}\{e(P,x)\},
\qquad
\nu(P,x)=\operatorname{logit}\{\mu_0(P,x)\}.
\]

Logit means log odds; its inverse is \(\ell(t)=1/(1+\exp(-t))\).

The homogeneous outcome model is

\[
\mu_1(P,x)=\ell\{\nu(P,x)+\theta(P)\}
\qquad (x\in[0,1]),
\]

Baseline risk varies with \(x\), while \(\theta(P)\) is constant.

Under consistency and independence of treatment and potential outcomes conditional on \(X\), \(\theta(P)\) is a causal conditional log-odds contrast.

---

## Assumptions

Let \(\mathcal M(\alpha,\beta)\) contain laws satisfying the model and these restrictions.

- **Bounded effect:** \(|\theta(P)|\le1/2\).
- **Bounded logits:** \(\|g(P,\cdot)\|_\infty\le1\) and \(\|\nu(P,\cdot)\|_\infty\le1\), keeping treatment probabilities and outcome risks away from zero and one.
- **Public smoothness:** \([g(P,\cdot)]_\alpha\le2\) and \([\nu(P,\cdot)]_\beta\le2\).
- **Rougher baseline risk:** \(0<\beta<1/4\) and \(\beta<\alpha\le1\).

A Hölder bound \([f]_\gamma\le2\) means that moving from \(x\) to \(z\) changes \(f\) by at most \(2|x-z|^\gamma\).

In the fair null example, both logits vanish, so all envelope and smoothness bounds hold.

---

## Honest precision

“Honest” means at least 90% coverage at **every** law in \(\mathcal M(\alpha,\beta)\), for the given sample size. Let \(\mathcal A_n(\alpha,\beta)\) be these interval procedures.

Evaluate length on \(\mathcal M_r(\alpha,\beta)\), the smaller class where \(|\theta(P)|\le r\).

\[
J_n(\alpha,\beta;r)
=
\inf_{I\in\mathcal A_n(\alpha,\beta)}
\sup_{P\in\mathcal M_r(\alpha,\beta)}
E_{P^{\otimes n}\otimes\lambda}
\bigl|I(\mathcal O,U)\bigr|.
\]

This is the smallest worst-case expected interval length subject to ambient coverage.

The comparison allows an independent uniform randomization seed \(U\); \(|I|\) means interval length.

Even at \(r=0\), coverage remains required for all effects in the ambient model.

---

## Main result

@informal thm:full-honest-frontier-answer: Under our bounded homogeneous model, known uniform design and public exponent conditions, one radius-independent interval attains the sharp expected-length profile for every \(n\ge1\) and \(r\in[0,1/2]\), with global 90% coverage.

\[
J_n(\alpha,\beta;r)\asymp
n^{-\min\{1/2,\,2(\alpha+\beta)/(2\alpha+2\beta+1)\}}
+r n^{-4\beta/(4\beta+1)}.
\]

The symbol \(\asymp\) means matching upper and lower bounds with positive absolute constants, uniform over sample sizes, permitted exponents, and radii.

Call the numerator exponent \(\mathsf a(\alpha,\beta)\) and denominator exponent \(\mathsf b(\beta)\).

At \(r=0\), optimal worst-case length has only the numerator contribution. It reaches order \(n^{-1/2}\) when \(\alpha+\beta\ge1/2\).

Every honest procedure, including a randomized one, faces the matching lower bound.

---

## Observable coordinates

The numerator is average conditional treatment–outcome covariance:

\[
C(P)
=
E_P[AY]
-
\int_0^1
E_P[A\mid X=x]E_P[Y\mid X=x]\,dx,
\]

The denominator multiplies conditional treated-failure and control-success probabilities:

\[
S(P)
=
\int_0^1
E_P[A(1-Y)\mid X=x]
E_P[(1-A)Y\mid X=x]\,dx.
\]

The common conditional odds multiplier factors out of these integrals:

\[
C(P)=\bigl(\exp\{\theta(P)\}-1\bigr)S(P),
\qquad
\theta(P)=\log\!\left(1+\frac{C(P)}{S(P)}\right),
\]

Thus two observable integrated products identify the effect. The bounded model guarantees \(S(P)\ge s_0=1/512\), keeping division stable.

---

## Projected products

Estimate the integrated products directly, using distinct-record pairs:

\[
\mathbb U_{n,k}(W,V)
=
\frac{1}{n(n-1)}
\sum_{\substack{1\le i,j\le n\\ i\ne j}}
H_k(X_i,X_j)W(O_i)V(O_j).
\]

Here \(W,V\) are bounded functions of a record; \(k\) is the number of retained cosine modes; \(H_k\) is their projection kernel under uniform design.

Distinct records supply independent factors. The kernel weights recover the integral of the product of their projected conditional means.

McGrath and Mukherjee (2026) establish the known-design covariance precedent: product projection bias and variance controlled even when the projection rank exceeds sample size.

Why does estimating a product require less precision than recovering both entire functions?

---

## Product bias

Let \(w(x)=E_P[W\mid X=x]\), \(v(x)=E_P[V\mid X=x]\), and let \(\Pi_k\) retain the first \(k\) cosine modes.

\[
\langle w,v\rangle_{L^2(\lambda)}
-
E_P\mathbb U_{n,k}(W,V)
=
\langle w-\Pi_k w,v-\Pi_k v\rangle_{L^2(\lambda)},
\]

The inner product integrates a product over the uniform design.

**Bias is the product of two approximation errors.** Orthogonality removes terms involving only one projection residual.

Retaining more modes reduces this bias, with sampling cost bounded by

\[
\operatorname{Var}_P\{\mathbb U_{n,k}(W,V)\}
\le
\frac4n+\frac{2k}{n(n-1)}.
\]

The first term is ordinary sampling variance; the second is the cost of increasing resolution.

---

## Coordinate estimates

Apply the pair statistic to the binary quantities defining each coordinate:

\[
\widehat C_n
=\frac1n\sum_{i=1}^n A_iY_i-\mathbb U_{n,k_C}(A,Y),\qquad
\widehat S_n
=\mathbb U_{n,k_S}\bigl(A(1-Y),(1-A)Y\bigr),
\]

The ranks \(k_C,k_S\) are fixed before sampling from \(n,\alpha,\beta\).

- \(\widehat C_n\) subtracts a projected product from the treated-success mean.
- \(\widehat S_n\) estimates the product of treated-failure and control-success probabilities.

For the numerator, the two conditional means have smoothness \(\alpha\) and \(\beta\).

For the denominator, both conditional means have smoothness \(\beta\).

These different products require different resolutions.

---

## Separate resolutions

Numerator approximation bias is bounded at scale \(k_C^{-(\alpha+\beta)}\); denominator bias at scale \(k_S^{-2\beta}\).

Balancing each bias against the rank-dependent sampling error gives

\[
R_C=n^{2/(2\alpha+2\beta+1)},\qquad
R_S=n^{2/(4\beta+1)}.
\]

Here \(R_C,R_S\) are target resolutions; the construction selects integer ranks within a factor of three of them.

Because \(\alpha>\beta\), the denominator needs a larger rank.

The resulting error scales are \(n^{-\mathsf a(\alpha,\beta)}\) for the numerator and \(n^{-\mathsf b(\beta)}\) for the denominator.

All tuning uses \(n,\alpha,\beta\), without an effect radius.

---

## Confidence bounds

For \(n\ge2\), set \(s=\alpha+\beta\) and use the variance envelope \(V_n(k)=10/n+4k/\{n(n-1)\}\).

Add approximation bias to sampling uncertainty:

\[
b_C=8k_C^{-s}+\sqrt{20V_n(k_C)},
\qquad
b_S=25k_S^{-2\beta}+\sqrt{20V_n(k_S)}.
\]

Here \(b_C,b_S\) are the numerator and denominator confidence radii.

Chebyshev’s inequality bounds each coordinate’s failure probability by \(1/20\). A union bound gives simultaneous coordinate coverage of at least 90%.

Keeping approximation bias in the confidence bounds secures coverage without requiring it to vanish relative to sampling error.

---

## Joint inversion

Set \(c_\pm=\widehat C_n\pm b_C\) and \(s_\pm=\operatorname{clip}_{[s_0,1]}(\widehat S_n\pm b_S)\).

Clipping truncates values to a known range, keeping denominators positive and effects within their envelope.

For candidate coordinates \(c,d\), define

\[
F(c,d)=
\log\!\left(
\operatorname{clip}_{[\exp(-1/2),\exp(1/2)]}(1+c/d)
\right),
\]

Its minimum and maximum over the confidence rectangle occur at corners:

\[
L=\min\{F(c_-,s_-),F(c_-,s_+)\},
\qquad
R=\max\{F(c_+,s_-),F(c_+,s_+)\}.
\]

The interval \([L,R]\) therefore covers whenever both coordinate bounds cover.

The delivered rational endpoints enclose \([L,R]\), adding at most \(2/n\) to length. At \(n=1\), return \([-1/2,1/2]\).

---

## Effect-sensitive length

The inversion width satisfies, on every sample,

\[
R-L
\le
\mathsf L_{\mathrm{sens}}b_C
+
\mathsf H_{\mathrm{sens}}b_S(|\widehat C_n|+b_C).
\]

The positive constants \(\mathsf L_{\mathrm{sens}},\mathsf H_{\mathrm{sens}}\) depend only on the fixed denominator floor.

Numerator error enters directly. Denominator error is multiplied by numerator magnitude.

For \(|\theta(P)|\le r\), the odds identity and coordinate error bounds give expected numerator magnitude at most \(\exp(1/2)r+b_C\).

Expected length is consequently bounded by the numerator rate plus \(r\) times the denominator rate, including samples where coordinate coverage fails.

At the fair null, \(C=0\): observed numerator uncertainty remains, while denominator sensitivity shrinks with it.

---

## Hidden signs

For optimality, we construct different effects with nearly indistinguishable sample distributions.

Partition \([0,1]\) into \(k\) equal cells. Within a cell, let \(u\in[0,1]\) denote relative position and define

\[
Z_u=\epsilon_0\cos(\pi u/2)+\epsilon_1\sin(\pi u/2).
\]

The independent fair signs \(\epsilon_0,\epsilon_1\) belong to the cell’s endpoints. Adjacent cells share an endpoint sign, making the perturbation continuous.

The signs are drawn once for the entire sample. Their averages satisfy \(EZ_u=0\) and \(EZ_u^2=1\).

We match each family’s distribution for one record after averaging the signs.

Joint records can expose the difference when their covariates fall in the same or neighboring cells and share hidden signs.

---

## Numerator calibration

Use amplitudes \(\eta=\varepsilon k^{-\alpha}\), \(\zeta=\varepsilon k^{-\beta}\), with fixed small \(\varepsilon>0\). Both families share outcome margin \(m=1/2+\zeta Z_u\).

| Family | Treatment probability | Conditional covariance | Effect |
|---|---|---|---|
| \(P_{0,\sigma}\) | \(1/2+\eta qZ_u\) | \(0\) | \(0\) |
| \(P_{1,\sigma}\) | \(1/2-\eta qZ_u\) | \(\mathfrak c(32\eta\zeta,e_1,m)\) | \(32\eta\zeta\) |

Here \(\sigma\) collects endpoint signs; \(\mathfrak c(t,e,m)\) adds covariance while preserving margins and imposing odds ratio \(\exp(t)\).

The calibration chooses \(q=\mathfrak q(\eta,\zeta,u)\), near one, so

\[
E_{\mathbf s}\mathfrak c\!\left(
32\eta\zeta,\frac12-\eta\mathfrak q(\eta,\zeta,u)Z_u,
                 \frac12+\zeta Z_u\right)
=2\eta\zeta\mathfrak q(\eta,\zeta,u).
\]

Here \(E_{\mathbf s}\) averages the two signs. Reversing the propensity perturbation changes the average margin product from \(1/4+\eta\zeta q\) to \(1/4-\eta\zeta q\). The covariance restores exactly the difference.

Equal averaged margins and treated-success probabilities match all four cells. Every constituent retains its homogeneous effect and belongs to \(\mathcal M(\alpha,\beta)\).

---

## Numerator indistinguishability

Let \(Q_0,Q_1\) be the sample distributions obtained by averaging \(P_{0,\sigma}^{\otimes n},P_{1,\sigma}^{\otimes n}\) over signs.

Conditional on covariates, groups using disjoint signs factor independently. An isolated record contributes no discrepancy because of exact matching.

Pairs in the same or neighboring cells occur with probability at most \(3/k\). Bounding connected groups gives an effective pair count of order \(n^2/k\).

The discrepancy disappears if either perturbation amplitude is zero, leaving a product-amplitude contribution:

\[
\mathcal H^2(Q_0,Q_1)
\le
C_{\mathrm{mix}}\frac{n^2}{k}\eta^2\zeta^2,
\]

Here \(\mathcal H^2\) is squared Hellinger distance, a measure of distributional separation; \(C_{\mathrm{mix}}\) is an absolute constant. The bound requires \(n/k\le\kappa\), a fixed small occupancy threshold.

When \(\alpha+\beta\le1/2\), choosing \(k\) as a sufficiently large constant multiple of \(n^{2/(2\alpha+2\beta+1)}\) makes this distance at most \(1/100\), while preserving effect separation of order \(n^{-2(\alpha+\beta)/(2\alpha+2\beta+1)}\).

A constant-risk comparison supplies the \(n^{-1/2}\) floor.

---

## Averaging logistic risks

For the second comparison, keep treatment probability one half and let the homogeneous effect be \(t\in[0,1/4]\).

Write \(\mathsf G(t,\xi)=\exp(t)\xi/[1+\{\exp(t)-1\}\xi]\): the treated risk obtained by adding \(t\) to the log odds of baseline risk \(\xi\).

At a cell endpoint, baseline risk fluctuates between \(p_*+\delta\) and \(p_*-\delta\), where \(p_*=2/5\).

Define the comparator effect \(\mathsf T(t,\delta)\) to match their average treated risk:

\[
\frac{\mathsf G(t,p_*+\delta)+\mathsf G(t,p_*-\delta)}2
=\mathsf G(\mathsf T(t,\delta),p_*).
\]

With \(B_*=1+\{\exp(t)-1\}p_*\), its exact value is

\[
\mathsf T(t,\delta)
=t+
\log\left(1-\frac{\{\exp(t)-1\}\delta^2}{p_*B_*}\right)
-\log\left(1+\frac{\{\exp(t)-1\}\delta^2}{(1-p_*)B_*}\right).
\]

Symmetry cancels first-order changes in \(\delta\). Logistic curvature leaves a squared-amplitude change, multiplied by \(\exp(t)-1\).

The calibrated bounds are \(3t\delta^2\le t-\mathsf T(t,\delta)\le6t\delta^2\). The displacement vanishes at \(t=0\).

---

## Matching throughout each cell

Inside a cell, \(Z_u\) has four sign combinations. Endpoint matching alone would not give one comparator effect at every \(x\).

Choose a deterministic baseline \(p=\mathfrak p(t,\delta,u)\), close to \(2/5\), to satisfy the same matching equation throughout the cell.

| Law | Control risk | Treated risk |
|---|---|---|
| Sign-varying \(P_{t,\sigma}\) | \(p+\delta Z_u\) | \(\mathsf G(t,p+\delta Z_u)\) |
| Deterministic \(P_{*,t,\delta}\) | \(p\) | \(\mathsf G(\mathsf T(t,\delta),p)\) |

The exact calibration gives

\[
E_{\mathbf s}\mathsf G\!\left(
 t,\mathfrak p(t,\delta,u)+\delta Z_u\right)
=\mathsf G\!\left(\mathsf T(t,\delta),
                       \mathfrak p(t,\delta,u)\right).
\]

This matches treated risks after sign averaging. Control risks match because \(EZ_u=0\); fair treatment then matches all four observed cells.

The smooth calibration changes \(p\) by at most a constant times \(\delta^2\) and returns \(2/5\) at both endpoints. Thus adjoining cells fit continuously.

With \(\delta=\varepsilon k^{-\beta}\), both laws satisfy our smoothness bounds, with homogeneous effects \(t\) and \(\mathsf T(t,\delta)\).

---

## Coverage forces length

Let \(Q_t\) average the sign-varying sample laws. The same shared-sign argument gives

\[
\mathcal H^2\!\left(Q_t,P_{*,t,\delta}^{\otimes n}\right)
\le
C_{\mathrm{mix}}\frac{n^2}{k}\delta^4.
\]

Sign symmetry removes first-order amplitude changes; squaring the remaining discrepancy gives \(\delta^4\).

Choose \(k\) as a sufficiently large constant multiple of \(n^{2/(4\beta+1)}\), with \(\delta=\varepsilon k^{-\beta}\). The distance is at most \(1/100\). Set \(t=r/2\).

For both comparisons, this Hellinger bound gives total variation at most \(1/10\): probabilities of any sample event differ by at most \(1/10\).

Global 90% coverage therefore forces an interval to contain **both** effects with probability at least \(7/10\) under the evaluation mixture.

Expected length must include their separation:

- The numerator comparison forces the null contribution \(n^{-\mathsf a(\alpha,\beta)}\).
- The fair comparison forces \(r n^{-4\beta/(4\beta+1)}\), through displacement \(t\delta^2\).

Together they bound length below by a constant times the sum. Independent randomization does not change this argument.

---

## Open questions

- Unknown design and unknown smoothness: how should estimation and adaptation enter honest coverage?
- Higher-dimensional covariates and heterogeneous effects: what targets and precision profiles replace this scalar characterization?
- Practical calibration and computation: how short are these intervals at realistic sample sizes, and how can endpoint evaluation be optimized?

---

## Takeaways

- Homogeneity turns conditional log odds into an observable numerator–denominator identity.
- Separate projection ranks and explicit bias allowances deliver finite-sample 90% coverage under rough baseline risk.
- Exact calibration hides different homogeneous effects in nearly identical samples, establishing that numerator uncertainty and effect-scaled prognosis uncertainty are both unavoidable.

---

## Appendix: Full honest frontier

This statement gives the sharp all-radius expected-length comparison, finite-sample attainment, and the lower bound for every honest procedure.

@formal thm:full-honest-frontier-answer

---

## Appendix: Uniform honesty and length

This statement gives global 90% coverage and the effect-sensitive expected-length bound for the constructed interval.

@formal thm:finite-honest-upper
