# Better Precision in Multiarm Binary Experiments

Allocate according to the comparison weights, then cap a small adjustment toward zero to reduce worst-case squared error.

---

## Research question

A practitioner wants to compare several treatments using a binary outcome. Both allocation and estimation affect precision.

The natural approach chooses allocation probabilities to control the variance of an unbiased inverse-probability estimator.

- Sudijono et al. (2026) establish the sharp improvement from allowing bias for two binary arms.
- Hull (2026) studies optimal design and estimation for bounded two-arm outcomes.

For several binary arms, which design and estimator improve worst-case precision—and how large can the improvement be?

---

## Key idea

Assign units independently in proportion to the absolute comparison weights. Keep that allocation and shrink the estimate toward zero, capping the adjustment.

Binary outcomes provide two protections:

- Near zero, shrinkage removes noise.
- Away from zero, nonzero unit comparisons already reduce variance enough to pay for the adjustment.

@informal thm:universal-second-order-rate: For fixed \(K\geq2\), a fixed nonzero zero-sum contrast \(c\), and unrestricted binary schedules, capped shrinkage improves worst-case risk by at least \(C_0(c)\kappa_c n^{-4/3}\) for sufficiently large \(n\); optimal improvement has order \(n^{-4/3}\).

Here \(n\) is population size, \(K\) is the number of arms, and \(c\) contains the comparison weights. The benchmark constant is \(C_0(c)=(\sum_a|c_a|)^2/4\), and \(\kappa_c>0\) depends on the comparison.

---

## Example

Compare arm 1 with the average of arms 2 and 3: \(c^\dagger=(1,-1/2,-1/2)\).

Assign independently with probabilities \(q^\star=(1/2,1/4,1/4)\).

\[
Z_i=\operatorname{sign}(c^\dagger_{A_i})(2Y_i^{\mathrm{obs}}-1),
\qquad
\mu_i=t_{i,1}-\frac{t_{i,2}+t_{i,3}}{2}.
\]

Unit \(i\) receives arm \(A_i\); its observed outcome is \(Y_i^{\mathrm{obs}}=t_{i,A_i}\), where \(t_{i,a}\) is its binary potential outcome under arm \(a\).

The transformed observation \(Z_i\) is a sign with mean \(\mu_i\), the unit comparison. Its average estimates the population comparison \(\tau_{c^\dagger}(z)\), where \(z\) records all potential outcomes.

\[
\mathbb E_{\mathcal D^\star}\!\left[
\left\{\frac{1}{n}\sum_i Z_i-\tau_{c^\dagger}(z)\right\}^2
\,\middle|\, z\right]
=
\frac{1}{n}-\frac{1}{n^2}\sum_i \mu_i^2 .
\]

The expectation averages over independent assignment \(\mathcal D^\star\). Nonzero unit comparisons subtract variance from the \(1/n\) benchmark.

---

## Model and assumptions

The schedule \(z=(t_1,\ldots,t_n)\) records every unit’s potential outcomes across arms \(\mathcal A_K=\{1,\ldots,K\}\).

\[
L_c=\sum_{a\in\mathcal A_K}|c_a|,
\qquad
I_c=\left[-\frac{L_c}{2},\frac{L_c}{2}\right],
\qquad
\tau_c(z)=\frac1n\sum_{i=1}^n\sum_{a\in\mathcal A_K}c_a\,t_{i,a}
\]

The target \(\tau_c(z)\) averages unit comparisons. The absolute-weight sum \(L_c\) determines its feasible range \(I_c\).

- **Fixed population:** assignment supplies the randomness.
- **Binary outcomes:** each \(t_{i,a}\) is zero or one.
- **No interference:** the observed outcome is \(t_{i,A_i}\).
- **Fixed comparison:** \(K\geq2\) and nonzero \(c\), with \(\sum_a c_a=0\), stay fixed as \(n\) grows.

Potential outcomes within a unit are otherwise unrestricted. The example permits every binary triple.

---

## Risk criterion

Choose an assignment law \(\mathcal D\) and estimator \(\widehat\tau\) before learning the schedule.

\[
\rho_n(c)=\inf_{\mathcal D\in\Delta(\mathcal A_K^n),\,\widehat\tau}\max_{z\in\mathcal T_K^n}\mathbb E_{\mathcal D}\left[\left\{\widehat\tau((A_i,Y_i^{\mathrm{obs}})_{i=1}^n)-\tau_c(z)\right\}^2\right].
\]

The minimax risk \(\rho_n(c)\) is the smallest achievable worst-case mean squared error.

- \(\Delta(\mathcal A_K^n)\) includes every assignment distribution, including dependent assignments.
- \(\mathcal T_K^n\) contains every complete binary schedule.
- \(R_n(\mathcal D,\widehat\tau;z)\) denotes the expected squared error inside this criterion.

Clipping an estimate to \(I_c\) cannot increase squared error because the target lies there.

The optimization permits biased estimators.

---

## Allocation and benchmark

Assign independently in proportion to absolute comparison weights.

\[
S_c=\{a\in\mathcal A_K:c_a\ne 0\},\qquad
L_c=\sum_{a\in\mathcal A_K}|c_a|,\qquad
q_a^\star=\frac{|c_a|}{L_c}\quad(a\in S_c).
\]

The set \(S_c\) contains arms entering the comparison; \(q_a^\star\) is their assignment probability.

\[
\widehat\tau_{\mathrm{cHT}}^\star
=
\operatorname{proj}_{[-L_c/2,L_c/2]}\!\left[
n^{-1}\sum_{i=1}^n\sum_{a\in S_c}
c_a\mathbf 1\{A_i=a\}\frac{Y_i^{\mathrm{obs}}-1/2}{q_a^\star}
\right].
\]

The centered Horvitz–Thompson rule subtracts \(1/2\), applies comparison and inverse-probability weights, and averages. The indicator selects the assigned arm; projection clips to the target range.

@informal thm:first-order-saddle: For fixed \(K\geq2\) and nonzero zero-sum \(c\), minimax risk has first-order constant \(C_0(c)\); independent proportional allocation and the projected centered Horvitz–Thompson rule have worst-case risk at most \(C_0(c)/n\).

The average before projection is unbiased. Its variance guarantee does not exploit improvements available from bias.

---

## Main result

Under the fixed binary model, no interference, and fixed \(K\geq2\) and nonzero zero-sum \(c\),

\[
\sup_{z\in\mathcal T_K^n}
R_n(\mathcal D^\star,\widehat\tau_n^{\mathrm{sh}};z)
\leq
C_0(c)\left\{n^{-1}-\kappa_c n^{-4/3}\right\}.
\]

For sufficiently large \(n\), our capped-shrinkage estimator \(\widehat\tau_n^{\mathrm{sh}}\) improves worst-case risk by at least \(C_0(c)\kappa_c n^{-4/3}\).

Define \(d_n(c)=C_0(c)/n-\rho_n(c)\), the best achievable improvement.

\[
C_0(c)\kappa_c
\leq
\liminf_{n\to\infty} n^{4/3}d_n(c)
\leq
\limsup_{n\to\infty} n^{4/3}d_n(c)
\leq
43C_0(c).
\]

The optimal improvement has order \(n^{-4/3}\), even allowing dependent assignments and arbitrary estimators.

In the example, \(C_0(c^\dagger)=1\): the benchmark is \(1/n\).

---

## Independent signs

Let \(h_c=L_c/2\), the target’s half-range.

\[
W_i=\sum_{a\in S_c}\frac{c_a\mathbf 1\{A_i=a\}}{q_a^\star}\left(Y_i^{\mathrm{obs}}-\frac12\right),
\qquad
V_i=\frac{W_i}{h_c},
\qquad
X_n=\frac1n\sum_{i=1}^nV_i.
\]

The weighted contribution \(W_i\) always has magnitude \(h_c\): proportional allocation cancels the magnitude of the assigned arm’s weight.

Thus \(V_i\) is minus one or one, and \(X_n\) averages independent signs.

Write \(\mu_i=\mathbb E(V_i\mid z)=\sum_a c_a t_{i,a}/h_c\). Their average mean is the normalized target \(\Theta_n(z)=\tau_c(z)/h_c\).

The unadjusted normalized risk is
\(\operatorname{Var}(X_n\mid z)=n^{-1}-n^{-2}\sum_i\mu_i^2\).

In the example, \(h_c=1\) and \(V_i=Z_i\).

---

## Binary spacing

A response type is one unit’s vector of binary potential outcomes. Fixed \(K\) gives finitely many types.

\[
\lambda_c
=
\min\left\{
\frac{\left|\sum_{a\in\mathcal A_K} c_a t_a\right|}{L_c/2}
:
t\in\mathcal T_K,\ 
\sum_{a\in\mathcal A_K} c_a t_a\neq 0
\right\}.
\]

Here \(\mathcal T_K\) contains all binary response types. The positive number \(\lambda_c\) is the smallest nonzero normalized unit comparison.

Every \(\mu_i\) is zero or has magnitude at least \(\lambda_c\). Therefore,
\(n^{-2}\sum_i\mu_i^2\geq(\lambda_c/n)|\Theta_n(z)|\).

Moving the population comparison away from zero forces variance savings, even when individual comparisons have opposing signs.

In the example, unit comparisons are \(-1,-1/2,0,1/2,1\), so \(\lambda_{c^\dagger}=1/2\).

---

## Shrinkage rule

Keep proportional allocation and adjust \(X_n\).

\[
b_n=n^{-1/3},\qquad
\varepsilon_n=\frac{\sqrt{\lambda_c}}4n^{-1/3},\qquad
g_n(x)=\max\{-b_n,\min(x,b_n)\},
\]

The width \(b_n\) caps the argument of the adjustment; \(\varepsilon_n\) controls its strength.

\[
\widehat\tau_n^{\mathrm{sh}}
=\operatorname{proj}_{[-h_c,h_c]}\bigl(h_c\{X_n-\varepsilon_ng_n(X_n)\}\bigr).
\]

The rule adjusts the normalized average, restores the original scale, and clips to the target range.

- Inside the cap, multiply \(X_n\) by \(1-\varepsilon_n\).
- Outside it, subtract a fixed magnitude \(\varepsilon_n b_n\) toward zero.

For the example, apply this rule directly to the average of the \(Z_i\), using \(h_c=1\) and \(\lambda_c=1/2\).

---

## Risk accounting

At a fixed schedule, the change in normalized risk is
\(-2\varepsilon_n\operatorname{Cov}(X_n,g_n(X_n)\mid z)+\varepsilon_n^2\mathbb E[g_n(X_n)^2\mid z]\).

- **Noise removed:** the covariance term lowers risk.
- **Adjustment cost:** the positive term is at most \((\lambda_c/16)n^{-4/3}\).
- **Monotonicity:** the increasing function \(g_n\) makes the covariance nonnegative.
- **The cap:** bounds the adjustment cost uniformly over schedules.

The original variance saving \(n^{-2}\sum_i\mu_i^2\) remains available.

Which source of savings pays for the adjustment?

---

## Two comparison regions

**Near zero: \(|\Theta_n(z)|\leq b_n/2\).**

Concentration makes crossing the cap exponentially unlikely. Usually \(g_n(X_n)=X_n\), so the covariance is nearly the original variance.

Existing variance savings plus noise removal provide at least \(2\varepsilon_n/n\), before the rare-event correction. Paying adjustment cost leaves coefficient
\(A_c=\sqrt{\lambda_c}/2-\lambda_c/16>0\).

**Away from zero: \(|\Theta_n(z)|>b_n/2\).**

Binary spacing already saves at least \((\lambda_c/2)n^{-4/3}\). Paying adjustment cost leaves coefficient
\(B_c=7\lambda_c/16>0\), even ignoring noise removal.

For sufficiently large \(n\), the rare-event correction is small enough that
\(\kappa_c=\frac12\min\{A_c,B_c\}>0\) works for every schedule.

---

## Embedded two-arm difficulty

Why can another procedure not achieve a larger-order improvement?

Restrict schedules so all positively weighted arms share one outcome, and all negatively weighted arms share another.

Changing an arm label within either group reveals the same outcome. The target becomes a two-arm effect multiplied by \(h_c\).

\[
C_0(c)\rho_{n,2}\leq \rho_n(c)
\qquad\text{and}\qquad
\rho_n(c)\leq \frac{C_0(c)}{n}.
\]

Here \(\rho_{n,2}=\rho_n((1,-1))\) is unrestricted two-arm minimax risk. Squared-error rescaling contributes \(h_c^2=C_0(c)\).

In the example, restrict to \(t_{i,2}=t_{i,3}\).

We therefore need a two-arm risk floor close to \(1/n\).

---

## Scalar experiment

A distribution over fixed schedules gives a lower bound on worst-case risk.

Start with counts \((p_+,p_-,r_0)\) summing to \(n\):

- Randomly place \(p_+\) positive-effect units of type \((1,0)\).
- Randomly place \(p_-\) negative-effect units of type \((0,1)\).
- Give each remaining unit type \((0,0)\) or \((1,1)\), with equal probabilities independently.

Transform observations to \(S_i=Y_i^{\mathrm{obs}}\) in arm 1 and \(S_i=1-Y_i^{\mathrm{obs}}\) in arm 2.

\[
X(z,A)=\sum_{i=1}^n S_i(z,A).
\]

The count \(X\) records transformed successes: positive-effect units contribute one, negative-effect units zero, and equal-outcome units fair bits.

Conditional on the counts, \(X=p_++B\), with \(B\sim\operatorname{Binomial}(r_0,1/2)\). The actual target is \((p_+-p_-)/n\).

---

## Why assignment cannot help

For every count triple, the law of \(X\) is the same for every assignment vector.

Conditional on \(X=x\), the transformed observation vector is uniform among binary vectors with \(x\) ones, regardless of the count triple.

Consequently, averaging an estimator over assignments and vectors with the same \(X\) gives a scalar rule \(f(X)\) with no larger average squared error.

A risk floor for every \(f\) therefore constrains every original design and estimator.

The remaining ingredient is a particular distribution over the count triples.

---

## Parameterized count prior

Fix \(n\geq8\) and set \(\alpha=n^{-1/3}\).

Use \(\theta\) as a scalar prior-family parameter, distinct from the normalized comparison \(\Theta_n(z)\). For \(|\theta|\leq\alpha/2\), draw unit response types independently:

\[
\Pr_\theta\{(1,0)\}=\frac{\alpha+\theta}{2},\qquad
\Pr_\theta\{(0,1)\}=\frac{\alpha-\theta}{2},\qquad
\Pr_\theta\{(0,0)\}=\Pr_\theta\{(1,1)\}=\frac{1-\alpha}{2}.
\]

These probabilities determine the distribution of \((p_+,p_-,r_0)\): count how many draws fall in each effect class.

The total probability of a nonzero effect is \(\alpha\); \(\theta\) shifts the balance between positive and negative effects.

Conditional on the counts, this is exactly the schedule construction just described.

---

## Observation law

Because assignment cannot improve this prior experiment, calculate its scalar risk using all first-arm observations.

Let \(\sigma_i=r_{i,1}\), where \(r_i\) is unit \(i\)’s drawn two-arm response type. Then \(X\) counts the ones in \(\sigma\).

\[
p_\theta(\sigma)
=
\prod_{i=1}^n
\left(\frac{1+\theta}{2}\right)^{\mathbf 1\{\sigma_i=1\}}
\left(\frac{1-\theta}{2}\right)^{\mathbf 1\{\sigma_i=0\}},
\]

This is the likelihood of \(n\) independent binary observations with success probability \((1+\theta)/2\).

Thus \(X\) has a binomial law determined by \(\theta\), connecting the count prior to an explicit statistical experiment.

Its target is still the realized schedule effect, rather than just the parameter \(\theta\).

---

## Conditional target

Let \(\tau(r)\) be the average realized two-arm effect. Write \(\bar R(\sigma)\) for the average of the observed signs \(2\sigma_i-1\).

\[
\gamma_\alpha(\theta,\sigma)
:=
\mathbb E_\theta(\tau(r)\mid \sigma)
=
\theta+\omega_\alpha(\theta)\{\bar R(\sigma)-\theta\},
\qquad
\omega_\alpha(\theta):=\frac{\alpha-\theta^2}{1-\theta^2}.
\]

The conditional target \(\gamma_\alpha\) combines the family mean \(\theta\) with the observed sign average. The coefficient \(\omega_\alpha\) lies between zero and \(\alpha\).

Only a small share of units have nonzero effects, so observations produce a small correction to the family mean.

Conditional averaging implies
\(\mathbb E[(f(X)-\tau(r))^2]\geq\mathbb E[(f(X)-\gamma_\alpha(\theta,\sigma))^2]\).

Bounding error for this conditional target therefore bounds error for the actual schedule target.

---

## Prior window

Mix the count distributions over \(\theta\) using the smooth density

\[
w_\alpha(\theta)
=
\frac{15}{8\alpha}
\left(1-\frac{4\theta^2}{\alpha^2}\right)^2
\mathbf 1\{|\theta|\le \alpha/2\}.
\]

The density \(w_\alpha\) integrates to one and vanishes at the endpoints of its support. Mixing over it completes the particular count prior.

Its Fisher information—expected squared derivative of the log density—is
\(J(w_\alpha)=40/\alpha^2=40n^{2/3}\).

A prior concentrated in a window of width \(\alpha\) has information on the inverse-square scale \(1/\alpha^2\).

How much can the observations add, and how sensitive is the target?

---

## Sensitivity and information

For the conditional target,

\[
\mathbb E_\theta\{\partial_\theta\gamma_\alpha(\theta,\sigma)\}
=
1-\omega_\alpha(\theta)
\ge
1-\alpha.
\]

The expected derivative measures how much the target moves when \(\theta\) changes. It remains close to one: the observation correction costs at most \(\alpha\) in sensitivity.

For the observation likelihood,

\[
I_n(\theta)=\frac{n}{1-\theta^2}
\le
\frac{n}{1-\alpha^2/4}.
\]

The information \(I_n\) adds across the \(n\) independent observations; success probabilities near one-half make its leading scale \(n\).

Van Trees (1968) bounds average squared error below by squared average target sensitivity divided by total prior and observation information.

---

## Two-arm risk floor

Applying that inequality to our explicit count prior gives a bound against every two-arm design and estimator.

@formal thm:coarse-two-arm-minimax-lower

The fraction now has identified components:

- **Numerator:** sensitivity is at least \(1-\alpha\).
- **Denominator:** observation information is at most \(n/(1-\alpha^2/4)\), and prior information is \(40/\alpha^2\).

With \(\alpha=n^{-1/3}\), the sensitivity loss and the prior information relative to \(n\) both have scale \(n^{-1/3}\).

That relative loss applied to baseline risk \(1/n\) gives \(n^{-4/3}\). The embedding therefore limits multiarm improvement to at most \(43C_0(c)n^{-4/3}\).

---

## Further results

Computable bounds from a feasible procedure and a schedule prior bracket minimax risk with width negligible relative to \(n^{-4/3}\), for every fixed real contrast.

---

## Open questions

- With at least three active arms, does \(n^{4/3}d_n(c)\) converge, and what is its sharp constant?
- Can the hardest response-count configurations identify a limiting equation, an optimal correction, and a matching prior?
- How far can finite optimization reach as the response-count state space grows?

---

## Takeaways

- Independent allocation proportional to absolute comparison weights attains the benchmark \(C_0(c)/n\).
- Capped shrinkage improves uniformly: noise removal protects comparisons near zero, and binary spacing protects comparisons away from zero.
- A concrete schedule prior and embedded two-arm difficulty limit the optimal improvement to order \(n^{-4/3}\).

---

## Appendix: Exact count reduction

Averaging over arbitrary unit labels turns the unrestricted experiment into an equivalent finite game using response-type, allocation, and observed-success counts.

@formal thm:exact-response-type-game

---

## Appendix: Universal second-order rate

Explicit capped shrinkage and an embedded two-arm converse bound the optimal improvement on the \(n^{-4/3}\) scale.

@formal thm:universal-second-order-rate

---

## Appendix: Rational risk certificates

For rational contrasts, a finite linear program minimizes a common risk ceiling over allocation probabilities and grid-estimator weights; its solution supplies a procedure, while dual risk weights supply a count prior with a matching lower bound up to grid error.

@formal thm:rational-contrast-grid-certificate-sandwich

---

## Appendix: Real contrast certificates

Rational approximations transfer finite procedure–prior risk brackets to every fixed real contrast with width negligible relative to \(n^{-4/3}\).

@formal thm:real-contrast-grid-certificate-transfer
