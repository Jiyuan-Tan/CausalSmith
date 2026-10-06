# Limits to Estimating Dose-Response Means

Even with smooth treatment assignment and good overlap, estimating the population mean at one exact dose faces an unavoidable error floor.

---

## Motivation

What would the population’s average outcome be if everyone received dose \(t_0\)?

Observe \(O=(Y,A,X)\): outcome \(Y\), continuous dose \(A\in[0,1]\), and covariates \(X\in[0,1]^d\), where \(d\) is their dimension.

\[
\theta_P(t_0)
=
\int_{[0,1]^d} \mu_P(t_0,x)\,p_{X,P}(x)\,dx .
\]

Here \(P\) is the observation’s law, \(\mu_P(t_0,x)\) is the conditional mean outcome at dose \(t_0\), and \(p_{X,P}\) is the covariate density.

The target fixes the dose and averages over the population’s covariates. Observations arrive at varying doses.

How accurately can they reveal the mean at this exact dose?

---

## Research question

The standard approach estimates outcome regression and treatment density, adjusts for covariates, and smooths across nearby doses.

- Kennedy et al. (2017) combine regression and treatment-density adjustment in doubly robust estimation.
- Bonvini and Kennedy (2022) add higher-order influence-function corrections: extra terms that reduce bias from estimating these functions.

Their upper error bounds describe what particular procedures achieve under their assumptions.

Our question concerns **every estimator**:

What is the smallest possible worst-case mean-squared error over a specified smoothness class?

---

## Key idea

Use two laws with identical treatment and covariate distributions. Change only the outcome regression near \(t_0\).

The target sees the change’s height at \(t_0\). Sample information depends on both its height and the width of the affected dose region.

Regression smoothness of order \(\alpha>0\) permits a change whose height is proportional to its width raised to \(\alpha\).

Balancing height and width produces a worst-case mean-squared-error lower bound of \(n^{-2\alpha/(2\alpha+1)}\), up to a positive constant, for sufficiently large sample size \(n\).

This holds under boundedness, positive smoothness, interiority, local positivity, and strict baseline slack: admissible design densities exist with a positive margin inside their restrictions.

---

## Example

Two-valued outcomes let us change a conditional mean through one probability.

Let \(Q_u\) and \(Q_v\) be distributions on \(\{-B,B\}\), with means \(u\) and \(v\), where \(B>0\).

\[
Q_u(B)=\frac{1+u/B}{2},
\qquad
Q_v(B)=\frac{1+v/B}{2}.
\]

These are the probabilities of outcome \(B\); the remaining probability goes to \(-B\).

At each dose and covariate value, changing this probability changes the regression while leaving treatment assignment fixed.

For \(|u|,|v|\le B/2\), both probabilities lie between \(1/4\) and \(3/4\).

We will use positive and negative localized mean changes as the two alternatives.

---

## Model

The regression and treatment density are

\[
\mu_P(a,x)=E_P[Y\mid A=a,X=x],
\qquad
\pi_P(a\mid x)=\text{density of }A\mid X=x .
\]

The regression supplies the target; the treatment density determines how often nearby doses occur.

- **Sampling:** \(n\) independent observations from the same law.
- **Bounded outcomes:** \(|Y|\le M\), with \(M>0\).
- **Interior dose:** \([t_0-\varepsilon_0,t_0+\varepsilon_0]\subset(0,1)\), with \(0<\varepsilon_0<1/2\).
- **Local positivity:** \(\pi_P(a\mid x)\ge c_0>0\) throughout this neighborhood for every \(x\).

For a causal interpretation, \(Y(a)\) denotes the potential outcome under dose \(a\). Consistency requires \(Y=Y(A)\); no unmeasured confounding requires \(Y(a)\) independent of \(A\) conditional on \(X\).

Together with positivity, these conditions identify the partial mean as the average potential outcome at \(t_0\).

---

## Smoothness assumptions

Hölder smoothness bounds derivatives and how quickly the highest controlled derivative can vary.

All orders are positive; all restrictions use radius \(M\).

| Direction | Restricted functions | Order |
|---|---|---|
| Dose, near \(t_0\) | Regression \(\mu_P(a,x)\) | \(\alpha\) |
| Dose, near \(t_0\) | Treatment density \(\pi_P(a\mid x)\) | \(\beta\) |
| Covariates, at \(t_0\) | \(\mu_P(t_0,x)\), \(\pi_P(t_0\mid x)\), and \(p_{X,P}(x)\) | \(s\) |

Also require \(0\le p_{X,P}(x)\le M\).

Write \(\mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0)\) for the class satisfying these and the preceding model conditions.

**Strict baseline slack:** normalized treatment and covariate densities exist with a positive margin inside their smoothness, density-envelope, and local positivity restrictions.

In our binary example, bounded probabilities alone are insufficient: the dose-specific means must also satisfy regression smoothness.

---

## Worst-case accuracy

Minimax risk is the smallest worst-case mean-squared error achievable by an estimator.

\[
R_n\!\left(\mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0),t_0\right)
=
\inf_{\substack{\hat\theta_n\ \mathrm{measurable}\\
\hat\theta_n(O_1,\ldots,O_n)\in[-M,M]\ \mathrm{for\ every\ sample}}}
\sup_{P\in \mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0)}
E_{P^{\otimes n}}\!\left[
\left\{\hat\theta_n(O_1,\ldots,O_n)-\theta_P(t_0)\right\}^2
\right],
\]

Here \(\hat\theta_n\) is an estimator and \(P^{\otimes n}\) is the joint law of the independent observations.

Read from inside outward:

- The expectation computes mean-squared error under \(P\).
- The supremum selects that estimator’s hardest law in the class.
- The infimum chooses the best estimator.

A lower bound survives choosing the best possible procedure.

---

## Main result

@informal thm:sharp-pointwise-lower-bound: With \(\alpha,\beta,s,M,c_0>0\), \(0<\varepsilon_0<1/2\), an interior dose window, and strict baseline slack, minimax mean-squared error is at least \(c\,n^{-2\alpha/(2\alpha+1)}\), with \(c>0\), for all sufficiently large \(n\).

\[
  c\, n^{-2\alpha/(2\alpha+1)}
  \le
  R_n\!\left(
    \mathcal P_{\alpha,\beta,s}(M,c_0,\varepsilon_0,t_0),
    t_0
  \right),
\]

This bounds the best achievable worst-case mean-squared error over our class. The constant \(c\) may depend on fixed model parameters, but not on \(n\).

For every fixed admissible treatment-density smoothness \(\beta>0\), the exponent is unchanged; constants and baseline feasibility may depend on \(\beta\).

Two admissible binary-outcome laws already force this error. Consequently, the bound constrains regression, adjustment, smoothing, and every other estimation procedure.

---

## Fixed design

A worst-case lower bound needs only two difficult laws inside the class.

Strict baseline slack supplies a covariate density \(p_0(x)\), a treatment density \(q_0(a)\), and a positive margin \(\eta_0\).

- Both densities integrate to one.
- Their smoothness restrictions and the covariate-density envelope have margin at least \(\eta_0\).
- Throughout the dose neighborhood, \(c_0+\eta_0\le q_0(a)\le M-\eta_0\).

Use the same \(p_0\) and \(q_0\) under both alternatives. Treatment is independent of covariates because \(q_0\) does not depend on \(x\).

Choose the binary outcome magnitude \(B=M/2\).

Doses and covariates cannot distinguish the alternatives. Only the conditional outcome probabilities change.

---

## Localized regressions

Let \(h\) be the dose half-width, with \(0<h\le\min\{1,\varepsilon_0\}\).

Choose a fixed smooth bump \(\psi\): it equals one for \(|z|\le1/2\), vanishes for \(|z|\ge1\), and stays between zero and one.

For sign \(\zeta\in\{-1,1\}\), use

\[
\mu_\zeta(a,x)
=
\zeta\,\lambda\,h^{\alpha}\,\psi\!\left(\frac{a-t_0}{h}\right),
\qquad a\in[0,1],\ x\in[0,1]^d,
\]

Here \(\lambda>0\) is a fixed amplitude constant, chosen small enough for smoothness and with \(\lambda\le M/4=B/2\).

The two regressions have opposite signs, height \(\lambda h^\alpha\), and support within distance \(h\) of \(t_0\). They are constant across covariates.

Under law \(P_\zeta\), draw the outcome from the binary example with mean \(u=\mu_\zeta(a,x)\).

---

## Why the height shrinks

A narrower bump changes more sharply. Its height must shrink to preserve \(\alpha\)-smoothness.

For a sufficiently small fixed \(\lambda\), every sign and every \(h\in(0,1]\) satisfy

\[
\Bigl(a\mapsto \zeta\,\lambda\,h^{\alpha}\,\psi\!\left(\tfrac{a-t_0}{h}\right)\Bigr)
\in
\mathcal H^{\alpha}\bigl(M;[t_0-\varepsilon_0,t_0+\varepsilon_0]\bigr).
\]

This says the scaled regression remains in the required dose-smoothness ball.

An order-\(j\) derivative, where \(j\) counts differentiations, acquires the factor \(h^{\alpha-j}\). The remaining highest-derivative Hölder variation has a width factor that cancels.

The same \(\lambda\) therefore works as \(h\) shrinks.

At \(t_0\), both means are constant in \(x\), satisfying covariate smoothness of every positive order \(s\). Also \(|\mu_\zeta|\le B/2\), so the binary probabilities remain admissible.

Together with the fixed design, both laws belong to our class.

---

## Target separation

Call the negative alternative \(P_0=P_{-1}\) and the positive alternative \(P_1=P_{+1}\).

At \(t_0\), the bump equals one. Since the regression is constant in \(x\), averaging over \(p_0\) preserves its height:

\[
\theta_{P_1}(t_0)-\theta_{P_0}(t_0)
=
2\lambda h^{\alpha}.
\]

This computes the gap between the two population means.

Write \(\theta_i=\theta_{P_i}(t_0)\), and denote their absolute gap by

\[
\Delta = |\theta_1-\theta_0|.
\]

Thus \(\Delta\) is twice the bump height.

The target gap shrinks with height, but contains no additional width factor. Where does width enter the sample’s ability to distinguish the laws?

---

## Information cost

Kullback–Leibler divergence, written \(\mathrm{KL}\), measures how distinguishable two distributions are.

For the binary example, when \(|u|,|v|\le B/2\),

\[
\mathrm{KL}(Q_u,Q_v)
\le
\frac{2(u-v)^2}{B^2}.
\]

Information is bounded by the squared conditional-mean difference, scaled by the squared outcome magnitude.

The common design means we average this bound over doses and covariates. The regressions differ only on an interval of length \(2h\), where \(q_0\le M-\eta_0\). Consequently,

\[
\mathrm{KL}(P_0,P_1)
\le
\frac{8\lambda^2h^{2\alpha}}{B^2}\cdot 2(M-\eta_0)h
=
\frac{16\lambda^2(M-\eta_0)}{B^2}\,h^{2\alpha+1}.
\]

This bounds information from one observation: squared height contributes \(h^{2\alpha}\), and the affected dose region contributes \(h\).

**The target sees height; information pays squared height times width.**

---

## Bandwidth choice

Independent observations add information. Keep total sample information bounded by choosing

\[
h=h_n=n^{-1/(2\alpha+1)} .
\]

Here \(h_n\) is the bump half-width at sample size \(n\). For sufficiently large \(n\), it fits inside the interior dose window.

With this choice,

\[
\mathrm{KL}\bigl(P_0^{\otimes n},P_1^{\otimes n}\bigr)
\le
n\,\mathrm{KL}(P_0,P_1)
\le
n\,\frac{16\lambda^2(M-\eta_0)}{B^2}\,h^{2\alpha+1}
=
\frac{16\lambda^2(M-\eta_0)}{B^2}
=
K,
\]

The product laws describe the complete samples; \(K\) is a fixed information budget independent of \(n\).

The exponent \(2\alpha+1\) combines squared smoothness-limited height with dose width. Choosing its reciprocal makes the information budget constant.

---

## From testing to estimation

Set \(Q_i=P_i^{\otimes n}\), the complete sample law under alternative \(i\).

The two-point testing bound from Tsybakov (2009) converts bounded information and target separation into unavoidable error:

\[
\max_{i=0,1} E_{Q_i}\!\left[(T-\theta_i)^2\right]\ge c_K \Delta^2 .
\]

Here \(T\) is any estimator, \(\theta_i\) is its target under alternative \(i\), and \(c_K>0\) depends only on the fixed information budget \(K\).

An estimate close enough to the correct target would distinguish the generating law. Bounded information prevents arbitrarily reliable distinction.

Every estimator therefore has error at least \(c_K\Delta^2\) under one alternative. Both alternatives lie in our class, so this also bounds worst-case error over the class.

---

## Origin of the exponent

The target gap is \(2\lambda h^\alpha\). Squaring it and substituting our bandwidth gives

\[
c_K\bigl(2\lambda h^{\alpha}\bigr)^2
=
4c_K\lambda^2h^{2\alpha}
=
c_{\mathrm{or}}\left(n^{-1/(2\alpha+1)}\right)^{2\alpha}
=
c_{\mathrm{or}}\,n^{-2\alpha/(2\alpha+1)} .
\]

Here \(c_{\mathrm{or}}=4c_K\lambda^2>0\) is fixed independently of sample size.

The mechanism is now quantitative:

- Smoothness permits height proportional to \(h^\alpha\).
- Sample information is bounded when \(n h^{2\alpha+1}\) stays constant.
- Squared target separation then has scale \(n^{-2\alpha/(2\alpha+1)}\).

Treatment-density smoothness \(\beta\) affects the admissible fixed design, but the shrinking regression bump supplies the exponent.

---

## Further results

Bonvini and Kennedy (2022) give the higher-order influence-function benchmark

\[
\rho_n
=
n^{-2\alpha/(2\alpha+1)}
\vee
n^{-2/(1+d/(4s)+1/\alpha)} .
\]

Here \(\rho_n\) is the benchmark sequence; \(\vee\) selects the larger term.

Their upper guarantee holds under additional regularity and estimator conditions, including \(\alpha\le\beta\).

It holds fixed the trained regression \(\hat\mu_n\), treatment density \(\hat\pi_n\), joint dose-covariate density \(\hat p_n\), and estimated projection kernels used in the corrections. Its mean-squared error averages over the estimation observations \(O_1,\ldots,O_n\), while these fitted objects remain fixed.

Our warranted comparison is between rate sequences: that conditional upper guarantee uses a more regular class; our minimax lower bound covers every estimator over our full class.

- When \(d\le4s\), the benchmark equals our regression lower-floor sequence.
- When \(4s<d\), the covariate term dominates and decays more slowly.

---

## Open questions

- Can an estimator attain a matching unconditional upper bound over our full Hölder class, accounting for randomness in trained nuisance functions?
- Can a full-class upper analysis, or an inclusion argument with the needed constants, connect our class to the published upper guarantee?
- When \(4s<d\), does attainable accuracy follow the published benchmark, an intermediate exponent, or a rate depending more directly on \(\beta\)?

---

## Takeaways

- Under positive smoothness, boundedness, interiority, local positivity, and strict baseline slack, minimax mean-squared error is at least a constant times \(n^{-2\alpha/(2\alpha+1)}\) for sufficiently large \(n\).
- A smooth binary-outcome perturbation has height \(h^\alpha\): the target sees that height, while sample information scales with squared height times width.
- Fixing \(h=n^{-1/(2\alpha+1)}\) keeps information bounded; testing then forces the stated error floor for every fixed admissible \(\beta>0\).

---

## Appendix: Interior dose-response lower bound

Every estimator faces the regression error floor under positive smoothness, interiority, and strict baseline slack.

@formal thm:sharp-pointwise-lower-bound

---

## Appendix: Smooth covariate comparison

When \(d\le4s\), the lower-floor exponent equals the published benchmark exponent.

@formal thm:sharp-minimax-smooth-covariate

---

## Appendix: Low covariate smoothness comparison

When \(4s<d\), the lower floor persists while the published benchmark has a strictly smaller exponent.

@formal thm:frontier-bracket-deficient
