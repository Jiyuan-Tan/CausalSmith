# Confidence Sets for Transported Complier Effects

When encouragement barely changes treatment receipt, we can still give reliable uncertainty statements about effects in a different population.

---

## Motivation

An encouragement experiment supplies evidence about treatment effects, but the population of interest may differ from the experimental population.

- **Source:** observe covariates \(X\), encouragement \(Z\), treatment receipt \(D\), and outcome \(Y\).
- **Target:** observe only covariates.
- **Compliers:** people who receive treatment when encouraged and do not receive it otherwise.

We want the average treatment effect among **target compliers**.

Target covariates tell us whom to represent. How much information does the source experiment provide about their effect?

---

## Research question

The usual estimator transports the encouragement effects on outcomes and receipt, then divides the outcome contrast by the receipt contrast.

Chen and Huang (2025) study this transported complier effect with a first stage bounded away from zero and asymptotically normal estimation.

When encouragement barely changes receipt, the estimated denominator can be as noisy as its mean. Normal inference for the ratio then becomes unreliable.

Ma (2023) develops identification-robust inference for complier effects within one population.

How short can uniformly valid confidence sets be when **weak compliance and uneven transport weights both reduce information**?

---

## Key idea

Test each candidate effect using an outcome-minus-receipt contrast. Retain candidates compatible with a zero contrast.

Precision depends on the transported first stage \(\mu_n\), the target complier share, and weight dispersion \(\kappa_n\), the second moment of the target-to-source weights:

\[
t_n=\frac{n\mu_n^2}{\kappa_n}.
\]

Here \(n\) is the source sample size; \(t_n\) measures effective strength.

With **known weights and assignment probabilities**, this inversion minimizes worst-case asymptotic expected length up to constants among uniformly valid procedures.

Under our causal, transport, overlap, and weight-growth conditions, that length has order \(\min\{1,t_0^{-1/2}\}\), comparing laws with \(t_n\ge t_0\) for each fixed \(t_0>0\).

Coverage remains required throughout the model, including arbitrarily weak first stages.

---

## Example

Suppose source and target covariate distributions coincide.

The transport weight \(w(X)\), the target-to-source covariate density ratio, equals one. Its second moment is \(\kappa_n=1\), so

\[
t_n=\frac{n\mu_n^2}{\kappa_n}=n\mu_n^2 .
\]

This computes effective strength without a transport penalty.

For each proposed effect, compare the outcome encouragement contrast with that effect times the receipt encouragement contrast.

A small receipt contrast leaves many effects compatible with the data. Outcomes bounded in \([0,1]\) restrict their average treatment effect to \([-1,1]\), providing a finite uncertainty scale.

---

## Model

Let \(S=1\) denote the source and \(S=0\) the target; both populations have positive probability. Receipt under encouragement \(z\) is \(D(z)\), and the outcome under treatment \(d\) is \(Y(d)\).

- **Bounded binary structure:** \(D(z)\in\{0,1\}\) and \(Y(d)\in[0,1]\).
- **Source validity:** encouragement is randomized conditional on \(X\); observed receipt and outcome satisfy \(D=D(Z)\) and \(Y=Y(D)\).
- **Exclusion and monotonicity in both populations:** encouragement affects outcomes only through receipt, and \(D(1)\ge D(0)\), ruling out people who take treatment only when unencouraged.

Under the transport restrictions below, the target effect is

\[
\frac{\mu_{Y,n}}{\mu_n}
=
\theta_T
=
\mathbb E_{P_n^F}\!\left[Y(1)-Y(0)\mid D(1)=1,\ D(0)=0,\ S=0\right]
\in \Theta=[-1,1].
\]

Here \(P_n^F\) is the full-data law. The ratio averages treatment effects among target compliers; \(\mu_{Y,n}\) is the transported outcome contrast and \(\mu_n>0\) is the target complier share. The candidate range is \(\Theta\).

---

## Transport assumptions

Let \(\Delta_Y(x)\) and \(\Delta_D(x)\) be the source encouragement effects on outcomes and receipt at covariate value \(x\).

- **Outcome transport:** the outcome encouragement contrast agrees across populations at every target covariate value.
- **Receipt transport:** the target-average receipt contrast agrees across populations; covariate-specific agreement is unnecessary.
- **Support:** every target covariate region is represented in the source, permitting density-ratio weights \(w(X)\).

The transported quantities are

\[
\mu_{Y,n}=\mathbb E_{P_S^X}\!\left[w(X)\,\Delta_Y(X)\right],
\qquad
\mu_n=\mathbb E_{P_S^X}\!\left[w(X)\,\Delta_D(X)\right],
\qquad
\kappa_n=\mathbb E_{P_S^X}\!\left[w(X)^2\right],
\]

where \(P_S^X\) is the source covariate distribution. The first two expectations reproduce target-average encouragement contrasts; the third measures how unevenly source observations represent the target.

@informal prop:compact-causal-range: Under our model assumptions, the transported outcome-to-receipt ratio identifies the target complier effect and lies in \([-1,1]\).

---

## Assumptions

**Assignment overlap:** the source encouragement probability \(e(X)\) satisfies \(\varepsilon\le e(X)\le1-\varepsilon\), with fixed \(0<\varepsilon<1/2\). Neither assignment arm becomes arbitrarily rare.

**Weight control:** \(0\le w(X)\le2k_n\) and \(\kappa_n\le k_n\), where the positive scale \(k_n\) limits extreme weights and their dispersion.

We allow weakening first stages and growing weight dispersion:

\[
k_n \to \infty,
\qquad
k_n=o(n^{1/2}),
\qquad
\mu_n\to 0 .
\]

Weight growth remains slower than the square root of source sample size.

The source observations and target draws form independent samples; target size \(N_n\) satisfies \(N_n/n\to c>0\).

In the no-shift example, \(w(X)=1\) automatically meets the weight controls eventually. A vanishing complier share remains allowed.

---

## Honest expected length

**Honesty** means asymptotic coverage of at least \(1-\alpha\), uniformly over every law in our model. The noncoverage level satisfies \(0<\alpha<1\).

An **oracle** procedure knows \(w\) and \(e\).

For a confidence set \(C_n\subseteq\Theta\), let \(\lambda(C_n)\) denote its length. Compare worst-case expected length over laws with effective strength at least a fixed \(t_0>0\):

\[
R((C_n),t_0)
=
\limsup_{n\to\infty}
\sup_{P\in\mathcal P_n:\,t_n\ge t_0}
\mathbb E_P[\lambda(C_n)].
\]

Here \(\mathcal P_n\) contains the laws \(P\) satisfying our model assumptions. The threshold restricts **length comparisons**, while coverage is required over the entire class.

The best achievable risk is

\[
V^\star(t_0)
=
\inf_{(C_n)\in\mathfrak C^{\mathrm{or}}}
R((C_n),t_0).
\]

The class \(\mathfrak C^{\mathrm{or}}\) contains all oracle procedures satisfying uniform honesty. “Optimal up to constants” compares our procedure with this infimum.

---

## Main result

Maintain the causal, transport, assignment-overlap, weight-control, and sampling-growth assumptions.

@informal thm:oracle-score-inversion-attainment: Under these assumptions and an admissible transport design, known-\(w,e\) score inversion is uniformly honest and attains optimal worst-case expected-length order \(\min\{1,t_0^{-1/2}\}\) for every fixed \(t_0>0\).

\[
\frac{3(1-\alpha)^2}{16}\min\{1,t_0^{-1/2}\}
\le
V^\star(t_0)
\le
C_0\min\{1,t_0^{-1/2}\},
\]

where \(C_0>0\) depends only on noncoverage and assignment overlap.

- Weak effective strength leaves worst-case expected length bounded below by a positive constant.
- Stronger effective strength permits inverse-square-root improvement.
- In the no-shift example, strength is \(n\mu_n^2\): more observations help only relative to the squared complier share.

These bounds compare procedures up to constants; they are not an exact formula for a realized confidence set’s length.

---

## Recovering source contrasts

Inverse-propensity weighting recovers the source encouragement contrast:

\[
H_i=\frac{Z_i}{e(X_i)}-\frac{1-Z_i}{1-e(X_i)},
\]

where \(H_i\) weights encouraged observations positively and unencouraged observations negatively, correcting for their assignment probabilities.

Transport these contrasts and estimate weight dispersion:

\[
\widehat A_n=\frac1n\sum_{i=1}^n w(X_i)H_iY_i,
\qquad
\widehat B_n=\frac1n\sum_{i=1}^n w(X_i)H_iD_i,
\qquad
\widehat\kappa_n=\frac1n\sum_{i=1}^n w(X_i)^2 .
\]

The statistics estimate the target outcome contrast \(\mu_{Y,n}\), receipt contrast \(\mu_n\), and dispersion \(\kappa_n\).

The natural ratio estimate is \(\widehat A_n/\widehat B_n\). What restriction remains testable when its denominator is small?

---

## A residual instead of a ratio

For a candidate effect \(\vartheta\in\Theta\), form

\[
\psi_i(\vartheta)
=
w(X_i)\left\{\frac{Z_i}{e(X_i)}-\frac{1-Z_i}{1-e(X_i)}\right\}(Y_i-\vartheta D_i).
\]

The score \(\psi_i(\vartheta)\) computes a transported encouragement contrast in the residual outcome \(Y_i-\vartheta D_i\).

Its mean is \(\mu_{Y,n}-\vartheta\mu_n\), which vanishes at the true effect \(\vartheta=\theta_T\). Its empirical mean is \(\widehat A_n-\vartheta\widehat B_n\).

A small first stage becomes a small **slope in the candidate effect**. Testing the zero-mean restriction requires no division.

This is the test-inversion logic of Anderson and Rubin (1949).

---

## Score inversion

Retain every candidate whose residual contrast is small enough:

\[
C_n
=
\left\{\vartheta\in\Theta:
\left|\widehat A_n-\vartheta\widehat B_n\right|
\le
L_\alpha\sqrt{\widehat\kappa_n/n}
\right\}.
\]

This computes the confidence set. The radius uses empirical weight dispersion and the calibration \(L_\alpha=\left(\frac{8}{\alpha\varepsilon^2}\right)^{1/2}\).

Coverage survives a weak first stage because:

- At the true effect, the residual score has mean zero.
- Bounded outcomes, binary receipt, and assignment overlap bound its second moment on the \(\kappa_n\) scale.
- Weight-growth control makes \(\widehat\kappa_n\) sufficiently reliable for uniform calibration.

In the no-shift example, \(\widehat\kappa_n=1\): the test compares the residual encouragement contrast with a radius proportional to \(n^{-1/2}\).

---

## From scores to length

The residual contrast is linear in \(\vartheta\), with slope \(-\widehat B_n\).

When \(\widehat B_n\) is close to \(\mu_n\), the accepted width is bounded by twice the score radius divided by \(|\widehat B_n|\). This yields the \(t_n^{-1/2}\) scale.

Samples with unreliable slopes are controlled by

\[
P\!\left(\frac{\mu_n(P)}2<\left|\widehat B-\mu_n(P)\right|\right)\le\frac{4}{\varepsilon^2t_n(P)} .
\]

Here \(\widehat B=\widehat B_n\); \(\mu_n(P)\) and \(t_n(P)\) are the first stage and effective strength under law \(P\). The bound measures how often the estimated slope differs from its mean by more than half that mean.

On those samples, restricting candidates to \([-1,1]\) bounds length by two.

Thus reliable slopes give shrinking width, while the bounded causal range controls the contribution of unreliable slopes.

---

## Hidden compliance types

To show why shorter honest sets are impossible, hold the source covariate law, weights, and propensity fixed as \(\mathfrak g=(P_S^X,w,e)_{n\ge1}\).

Choose \(\mu_n=\left(\frac{t_0\kappa_n}{n}\right)^{1/2}\) and conditional complier probability \(p_n(x)=\mu_n w(x)/\kappa_n\). The transported first stage is \(\mu_n\), and effective strength is exactly \(t_0\).

Conditional on \(X=x\), use these compliance shares:

| Type | Receipt behavior | Share |
|---|---|---|
| Complier | \(D(0)=0,\ D(1)=1\) | \(p_n(x)\) |
| Always-taker | Receives treatment under either assignment | \((1-p_n(x))/2\) |
| Never-taker | Receives treatment under neither assignment | \((1-p_n(x))/2\) |

Set \(Y(0)=0\). Complier treated outcomes are Bernoulli with mean \(1/2+h\); other types’ treated outcomes are Bernoulli with mean \(1/2\).

Use the same conditional law in both populations. The target effect is \(1/2+h\), while covariates and compliance shares remain unchanged. Weight-growth control makes these shares valid for sufficiently large \(n\).

---

## Diluted outcome changes

Compliance type is unobserved. Among encouraged treatment recipients, compliers mix with always-takers.

At \(h=0\), conditional on \(X=x,Z=1\), each observed cell \((D,Y)=(1,1)\) and \((1,0)\) has probability \((1+p_n(x))/4\).

Changing \(h\) moves probability \(p_n(x)h\) from one cell to the other. All other observed cells remain unchanged.

The always-takers supply outcome variation even when compliers are rare. Consequently, the squared observable change scales with \(p_n(x)^2h^2\), rather than with the complier share alone.

Averaging across source covariates gives \(\mathbb E_S[p_n(X)^2]=\mu_n^2/\kappa_n\). Across \(n\) source observations, the information scale is therefore \(n\mu_n^2h^2/\kappa_n=t_0h^2\).

This explains why uneven transport weights and weak compliance enter the same lower-bound calculation.

---

## Nearby laws and length

Let \(Q_{n,h}^{\mathfrak g}\) be the joint observed-data law under tilt \(h\), and \(Q_{n,0}^{\mathfrak g}\) its center law.

Set \(\rho=(1-\alpha)/8\) and restrict \(|h|\le H(t_0)=\min\{1/4,\rho t_0^{-1/2}\}\). For sufficiently large \(n\),

\[
1+\chi^2(Q_{n,h}^{\mathfrak g}\Vert Q_{n,0}^{\mathfrak g})\le\exp(8t_0h^2),
\qquad
\|Q_{n,h}^{\mathfrak g}-Q_{n,0}^{\mathfrak g}\|_{\mathrm{TV}}\le2\rho.
\]

Chi-square distance aggregates squared probability changes relative to their baseline probabilities. Total variation bounds the difference in the probability of **any event**.

Honesty under each tilted law requires coverage of its effect \(1/2+h\). The distance bound transfers that coverage to the common center law, with a loss of at most \(2\rho\).

Integrating these inclusion probabilities over the interval of effects forces expected length under the center law to be at least a positive coverage-dependent constant times \(H(t_0)\).

@informal thm:fixed-geometry-frontier: Under our model, overlap, and growth conditions, every admissible fixed source-covariate, weight, and propensity array has optimal honest expected-length order \(\min\{1,t_0^{-1/2}\}\) for each fixed \(t_0>0\).

---

## Learning target weights

Now suppose \(X\) is observed as one of \(k_n\) cell labels. Source cells each have probability \(1/k_n\), and encouragement is balanced: \(e(X)=1/2\).

Estimate target cell masses using target covariates:

\[
H_i=2(2Z_i-1),\qquad
\widehat p_{x,n}=\frac1{N_n}\sum_{j=1}^{N_n}\mathbf 1\{X_j^T=x\},
\]

where \(X_j^T\) is target observation \(j\), \(\widehat p_{x,n}\) is the empirical target frequency of cell \(x\), and \(H_i\) is the balanced-assignment contrast weight.

For \(G\in\{Y,D\}\), estimate source contrasts and transport them:

\[
\widehat m_{G,n}(x)=\frac{k_n}{n}\sum_{i=1}^n
\mathbf 1\{X_i=x\}H_iG_i,\qquad
\widehat M_{G,n}=\sum_{x=1}^{k_n}\widehat p_{x,n}\widehat m_{G,n}(x).
\]

Here \(\widehat m_{G,n}(x)\) estimates the cell’s encouragement contrast. The factor \(k_n\) corrects for source cell probability \(1/k_n\).

The target-frequency average \(\widehat M_{G,n}\) replaces the oracle transported contrast using only the two samples.

---

## Dispersion from coincidences

Pairs of target observations in the same cell reveal how concentrated the target distribution is.

For \(N_n\ge2\), compute

\[
\widehat\kappa_{U,n}
=\frac{k_n}{N_n(N_n-1)}
\sum_{j\ne\ell}\mathbf 1\{X_j^T=X_\ell^T\},\qquad
\widehat K_n=1+\widehat\kappa_{U,n},
\]

where the sum counts ordered pairs of distinct target observations. The scaled coincidence count estimates weight dispersion; \(\widehat K_n\) is the feasible dispersion proxy.

Use the same residual-inversion idea:

\[
C_n=\left\{\vartheta\in\Theta:
|\widehat M_{Y,n}-\vartheta\widehat M_{D,n}|
\le L_{\alpha,c}\sqrt{\widehat K_n/n}\right\},
\]

where \(L_{\alpha,c}=\left(\frac{2B_c}{\alpha}\right)^{1/2}\) and \(B_c=32(1+c^{-1})\).

The calibration accounts for uncertainty in both source contrasts and target frequencies. The condition \(k_n=o(n^{1/2})\) controls the error from combining their estimates.

---

## Feasible main result

Retain the causal, transport, boundedness, and weight assumptions. Require uniform source cells, balanced assignment, \(N_n/n\to c>0\), and \(k_n\to\infty\) with \(k_n/\sqrt n\to0\).

@informal thm:finite-cell-unknown-weight-attainment: Under our model and growth assumptions, uniform source cells and balanced assignment allow sample-only uniformly honest inversion with optimal worst-case expected-length order \(\min\{1,t_0^{-1/2}\}\) for every fixed \(t_0>0\).

\[
\limsup_{n\to\infty}\sup_{P\in\mathcal N_n:\,t_n\ge t_0}
\mathbb E_P[\lambda(C_n)]
\le
C_0\min\{1,t_0^{-1/2}\}.
\]

Here \(\mathcal N_n\) is the uniform-cell model class. This bounds the feasible procedure’s worst-case asymptotic expected length; \(C_0>0\) depends on coverage and the sample-size ratio.

A matching lower bound applies to every sample-only honest procedure in this class.

Thus learning target weights preserves the oracle order in this finite-cell experiment.

---

## Open questions

- Feasible weight learning beyond these finite-cell designs, together with assignment-propensity learning.
- Continuous-covariate approximations.
- Moving effective-strength thresholds and sharp expected-length constants.

---

## Takeaways

- Under the causal and transport restrictions, the transported outcome-to-receipt ratio identifies the target complier effect.
- Test residual contrasts to obtain uniform coverage; their noise and slope combine through \(t_n=n\mu_n^2/\kappa_n\).
- Score inversion attains optimal worst-case expected-length order \(\min\{1,t_0^{-1/2}\}\). Hidden compliance types explain the matching lower bound, and finite-cell target-weight learning preserves the order.

---

## Appendix: Identification and causal range

The transported ratio equals the target complier effect and belongs to the bounded causal range.

@formal prop:compact-causal-range

---

## Appendix: Oracle and fixed-geometry frontier

Oracle score inversion is honest and matches the expected-length lower bound globally and within every admissible fixed transport design.

@formal thm:oracle-score-inversion-attainment

---

## Appendix: Finite-cell sample-only attainment

Uniform source cells and balanced encouragement allow target-weight learning with the same honest minimax expected-length order.

@formal thm:finite-cell-unknown-weight-attainment

---

## Appendix: Regular-cell score attainment

Known regular source-cell probabilities and known overlapping propensity allow feasible score inversion with matching expected-length bounds.

@formal thm:regular-cell-unknown-weight-attainment
