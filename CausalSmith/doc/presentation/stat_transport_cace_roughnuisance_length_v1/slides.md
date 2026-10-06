# Confidence Intervals for Transported Complier Effects

How precisely can an encouragement experiment measure treatment effects for compliers in a population that supplies only covariates?

---

## Motivation

An encouragement experiment records covariates, encouragement, treatment receipt and outcomes.

A target population supplies only covariates. We want its average treatment effect among **compliers**: people whose receipt changes when encouraged.

The standard approach transports source encouragement-arm contrasts, divides the outcome contrast by the receipt contrast, and applies the delta method.

Chen and Huang (2025) identify this ratio and establish regular inference under their assignment, selection and moment conditions, at a fixed positive first stage.

Two difficulties interact:

- Rough transport functions leave nonlinear estimation bias after first-order correction.
- Weak compliance makes division by an estimated first stage unstable.

How short can intervals be if coverage must hold even under arbitrarily weak positive compliance?

---

## Key idea

Correct the two transported contrasts through cubic order. Then retain candidate effects whose implied outcome contrast agrees with the estimated outcome contrast.

This separates two tasks: controlling rough-function estimation error and handling weak compliance.

Our setting has independent source and target samples of size \(n\), scalar covariates, bounded outcomes and Hölder-\(1/8\) nuisance functions.

@informal thm:sharp-length-frontier-full-elbow: Under our equal-size Hölder-\(1/8\) model, fixed overlap, valid monotone encouragement and both complier transport equalities, optimal honest expected length is of order \(\min\{1,n^{-1/3}/a\}\) for \(n\ge256\), \(0<a\le1/4\).

Here \(a\) is a compliance floor used to evaluate precision. One observable interval sequence attains this order without knowing \(a\).

---

## Example

Consider a balanced encouragement experiment.

- Both populations have uniform covariates; encouragement probability is one half.
- Compliers have share \(b\); always-takers and never-takers each have share \((1-b)/2\).
- Binary outcomes have mean one half in both encouragement arms.

Its density and arm-mean functions are

\[
f_{\mathrm S}=f_{\mathrm T}=1,\qquad
e=\frac12,\qquad
m_{Dz}=r_z^{(b)},\qquad
m_{Yz}=\frac12,
\]

where \(f_{\mathrm S},f_{\mathrm T}\) are covariate densities, \(e\) is encouragement probability, and \(m_{Az}\) is the mean response \(A\) in arm \(z\). Receipt probability is \(r_z^{(b)}=(1+(2z-1)b)/2\).

For this center law \(P_{\star}\),

\[
\mu(P_{\star})=b,\qquad \theta(P_{\star})=0.
\]

The transported compliance share \(\mu\) is \(b\); the target complier effect \(\theta\) is zero.

Our lower bound will compare this center with rough alternatives that have different effects but are difficult to distinguish observationally.

---

## Model

We observe \(n\) independent source records \((X,Z,D,Y)\) and \(n\) independent target covariates \(X\); the samples are independent.

- \(X\in[0,1]\); encouragement \(Z\) and receipt \(D\) are binary.
- \(D(z)\) is potential receipt under encouragement \(z\).
- \(Y(d)\in[0,1]\) is the potential outcome under receipt \(d\).
- \(C=\mathbf 1\{D(1)>D(0)\}\) indicates a complier; \(S=0\) denotes target membership and \(S=1\) source membership.

The estimand is

\[
\theta=
\frac{\mathbb E_{P_n^F}[(Y(1)-Y(0))C\mid S=0]}
     {\mathbb E_{P_n^F}[C\mid S=0]},
\]

where \(P_n^F\) is the full-data law of populations and potential variables.

The numerator averages effects weighted by complier status; the denominator normalizes by target complier prevalence. Bounded outcomes give the effect domain \(\Theta=[-1,1]\).

---

## Assumptions

**Fixed overlap and roughness.** Both covariate densities lie between fixed envelopes \(0<c_f<1<C_f\). Encouragement probabilities lie between \(1/4\) and \(3/4\). Densities, propensity and four arm means have supremum norm at most \(L>1\) and changes bounded by \(L|x-x'|^{1/8}\).

**Valid encouragement.** Conditional on \(X\), source encouragement is independent of potential variables. Observed variables satisfy consistency, and encouragement affects outcomes through receipt.

**Monotonicity.** \(D(1)\ge D(0)\): encouragement never prevents receipt.

**Two transport equalities.** At almost every target covariate value,

\[
\mathbb E_{P_n^F}[(Y(1)-Y(0))C\mid X=x,S=0]
=
\mathbb E_{P_n^F}[(Y(1)-Y(0))C\mid X=x,S=1],
\]

\[
\mathbb E_{P_n^F}[C\mid X=x,S=0]
=
\mathbb E_{P_n^F}[C\mid X=x,S=1],
\]

These carry the complier-weighted effect and complier prevalence across populations.

In the balanced example, the same conditional potential-variable law in both populations satisfies both equalities.

---

## Identification

Let \(m_{Az}(x)\) be the source mean of response \(A\in\{D,Y\}\) in encouragement arm \(z\), and let \(\Delta_A(x)=m_{A1}(x)-m_{A0}(x)\).

Average each source contrast over the target covariate distribution:

\[
T_A=\int \Delta_A(x)f_{\mathrm T}(x)\,dx.
\]

This computes the transported receipt or outcome contrast.

Validity and monotonicity make the receipt contrast a complier share and the outcome contrast a complier-weighted effect. The two transport equalities then give

\[
\mu=T_D,
\qquad
\theta=\frac{T_Y}{T_D}.
\]

We assume \(\mu>0\), allowing it to approach zero.

@informal lem:transported-cace-identification: Under our sampling, regularity, valid-encouragement, monotonicity and two complier transport restrictions, \(T_D\) equals target complier prevalence and \(T_Y/T_D\) identifies the target complier effect.

---

## Honest inference

Let \(\mathcal M_n\) collect the assumptions just given, including every positive compliance share.

Fix noncoverage probability \(0<\alpha<1\). An interval is **honest** if coverage is at least \(1-\alpha\) at every law in \(\mathcal M_n\).

Evaluate precision on the slice \(\mathcal M_n(a)\), where \(a\le\mu(P)\le1/4\):

\[
L_n(a)
=
\inf_{C_n\in\mathfrak H_n}
\sup_{P\in\mathcal M_n(a)}
\mathbb E_P\!\left[\lambda_{\Theta}(C_n)\right],
\qquad n\ge n_0,\quad 0<a\le\frac14,
\]

Here \(\mathfrak H_n\) is the class of honest connected intervals, \(C_n\) is a candidate procedure, and \(\lambda_{\Theta}\) measures length within the effect domain. The threshold is \(n_0=256\).

This is the smallest worst-case expected length on a strength slice. Coverage remains global; \(a\) evaluates performance and is not an input to our procedure.

---

## Main result

Under our model, with fixed \(\alpha,c_f,C_f,L\), positive constants \(c_0,C_0\) independent of \(n,a\) satisfy, for \(n\ge256\) and \(0<a\le1/4\),

\[
c_0\min\{1,n^{-1/3}/a\}
\le L_n(a)
\le C_0\min\{1,n^{-1/3}/a\}.
\]

This bounds optimal worst-case expected length from both sides.

- At \(a\le n^{-1/3}\), optimal expected length has constant order.
- Above that scale, it has order \(n^{-1/3}/a\).

The same interval sequence \(I_n\) responds to actual compliance:

\[
\mathbb E_P\!\left[\lambda_{\Theta}(I_n)\right]
\le C_0\min\{1,n^{-1/3}/\mu(P)\},
\]

for every \(P\in\mathcal M_n\) and \(n\ge256\). In the balanced example, \(\mu(P_{\star})=b\): even a zero effect becomes difficult to measure when compliance is weak.

@informal thm:honest-upper-full-elbow: Under our model with fixed admissible coverage, density and smoothness constants, \(I_n\) is honest for every positive sample size; for \(n\ge256\), its expected length is at most \(C_0\min\{1,n^{-1/3}/\mu(P)\}\).

---

## Observable density components

Estimate density components from counts and response-weighted counts:

\[
q_z(x)=f_{\mathrm S}(x)P_{\mathrm S}(Z=z\mid X=x),
\qquad
r_{Az}(x)=q_z(x)m_{Az}(x),
\qquad A\in\{Y,D\},\quad z\in\{0,1\}.
\]

Here \(P_{\mathrm S}\) is the source-record law. The arm density \(q_z\) counts records in arm \(z\); \(r_{Az}\) weights those records by receipt or outcome.

Let \(F\) collect the target density, two arm densities and four response-weighted arm densities. Then

\[
T_A=\int_0^1\Phi_A(F(x))\,dx,
\qquad
\Phi_A(F)=f_{\mathrm T}
\left(\frac{r_{A1}}{q_1}-\frac{r_{A0}}{q_0}\right).
\]

The ratios recover arm means; target density weighting transports their difference.

Fixed overlap keeps the arm densities away from zero. Thus the function \(\Phi_A\) has bounded derivatives through order four, even though its unknown inputs vary roughly with covariates.

---

## Bias correction

A histogram pilot \(\widehat F\) estimates the seven density components. Clipping keeps its values within the fixed model bounds.

Plugging the pilot into \(\Phi_A\) leaves nonlinear bias. A linear correction removes first-order error; products of two and three pilot errors still need correction.

Our estimator is

\[
\widehat T_A=
\begin{cases}
\displaystyle
\int_0^1\Phi_A(\widehat F(x))\,dx+
\mathsf L_A+\mathsf Q_A+\mathsf C_A,
& n\ge n_0,\\
0,& n<n_0.
\end{cases}
\]

The pilot integral estimates \(T_A\); \(\mathsf L_A,\mathsf Q_A,\mathsf C_A\) estimate its linear, quadratic and cubic Taylor corrections.

Robins et al. (2008) supply the higher-order functional-estimation approach. Our construction applies it to the seven observable source–target density components.

How can noisy data estimate products of unknown pilot errors?

---

## Independent residual products

Split each sample into one training block and three evaluation blocks. Conditional on the pilot, evaluation blocks are independent.

Let \(H_{i,K}^{(b)}\) be the response-weighted histogram for coordinate \(i\), block \(b\) and \(K\) cells. Its residual is \(R_{i,K}^{(b)}=H_{i,K}^{(b)}-\widehat F_i\).

The quadratic correction is

\[
\mathsf Q_A=
\frac{1}{2K_2}
\sum_{i,j\in\mathcal I}\sum_{\ell=1}^{K_2}
\partial_{ij}\Phi_A(\widehat F(x_{\ell,K_2}))
R_{i,K_2}^{(1)}(x_{\ell,K_2})
R_{j,K_2}^{(2)}(x_{\ell,K_2}).
\]

Here \(\mathcal I\) indexes the seven coordinates, \(x_{\ell,K_2}\) is a cell midpoint, and \(\partial_{ij}\Phi_A\) measures curvature.

Each residual's conditional mean is its cell-averaged pilot error. Independence makes the product's conditional mean the product of those errors.

The cubic term uses three residual factors from distinct blocks. Repeated coordinates also use distinct blocks, preventing evaluation-noise products from introducing bias.

---

## Why cubic order

Write the coordinate pilot error as \(\delta_i(x)=F_i(x)-\widehat F_i(x)\). Its moment bounds are

\[
\mathbb E_P[\delta_i(x)^2]
\le C_{\mathrm{pilot},2}n^{-1/5},
\qquad
\mathbb E_P[|\delta_i(x)|^8]
\le C_{\mathrm{pilot},8}n^{-4/5}.
\]

The constants depend on fixed model bounds. These inequalities control squared and eighth-power errors at every covariate value.

- Linear correction leaves products of two errors.
- Quadratic correction leaves products of three errors.
- Cubic correction leaves products of four errors.

Squaring the fourth-order remainder produces eighth powers. The second bound controls its squared contribution at scale \(n^{-4/5}\), below the required \(n^{-2/3}\).

Independent residual products estimate cell averages. The remaining task is to control what cell averaging loses.

---

## Resolution balance

Within each cell, a function minus its cell average integrates to zero. Terms containing exactly one such difference therefore cancel.

Quadratic approximation error begins with two differences; cubic approximation error also benefits from a remaining pilot-error factor.

| Component | Number of cells | Purpose |
|---|---|---|
| Pilot | \(K_0\asymp n^{4/5}\) | Controls pilot moments |
| Quadratic correction | \(K_2\asymp n^{4/3}\) | Balances approximation error and variance \(n^{-1}+K_2n^{-2}\) |
| Cubic correction | \(K_3\asymp n\) | Controls approximation while limiting product variance |

Combining the Taylor remainder, cell approximation and sampling fluctuations gives

\[
\sup_{P\in\mathcal M_n}
\mathbb E_P\!\left[(\widehat T_A-T_A)^2\right]
\le C_{\mathrm{mse}}n^{-2/3},
\qquad A\in\{Y,D\}.
\]

Both transported contrasts therefore have root-mean-square error at most a constant times \(n^{-1/3}\). The computable constant \(C_{\mathrm{mse}}\) depends on \(c_f,C_f,L\).

---

## Confidence interval

Anderson and Rubin (1949) supply the inversion principle: test the outcome contrast implied by a candidate effect while retaining the first stage inside the moment.

Our acceptance set is

\[
\mathcal A_n
=
\left\{
\theta\in[-1,1]:
\left|\widehat T_Y-\theta\widehat T_D\right|
\le
2\sqrt{\frac{2C_{\mathrm{mse}}}{\alpha}}\,
n^{-1/3}
\right\}.
\]

Each candidate \(\theta\) predicts outcome contrast \(\theta\widehat T_D\). We retain it when its discrepancy from \(\widehat T_Y\) is within the uniform tolerance.

For \(n\ge256\), report this interval if nonempty and \(\{0\}\) otherwise. For smaller samples, report \(\Theta=[-1,1]\).

The procedure uses the coverage level and fixed model bounds, without a compliance floor. Its explicit worst-case calibration constant is highly conservative.

---

## Coverage mechanism

For \(n\ge256\), let \(r_n=\sqrt{2C_{\mathrm{mse}}/\alpha}\,n^{-1/3}\) be the single-contrast radius.

The mean-square bound and Chebyshev's inequality place both contrast errors within \(r_n\) with probability at least \(1-\alpha\).

At the true effect,

\[
\begin{aligned}
|\widehat T_Y-\theta(P)\widehat T_D|
&=
|(\widehat T_Y-T_Y(P))
 +\theta(P)(\mu(P)-\widehat T_D)|\\
&\le|\widehat T_Y-T_Y(P)|
  +|\theta(P)|\,|\widehat T_D-\mu(P)|\\
&\le2r_n.
\end{aligned}
\]

This bounds the true effect's score error using identification, \(T_Y(P)=\theta(P)\mu(P)\), and the effect-domain bound \(|\theta(P)|\le1\).

The true effect is accepted whenever both contrast bounds hold. The calculation remains valid however small positive compliance becomes.

---

## Length mechanism

The estimated first stage is the score's slope as the candidate effect varies.

When \(|\widehat T_D-\mu(P)|\le\mu(P)/2\), the slope has magnitude at least \(\mu(P)/2\). Hence

\[
\lambda_\Theta(I_n)
\le
\min\left\{2,\frac{4r_n}{|\widehat T_D|}\right\}
\le
\min\left\{2,\frac{8r_n}{\mu(P)}\right\}.
\]

Length is bounded by the effect-domain diameter and by score tolerance divided by slope.

The mean-square bound controls the probability of an unreliable slope; length is at most two on those realizations.

Above the rough estimation scale, compliance converts contrast uncertainty into inverse-strength effect uncertainty. At or below that scale, the bounded effect domain supplies the constant-length branch.

What forces every honest procedure to face these same two regimes?

---

## Rough alternatives

Return to the balanced center, now with compliance \(b=\bar a=\max\{a,n^{-1/3}\}\).

Tile \([0,1]\) with sine waves, independently choosing each cell's sign \(\lambda_\ell\). Write the resulting perturbation as \(u=u_\lambda\). Its cell count and height are

\[
K_{\mathrm L}=\lceil n^{4/3}\rceil,
\qquad
\bar a=\max\{a,n^{-1/3}\},
\qquad
h_n=c_{\star}K_{\mathrm L}^{-1/8}.
\]

The small fixed amplitude \(c_{\star}>0\) keeps the alternatives within the model; write \(h=h_n\). Each cell contains \(h\lambda_\ell\sin(2\pi(K_{\mathrm L}x-\ell))\).

Change target density and encouragement together:

\[
f_{\mathrm S}=1,
\qquad
f_{\mathrm T}=1+u_{\lambda},
\qquad
e_1^{(\lambda)}=\frac12+u_{\lambda},
\qquad
e_0^{(\lambda)}=\frac12-u_{\lambda}.
\]

Here \(e_z^{(\lambda)}\) is encouragement-arm probability. Each wave integrates to zero, preserving the target density's total mass.

---

## Coupled outcome means

A continuum index \(\tau\in[-1,1]\) controls outcome changes. Set \(v=\tau u\).

The alternative's receipt and outcome means are

\[
m_{Dz}(x)=r_z^{(b)}=\frac{1+(2z-1)b}{2},
\qquad
m_{Yz}(x)=
\frac12+\frac{\tau u(x)}{1+2(2z-1)u(x)},
\quad z\in\{0,1\}.
\]

Receipt means retain their balanced-center values. Both outcome arms move with the same signed perturbation, but their denominators reflect opposite encouragement changes.

Subtracting the arms gives

\[
\Delta_D(x)=b,\qquad
\Delta_Y(x)=-\frac{u(x)v(x)}{1/4-u(x)^2}.
\]

The receipt contrast stays fixed. Because \(v=\tau u\), the outcome contrast depends on \(u^2\): reversing a cell's sign preserves it.

Small amplitude permits a realization using only compliers, always-takers and never-takers. The same conditional potential-variable law in both populations supplies both transport equalities.

---

## Sign-independent separation

Let \(B(t)=\sin(2\pi t)\) denote one cell's wave, with \(t\in[0,1]\) its local coordinate. Define

\[
J_n
=
h^2\int_0^1
\frac{B(t)^2}{1/4-h^2B(t)^2}\,dt.
\]

This measures the integrated squared perturbation, adjusted for encouragement probabilities.

Transport weights the outcome contrast by \(1+u\). The resulting quadratic term is independent of cell signs; the cubic term integrates to zero because \(B(1-t)=-B(t)\).

Thus every sign configuration at a given \(\tau\) has the same effect:

\[
\theta(Q_{\lambda,\tau})=-\frac{\tau J_n}{b}.
\]

Here \(Q_{\lambda,\tau}\) is the alternative law, whose transported compliance remains \(b\).

Since the denominator in the integral stays bounded away from zero, \(2h^2\le J_n\le4h^2\).

With \(h=c_{\star}K_{\mathrm L}^{-1/8}\) and \(K_{\mathrm L}=\lceil n^{4/3}\rceil\), separation has order \(n^{-1/3}\). Varying \(\tau\) sweeps out a continuum of effects around zero.

---

## Hidden observable changes

The nonlinear arm means arise from source probabilities that change only **linearly** in the signed perturbation:

\[
Q_{\lambda,\tau}(Z=z,D=d,Y=y\mid X=x)
=
e_z^{(\lambda)}(x)R_z^{(b)}(d,y)
+\frac{v_{\lambda,\tau}(x)(2y-1)}4,
\]

where \(d,y\in\{0,1\}\), \(v_{\lambda,\tau}=\tau u_\lambda\), and \(R_z^{(b)}\) is the center's receipt–outcome cell probability. It equals \(r_z^{(b)}/2\) for \(d=1\) and \((1-r_z^{(b)})/2\) for \(d=0\).

Encouragement changes and outcome-cell changes are both linear in \(u_\lambda\). Target density changes are linear too.

Averaging cell signs therefore restores each one-record observed law to the center.

Across records, the common cell signs still induce dependence. Terms using a cell's sign an odd number of times cancel; products using it an even number of times can survive.

The causal contrast survives because it depends on the squared perturbation.

---

## Mixture balance

Let \(M_\tau\) average the alternatives' full two-sample experiments over cell signs. Let \(P_{\star}^{(n,n)}\) be the center's experiment with \(n\) source and \(n\) target records.

The surviving sign products accumulate according to \(n^2h^4/K_{\mathrm L}\). This accounts for evidence from both samples, including their shared cell signs.

The chosen scaling satisfies

\[
n^2\le K_{\mathrm L}^{3/2},
\qquad
h^4=c_{\star}^4K_{\mathrm L}^{-1/2},
\]

so accumulated evidence is bounded by a constant times \(c_{\star}^4\), while effect separation remains proportional to \(h^2\).

The likelihood calculation establishes

\[
1+\chi^2(M_{\tau},P_{\star}^{(n,n)})
\le\exp\{C_{\mathrm{mix}}c_{\star}^4\}.
\]

Here \(\chi^2\) measures squared likelihood discrepancy and \(C_{\mathrm{mix}}\) is a fixed numerical constant. Choosing \(c_{\star}\) sufficiently small gives, uniformly in \(\tau\),

\[
\operatorname{TV}(M_{\tau},P_{\star}^{(n,n)})
\le\frac{1-\alpha}{2}.
\]

Total variation bounds the difference in probability of any data event. The mixture hides the alternatives while preserving their common effect separation.

---

## Why shorter intervals fail

Set \(r_{\mathrm{sep}}=J_n/b\), the radius of the alternatives' effect continuum.

Honesty requires coverage for every alternative. Averaging signs preserves that coverage; mixture closeness transfers it to the center:

\[
P_{\star}^{(n,n)}(t\in C_n)
\ge\frac{1-\alpha}{2},
\qquad
t\in[-r_{\mathrm{sep}},r_{\mathrm{sep}}].
\]

Thus any globally honest confidence set \(C_n\) must include every candidate effect in this continuum with substantial probability under the zero-effect center.

Expected length integrates inclusion probabilities:

\[
\mathbb E_P\!\left[\lambda_{\Theta}(C_n)\right]
=
\int_{\Theta}P(t\in C_n)\,dt.
\]

At the center, this gives expected length at least \((1-\alpha)r_{\mathrm{sep}}\).

Because \(J_n\) has order \(n^{-1/3}\) and \(b=\max\{a,n^{-1/3}\}\), it produces both branches of the frontier.

@informal thm:honest-lower-full-elbow: Under our model with fixed admissible coverage, density and smoothness constants, every globally honest measurable confidence set has worst-case expected length at least \(c_0\min\{1,n^{-1/3}/a\}\) for \(n\ge256\), \(0<a\le1/4\).

---

## Open questions

- What is the exact length frontier when source and target sample sizes grow at unrelated rates, and can one honest interval attain every allocation regime?
- How does the benchmark change with higher-dimensional covariates or unknown smoothness?
- How should inference change under dependent records or alternative transport restrictions?

The unequal-sample question retains the same causal assumptions and requires a matching lower family satisfying monotonicity.

---

## Takeaways

- Valid monotone encouragement and two conditional transport equalities identify the target complier effect as a ratio of transported contrasts.
- Cubic correction controls rough estimation error; score inversion preserves coverage under arbitrarily weak positive compliance.
- Squared perturbations change the effect while sign averaging hides observable changes, forcing optimal expected length of order \(\min\{1,n^{-1/3}/a\}\).

---

## Appendix: Sharp length frontier

The exact result combines global finite-sample coverage, matching optimal-length bounds and a law-specific guarantee for one interval sequence.

@formal thm:sharp-length-frontier-full-elbow

---

## Appendix: Honest upper length envelope

The attaining interval covers throughout the model and has expected length bounded according to actual transported compliance.

@formal thm:honest-upper-full-elbow

---

## Appendix: Honest length lower bound

Every globally honest measurable confidence set faces the matching worst-case expected-length bound, including disconnected sets.

@formal thm:honest-lower-full-elbow
