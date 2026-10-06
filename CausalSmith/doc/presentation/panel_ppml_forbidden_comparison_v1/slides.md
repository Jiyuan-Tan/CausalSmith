# When Pooled Poisson Gets the Sign Wrong

A pooled Poisson treatment coefficient can be negative even when treatment raises the mean outcome in every treated cohort and period.

---

## Research question

A practitioner wants one number summarizing a policy adopted by different groups at different dates.

- With multiplicative outcomes, a natural choice is Poisson pseudo-maximum likelihood (PPML) with unit effects, time effects, and one treatment indicator.
- Wooldridge (2023) supplies the multiplicative untreated-mean framework for nonlinear difference-in-differences.
- In linear regressions, de Chaisemartin and D'Haultfoeuille (2020) show that heterogeneous effects can receive negative weights.

Does pooling proportional effects in fixed-effect Poisson preserve their sign?

---

## Key idea

The pooled coefficient is a **population projection**: the best fit to outcome means using fixed effects and one common treatment coefficient.

Increasing one cell's effect also changes the fitted fixed effects. The treatment variation left in that cell can be negative, pushing the pooled coefficient downward.

@informal prop:four-cohort-sign-reversal: With four equal-share cohorts, flat untreated means, multiplier \(4\) at \((2,4)\), and \(101/100\) elsewhere treated, every effect is positive but the limiting pooled Poisson coefficient is negative.

Under multiplicative untreated means, stable positive cohort shares and baselines, full rank, and the specified adoption support, an index \(\Phi\) built from mean totals gives the coefficient's exact sign.

---

## Example

Four periods; equal-sized cohorts adopt in periods 2, 3, and 4, or never. Every untreated mean equals one.

The entries are observed mean multipliers:

| Adoption cohort | Period 1 | Period 2 | Period 3 | Period 4 |
|---|---|---|---|---|
| 2 | \(1\) | \(x\) | \(x\) | \(y\) |
| 3 | \(1\) | \(1\) | \(x\) | \(x\) |
| 4 | \(1\) | \(1\) | \(1\) | \(x\) |
| Never | \(1\) | \(1\) | \(1\) | \(1\) |

Here \(x>1\) is the treated multiplier outside the early cohort's final period; \(y>1\) is that final-period multiplier.

The sign index specializes to

\[
\Phi=\frac{5x^2+12x-2y-15}{16}.
\]

Set \(x=101/100\) and \(y=4\): every treatment effect is positive, but \(\Phi=-11559/32000\), so the pooled coefficient is negative.

---

## Model

Let \(g\) index adoption cohorts in the finite set \(\mathcal C\), and \(t\) index the \(T\) periods. Treatment is absorbing; \(D_{gt}\) equals one from adoption onward.

\[
m_{gt}=\bar b_g\exp(\gamma_{t0})\exp(D_{gt}\delta_{gt}),
\qquad
H=\{(g,t):g\in\mathcal C,\ D_{gt}=1\}.
\]

This gives the observed cohort-period mean \(m_{gt}\); \(H\) is the set of treated cells.

- **Multiplicative untreated means:** each unit has a positive baseline and shares the calendar multiplier \(\exp(\gamma_{t0})\). The limiting cohort-average baseline is \(\bar b_g\).
- **Proportional effects:** treatment multiplies the untreated mean by \(\exp(\delta_{gt})\), common within each cohort-period cell but varying across cells.

Write \(B_{gt}=\bar b_g\exp(\gamma_{t0})\) for the untreated mean. In our example, \(B_{gt}=1\) everywhere.

---

## From units to cohorts

The motivating regression has unit effects. Why can we analyze cohort effects instead?

Within a cohort, every unit has the same treatment path and the same cohort-period treatment multipliers. Its mean path differs from other units' paths only through its positive baseline scale.

- Fitting each unit effect absorbs that scale.
- After fitting unit effects, the time and treatment scores depend on unit baselines only through their cohort averages.
- Replacing units by cohort means, weighted by cohort shares, therefore preserves the population treatment coefficient exactly at each panel size.

Let \(\beta_N^\star(\delta)\) denote the unit-effect population coefficient with \(N\) units. Under the model, support, stability, and rank conditions:

\[
\beta_N^\star(\delta)\longrightarrow \beta^\star(\delta)
\qquad\text{as }N\to\infty .
\]

Thus the limiting cohort-mean criterion retains the treatment coefficient from the unit-effect population fit.

---

## Population projection

Pooling replaces the heterogeneous log effects \(\delta_{gt}\) with one coefficient.

\[
L(\theta;\delta)
=
\sum_{g\in\mathcal C}\sum_{t=1}^T
q_{gt}
\left\{
m_{gt}(\delta)\,r_{gt}'\theta-\exp(r_{gt}'\theta)
\right\}.
\]

This is the population Poisson criterion, evaluated at means.

- The cell mass is \(q_{gt}=\pi_g/T\), where \(\pi_g\) is the limiting cohort share.
- The regressor vector \(r_{gt}\) contains cohort effects, time effects, and treatment; \(\theta\) contains their coefficients.
- Its maximizer is \(\theta^\star(\delta)\); the treatment coordinate is \(\beta^\star(\delta)\).

\[
\mu^\star_{gt}(\delta)=\exp\{r_{gt}'\theta^\star(\delta)\}.
\]

This is the fitted cohort-period mean. Our sign results concern this population fit.

---

## Assumptions

The global sign result uses the model plus four conditions:

- **Support:** \(T\ge 4\); cohorts include adoption dates 2, 3, and 4 and a never-treated cohort. No cohort adopts in period 1.
- **Stability:** every unit belongs to this fixed finite cohort set. Cohort shares converge to \(\pi_g\in(0,1)\), and cohort-average baselines converge to \(\bar b_g\in(0,\infty)\).
- **Full rank:** treatment cannot be reproduced exactly by cohort and time effects. This preserves separate treatment variation.
- **Positive effects:** \(\delta_{gt}>0\) in every treated cell.

Our example has equal shares and constant baselines. Its positive multipliers satisfy the positive-effect condition despite the negative pooled coefficient.

---

## Common-effect benchmark

@informal prop:homogeneous-effect-reduction: Under multiplicative untreated means, positive baselines and cohort shares, and full rank, if every treated cell has the same log effect \(\delta_0\), pooled PPML recovers that effect exactly.

\[
\beta^\star(\delta)=\delta_0,
\]

Here \(\delta_0\) is the common treated-cell log multiplier.

\[
\mu^\star_{gt}(\delta)
=
B_{gt}\exp(D_{gt}\delta_0).
\]

The fitted mean equals the actual mean in every cell: fixed effects plus treatment fit the entire mean structure.

In our four-cohort family, this benchmark is \(y=x\). Why can allowing \(y\) to differ change the pooled sign?

---

## Mean totals

The global diagnostic starts with observed means weighted by cohort shares.

\[
h_{gt}
=
\pi_g B_{gt}\exp(D_{gt}\delta_{gt}),\qquad
R_g=\sum_t h_{gt},\qquad
C_t=\sum_g h_{gt},
\]

Here \(h_{gt}=\pi_g m_{gt}\) is the share-weighted observed mean; \(R_g\) is its cohort total, and \(C_t\) its period total.

\[
M=\sum_g R_g,\qquad
A=\sum_{g,t}D_{gt}h_{gt}.
\]

The grand total is \(M\). The observed total in treated cells is \(A\).

These totals let us compare observed treated outcomes with what fixed effects alone would allocate to treated cells.

---

## Main result

Define the difference between the observed treated total and the allocation implied by cohort and period totals:

\[
\Phi(\delta)
=
M A
-
\sum_{g,t} D_{gt} R_g C_t,
\]

The first term scales the observed treated total \(A\) by the grand total \(M\). The second sums products of cohort totals \(R_g\) and period totals \(C_t\) over treated cells.

@informal thm:primitive-global-frontier: Under our multiplicative mean model, support, stability, full-rank, and positive-effect conditions, the pooled population coefficient has exactly the sign of \(\Phi\).

\[
\beta^\star(\delta)<0\iff \Phi<0,\qquad
\beta^\star(\delta)=0\iff \Phi=0,\qquad
0<\beta^\star(\delta)\iff 0<\Phi .
\]

Positive cell effects alone do not determine the pooled sign. In our example, \(\Phi=-11559/32000\) establishes a negative coefficient.

---

## Why the index works

Set the treatment coefficient to zero and fit only cohort and time effects.

1. Their score equations require the fit to match observed cohort and period totals.
2. Matching both margins allocates the share-weighted fitted mean \(R_g C_t/M\) to cell \((g,t)\).
3. The observed treated total is \(A\). Subtracting the fitted allocation over treated cells gives \(\Phi/M\).
4. This discrepancy has the sign of the treatment score at zero.

The Poisson criterion is concave. A negative score at zero puts the maximizing coefficient below zero; a positive score puts it above zero.

The index diagnoses the pooled sign without solving for its magnitude. What makes a particular treated cell push that coefficient downward?

---

## Removing fixed effects

Increasing one treated mean changes the fixed effects needed to match cohort and period totals. The cell's remaining treatment variation determines its influence on the pooled coefficient.

Let \(X_{gt}\) contain the cohort and time regressors, and let \(\rho\) be their auxiliary regression coefficients.

\[
\rho^\star(\delta)
\in
\arg\min_{\rho\in\mathbb R^{|\mathcal C|+T-1}}
\sum_{g\in\mathcal C}\sum_{t=1}^T
q_{gt}\,\mu^\star_{gt}(\delta)\{D_{gt}-X_{gt}'\rho\}^2.
\]

This projects treatment on fixed effects, weighting each cell by its mass times its fitted Poisson mean.

\[
\widetilde W_{gt}(\delta)=D_{gt}-X_{gt}'\rho^\star(\delta).
\]

The residual \(\widetilde W_{gt}\) is the treatment variation left after that projection. The weights depend on fitted means, so they change with treatment effects.

---

## The local sign rule

@informal thm:sharp-ppml-forbidden-sign: With positive cohort shares and baselines and full rank, increasing a treated-cell log effect lowers \(\beta^\star\) exactly when that cell's fitted-mean-weighted treatment residual is negative.

For a treated cell \((k,s)\), the derivative with respect to its log effect is

\[
\frac{
q_{ks}\,B_{ks}\exp(\delta_{ks})\,\widetilde W_{ks}(\delta)
}{
\mathcal E(\delta)
}.
\]

Here \(q_{ks}\) is cell mass, \(B_{ks}\exp(\delta_{ks})\) is the treated mean, and \(\widetilde W_{ks}\) is residualized treatment.

The denominator measures remaining weighted treatment variation:

\[
\mathcal E(\delta)
=
\sum_{g\in\mathcal C}\sum_{t=1}^T
q_{gt}\,\mu^\star_{gt}(\delta)\,
\widetilde W_{gt}(\delta)^2 .
\]

Full rank makes \(\mathcal E(\delta)>0\). Only the residual can change the derivative's sign.

---

## Example revisited

In the four-cohort design, at zero treatment effects the residualized treatment values are

\[
\frac{1}{8}
\begin{pmatrix}
-3 & 3 & 1 & -1\\
-1 & -3 & 3 & 1\\
1 & -1 & -3 & 3\\
3 & 1 & -1 & -3
\end{pmatrix},
\]

Rows are cohorts \(2,3,4,\infty\); columns are periods \(1,2,3,4\). Here \(\infty\) denotes the never-treated cohort.

The early-treated cohort's final cell has \(\widetilde W_{2,4}=-1/8\). Raising its log effect from zero moves the pooled coefficient downward, with derivative \(-1/10\).

This negative derivative persists near zero with small strictly positive effects.

The residual explains the local mechanism. The index \(\Phi\) establishes the global reversal when that cell's multiplier is \(4\).

---

## A positive causal summary

Moreau-Kastler (2025) motivates proportional treatment on the treated, denoted \(PTT\), weighted by untreated counterfactual exposure.

Recover the untreated mean using only observed means:

\(B^{obs}_{gt}=m_{g1}(m_{\infty t}/m_{\infty1})\).

- \(m_{g1}\) is cohort \(g\)'s period-1 mean, before any adoption.
- \(m_{\infty t}/m_{\infty1}\) is the never-treated cohort's proportional change from period 1 to \(t\).
- Multiplicative untreated means give every cohort this same time multiplier. Thus this product equals \(B_{gt}\).

\[
PTT
=
\frac{\sum_{(g,t)\in H} q_{gt}m_{gt}}
{\sum_{(g,t)\in H} q_{gt}B^{obs}_{gt}}
-1.
\]

This compares observed outcomes in treated cells with their recovered untreated total. It averages \(\exp(\delta_{gt})-1\) with positive weights proportional to \(q_{gt}B_{gt}\).

\[
\Phi<0
\quad\Longrightarrow\quad
\beta^\star(\delta)<0<PTT .
\]

Under our conditions, a negative pooled coefficient can coexist with a positive proportional causal aggregate.

---

## Open questions

- Estimate the mean primitives and develop a sampling distribution for \(\Phi\).
- Construct operational positive-weight estimators from granular proportional effects.
- Determine how often sign reversal occurs in empirically calibrated designs.

---

## Takeaways

- With a common proportional effect, pooled fixed-effect PPML recovers the common log multiplier exactly.
- With heterogeneous effects, fixed-effect adjustment can leave negative treatment variation in a treated cell. Increasing that cell's effect then lowers the pooled coefficient.
- Under our conditions, \(\Phi\) gives the pooled coefficient's exact sign, while aggregation by untreated counterfactual exposure preserves the sign of positive cell effects.

---

## Appendix: Sharp PPML sign

The derivative of the pooled population coefficient has exactly the sign of the treated cell's weighted treatment residual.

@formal thm:sharp-ppml-forbidden-sign

---

## Appendix: Four-cohort sign reversal

Equal shares, flat untreated means, and strictly positive effects can produce a negative limiting pooled coefficient.

@formal prop:four-cohort-sign-reversal

---

## Appendix: Homogeneous effect reduction

A common treated-cell log multiplier is recovered exactly under multiplicative untreated means and full rank.

@formal prop:homogeneous-effect-reduction

---

## Appendix: Primitive sign frontier

A scalar built from mean totals gives the pooled coefficient's exact sign and establishes its contrast with a positive proportional target.

@formal thm:primitive-global-frontier
