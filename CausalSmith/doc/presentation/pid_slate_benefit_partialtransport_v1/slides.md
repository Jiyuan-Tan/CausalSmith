# Who Benefits When Outcomes Are Missing?

We bound the fraction who benefit from treatment among people whose receipt responds to an offer and whose outcome would be observed either way.

---

## Research question

- A training offer changes treatment receipt, while wage categories are observed only for employed people.
- Comparing employed recipients with employed nonrecipients mixes treatment effects with differences in who is employed.
- **Survivor compliers** respond to the offer and would be observed under either treatment. Kennedy et al. (2019) study this group.
- Dong and Heiler (2026) recover selected-complier information when selection directions vary with covariates.
- Lu et al. (2018) bound ordinal benefit from complete outcome margins. Here, the selected groups can differ in size, and survivor membership is unknown.

What fraction of survivor compliers would have a strictly higher outcome under treatment?

---

## Key idea

An outcome bin supplies a **capacity**: the selected-complier probability mass available at that level.

Selection monotonicity makes the two selected groups nested within each covariate cell. Their smaller total is exactly the survivor-complier mass.

Pair that amount across the outcome lists, allowing unused capacity in the larger group.

Under the IV and selection assumptions, ordered outcomes give closed formulas for the smallest and largest possible benefit shares. Both endpoints are attainable.

The unknown pairing remains uncertain; its total mass becomes known.

---

## Example

One covariate cell \(x^{\star}\), three outcome levels, and full compliance: receipt equals instrument assignment. Each assignment has probability \(1/2\).

Entries are joint probabilities of selection and outcome, conditional on assignment.

| Outcome status | Untreated arm | Treated arm |
|---|---:|---:|
| Selected, level 0 | 0.075 | 0.10 |
| Selected, level 1 | 0.10 | 0.25 |
| Selected, level 2 | 0.075 | 0.15 |
| Not selected | 0.75 | 0.50 |

Assume treatment can increase selection without removing anyone. The untreated selected mass \(1/4\) consists entirely of survivors; the treated selected mass is \(1/2\).

\[
\Theta_I(P_{\mathrm{obs}}^{\star})
=
\left[0,\frac{7}{10}\right].
\]

Here \(P_{\mathrm{obs}}^{\star}\) denotes these data, and \(\Theta_I\) is the set of compatible benefit probabilities. The same data permit both zero benefit and 70% benefit.

Which people and outcome pairs make these endpoints possible?

---

## Model

\(X\) indexes finitely many covariate cells. The instrument \(Z\), receipt \(D\), and selection \(S\) are binary. The observed outcome \(Y\) has ordered levels \(\mathcal Y=\{0,\ldots,K-1\}\), with \(K\ge3\).

Potential receipts \(D_0,D_1\) vary instrument assignment:

\[
D=D_Z
\]

Potential selections \(S_0,S_1\) vary received treatment:

\[
S=S_D
\]

Potential outcomes \(Y_0,Y_1\) also vary received treatment:

\[
Y=Y_D
\]

The last equation applies when \(S=1\). Together, these equations impose consistency and exclude direct instrument effects on selection and outcomes.

Compliers are \(C=\{D_0=0,D_1=1\}\). Our target is \(\theta=P(Y_1>Y_0\mid S_1=S_0=1,C)\): strict improvement for the same survivor complier.

---

## Assumptions

\[
(D_0,D_1,S_0,S_1,Y_0,Y_1)\perp Z\mid X.
\]

**IV independence:** within each covariate cell, assignment is independent of all potential receipts, selections, and outcomes.

- **Consistency and exclusion:** the three model equations connect observed variables to potential variables through received treatment.
- **Overlap:** \(\varepsilon_Z\le\pi(x)\le1-\varepsilon_Z\), where \(\pi(x)=P(Z=1\mid X=x)\) and \(0<\varepsilon_Z<1/2\). Both assignments occur in each supported cell.
- **Treatment monotonicity:** \(D_1\ge D_0\). Nobody takes treatment only under the lower instrument state.
- **Cellwise selection monotonicity:** among compliers within a cell, either everyone satisfies \(S_0\le S_1\), or everyone satisfies \(S_1\le S_0\). The direction may differ across cells.
- **Positive survivor mass:** the aggregate survivor-complier probability \(M\) is positive.

In the example, everyone complies and \(S_0\le S_1\): treatment adds selected people without removing anyone.

---

## Recovering the capacities

Use joint events containing receipt, selection, and outcome. Condition on assignment and covariates—not on receipt.

For untreated level \(i\), define:

\(\ell_i(x)=P(D=0,S=1,Y=i\mid Z=0,X=x)-P(D=0,S=1,Y=i\mid Z=1,X=x)\).

For treated level \(j\), reverse the subtraction:

\(h_j(x)=P(D=1,S=1,Y=j\mid Z=1,X=x)-P(D=1,S=1,Y=j\mid Z=0,X=x)\).

Instrument independence makes the groups whose receipt never changes cancel. Treatment monotonicity leaves compliers:

\[
\ell_i(x)=P(Y_0=i,S_0=1,C\mid X=x)
\]

This identifies untreated selected-complier mass at level \(i\).

\[
h_j(x)=P(Y_1=j,S_1=1,C\mid X=x)
\]

This identifies treated selected-complier mass at level \(j\). Add each arm’s capacities:

\[
q_0(x)=\sum_{i\in\mathcal Y}\ell_i(x),
\qquad
q_1(x)=\sum_{j\in\mathcal Y}h_j(x),
\]

The totals count selected compliers under each treatment.

\[
\Delta q(x)=q_1(x)-q_0(x),
\qquad
m(x)=\min\{q_0(x),q_1(x)\}.
\]

The gap \(\Delta q(x)\) measures the selection change. Nested selected groups have intersection mass \(m(x)\).

In the example, \(q_0=1/4\), \(q_1=1/2\), and \(m=1/4\); another \(1/4\) is selected only under treatment. Equal totals imply equal selection status among compliers.

We know how many survivors there are, while their membership in the larger group remains unknown.

---

## Pairing exactly the survivors

Let \(\gamma_{ij,x}\) be survivor-complier mass with untreated outcome \(i\) and treated outcome \(j\), conditional on cell \(x\).

\[
\Gamma_x^{\ast}
=
\left\{
\gamma_x\ge0:
\sum_{j\in\mathcal Y}\gamma_{ij,x}\le\ell_i(x),\
\sum_{i\in\mathcal Y}\gamma_{ij,x}\le h_j(x),\
\sum_{i,j\in\mathcal Y}\gamma_{ij,x}=m(x)
\right\}.
\]

The set \(\Gamma_x^{\ast}\) contains feasible pairing arrays: each row and column respects its available capacity, and exactly the survivor mass is paired.

Benefit mass is \(b_x(\gamma_x)=\sum_{i<j}\gamma_{ij,x}\): count pairs with a higher treated outcome.

In the example, every untreated capacity must be used, while only \(1/4\) of the treated capacity is used.

Separately normalizing the two selected lists would pair different populations. These constraints retain the uncertainty about which treated selected people are survivors.

---

## Main result

Let \(B_L(x)\) and \(B_U(x)\) be the minimum and maximum feasible benefit masses in cell \(x\).

Write \(p_x=P(X=x)\) for its population weight and \(M=\sum_xp_xm(x)\) for aggregate survivor-complier mass.

@informal thm:sharp-exact-mass-threshold-interval: In the finite ordered-outcome model, IV independence, consistency/exclusion, overlap, treatment monotonicity, cellwise selection monotonicity and \(M>0\) make the threshold interval exactly the feasible benefit probabilities.

\[
\Theta_I(P_{\mathrm{obs}})
=
\left[
\frac{\sum_{x\in\mathcal X}p_xB_L(x)}{M},
\frac{\sum_{x\in\mathcal X}p_xB_U(x)}{M}
\right].
\]

Here \(P_{\mathrm{obs}}\) is the observed-data law. Each endpoint adds population-weighted benefit masses and divides by population-weighted survivor mass.

**Sharpness:** every value in this interval is compatible with the data and assumptions.

For the example, \(B_L=0\), \(B_U=7/40\), and \(M=1/4\), giving \([0,0.7]\).

How do we find—and attain—the two cell endpoints?

---

## Upper threshold bound

Choose an outcome threshold \(t\). Write \(\ell_{<t}(x)=\sum_{i<t}\ell_i(x)\) for untreated mass below it and \(h_{>t}(x)=\sum_{j>t}h_j(x)\) for treated mass above it.

Every beneficial pair \(i<j\) uses at least one of these two capacities: if \(i\ge t\), then \(j>t\).

\[
B_U(x)
=
\min\left\{
m(x),\
\min_{t\in\mathcal Y}\bigl[\ell_{<t}(x)+h_{>t}(x)\bigr]
\right\}.
\]

Maximum benefit mass is limited by survivor mass and by the tightest threshold capacity.

In the example, \(t=2\) leaves only untreated levels 0 and 1 available for improvement. Their mass is \(7/40\).

The bound is necessary. Why is it sufficient?

---

## Ordered pairing

To maximize benefit, serve untreated levels from highest to lowest: higher starting outcomes have fewer improving partners.

1. For the current untreated level \(i\), find the lowest treated level with unused capacity and \(j>i\).
2. Pair as much mass as those two bins allow. Advance whenever a bin is exhausted.
3. If no improving partner remains, leave that row’s residual for completion. Continue to lower untreated levels.
4. Stop the benefit allocation if it reaches survivor mass \(m(x)\).

A lower untreated level can use every improving partner available to a higher level. Exchanging partners therefore protects the hardest-to-match rows without losing benefit.

For rows \(i\ge t\), the combined improving partner set is \(j>t\). Any collection’s partner set is determined by its lowest level; adding all higher rows increases demand without expanding that set.

Thus consecutive upper groups give the strongest shortages. Rows below \(t\) contribute at most \(\ell_{<t}(x)\); the rest share at most \(h_{>t}(x)\).

The ordered pairing exhausts these shortages. Complete to mass \(m(x)\) with residual capacities; no available improving pair remains unless the benefit allocation already reached \(m(x)\).

---

## Example: Attaining 70%

Apply the ordered pairing to the same three-level capacities.

| Untreated \(Y_0\) | Treated \(Y_1\) | Survivor mass | Role |
|---:|---:|---:|---|
| 1 | 2 | \(1/10\) | Improving pair |
| 0 | 1 | \(3/40\) | Improving pair |
| 2 | 0 | \(3/40\) | Residual completion |

Level 2 cannot improve. Match level 1 to level 2, then level 0 to level 1. Improving mass is \(7/40\); completion brings survivor mass to \(1/4\), giving benefit share \(7/10\).

Assign unused treated capacity to the \(1/4\) selected only under treatment. The remaining \(1/2\) are never selected. This reproduces the observed arms.

More generally, put unused selected capacity into the one-sided selected-complier group allowed by selection monotonicity, put remaining compliers into the never-selected group, and preserve people whose receipt is always zero or always one.

@informal thm:full-law-endpoint-attainment: Under IV independence, consistency/exclusion, overlap, treatment monotonicity, cellwise selection monotonicity and \(M>0\) in the finite ordered-outcome model, both endpoint pairings extend to full causal laws reproducing the observed data.

Combine cell constructions using \(p_x\). Mixing lower and upper compatible laws preserves the data and assumptions and produces every intermediate benefit probability.

Sharpness describes complete causal explanations, as well as feasible pairing arrays.

---

## Lower threshold bound

Write \(\ell_{\le t}(x)=\sum_{i\le t}\ell_i(x)\) and \(h_{\le t}(x)=\sum_{j\le t}h_j(x)\) for capacities through threshold \(t\).

Survivors starting at or below \(t\) can avoid improvement only by using treated outcomes at or below their starting level.

\[
B_L(x)
=
\max\left\{
0,\
\max_{t\in\mathcal Y}\bigl[\ell_{\le t}(x)-h_{\le t}(x)\bigr]
+\min\{\Delta q(x),0\}
\right\}
\]

The largest shortage of low treated outcomes forces benefit. When untreated selected mass is larger, the correction \(\min\{\Delta q(x),0\}\) subtracts untreated capacity that can belong to nonsurvivors.

To attain minimum benefit, maximize pairs that do **not** improve, \(j\le i\):

1. Serve untreated levels from lowest to highest.
2. Use the highest remaining treated level satisfying \(j\le i\), allocating until a bin is exhausted.
3. Complete to survivor mass \(m(x)\) with residual capacities.

Lower starting levels have fewer nonimproving partners. For any collection of rows, those partners are determined by its highest level; adding all lower rows adds demand without adding partners. Only lower-prefix shortages can force improvement.

After maximizing nonimproving mass, every residual pair needed for completion improves.

In the example, every untreated prefix fits within the treated prefix. Diagonal pairs with masses \(0.075,0.10,0.075\) fill survivor mass: \(B_L=0\), and nobody benefits.

---

## Estimation

Take independent observations from the same observed-data law.

Replace the observable conditional probabilities with empirical frequencies. Set negative estimated capacities to zero, then apply the same totals and threshold formulas.

Screen out cells with very small estimated contributions to survivor mass:

\[
\widehat r_x=\widehat p_x\widehat m(x),
\qquad
\widehat I_x=\mathbf 1\{\widehat r_x>\eta_n\}.
\]

Here \(\widehat p_x\) estimates the cell weight, \(\widehat m(x)\) estimates survivor mass, and \(\widehat I_x\) indicates retention. Choose \(\eta_n>0\), with \(\eta_n\to0\) and \(\sqrt n\,\eta_n\to\infty\).

\[
\widehat\Psi_n=
\begin{cases}
\left(\widehat N_{L,n}/\widehat M_n,\ \widehat N_{U,n}/\widehat M_n\right),
& \widehat M_n>0,\\
(0,1), & \widehat M_n=0.
\end{cases}
\]

The denominator \(\widehat M_n\) adds retained, cell-weighted survivor masses. The numerators \(\widehat N_{L,n}\) and \(\widehat N_{U,n}\) add retained, cell-weighted benefit masses. Their ratios estimate the interval endpoints.

---

## Guarded inference

Maintain the structural assumptions, independent sampling, fixed finite supports, common overlap \(\varepsilon_Z\), and a known bound \(M\ge m_{\star}>0\). Use the screening sequence above and \(0<\alpha<1\).

\[
\mathcal C_{1-\alpha,n}
=
\left[
\max\{0,\widehat\Psi_{n,L}-g_{n,\alpha}\},\
\min\{1,\widehat\Psi_{n,U}+g_{n,\alpha}\}
\right].
\]

The interval \(\mathcal C_{1-\alpha,n}\) expands the estimated endpoints by deterministic padding \(g_{n,\alpha}\), then restricts them to probabilities.

The padding controls **sampling error plus mass lost through screening**. The positive mass bound \(m_{\star}\) controls division by survivor mass.

@informal thm:uniform-deterministic-guard: Under the structural assumptions, independent sampling, fixed finite supports, common overlap, \(M\ge m_{\star}>0\) and the prescribed screening sequence, the guarded interval covers the entire sharp interval with probability at least \(1-\alpha\), uniformly.

Thus \(P\{\Theta_I(P_{\mathrm{obs}})\subseteq\mathcal C_{1-\alpha,n}\}\ge1-\alpha\) throughout this class, at every sample size.

**Practical width:** with three levels, one cell, \(\varepsilon_Z=1/4\), \(\alpha=0.05\), and \(m_{\star}=1/4\), the current guard gives \([0,1]\) below roughly \(10^{11}\) observations.

---

## Further results

@informal thm:linear-sparse-threshold-flow: For nonnegative capacities on finite covariate support with \(K\ge3\), both threshold endpoints and sparse attaining pairings can be computed with work bounded by \(O(|\mathcal X|K)\).

@informal thm:branch-free-pointwise-directional-limit: At a fixed law, under the structural and sampling assumptions, fixed finite supports, prescribed screening, and the multinomial and directional delta-method inputs, the estimator is consistent and has a directional limit.

A directional limit describes how the endpoint changes under small perturbations; tied thresholds can make that response nonlinear.

---

## Open questions

- **Useful confidence widths:** sharper concentration bounds and simulations are needed to make the uniform guard practical.
- **Calibrated inference:** can resampling handle simultaneous threshold ties and changing retained cells when selection gaps stay bounded away from zero?
- **Extensions:** empirical reanalysis, continuous outcomes, sensitivity to selection monotonicity, and restrictions linking the two potential outcomes.

---

## Takeaways

- Joint instrument-arm contrasts identify selected-complier capacities. Selection monotonicity identifies their common survivor mass.
- Pair exactly that mass. Ordered partner sets make threshold shortages the only obstacles, and ordered pairing constructs both endpoints.
- The resulting interval is sharp. Empirical formulas estimate it; uniform whole-interval coverage is available with currently impractical padding.

---

## Appendix: Sharp exact-mass interval

The threshold formulas give exactly the feasible benefit probabilities, including equal-total and zero-survivor cells.

@formal thm:sharp-exact-mass-threshold-interval

---

## Appendix: Endpoint law attainment

Both endpoints are realized by full potential-outcome laws preserving the observed data and structural restrictions.

@formal thm:full-law-endpoint-attainment

---

## Appendix: Branch-free endpoint limit

At a fixed law, screening recovers the positive-survivor cells and the estimated endpoints have a directional limit.

@formal thm:branch-free-pointwise-directional-limit

---

## Appendix: Uniform deterministic guard

The guarded confidence interval contains the entire sharp identified interval uniformly at every sample size.

@formal thm:uniform-deterministic-guard

The padding is computed from:

\[
b_{n,\alpha}=\sqrt{\frac{|\mathcal E|}{4n\alpha}}.
\]

Here \(b_{n,\alpha}\) bounds empirical frequency error across the finite event collection \(\mathcal E\).

\[
A_{n,\alpha}
=
\frac{64K|\mathcal X|}{\varepsilon_Z^2}b_{n,\alpha}
+
|\mathcal X|\eta_n,
\]

The envelope \(A_{n,\alpha}\) combines sampling error and screening error; \(|\mathcal X|\) is the number of covariate cells.

\[
g_{n,\alpha}
=
\min\left\{1,\frac{4A_{n,\alpha}}{m_{\star}}\right\}.
\]

The padding \(g_{n,\alpha}\) converts that envelope to endpoint error using the known mass bound \(m_{\star}\).

The events are \(\{X=x\}\), \(\{X=x,Z=z\}\), and \(\{X=x,Z=z,D=d,S=1,\widetilde Y=k\}\), where \(\widetilde Y\) records the outcome when selected.

\[
|\mathcal E|=|\mathcal X|+2|\mathcal X|+4K|\mathcal X|
=|\mathcal X|(4K+3).
\]

This counts all cell, assignment-arm, and selected-outcome events used by the guard.
