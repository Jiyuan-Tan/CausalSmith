# Treatment Effects When Assignment Scores Lose Their Links

Labels attached to trial outcomes let us measure lost information, choose how much to retain, and account for the remaining uncertainty.

---

## Research question

A randomized trial releases treatment \(A\), outcome \(Y\), and a label \(R=g(E)\) of each person’s assignment probability \(E\). We know the score distribution \(H\) and label rule \(g\).

- We want the population average treatment effect (ATE).
- Inverse-probability weighting needs each outcome’s own assignment probability: Horvitz and Thompson (1952).
- Knowing the distribution of weights does not recover their association with outcomes.
- Fan et al. (2014) gives sharp treatment-effect bounds for fixed combined-data distributions.

How much uncertainty remains, and how should we design the labels?

---

## Key idea

Within each treatment–label cell, we know the outcome distribution and the reciprocal-weight distribution. Only their association is missing.

Pairing their ranks gives the exact ATE interval. Maximizing its width over outcome distributions gives a score-only design criterion, \(D_H(g)\).

@informal thm:all-label-ambiguity: With outcomes in \([0,1]\), fixed overlap, any score law \(H\), and any measurable finite-label rule \(g\), maximum sharp ATE width has an exact score-only formula, attained by half-zero, half-one outcomes in every positive-mass arm-label cell.

A positive score-density floor makes the best ambiguity with \(K\) labels of order \(K^{-1}\). For continuous positive densities, we also obtain the exact leading constant and an attaining allocation.

---

## Example

Half the population has \(E=1/4\); half has \(E=3/4\). Everyone receives the same label. Observed outcomes are half zeros and half ones in each arm.

- Higher scores are more common among treated rows; control assignment reverses this tilt.
- Within either arm, ones can belong to larger or smaller reciprocal assignment weights.
- The attainable mean of either potential outcome ranges from \(1/3\) to \(2/3\).

Compatible populations therefore attain ATEs \(1/3\) and \(-1/3\) under the same release.

The sharp ATE interval is \([-1/3,1/3]\), with width \(2/3\), even with unlimited data.

Giving the two scores separate labels eliminates this ambiguity.

---

## Model

Let \(Y_0,Y_1\in[0,1]\) be control and treatment potential outcomes. For population law \(P\), the target is \(\theta(P)=\mathbb E_P[Y_1-Y_0]\).

**Randomization:** conditional on the score, assignment does not select on potential outcomes.

\[
P(A=1\mid E,Y_0,Y_1)=E
\quad\text{almost surely}.
\]

**Consistency:** the observed outcome comes from the assigned arm.

\[
Y=AY_1+(1-A)Y_0
\quad\text{almost surely}.
\]

**Release:** the known measurable rule assigns each score a finite label.

\[
R=g(E)
\quad\text{almost surely}.
\]

**Fixed overlap:** \(E\in[\varepsilon,1-\varepsilon]\), with \(0<\varepsilon<1/2\), bounds both reciprocal weights. The example uses \(\varepsilon=1/4\).

The score law \(H\) is known for identification and label design.

---

## The weighting bridge

For arm \(a\in\{0,1\}\) and label \(r\), define:

\[
p_1(e)=e,\qquad p_0(e)=1-e,\qquad
C_r=\{e:g(e)=r\},\qquad
q_{ar}=\int_{C_r}p_a(e)\,H(de).
\]

Here \(p_a(e)\) is the arm’s assignment probability, \(C_r\) is the label’s score set, and \(q_{ar}\) is the arm–label probability.

Randomization and consistency give
\(\mathbb E_P[Y_a]=\mathbb E_P[\mathbf 1\{A=a\}Y/p_a(E)]=\sum_r q_{ar}\mathbb E_P[Y/p_a(E)\mid A=a,R=r]\).

The release supplies the cell outcome law \(F_{ar}\). Known \(H\) supplies the assignment-weighted score law and reciprocal weight:

\[
G_{ar}(de)=\frac{\mathbf 1\{e\in C_r\}p_a(e)\,H(de)}{q_{ar}},
\qquad E_{ar}\sim G_{ar},
\qquad W_{ar}=\frac{1}{p_a(E_{ar})}.
\]

The missing object is an outcome–weight product expectation with both marginal distributions known.

---

## Why sorting is extremal

Consider two outcome values \(y_2\ge y_1\) and two reciprocal weights \(w_2\ge w_1\).

Matching larger outcomes with larger weights, rather than crossing the pairs, changes their product sum by
\((y_1w_1+y_2w_2)-(y_1w_2+y_2w_1)=(y_2-y_1)(w_2-w_1)\ge0\).

- To maximize the weighted mean, swap any crossed pairs into matching order.
- To minimize it, swap matching pairs into opposite order.
- Repeating these swaps sorts the pairings. Quantile integrals express the same argument for distributions, including distributions with atoms.

In the example, the upper mean pairs ones with the larger reciprocal weights; the lower mean pairs ones with the smaller weights.

---

## Sharp identified interval

Let \(Q_F(u)\) denote distribution \(F\)’s value at percentile \(u\).

Opposite ranks give the lower arm mean; matching ranks give the upper arm mean:

\[
\underline\mu_a
=\sum_{r:q_{ar}>0}q_{ar}\int_0^1
Q_{F_{ar}}(u)Q_{W_{ar}}(1-u)\,du,
\qquad
\overline\mu_a
=\sum_{r:q_{ar}>0}q_{ar}\int_0^1
Q_{F_{ar}}(u)Q_{W_{ar}}(u)\,du.
\]

Each integral is a cell’s weighted outcome mean. Multiplying by \(q_{ar}\) and summing implements the population weighting identity.

For a compatible released law \(P_{\mathrm{rel}}\), the exact attainable ATE range is:

\[
I(P_{\mathrm{rel}};H,g)
=
[\underline\mu_1-\overline\mu_0,\,
 \overline\mu_1-\underline\mu_0].
\]

The arm endpoints can coexist: choose the conditional distributions of \(Y_1\) and \(Y_0\) given each score separately, join them independently, and then randomize treatment with probability \(E\).

This reproduces both observed arm distributions. In the example, means \(2/3\) and \(1/3\) coexist; reversing their pairings gives the other ATE endpoint.

---

## Why half zeros and ones

A cell’s contribution to the arm-mean range is
\(q_{ar}\int_0^1 Q_{F_{ar}}(u)[Q_{W_{ar}}(u)-Q_{W_{ar}}(1-u)]\,du\).

- Below the halfway rank, the bracket is nonpositive.
- Above halfway, it is nonnegative.
- Outcomes in \([0,1]\) maximize this gap by taking zero below halfway and one above.

This is a valid outcome distribution: half zeros and half ones, exactly as in the example.

The resulting upper-half minus lower-half weight integral equals absolute deviation from a median. The maximal cell contribution is
\(q_{ar}\inf_c\mathbb E|W_{ar}-c|=\inf_c\int_{C_r}|1-cp_a(e)|\,H(de)\).

The assignment factor \(p_a(e)\) cancels the reciprocal weight. This turns uncertainty about outcomes into a criterion involving only scores and labels.

---

## Exact release uncertainty

For fixed \(H\) and \(g\), \(D_H(g)\) is the largest sharp ATE width across compatible outcome laws:

\[
D_H(g)=
\sum_{r\in\mathcal R_J}
\left[
\inf_{c\in[1/(1-\varepsilon),\,1/\varepsilon]}
\int_{C_r}|1-ce|\,H(de)
+
\inf_{c\in[1/(1-\varepsilon),\,1/\varepsilon]}
\int_{C_r}|1-c(1-e)|\,H(de)
\right].
\]

The sum runs over the \(J\) labels in \(\mathcal R_J\). Each arm chooses its own constant reciprocal weight \(c\); the remaining absolute error measures information lost within that label.

The half-zero, half-one outcome law attains this width, including for atomic score laws and disconnected score sets.

@informal thm:universal-point-identification: Under fixed overlap, any score law \(H\), and a measurable finite-label rule \(g\), every compatible release identifies the ATE exactly if and only if the label determines the score \(H\)-almost surely.

Equivalently, \(D_H(g)=0\) iff \(E=h(R)\) almost surely for a recovery map \(h\). Separate labels for the example’s two scores make every term vanish.

---

## Label design

Let \(\Delta_K(H)\) be the smallest \(D_H(g)\) achievable with at most \(K\) labels. Write \(\ell=1-2\varepsilon\) for the score interval’s length.

A density floor \(f(e)\ge m_f>0\) puts baseline score mass in every subinterval. Under this condition:

\[
\frac{m_f\ell^2}{2(1-\varepsilon)K}\leq\Delta_K(H).
\]

For every score law, equal-width labels \(g\) satisfy:

\[
\Delta_K(H)\leq\frac{\ell}{2\varepsilon(1-\varepsilon)K},
\qquad
D_H(g)\leq\frac{\ell}{2\varepsilon(1-\varepsilon)K}.
\]

These bounds establish order \(K^{-1}\).

Each absolute-deviation term is distance from a score representative:
\(|1-ce|=c|e-1/c|\), with control representative \(1-1/c\).

Even assigning every score to its nearest of \(K\) representatives leaves integrated distance at least \(\ell^2/(4K)\). The density floor and two arms give the lower bound; equal-width cells control distance to label midpoints.

Can disconnected cells improve the exact leading constant?

---

## Arbitrary cells cannot improve

Assume now that \(f\) is continuous and strictly positive. Each label has a treatment and a control score representative.

The lower-bound argument allows arbitrary measurable cells:

- **Localization:** at the \(K^{-1}\) cost scale, the score length far from either representative vanishes. Positivity makes distant scores costly.
- **Local weights:** on the retained pieces, continuity makes the two distance coefficients nearly constant. Their sum approaches \(w(e)=f(e)/[e(1-e)]\).
- **Shape bound:** for any measurable score set \(B\) of length \(|B|\) and any representative \(z\), \(\int_B|e-z|\,de\ge |B|^2/4\). The closest points to \(z\) minimize this integral; disconnected pieces cannot lower it.
- **Shared budget:** both arms use the same cells. Summing their local squared-length costs and applying Cauchy–Schwarz with at most \(K\) cells gives the square of total weighted length, divided by \(4K\).

Letting the localization neighborhoods shrink makes that weighted length approach \(\int_{\varepsilon}^{1-\varepsilon}\sqrt{w(e)}\,de\).

Thus every measurable design obeys the same leading lower bound that short interval cells can attain.

---

## Optimal label allocation

For a short interval of width \(h\) near score \(e\), the leading ambiguity cost is \(f(e)h^2/[4e(1-e)]\).

More labels reduce local widths. Cauchy–Schwarz allocates labels per unit score length in proportion to \(\sqrt{f(e)/[e(1-e)]}\).

@informal thm:sharp-high-resolution-constant: Under fixed overlap and a continuous, strictly positive score density \(f\), interval labels attain the exact limiting value of \(K\Delta_K(H)\), although optimization allows every measurable label rule.

\[
\lim_{K\to\infty}K\Delta_K(H)
=
\lim_{K\to\infty}K D_H(g_K)
=
\frac14\left(
\int_{\varepsilon}^{1-\varepsilon}
\sqrt{\frac{f(e)}{e(1-e)}}\,de
\right)^2.
\]

Here \(g_K\) is the attaining interval-label design. The formula gives the leading ambiguity per label budget.

Place boundaries at equal increments of cumulative weight
\(\int_{\varepsilon}^{e}\sqrt{f(t)/[t(1-t)]}\,dt\).

Regions with more score mass or larger reciprocal-assignment factors receive narrower cells.

---

## Honest interval length

Observe \(n\) independent, identically distributed released trial rows, with \(H\) known.

An interval is **uniformly honest** if it covers the ATE with probability at least \(1-\alpha\) under every causal law satisfying our model: Imbens and Manski (2004).

Let \(\mathcal L^\star_{n,K,\alpha}(H)\) be the smallest worst-case expected length, jointly choosing labels and an honest interval.

@informal thm:minimax-honest-length: With known \(H\), independent trial rows, fixed overlap, score density \(f\ge m_f>0\), and \(0<\alpha<1/2\), optimal worst-case expected honest interval length has order \(K^{-1}+n^{-1/2}\).

\[
c_{\varepsilon,m_f,\alpha}\bigl(K^{-1}+n^{-1/2}\bigr)
\leq \mathcal L^\star_{n,K,\alpha}(H)
\leq C_{\varepsilon,\alpha}\bigl(K^{-1}+n^{-1/2}\bigr).
\]

The positive constants depend only on their subscripts, not on \(H,n,K\).

Observationally identical endpoint populations force retained ambiguity; trial sampling adds uncertainty. A label budget of order \(\sqrt n\) balances the two.

---

## Midpoint weighting

Use equal-width labels. Replace the missing score by its label midpoint
\(z_r=\varepsilon+\frac{(r-\tfrac12)(1-2\varepsilon)}{K}\).

\[
\widehat T_n=\frac1n\sum_{i=1}^n
\left\{\frac{A_iY_i}{z_{R_i}}-\frac{(1-A_i)Y_i}{1-z_{R_i}}\right\},
\qquad
R_{n,K}=\frac4\varepsilon\sqrt{\frac{\log(4/\alpha)}{n}}
+\frac{1-2\varepsilon}{2K\varepsilon(1-\varepsilon)}.
\]

The estimator \(\widehat T_n\) averages midpoint-weighted outcomes. The radius \(R_{n,K}\) pays separately for sampling variation and score substitution.

For observed data \(x\), use:

\[
C_n(x)=
\left[
\operatorname{clampATE}\bigl(\widehat T_n(x)-R_{n,K}\bigr),
\operatorname{clampATE}\bigl(\widehat T_n(x)+R_{n,K}\bigr)
\right]
\]

The function \(\operatorname{clampATE}\) keeps endpoints in \([-1,1]\).

Accounting for midpoint substitution makes this interval uniformly honest and attains the upper length order.

---

## Independent score log

Fix a measurable release \(g\) with \(J\) labels. Observe \(n\) independent trial rows and an independent sample of \(m\) scores from \(H\).

Call \(\operatorname{len}I(P_{\mathrm{rel}};H,g)\) the **population sharp width**. Let \(\mathcal R^\star_{n,m,\alpha}(g)\) minimize worst-case expected positive excess length beyond that width among uniformly honest intervals.

Under our model and \(0<\alpha<1/2\):

\[
c_{\mathrm{tr}}(\alpha)n^{-1/2}
\le \mathcal R^\star_{n,m,\alpha}(g)
\le C_{\varepsilon,J,\alpha,g}
\bigl(n^{-1/2}+m^{-1/2}\bigr).
\]

Trial uncertainty gives the lower bound at every sample size. Score-log uncertainty also remains unavoidable:

\[
\liminf_{m\to\infty}\inf_{n\ge1}
\sqrt m\,\mathcal R^\star_{n,m,\alpha}(g)
\ge c_{\mathrm{log}}(g,\alpha)>0.
\]

The constants depend only on the indicated fixed quantities, not on \(H,n,m\).

@informal thm:external-score-root-order: For fixed measurable finite-label \(g\), fixed overlap, \(0<\alpha<1/2\), and independent iid trial and score-log samples, minimax excess length has order \(n^{-1/2}+m^{-1/2}\) when \(n/m\to\rho\in(0,\infty)\).

---

## Projection construction

Estimate each cell’s outcome measure and assignment-weighted score measure:

\[
\widehat\lambda_{ar}(B)
=\frac1n\sum_{i=1}^{n}\mathbf 1\{R_i=r,A_i=a,Y_i\in B\},
\qquad
\widehat\sigma_{ar}(B)
=\frac1m\sum_{j=1}^{m}p_a(E_j^{\mathrm{log}})
\mathbf 1\{g(E_j^{\mathrm{log}})=r,E_j^{\mathrm{log}}\in B\}.
\]

For a set \(B\), \(\widehat\lambda_{ar}\) counts outcomes; \(\widehat\sigma_{ar}\) weights logged scores. Both retain cell mass.

Define closeness by **total-mass difference plus integrated cumulative distribution function distance**: integrate the absolute gap between the measures’ cumulative distribution functions. This controls cell frequencies and movement of values.

Keep candidate arrays with matching outcome–score masses within empirical radii
\(r_n=\frac{4J}{\alpha\sqrt n}\) and \(r_m=\frac{2J(2-2\varepsilon)}{\alpha\sqrt m}\). Call this set \(\mathcal B_{n,m}\).

Compute each candidate’s rank-pairing interval \(I(b)\), then form:

\[
J_{n,m}
=
[-1,1]\cap
\operatorname{cl}\operatorname{conv}
\left(\bigcup_{b\in\mathcal B_{n,m}}I(b)\right).
\]

This is the smallest closed interval containing all candidate intervals, within \([-1,1]\). On the coverage event, it contains the population sharp interval.

Overlap bounds weight changes. Integrated distribution-function distance controls quantile movement; retaining masses avoids division by small cell probabilities. Consequently, projection adds only order \(n^{-1/2}+m^{-1/2}\) expected excess length, including with atoms and flat quantiles.

---

## Takeaways

- Rank pairings recover the exact ATE range. \(D_H(g)=0\) iff \(E=h(R)\) almost surely: the example’s separate-score labels eliminate ambiguity because they recover each score.
- Half-zero, half-one outcomes attain worst-case ambiguity. Optimal ambiguity has order \(K^{-1}\) under a density floor; continuous positive densities give an exact constant and square-root label allocation.
- Honest inference accounts for both missing links and sampling: known-score length has order \(K^{-1}+n^{-1/2}\); an independent score log gives excess length of order \(n^{-1/2}+m^{-1/2}\) at a fixed positive sample-size ratio.

---

## Appendix: Exact release uncertainty

The score-only formula is the attained maximum sharp ATE width for any finite-label release.

@formal thm:all-label-ambiguity

---

## Appendix: Optimal label allocation

A continuous, strictly positive score density yields an exact leading ambiguity constant attained by interval labels.

@formal thm:sharp-high-resolution-constant

---

## Appendix: Honest interval length

Equal-width labels and midpoint weighting attain the minimax honest-length order under a positive density floor.

@formal thm:minimax-honest-length

---

## Appendix: Independent score log

Projection attains the two-source excess-length upper order, with separate trial and score-log lower bounds.

@formal thm:external-score-root-order
