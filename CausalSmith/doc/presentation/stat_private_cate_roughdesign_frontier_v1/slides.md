# Private Treatment Effects With Rough Nuisance Functions

Nearby pairs of confidential records can reveal a smooth treatment effect even when treatment selection and baseline outcomes vary roughly.

---
## Research question

We observe \(n\) confidential records \((X,A,Y)\): a covariate, binary treatment, and binary outcome.

We want the causal effect at \(X=1/2\), together with a uniformly valid 90% confidence interval.

- Usual methods fit treatment probabilities and outcome regressions. Their remaining bias includes products of nuisance estimation errors.
- A smooth treatment effect does not make those nuisance functions easy to estimate.
- Kennedy et al. (2024), our closest comparison, attain \(n^{-1/4}\) with additional approximation, eigenvalue, boundedness, and covariate-distribution estimation conditions; our attainment uses observed occupancies under only the stated density bounds.

**Pure replacement privacy:** replacing one record can multiply the probability of any release event by at most \(\exp(\epsilon)\). Smaller \(\epsilon\) means stronger protection.

What accuracy remains possible when the nuisances are rough and the covariate density is unknown and merely measurable?

---
## Key idea

Use two resolutions:

- A neighborhood where the treatment effect barely changes.
- Much smaller cells where treatment selection and baseline variation leave only a small product.

Compare records within cells. Give the numerator and denominator identical count weights, then release both together.

For our binary, scalar-covariate model with bounded density and overlap, one-tenth nuisance smoothness, and a Lipschitz effect, optimal estimation error and honest interval length have order

\[
r(n,\epsilon)=
\min\left\{1,\,
\max\left\{
n^{-1/4},\,
(n^2\epsilon)^{-1/7},\,
(n\epsilon)^{-1/2}
\right\}\right\}.
\]

Here \(r(n,\epsilon)\) is the accuracy benchmark, \(n\ge2\), and \(0<\epsilon\le1\). The largest of three scales governs accuracy, capped at one.

---
## Model, identification, and scope

Let \(P\) describe a causal population with binary potential outcomes \(Y(0),Y(1)\). The observed records \((X,A,Y)\) are iid, satisfy consistency \(Y=Y(A)\), and satisfy conditional exchangeability given \(X\).

With overlap, the observed contrast identifies the causal effect:

\[
\tau_P(x)
=
E_P[Y\mid X=x,A=1]
-
E_P[Y\mid X=x,A=0],
\qquad x\in[0,1].
\]

The target is \(\theta(P)=\tau_P(1/2)\). Continuity and positive design density make this point value unique.

Write \(e_P(x)=P(A=1\mid X=x)\) and \(\mu_{a,P}(x)=E_P[Y\mid X=x,A=a]\).

The class \(\mathcal P\) imposes:

- measurable density \(1/2\le f_P\le3/2\) almost everywhere;
- overlap \(1/4\le e_P\le3/4\);
- \(|e_P(x)-e_P(x')|\le3|x-x'|^{1/10}\) and \(|\mu_{0,P}(x)-\mu_{0,P}(x')|\le3|x-x'|^{1/10}\);
- \(|\tau_P(x)-\tau_P(x')|\le3|x-x'|\).

These radii bound increments. Binary outcomes separately give \(0\le\mu_{a,P}\le1\); the class has no fixed interior arm-mean margin.
---
## Main result

Let \(R_{n,\epsilon}\) be the smallest worst-case expected absolute error among private estimators.

@informal thm:matched-risk-frontier: For \(n\ge2\), \(0<\epsilon\le1\), and \(\mathcal P\), optimal private worst-case expected absolute error is bounded above and below by numerical multiples of \(r(n,\epsilon)\).

\[
2^{-20}r(n,\epsilon)
\le R_{n,\epsilon}
\le 2^{18}r(n,\epsilon).
\]

An interval is **honest** if coverage is at least 90% for every \(P\in\mathcal P\) at the given sample size. Let \(H_{n,\epsilon}\) be the smallest worst-case expected length among private connected honest intervals.

@informal thm:sharp-interval-frontier: For \(n\ge2\), \(0<\epsilon\le1\), and \(\mathcal P\), optimal private honest expected interval length is bounded above and below by numerical multiples of \(r(n,\epsilon)\).

\[
2^{-20}r(n,\epsilon)
\le H_{n,\epsilon}
\le
\sup_{P\in\mathcal P}
E_{(P^{\mathrm{obs}})^{\otimes n},I^*_{n,\epsilon}}
\operatorname{Leb}\!\left(I^*_{n,\epsilon}(D)\right)
\le2^{22}r(n,\epsilon).
\]

Here \(D\) is the dataset, \(P^{\mathrm{obs}}\) its observed-record law, \(I^*_{n,\epsilon}\) our interval, and \(\operatorname{Leb}\) its length. Expectations include sampling and release noise.

Our pair release attains both upper bounds across every admissible density.

---
## Within-cell pairs

Choose a public window \([x_0-h,x_0+h]\) centered at \(x_0=1/2\), with \(0<h\le1/4\), and divide it into \(k\ge2\) cells of width \(\delta=2h/k\).

For two records, use numerator and denominator contributions

\[
\begin{aligned}
K_N\bigl((X,A,Y),(X',A',Y')\bigr)
  &=(A-A')(Y-Y'),\\
K_D\bigl((X,A,Y),(X',A',Y')\bigr)
  &=(A-A')^2.
\end{aligned}
\]

For either kernel \(\kappa\), a cell’s records \(\mathscr R=(o_1,\ldots,o_s)\) contribute

\[
F_\kappa(\mathscr R)=
\begin{cases}
0,&s<2,\\[2pt]
\displaystyle\frac{s}{\binom{s}{2}}
\sum_{1\le i<i'\le s}\kappa(o_i,o_{i'}),&s\ge2.
\end{cases}
\]

Both statistics use this same rule: \(S_N(D)=\sum_jF_{K_N}(\mathscr R_j)\) and \(S_D(D)=\sum_jF_{K_D}(\mathscr R_j)\), where \(\mathscr R_j\) contains cell \(j\)’s records.

For example, a two-record cell with \((A,Y)=(1,1),(0,0)\) contributes \((F_{K_N},F_{K_D})=(2,2)\). A second two-record cell with \((A,Y)=(1,0),(0,1)\) contributes \((-2,2)\). Their identical count weights combine to total numerator \(0\), denominator \(4\), and ratio \(0\).

---
## Product bias and density robustness

Pair differencing reduces baseline contamination within a cell to

\((e_P(x)-e_P(x'))(\mu_{0,P}(x)-\mu_{0,P}(x'))\).

The two rough increments make this product order \(\delta^{1/5}\), while effect variation across the window is order \(h\). For expected numerator and denominator pair contributions \(\nu_j,d_j\), with \(b=3h+24\delta^{1/5}\),

\[
d_j\ge\frac38,
\qquad
\left|\nu_j-\theta(P)d_j\right|\le b\,d_j.
\]

Let \(w_j\) be the expected number of records in cell \(j\) that have a partner. Then

\[
\overline N=\sum_{j=1}^k w_j\nu_j,
\qquad
\overline D=\sum_{j=1}^k w_jd_j.
\]

The ratio is a nonnegative weighted average of controlled cell ratios, so \(|\overline N/\overline D-\theta(P)|\le b\). Unknown density changes the common weights without changing this guarantee.

The usable-information scale is \(\mathcal A=nh\min\{1,n\delta\}\): local sample size times partner availability.
---
## One private release

Count weighting bounds the total absolute change in both statistics by 12 when one record is replaced—even when cell counts cross zero, one, or two.

Using sensitivity-calibrated Laplace noise from Dwork et al. (2006), release

\[
\widetilde S=
\bigl(S_N(D)+\xi_N,\ S_D(D)+\xi_D\bigr),
\qquad
\xi_N,\xi_D\overset{\mathrm{ind}}{\sim}
\operatorname{Laplace}(0,12/\epsilon).
\]

The noises \(\xi_N,\xi_D\) are independent, each with scale \(12/\epsilon\). Write \(\widetilde S_N,\widetilde S_D\) for the released coordinates.

With public floor \(d_0=3\mathcal A/64\), estimate

\[
\widehat T_{h,k}
=
\operatorname{clip}_{[-1,1]}
\left\{
\frac{\widetilde S_N}
{\max\{d_0,\widetilde S_D\}}
\right\},
\]

The floor prevents unstable division. Clipping moves values outside the target range to the nearest endpoint.

The ratio and any interval computed from this release inherit its pure replacement privacy.

---
## Error budget and public tuning

@informal thm:uniform-private-upper: For \(P\in\mathcal P\), \(n\ge2\), \(k\ge2\), \(0<h\le1/4\), and \(0<\epsilon\le1\), the private ratio's mean squared error is at most \(V(h,\delta)\), with \(\delta=2h/k\).

\[
\mathcal A=nh\min\{1,n\delta\},
\qquad
V(h,\delta)
=
2^{20}\left[
h^2+\delta^{2/5}+\mathcal A^{-1}
+(\epsilon\mathcal A)^{-2}
\right].
\]

The terms are localization, nuisance-product bias, sampling variation, and privacy noise. On the local branch choose \(h\) within a factor of two of \(r(n,\epsilon)\) and \(\delta=h^5\).

| Occupancy regime and error source | Accuracy scale |
|---|---|
| Sparse \(n\delta<1\): sampling | \(n^{-1/4}\) |
| Sparse \(n\delta<1\): privacy | \((n^2\epsilon)^{-1/7}\) |
| Dense \(n\delta\ge1\): privacy | \((n\epsilon)^{-1/2}\) |

With \(\delta=h^5\), sparse occupancy gives \(\mathcal A=n^2h^6\): sampling requires \(n^2h^8\gtrsim1\), and privacy requires \(\epsilon n^2h^7\gtrsim1\). Dense privacy requires \(\epsilon nh^2\gtrsim1\). Dense sampling is already controlled, so it adds no fourth term.

The local branch is \(r(n,\epsilon)<1/8\). When \(r(n,\epsilon)\ge1/8\), the public fallback outputs \(\widehat T^*=0\) and \(\widehat I^*=[-1,1]\); the bounded target range supplies constant-order error and length in this capped regime.
---
## Honest interval construction

On the local branch, use the same estimate and public envelope:

\[
\widehat I^*(D)
=
[-1,1]\cap
\left[
\widehat T_{h,k}(D)-\sqrt{10V(h,\delta)},
\widehat T_{h,k}(D)+\sqrt{10V(h,\delta)}
\right].
\]

This centers our interval at the private estimate, with radius \(\sqrt{10V(h,\delta)}\).

- The squared-error bound makes the probability of exceeding this radius at most \(1/10\).
- The target belongs to \([-1,1]\), so intersection preserves coverage.
- Both endpoints reuse the same private release.

Coverage holds at every sample size. Constants are conservative: for \(2\le n\le2^{40}\), this tuned interval is exactly \([-1,1]\).

The optimal-order claim comes from matching lower bounds. Why must every private procedure face the same three scales?

---
## Shared signs

For the hard alternatives, use a localized effect bump \(tq(x)\), supported on \(|x-x_0|\le h_{\mathrm L}\), with \(0\le q\le1\) and \(q(x_0)=1\).

\[
\delta_{\mathrm L}=h_{\mathrm L}^{5},
\qquad
t=2^{-12}h_{\mathrm L}.
\]

Choose a shared-sign perturbation \(S_\lambda\) satisfying the two identities used by the lower bound:

Within cell \(j\), define \(\omega_{\mathrm L}(x)=\pi(x-j\delta_{\mathrm L})/(2\delta_{\mathrm L})\) and \(g^2=q\). The two local weights are \(\cos\omega_{\mathrm L}\) and \(\sin\omega_{\mathrm L}\), and

\(S_\lambda(x)=g(x)[(2\lambda_j-1)\cos\omega_{\mathrm L}(x)+(2\lambda_{j+1}-1)\sin\omega_{\mathrm L}(x)].\)

Independent fair signs and \(\cos^2+\sin^2=1\) give

\(E_\lambda S_\lambda(x)=0,\qquad E_\lambda S_\lambda(x)^2=q(x).\)

The first identity cancels linear nuisance terms; the second cancels the effect against the squared perturbation. Sign \(\lambda_{j+1}\) is reused in the neighboring cell.

@figure adjacent-sign-cells: Sign \(2\lambda_j-1\) feeds the cosine weight in cell \(j\); sign \(2\lambda_{j+1}-1\) feeds the sine weight in cell \(j\) and the cosine weight in cell \(j+1\); sign \(2\lambda_{j+2}-1\) feeds the sine weight in cell \(j+1\).

---
## One-record cancellation

For each fixed sign vector, draw \(X\) uniformly and generate treatment and potential outcomes independently conditional on \(X\).

Selection probability is \((1+\sqrt t\,S_\lambda(x))/2\). Control and treated means are \((1-\sqrt t\,S_\lambda(x)-tq(x))/2\) and \((1-\sqrt t\,S_\lambda(x)+tq(x))/2\).

Thus nuisance shifts have amplitude \(\sqrt t\), while every alternative has effect \(tq(x)\) and target \(t\). Calibration keeps every alternative in \(\mathcal P\).

The fair null \(P_0\) has uniform \(X\), treatment probability \(1/2\), both conditional outcome means \(1/2\), and zero treatment effect.

Let \(U=2A-1\) and \(V_Y=2Y-1\) encode treatment and outcome. Relative to the fair null \(P_0\), the conditional likelihood is

\[
\begin{aligned}
L_\lambda(x,U,V_Y)
={}&1+U\sqrt t\,S_\lambda(x)
 +V_Y\sqrt t\,\bigl(tq(x)-1\bigr)S_\lambda(x)\\
&+UV_Yt\bigl(q(x)-S_\lambda(x)^2\bigr).
\end{aligned}
\]

This is four times the conditional probability of the observed treatment–outcome pair.

Sign averaging removes the linear terms and the centered squared term. Consequently,

\[
E_\lambda P_\lambda^{\mathrm{obs}}=P_0^{\mathrm{obs}}.
\]

A single record hides the positive effect exactly. Shared signs can still reveal it across records.

---
## Full-sample information

Draw one sign vector for the entire dataset:

\[
Q_n=E_\lambda\!\left[(P_\lambda^{\mathrm{obs}})^{\otimes n}\right],
\]

Here \(Q_n\) averages alternative dataset laws. Sampling is independent within each population; averaging a common sign vector creates dependence.

Records using disjoint signs cancel separately. Nearby records sharing signs can reveal the nuisance pattern.

Our likelihood comparison gives

\[
\chi^2\!\left(Q_n,(P_0^{\mathrm{obs}})^{\otimes n}\right)
\le
\exp\!\left(160n^2t^2h_{\mathrm L}\delta_{\mathrm L}\right)-1,
\qquad
Q_n\ll(P_0^{\mathrm{obs}})^{\otimes n},
\]

Chi-square divergence measures squared likelihood deviation. The final condition means the alternative assigns no mass to null-impossible events.

The exponent combines record-pair opportunities, shared-sign localization, and squared signal size. Calibration makes it proportional to \(n^2h_{\mathrm L}^8\).

Taking \(h_{\mathrm L}=n^{-1/4}/4\) keeps total variation—the largest difference in event probabilities—at most \(1/4\), even before privacy.

---
## Component cancellation and matching

Link records that use a common nuisance sign. Conditional on covariates, different components use independent sign sets, and singleton components match the null exactly.

For a component \(C\) of size \(m\), fair-sign averaging cancels the first-order change. Its alternative and null configuration masses differ only at second order, yielding mismatch probability at most \(4tm^2\).

Let \(\alpha\) be the total common configuration mass matched by the component coupling. Write \(c_{\mathrm H,C}(x)\) for the expected number of replaced records in component \(C\), conditional on its full covariate configuration \(x\). A residual mismatch has mass \(1-\alpha\) and changes at most \(m\) records, so

\[
c_{\mathrm H,C}(x)
\le m(1-\alpha)
\le4tm^3.
\]

Thus isolated records cost nothing, and shared-sign components incur replacement cost proportional to \(t\), rather than \(\sqrt t\).
---
## Sparse replacement cost

A linked pair must lie inside the bump window and within \(2\delta_{\mathrm L}\) of each other.

This gives the factors behind the aggregate cost:

- \(n^2\): opportunities for a record pair.
- \(h_{\mathrm L}\delta_{\mathrm L}\): probability of a localized shared-sign pair.
- \(t\): mismatch probability after first-order sign cancellation.

Larger components add nearby records. Under \(n\delta_{\mathrm L}\le1/128\), their summed contribution remains bounded. Keller and Trotter (2017) supply the labeled-tree count used in this component bound.

Our constructed dataset coupling \(\gamma\) satisfies

\[
\int d_{\mathrm H}(D,D')\,\gamma(dD,dD')
\le1024tn^2h_{\mathrm L}\delta_{\mathrm L}.
\]

Here \(d_{\mathrm H}\) counts replaced record positions.

The coupling principle of Acharya et al. (2021) converts expected replacement cost into private output distance:

\[
d_{\mathrm{TV}}(MQ,MQ')
\le 2\epsilon W_{\mathrm H}(Q,Q').
\]

Here \(MQ\) is the release law under dataset law \(Q\), and \(W_{\mathrm H}\) is minimum expected replacement cost.

Applied to our coupling, output distance is at most \(2048\epsilon tn^2h_{\mathrm L}\delta_{\mathrm L}\). Calibration makes this proportional to \(\epsilon n^2h_{\mathrm L}^7\), producing the seventh-root scale.

---
## Direct privacy comparison

For the remaining privacy regimes, use the same localized bump with constant selection and baseline means.

Couple null and alternative records using the same covariate. Match their treatment–outcome pairs except for mass moved from treated outcome zero to treated outcome one:

\[
\omega_{\mathrm{cross}}(x):=\frac{tq(x)}2,
\qquad
0\le\omega_{\mathrm{cross}}(x)\le\frac14.
\]

The crossing probability \(\omega_{\mathrm{cross}}(x)\) is exactly the changed treated-outcome mass.

Because \(q\le1\) and its support has width \(2h_{\mathrm L}\), expected replacements across \(n\) records are at most \(nth_{\mathrm L}\).

The same privacy coupling principle bounds output distance by \(2\epsilon nth_{\mathrm L}\), proportional to \(n\epsilon h_{\mathrm L}^2\).

A radius of order \((n\epsilon)^{-1/2}\) keeps private outputs close. When \(n\epsilon\le1\), a fixed-radius bump already does so, forcing constant-order error.

---
## Forced error and length

Choose the applicable signed or direct comparison at radius \(h_{\mathrm L}=r(n,\epsilon)/4\).

- The \(n^{-1/4}\) term uses the signed full-sample likelihood comparison.
- The \((n^2\epsilon)^{-1/7}\) term uses the signed private coupling; this regime satisfies its required sparse-cell condition \(n\delta_{\mathrm L}\le1/128\).
- The \((n\epsilon)^{-1/2}\) term and the capped regime use the direct bump comparison.

Its null target is zero; every alternative target is \(\Delta=2^{-14}r(n,\epsilon)\). For every private release \(M\),

\[
d_{\mathrm{TV}}\!\left(MQ^{(0)},MQ^{(1)}\right)\le\frac14,
\]

Here \(Q^{(0)}\) and \(Q^{(1)}\) are the null and alternative dataset laws.

- **Estimation:** an accurate estimate would distinguish the targets by comparison with \(\Delta/2\). Close output laws prevent uniformly reliable distinction, forcing error proportional to \(\Delta\).
- **Honesty:** containing \(\Delta\) with probability \(9/10\) under the alternative implies containment with probability at least \(9/10-1/4\) under the null.
- **Length:** under the null, coverage of zero and transferred coverage of \(\Delta\) imply simultaneous containment with probability at least \(11/20\).

A connected interval containing both targets has length at least \(\Delta\). Expected length is therefore at least \((11/20)\Delta\).

The same separated populations force both lower bounds.

---
## Takeaways

- Fine-cell pairs replace nuisance-fitting error with a controlled product of local increments; shared occupancy weights preserve it under unknown measurable density.
- Shared signs hide a positive effect from isolated records. Likelihood and replacement comparisons produce the three unavoidable scales.
- One private release attains optimal estimation error and honest interval length of order \(r(n,\epsilon)\); both vanish exactly when \(n\epsilon_n\to\infty\).
- Next steps include sharper constants, finite-sample evaluation, represented-real implementations, and broader outcome or covariate classes.
---
## Appendix: Matched private risk frontier

This theorem gives matching finite-sample bounds for optimal private absolute error and shows that the publicly tuned pair ratio attains the upper bound.

@formal thm:matched-risk-frontier

---
## Appendix: Sharp honest interval frontier

This theorem gives uniform finite-sample 90% coverage and matching bounds for optimal expected length of private connected intervals.

@formal thm:sharp-interval-frontier

---
## Appendix: Verification and implementation scope

The main formal results are conditional on three registered published premises:

- **EfronSteinReplacement** — Boucheron, Lugosi, and Massart (2013), Theorem 3.1, replacement-copy form, p. 54.
- **BoundedDifferencesMGF** — Boucheron, Lugosi, and Massart (2013), Theorem 6.2, displayed log-mgf conclusion in its proof, p. 167.
- **CayleyLabeledTreeCount** — Keller and Trotter (2017), Section 5.6, Theorem 5.40.

Their source proofs are premises; the downstream mapped derivations are the formalized scope.

The estimator and interval are exact-real randomized constructions. Their mathematical privacy, risk, and coverage conclusions are not a finite-precision software guarantee; arithmetic, noise generation, and endpoint handling require separate implementation analysis.

---
## Appendix: Shared-sign construction

The bump and its squared-cosine envelope are

\[
q(x)=
\begin{cases}
\displaystyle
\cos^{4}\!\left(\frac{\pi(x-x_0)}{2h_{\mathrm L}}\right),
& |x-x_0|\le h_{\mathrm L},\\
0,& |x-x_0|>h_{\mathrm L},
\end{cases}
\]

with \(g(x)^2=q(x)\).

Within cell \(j\), put \(\omega_{\mathrm L}(x)=\pi(x-j\delta_{\mathrm L})/(2\delta_{\mathrm L})\). Then

\(S_\lambda(x)=g(x)\left[(2\lambda_j-1)\cos\omega_{\mathrm L}(x)+(2\lambda_{j+1}-1)\sin\omega_{\mathrm L}(x)\right].\)

Independent fair signs and \(\cos^2+\sin^2=1\) give \(E_\lambda S_\lambda=0\) and \(E_\lambda S_\lambda^2=q\). The adjacent-cell reuse is shown in the talk figure.
