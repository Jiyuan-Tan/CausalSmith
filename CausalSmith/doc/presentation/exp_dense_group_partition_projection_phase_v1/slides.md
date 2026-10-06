# Variance After Random Group Formation

When groups compete for members of a finite population, standard cluster variance calculations can exceed the variance of the estimated treatment effect.

---

## Motivation

- A population of \(n\) units supplies \(G_n\) disjoint groups, each of fixed size \(M\ge2\).
- Treatment is randomized across groups. Outcomes may depend on who joins each group.
- We want the average treatment effect across possible group compositions—and its variance over repeated grouping and assignment.
- The participating population has size \(N_n=MG_n\). Drawing one group changes the members available to every other group.

Fu et al. (2026), our closest comparison, establish CR2 ratio consistency under boundedness, their other assumptions, and the sparse condition \(N_n^2/n\to0\).

What happens when competition for members remains relevant?

---

## Standard approach

Compare treated and control group means, then use a cluster-robust variance estimator with the CR2 small-sample adjustment.

Let \(G_{1n}\) and \(G_{0n}\) be the treated and control group counts. Let \(s_{z,n}^2\) be the sample variance of observed group means in arm \(z\), using denominator \(G_{zn}-1\).

\[
\widehat V_{\mathrm{CR2},n}
=
\frac{s_{1,n}^2}{G_{1n}}
+
\frac{s_{0,n}^2}{G_{0n}}.
\]

This adds the estimated variance of each arm mean.

Pustejovsky and Tipton (2018) develop the adjustment under an independent-cluster working covariance model. Disjoint random groups can covary because they cannot reuse members.

When does this calculation still recover the exact design variance?

---

## Key idea

Keep the covariance created by drawing groups without replacement.

Separate treatment-effect variation into **additive member contributions** and remaining composition effects. Only the additive part survives in the leading finite-population correction.

With fixed group size, growing group count, stable treatment shares, convergent participation, and bounded outcomes:

- CR2 estimates the independent-group variance scale.
- The exact variance subtracts participation density times additive treatment-effect heterogeneity.

With a positive scaled-variance floor, CR2 is asymptotically conservative; it is sharp exactly when that correction is relatively negligible.

---

## Example

Eight units form four pairs; two pairs receive treatment. All units participate.

Four units have sign \(a_i=+1\), and four have sign \(a_i=-1\). For pair \(A=\{j,k\}\), both members have potential outcomes

\[
Y_{i,n}(0,A)=0,
\qquad
Y_{i,n}(1,A)=\frac{a_j+a_k}{2}.
\]

The treated pair outcome is its average sign. Selecting a pair with positive signs removes those signs from the remaining pool.

The exact variance of the treated–control difference is \(\sigma_n^2=1/7\), but

\[
\mathbb E\!\left[\widehat V_{\mathrm{CR2},n}\right]=\frac{2}{7}.
\]

Expected CR2 is twice the exact variance. Which feature of the outcome table creates this gap?

---

## Model

Draw the disjoint groups uniformly, then independently choose exactly \(G_{1n}\) groups for treatment.

For arm \(z\in\{0,1\}\), \(Y_{i,n}(z,A)\) is unit \(i\)'s fixed potential outcome in group \(A\). The group table records its average:

\[
h_{z,n}(A)=\frac{1}{M}\sum_{i\in A}Y_{i,n}(z,A).
\]

Our target averages the treatment contrast over every possible size-\(M\) group; \(\mathbb E_n\) denotes that uniform average:

\[
\tau_n=\mathbb E_n\!\left[h_{1,n}-h_{0,n}\right].
\]

For realized group \(A_{ng}\), let \(Z_{ng}=1\) indicate treatment. The estimator is

\[
\widehat\tau_n
=
\frac{1}{G_{1n}}\sum_g Z_{ng}h_{1,n}(A_{ng})
-
\frac{1}{G_{0n}}\sum_g (1-Z_{ng})h_{0,n}(A_{ng}).
\]

It is unbiased for \(\tau_n\). Its exact variance, \(\sigma_n^2\), includes both grouping and treatment randomness.

---

## Assumptions

Consider feasible experiments with fixed group size \(M\ge2\) and deterministic potential outcomes.

- **Group growth:** \(G_n\to\infty\), providing many randomized groups.
- **Stable treatment shares:** \(p_n=G_{1n}/G_n\to p\in(0,1)\), keeping both arms represented.
- **Convergent participation:** \(N_n/n\to\rho\in[0,1]\), recording how much of the population participates.
- **Bounded outcomes:** \(\sup_{n,i,z,A}\left|Y_{i,n}(z,A)\right|\le B<\infty\), ruling out increasingly extreme outcomes.
- **Variance floor:** \(c_\sigma\le\liminf_{n\to\infty}G_n\sigma_n^2\), with \(c_\sigma>0\), preventing the target variance from vanishing too quickly.

The pair-sign example has \(B=1\) and full participation. It illustrates the finite mechanism; the asymptotic results require growing group counts.

---

## Additive heterogeneity

For a group table \(f\), its additive component has the form  
\(\Pi_{n,1}f(A)=\sum_{i\in A}b_i\), with centered member coefficients \(\sum_{i=1}^n b_i=0\).

Each \(b_i\) measures a member's additive contribution to the centered group outcome.

The remaining centered table, \(f-\mathbb E_n f-\Pi_{n,1}f\), is orthogonal to every centered additive sum: their product averages to zero over possible groups. This distinguishes member contributions from residual composition effects.

For the treatment-contrast table, define

\[
E_{\tau,1,n}
=
\left\|\Pi_{n,1}(h_{1,n}-h_{0,n})\right\|_n^2 .
\]

The squared norm means average squared additive contrast over possible groups.

In the pair-sign example, \(b_i=a_i/2\). The contrast is entirely additive, the residual is zero, and \(E_{\tau,1,n}=V_{1,n}=3/7\), where \(V_{1,n}\) is the treated-table variance.

---

## Main result

Let \(V_{z,n}\) be the variance of arm \(z\)'s outcome table over all possible groups. The independent-group variance scale is

\[
R_n
=
\frac{V_{1,n}}{p_n}
+
\frac{V_{0,n}}{1-p_n}.
\]

Under group growth, stable treatment shares, convergent participation, and bounded outcomes,

\[
G_n\sigma_n^2-\bigl(R_n-\rho E_{\tau,1,n}\bigr)\to 0,
\]

The exact variance, scaled by group count, subtracts the participation-weighted additive contrast variation.

With the variance floor as well,

\[
G_n\widehat V_{\mathrm{CR2},n}-R_n \xrightarrow{p}0
\]

CR2 tracks \(R_n\), rather than the corrected scale. Neither scale needs to converge to a constant.

Why does dependence change the exact variance while leaving CR2's target intact?

---

## Exact variance

Let \(C_{ab,n}\) be the covariance between arm-\(a\) and arm-\(b\) outcomes for a uniformly drawn disjoint pair of groups.

Their treatment-contrast covariance is \(C_{\tau\tau,n}=C_{11,n}+C_{00,n}-2C_{10,n}\).

For a feasible design with at least two groups per arm,

\[
\sigma_n^2
=
\frac{R_n}{G_n}
+
C_{\tau\tau,n}
-
\frac{C_{11,n}}{G_{1n}}
-
\frac{C_{00,n}}{G_{0n}},
\]

The within-arm sample variances incorporate the final two terms. Their expected CR2 calculation misses exactly the contrast covariance:

\[
\mathbb E[\widehat V_{\mathrm{CR2},n}]-\sigma_n^2=-C_{\tau\tau,n}.
\]

In the pair-sign example, \(C_{\tau\tau,n}=C_{11,n}=-1/7\). Its negative covariance explains the entire expectation gap of \(1/7\).

---

## Removing members

For a group table \(f\), \(\mathsf K_n f\) averages its value over groups disjoint from an already chosen group \(A\):

\[
(\mathsf K_n f)(A)
=
\binom{n-M}{M}^{-1}
\sum_{C:C\cap A=\varnothing} f(C).
\]

The Johnson decomposition separates the centered table into mutually orthogonal components \(\Pi_{n,k}f\): degree one is additive; higher degrees contain composition variation left after lower degrees are removed. We use the decomposition of Filmus (2016).

Disjointness multiplies each component separately:

\[
\mathsf K_n(\Pi_{n,k}f)(A)=\lambda_{n,k}\,\Pi_{n,k}f(A),
\qquad
\lambda_{n,k}=(-1)^k\frac{(M)_k}{(n-M)_k},
\]

Here \(k\) is the degree and \((x)_k\) is a falling factorial.

For degree one, \(\lambda_{n,1}=-M/(n-M)\): an above-average additive group leaves a below-average pool.

---

## Accumulating dependence

Orthogonality turns the treatment-contrast covariance into a sum of separate degree contributions:

\[
C_{\tau\tau,n}
=
\sum_{k=1}^{M}\lambda_{n,k}
\bigl\|\Pi_{n,k}(h_{1,n}-h_{0,n})\bigr\|_n^2 .
\]

Each component contributes its mean square times its disjointness multiplier.

- **Degree one:** multiplying \(-M/(n-M)\) by \(G_n\) leaves the participation correction.
- **Higher degrees:** their multipliers decay faster. Bounded outcomes control total component variation; their combined contribution after scaling by \(G_n\) has absolute value at most \(C/n\), for a constant \(C\).

Thus

\[
G_nC_{\tau\tau,n}+\rho E_{\tau,1,n}\to 0,
\]

The scaled contrast covariance approaches minus the participation-weighted additive energy. The within-arm covariance terms in the scaled exact variance also vanish.

This gives the corrected variance scale. Does it also explain concentration of the observed sample variances?

---

## Concentration despite dependence

Yes: apply the same disjointness covariance control to **both** the outcome table \(h_{z,n}\) and its square \(h_{z,n}^2\).

With fixed \(M\), every nonconstant disjointness multiplier tends to zero. Bounded outcomes keep the total component variation bounded—for the outcome table and for its square. Their disjoint-pair covariances therefore vanish.

For each arm:

- The variance of an empirical moment has a single-group contribution divided by the growing arm count, plus a disjoint-pair covariance contribution. Both vanish.
- Consequently, empirical first and second moments concentrate around \(\mathbb E_n h_{z,n}\) and \(\mathbb E_n[h_{z,n}^2]\).
- Sample variance is second moment minus squared first moment, with a denominator adjustment tending to one. Hence \(s_{z,n}^2-V_{z,n}\xrightarrow{p}0\).

Stable treatment shares then yield

\[
G_n\widehat V_{\mathrm{CR2},n}-R_n \xrightarrow{p}0
\]

Dependence vanishes for moment estimation, but accumulates in the estimator's variance after scaling by \(G_n\).

---

## Conservativeness and sharpness

Under all five assumptions, the correction is nonnegative and the variance floor permits comparison in relative terms. For every fixed tolerance \(\varepsilon>0\),

\[
\Pr\!\left\{
\widehat V_{\mathrm{CR2},n}/\sigma_n^2<1-\varepsilon
\right\}\longrightarrow 0 ,
\]

The probability of understating exact variance by a fixed proportion vanishes.

@informal thm:cr2-phase-frontier: With fixed \(M\ge2\), group growth, stable treatment shares, convergent participation, bounded outcomes, and a positive scaled-variance floor, CR2 is ratio consistent exactly when the correction is relatively negligible.

Precisely, the ratio converges in probability to one if and only if

\[
\frac{\rho E_{\tau,1,n}}{R_n-\rho E_{\tau,1,n}}\longrightarrow 0 .
\]

The numerator is the correction; the denominator is the corrected variance scale.

At \(\rho=0\), ratio consistency follows. This includes \(N_n=M\Big\lfloor \frac{n^{3/4}}{M}\Big\rfloor\), where \(N_n/n\to0\) although \(N_n^2/n\to\infty\), beyond Fu et al. (2026)'s sparsity condition.

---

## Invisible counterfactual alignment

Can one realization reveal the correction? Compare two ways to draw bounded potential-outcome schedules:

- **Same signs:** each unit receives a fair sign, \(+1\) or \(-1\), shared by both arms.
- **Independent signs:** each unit receives independent fair signs for its two arms.

Outcomes depend only on a unit's assigned-arm sign. Each observed unit reveals one sign, so the two observed-data mixtures are identical.

Yet the scaled exact variances approach different limits:

\[
d_{\mathrm{same}}=\frac{1}{M p(1-p)},
\qquad
d_{\mathrm{ind}}=\frac{1}{M p(1-p)}-\frac{2\rho}{M},
\]

These symbols name the same-sign and independent-sign variance limits.

Under same signs, the contrast energy approaches zero; under independent signs, it approaches \(2/M\). At \(\rho>0\), unobserved cross-arm alignment therefore changes variance by \(2\rho/M\) without changing the observed-data mixture.

---

## One-realization lower bound

Let \(\mathcal C_{\mathrm{dense}}\) contain feasible sequences satisfying our five assumptions with fixed parameters \(M,p,\rho,B,c_\sigma\).

Require \(\rho>0\), \(B\ge1\), and \(0<c_\sigma<d_{\mathrm{ind}}\).

@informal thm:qv-diagonal-impossibility: Under these conditions, every variance statistic based on one realization has a limiting worst-case relative-error probability of at least \(1/2\) at some fixed positive tolerance.

Let \(\mathcal O_n\) contain realized groups, assignments, and observed unit outcomes. Every variance statistic \(\widehat S_n(\mathcal O_n)\) satisfies, for some \(\varepsilon>0\),

\[
\frac12
\le
\liminf_{n\to\infty}
\sup_{Y\in\mathcal C_{\mathrm{dense}}}
\Pr_Y\!\left(
\left|
\frac{\widehat S_n(\mathcal O_n)}{\sigma_n^2}-1
\right|>\varepsilon
\right).
\]

Here \(\Pr_Y\) is randomization probability for fixed potential outcomes \(Y\).

The sign constructions concentrate on schedules in this class. Their variance targets stay separated while their observed laws remain asymptotically indistinguishable. A statistic cannot reliably hit both targets.

---

## Open questions

- Gaussian approximation, studentized testing, and Wald coverage.
- Finite-sample CR2 conservativeness.
- Extensions to variable group sizes.

---

## Takeaways

- Groups compete for finite-population members. Additive member contributions create the dependence that survives at the leading variance scale.
- CR2's sample variances concentrate around population table variances. The exact design variance subtracts participation density times additive treatment-effect variation.
- Under our assumptions, CR2 is asymptotically conservative and sharp exactly when that correction is relatively negligible. At positive density, one realization cannot uniformly recover exact variance over the bounded schedule class.

---

## Appendix: Exact variance

This statement gives unbiasedness, the exact design variance, and the exact expectation gap for equal-group CR2.

@formal thm:exact-pame-variance

---

## Appendix: Dense projection limit

This statement identifies the degree-one finite-population correction and bounds the aggregate higher-degree contribution.

@formal thm:dense-projection-limit

---

## Appendix: CR2 phase frontier

This statement gives CR2's probability limit, its one-sided conservativeness, and the necessary and sufficient condition for ratio consistency.

@formal thm:cr2-phase-frontier

---

## Appendix: One-realization lower bound

This statement proves a nonvanishing worst-case relative-error probability for every one-realization variance statistic at positive density.

@formal thm:qv-diagonal-impossibility
