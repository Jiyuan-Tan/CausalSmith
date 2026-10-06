# Cutoff Effects With a Noisy Score

A reliable treatment record lets us estimate the effect at the true cutoff and quantify its precision, even when the score is measured with error.

---

## Motivation

A practitioner observes treatment, an outcome, and a noisy eligibility score.

- Standard regression discontinuity compares outcomes just above and below the true cutoff.
- Selecting observations near the noisy cutoff mixes people at different true distances; recorded treatment still reveals their true side.
- Pei and Shen (2017) establish identification from observed treatment and a Gaussian-contaminated score.
- Dong (2018) develops deconvolution local-linear inference using a bias-centered asymptotic normal approximation under its smoothness and error conditions.

How precisely can we estimate the true cutoff effect, with coverage guaranteed across a specified class at every sample size?

---

## Key idea

Recorded treatment turns the cutoff into an endpoint within each arm.

We construct positive averages near that latent endpoint, then correct their polynomial weights for Gaussian noise.

Our benchmark maintains:

- Known support \([-1,1]\), known noise scale \(\sigma\in[0,1]\), and Gaussian error independent of the score and both potential outcomes.
- A continuous score density and binary potential-outcome means between \(1/4\) and \(3/4\).
- Continuous means whose variation is at most twice distance raised to a fixed power \(0<\beta\le1\), throughout the support.

These conditions yield matching optimal orders for absolute estimation error and uniformly valid \(90\%\) connected interval length, across every sample size and noise scale.

---

## Example

Take \(\beta=1\): either potential-outcome mean changes by at most twice the change in the true score.

Suppose the known noise standard deviation is \(\sigma=n^{-1/6}\), where \(n\ge2\) is sample size.

\[
r_1(n,n^{-1/6})
=h_\star(n,n^{-1/6})
\asymp
\frac{n^{-1/6}}{[1+\tfrac12\log n]^{3/2}}.
\]

Here \(h_\star\) is the recoverable distance from the cutoff; \(r_1\) is the common optimal order of estimation error and honest interval length. The symbol \(\asymp\) means comparison within positive constant factors.

Although measurement improves with sample size, noise still affects precision: the direct-observation order would be \(n^{-1/3}\).

---

## Model

Let \(P\) denote the latent population law. The true score is \(X\); \(Y^0,Y^1\) are binary potential outcomes; \(\varepsilon\) is standardized measurement error.

\[
D=\mathbf1\{X\ge0\},\qquad
Y=(1-D)Y^0+DY^1,\qquad
W=X+\sigma\varepsilon.
\]

We observe treatment \(D\), realized outcome \(Y\), and proxy score \(W\) in \(n\) independent observations. Treatment records the true cutoff side.

Let \(\mu_d(P,x)\) be the continuous conditional mean of potential outcome \(Y^d\) at true score \(x\), for arm \(d=0,1\).

\[
\theta(P)=\mu_1(P,0)-\mu_0(P,0).
\]

The target \(\theta(P)\) is the treatment effect at the true cutoff. Continuity connects each cutoff mean to observations in its own arm.

---

## Assumptions

Write \(\mathcal M_\beta(\sigma)\) for the benchmark population class.

- **Calibration:** \(\varepsilon\sim N(0,1)\) and \(\varepsilon\perp(X,Y^0,Y^1)\). The same known error mechanism applies across scores and outcomes.
- **Support and density:** \(X\in[-1,1]\), with continuous density \(f(P,x)\) satisfying \(1/4\le f(P,x)\le3/4\) everywhere on this interval. Both arms have mass near the cutoff.
- **Outcome range:** \(1/4\le\mu_d(P,x)\le3/4\) throughout the interval. Success probabilities stay away from zero and one.
- **Global smoothness:** \([\mu_d(P,\cdot)]_\beta\le2\). This means \(|\mu_d(P,x)-\mu_d(P,t)|\le2|x-t|^\beta\) for every pair of scores.

Support, calibration, and \(\beta\) are known inputs.

In our \(\beta=1\) example, smoothness bounds slopes in this distance sense across the entire interval.

---

## Resolution

Let \(\nu=2\beta+1\) and \(h_0=n^{-1/\nu}\), the direct-observation resolution. A candidate distance \(h\) from the cutoff incurs Gaussian inversion cost \(\Psi(h,\sigma)\):

\[
\Psi(h,\sigma)=
\begin{cases}
0,&\sigma\le h,\\
(\sigma/h)^{2/3}-1,&\sigma^4\le h<\sigma,\\
h^{-1/2}\{1+\log(\sigma^2/\sqrt h)\}-1,&h<\sigma^4.
\end{cases}
\]

Noise below the candidate resolution adds no cost in this characterization. Finer resolution requires increasingly costly correction.

The optimal resolution \(h_\star(n,\sigma)\) is the unique root in \([h_0,1]\) of

\[
\log n+\nu\log h_\star(n,\sigma)
=\Psi(h_\star(n,\sigma),\sigma).
\]

This equation balances sample information against endpoint precision and noise correction. The effect-error scale is \(r_\beta(n,\sigma)=h_\star(n,\sigma)^\beta\).

---

## Main result

Define \(R_\beta(n,\sigma)\) as the smallest worst-case expected absolute error over all estimators.

Define \(\mathcal L_\beta(n,\sigma)\) as the smallest worst-case expected length among connected intervals covering \(\theta(P)\) with probability at least \(0.9\) for every \(P\in\mathcal M_\beta(\sigma)\).

@informal thm:uniform-frontier: For fixed \(0<\beta\le1\), optimal absolute error and honest connected interval length are comparable to \(r_\beta(n,\sigma)\), uniformly over \(n\ge2\) and known \(\sigma\in[0,1]\) on \(\mathcal M_\beta(\sigma)\).

\[
c r_\beta(n,\sigma)
\le R_\beta(n,\sigma)
\le \sup_{P\in\mathcal M_\beta(\sigma)}
\mathbb E_{P,n}
\left|\widetilde\theta_{\beta,n,\sigma}-\theta(P)\right|
\le E_\beta(n,\sigma)
\le C r_\beta(n,\sigma)
\]

\[
c r_\beta(n,\sigma)
\le \mathcal L_\beta(n,\sigma)
\le \sup_{P\in\mathcal M_\beta(\sigma)}
\mathbb E_{P,n}
\operatorname{length}(\widetilde I_{\beta,n,\sigma})
\le 2E_\beta(n,\sigma)
\le C r_\beta(n,\sigma),
\qquad
\widetilde I_{\beta,n,\sigma}\in\mathcal I_{\beta,n,\sigma}.
\]

Here \(\widetilde\theta_{\beta,n,\sigma}\) and \(\widetilde I_{\beta,n,\sigma}\) are the selected observable estimator and interval; \(\mathbb E_{P,n}\) averages over sampling and any independent procedure randomization. Membership in \(\mathcal I_{\beta,n,\sigma}\) means uniform \(90\%\) coverage.

The construction below supplies the observable estimator with worst expected error at most \(E_\beta\), and a connected interval with uniform \(90\%\) coverage and worst expected length at most \(2E_\beta\).

The constants \(c,C>0\) depend only on \(\beta\). In our example, both optimal criteria therefore have the order shown on the example slide.

---

## Endpoint weights

We first design the average we would want if the true score were observed.

For integer index \(L\ge1\), let \(T_L\) be the Chebyshev polynomial, normalized by \(T_L(\cos t)=\cos(Lt)\).

\[
K_L(x)
=
\frac{
\left(\dfrac{1-T_L(1-2x)}{2x}\right)^3
}{
\displaystyle\int_0^1
\left(\dfrac{1-T_L(1-2t)}{2t}\right)^3\,dt
}.
\]

The polynomial weight \(K_L\) is nonnegative on \([0,1]\) and integrates to one. Increasing \(L\) concentrates this averaging near zero.

\[
M_{L,\beta}=\int_0^1 x^\beta K_L(x)\,dx.
\]

The moment \(M_{L,\beta}\) measures displacement from the cutoff in smoothness units. It satisfies \(M_{L,\beta}\le C L^{-2\beta}\): endpoint resolution is of order \(L^{-2}\).

---

## Population ratios

Reflect the untreated arm onto \([0,1]\): use signs \(s_1=1\) and \(s_0=-1\). Within arm \(d\), the reflected true score \(s_dX\) is nonnegative.

\[
A_{d,L}(P)
=\int_0^1 K_L(x)\,\mu_d(P,s_dx)\,f(P,s_dx)\,dx,
\qquad
B_{d,L}(P)
=\int_0^1 K_L(x)\,f(P,s_dx)\,dx.
\]

The numerator \(A_{d,L}\) averages outcomes near the endpoint; the denominator \(B_{d,L}\) measures their weighted population mass.

- Their ratio is a positive weighted average of the arm’s conditional mean.
- Density bounds guarantee \(B_{d,L}(P)\ge1/4\).
- Smoothness bounds each ratio’s distance from its cutoff mean by at most \(6M_{L,\beta}\).

The ratio handles the unknown density through normalization. How can we estimate these averages using the noisy score?

---

## Gaussian correction

Wu and Yang (2020) use Gaussian polynomial inversion to obtain unbiased latent moments. We apply that principle to the endpoint weight.

Let \(m_L=3(L-1)\) be its degree, and let \(K_L^{(2k)}\) denote its derivative of order \(2k\).

\[
Q_{L,\sigma}(w)
=
\sum_{k=0}^{\lfloor m_L/2\rfloor}
\frac{(-\sigma^2/2)^k}{k!}\,
K_L^{(2k)}(w).
\]

The correction \(Q_{L,\sigma}\) uses the known noise scale. Its sum is finite because the weight is a polynomial.

\[
\mathbb E\!\left[Q_{L,\sigma}(x+\sigma\varepsilon)\right]=K_L(x),
\qquad
\mathbb E\!\left[Q_{L,\sigma}(x+\sigma\varepsilon)^2\right]
=\sum_{j=0}^{m_L}\frac{\sigma^{2j}[K_L^{(j)}(x)]^2}{j!}.
\]

At each true score \(x\), averaging over Gaussian error exactly recovers the desired weight. The second identity gives the sampling cost of that recovery.

Using \(K_L(W)\) directly would average a noise-blurred weight.

---

## Observable arm estimates

For observation \(i\), use its recorded arm \(D_i\), outcome \(Y_i\), and reflected proxy \(s_dW_i\).

\[
\widehat A_{d,L}
=
\frac1n\sum_{i=1}^n
\mathbf1\{D_i=d\}Y_iQ_{L,\sigma}(s_dW_i).
\]

\[
\widehat B_{d,L}
=
\frac1n\sum_{i=1}^n
\mathbf1\{D_i=d\}Q_{L,\sigma}(s_dW_i).
\]

These averages are unbiased for \(A_{d,L}(P)\) and \(B_{d,L}(P)\). Corrected weights can have either sign, so an empirical denominator can be small or negative.

\[
\widehat\mu_{d,L}
=
\Pi_{[1/4,3/4]}
\left(
\frac{\widehat A_{d,L}}
{\max\{\widehat B_{d,L},1/8\}}
\right).
\]

Flooring stabilizes division below the population mass bound; projection \(\Pi_{[1/4,3/4]}\) restricts the estimate to the maintained mean range.

Subtract the two arm estimates to estimate the cutoff effect.

---

## Cost of precision

The density upper bound and exact Gaussian second moments give a common second-moment bound:

\[
V_L(\sigma)
=\frac34\sum_{j=0}^{m_L}\frac{\sigma^{2j}}{j!}
\int_0^1\bigl(K_L^{(j)}(x)\bigr)^2\,dx.
\]

Here \(V_L(\sigma)\) controls the variance of each empirical average after division by \(n\).

A factorial derivative bound yields

\[
V_L(\sigma)\le C L^2
\sum_{j=0}^{m_L}\frac{(C\sigma^2L^4)^j}{(j!)^3}.
\]

One factorial comes from Gaussian orthogonality; two come from the squared derivative bound.

Larger \(L\) reduces endpoint bias but increases the cost of recovering the latent average. Bounding this finite series produces the noise cost \(\Psi\) in the resolution equation.

---

## Honest inference

For each positive index, combine the arm estimates and construct a public radius:

\[
\widehat\theta_L=\widehat\mu_{1,L}-\widehat\mu_{0,L},
\qquad
\rho_L=12M_{L,\beta}
+28\sqrt{\frac{40V_L(\sigma)}{n}},
\]

The first term covers worst-case endpoint bias; the second covers sampling error in both numerators and denominators.

\[
I_L=
[\widehat\theta_L-\rho_L,\widehat\theta_L+\rho_L]
\cap[-1,1].
\]

The interval \(I_L\) surrounds the observable effect estimate with both allowances.

Chebyshev’s inequality and a union bound control the four empirical-average errors simultaneously with probability at least \(0.9\).

@informal thm:finite-certificate: For \(P\in\mathcal M_\beta(\sigma)\), \(n\ge2\), \(0<\beta\le1\), \(0\le\sigma\le1\) and integer \(L\ge1\), \(I_L\) covers \(\theta(P)\) with probability at least \(0.9\); public selection preserves uniform coverage.

---

## Public selection

Choose precision using known inputs, before observing outcomes.

The finite candidate cap is \(L_{\max}=\left\lceil n^{1/(4\beta+2)}\right\rceil\).

\[
L_\star
=
\min\operatorname*{arg\,min}_{L\in\{0,\ldots,L_{\max}\}}
\rho_L.
\]

The selected index \(L_\star\) minimizes the radius, resolving ties by the smallest index.

\[
E_\beta(n,\sigma)=\rho_{L_\star}.
\]

This minimum is the public error bound \(E_\beta\) appearing in the main result.

- Index zero supplies estimate zero, radius \(1/2\), and interval \([-1/2,1/2]\), containing the full admissible target range.
- Selection depends only on \((\beta,n,\sigma)\), so the same index is used across samples.
- The selected estimate has worst expected absolute error at most \(E_\beta\); the selected honest interval has worst expected length at most \(2E_\beta\).

---

## Noise regimes

The same resolution equation covers three regions. Recall \(\nu=2\beta+1\) and \(h_0=n^{-1/\nu}\).

| Region | Exact condition | Endpoint resolution |
|---|---|---|
| Direct | \(\sigma\le h_0\) | Exactly \(h_0\) |
| Intermediate | \(\sigma>h_0\) and \(\log(n\sigma^{4\nu})\le\sigma^{-2}-1\) | Comparable to \(\sigma/[1+\log(n\sigma^\nu)]^{3/2}\) |
| Compact support | \(\sigma>h_0\) and \(\log(n\sigma^{4\nu})>\sigma^{-2}-1\) | Determined by the compact branch of \(\Psi\) |

The formulas agree at \(h_\star=\sigma=h_0\) and at \(h_\star=\sigma^4\).

Our \(\beta=1,\sigma=n^{-1/6}\) example stays in the intermediate region for every \(n\ge2\).

For every fixed positive \(\sigma\), the compact-support region eventually applies:

\[
r_\beta(n,\sigma)
\asymp
\left\{\frac{\log\log(en)}{\log(en)}\right\}^{2\beta}
\]

This is the asymptotic order of both optimal criteria; constants here may depend on the fixed noise level.

---

## Hidden cutoff changes

To establish optimality, construct two benchmark populations \(P^\pm_{b,m}\) with uniform scores and untreated mean \(1/2\).

Here \(0<b\le1\) is a support width and integer \(m\ge2\) controls cancellation. A polynomial \(g_m\) equals one at zero and zero at one, while

\[
\int_0^1t^kg_m(t)\,dt=0.
\]

This holds for every integer \(0\le k\le m-2\): the perturbation’s low-order moments cancel.

Define the full-interval profile explicitly by

\[
v_{b,m}(x)=
\begin{cases}
1,&-1\le x<0,\\
g_m(x/b),&0\le x\le b,\\
0,&b<x\le1.
\end{cases}
\]

With \(\kappa=1/100\), both laws have untreated mean \(1/2\), and their treated means are \(\mu_1(P^\pm_{b,m},x)=\frac12\pm\kappa(b/m^2)^\beta v_{b,m}(x)\).

Both populations obey the global restrictions, but

\[
\left|\theta(P^+_{b,m})-\theta(P^-_{b,m})\right|
=
2\kappa\left(\frac{b}{m^2}\right)^\beta.
\]

Their cutoff effects differ while Gaussian smoothing suppresses the observable difference.

---

## Why both bounds match

Choose the perturbation’s support and endpoint resolution as

\[
b_m(\sigma)=\min\{1,\sigma\sqrt m/8\},
\qquad
h_m(\sigma)=\frac{b_m(\sigma)}{m^2},
\qquad \sigma>0.
\]

The support grows with noise and polynomial order until it reaches the known boundary. This saturation explains the compact-support regime up to constant factors.

For \(b=b_m(\sigma)\) and \(h=h_m(\sigma)\), moment cancellation gives

\[
\chi^2\bigl((P^+_{b,m})_{\mathrm{obs}},
           (P^-_{b,m})_{\mathrm{obs}}\bigr)
\le
\frac{32}{3}\kappa^2 h^{2\beta+1}
\exp\!\left(-\frac{1+\Psi(h,\sigma)}{32}\right).
\]

The quantity \(\chi^2\) measures squared likelihood-ratio differences between the full observed triples.

Choose \(m\) so \(h\) is within fixed constant factors of \(h_\star\). The sample laws then differ by at most \(1/5\) in any event probability.

- An estimator cannot reliably distinguish the separated cutoff effects.
- Uniform \(90\%\) coverage forces an interval to contain both effects with probability at least \(3/5\) under one alternative, requiring their separation in length.

Thus the same resolution limits estimation and honest inference, including independently randomized procedures.

At \(\sigma=0\), localized direct alternatives of width \(h_0=n^{-1/(2\beta+1)}\) supply the corresponding lower bound of order \(h_0^\beta\). Adding Gaussian noise is a Markov transformation, so this direct lower bound also remains valid at every positive noise scale.

---

## Open questions

- **Estimated calibration:** incorporate validation data and noise-scale uncertainty into the weights and coverage guarantee.
- **Unknown smoothness:** account for choosing procedures across smoothness classes while maintaining honest coverage.
- **Applied precision:** assess latent benchmark restrictions and the numerical size of the explicit radius at relevant sample sizes.

---

## Takeaways

- Recorded treatment reveals the true cutoff side; Gaussian-corrected polynomial averages recover information about distance from that cutoff.
- Positive endpoint averaging, stabilized ratios, and a public bias-plus-sampling radius give observable estimation and finite-sample honest inference.
- Under known calibration, bounded support, density bounds, and global outcome-mean smoothness, one resolution equation gives matching optimal orders across all noise scales.

---

## Appendix: Uniform estimation and interval frontier

The resolution rate characterizes both minimax criteria, with observable attainment and constants uniform in sample size and noise scale.

@formal thm:uniform-frontier

---

## Appendix: Finite sample certificate

The polynomial ratio procedure has explicit absolute-error and coverage bounds, preserved by deterministic public selection.

@formal thm:finite-certificate

---

## Appendix: Direct-experiment specialization

The direct lower bound holds at every noise scale, and the public procedure attains the direct rate at zero noise.

@formal thm:direct-reduction

---

## Appendix: Larger-class converse

The benchmark embeds into the locally regular Gaussian class without changing the target or randomized observed experiment, so its lower bounds transfer.

@formal prop:published-class-converse-transfer

**Source provenance**

The Dong (2018) comparison is provenance-only and has no proof-use. Codex verified the supplied primary-source attestation, while Claude could not independently retrieve the cited dissertation.
