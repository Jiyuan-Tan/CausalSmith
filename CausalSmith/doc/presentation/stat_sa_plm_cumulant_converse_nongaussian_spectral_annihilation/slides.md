# Estimating Treatment Effects With Transform Zeros

Zeros of a treatment-noise transform let us remove covariate contamination exactly, even with an imperfect treatment regression.

---

## Motivation

We observe covariates \(X\), treatment \(T\), and outcome \(Y\), and want the treatment coefficient \(\theta_0\).

Robinson (1988) residualizes treatment and outcome: subtract their conditional means, then estimate the coefficient from the remaining variation.

- Let \(g_0(X)=E_P[T\mid X]\), where \(P\) is the observed-data law; treatment noise is \(\eta=T-g_0(X)\).
- Supplied regression estimates leave covariate-dependent errors in the residuals.
- Mackey et al. (2018) use non-Gaussian treatment noise to support higher-order corrections.

For correction order \(r\ge2\), Jin et al. (2025) give an absolute-error quantile upper guarantee proportional to

\[
\varepsilon_{1,n}^r\varepsilon_{2,n}
+
C_{\theta}\varepsilon_{1,n}^{r+1}
+
(\gamma n)^{-1/2},
\]

Here \(\varepsilon_{1,n},\varepsilon_{2,n}\) bound treatment- and outcome-regression errors in \(L^r\); \(C_{\theta}\) bounds the coefficient; \(n\) is sample size; and \(\gamma\in(1/2,1)\) determines the lower \((1-\gamma)\)-quantile. Their eligibility conditions apply.

Finite-order correction leaves nuisance terms that can dominate sampling error. Can treatment-noise information remove them exactly?

---

## Key idea

A transform zero produces a weight whose expectation vanishes after **every real shift** of treatment noise.

- Treatment-regression error is a shift depending on \(X\).
- Independence of \(\eta\) and \(X\) turns shift cancellation into conditional cancellation.
- A contour integral combines unknown zeros without locating them individually.

The transform is \(M(z)=E_P[e^{z\eta}]\), with \(z\) allowed to be complex. A contour integral follows a closed circle in that complex plane.

With the conditional-mean model, independent treatment noise, fixed nonzero higher cumulant, fixed range and tail bounds, i.i.d. sampling, and sufficiently small mean absolute treatment-regression error, our estimator attains minimax mean-squared error of order \(n^{-1}\).

The treatment-error condition protects the zeros needed for exact cancellation.

---

## Example

Let \(\eta\) have law \(\tfrac12 N(-1,1)+\tfrac12 N(1,1)\), where \(N(m,v)\) has mean \(m\) and variance \(v\).

Its transform vanishes at \(i\pi/2\), where \(i\) is the imaginary unit. The corresponding real weight is \(\sin(\pi Z_n/2)\), with \(Z_n=T-\bar g_n(X)\) and supplied treatment regression \(\bar g_n\).

\[
\widehat\theta_{\sin,n}
=
\begin{cases}
\displaystyle
\Pi_{[-C_{\theta},C_{\theta}]}
\left\{
\frac{\mathbb P_n[Y\sin(\pi Z_n/2)]}
{\mathbb P_n[Z_n\sin(\pi Z_n/2)]}
\right\},
&\displaystyle \mathbb P_n[Z_n\sin(\pi Z_n/2)]\ge e^{-\pi^2/8}/4,\\[3mm]
0,
&\displaystyle \mathbb P_n[Z_n\sin(\pi Z_n/2)]< e^{-\pi^2/8}/4.
\end{cases}
\]

Here \(\mathbb P_n\) is the sample average. The numerator weights outcomes; the denominator weights treatment residuals.

Projection \(\Pi\) clips the ratio to the coefficient range. A small denominator triggers output zero.

Why does this weight remove covariate contamination?

---

## Model

The population treatment and outcome regressions are

\[
 g_0(X)=E_P[T\mid X],\qquad q_0(X)=E_P[Y\mid X]
\]

The innovations separate the coefficient from these covariate functions:

\[
 \eta=T-g_0(X),\qquad \xi=Y-q_0(X)-\theta_0\eta,
\]

Thus \(\theta_0\) links treatment innovation \(\eta\) to the outcome after removing \(q_0(X)\); \(\xi\) is the remaining outcome innovation.

Require \(E_P[\xi\mid X,T]=0\): the conditional outcome mean is \(q_0(X)+\theta_0\{T-g_0(X)\}\).

Treat supplied estimates \((\bar g_n,\bar q_n)\) as fixed before drawing the estimation sample, or condition on external training.

The supplied treatment regression is clipped to its known range. Residualizing treatment means subtracting this supplied function.

---

## Assumptions

**Independence:** \(\eta\perp X\). Every covariate value shares the same treatment-noise distribution.

**Fixed non-Gaussian separation:**

\[
|\kappa_k(\eta)|\ge\delta.
\]

Here \(k=r+1\ge3\), and the cumulant \(\kappa_k\) is the \(k\)th derivative of \(\log M\) at zero. The positive separation \(\delta\) stays fixed as \(n\) grows.

- **Range bounds:** \(|\theta_0|\le C_{\theta}\), \(\|g_0\|_{\infty}\le C_g\), and \(\|q_0\|_{\infty}\le C_q\). These bound the target and covariate contamination.
- **Tail bounds:** \(E_P[\exp(\eta^2/\psi_{\eta}^2)]\le2\) and \(E_P[\exp(\xi^2/\psi_{\xi}^2)\mid X]\le2\). The fixed scales \(\psi_{\eta},\psi_{\xi}\) control the exponential weights.
- **Sampling:** observations are i.i.d.; all range, tail, order, and separation constants are fixed.

In the mixture example, \(k=4\) and \(\kappa_4(\eta)=-2\).

---

## Main result

Compare laws satisfying the model and assumptions with the **same supplied regression inputs**. Denote this class by \(\mathcal P_{\mathrm{NG},n}(p;\mathrm{base})\), where \(p\) collects the parameters and “base” fixes those inputs.

Require a nonempty class, \(n\ge2\), and \(E_P|g_0(X)-\bar g_n(X)|\le\varepsilon_{1,n}\), with

\[
\varepsilon_{1,n}\le \{4R_1\exp(2C_gR_1)\}^{-1},
\]

Here \(R_1\) is a fixed search radius determined by cumulant separation and the treatment-tail bound.

@informal thm:adaptive-rootn-minimax: With the model, independence, fixed cumulant, range and tail bounds, i.i.d. sampling and this treatment-error gate, the contour statistic attains minimax MSE of order \(n^{-1}\) on every nonempty fixed-input class with \(n\ge2\).

\[
\frac{c}{n}
\le
\mathfrak R_n^{\mathrm{NG}}
\le
\sup_{P\in\mathcal P_{\mathrm{NG},n}(p;\mathrm{base})}
E_P\!\left[(\widehat\theta_{\mathrm{spec},n}-\theta_0(P))^2\right]
\le
\frac{C}{n},
\]

The statistic is \(\widehat\theta_{\mathrm{spec},n}\). The minimax risk \(\mathfrak R_n^{\mathrm{NG}}\) is the smallest worst-case MSE over estimators using those same inputs. Positive \(c,C\) depend only on the fixed constants.

For the mixture example, the sine estimator has MSE at most \(C/n\) under the model, independence, sampling, range and outcome-tail bounds, with \(\varepsilon_{1,n}\le1/\pi\).

---

## Zero instruments

Suppose \(M\) has a zero \(z_0\) of multiplicity \(\ell\): its derivatives through order \(\ell-1\) vanish there.

Construct the weight

\[
J_{z_0,\ell}(w)=w^{\ell-1}e^{z_0w},\qquad w\in\mathbb C.
\]

Here \(w\) is the residual at which we evaluate the weight. For every real shift \(d\),

\[
E_P\!\left[J_{z_0,\ell}(\eta+d)\right]=0.
\]

Expanding the shifted polynomial uses only derivatives of \(M\) through order \(\ell-1\); all vanish at \(z_0\).

Independence therefore gives \(E_P[J_{z_0,\ell}(Z_n)\mid X]=0\). This removes any outcome component depending only on \(X\).

When the denominator is nonzero,

\[
\theta_0
=
\frac{E_P\!\left[YJ_{z_0,\ell}(Z_n)\right]}
     {E_P\!\left[Z_nJ_{z_0,\ell}(Z_n)\right]}.
\]

This is the population weighted-outcome ratio. The mixture’s sine weight is the imaginary part of its exponential weight.

But individual zeros and their multiplicities are unknown.

---

## Observable transforms

Write treatment-regression error as \(D_n(X)=g_0(X)-\bar g_n(X)\). Then \(Z_n=\eta+D_n(X)\).

Use observable residual and outcome transforms:

\[
F_n(z)=E_P[e^{zZ_n}],
\qquad
G_n(z)=E_P[Ye^{zZ_n}],
\qquad
H_n(z)=E_P[e^{z\{g_0(X)-\bar g_n(X)\}}].
\]

\(F_n\) averages exponential residual weights; \(G_n\) weights outcomes with them. The unobserved \(H_n\) is the transform of regression error.

Independence gives

\[
F_n(z)=M(z)H_n(z)
\]

Thus residualization multiplies the innovation transform by a nuisance factor.

Let \(b_n(X)=q_0(X)-\theta_0D_n(X)\) and \(B_n(z)=E_P[b_n(X)e^{zD_n(X)}]\). The conditional-mean model gives

\[
G_n(z)=\theta_0(P)F_n'(z)+M(z)B_n(z).
\]

The prime means differentiation in \(z\). Dividing by \(F_n\) separates a coefficient term \(\theta_0(P)F_n'/F_n\) from covariate contamination \(B_n/H_n\).

---

## Contour identification

Choose a counterclockwise circle \(C_j\) with:

- No zero of \(F_n\) on its boundary.
- No zero of \(H_n\) on or inside it.
- A positive enclosed zero count \(N_{C_j}(F_n)\), including multiplicities.

@informal thm:exact-contour-identification: In the non-Gaussian class, a bank circle identifies \(\theta_0(P)\) when \(F_n\) is nonzero on its boundary, \(H_n\) is nonzero on and inside it, and its enclosed zero count is positive.

\[
(\theta_0(P):\mathbb C)
=
\Theta_{C_j}(F_n,G_n)
=
\{N_{C_j}(F_n)\,2\pi i\}^{-1}
\oint_{C_j}\frac{G_n(z)}{F_n(z)}\,dz .
\]

The integral accumulates the observable ratio around the circle; \(\Theta_{C_j}\) divides it by the enclosed count and \(2\pi i\).

- The integral of \(F_n'/F_n\) equals \(2\pi i\) times the zero count.
- The contamination \(B_n/H_n\) is analytic—complex differentiable throughout the interior—so its integral is zero.

Each enclosed zero contributes the same coefficient. Dividing by their count recovers \(\theta_0\).

What guarantees a usable circle?

---

## Treatment-error stability

The first requirement is that regression error contributes no zeros:

\[
 \sup_{|z|\le R_1}|H_n(z)-1|
 \le R_1 e^{2C_gR_1}\varepsilon_{1,n}.
\]

This bounds how far the nuisance transform can move from one across the search disk.

Bounded treatment regressions give \(|D_n|\le2C_g\). Under the main result’s error gate, the right side is at most \(1/4\), so \(|H_n|\ge3/4\).

Consequently, \(F_n=MH_n\) and \(M\) have the same zeros there, including multiplicities.

The mixture makes the same protection concrete:

\[
E_P\!\left[
Z_n\sin\!\left(\frac{\pi Z_n}{2}\right)
\right]
=
e^{-\pi^2/8}
E_P\!\left[
\cos\!\left(\frac{\pi D_n}{2}\right)
\right],
\]

This is its population denominator. When \(E_P|D_n|\le1/\pi\), it is at least \(e^{-\pi^2/8}/2\).

Regression error changes instrument strength while preserving exact cancellation.

---

## Why zeros must exist

Suppose the innovation transform had no zeros throughout a large disk.

- Then \(\log M\) would be analytic throughout that disk, with value zero at the origin because \(M(0)=1\).
- The sub-Gaussian tail restriction bounds transform growth: the real part of \(\log M\) has a quadratic upper envelope.
- Analytic derivative bounds then force derivatives of order \(k\ge3\) at the origin to become small as the zero-free disk grows.
- But that derivative is \(\kappa_k(\eta)\), whose magnitude must be at least the fixed \(\delta\).

These restrictions cannot coexist on an arbitrarily large zero-free disk.

@informal lem:zero-localization: A centered treatment innovation with \(k=r+1\), \(r\ge2\), sub-Gaussian scale at most \(\psi_{\eta}\), and \(|\kappa_k(\eta)|\ge\delta\) has a transform zero within radius \(R_0\).

\[
A_k=(2^{k+4}k!)^{1/(k-2)},\qquad
R_0=A_k(\psi_{\eta}^2/\delta)^{1/(k-2)},\qquad
M(z)=E_P[e^{z\eta}].
\]

This computes the guaranteed zero radius: \(A_k\) depends only on order, \(\psi_{\eta}\) controls growth, and \(\delta\) prevents higher derivatives from being too small.

---

## A protected contour bank

Set \(R_1=R_0+1\). Every circle with radius strictly between \(R_0\) and \(R_1\) encloses the guaranteed zero.

Avoiding boundary zeros alone is insufficient: estimation also needs the transform bounded away from zero.

- The fixed tail envelope and normalization \(M(0)=1\) bound how many zeros can occur in a slightly larger disk.
- Place finitely many candidate radii between \(R_0\) and \(R_1\), with enough candidates to avoid small neighborhoods of every zero’s distance from the origin.
- After accounting for these zeros, the same analytic growth control bounds the remaining factor away from zero on a protected circle.

Thus one bank, fixed before seeing the distribution, guarantees a circle with positive count and a fixed positive boundary lower bound \(a_{\star}\).

@informal lem:finite-contour-bank: Under the non-Gaussian class assumptions, a finite bank determined by the fixed constants contains a circle between \(R_0\) and \(R_1\) that encloses a zero and satisfies \(|M(z)|\ge a_{\star}>0\) on its boundary.

Since \(|H_n|\ge3/4\), this protection transfers to \(F_n\). The protected index may vary across distributions; the bank and lower bound remain fixed.

---

## Pilot selection

Split the sample: a pilot fold selects the circle and count; an independent evaluation fold estimates the coefficient.

For fold \(a\), with observation indices \(I_a\), compute

\[
\widehat F_{a,n}(z)=|I_a|^{-1}\sum_{i\in I_a}\exp(zZ_{n,i}),
\qquad
\widehat G_{a,n}(z)=|I_a|^{-1}\sum_{i\in I_a}Y_i\exp(zZ_{n,i}),
\]

Here \(Z_{n,i}=T_i-\bar g_n(X_i)\). These sample averages estimate \(F_n\) and \(G_n\).

For each pilot circle with a positive boundary denominator, compute its empirical zero count:

\[
N_j=
\frac{1}{2\pi i}\oint_{C_j}
\frac{\widehat F'_{0,n}(z)}
{\widehat F_{0,n}(z)}\,dz
\]

The logarithmic-derivative integral counts zeros of the pilot transform. Numerical integration isolates its unique integer value.

Retain circles with boundary lower bound at least \(a_{\star}/2\) and \(N_j\ge1\). Select the retained circle with the strongest lower bound; call its index \(j_{\star}\).

Why does its pilot count equal the population count?

---

## Stability of the count

A zero count changes only when a zero crosses the contour boundary.

If \(\sup_{z\in C_j}|\widehat F_{0,n}(z)-F_n(z)|<\inf_{z\in C_j}|F_n(z)|\), continuously moving from \(F_n\) to \(\widehat F_{0,n}\) never makes a boundary value zero.

Therefore their enclosed counts agree, even if individual zeros move or split.

Under our model, range, tail and sampling assumptions,

\[
E_{P^{\otimes n}}\!\left[\sup_{|z|\le R_1}
|\widehat F_{a,n}(z)-F_n(z)|^2\right]
+
E_{P^{\otimes n}}\!\left[\sup_{|z|\le R_1}
|\widehat G_{a,n}(z)-G_n(z)|^2\right]
\le
\frac{K}{|I_a|}.
\]

Here \(K\) is fixed. The bound controls both transforms uniformly across the whole search disk, hence every candidate circle.

- Small pilot error makes the guaranteed protected circle eligible.
- Every retained circle then has a population boundary margin larger than that error, so \(N_{j_{\star}}=N_{C_{j_{\star}}}(F_n)\).
- Crossing a fixed error threshold has probability at most a constant divided by \(n\), by the squared-error bound.

Thus an incorrect normalization is confined to an event whose contribution to MSE can be controlled.

---

## Evaluation and risk

On the independent evaluation fold, check the selected boundary denominator again and approximate

\[
\frac{1}{N_{j_{\star}}2\pi i}
\oint_{C_{j_{\star}}}
\frac{\widehat G_{1,n}(z)}
{\widehat F_{1,n}(z)}\,dz
\]

This is the empirical identifying integral on the selected circle, normalized by its pilot count.

- **Correct normalization:** on the small-error event, the pilot count equals the population count.
- **Stable division:** protected boundary denominators turn transform errors into coefficient errors with a fixed amplification bound.
- **Bounded failures:** clip the real output to \([-C_{\theta},C_{\theta}]\); failed checks return zero. The squared loss is bounded, so events with probability at most a constant divided by \(n\) contribute at most that order to MSE.
- **Numerical accuracy:** integration error is at most \(1/n\).

Exact population cancellation and uniform transform variance yield the \(C/n\) upper bound.

For the matching lower bound, keep treatment, regressions and supplied inputs fixed; vary the coefficient with independent Gaussian outcome noise. Coefficients separated by \(h/\sqrt n\), for a fixed small \(h\), remain difficult to distinguish.

---

## Open questions

What happens when non-Gaussian separation weakens with sample size?

\[
|\kappa_k(\eta_n)|\ge\delta_n
\qquad\text{with}\qquad
\delta_n\downarrow0
\]

Here \(\eta_n\) is a changing treatment-noise law and \(\delta_n\) its shrinking separation threshold.

- Determine sharp minimax MSE as a function of \((n,\varepsilon_{1,n},\varepsilon_{2,n},\delta_n)\).
- Select from data among double/debiased machine learning, finite-order corrections, and contour procedures.
- Establish uniformly valid inference and matching local minimax lower bounds.

---

## Takeaways

- Transform zeros give weights that cancel every covariate-dependent treatment-regression shift; contour integration removes the remaining covariate contamination exactly.
- Fixed cumulant separation and tail bounds guarantee a localized zero and a protected circle in a finite bank. Small mean absolute treatment error preserves that geometry.
- Uniform transform control preserves the pilot zero count and stabilizes evaluation. Under the model, independence, fixed bounds, i.i.d. sampling and explicit treatment-error gate, the resulting fixed-input minimax MSE is of order \(n^{-1}\).

---

## Appendix: Zero-based instruments

A known innovation-transform zero yields a shift-annihilating instrument and, when its denominator is nonzero, an identifying moment ratio.

@formal thm:known-zero-instrument

---

## Appendix: Exact contour identification

A contour with a zero-free boundary, zero-free nuisance factor inside, and positive zero count identifies the coefficient exactly.

@formal thm:exact-contour-identification

---

## Appendix: Fixed-code minimax estimation

With fixed cumulant separation and the treatment-error gate, the finite contour statistic attains matched fixed-code MSE bounds and the stated generalized-quantile bound.

@formal thm:adaptive-rootn-minimax
