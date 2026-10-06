# Causal Means From Noisy Doses

We characterize how accurately a causal response can be estimated when true doses are scarce near the target and recorded with Gaussian error.

---

## Motivation

- \(A\) is the true dose, \(W\) its recorded value, \(Y\) the outcome, and \(X\) one of two observed strata.
- We want the population mean outcome from setting everyone’s true dose to \(a_0=1/2\).
- Adjusting within strata addresses confounding.
- Averaging outcomes at nearby recorded doses mixes true doses that may be far apart.

Huang and Zhang (2023) combine causal adjustment with deconvolution—reversing measurement-error averaging—under positivity and regularity conditions.

Here latent-dose density can vanish at the target. Reversing Gaussian averaging also makes narrow localization increasingly variable.

How do dose scarcity and measurement precision jointly determine estimation accuracy and confidence-interval length?

---

## Key idea

Separate the weight we want on true doses from the weight we calculate on recorded doses.

- A **nonnegative latent weight** averages causal responses near the target.
- An **observable inverse weight** reproduces that latent weight after averaging over measurement error.
- An error bound calculated from known model parameters chooses how much localization the sample can support.

Under bounded responses, two strata with unconfounded dose assignment within each stratum, known compact dose support, fixed smoothness, and polynomial dose scarcity, estimation error and honest \((1-\alpha)\)-interval length have matching optimal orders for \(\alpha\in(0,1/2)\).

Fourier inversion supplies the smaller-error regimes. Polynomial inversion exploits known support at larger error scales.

---

## Example

Consider equal stratum shares and the same centered-dose density in both strata:

\(p_0=p_1=1/2\) and \(g_x(t)=(\kappa+1)2^\kappa|t|^\kappa\mathbf1\{|t|\le1/2\}\), where \(t=A-a_0\). The exponent \(\kappa\) controls scarcity.

A Bernoulli response has mean \(\mu_+(a_0+t)=1/2+\delta(t)\), with

\[
\delta(t):=
\varepsilon h_0^\beta
\left(1-\left(\frac{t}{h_0}\right)^2\right)^2
\mathbf1\{|t|\le h_0\}.
\]

Here \(\beta\) controls response smoothness, \(h_0=n^{-1/(2\beta+\kappa+1)}\) is the bump width for sample size \(n\), and \(\varepsilon>0\) is a small fixed amplitude.

The causal target is the peak: \(\theta(P_+)=1/2+\varepsilon h_0^\beta\).

A positive true-dose weight concentrated near zero averages the bump near its peak. How can noisy recorded doses recover that same weighted height?

---

## Model

Under a structural law \(P\), \(Y(a)\) is the potential outcome at dose \(a\). Consistency gives \(Y=Y(A)\).

\[
W=A+\sigma Z.
\]

Each record \(O=(X,W,Y)\) contains stratum, recorded dose, and realized outcome. We observe \(n\) independent records from the same distribution.

- \(Z\sim N(0,1)\), with known standard deviation \(\sigma\in[0,1/4]\).
- \(Z\perp(X,A,Y(\cdot))\): measurement error carries no information about assignment or responses.
- \(Y(\cdot)\perp A\mid X\): within each stratum, dose assignment is independent of the entire potential-response schedule.

Write \(\mathcal X=\{0,1\}\), \(p_x=P(X=x)\), and \(\mu_x(a)=E_P[Y(a)\mid X=x]\).

\[
\theta(P)=E_P[Y(a_0)].
\]

The target averages stratum-specific causal responses using population shares: \(\theta(P)=\sum_{x\in\mathcal X}p_x\mu_x(a_0)\).

---

## Assumptions

Center the recorded dose: \(V=W-a_0=t+\sigma Z\).

**Public class constants.** Write \(K=(p_{\min},c_{\mathrm{lo}},c_{\mathrm{hi}})\), where \(0<p_{\min}\le1/2\) and \(0<c_{\mathrm{lo}}\le c_{\mathrm{hi}}\). True doses lie in \([0,1]\), and each centered conditional density satisfies
\(c_{\mathrm{lo}}|t|^\kappa\le g_x(t)\le c_{\mathrm{hi}}|t|^\kappa\) on \([-1/2,1/2]\), with \(\kappa\in[0,2]\).

**Fixed smoothness.** For every \(a,a'\in[0,1]\),  
\(|\mu_x(a)-\mu_x(a')|\le|a-a'|^\beta\), with fixed \(\beta\in(0,1]\).

Responses within distance \(h\) of the target therefore differ from its response by at most \(h^\beta\).

**Bounded responses and represented strata.** Potential outcomes and conditional means lie in \([0,1]\), and every stratum has probability at least \(p_{\min}\).

These restrictions define \(\mathcal P_{K,\beta,\kappa,\sigma}\). The matched lower-bound class is nonempty under the calibration \(c_{\mathrm{lo}}\le(\kappa+1)2^\kappa\le c_{\mathrm{hi}}\).

---

## Three precision regimes

Define \(d=2\beta+\kappa+1\), combining smoothness and scarcity, and \(L_n=\log(en)\), the logarithmic sample scale.

\[
\rho_{n,\sigma}=b_{n,\sigma}^{\beta},
\qquad
b_{n,\sigma}=
\begin{cases}
n^{-1/d},&0\le\sigma\le n^{-1/d},\\[2pt]
\dfrac{\sigma}{\sqrt{\log(e+n\sigma^d)}},
&n^{-1/d}<\sigma\le L_n^{-1/2},\\[6pt]
\dfrac{\log(e+\sigma^2L_n)}{L_n},
&L_n^{-1/2}<\sigma\le1/4.
\end{cases}
\]

The width \(b_{n,\sigma}\) describes attainable localization; smoothness turns it into error scale \(\rho_{n,\sigma}\).

- **Direct:** measurement error is no larger than the width already required by scarce doses.
- **Intermediate:** the cost of Gaussian Fourier inversion determines the width.
- **Compact support:** polynomial localization uses the known latent interval.

The last branch requires a different inversion mechanism.

---

## Main result

Let \(Q_P^n\) denote the complete observed-sample distribution.

- \(R_n(\sigma)\) is the smallest worst-law expected absolute error among all estimators.
- \(H_n(\sigma)\) is the smallest worst-law expected length among connected intervals with coverage at least \(1-\alpha\) under every model law, for fixed \(\alpha\in(0,1/2)\).

@informal thm:uniform-frontier: For fixed \(K\), \(\beta\in(0,1]\), \(\kappa\in[0,2]\), and \(\alpha\in(0,1/2)\), optimal absolute error and honest \((1-\alpha)\)-interval length have order \(\rho_{n,\sigma}\), uniformly over known \(\sigma\in[0,1/4]\) for sufficiently large \(n\), under the calibration above.

\[
c\rho_{n,\sigma}\le R_n(\sigma)\le C\rho_{n,\sigma},
\qquad
c\rho_{n,\sigma}\le H_n(\sigma)\le C\rho_{n,\sigma}.
\]

The positive constants \(c,C\) and sample-size threshold are independent of \(\sigma\).

One observable procedure attains both upper bounds; no estimator or honest connected interval improves their order uniformly over the model.

At zero error, the optimal scale is \(n^{-\beta/(2\beta+\kappa+1)}\): the response-height scale of the example’s bump.

---

## Latent localization

First suppose true doses were observed. Choose a nonnegative weight \(q(t)\) concentrated near zero.

\[
m_{x,q}
=
\frac{\displaystyle\int_{-1/2}^{1/2}
\mu_x(a_0+t)q(t)g_x(t)\,dt}
{\displaystyle\int_{-1/2}^{1/2}q(t)g_x(t)\,dt},
\qquad x\in\mathcal X.
\]

The ratio \(m_{x,q}\) is a weighted causal mean within stratum \(x\).

- Nonnegativity makes it a genuine average.
- Neighborhood support gives a positive denominator even when \(g_x(0)=0\).
- Smoothness controls its distance from \(\mu_x(a_0)\).

In the example, this averages the bump’s height above \(1/2\). Narrower localization approaches the peak but uses fewer true doses.

The remaining obstacle is that we observe \(V\), not \(t\).

---

## Observable localization

Construct a recorded-dose weight \(\ell_q\) satisfying

\[
E_Z[\ell_q(t+\sigma Z)]=q(t),
\qquad -1/2\le t\le1/2,
\qquad Z\sim N(0,1),
\]

At each true-dose displacement \(t\), averaging \(\ell_q\) over measurement error returns the desired latent weight.

\[
m_{x,q}
=\frac{E_P[\mathbf 1\{X=x\}Y\ell_q(V)]}
       {E_P[\mathbf 1\{X=x\}\ell_q(V)]}
\]

This observable ratio computes exactly the same localized causal mean.

Error independence supplies inversion. Exchangeability and consistency replace the realized outcome by its causal mean in the numerator.

Thus noisy doses recover the example’s weighted bump height. The observable weight may be signed; its Gaussian average is nonnegative.

@informal prop:identification: Under our model with \(\beta\in(0,1]\), \(\kappa\in[0,2]\), and known \(\sigma\in[0,1/4]\), the distribution of \((X,W,Y)\) uniquely determines \(\theta(P)\), including when latent-dose density vanishes at the target.

---

## Support and bias bounds

The density envelopes turn each candidate weight into bounds that hold across the model.

\(I_\kappa(q)=\int_{-1/2}^{1/2}|t|^\kappa q(t)\,dt,\qquad b_q(K)=p_{\min}c_{\mathrm{lo}}I_\kappa(q),\qquad 0<I_\kappa(q)<\infty.\)

The moment \(I_\kappa(q)\) measures weighted dose support. The quantity \(b_q\) bounds the observable stratum denominator from below.

Define \(I_{\kappa+\beta}(q)\) by replacing \(\kappa\) with \(\kappa+\beta\) in the integral.

\(B_q(K)=\frac{c_{\mathrm{hi}}}{c_{\mathrm{lo}}}\,\frac{I_{\kappa+\beta}(q)}{I_\kappa(q)}.\)

The bias bound \(B_q\) measures weighted distance from the target on the response-smoothness scale:

\(|m_{x,q}-\mu_x(a_0)|\le B_q(K).\)

Scarcity enters through weighted support; smoothness enters through the higher moment. Positive density at the exact target is unnecessary.

---

## Error certificate

Inverse weighting creates variability. Its second-moment bound is

\(V_q^{(16)}:=16\int_{-1/2}^{1/2}|t|^\kappa\left(\int_{\mathbb R}\ell_q(t+\sigma z)^2\frac{e^{-z^2/2}}{\sqrt{2\pi}}\,dz\right)dt.\)

The reference quantity \(V_q^{(16)}\) uses factor \(16\). The public moment is \(V_q(K)=\frac{c_{\mathrm{hi}}}{16}V_q^{(16)}\).

\(A_q(K)=B_q(K)+\frac{12}{b_q(K)}\sqrt{\frac{V_q(K)}{n}}+2\sqrt{\frac{3}{n}}.\)

The score \(A_q\) adds three errors:

- Localization bias, \(B_q\).
- Sampling error in weighted moments, amplified by division by \(b_q\).
- Sampling error in population stratum shares.

For \(n\ge3\), \(A_q\) bounds expected absolute error of the stabilized weight-specific estimator \(\widehat\theta_q\).

The choice of weight must control the whole ratio error, including scarce denominators.

---

## Fourier inversion

Let \(h\) be the localization width. Use \(q_h^{\mathrm F}(t)=Q(t/h)\), where \(Q(u)=(\sin u/u)^6\) away from zero and \(Q(0)=1\).

The Fourier transform of \(Q\) has bounded support. Scaling by \(h\) therefore confines the frequencies of \(q_h^{\mathrm F}\) to \(|\omega|\le C/h\): smaller localization widths require higher frequencies.

\[
\ell_h^{\mathrm F}(v)
=\mathcal F^{-1}\!\left[
\widehat q_h^{\mathrm F}(\omega)e^{\sigma^2\omega^2/2}
\right](v),\qquad v\in\mathbb R.
\]

Here \(\omega\) is frequency, \(\widehat q_h^{\mathrm F}\) is the Fourier transform, and \(\mathcal F^{-1}\) reconstructs the observable weight.

Gaussian averaging attenuates high frequencies. The exponential multiplier exactly reverses that attenuation.

\[
\mathfrak s_{n,\sigma}(h)
:=\sqrt{\frac{h^{-\kappa-1}(1+\sigma/h)^{10}
                         e^{36(\sigma/h)^2}}{n}},
\]

The quantity \(\mathfrak s_{n,\sigma}(h)\) bounds the complete stochastic ratio error up to a fixed constant.

Balancing it against bias \(h^\beta\) gives the direct and intermediate widths. Because inversion reaches frequencies of order \(1/h\), the Gaussian multiplier contributes the displayed \(e^{C(\sigma/h)^2}\) penalty; below the measurement-error scale, narrower localization is exponentially costly.

---

## Polynomial localization

Known support permits a weight that localizes on the latent interval and has a polynomial extension.

For a positive odd index \(m\), use

\[
q_m^{\mathrm M}(t)=
\begin{cases}
\displaystyle
\left[\frac{\sin(m\arcsin(2t))}{2mt}\right]^6,
&t\ne0,\\[6pt]
1,&t=0.
\end{cases}
\]

On \([-1/2,1/2]\), this weight is nonnegative, equals one at the target, and concentrates on a width proportional to \(1/m\).

For odd \(m\), its extension to the real line is a polynomial of degree \(6(m-1)\).

Localization only needs to hold where true doses can occur. The observable inverse must still accept recorded doses anywhere on the real line.

How can a polynomial reverse Gaussian averaging?

---

## Polynomial inversion

Use the finite derivative correction

\[
\ell_m^{\mathrm M}(v)
=\sum_{j=0}^{3(m-1)}
\frac{(-\sigma^2/2)^j}{j!}
(q_m^{\mathrm M})^{(2j)}(v),
\qquad v\in\mathbb R,
\]

where \((2j)\) denotes derivative order.

- Gaussian averaging of a polynomial retains even derivatives with positive coefficients \((\sigma^2/2)^j/j!\).
- The inverse applies the same derivative operation with alternating signs.
- Composing the two operations cancels every nonzero derivative order.
- Derivatives above the polynomial degree vanish, so the calculation is finite.

Consequently,

\[
E_Z\!\left[\ell_m^{\mathrm M}(t+\sigma Z)\right]
=q_m^{\mathrm M}(t),\qquad t\in\mathbb R.
\]

This identity exactly removes measurement-error averaging. Its cost is growth in observable polynomial moments.

---

## Polynomial error balance

Write \(D_{\mathrm{pol},m}=6(m-1)\) for the polynomial degree.

\(V_{q_m^{\mathrm M}}\le C_0^{D_{\mathrm{pol},m}}(1+D_{\mathrm{pol},m}\sigma^2)^{D_{\mathrm{pol},m}}\),

The observable moment cost grows with polynomial degree and Gaussian moments. Increasing \(m\) sharpens localization, but also makes this inverse weight more variable.

Choose an available odd \(m\) proportional to a sufficiently small fixed fraction of \(L_n/\log(e+\sigma^2L_n)\).

\(\underbrace{B_{q_m^{\mathrm M}}}_{\text{bias}}\le C_1m^{-\beta},\qquad \underbrace{b_{q_m^{\mathrm M}}^{-1}}_{\text{scarce denominator}}\le C_2m^{\kappa+1}\),

and the moment bound makes the **complete ratio error** obey

\(\frac{12}{b_{q_m^{\mathrm M}}}\sqrt{\frac{V_{q_m^{\mathrm M}}}{n}}\le C_3m^{-\beta}\).

Thus \(A_{q_m^{\mathrm M}}\le C_{\mathrm{poly}}m^{-\beta}\) for a fixed \(C_{\mathrm{poly}}\). The selected width \(1/m\) has the compact-support branch’s order.

---

## Observable estimator

The finite dictionary \(\mathcal D_{n,\sigma}\) contains Fourier weights at dyadic widths, polynomial weights at selected odd indices, and the constant weight.

\(\widehat q=\operatorname*{arg\,min}_{q\in\mathcal D_{n,\sigma}} A_q(K)\),

with a fixed rule for ties. Selection uses only \(n,\sigma,K,\beta,\kappa\) and the known weight formulas.

Split observations into three blocks \(\mathcal I_0,\mathcal I_1,\mathcal I_2\), used respectively for stratum frequencies \(\widehat p_x\), weighted denominators \(\widehat D_x(q)\), and weighted outcome numerators \(\widehat M_x(q)\).

\(\widehat\mu_x(q)=\Pi_{[0,1]}\left(\frac{\widehat M_x(q)}{\max\{\widehat D_x(q),b_q(K)/2\}}\right),\qquad \Pi_{[0,1]}(u)=\min\{1,\max\{0,u\}\}.\)

The formula estimates the stratum mean: flooring stabilizes division, and clipping keeps the result in its known range.

Aggregate as \(\widehat\theta=\sum_x\widehat p_x\widehat\mu_x(\widehat q)\); an empty block returns \(1/2\).

@informal thm:observable-upper: For fixed \(K\), \(\beta\in(0,1]\), and \(\kappa\in[0,2]\), the selected estimator has expected absolute error at most \(C\rho_{n,\sigma}\), uniformly over \(\sigma\in[0,1/4]\) for sufficiently large \(n\).

---

## Honest confidence interval

The same selected error certificate supplies an interval radius.

For any noncoverage level \(\alpha\in(0,1)\), when every block is nonempty,
\(C_{n,\sigma}=[\widehat\theta-A_{\widehat q}(K)/\alpha,\widehat\theta+A_{\widehat q}(K)/\alpha]\cap[0,1]\). When some block is empty, \(C_{n,\sigma}=[0,1]\).

The interval centers on the estimate, uses radius \(A_{\widehat q}(K)/\alpha\), and respects the target range.

With nonempty blocks, expected absolute error is at most \(A_{\widehat q}(K)\). Markov’s inequality bounds noncoverage by \(\alpha\).

An empty block triggers the full target range.

@informal thm:finite-honesty: For every \(\alpha\in(0,1)\), coverage is at least \(1-\alpha\) for every \(n\ge0\); expected length is at most \(C\rho_{n,\sigma}\), uniformly over \(\sigma\in[0,1/4]\) for sufficiently large \(n\).

---

## Direct-regime lower bound

Return to the example’s equal shares and common density \(g=g_x\). Compare Bernoulli laws with opposite response changes:

\(\mu_\star(a)=\frac12,\qquad \mu_\pm(a_0+t)=\frac12\pm\delta(t).\)

The reference law \(P_\star\) is flat; \(P_+\) and \(P_-\) use the original bump. All three share assignment and measurement error.

Their targets differ by \(2\varepsilon h_0^\beta\).

Let \(Q_\pm,Q_\star\) be their single-record observed laws. Chi-squared divergence measures their statistical discrepancy:

\[
\chi^2(Q_\pm,Q_\star)
\le4\int_{\mathbb R}g(t)\delta(t)^2\,dt.
\]

Gaussian recording cannot increase this bound; at zero error it is an equality.

- Only a neighborhood with probability of order \(h_0^{\kappa+1}\) changes.
- The squared response change has order \(\varepsilon^2h_0^{2\beta}\).
- Their product, multiplied by \(n\), stays proportional to \(\varepsilon^2\), because \(nh_0^d=1\).

For any prescribed \(\tau>0\), the calibrated construction chooses \(\varepsilon\) and a sufficiently large sample threshold so complete-sample total variation is at most \(\tau\). The direct-regime target change is therefore hard to detect even with exact doses.

---

## Filtered Jacobi construction

In the inverse regimes, a wider response change needs positive and negative offsets that disappear under Gaussian averaging.

Use **Jacobi polynomials**: polynomials orthogonal to all lower-degree polynomials under a specified interval weight. Write \(\mathsf J_j^{(a,b)}\) for degree \(j\), and \(H_j^{a,b}\) for its squared norm, which normalizes each summand.

For integer construction degree \(m\ge4\), let \(\eta\) be a smooth filter supported inside \((1,2)\). One filtered sum is

\[
b=\frac{\kappa-1}{2},\qquad
K_m(z)=\sum_{j\ge0}\eta(j/m)
\frac{\mathsf J_j^{(r,b)}(-1)\mathsf J_j^{(r,b)}(z)}
{H_j^{r,b}}.
\]

Because \(\eta(j/m)\) vanishes outside \(1<j/m<2\), this combines only degrees between \(m\) and \(2m\); smoothness means the retained coefficients vary through the smooth filter \(\eta\). The companion \(\widetilde K_m\) uses the symmetric Jacobi weight and anchor zero.

\[
\widetilde K_m(u)=\sum_{j\ge0}\eta(j/m)
\frac{\mathsf J_j^{(r,r)}(0)\mathsf J_j^{(r,r)}(u)}
{H_j^{r,r}}.
\]

\[
\psi_m(u)=
\begin{cases}
(1-u^2)^r K_m(2u^2-1)/K_m(-1),
& |u|\le1,\ \kappa>0,\\
(1-u^2)^r\widetilde K_m(u)/\widetilde K_m(0),
& |u|\le1,\ \kappa=0,\\
0,& |u|>1.
\end{cases}
\]

Here \(r=4\) tapers the boundary. The denominators are positive sums of squared polynomial values, so normalization preserves \(\psi_m(0)=1\).

---

## Why low moments cancel

- For \(\kappa>0\), choose Jacobi weight \((1-z)^4(1+z)^{(\kappa-1)/2}\). The substitution \(z=2u^2-1\) converts even design-weighted moments into lower-degree polynomial integrals.
- Removing all degrees at or below \(m\) makes those integrals zero by orthogonality. Odd moments vanish by symmetry.
- For \(\kappa=0\), the symmetric Jacobi weight is directly \((1-u^2)^4\); the same degree removal cancels low-order moments.

Thus, for a fixed \(c>0\),

\[
\int_{-1}^{1}|u|^\kappa u^j\psi_m(u)\,du=0
\quad\text{for every integer }0\le j<cm.
\]

The operation enforcing cancellation is the removal of low polynomial degrees.

---

## Localization and smoothness

Degree removal alone does not guarantee a localized, smooth response change. The smooth combination of retained degrees supplies that control.

Petrushev and Xu (2005) supply arbitrarily fast decay of the filtered kernel away from its anchor in angular distance. After our normalization and tapering, this gives decay bounded by a fixed constant times \((1+m|u|)^{-(\kappa+2)}\).

Consequently, the design-weighted mass is concentrated on width \(1/m\):

\[
\int_{-1}^{1}|u|^\kappa|\psi_m(u)|\,du
\le Cm^{-\kappa-1},
\qquad
\int_{-1}^{1}|u|^\kappa\psi_m(u)^2\,du
\le Cm^{-\kappa-1},
\]

Here \(C\) is a fixed positive bound constant. These integrals control the absolute and squared mass of the signed response change.

Kyriazis et al. (2008) supply local kernel difference control. Together with tapering, it yields \(|\psi_m'(u)|\le Cm\); the zero extension is continuously differentiable.

Set support radius \(\ell\), width \(h=\ell/m\), and \(\delta(t)=\varepsilon h^\beta\psi_m(t/\ell)\).

This perturbation retains peak \(\varepsilon h^\beta\) and vanishes outside \([-\ell,\ell]\).

For dose differences at most \(h\), derivative control gives the required smoothness bound; for larger differences, bounded amplitude does. A sufficiently small fixed \(\varepsilon\) keeps both response alternatives in our model.

Localization and derivative estimates are imported; the design-matched transformation and orthogonality enforce our moment cancellations.

---

## Hidden response changes

For the common design, scaling the constructed function gives  
\(\int_{\mathbb R}t^j g_x(t)\delta(t)\,dt=0\) for \(0\le j<J\), where \(J=\lfloor c_pm\rfloor\) and \(c_p>0\) is fixed.

In the Gaussian comparison, each series term depends on a squared design-weighted moment. Cancellation removes the first \(J\) terms:

\(\chi^2(Q_\pm,Q_\star)\le C\sigma^{-\kappa-1}h^{2\beta+2\kappa+2}\sum_{j=J}^{\infty}\frac{(\ell^2/\sigma^2)^j}{j!}.\)

Here \(Q_\pm,Q_\star\) are the single-record observed laws. The constants \(\varepsilon,c_p,C\), admissible tuning, and sample threshold are supplied by the calibrated witness theorem rather than chosen arbitrarily. The remaining factorial tail can be small despite a nonzero target peak.

| Regime | Support and cancellation choice |
|---|---|
| Intermediate | Choose \(\ell\) proportional to \(\sigma\sqrt m\) and \(m\) proportional to \(\log(e+n\sigma^d)\). Then \(h=\ell/m\) has the intermediate width’s order. |
| Compact support | Keep \(\ell\) fixed and choose \(m\) proportional to \(L_n/\log(e+\sigma^2L_n)\). Then \(h\) has the compact-support width’s order. |

For any \(\tau>0\), and all sufficiently large \(n\), these calibrated choices give \(c\rho_{n,\sigma}\le|\theta(P_+)-\theta(P_-)|,\qquad \operatorname{TV}(Q_{P_+}^n,Q_{P_-}^n)\le\tau\).

Total variation, \(\operatorname{TV}\), measures complete-sample distinguishability.

An estimator cannot reliably resolve both separated targets. An honest connected interval must often cover both, forcing length at their separation scale.

---

## Open questions

We prove exact-arithmetic certificates and asymptotic orders. A reproducible numerical study of selected weights, score radii, and inversion stability is deferred; the current results do not supply empirical informativeness thresholds.

- Can localization adapt to unknown smoothness and dose scarcity while retaining honest coverage?
- How much replicate or calibration information is needed when measurement-error scale is unknown?
- How do richer confounders and simultaneous reporting across doses change attainable precision?
- How can validation measurements assess latent support and density envelopes and incorporate their uncertainty?

---

## Takeaways

- Dose scarcity and measurement precision jointly determine three optimal orders for absolute error and honest interval length.
- Positive latent localization controls bias; observable inverse weights recover its moments. Known support permits finite polynomial inversion when Fourier inversion becomes too costly.
- A bound on the complete ratio error selects the weight and supplies finite-sample \((1-\alpha)\) coverage for every \(\alpha\in(0,1)\). Orthogonal polynomial constructions hide separated causal means, establishing matching lower bounds for the uniform frontier when \(\alpha\in(0,1/2)\).

---

## Appendix: Uniform risk and length frontier

This statement gives matching estimation and honest-length orders, including transition neighborhoods and the fixed-positive-error consequence.

@formal thm:uniform-frontier

---

## Appendix: Observable upper risk bound

This statement establishes the estimator’s uniform upper bound and the Fourier and polynomial comparison guarantees.

@formal thm:observable-upper

---

## Appendix: Finite-sample honesty and length

This statement separates coverage at every sample size from the uniform sufficiently-large-sample length bound.

@formal thm:finite-honesty

---

## Appendix: Observed-law lower-bound witnesses

Under calibrated \(K\), fixed \(\beta\in(0,1]\), \(\kappa\in[0,2]\), any \(\tau>0\), and sufficiently large \(n\), this statement chooses admissible constants and tuning and constructs model-valid alternatives separated at the optimal scale with complete-sample TV at most \(\tau\).

@formal thm:observed-lower
