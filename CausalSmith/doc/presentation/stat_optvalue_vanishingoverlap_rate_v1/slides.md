# Estimating the Value of Optimal Treatment

We establish how accurately we can estimate the outcome from choosing the better treatment in each covariate group, even when some treatments are rarely observed.

---

## Research question

A practitioner wants the population value of choosing the better treatment separately in each covariate cell.

\[
\Psi(\mathbb P)
=\sum_{x\in[d]}p_x\max_{a\in\{0,1\}}\mu_{ax}.
\]

Here \(\mathbb P\) is the population law, \(d\) is the number of cells, \(p_x\) is cell \(x\)’s population share, and \(\mu_{ax}\) is its outcome mean under treatment \(a\).

- Plug-in estimation replaces shares and outcome means by sample averages.
- Rare treatments make those averages unstable.
- Taking their maximum selects upward noise near treatment ties.

Archive (2026), Theorem 3, establishes the fixed-overlap risk order \(\min\{1,d/[n\log(ed)]\}\), with constants depending on overlap.

With \(n\) observations and known minimum treatment probability \(\epsilon\), how does attainable precision deteriorate as \(\epsilon\) shrinks?

---

## Key idea

Estimate a polynomial approximation to the maximum, rather than taking the maximum of noisy estimates.

- Pilot counts locate each cell’s probabilities.
- A polynomial approximates its value across treatment ties.
- Independent counts estimate polynomial terms without power-estimation bias.
- Each arm’s denominator sensitivity is paired with that arm’s count fluctuations.

@informal thm:matched-frontier: With \(n\ge1\) independent categorical observations, \(d\ge2\), binary treatment and outcome, and known \(0<\epsilon\le1/2\), minimax squared risk is between universal multiples of \(\min\{1,d/[n\epsilon\log(ed)]\}\).

A deterministic estimator attains this scale uniformly over unknown shares, propensities, and treatment ties.

---

## Example

Consider equal-sized cells with treatment means around a tie:

\[
p_x=\frac1d,
\qquad
\pi_x=\epsilon,
\qquad
\mu_{0x}=\frac12,
\qquad
\mu_{1x}=\frac12+\mathfrak a T_x^{\mathrm{de}}.
\]

The treatment-one probability \(\pi_x\) equals the overlap floor. The perturbation \(T_x^{\mathrm{de}}\) lies in \([-1,1]\); amplitude \(0<\mathfrak a\le1/2\) keeps outcome means in \([0,1]\).

\[
\Psi_{\mathrm{de}}(\mathbf T^{\mathrm{de}})
=\frac12+\frac{\mathfrak a}{2d}
 \sum_{x\in[d]}(|T_x^{\mathrm{de}}|+T_x^{\mathrm{de}}),
\]

This computes the family’s value; \(\mathbf T^{\mathrm{de}}\) collects its cell perturbations.

Negative perturbations give no gain over control. Positive perturbations give linear gain. At zero, the preferred treatment changes: the value has a corner.

How can we estimate that gain without interpreting noise as improvement?

---

## Model

Observe \(n\ge1\) independent units \(O_i=(X_i,A_i,Y_i)\) with common law \(\mathbb P\).

Covariate \(X_i\) has \(d\ge2\) categories; treatment \(A_i\) and outcome \(Y_i\) are binary.

\[
q_{ay,x}:=\mathbb P(X=x,A=a,Y=y),
\qquad
p_x:=\sum_{a\in\{0,1\}}\sum_{y\in\{0,1\}}q_{ay,x},
\]

An atom probability \(q_{ay,x}\) records one cell, treatment, and outcome combination. Summing its four atoms gives the cell share.

The propensity is \(\pi_x=(q_{10,x}+q_{11,x})/p_x\), and the arm mean is \(\mu_{ax}=q_{a1,x}/(q_{a0,x}+q_{a1,x})\).

For every occupied cell, require

\[
\epsilon\le\pi_x\le1-\epsilon.
\]

The known floor \(0<\epsilon\le1/2\) guarantees observations from both arms. Write \(\mathcal D_{d,\epsilon}^{\mathrm{obs}}\) for these laws.

Our example places treatment one exactly at the floor.

---

## Causal interpretation

Let \(Y(a)\) be the potential outcome under treatment \(a\), and \(P\) the full-data law.

- **Consistency:** \(Y=Y(A)\); the observed outcome belongs to the treatment received.
- **Conditional exchangeability:** \(Y(a)\perp A\mid X\); within a recorded cell, treatment carries no further information about either potential outcome.
- **Overlap:** both treatments occur in every occupied cell.

\[
V^\star(P)
=
\sum_{x\in[d]} P(X=x)
\max_{a\in\{0,1\}}
\mathbb E_P[Y(a)\mid X=x]
=
\Psi\{\operatorname{Obs}(P)\},
\]

The causal optimal value \(V^\star(P)\) averages the causally better treatment’s mean. The observed marginal of \((X,A,Y)\) is \(\operatorname{Obs}(P)\).

These conditions identify the causal value from the observed target. Every admissible observed law has such a causal completion, so the same risk characterization applies.

---

## Main result

Minimax risk \(\mathfrak R_{n,d,\epsilon}\) is the smallest worst-case mean squared error over all estimators. Write \(L_d=\log(ed)\).

Under independent sampling and the overlap restriction, for every \(n\ge1\), \(d\ge2\), and \(0<\epsilon\le1/2\),

\[
c_\star\min\left\{1,\frac{d}{n\epsilon L_d}\right\}
\le
\mathfrak R_{n,d,\epsilon}
\le
\sup_{\mathbb P\in\mathcal D_{d,\epsilon}^{\mathrm{obs}}}
E_{\mathbb P}\!\left[
\bigl(\widehat V_{n,d,\epsilon}^{\mathrm{AF}}-\Psi(\mathbb P)\bigr)^2
\right]
\le
C_\star\min\left\{1,\frac{d}{n\epsilon L_d}\right\}.
\]

The deterministic estimator \(\widehat V_{n,d,\epsilon}^{\mathrm{AF}}\) attains the scale. Positive constants \(c_\star,C_\star\) are universal.

- \(n\epsilon\) is the expected rare-arm count when its propensity equals the floor throughout the population.
- Risk has constant order when \(n\epsilon\le d/L_d\); above that threshold, its scale is \(d/(n\epsilon L_d)\).
- In our example, the guarantee holds for every perturbation vector, including ties in every cell.

---

## Cell contribution

Collect the four atom probabilities as \(q_x=(q_{00,x},q_{01,x},q_{10,x},q_{11,x})\).

For a nonnegative vector \(u\), let \(s_a(u)=u_{a0}+u_{a1}\) be arm mass, \(s(u)=s_0(u)+s_1(u)\) total mass, and \(D_a(u)=\max\{s_a(u),\epsilon s(u)\}\) a protected denominator.

\[
F_\epsilon(u)
=
\begin{cases}
\displaystyle
\max_{a\in\{0,1\}}\frac{s(u)u_{a1}}{D_a(u)},&u\ne0,\\[6pt]
0,&u=0,
\end{cases}
\qquad u\in\mathbb R_+^4,
\]

This computes a weighted maximum while protecting nearly empty arm denominators.

At true probabilities, overlap makes protection inactive:

\[
F_\epsilon(q_x)=p_x\max_{a\in\{0,1\}}\mu_{ax}.
\]

Summing these cell contributions gives \(\Psi(\mathbb P)\). Protection also permits approximation at nearby vectors that need not satisfy overlap.

The sensitivity to changes within arm \(a\) is weighted by \(1+p_x/s_a(q_x)\): smaller arms have more sensitive ratios.

---

## Pilot localization

Sample splitting uses pilot observations to choose an approximation region and independent evaluation observations to estimate its polynomial.

In an auxiliary Poisson experiment, all pilot and evaluation atom counts are independent, each with mean \(mq_{ay,x}\). Set \(m=n/8\) and \(L=L_d\).

\[
c_{ay,x}=\frac{N'_{ay,x}}m,\qquad
h_{ay,x}
=
H_0\left\{\sqrt{\frac{c_{ay,x}L}{m}}+\frac Lm\right\},
\]

Pilot count \(N'_{ay,x}\) gives estimated mass \(c_{ay,x}\) and uncertainty radius \(h_{ay,x}\). The constant \(H_0\) is universal.

- The square-root term follows that atom’s count fluctuations.
- The additive term retains uncertainty when the count is zero.

Intersect each interval with the nonnegative line. Their product is rectangle \(Q_x\), with lower endpoints \(\ell_{ay,x}\), upper endpoints \(u_{ay,x}\), midpoint \(b_x\), and half-widths \(r_x\).

Successful localization means \(\mathcal G_x=\{q_x\in Q_x\}\).

In our example, treatment-one atoms have total mass \(\epsilon/d\): their smaller fluctuations enter their own localization widths.

---

## Polynomial smoothing

Jiao et al. (2015) supply the strategy of polynomial approximation followed by unbiased polynomial estimation.

Within \(Q_x\), express each coordinate using a cosine. Average nearby angles with nonnegative, normalized Jackson weights \(J_{K_n}\):

\[
P_{x,K_n}(b_x+r_x\odot\cos\theta)
=
\int_{[-\pi,\pi]^4}
F_\epsilon\!\left(b_x+r_x\odot\cos(\theta+\tau)\right)
\prod_{a,y\in\{0,1\}}J_{K_n}(\tau_{ay})\,d\tau,
\qquad \theta\in\mathbb R^4.
\]

Here \(\theta\) locates a point, \(\tau\) shifts its angles, and \(\odot\) means coordinatewise multiplication.

The weights contain only finitely many oscillation frequencies. After averaging, the function is a polynomial \(P_{x,K_n}\), with maximum coordinate degree \(D=2(K_n-1)\).

Their average angular displacement is at most \(C/K_n\); their average squared displacement is at most \(C/K_n^2\).

In our example, restricting this polynomial to the cell’s perturbation path smooths the gain across zero.

How do angular resolution and the pilot rectangle determine approximation error?

---

## Approximation balance

Let \(R_{a,x}=r_{a0,x}+r_{a1,x}\) be the total half-width within arm \(a\). On successful localization in an occupied cell,

\[
\begin{aligned}
|P_{x,K_n}(q_x)-F_\epsilon(q_x)|
\le64\sum_{a=0}^1
\left(1+\frac{p_x}{s_a(q_x)}\right)
\left\{
\frac{\sum_y\sqrt{(q_{ay,x}-\ell_{ay,x})(u_{ay,x}-q_{ay,x})}}{K_n}
+\frac{R_{a,x}}{K_n^2}
\right\}.
\end{aligned}
\]

This bounds the cell approximation error.

- **Sensitivity:** \(1+p_x/s_a(q_x)\) weights each arm separately.
- **Pilot uncertainty:** the square-root product measures distances to the interval’s two ends. It vanishes at an endpoint.
- **Resolution:** the first term receives \(1/K_n\); the remaining boundary error receives \(1/K_n^2\).

The square-root product is at most a constant times \(\sqrt{q_{ay,x}L/m}\). Pairing these fluctuations with their own arm sensitivities costs \(\sqrt{p_x/\epsilon}\).

Choose \(K_n=\max\{2,\lfloor\kappa L\rfloor\}\), with small universal \(\kappa>0\). Then

\[
\eta_x=
\sqrt{\frac{p_x}{m\epsilon L}}+\frac1{m\epsilon L},
\]

and approximation error is at most \(C\eta_x\). The first term comes from fluctuations; the second comes from boundary error.

---

## Polynomial estimation

Define \(D=2(K_n-1)\), the maximum degree in each coordinate.

Expand the polynomial around midpoint \(b_x\), using half-widths \(r_x\) to normalize coordinates:

\[
P_{x,K_n}(v)-F_\epsilon(b_x)
=
\sum_{\boldsymbol\alpha\in\{0,\ldots,D\}^4}
\beta_{x,\boldsymbol\alpha}
\prod_{a,y\in\{0,1\}}
\left(\frac{v_{ay}-b_{ay,x}}{r_{ay,x}}\right)^{\alpha_{ay}},
\qquad v\in Q_x.
\]

The four exponents \(\boldsymbol\alpha\) specify a term, and \(\beta_{x,\boldsymbol\alpha}\) is its coefficient.

Replace every centered power by a centered factorial statistic \(U_k\):

\[
Z_x
=
F_\epsilon(b_x)
+
\sum_{\boldsymbol\alpha\in\{0,\ldots,D\}^4}
\beta_{x,\boldsymbol\alpha}
\prod_{a,y\in\{0,1\}}
\frac{U_{\alpha_{ay}}(N_{ay,x};b_{ay,x})}
{r_{ay,x}^{\alpha_{ay}}}.
\]

Here \(N_{ay,x}\) are independent evaluation counts. The pilot chooses the coefficients and centers.

Conditional on the complete pilot array \(N'\),

\[
\mathbb E_{\mathrm{aux}}[Z_x\mid N']
=P_{x,K_n}(q_x),
\]

where \(\mathbb E_{\mathrm{aux}}\) averages the auxiliary experiment.

The remaining bias is approximation error. Why does replacing powers by factorials work?

---

## One cell through the estimator

For one cell in our example, the true atoms are

\[
q_{00,x}=q_{01,x}=\frac{1-\epsilon}{2d},
\qquad
q_{10,x}=\frac{\epsilon}{d}\left(\frac12-\mathfrak a T_x^{\mathrm{de}}\right),
\qquad
q_{11,x}=\frac{\epsilon}{d}\left(\frac12+\mathfrak a T_x^{\mathrm{de}}\right).
\]

These describe a line through the treatment tie.

Within the pilot rectangle, its true contribution is \(1/(2d)+\mathfrak a(|T_x^{\mathrm{de}}|+T_x^{\mathrm{de}})/(2d)\). The restriction of \(P_{x,K_n}\) approximates this localized gain curve across zero.

For count \(N\), center \(\zeta\), and degree \(k\),

\[
U_k(N;\zeta)
=
\sum_{t=0}^{k}\binom kt(-\zeta)^{k-t}\frac{(N)_t}{m^t},
\]

where \((N)_t=N(N-1)\cdots(N-t+1)\) counts ordered selections of distinct records.

A squared treated-success factor \(((q_{11,x}-b_{11,x})/r_{11,x})^2\) is estimated by \(U_2(N_{11,x};b_{11,x})/r_{11,x}^2\).

Here \(U_2(N;b)=N(N-1)/m^2-2bN/m+b^2\). Its expectation is \((q-b)^2\); using \(N^2\) would add count noise.

Applying this replacement to every term estimates the polynomial even at the exact tie, without first selecting a winning arm.

---

## Cell noise

Higher-degree terms reduce approximation bias but increase estimation noise.

Conditional on a successful pilot,

\[
\mathbb E_{\mathrm{aux}}
[(Z_x-F_\epsilon(b_x))^2\mid N']
\le
\left(\sum_{\boldsymbol\alpha}|\beta_{x,\boldsymbol\alpha}|\right)^2
e^{32D^2/L}
\quad\text{on }\mathcal G_x.
\]

The coefficient sum measures how much the polynomial can amplify count noise. The exponential factor bounds the second moments of factorial terms.

Measure cell variation using arm widths and sensitivities:

\[
R_{a,x}=r_{a0,x}+r_{a1,x},\qquad
w_{a,x}=1+\frac{s(b_x)}{D_a(b_x)},\qquad
S_x^{\mathrm{aw}}=2\sum_{a=0}^{1}w_{a,x}R_{a,x},
\]

Here \(w_{a,x}\) is arm sensitivity at the midpoint, and \(S_x^{\mathrm{aw}}\) bounds variation across the rectangle.

Small logarithmic degree bounds the preceding second moment by \(C_{\mathrm{fac}}d^{1/16}(S_x^{\mathrm{aw}})^2\), with universal \(C_{\mathrm{fac}}\).

Clip \(Z_x\) around \(F_\epsilon(b_x)\) with radius \(d^{1/4}S_x^{\mathrm{aw}}\), obtaining \(T_x\). Clipping controls excursions from bad pilots.

Can summing over \(d\) cells absorb the factor \(d^{1/16}\)?

---

## Summed variance

The squared clipping scale retains the cell’s population mass. Define \(\mathfrak a_x=p_xL/(m\epsilon)+L^2/(m^2\epsilon^2)\). Then

\[
\mathbb E_{\mathrm{aux}}(S_x^{\mathrm{aw}})^2
\le C_{\mathrm s}\mathfrak a_x.
\]

The constant \(C_{\mathrm s}\) is universal. Thus the quantity being summed is a bound on expected squared cell variation.

\[
\mathfrak r_{\mathrm{aux}}=\frac{d}{m\epsilon L},
\qquad
\mathfrak m_{\mathrm{sum}}
=\sum_x\mathfrak a_x
=\frac L{m\epsilon}+\frac{dL^2}{m^2\epsilon^2}.
\]

Here \(\mathfrak r_{\mathrm{aux}}\) is the target auxiliary risk scale.

**Population mass enters here:** \(\sum_xp_x=1\) makes the first term independent of \(d\).

**The active regime enters next:** \(n\epsilon\ge d/L\), or \(d\le8m\epsilon L\), gives \(\mathfrak m_{\mathrm{sum}}\le(L^2+8L^4)/(m\epsilon L)\).

Consequently,
\(d^{1/16}\mathfrak m_{\mathrm{sum}}/\mathfrak r_{\mathrm{aux}}\le d^{-15/16}(L^2+8L^4)\), which is uniformly bounded because \(L=\log(ed)\).

\[
d^{1/16}\sum_x\mathbb E_{\mathrm{aux}}(S_x^{\mathrm{aw}})^2
\le C_{\mathrm s}C_{\mathrm{var}}\mathfrak r_{\mathrm{aux}}.
\]

The universal constant \(C_{\mathrm{var}}\) absorbs that bounded ratio. This is the connection from cell noise to aggregate variance.

---

## Aggregate error

Independent cell statistics make mean squared error equal summed variances plus squared summed bias.

The variance calculation already absorbs polynomial growth. Three bias contributions remain:

- **Approximation:** total population mass gives \(\sum_x\sqrt{p_x}\le\sqrt d\).
- **Clipping:** cell bias is at most a constant times \(d^{-3/16}\mathbb E_{\mathrm{aux}}S_x^{\mathrm{aw}}\); squaring the sum uses the same mass calculation.
- **Failed pilots:** their error moments decay rapidly with \(L\), retaining the cell scales \(\mathfrak a_x\).

For the approximation scales,

\[
\sum_x\eta_x\le\sqrt{\mathfrak r_{\mathrm{aux}}}+\mathfrak r_{\mathrm{aux}},
\qquad
\sum_x\eta_x^2\le\left(\sum_x\eta_x\right)^2
\le18\mathfrak r_{\mathrm{aux}}.
\]

This bounds summed approximation bias and its squared cell contributions; the active regime gives \(\mathfrak r_{\mathrm{aux}}\le8\).

Together,

\[
\mathbb E_{\mathrm{aux}}
\left(\sum_xT_x-\Psi(\mathbb P)\right)^2
\le C_{\mathrm P}\frac{d}{m\epsilon L}.
\]

The universal constant \(C_{\mathrm P}\) collects the error terms. Since \(m=n/8\), this is the required upper-bound scale.

---

## Deterministic estimator

Turn the auxiliary construction into a statistic using exactly \(n\) observations.

Draw \(\mathsf M\sim\operatorname{Pois}(n/4)\). When \(\mathsf M\le n\), use the first \(\mathsf M\) records and fair pilot/evaluation allocations.

\[
\widetilde V
=
\begin{cases}
\displaystyle\Pi_{[0,1]}\left(\sum_{x\in[d]}T_x\right),
&\mathsf M\le n,\\[4pt]
0,&\mathsf M>n,
\end{cases}
\qquad
\widehat V_{n,d,\epsilon}^{\mathrm{AF}}
=
E[\widetilde V\mid O_1,\ldots,O_n].
\]

Projection \(\Pi_{[0,1]}\) keeps the estimate in the value range. Conditional averaging integrates the auxiliary count and allocations, producing a deterministic function of the observations.

Projection and averaging cannot increase squared-error risk. The exponentially unlikely overflow contributes at most the required scale.

Under our calibration, use this construction when \(n\epsilon\ge d/L\). Otherwise return \(1/2\), whose squared error is at most \(1/4\).

Why can no estimator uniformly improve the risk order?

---

## Hard alternatives near ties

Return to the equal-share example. Draw cell perturbations independently from either of two symmetric distributions \(\eta_0,\eta_1\) on \([-1,1]\).

Choose them to match moments through degree \(K_{\mathrm{de}}\), while their expected absolute perturbations differ by at least \(1/(50K_{\mathrm{de}})\).

Here \(K_{\mathrm{de}}\) is the tie family’s matched degree—the degree denoted \(K_{\mathrm{abs}}\) in the scalar approximation argument.

Under \(z=\sin2\omega\), degree-\(K_{\mathrm{de}}\) polynomials use only low angular frequencies. A signed angular average cancels these frequencies, while the corner retains higher ones:

\[
|\sin2\omega|
=\frac2\pi-\frac4\pi
 \sum_{\ell=1}^\infty\frac{\cos(4\ell\omega)}{4\ell^2-1}.
\]

This expands the absolute-value gain. Its nonconstant coefficients share one sign; the surviving block contains \(K_{\mathrm{de}}\) terms of size proportional to \(K_{\mathrm{de}}^{-2}\).

Approximation–moment duality, as in Wu and Yang (2019), converts this inverse-degree separation into symmetric moment-matched distributions.

Symmetry removes the signed perturbation from average value. Their value centers differ by at least \(\mathfrak a/(100K_{\mathrm{de}})\).

---

## Sparse intensity family

Tie perturbations have bounded amplitude. A second family allows a wider range of cell intensities \(z_x\in[0,M]\), with \(M\ge2\).

Before normalization, set

\[
\widetilde q_{11,x}=\frac{\epsilon(1-\epsilon)z_x}{d},
\qquad
\widetilde q_{10,x}=\frac{\epsilon(1-\epsilon)}{d},
\qquad
\widetilde q_{00,x}=\widetilde q_{01,x}
=\frac{(1-\epsilon)^2+\epsilon^2z_x}{2d}.
\]

These are cell–arm–outcome masses. Divide by their total \(S(\mathbf z)=1-\epsilon+(\epsilon/d)\sum_xz_x\) to obtain law \(\mathbb P_{\mathbf z}^{\mathrm{sp}}\).

Control mean is \(1/2\), treatment mean is \(z_x/(1+z_x)\), and overlap holds. Treatments tie at intensity one.

Define weighted gain \(\phi_\epsilon(z)=(1-\epsilon+\epsilon z)\max\{z-1,0\}/(1+z)\). Then

\[
\Psi(\mathbb P_{\mathbf z}^{\mathrm{sp}})
=\frac12+\frac{1}{2dS(\mathbf z)}
\sum_{x\in[d]}\phi_\epsilon(z_x).
\]

This computes baseline plus normalized average gain.

We need two intensity distributions with matching moments, different gains, and common mean one so that the normalizer centers at one.

---

## Moment cancellation

Map angle to intensity by \(z_M(\omega)=M(1+\cos\omega)/2\). The angles \(\pm\vartheta_M\), where \(\vartheta_M=\arccos(2/M-1)\), map to the treatment tie \(z=1\).

Use a nonnegative periodic Jackson weight \(\mathcal J_N\), normalized to integrate to one against \(du/(2\pi)\).

- Its frequencies satisfy \(|j|\le2N-2\).
- Its angular spread is at most a constant times \(1/N\).
- Multiplying by \(\cos(4Nu)\) shifts its frequencies to absolute values between \(2N+2\) and \(6N-2\).

Set \(N=A_0K\), with sufficiently large universal integer \(A_0\), and \(k_N(u)=\mathcal J_N(u)\cos(4Nu)\).

\[
H_{K,M}(\omega)
=k_N(\omega-\vartheta_M)+k_N(\omega+\vartheta_M),
\qquad
W_{K,M}
=\int_{-\pi}^{\pi}
\{1+z_M(\omega)\}|H_{K,M}(\omega)|\,\frac{d\omega}{2\pi}.
\]

The signed weight \(H_{K,M}\) places oscillations at both ties. \(W_{K,M}\) is its absolute mass weighted by \(1+z\).

A degree-\(K\) polynomial in \(z_M(\omega)\) has frequencies at most \(K\). The shifted weights have none there, so every polynomial moment through \(K\) cancels.

Why does the gain survive this cancellation?

---

## Gain at the corner

Near a tie angle, the intensity map has slope magnitude \(\sqrt{M-1}\).

Angular width \(1/N\) therefore becomes intensity width proportional to \(\sqrt M/K\). Across that width, the gain changes slope by \(1/2\).

To see why signed oscillations retain this response, let \(G_N\) be the twice-integrated weight: \(G_N''=k_N\).

- At its center, \(|G_N(0)|\) is between universal multiples of \(1/N\).
- Its absolute integral is at most \(C/N^2\).
- Integration by parts pairs the gain’s slope change with \(G_N(0)\); smooth curvature is paired with the smaller integral.

The corner contribution has scale \(\sqrt M/N\); the smooth remainder is at most \(CM/N^2\). For \(2\le M\le K^2\), large \(A_0\) makes the corner dominate.

Localization also bounds \(W_{K,M}\) above by a universal constant. Hence

\[
\left|
\int_{-\pi}^{\pi}
\phi_\epsilon\{z_M(\omega)\}
\frac{H_{K,M}(\omega)}{W_{K,M}}\,
\frac{d\omega}{2\pi}
\right|
\ge c_{\mathrm p}\frac{\sqrt M}{K}.
\]

This is the gain contrast retained after normalization; \(c_{\mathrm p}>0\) is universal.

---

## Mean-one alternatives

Map the positive and negative parts of \(H_{K,M}/W_{K,M}\) into intensity space, obtaining nonnegative measures \(\sigma_+,\sigma_-\).

Moment cancellation gives them equal mass \(t\) and equal first moment \(u\).

The definition of \(W_{K,M}\) gives

\[
\int(1+z)\,d(\sigma_++\sigma_-)=1.
\]

This computes their combined weighted mass. Equal masses and first moments imply \(2t+2u=1\), hence \(t+u=1/2\).

Add the same atom at \(z_0=(1-u)/(1-t)\):

\[
\nu_0=\sigma_-+(1-t)\delta_{z_0},
\qquad
\nu_1=\sigma_++(1-t)\delta_{z_0}.
\]

Here \(\delta_{z_0}\) is a unit point mass. Both distributions now have total mass one and mean one. The completion point satisfies \(1/2\le z_0\le2\le M\).

The common atom changes neither moment differences nor the gain contrast.

@informal thm:weighted-separation-and-frontier: For integer \(K\ge2\), \(2\le M\le K^2\), and \(0\le\epsilon\le1/2\), two probability laws on \([0,M]\) can share mean one and moments through \(K\), yet differ in expected weighted gain by at least \(c\sqrt M/K\), with universal \(c>0\).

---

## Full likelihood comparison

A gain gap implies statistical difficulty only if the observations cannot reliably distinguish the alternatives.

Fix an inflation factor \(B>2\). In the intensity family, observe all four independent Poisson counts with means \(Bn\widetilde q_{ay,x}(z)\), including controls.

Let \(L_z\) be their likelihood ratio relative to \(z_\star=M/2\), and \(E_{z_\star}\) reference expectation. Then

\[
E_{z_\star}[L_zL_w]
=\exp\!\left\{\alpha(z-z_\star)(w-z_\star)\right\},
\]

where \(w\) is another intensity and \(\alpha\le2Bn\epsilon/(dM)\) measures the full likelihood’s sensitivity.

Matching moments through \(K_{\mathrm{sp}}\), the intensity family’s degree, cancels the exponential expansion through that degree. Its remaining terms are small when \(Bn\epsilon M/(2d)\) is at most a small multiple of \(K_{\mathrm{sp}}\).

The tie family has the parallel identity

\[
E_0[L_{\mathrm{de},z}L_{\mathrm{de},w}]
=\exp\{4\lambda_{\mathrm{tr}}\mathfrak a^2zw\},
\qquad z,w\in[-1,1].
\]

Here \(E_0\) is expectation at the tie and \(\lambda_{\mathrm{tr}}=Bn\epsilon/d\) is treated count intensity per cell.

Degrees proportional to \(L_d\) make both complete count mixtures close after combining all cells. Randomly ordering the Poisson records transfers this difficulty to their first \(n\) observations; large fixed \(B\) controls shortage.

---

## Lower-bound coverage

Choose logarithmic matched degrees \(K_{\mathrm{sp}}\asymp K_{\mathrm{de}}\asymp L_d\). Write \(x_{\mathrm{splice}}=d/(Bn\epsilon)\).

Choose the tie amplitude and intensity support by

\[
\mathfrak a_{\mathrm{de}}^2
=\min\left\{\frac14,
\frac{\eta_{\mathrm{de}}dK_{\mathrm{de}}}{Bn\epsilon}\right\}.
\]

\[
M_{\mathrm{sp}}
=\min\left\{
K_{\mathrm{sp}}^2,
\frac{\eta_{\mathrm{sp}}dK_{\mathrm{sp}}}{Bn\epsilon}
\right\}.
\]

The small universal constants \(\eta_{\mathrm{de}},\eta_{\mathrm{sp}}>0\) keep the likelihood mixtures close.

| Family | Range supplying coverage | Squared value separation: at least a universal multiple of |
|---|---|---|
| Perturbations around ties | \(\eta_{\mathrm{sp}}x_{\mathrm{splice}}K_{\mathrm{sp}}<2\) | \(\min\{1/(4K_{\mathrm{de}}^2),\eta_{\mathrm{de}}x_{\mathrm{splice}}/K_{\mathrm{de}}\}\) |
| Cell intensities | \(\eta_{\mathrm{sp}}x_{\mathrm{splice}}K_{\mathrm{sp}}\ge2\), so \(M_{\mathrm{sp}}\ge2\) | \(\min\{1,\eta_{\mathrm{sp}}x_{\mathrm{splice}}/K_{\mathrm{sp}}\}\) |
| Two rare-arm laws | Bounded \(d\) | \(\min\{1,1/(n\epsilon)\}\) |

For sufficiently many cells, independent draws concentrate values around separated centers. Common mean one centers the intensity normalizer at one.

An estimator accurate below these gaps would distinguish close observation mixtures. Degree comparison makes the first two rows cover \(\min\{1,d/(n\epsilon L_d)\}\); the last supplies bounded alphabets.

---

## Takeaways

- **Precision:** optimal worst-case squared risk has order \(\min\{1,d/[n\epsilon\log(ed)]\}\), uniformly over unknown shares, propensities, and treatment ties.
- **Estimation:** local polynomials handle the maximum’s corner; factorial statistics estimate their terms without bias. Summing mass-sensitive cell scales absorbs polynomial noise.
- **Necessity:** matching moments hides changes in gains. Localized oscillations cancel polynomial information while retaining the gain’s change in slope.

@informal thm:consistency-threshold: For independent observations of a common law, \(d_n\ge2\), and known \(0<\epsilon_n\le1/2\), uniform mean-square consistency is possible exactly when \(\frac{d_n}{n\epsilon_n\log(e d_n)}\longrightarrow0\).

Here \(d_n\) and \(\epsilon_n\) are cell counts and overlap floors along the sample-size sequence. Under outcome consistency and conditional exchangeability, the same criterion governs causal optimal value.

---

## Appendix: Matched risk frontier

The deterministic estimator attains the universal minimax squared-error scale for observed and causally identified values.

@formal thm:matched-frontier

---

## Appendix: Observable upper bound

The prescribed observed-data estimator achieves the uniform squared-error upper bound.

@formal thm:observable-upper

---

## Appendix: Minimax lower bound

Every estimator faces the same worst-case squared-error order over the observed class.

@formal thm:all-estimator-lower

---

## Appendix: Consistency threshold

The joint cell-count and overlap criterion exactly characterizes uniform mean-square consistency, with fixed-parameter specializations.

@formal thm:consistency-threshold
