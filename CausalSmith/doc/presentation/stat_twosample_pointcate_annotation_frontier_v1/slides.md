# Treatment Effects With Fewer Outcome Labels

Records without outcomes can improve treatment-effect precision by helping us learn how treatment was assigned.

---

## Motivation

A practitioner wants the treatment effect at a particular covariate profile, such as a patient’s characteristics.

- A labeled record contains covariates \(X\), treatment \(A\), and response \(Y\).
- An outcome-free record contains \(X,A\), but no response.
- We observe \(n\ge2\) labeled records and \(m\ge0\) independent outcome-free records from the same population.
- All \(N=n+m\) records contain treatment information; only \(n\) contain responses.

How much can additional treatment information improve precision?

---

## Standard approach

Separate regressions estimate treated and control response means, then subtract them.

Their difference can be smoother—and easier to estimate—than either response mean.

- Residualization exploits the smoother effect, but learning treatment assignment and baseline response still creates adjustment error.
- Kennedy (2023) separates target-regression error from products of adjustment-function errors.
- Kennedy et al. (2024) provide the closest supervised minimax comparison. Their localized projection correction balances effect approximation, nuisance approximation, and sampling noise, attaining their supervised order under their conditions.

We use this projection architecture with independent response and treatment samples. Enlarging the treatment sample changes correction noise from a labeled-by-labeled calculation to one governed by labeled and total counts.

When does that change improve the estimation order?

---

## Key idea

Estimate the adjustment by pairing an independent response sample with a larger treatment sample.

Let \(d\) be covariate dimension, and let \(\alpha,\beta,\gamma\) measure the smoothness of assignment, baseline response, and treatment effect.

Under known uniform covariates, binary responses, exchangeability, fixed overlap, and our public smoothness restrictions, the optimal worst-case error has order

\(R(n,m)\asymp\max\left\{n^{-\gamma/(2\gamma+d)},[n(n+m)]^{-\gamma/(2\gamma+d+\gamma d/(\alpha+\beta))}\right\}\).

Here \(R(n,m)\) is the smallest achievable worst-case expected absolute error; \(\asymp\) means equality of order up to fixed positive constants.

- Response labels determine the first term.
- Learning the adjustment determines the second.
- Extra treatment records reduce the second term until response labels govern precision.

---

## Example

One covariate, a Lipschitz treatment effect, and rough assignment and baseline response:

\(d=1\), \(\gamma=1\), and \(\alpha=\beta=1/8\).

\[
r_*(n,m)=\max\left\{n^{-1/3},[n(n+m)]^{-1/7}\right\}.
\]

Here \(r_*\) is the sharp error order.

- Labeled records alone give order \(n^{-2/7}\).
- The terms meet at total count \(N=n^{4/3}\).
- With \(n=1000\), this is \(N=10000\): \(9000\) outcome-free records.
- Beyond that boundary, the order remains \(n^{-1/3}\).

These counts equate rate formulas; actual risks retain model-dependent constants.

---

## Model

Treatment \(A\) and potential responses \(Y(0),Y(1)\) are binary. The observed response is \(Y(0)\) under control and \(Y(1)\) under treatment.

For population law \(P\), the propensity \(e_P(x)\) is the treatment probability at profile \(x\). The arm means \(\mu_{0,P}(x),\mu_{1,P}(x)\) are the corresponding potential-response probabilities.

\[
\mu_{1,P}(x)-\mu_{0,P}(x)=\tau_P(x)
\qquad\text{for every }x\in[0,1]^d.
\]

This difference defines the conditional treatment effect \(\tau_P(x)\). Our target is its value at the cube center \(x_0=(1/2,\ldots,1/2)\).

Exchangeability and overlap identify the arm means from observed responses. Continuity and full covariate support identify their contrast at this particular point.

---

## Assumptions

The model class \(\mathcal M=\mathcal M(d,\alpha,\beta,\gamma,L,\varepsilon)\) maintains:

- **Known design:** \(X\) is uniform on \([0,1]^d\), with integer \(d\ge1\); local covariate probabilities are known.
- **Exchangeability:** \(A\perp(Y(0),Y(1))\mid X\); recorded covariates remove treatment selection relevant to responses.
- **Overlap:** \(e_P(x)\in[\varepsilon,1-\varepsilon]\), with fixed public \(0<\varepsilon<1/2\); both treatment arms remain observable.
- **Response bounds:** both arm means lie in \([0,1]\), so effects lie in \([-1,1]\).
- **Public smoothness:** \(\|e_P\|_{H^\alpha}\le L\), \(\|\mu_{0,P}\|_{H^\beta}\le L\), and \(\|\tau_P\|_{H^\gamma}\le L\), with \(0<\alpha,\beta\le1\), \(1\le\gamma\le3\), and public radius \(L>1/2\).
- **Sampling:** all records are independent draws through their observation channels from the same population.

Hölder smoothness bounds local variation and, at higher orders, variation in derivatives. Assignment and baseline response are the two nuisance functions needed for adjustment.

In our example, their smoothness orders are \(1/8\), while the effect is Lipschitz.

---

## Main result

Write \(\mathcal R_{n,m}(T,P)\) for estimator \(T\)’s expected absolute error. Minimax risk \(R(n,m)\) chooses the estimator with the smallest worst-case error over \(\mathcal M\).

The sharp rate is

\[
r_*(n,m;d,\alpha,\beta,\gamma)
=
\max\left\{
n^{-\gamma/(2\gamma+d)},
[n(n+m)]^{-\gamma/(2\gamma+d+\gamma d/(\alpha+\beta))}
\right\}
=
r_{\mathrm{up}}(n,m),
\]

where \(r_{\mathrm{up}}\) denotes our estimator’s upper-bound order.

\[
c\,r_*
\le R(n,m)
\le \sup_{P\in\mathcal M}\mathcal R_{n,m}(T_*,P)
\le C\,r_*.
\]

Here \(T_*\) is our publicly tuned projection estimator; \(c,C\) depend only on the fixed model parameters.

@informal thm:sharp-annotation-frontier: Under the model and public parameter restrictions, for all \(n\ge2,m\ge0\), \(T_*\) has worst-case expected absolute error at most \(Cr_*\), and every estimator, including randomized ones, has worst-case error at least \(cr_*\).

In the example, both the labeled-only order \(n^{-2/7}\) and eventual floor \(n^{-1/3}\) are unavoidable.

---

## Residualization

Subtracting the treatment probability from treatment isolates the effect:

\[
\mathbb E_P[(A-e_P(X))Y\mid X=x]
=e_P(x)\{1-e_P(x)\}\tau_P(x).
\]

The left side removes predictable treatment selection from the treatment-response moment. The right side is the effect multiplied by treatment variation, which overlap keeps positive.

With supplied \(e_P\), smoothing can exploit the effect’s regularity directly. Estimating \(e_P\) introduces adjustment error that our projection correction must control.

Define \(r_o(n)=n^{-\gamma/(2\gamma+d)}\), the supplied-propensity order.

@informal thm:supplied-propensity: Under the model and public parameter restrictions, supplying \(e_P\) gives minimax expected absolute-error order \(r_o(n)\) for every \(n\ge2,m\ge0\).

The same lower bound holds when \(e_P=\mu_{0,P}=1/2\). Even perfect treatment information leaves a response-label floor.

---

## Two spatial scales

Use a neighborhood \(C_h\) of side length \(h\), centered at \(x_0\).

- A coarse polynomial basis \(r(x)\), of total degree at most two, approximates the effect across the neighborhood.
- A finer grid resolves assignment and baseline-response variation.

\[
\delta=\frac hJ,\qquad
K_J(x,x')=\mathbf b_J(x)^\top \mathbf b_J(x'),\qquad
\Pi_Jf(x)=\int K_J(x,x')f(x')\,d\nu_h(x').
\]

Here \(J\) is grid resolution, \(\delta\) is cell width, \(\mathbf b_J\) collects cellwise polynomial basis functions, and \(\nu_h\) is the uniform probability measure on \(C_h\).

The kernel \(K_J\) computes the projection \(\Pi_Jf\), a polynomial approximation within each fine cell. Write \(r_0=r(x_0)\) for evaluating a coarse polynomial at the target.

A smooth effect can be fitted across a neighborhood that still contains substantial nuisance variation.

---

## Independent record roles

Sample splitting assigns disjoint records to response and treatment roles, making their averages independent.

\[
\ell=\lfloor n/2\rfloor,\qquad
t=N-\ell,\qquad
I_L=\{1,\ldots,\ell\},\qquad
I_T=\{\ell+1,\ldots,N\}.
\]

These formulas allocate records:

- \(I_L\) selects \(\ell\) labeled records for the response role.
- \(I_T\) selects \(t\) records for the treatment role: remaining labeled records plus all outcome-free records.
- Treatment-role pairs are denoted \((X_i^T,A_i^T)\); their outcomes are discarded.

The response role grows with \(n\); the treatment role grows with \(N\).

Cross-role products estimate products of population moments without using the same record on both sides of a pair.

---

## Response correction

Let \(w_h(x)=h^{-d}\mathbf1\{x\in C_h\}\) weight observations into the neighborhood.

The empirical projection \(\widehat\eta_J^L\) estimates a fine-cell approximation to the mean observed response.

\[
\begin{aligned}
\widehat R_{h,J}
&=\frac1\ell\sum_{j\in I_L}w_h(X_j)r(X_j)A_jY_j
-\frac1t\sum_{i\in I_T}w_h(X_i^T)r(X_i^T)A_i^T
\widehat\eta_J^L(X_i^T)\\
&=\frac1\ell\sum_{j\in I_L}w_h(X_j)r(X_j)A_jY_j
-\frac1{t\ell}\sum_{i\in I_T}\sum_{j\in I_L}
w_h(X_i^T)w_h(X_j)r(X_i^T)A_i^T
K_J(X_i^T,X_j)Y_j.
\end{aligned}
\]

This computes the corrected response vector \(\widehat R_{h,J}\): treated responses minus the projected treatment-response product.

The correction pairs every treatment-role record with every response-role record—a rectangle with \(t\) rows and \(\ell\) columns.

Additional outcome-free records enlarge its rows.

---

## Design correction

The effect’s local polynomial design needs the corresponding treatment-treatment correction:

\[
\begin{aligned}
\widehat Q^{\mathrm{raw}}_{h,J}
&=\frac1\ell\sum_{j\in I_L}w_h(X_j)r(X_j)r(X_j)^\top A_j\\
&\quad-\frac1{t\ell}\sum_{i\in I_T}\sum_{j\in I_L}
w_h(X_i^T)w_h(X_j)r(X_i^T)r(X_j)^\top
A_i^TA_jK_J(X_i^T,X_j).
\end{aligned}
\]

This matrix supplies the corrected coefficients multiplying the effect polynomial. Its rectangular term uses treatment indicators from both roles.

Use the symmetric average
\(\widehat Q_{h,J}=(\widehat Q^{\mathrm{raw}}_{h,J}+(\widehat Q^{\mathrm{raw}}_{h,J})^\top)/2\).

Correcting both the response vector and the design matrix preserves their population equation for the effect polynomial.

Why does the remaining nuisance error involve a product?

---

## Why only a product remains

Orthogonal projection removes terms containing only one projection residual.

For square-integrable functions \(f_1,f_2\),

\[
\int f_1f_2\,d\nu_h-\int f_1\Pi_Jf_2\,d\nu_h
=
\int(f_1-\Pi_Jf_1)(f_2-\Pi_Jf_2)\,d\nu_h,
\]

This identity computes the difference between a true product moment and its projected correction: only the product of the two unrepresented parts remains.

- In our response equation, \(f_1=e_Pr_u\), where \(r_u\) is a coarse basis coordinate, and \(f_2=\mu_{0,P}\).
- Their projection residuals have norms bounded by orders \(\delta^\alpha\) and \(\delta^\beta\).
- Their product contributes at most order \(\delta^{\alpha+\beta}\).

Correcting the design reproduces the coarse effect polynomial. Approximating the actual effect by that polynomial contributes at most order \(h^\gamma\).

---

## Guarded local fit

Invert the corrected matrix, fit the polynomial, and evaluate it at the target when the matrix is stable:

\[
\widehat T_{h,J}=
\begin{cases}
\mathrm{clip}_{[-1,1]}
\bigl(r_0^\top\widehat Q_{h,J}^{-1}\widehat R_{h,J}\bigr),
&\lambda_{\min}(\widehat Q_{h,J})\ge g(\varepsilon),\\
0,
&\lambda_{\min}(\widehat Q_{h,J})<g(\varepsilon).
\end{cases}
\]

This computes the point estimate \(\widehat T_{h,J}\). Here \(\lambda_{\min}\) is the smallest eigenvalue and \(g(\varepsilon)=\varepsilon(1-\varepsilon)/2\).

The population matrix remains stable: its quadratic form is treatment variation plus a nonnegative squared projection residual.

The guard prevents unstable sample inversion. Clipping projects the estimate onto the feasible effect range \([-1,1]\) and cannot increase absolute error.

---

## Error budget

Let \(S=\alpha+\beta\), the combined nuisance smoothness.

@informal thm:rectangular-upper: Under the model and public parameter restrictions, for \(n\ge2,m\ge0\), \(0<h\le1/2\), and integer \(J\ge1\), the guarded estimator’s worst-case expected absolute error is at most the four-term bound below.

\[
\mathcal R_{n,m}(\widehat T_{h,J},P)
\le
C\min\left\{
1,\,
h^\gamma+
(h/J)^{\alpha+\beta}+
(nh^d)^{-1/2}+
\bigl(n(n+m)h^d(h/J)^d\bigr)^{-1/2}
\right\}.
\]

The bound separates four sources of error:

- \(h^\gamma\): effect approximation across the neighborhood.
- \(\delta^S\): the product of nuisance projection errors.
- \((nh^d)^{-1/2}\): response sampling within the neighborhood.
- \((nNh^d\delta^d)^{-1/2}\): sampling the rectangular correction.

Pairs share records. Separating each role’s fluctuations from the joint remainder yields the two sampling terms.

Finer cells reduce nuisance bias but raise correction noise; additional treatment records reduce that noise.

---

## Public tuning

Let \(\Delta=2\gamma+d+\gamma d/S\), the denominator governing the product-of-counts rate.

\[
h_*=\frac12\max\left\{n^{-1/(2\gamma+d)},(nN)^{-1/\Delta}\right\},
\qquad
J_*=\left\lceil h_*^{-\max\{0,\gamma/S-1\}}\right\rceil,
\qquad
\widehat T_{\mathrm{up}}=\widehat T_{h_*,J_*},
\]

These choices compute the neighborhood width \(h_*\), grid resolution \(J_*\), and tuned estimator \(\widehat T_{\mathrm{up}}\), also denoted \(T_*\), from observed counts and public smoothness parameters.

- If \(S<\gamma\), cell width has order \(h_*^{\gamma/S}\), matching nuisance bias to effect bias.
- If \(S\ge\gamma\), one cell suffices.
- The neighborhood is large enough to control both sampling terms.

In our example, \(S=1/4\) and \(\gamma=1\): adjustment uses much finer cells than the effect fit.

Why can no estimator improve the resulting order?

---

## Shared local signs

To construct difficult populations, choose a hypothesis \(\theta\in\{-1,+1\}\).

At each local index \(\mathbf z\), draw an assignment sign \(\lambda_{\mathbf z}\) and a response sign \(\eta_{\mathbf z}\). Both are individually fair; their correlation is \(\rho_\theta=\theta/2\).

| Sign pair | Under \(\theta=+1\) | Under \(\theta=-1\) |
|---|---|---|
| \((+1,+1)\) or \((-1,-1)\), each | \(3/8\) | \(1/8\) |
| \((+1,-1)\) or \((-1,+1)\), each | \(1/8\) | \(3/8\) |

Pairs are independent across indices. Draw the signs once for a population, then share them across all its records.

Let \(\phi_{\mathbf z}\) be smooth shapes localized at scale \(\delta\) inside \(C_h\), and let \(\mathcal I\) index those shapes.

\[
F_\lambda(x)=
\sum_{\mathbf z\in\mathcal I}\lambda_{\mathbf z}\phi_{\mathbf z}(x),
\qquad
G_\eta(x)=
\sum_{\mathbf z\in\mathcal I}\eta_{\mathbf z}\phi_{\mathbf z}(x).
\]

These sums turn the sign arrays into local assignment and response patterns. The hypotheses change their correlation while preserving each pattern’s marginal distribution.

---

## Opposite effects

Let \(B_h\) be a smooth bump supported on \(C_h\), equal to one at \(x_0\). Choose small positive assignment and response amplitudes \(a,b\).

\[
e_\lambda(x)=\frac12+aF_\lambda(x),
\qquad
\tau_\theta(x)=-4ab\rho_\theta B_h(x)^2,
\]

\[
\mu_{0,\theta,\eta}(x)=
\frac12+bG_\eta(x)-\frac12\tau_\theta(x),
\qquad
\mu_{1,\theta,\eta}(x)=
\frac12+bG_\eta(x)+\frac12\tau_\theta(x).
\]

These formulas build the population’s treatment probability, effect, and arm means.

- **Assignment perturbation:** \(aF_\lambda\) changes treatment probabilities.
- **Common response perturbation:** \(bG_\eta\) changes both arm means equally and cancels from their contrast.
- **Opposite effect shifts:** the two arms receive opposite shifts; at \(x_0\), the hypotheses have effects \(-2ab\) and \(2ab\), separated by \(4ab\).

The constraints \(a\le c\delta^\alpha\), \(b\le c\delta^\beta\), and \(ab\le ch^\gamma\), for a sufficiently small fixed \(c>0\), keep these populations inside our model.

---

## Singleton cancellation

The shapes satisfy \(\sum_{\mathbf z\in\mathcal I}\phi_{\mathbf z}(x)^2=B_h(x)^2\). Averaging signs under hypothesis \(\theta\), denoted by \(\mathbb E_\theta\), therefore gives zero means for \(F_\lambda,G_\eta\) and
\(\mathbb E_\theta[F_\lambda(x)G_\eta(x)]=\theta B_h(x)^2/2\).

Encode treatment and response as \(s^A=2A-1\) and \(s^Y=2Y-1\). A labeled record’s likelihood relative to four equally likely observed values is

\[
L_{\theta,\lambda,\eta}(x;s^A,s^Y)
:=
(1+2s^AaF_\lambda(x))
(1+2s^YbG_\eta(x)+s^As^Y\tau_\theta(x)).
\]

This multiplies the treatment and response likelihood factors.

After averaging signs, the effect term cancels exactly against \(4ab\,\mathbb E_\theta[F_\lambda(x)G_\eta(x)]\). All other nonconstant terms average to zero.

Thus a single labeled record has the same conditional law under both hypotheses: every \((A,Y)\) value has probability \(1/4\).

Outcome-free records alone also have identical joint laws because the entire assignment-sign distribution is unchanged.

---

## Information per nearby group

Conditional on the covariates, connect records inside \(C_h\) when their maximum-coordinate distance is at most \(2\delta\).

Different connected groups use disjoint sign entries, so their mixture likelihoods factor. Only groups containing a label and at least one other record can distinguish the hypotheses.

Let \(\mathcal V\) be a group of size \(p_{\mathrm{cmp}}\). Its mixture density \(g_{\theta,\mathcal V}\) averages record likelihoods over shared signs; \(\mathbf x,\mathbf s\) collect its covariates and encoded observations.

Assignment-only and response-only terms have identical averages across hypotheses. The difference requires their product, of size \(ab\); the direct effect shift also has size \(ab\).

\[
|g_{+1,\mathcal V}(\mathbf x,\mathbf s)
-g_{-1,\mathcal V}(\mathbf x,\mathbf s)|
\le
C_\Delta(3/2)^{p_{\mathrm{cmp}}}
p_{\mathrm{cmp}}^2ab.
\]

This bounds the group’s likelihood difference; \(C_\Delta\) is a fixed constant.

Small amplitudes also give a density floor \((1/2)^{p_{\mathrm{cmp}}}\). Squaring the likelihood difference bounds the group’s squared Hellinger distance by
\(K_{\mathrm{info}}(9/2)^{p_{\mathrm{cmp}}}p_{\mathrm{cmp}}^4a^2b^2\), with fixed \(K_{\mathrm{info}}\).

Squared Hellinger distance measures distinguishability between the two group-data laws. A small value prevents reliable discrimination between their opposite target effects. For two records, this information is at most a fixed multiple of \(a^2b^2\).

---

## Controlling larger groups

Connect each informative group through a tree rooted at a labeled record. The root lies in \(C_h\), and every additional record must lie within the fine spatial scale \(\delta\).

- For two records, the interaction count is at most order \(nNh^d\delta^d\): labels × possible partners × nearby-location probabilities.
- Each additional record introduces a factor \(N\delta^d\). Requiring \(N\delta^d\le c_0\), for a sufficiently small fixed \(c_0>0\), makes the sum over group sizes converge despite the tree counts and distance factors.
- Larger groups therefore change the constant, while preserving the interaction scale.

Squared Hellinger distances add as upper bounds across independent groups. Averaging over covariates yields

\[
H^2(M_{+1},M_{-1})
\le CnNh^d\delta^da^2b^2.
\]

Here \(M_{+1},M_{-1}\) are the full-data mixture laws, and \(H^2\) measures how distinguishable they are. This is our original-record information bound.

---

## Matching lower bounds

Define the smoothness threshold \(S_{\mathrm{crit}}=\gamma d/(2\gamma+d)\) and total-count exponent \(q_*=S_{\mathrm{crit}}/S\).

When \(S<S_{\mathrm{crit}}\) and \(N\le n^{q_*}\):

- Choose \(h\) of order \((nN)^{-1/\Delta}\) and \(\delta\) of order \((nN)^{-\gamma/(S\Delta)}\), with sufficiently small amplitudes at their allowed smoothness scales.
- The target separation \(4ab\) has order \((nN)^{-\gamma/\Delta}\), while the full-data information bound stays below a fixed small constant.
- These scales satisfy small occupancy throughout this count range, including its boundary.

Kennedy et al. (2024), Lemma 1, supply the testing inequality: separated targets with close mixture laws force expected absolute error at least a fixed fraction of their separation. Applied here, it gives

\[
R(n,m)\ge c(nN)^{-\gamma/\Delta}.
\]

This is the matching adjustment lower bound.

The supplied-propensity lower bound matches the response-label term when \(S\ge S_{\mathrm{crit}}\), or when \(S<S_{\mathrm{crit}}\) and \(N\ge n^{q_*}\).

In our example, the mixture argument covers \(N\le n^{4/3}\); the response-label floor matches thereafter.

---

## Open questions

- General or unknown covariate distributions, covariate shift, and adaptive selection of records for response review.
- Data-driven smoothness selection and confidence intervals with valid coverage.
- Other losses and causal targets, and richer auxiliary information such as response proxies or repeated measurements.

---

## Takeaways

- Outcome-free treatment records improve precision when rough assignment and baseline-response functions govern the labeled-only rate, until response labels impose the floor.
- Independent record roles and a fine projection leave a product of nuisance errors, with correction noise governed by labeled and total counts.
- The lower bound follows the same interaction scale: single records hide opposite effects, nearby labeled–record groups reveal information of size at most \(a^2b^2\), and small occupancy controls all larger groups.

---

## Appendix: Sharp annotation frontier

The projection estimator attains the optimal error order uniformly across labeled and outcome-free sample sizes.

@formal thm:sharp-annotation-frontier

---

## Appendix: Supplied propensity benchmark

Supplying treatment probabilities isolates the precision limit imposed by response labels.

@formal thm:supplied-propensity

---

## Appendix: Rectangular estimator guarantee

The four-term risk bound explains how separate localization and projection scales attain the sharp rate.

@formal thm:rectangular-upper

---

## Appendix: Acquisition thresholds

The sharp rate gives order comparisons and simultaneous acquisition requirements for labels and total treatment records.

@formal prop:annotation-threshold
