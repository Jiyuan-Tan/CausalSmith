# Estimating Latent Treatment-Effect Distributions

We can learn how population mass is distributed across latent class-average effects, even when those effects coincide.

---

## Research question

Treatment depends on an unobserved class \(U\). We observe treatment, outcomes, and two proxies informative about that class.

Miao et al. (2018) establish causal identification using two proxies and rank conditions. Virk et al. (2026) recover latent class-average effects and masses through an observable matrix:

- Eigenvalues locate effects.
- Normalized eigenvectors recover class features and masses.
- Their simultaneous recovery guarantees require separated effects.

As effects approach, individual eigenvectors become unstable. Equal effects cannot distinguish their classes through that matrix.

Can we estimate the **population distribution of class-average effects** through these collisions?

---

## Key idea

Combine population masses at equal effect values.

\[
\nu_P:=\sum_{u=1}^{k}p_u\delta_{\tau_u}.
\]

Here \(P\) is the population law, \(k\) is the number of latent classes, \(p_u=P(U=u)\), and \(\delta_{\tau_u}\) puts unit mass at effect \(\tau_u\).

The effect is \(\tau_u:=\mu_{1u}-\mu_{0u}\), where \(\mu_{tu}:=E_P[Y(t)\mid U=u]\). Potential outcomes \(Y(t)\) describe outcomes under treatment \(t\).

Use \(W_1\), the minimum cost of moving probability mass, charging mass times distance.

@informal thm:collision-uniform-root-n: Under the causal and proxy restrictions, fixed known dimensions, bounded contributions, latent-arm overlap, and uniform proxy-rank margins, both law estimators have uniform root-\(n\) Wasserstein bounds, including equal effects.

---

## Example

Two classes have population masses \(0.4\) and \(0.6\), and treatment probabilities \(0.4\) and \(0.6\), respectively.

Their Bernoulli potential-outcome means are

\[
E[Y(0)\mid U]=(0.25,0.25),
\qquad
E[Y(1)\mid U]=(0.5-\varepsilon,0.5+\varepsilon).
\]

Subtracting untreated from treated means gives, for \(0\le\varepsilon\le1/8\),

\[
\nu_{P_{\varepsilon}^{\mathrm{wit}}}
=
0.4\,\delta_{0.25-\varepsilon}
+
0.6\,\delta_{0.25+\varepsilon}.
\]

Here \(P_{\varepsilon}^{\mathrm{wit}}\) denotes this two-class population.

Moving both masses to \(0.25\) costs \(\varepsilon\). At zero, the target becomes \(\delta_{0.25}\), one atom with total mass \(1\).

What must remain informative as the effects merge?

---

## Model

Observe independent records \((T,X,Z,Y)\): binary treatment \(T\), target proxy \(X\in\mathbb R^{d_x}\), reference proxy \(Z\in\mathbb R^{d_z}\), and realized outcome \(Y\).

- **Causal validity:** \(Y=Y(T)\) and \(Y(t)\perp T\mid U\). Within a class, treatment does not select potential outcomes.
- **Reference-proxy separation:** \(Z\perp(X,Y)\mid(T,U)\). Given class and treatment, the reference proxy separates from the target proxy and outcome.
- **Target-proxy separation:** \(X\perp(Y,T)\mid U\). The target proxy measures class consistently across arms.
- **Normalization:** \(X_1=1\). A constant first coordinate fixes the scale needed to recover population masses.

Our target distributes **class-average treatment effects** across the population.

---

## Assumptions

The dimensions and supplied constants stay fixed as \(n\) grows. These restrictions define \(\mathcal M\).

**Latent-arm overlap:**

\[
\min_{1\le u\le k,\ t\in\{0,1\}} P(U=u,T=t)\ge \pi_0 .
\]

The positive margin \(\pi_0\) prevents any class from disappearing within either arm.

**Informative proxies:**

\[
\min\{\sigma_k(A_0),\sigma_k(A_1),\sigma_k(B)\}\ge \sigma_0 .
\]

Columns of \(A_t\) are reference-proxy means within class and arm; columns of \(B\) are target-proxy means within class. Their smallest singular values \(\sigma_k\) stay above \(\sigma_0\).

**Bounded contributions:** \(\|X\|_2\le L\), \(\|ZX^\top\|_{\mathrm{op}}\le L\), and \(\|YZX^\top\|_{\mathrm{op}}\le L\).

The parameter domain is \(2\le k\le\min\{d_x,d_z\}\), \(L\ge1\), \(0<\pi_0\le1/(2k)\), and \(0<\sigma_0\le1\).

---

## Proxies through the collision

In our example, \(X=(1,X_2)^\top\) and \(Z=(1,Z_2)^\top\), with Bernoulli second coordinates.

Their class-specific mean matrices are

\[
B=\begin{psmallmatrix}1&1\\0.2&0.8\end{psmallmatrix},
\qquad
A_0=\begin{psmallmatrix}1&1\\0.3&0.7\end{psmallmatrix},
\qquad
A_1=\begin{psmallmatrix}1&1\\0.35&0.75\end{psmallmatrix},
\]

where columns correspond to the two classes.

Conditional on \(U\), treatment, the target proxy, and potential outcomes are independent. Conditional on \((U,T)\), the reference proxy separates from the target proxy and potential outcomes.

The proxy matrices stay unchanged as \(\varepsilon\) shrinks: effect equality does not destroy information about class.

@informal prop:two-class-witness-valid: For every \(0\le\varepsilon\le1/8\), this population belongs to \(\mathcal M\) with \(L=2\) and \(\pi_0=\sigma_0=0.1\); its proxy and observable moment matrices remain nonsingular at the collision.

---

## Observable moments

The method uses five observable blocks:

\[
S(P):=\bigl(M_0(P),M_1(P),N_0(P),N_1(P),m_X(P)\bigr).
\]

Here \(M_t(P)=E_P[ZX^\top\mid T=t]\), \(N_t(P)=E_P[YZX^\top\mid T=t]\), and \(m_X(P)=E_P[X]\).

The matrices measure proxy cross-moments and outcome-weighted cross-moments within each arm. The vector measures the proxy mean across the population.

Their combined error is

\[
d_S(s,s')
:=
\sum_{j=1}^{4}\lVert s_j-s'_j\rVert_{\mathrm{op}}
+\lVert s_5-s'_5\rVert_2.
\]

This adds matrix operator-norm errors and the Euclidean mean error.

The empirical summary \(\widehat S_n\) replaces these expectations by armwise sample averages and the overall proxy average.

---

## Main result: stability

Under the model restrictions defining \(\mathcal M\),

@informal thm:gap-free-positive-measure-modulus: Throughout \(\mathcal M\), observable-summary error bounds effect-law error linearly, with a constant depending only on the fixed dimensions, contribution bound, overlap margin, and proxy-rank margin.

\[
W_1(\nu_P,\nu_Q)\le C_{\mathrm{mod}}\,d_S(S(P),S(Q)).
\]

This holds for every \(P,Q\in\mathcal M\). The constant \(C_{\mathrm{mod}}>0\) does not depend on effect separation.

Equal summaries identify the same law. Small summary errors imply proportionally small transport errors through simultaneous merges and splits.

For our example, the guarantee includes \(\varepsilon=0\), where two class effects become one support point.

---

## Main result: estimation

Two estimators turn this population stability into sample inference:

- \(\widehat\nu_n\) repairs the empirical summary to the population-summary domain.
- \(\widehat\lambda_n\) fits a finite grid of conditioned spectral factors and valid probability laws.

For every \(P\in\mathcal M\), \(n\ge1\), and \(0<\eta<1/2\),

\[
Q_P^{(n)}\!\left\{
\max\!\left\{
W_1(\widehat\lambda_n,\nu_P),
W_1(\widehat\nu_n,\nu_P)
\right\}
>
C\sqrt{\frac{\log(C/\eta)}{n}}
\right\}\le \eta .
\]

Here \(Q_P^{(n)}=P_O^{\otimes n}\) is the sampling law of \(n\) independent observed records, and \(\eta\) is the tail probability.

The constant \(C\) depends only on the fixed dimensions and supplied bounds and margins. No effect gap enters the bound.

---

## Proxy cancellation

Proxy independence factors the armwise moment:

\[
M_t(P)
=
A_t\operatorname{diag}\{P(U=u\mid T=t):1\le u\le k\}B^\top .
\]

The diagonal contains class shares **within treatment arm \(t\)**. The matrix \(N_t(P)\) inserts the class outcome means \(\mu_{tu}\) into the same factorization.

Choose an orthonormal basis \(V(P)\) for the common \(k\)-dimensional row space of the two moment matrices. Form

\[
\Delta Q(P)
:=
\{M_1(P)V(P)\}^{\dagger}N_1(P)V(P)
-
\{M_0(P)V(P)\}^{\dagger}N_0(P)V(P),
\]

where \(\dagger\) denotes the Moore–Penrose inverse.

Inversion cancels reference-proxy features and arm shares. With \(R=B^\top V(P)\), this gives \(\Delta Q(P)=R^{-1}\operatorname{diag}(\tau)R\).

The eigenvalues are effects. Proxy conditioning controls the coordinate matrix \(R\), even when effects coincide.

---

## Population weighting

Eigenvalues locate effects; two observable anchors supply their population weights:

\[
a(P)^\top:=m_X(P)^\top V(P),
\qquad
c(P):=V(P)^\top e_1.
\]

Here \(e_1\) selects the constant first proxy coordinate.

Let \(p=(p_1,\ldots,p_k)^\top\) and let \(\mathbf1_k\) be the vector of ones. Since \(m_X(P)=Bp\) and \(B^\top e_1=\mathbf1_k\),

- \(a(P)^\top=p^\top R\).
- \(c(P)=R^{-1}\mathbf1_k\).
- \(\Delta Q(P)=R^{-1}\operatorname{diag}(\tau)R\).

The transformations cancel:

\(\int x^j\,d\nu_P(x)=a(P)^\top\Delta Q(P)^j c(P)=\sum_u p_u\tau_u^j\), for \(j=0,\ldots,2k-1\).

Here \(x\) is an effect value. The operator and anchors recover population-weighted effect moments, although the original matrices use treatment-arm shares.

---

## From moments to transport

A one-Lipschitz function satisfies \(|f(x)-f(y)|\le|x-y|\): it cannot magnify a distance between effects.

Normalize it by \(f(0)=0\). This leaves comparisons of probability laws unchanged and gives \(|f(x)|\le L_\tau\) on the effect interval, where \(L_\tau=4L\sqrt{d_z}/\sigma_0\).

Apply \(f\) to the diagonal effects in the similarity representation:

\(f(\Delta Q(P))=R^{-1}\operatorname{diag}\{f(\tau_u)\}R\).

The same anchors recover the integral:

\(\int f(x)\,d\nu_P(x)=a(P)^\top f(\Delta Q(P))c(P)\).

Thus bounding anchored operator comparisons for all these functions bounds \(W_1\), the largest difference between their integrals.

Why can those operator comparisons avoid dividing by an effect gap?

---

## Why gaps cancel

Compare two effect operators \(\Delta=R^{-1}\operatorname{diag}(\tau)R\) and \(\Delta'=R'^{-1}\operatorname{diag}(\tau')R'\). Let \(H=RR'^{-1}\) describe mixing between their coordinates.

Each entry satisfies

\((\tau_i-\tau'_j)H_{ij}=[R(\Delta-\Delta')R'^{-1}]_{ij}\).

Replacing effects by \(f\) changes the left side to \((f(\tau_i)-f(\tau'_j))H_{ij}\). Its magnitude cannot increase, because \(f\) is one-Lipschitz.

Conditioned \(R,R'\) control conversion back to operator norm. No inverse effect gap appears.

For a group separated by distance \(g\), mass uncertainty can grow like summary error divided by \(g\); transporting that uncertainty costs \(g\) times its size.

In our example, moving mass \(h\) between effects costs \(2\varepsilon|h|\). At the collision, \(\Delta Q=0.25I_2\), and the anchors recover total mass \(1\) without choosing individual eigenvectors.

---

## Repairing sample moments

Noisy summaries can produce nonreal eigenvalues or invalid masses. The first estimator repairs the summary before recovering a probability law.

A **feasible summary** is \(q=S(P_q)\) for some \(P_q\in\mathcal M\). Identification makes its law independent of which representative \(P_q\) is chosen.

Let \(\mathcal K\) be the closure of these summaries. Choose a nearest point:

\[
\Pi(s)\in\mathcal K,
\qquad
d_S(\Pi(s),s)\le d_S(q,s)\quad\text{for every }q\in\mathcal K .
\]

Here \(s\) is a noisy summary; \(q\) ranges over the closed population-summary domain.

The stable law map extends to \(\mathcal K\) as \(\overline F\). Return \(\widehat\nu_n=\overline F(\Pi(\widehat S_n))\).

Because the true summary belongs to \(\mathcal K\), repair increases its distance from truth by at most a factor of two. Wu and Yang (2020) similarly repair noisy mixture moments by imposing feasibility.

---

## Empirical effect operator

The grid estimator works directly in the original \(d_x\) proxy coordinates.

At the population summary, the \(k\)-dimensional operator lifts to \(D(P)=V(P)\Delta Q(P)V(P)^\top\). It acts as zero outside the proxy signal space.

Its sample analogue is

\[
\widehat D_n:=(\widehat M_{1,n})^\dagger_{\ge s_0/2}\widehat N_{1,n}-(\widehat M_{0,n})^\dagger_{\ge s_0/2}\widehat N_{0,n}.
\]

Here \(s_0=\pi_0\sigma_0^2\). For each empirical arm matrix, retain singular directions with singular values at least \(s_0/2\), invert those values, and discard the rest.

The hatted matrices are the observed armwise averages defined by \(\widehat S_n\). Thus \(\widehat D_n\) is a fully specified \(d_x\times d_x\) matrix.

At a model summary, both arms have the same signal row space and this construction equals the lifted population operator. Noisy arm matrices can have different retained spaces; the formula still supplies the matrix the grid fits.

---

## Finite grid search

Search candidates \(\vartheta=(V,R,p,\tau)\) on prescribed grids with mesh at \(n^{-1/2}\) scale:

- \(V\) has \(k\) orthonormal columns in the \(d_x\) proxy coordinates.
- \(R\) satisfies \(\sigma_k(R)\ge\sigma_0/2\) and \(\|R\|_{\mathrm{op}}\le2\sqrt{k}L\).
- Masses satisfy \(p_u\ge\pi_0\) and \(\sum_up_u=1\).
- Effects are real and lie in \([-L_\tau,L_\tau]\).

Each candidate implies \(D_\vartheta=VR^{-1}\operatorname{diag}(\tau)RV^\top\), \(m_\vartheta=VR^\top p\), and \(b_\vartheta=RV^\top e_1\).

Minimize

\[
J_n(\vartheta;s):=\lVert D_\vartheta-\widehat D(s)\rVert_{\mathrm{op}}+\lVert m_\vartheta-m_X\rVert_2+\lVert b_\vartheta-\mathbf 1_k\rVert_2.
\]

At \(s=\widehat S_n\), \(\widehat D(s)=\widehat D_n\) and \(m_X=\widehat m_{X,n}\). The terms fit the effect operator, population weighting, and constant-coordinate normalization.

Return the first grid minimizer’s law \(\lambda_\vartheta=\sum_up_u\delta_{\tau_u}\). Every distinct output atom has mass at least \(\pi_0\), including after coincident locations are merged.

---

## From fit to law

Candidates need not describe complete causal populations. Their conditioned operator structure and anchors suffice.

For a one-Lipschitz \(f\) with \(f(0)=0\),

\(m_\vartheta^\top f(D_\vartheta)e_1=p^\top f(\operatorname{diag}(\tau))b_\vartheta\).

The candidate law instead integrates \(f\) as \(p^\top f(\operatorname{diag}(\tau))\mathbf1_k\). Their discrepancy is at most \(L_\tau\|b_\vartheta-\mathbf1_k\|_2\).

The operator residual is controlled by gap cancellation; the mean residual controls population weighting. Together, all three objective terms control law error.

Rounding the true factors supplies a candidate with \(1/\sqrt n\) approximation error. The minimizer fits at least as well:

\[
W_1(\widehat\lambda_n(\omega),\nu_P)
\le
C_{\mathrm{lat}}\left\{
d_S(\widehat S_n(\omega),S(P))+\frac{1}{\sqrt n}
\right\}
\]

This holds for every sample \(\omega\). Bounded contributions and latent-arm overlap give uniform summary concentration, completing the root-\(n\) guarantee.

---

## Honest confidence sets

For miscoverage probability \(0<\alpha<1/2\), summary concentration gives radius \(r_{n,\alpha}:=C_0L\sqrt{\log(C_0/\alpha)/n}\), with calibrated constant \(C_0\).

Define

\[
m_\star:=\pi_0,\qquad
R_{n,\alpha}:=C_{\mathrm{lat}}\left(r_{n,\alpha}+(\sqrt n)^{-1}\right).
\]

The law radius combines sampling error and grid approximation. The mass floor \(m_\star\) holds for every distinct true atom and every distinct grid-estimator atom.

Use the confidence set

\[
\mathcal C^{\mathrm{alg}}_{n,\alpha}
:=
\{\xi\in\mathcal P_{\le k}([-L_\tau,L_\tau]):
\operatorname{AtomFloor}(m_\star,\xi),\
W_1(\xi,\widehat\lambda_n)\le R_{n,\alpha}\}.
\]

Here \(\mathcal P_{\le k}\) contains probability laws with at most \(k\) atoms; \(\operatorname{AtomFloor}\) requires each distinct atom’s mass to be at least \(m_\star\).

@informal thm:honest-root-n-confidence: Throughout \(\mathcal M\), this grid-centered set covers \(\nu_P\) with probability at least \(1-\alpha\); on every sample it is nonempty and has Wasserstein diameter at most \(2R_{n,\alpha}\).

Membership uses finite constraints on atom locations, masses, and a transport plan.

---

## Reporting unresolved groups

Set \(\rho_{n,\alpha}=R_{n,\alpha}/m_\star\). Connect estimated support points within \(4\rho_{n,\alpha}\); let \(C\) be a connected component.

On the confidence event:

- A true atom farther than \(\rho_{n,\alpha}\) from estimated support would alone cost more than \(R_{n,\alpha}\) to transport.
- The reverse argument holds because the grid constraint \(p_u\ge\pi_0\) gives the estimated center the same distinct-atom mass floor.
- Different components are more than \(4\rho_{n,\alpha}\) apart, so each true atom associates with exactly one component.

Report \([\min C-\rho_{n,\alpha},\max C+\rho_{n,\alpha}]\) for support. Let \(K_C(\xi)\) contain candidate atoms within \(\rho_{n,\alpha}\) of \(C\).

\[
I_C:=\left[
\inf_{\xi\in\mathcal C^{\mathrm{alg}}_{n,\alpha}}\xi(K_C(\xi)),
\sup_{\xi\in\mathcal C^{\mathrm{alg}}_{n,\alpha}}\xi(K_C(\xi))
\right].
\]

This reports all aggregate masses compatible with the confidence set.

@informal thm:cluster-adaptive-report: Throughout \(\mathcal M\), with probability at least \(1-\alpha\), reported groups partition the true support, their support intervals contain associated effects, and their mass intervals contain associated aggregate masses.

---

## Further results

- In our calibrated two-class model, the worst-case expected law-estimation rate \(n^{-1/2}\) is minimax sharp.
- Ordered masses have sharp worst-case \(\ell_1\) rate \(\min\{1,1/(\sqrt n\,g)\}\) on two-class strata with distinct effects and smallest gap between \(g/2\) and \(2g\), for \(0<g\le1/4\).
- This inverse-gap mass cost matches the mechanism: transport multiplies mass uncertainty by the distance across which it moves.

---

## Open questions

- Inference when the number of latent classes \(k\) is unknown.
- Application-specific conditions that justify the causal and proxy restrictions.
- Exact polynomial-time computation of the original nearest-summary confidence image and its support-dependent mass extrema.

---

## Takeaways

- Population mass at class-average effect values remains a stable target when effects coincide.
- Causal and proxy restrictions, fixed dimensions, bounded contributions, latent-arm overlap, and conditioned proxies deliver uniform root-\(n\) estimation and honest confidence reporting.
- Observable anchors recover population weights; transport cancels gap sensitivity. Resolving separate ordered masses retains an inverse-gap cost.

---

## Appendix: Gap-free law stability

Observable-summary error controls effect-law error uniformly through collisions.

@formal thm:gap-free-positive-measure-modulus

---

## Appendix: Collision-uniform estimation

Both summary repair and finite grid search satisfy uniform root-\(n\) Wasserstein tail bounds.

@formal thm:collision-uniform-root-n

---

## Appendix: Honest confidence reporting

Both confidence constructions simultaneously cover the true law and have bounded Wasserstein diameters.

@formal thm:honest-root-n-confidence

---

## Appendix: Matching local lower bounds

Explicit two-class observed-data experiments establish root-\(n\) law difficulty and inverse-gap ordered-mass difficulty.

The calibration is \(k=d_x=d_z=2\), \(L=2\), and \(\pi_0=\sigma_0=1/10\). Law estimators have output support radius \(L_\tau=80\sqrt2\); ordered-mass estimators return probability vectors.

For the same-class ordered comparison, \(\mathcal M(g)\) contains populations with two distinct effects and \(g/2\le\delta(P)\le2g\), where \(\delta(P)\) is their effect gap and \(0<g\le1/4\).

The local experiments restrict one-record observed-data Kullback–Leibler divergence to at most \(c_{\mathrm{loc}}/n\), for fixed \(0<c_{\mathrm{loc}}<1\). This divergence measures statistical distinguishability of the observed laws.

@formal thm:matching-local-lower-bounds
