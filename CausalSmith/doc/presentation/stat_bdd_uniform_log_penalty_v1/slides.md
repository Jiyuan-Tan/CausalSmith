# Uniform Accuracy Along a Boundary

Distance hides direction; recovering an entire boundary curve requires resolving many hidden local changes at once.

---

## Research question

A geographic regression discontinuity design assigns treatment by location. Practitioners want accurate treatment effects **along the whole boundary**.

Keele and Titiunik (2015) explain the geographic design. Cattaneo et al. (2026) develop identification and local polynomial estimation using signed distance.

The usual procedure fits outcomes against signed distance separately on each side and subtracts the fitted intercepts.

| Experiment | Information at each query | Target |
|---|---|---|
| Unsigned | Outcomes and Euclidean distances | Boundary regression mean |
| Signed | Outcomes, signed distances, query, and known geometry | Boundary treatment effect |

Cattaneo et al. (2026) establish an unsigned common-rule lower scale of \(n^{-1/4}\), and signed-distance bias and stochastic control in probability.

Pointwise accuracy does not control the largest boundary error. Probability bounds alone do not control expected loss on unusual samples.

What does simultaneous recovery cost, and how can an estimator control expected loss?

---

## Key idea

Pair a smooth change in the regression mean with a change in **where observations lie around the query**. Distance can hide the pair.

\[
a_n=\left(\frac{\log n}{n}\right)^{1/4}.
\]

Here \(n\) is sample size and \(a_n\) is the risk normalization.

- **Unsigned:** expected largest boundary error is asymptotically at least a positive multiple of \(a_n\), including rules chosen separately at each query.
- **Signed:** the same lower scale holds with treatment sides and fixed known rectangular geometry.
- **Signed attainment:** a stabilized local polynomial estimator achieves error at most a constant times \(a_n\), under distance identification, uniform first-order bias, and joint expected sampling bounds.

Hiding direction leaves fourth-power information about each local change. Resolving many changes adds the logarithm.

---

## Example

Fix support \(\mathcal X=[-3,3]^2\), treated region \(\mathcal A_1=[-1,1]\times[0,2]\), control region \(\mathcal A_0=\mathcal X\setminus\mathcal A_1\), and treatment boundary \(\mathcal B=\partial\mathcal A_1\).

Place separated disks of radius \(w\) along the middle of the bottom edge. Their centers are \(x_j\).

Each disk carries a binary choice \(\omega_j\): enable a smooth bump of height \(\Delta\), or leave it off. The vector \(\omega\) specifies the observation law \(P_\omega\).

\[
\tau_{P_\omega}(x_j)=\frac{x_j^{(1)}}{16}+\omega_j\Delta .
\]

This is the treatment effect at center \(j\); \(x_j^{(1)}\) is its horizontal coordinate.

The potential outcomes are binary. The control mean is \(1/2\); the treatment mean adds a horizontal slope and the enabled bumps.

Positive signed distance identifies the treated semicircle. It still hides whether an observation lies to the left or right within that semicircle.

That remaining ambiguity lets us hide each bump.

---

## Unsigned model

Let \(Y\) be an outcome, \(X\) a two-dimensional location, and \(P\) their unknown law.

The target is \(\mu_P(x)=\mathbb E_P[Y\mid X=x]\) on the support boundary \(\operatorname{bd}(\mathcal X_P)\).

At query \(x\), the rule receives

\[
V_{n,P}(x)
=
\bigl((Y_i,\lVert X_i-x\rVert_2):1\leq i\leq n\bigr).
\]

These are \(n\) independent observations expressed as outcomes and distances; direction is discarded.

For integer \(q\geq1\) and envelope \(L\geq4\), the class \(\mathcal P_{\mathrm{NP}}(L,q)\) requires:

- Compact support inside \([-L,L]^2\), with a Lipschitz boundary.
- Continuous location density between \(L^{-1}\) and \(L\), keeping local observations available.
- Regression derivatives bounded through order \(q-1\), with the highest derivative Lipschitz, preventing arbitrarily narrow changes.
- Continuous conditional variance between \(L^{-1}\) and \(L\), keeping noise bounded and nondegenerate.

Rules may differ across queries, but are chosen independently of the unknown law.

---

## Signed model

Let \(Y(0)\) and \(Y(1)\) be potential outcomes and \(T\) the treatment indicator.

\[
T=\mathbf 1\{X\in\mathcal A_{1,P}\},
\qquad
Y=TY(1)+(1-T)Y(0).
\]

Treatment follows the known assignment region; \(Y\) is the observed outcome.

The target is \(\tau_P(x)=\mu_{1,P}(x)-\mu_{0,P}(x)\), where \(\mu_{t,P}(x)=\mathbb E_P[Y(t)\mid X=x]\) is the mean for arm \(t\).

At a query on treatment boundary \(\mathcal B_P\), use

\[
D^{\pm}_{P,x}
=
\{\mathbf 1(X\in\mathcal A_{1,P})-\mathbf 1(X\in\mathcal A_{0,P})\}
\lVert X-x\rVert_2
\]

Positive distance denotes treatment; negative distance denotes control. Rules receive outcomes and signed distances, together with the query and known geometry.

The independent-sample class \(\mathcal P_{12}(p,\nu,L)\) requires square support, bounded positive continuous density, and a compact interior boundary curve of controlled length.

Arm means have smooth extensions with bounded Lipschitz derivatives through integer order \(p\geq0\). Variances lie between \(L^{-1}\) and \(L\); conditional \(2+\nu\) moments are bounded by \(L\), with \(\nu\geq2\).

Here \(L\geq4\) is the common envelope. Local geometry must also support fitting on both arms.

---

## Local geometry

A **distance slice** is the part of a circle at exactly radius \(s\) from query \(x\) that lies in arm \(t\):

\[
\{z\in\mathcal A_{t,P}:\lVert z-x\rVert_2=s\}
\]

Here \(z\) is a location. For every boundary query, both arms, and \(0<s\leq L^{-1}\), require \(0<\int_{\text{slice}} f_P(z)\,d\mathcal H^1(z)<\infty\): finite positive density-weighted arc length. The measure \(\mathcal H^1\) measures length along the circle.

A neighborhood condition instead accumulates area over **all radii up to \(h\)**. With \(K_\square(u)=\mathbf 1\{|u|\leq1\}\),

\[
{1\over h^2}\int_{\mathcal A_{t,P}}
K_\square(\{(2t-1)\lVert z-x\rVert_2\}/h)\,dz
\geq L^{-1}.
\]

For every query, both arms, and \(0<h\leq L^{-1}\), each arm occupies a uniformly positive fraction of the local disk; \(dz\) measures planar area.

Finally, the population matrix \(\Psi_{t,P,x}(h)\) of local polynomial regressor second moments, normalized by \(h^{-2}\), satisfies \(\lambda_{\min}(\Psi_{t,P,x}(h))\geq L^{-1}\). This prevents unstable inversion.

In the rectangle, circular arcs give positive slice mass. Both arms retain quarter-disk sectors even at corners, providing neighborhood mass and stable designs.

---

## Identification and approximation

The signed upper bound needs two population assumptions.

**Distance identification** connects signed-distance conditional means to the treatment effect:

\[
\tau_P(x)=\theta_1(0+)-\theta_0(0-).
\]

Here \(\theta_1\) and \(\theta_0\) are conditional outcome means on positive and negative signed distances. Their one-sided limits identify the two arm means at query \(x\). We take this identification input from Cattaneo et al. (2026).

**Uniform first-order bias** controls the difference between the population degree-\(p\) fitted intercepts and \(\tau_P(x)\).

\[
\limsup_{n\to\infty}
\mathrm{BiasRatio}_{p,\nu',L}(h_n)\leq C_b .
\]

The ratio divides the largest population intercept-difference error by \(h_n\), taking the supremum over all boundary queries and all laws in \(\mathcal P_{12}(p,\nu',L)\).

- The same \(C_b\), depending only on \(p,L\), covers every \(\nu'\geq2\).
- The index \(\nu'\) varies the **moment class**: its laws have bounded conditional \(2+\nu'\) moments. The theorem’s \(\nu\) remains fixed.
- The bound must hold along every positive decreasing deterministic sequence \(h_n\to0\) with \(nh_n^2\to\infty\).

Thus approximation error is uniformly \(O(h_n)\), across these classes and bandwidth sequences.

---

## Expected sampling bounds

The third additional assumption is **joint expected sampling bounds**.

Let \(\widehat\Psi\) be the sample counterpart of the population design matrix \(\Psi\).

- \(\mathrm{GramDev}\) is the largest entrywise error \(|\widehat\Psi-\Psi|\), over arms and boundary queries.
- \(\mathrm{ScoreDev}\) is the largest error in local polynomial-weighted **raw-outcome averages**, normalized by \(h_n^{-2}\).

For some constant \(C_m>0\), require

\[
\mathbb E_P^*\!\left[\mathrm{GramDev}_{n,p,P}(h_n)\right]
\leq
C_m
\sqrt{\frac{\log(h_n^{-1})}{n h_n^2}},
\]

\[
\mathbb E_P^*\!\left[\mathrm{ScoreDev}_{n,p,P}(h_n)\right]
\leq
C_m\left\{
\sqrt{\frac{\log(h_n^{-1})}{n h_n^2}}
+
\frac{\log(h_n^{-1})}{n^{(1+\nu)/(2+\nu)}h_n^2}
\right\}.
\]

These bound expected fluctuations over the whole boundary. The second term accommodates outcome tails; \(\mathbb E_P^*\) is outer expectation, the expected-loss convention for boundary suprema.

Both bounds hold eventually, uniformly over \(P\in\mathcal P_{12}(p,\nu,L)\), along every positive deterministic \(h_n\to0\) satisfying \(\frac{n^{(1+\nu)/(2+\nu)}h_n^2}{\log(h_n^{-1})}\to\infty\).

All three additional inputs are assumptions.

---

## Unsigned main result

Let \(\mathcal T_n^{\mathrm{PI}}\) contain unsigned-distance rules chosen separately at each query, independently of the unknown law.

\[
R_n^{\mathrm{PI}}
=
\inf_{\widehat\mu_n^{\mathrm{PI}}\in\mathcal T_n^{\mathrm{PI}}}
\sup_{P\in\mathcal P_{\mathrm{NP}}(L,q)}
\mathbb E_P^*\!\left[
\sup_{x\in\operatorname{bd}(\mathcal X_P)}
\left|\widehat\mu_{n,P}^{\mathrm{PI}}(x)-\mu_P(x)\right|
\right].
\]

The infimum chooses the best rule, the outer supremum chooses the worst law, and the inner supremum selects the largest boundary error.

@informal thm:point-indexed-distance-log-converse: For integer \(q\geq1\) and \(L\geq4\), unsigned-distance rules chosen separately at each query have minimax expected largest boundary error asymptotically at least a positive multiple of \(a_n\).

\[
\liminf_{n\to\infty}
\left(\frac{n}{\log n}\right)^{1/4} R_n^{\mathrm{PI}}
=
\liminf_{n\to\infty}
\frac{R_n^{\mathrm{PI}}}{a_n}
\geq c_{\mathrm{PI}}.
\]

Here \(c_{\mathrm{PI}}>0\) depends on \(q,L\).

One common rule at every query inherits this bound. Choosing rules query by query cannot remove the information barrier.

---

## Signed main result

Let \(\mathcal T_n^{12,\pm}\) contain rules using outcomes, signed distances, the query, and known geometry, chosen independently of the unknown law.

\[
 R^{12,\pm}_n(p,\nu,L)
 =
 \inf_{\widehat\tau_n\in\mathcal T^{12,\pm}_n}
 \sup_{P\in\mathcal P_{12}(p,\nu,L)}
 \mathbb E_P^*\!\left[
 \sup_{x\in\mathcal B_P}|\widehat\tau_{n,P}(x)-\tau_P(x)|
 \right].
\]

This is the best worst-law expected largest treatment-effect error.

@informal thm:cty-a1-a2-point-indexed-log-converse-all-orders: For integer \(p\geq0\), \(\nu\geq2\), and \(L\geq L_0(p)\geq48\), signed-distance minimax expected largest error is asymptotically at least a positive multiple of \(a_n\), already with fixed rectangular geometry.

Under **distance identification**, **uniform first-order bias**, and **joint expected sampling bounds**,

\[
c
\leq
\liminf_{n\to\infty}\frac{R^{12,\pm}_n(p,\nu,L)}{a_n}
\leq
\limsup_{n\to\infty}\frac{R^{12,\pm}_n(p,\nu,L)}{a_n}
\leq C .
\]

The constants satisfy \(0<c\leq C\). The lower bound is unconditional within the law class; the upper bound uses all three additional inputs.

In the rectangle, the loss includes every edge and corner, although the hard changes lie along one edge.

---

## Angular cancellation

Return to disk \(j\) in the rectangle. Let \(r\) be distance from its center and \(\eta_j(x)\) the horizontal direction cosine: negative to the left, positive to the right.

Let \(\varphi_{\mathrm r}(r/w)\) be a smooth radial bump, equal to one at the center and zero beyond radius \(w\).

With fixed location density, enabling the bump adds \(\Delta\varphi_{\mathrm r}(r/w)\) to the pooled treatment mean throughout the disk.

Instead, change density to \((1/36)\{1+t_\Delta(r)\eta_j(x)\}\). A smooth cutoff turns off the tilt near the center; for \(r\geq256\Delta\), use \(t_\Delta(r)=-32\Delta\varphi_{\mathrm r}(r/w)/r\).

- Left–right reflection preserves radius and treatment side. The average of \(\eta_j\) is zero, preserving signed-distance probabilities.
- The horizontal baseline varies by \(r\eta_j/16\). Multiplying it by the tilt contributes \(-2\Delta\varphi_{\mathrm r}(r/w)\eta_j^2\).
- The semicircle average of \(\eta_j^2\) is one-half, exactly canceling the bump.

For binary outcomes, the success probability determines the whole outcome law.

Let \(Q_{j,b}\) be the one-observation outcome–signed-distance law conditional on disk \(j\), under choice \(b\). With \(E=\{(y,u):0<u<2C\Delta\}\) and \(C=128\),

\[
Q_{j,0}(\,\cdot\,\cap E^{c})=Q_{j,1}(\,\cdot\,\cap E^{c}),
\]

Here \(y\) is outcome and \(u\) signed distance. Only the small central positive-distance window distinguishes the choices.

---

## Fourth-power information

Set \(q=p+1\). Smoothness permits the packing

\[
M\geq c\Delta^{-1/q},\qquad
w=A\Delta^{1/q},\qquad
\rho=\frac{\pi w^2}{36}.
\]

Here \(M\) counts separated disks, \(w\) is their radius, \(\rho\) is each disk’s probability, and \(c,A>0\) are fixed construction constants.

Width \(w\) keeps the bump derivatives within the smoothness envelope.

Inside the uncancelled window, the binary success probabilities differ by at most \(\Delta\) and remain between \(1/4\) and \(3/4\).

Kullback–Leibler divergence, written \(\operatorname{KL}\), measures how distinguishable two laws are. The construction gives

\[
\operatorname{KL}(Q_{j,0},Q_{j,1})\leq C_0\frac{\Delta^4}{w^2},
\qquad
\operatorname{KL}(Q_{j,1},Q_{j,0})\leq C_0\frac{\Delta^4}{w^2}.
\]

Here \(C_0>0\) is fixed.

- Squared success-probability separation contributes two powers of \(\Delta\).
- The remaining window has area proportional to \(\Delta^2\), contributing two more.
- Conditioning on the disk divides by its area, proportional to \(w^2\).

The hidden change therefore carries fourth-power information.

---

## Unsigned construction

Use the same bump-and-density pairing on half-disks along the bottom edge of support \(S=[-1/2,1/2]^2\).

Take width \(w_n=a_n^{1/q}\), signal \(\delta_n=c_1a_n\), and \(M_n\) separated centers \(x_j\), with fixed \(c_1>0\) sufficiently small.

\[
\mu_\omega(x)
=
\frac12+\frac{x^{(1)}}{8}
+
\sum_{j=1}^{M_n}\omega_j\,\delta_n\,
\varphi\!\left(\frac{x-x_j}{w_n}\right),
\]

This regression mean has a horizontal baseline and enabled radial bumps; \(\varphi\) is the smooth bump used above.

Given \(X=x\), use the outcome law

\[
\mu_\omega(x)\,N(1,1)+\{1-\mu_\omega(x)\}\,N(0,1).
\]

The notation \(N(m,1)\) means a normal law with mean \(m\) and variance one.

The entire mixture law depends **linearly** on its weight \(\mu_\omega(x)\). The same angular cancellation therefore preserves the full outcome–distance law outside the central window.

One-observation divergence is at most \(C_{\mathrm{KL}}\delta_n^4\), with fixed \(C_{\mathrm{KL}}>0\). For \(n\) observations, the construction ensures \(n\,C_{\mathrm{KL}}\,\delta_n^{4}\le\alpha\log M_n\), with \(0<\alpha<1/8\).

How do these local ambiguities force an error somewhere when every query reuses one sample?

---

## Independent local blocks

Distance data at different queries share observations. Independent pointwise tests do not establish a uniform lower bound.

For the argument, draw a Poisson number of observations with mean \(2n\). Splitting observations among disjoint cells produces independent blocks conditional on the binary choices.

Let \(Z_j\) collect raw observations in cell \(j\), and \(Z_0\) collect the background. Each cell law depends only on its own choice; the background law is common.

Decoder \(j\), which tries to recover choice \(j\), receives:

- Its own block compressed to outcomes and distances, denoted \(S_j=c_j(Z_j)\).
- Every other block and the background with raw locations.

For signed rules, the compression retains signed distance. Other raw blocks let decoder \(j\) reconstruct their distances from its query.

This enlarged view reproduces every admissible query rule while keeping its own angular information hidden.

The decoders have different raw-data views. We must compare their **joint success**, not multiply their individual success probabilities.

---

## Coupled alternatives

For this argument, \(Q_{j,b}\) denotes the compressed **sample-block** law under choice \(b\).

Its overlap is \(\rho_j=1-\lVert Q_{j,0}-Q_{j,1}\rVert_{\mathrm{TV}}\), where total variation is the largest probability difference across events.

Construct a pair of raw blocks \((Z_j^0,Z_j^1)\) with the correct laws for choices zero and one, whose compressions agree with probability at least \(\rho_j\).

First couple the compressed laws on their common probability mass. Then draw raw locations conditional on each compressed block. This preserves both raw-block laws.

Draw these pairs independently across cells, and draw one common background \(Z_0\).

For any choice vector \(\omega\), select

\[
Z_j(\omega)=Z_j^{\omega_j},
\qquad 1\leq j\leq M .
\]

This selects the appropriate raw alternative in each cell. Every fixed \(\omega\) has exactly its original product experiment.

We can therefore compare all choice vectors using **one realized array of paired blocks**.

---

## Two-cell pairing

Fix a coupled array with two cells. Suppose cell 1 overlaps: \(c_1(Z_1^0)=c_1(Z_1^1)=S_1\).

For either fixed choice \(b\in\{0,1\}\) in cell 2:

| Choice vector | Decoder 1 receives | Decoder 2 receives |
|---|---|---|
| \((0,b)\) | \((S_1,Z_2^b,Z_0)\) | \((c_2(Z_2^b),Z_1^0,Z_0)\) |
| \((1,b)\) | \((S_1,Z_2^b,Z_0)\) | \((c_2(Z_2^b),Z_1^1,Z_0)\) |

Decoder 2 may see different raw information. **Decoder 1 sees exactly the same input**, while its true choice changes.

Its guess cannot be correct in both alternatives. Consequently, both decoders can be correct in at most one alternative of each pair.

Pair \((0,0)\) with \((1,0)\), and \((0,1)\) with \((1,1)\): at most half the four choice vectors have simultaneous success.

For any number of cells, the same argument applies: after fixing the coupled array, choose one overlapping coordinate and pair every vector with the vector that flips that coordinate.

Whenever an overlap occurs, at least half the choice vectors incur an error somewhere.

---

## Uniform decoding failure

The overlap events are independent because the **coupled cell pairs** were drawn independently.

The chance that every cell avoids overlap is at most \(\prod_{j=1}^M(1-\rho_j)\).

On that event, simultaneous success can be as high as one. Otherwise, the pairing argument bounds success by one-half. Averaging over coupled arrays and uniform binary choices gives

\[
 \Pr\{\widehat\Omega_j=\Omega_j\text{ for every }j\}
 \leq
 \frac12\left\{1+\prod_{j=1}^M(1-\rho_j)\right\}.
\]

Here \(\Omega_j\) is the true choice and \(\widehat\Omega_j\) its decoded value.

If each block has divergence at most \(\kappa\log M\), with \(0\leq\kappa<1\), the standard divergence-to-overlap bound gives \(\rho_j\geq\frac12\exp\{-\kappa\log M\}\).

Many chances to overlap then imply

\[
 \Pr\{\text{at least one decoding error}\}
 \geq
 \frac12\left[1-\exp\{-M^{1-\kappa}/2\}\right].
\]

This lower bound stays away from zero as \(M\) grows. It allows all the additional raw information in the decoders’ different views.

---

## Rate calibration

A signed Poisson cell block has expected size \(2n\rho\).

Its conditional one-observation divergence is at most a constant times \(\Delta^4/w^2\). Since \(\rho=\pi w^2/36\), multiplying by expected block size cancels \(w^2\).

Block information is therefore at most a constant times \(n\Delta^4\).

The packing has \(M\asymp\Delta^{-1/q}\). Calibrate the signal by

\[
n\Delta^4\asymp \log M,
\qquad\text{hence}\qquad
\Delta\asymp \left(\frac{\log n}{n}\right)^{1/4}.
\]

These relations choose a signal comparable to \(a_n\); a sufficiently small constant keeps block divergence within the simultaneous-testing budget.

- An estimate accurate within half the center separation would decode every choice.
- An error somewhere therefore forces expected maximum estimation error at least a positive multiple of \(a_n\).
- Keeping the first \(n\) Poisson observations recovers the original experiment; the probability of a sample shortage is exponentially small.

Smoothness determines how many bumps fit. Angular cancellation determines the fourth root. Simultaneous recovery determines the logarithm.

---

## Local polynomial estimator

For signed attainment, fit degree-\(p\) polynomials separately on the two arms within distance \(h\).

Use \(r_p(u)=(1,u,\ldots,u^p)^\top\), with \(u\) equal to signed distance divided by \(h\). The arm intervals are \(I_1=[0,\infty)\) and \(I_0=(-\infty,0)\).

Winsorization replaces outcomes outside \([-B,B]\) by the nearest endpoint; denote it by \(\psi_B\) and take \(B(h)=h^{-1/3}\).

\[
\widehat m^B_{t,x}(h)
 =
 {1\over nh^2}\sum_{i=1}^n
 \mathbf 1\{D^{\pm}_{P,x,i}\in I_t\}K_\square(D^{\pm}_{P,x,i}/h)
 r_p(D^{\pm}_{P,x,i}/h)\psi_{B(h)}(Y_i).
\]

This vector averages polynomial-weighted winsorized outcomes. The factor \(h^{-2}\) normalizes a two-dimensional neighborhood.

The sample matrix \(\widehat\Psi\) uses the same weights with regressor outer products. Set \(\widehat\beta^B=\widehat\Psi^{-1}\widehat m^B\) when its smallest eigenvalue is at least \((2L)^{-1}\); otherwise use zero.

With \(e_1=(1,0,\ldots,0)^\top\) selecting the intercept, estimate

\[
\widehat\tau^{12,\mathrm{LP}}_{n,h}(x)
 =
 \max\!\left\{-2L,\min\!\left\{2L,
 e_1^\top(\widehat\beta^B_{1,x}(h)-\widehat\beta^B_{0,x}(h))
 \right\}\right\}.
\]

This subtracts the fitted intercepts and clips the effect estimate to its bounded target range.

---

## Residual control

Let \(\beta^*_{t,P,x}(h)\) be the population coefficient fitted using raw outcomes. Its polynomial-weighted raw residual has mean zero.

Write \(\operatorname{score}^{B}_{t,x,h}\) for the sample weighted residual vector: winsorized outcomes minus predictions from \(\beta^*\).

On the guarded branch, coefficient error is the inverse sample design matrix times this residual vector. The eigenvalue guard bounds amplification.

The moment envelope bounds the absolute conditional winsorization remainder by \(LB^{-3}\), for \(B\geq1\) and \(\nu\geq2\).

For centered fluctuations, we establish

\[
\mathbb E_{P^n}^{*}\!\left[
\sup_{t\in\{0,1\},\,x\in\mathcal B_P}
\left\|
\operatorname{score}^{B}_{t,x,h}
-\mathbb E_{P^n}\!\left[\operatorname{score}^{B}_{t,x,h}\right]
\right\|
\right]
\leq
C\left\{
\sqrt{\frac{\log(B/h)}{n h^2}}
+
\frac{B\log(B/h)}{n h^2}
\right\}.
\]

Here \(P^n\) is the independent sample law and \(C=C(p,L)\). This bounds expected residual fluctuations across both arms and the entire boundary.

We apply van der Vaart and Wellner (1996) for maxima of bounded sample averages. Winsorization bounds individual contributions; local windows have probability proportional to \(h^2\).

This proved bound supplies the winsorized residual component. The theorem assumes the joint sampling package; the attainment argument uses its Gram bound.

---

## Expected risk and tuning

Expected largest error has four contributions:

| Contribution | Control |
|---|---|
| Population approximation, \(O(h)\) | Uniform first-order bias |
| Mean tail remainder, \(O(B^{-3})\) | Conditional outcome moments |
| Centered residual fluctuations | Proved expected maximal bound |
| Unstable sample designs | Expected Gram bound and clipping |

Small Gram deviation activates every inversion guard. On other samples, clipping bounds the largest loss by \(4L\). Expected Gram control therefore also pays for unusual samples.

Choose \(h_n=a_n\) and \(B_n=a_n^{-1/3}\). The bandwidth balances first-order bias with \(\{\log(h_n^{-1})/(n h_n^2)\}^{1/2}\), while \(B_n^{-3}=a_n\).

Every contribution is at most a constant times \(a_n\):

\[
\sup_{P\in\mathcal P_{12}(p,\nu,L)}
\mathbb E_P^*\!\left[
\sup_{x\in\mathcal B_P}
\left|\widehat\tau^{12,\mathrm{LP}}_{n,h_n}(x)-\tau_P(x)\right|
\right]
\leq C a_n .
\]

This bounds the estimator’s expected largest treatment-effect error uniformly over the law class, eventually in \(n\).

@informal prop:cty-a1-a2-winsorized-expected-outer-upper: For integer \(p\geq0\), \(\nu\geq2\), and \(L\geq4\), distance identification, uniform first-order bias, and joint expected sampling bounds give the stabilized estimator expected largest boundary error at most \(Ca_n\) eventually.

In the rectangle, this covers every edge and corner. With the lower bound, it gives the matched signed rate for \(L\geq L_0(p)\).

---

## Open questions

- Establish a matching unsigned upper bound.
- Derive all three signed-distance analytic inputs within the same law class.
- Extend the analysis to other metrics, kernels, boundary regularity, and losses suited to inference.

The common lower scale alone does not rank achievable unsigned and signed risks.

---

## Takeaways

- **Hidden direction:** angular density reweighting cancels a smooth mean bump in the full distance-observation law outside a small central window.
- **Uniform difficulty:** fourth-power local information and many separated choices produce \(a_n=(\log n/n)^{1/4}\); coupling and pairing force an error somewhere despite the decoders’ different raw-data views.
- **Expected-risk attainment:** under distance identification, uniform first-order bias, and joint expected sampling bounds, winsorization, guarded inversion, and clipping attain signed error at most a constant times \(a_n\).

---

## Appendix: Common-map lower bound

One common unsigned-distance rule incurs the logarithmic lower scale over the full nonparametric class.

@formal thm:cty-same-class-log-converse

---

## Appendix: Point-indexed unsigned lower bound

Allowing a separate unsigned-distance rule at each query preserves the logarithmic lower scale.

@formal thm:point-indexed-distance-log-converse

---

## Appendix: Signed-distance lower bound

The signed-distance logarithmic lower bound already holds with one fixed known rectangular geometry.

@formal thm:cty-a1-a2-point-indexed-log-converse-all-orders

---

## Appendix: Conditional matched rate

Under the three analytic inputs, signed-distance minimax expected risk is bounded above and below on the \(a_n\) scale.

@formal thm:cty-a1-a2-winsorized-matched-frontier
