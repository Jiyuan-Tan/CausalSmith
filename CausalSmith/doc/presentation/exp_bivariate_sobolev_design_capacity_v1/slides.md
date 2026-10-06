# Balancing Smooth Pairwise Effects in Randomized Experiments

One fair assignment rule improves treatment-effect precision by balancing smooth outcome predictors, without knowing their smoothness.

---

## Motivation

We observe covariates for \(n\) experimental units and want to estimate the average treatment effect precisely.

Let \(O_i(0),O_i(1)\) be unit \(i\)’s potential outcomes. Assignment signs \(Z_i=1\) and \(Z_i=-1\) select treatment and control.

Each unit receives treatment with probability one half, conditional on all covariates. The Horvitz–Thompson estimator is

\[
\widehat T_P=\frac2n\sum_{i=1}^n Z_iO_i((Z_i+1)/2),
\]

Here \(P\) is the population law. The estimator weights observed outcomes by their inverse assignment probabilities and targets \(\vartheta(P)=\mathbb E_P[O(1)-O(0)]\).

Correlating assignments can reduce variance by balancing predictors of outcomes. Which predictors should we balance?

---

## Research question

The standard approach balances a selected list of covariate features.

Harshaw et al. (2024) use the Gram–Schmidt walk, a randomized rounding method that creates fair assignments with feature-balance guarantees.

The closest econometric comparison is Cytrynbaum (2026):

- Excess variance equals scaled expected squared imbalance in the conditional potential-outcome midpoint mean.
- For smooth main and pair effects, a structured design has an upper bound of order \((d^2\log n/n)^{s\wedge1}\).
- For a single bivariate component, the lower exponent is \(n^{-s}\).

Here \(d\) is covariate dimension and \(s\) measures smoothness.

Coordinate averages miss interactions; a finite feature list leaves finer variation uncontrolled.

Can one fair rule control all smooth pairwise predictors, and is the logarithmic loss necessary?

---

## Key idea

Order features from low to high frequency, giving earlier features stronger balance.

Under independent uniform covariates, centered main and pair effects share one total smoothness budget.

\[
B=\binom d2,
\qquad
a_s(n,d)=\min\{1,(B/n)^s\},
\qquad n,d\geq2,\quad 0<s\leq1.
\]

Here \(B\) counts coordinate pairs. The scale \(a_s(n,d)\) describes the smallest possible worst-case excess variance after multiplying variance by \(n\).

- When \(B<n\), the scale is \((B/n)^s\).
- When \(B\geq n\), it stays bounded away from zero.
- One fair, outcome-independent rule attains this scale for every \(s\).

A shared random shift separates frequency losses. Ordered rounding protects low frequencies longer.

---

## Example

Take two independent uniform covariates and the centered pair predictor
\(m(x)=\frac{2}{C_0}\cos(\pi x_1)\cos(\pi x_2)\), where \(C_0=\sqrt{48+32\pi^2}\).

It averages to zero in either coordinate: coordinate averages cannot capture it.

Let the conditional treatment effect be \(\tau(x)=0.2+0.1\sqrt2\sin(2\pi x_1)\), and generate outcomes by

\[
Y_i(0)=m(X_i)-\frac{\tau(X_i)}2+\epsilon_i(0),
\qquad
Y_i(1)=m(X_i)+\frac{\tau(X_i)}2+\epsilon_i(1).
\]

The errors are independent standard Gaussians, independent of covariates. The mean treatment effect is \(0.2\); treatment-effect variation and outcome noise give benchmark \(V^*=4.01\).

For the Horvitz–Thompson estimate \(\widehat\theta\),
\(n\operatorname{Var}(\widehat\theta)-V^*=\frac4n\,\mathbb E\!\left[\left(\sum_{i=1}^n Z_i m(X_i)\right)^2\right]\).

Thus balancing this pair predictor directly improves actual treatment-effect precision.

---

## Model

Units are sampled independently. Each covariate vector \(X_i\) has \(d\) independent uniform coordinates on \([0,1]\).

The prognostic function \(m\) is the conditional mean of the potential-outcome midpoint, with population mean zero.

\[
m(x)=\sum_{j=1}^d g_j(m)(x_j)
+\sum_{j<\ell}g_{j\ell}(m)(x_j,x_\ell)
\]

Here \(g_j(m)\) is coordinate \(j\)’s main effect; \(g_{j\ell}(m)\) is the interaction between coordinates \(j\) and \(\ell\).

Main effects average to zero. Pair effects average to zero in either coordinate. Main and pair effects account for prognosis exactly.

In our example, both main effects vanish and \(g_{12}(m)=m\).

Assignment uses all original covariates and independent randomness, with \(\mathbb E_\pi[Z_i\mid X]=0\) for every unit. It uses neither outcomes nor the unknown outcome model.

---

## Smoothness budget

All components share one budget:

\[
\sum_{j=1}^d N_{1,s}(g_j(m))^2
+\sum_{j<\ell}N_{2,s}(g_{j\ell}(m))^2
\leq 1,
\]

The quantities \(N_{1,s}\) and \(N_{2,s}\) are nonperiodic Sobolev restriction norms for one- and two-dimensional functions.

They measure magnitude and roughness through the smallest Sobolev norm of an extension off the component’s cube. Larger \(s\) penalizes rapid oscillation more strongly.

Pooling fixes total component strength while allowing it to move across coordinates and pairs.

Write \(\mathcal H_{d,s}\) for the centered main-and-pair functions satisfying this budget.

In our example, the budget is \(N_{2,s}(m)^2\leq1\). The normalization \(C_0\) ensures membership for every \(0<s\leq1\).

---

## Worst-case precision

Let \(\mathcal D_{n,d,s}\) be the fair, outcome-independent assignment rules using all original covariates.

Our objective is

\[
R_s(n,d)
=
\inf_{\pi\in\mathcal D_{n,d,s}}
\sup_{m\in\mathcal H_{d,s}}
\frac{4}{n}
\mathbb E_{X,Z}
\left[
\left(\sum_{i=1}^{n}Z_i m(X_i)\right)^2
\right].
\]

The signed sum is prognostic imbalance between treatment and control. Its scaled expected square is the loss \(\mathcal L_{n,d,s}(\pi,m)\).

The order matters:

- Choose one assignment rule \(\pi\).
- Evaluate its worst population predictor \(m\).
- Average over covariate sampling and assignment inside the loss.

The adverse function is fixed across samples; it cannot be selected after observing the covariates.

---

## Main result

@informal thm:log-free-bivariate-capacity: For \(n,d\geq2\) and \(0<s\leq1\), under independent uniform sampling and the centered pooled main-and-pair budget, one fair, outcome-independent rule attains minimax scaled excess within uniform constant factors of \(a_s(n,d)\).

\[
c_1a_s(n,d)
\leq c_sa_s(n,d)
\leq R_s(n,d)
\leq \sup_{m\in\mathcal H_{d,s}}
       \mathcal L_{n,d,s}(\pi^\star_{n,d},m)
\leq3072a_s(n,d).
\]

Here \(\pi^\star_{n,d}\) is our assignment rule. The positive lower constants satisfy \(0<c_1\leq c_s\), uniformly over \(0<s\leq1\).

The same rule works for every smoothness, including \(s=1\). The matched characterization has no logarithmic factor.

In our example, \(B=1\): scaled excess is at most \(3072n^{-s}\). The matching lower bound concerns the worst legal predictor.

How can finitely many balancing inputs control an entire smoothness class?

---

## Reflection

Reflect the cube to express smoothness as a frequency budget.

Let \(F(y)=m(b_d(y))\), where \(b_d\) folds each coordinate of \([0,2)\) onto \([0,1]\). Addition on this enlarged domain wraps around modulo two.

An integer vector \(k\) specifies a Fourier frequency. Its coefficient is \(\widehat F(k)\); \(\operatorname{supp}(k)\) contains its nonzero coordinates.

The complexity \(t(k)=\|k\|_2^2/|\operatorname{supp}(k)|\) measures average squared frequency across those coordinates.

\[
\sum_{\substack{k\in\mathbb Z^d\\
1\leq|\operatorname{supp}(k)|\leq2}}
(1+\pi^2t(k))^s|\widehat F(k)|^2
\leq1.
\]

This bounds weighted squared Fourier coefficients by the original smoothness budget. Centering removes the constant frequency; main-and-pair structure leaves only one- and two-coordinate frequencies.

Our example has four frequencies \(k=(\pm1,\pm1)\), all with \(t(k)=1\).

---

## Common random shift

Independently lift each observed coordinate to either \(X_{ij}\) or \(2-X_{ij}\), then add one shared uniform shift \(T\):

\[
W_i=\operatorname{lift}(X_i,\text{reflection coins})+T,
\]

The transformed covariates \(W_i\) supply features for original unit \(i\). Addition wraps around modulo two, and \(F(W_i-T)=m(X_i)\).

Uniform sampling makes the entire transformed sample \(W\) independent of \(T\). Generate assignments using \(W\).

Let \(e_k(w)=\exp(\mathrm i\pi k\cdot w)\) combine the cosine and sine at frequency \(k\). Then

\[
\mathbb E\left|\sum_{i=1}^n Z_i m(X_i)\right|^2
=
\sum_{k\in\mathbb Z^d}
|\widehat F(k)|^2\,
\mathbb E\left|\sum_{i=1}^n Z_i e_k(W_i)\right|^2.
\]

Averaging the shared random phase removes cross-frequency terms. Prognostic imbalance becomes a sum of separate frequency losses, even though assignment depends on the sample.

---

## Ordered balancing

When \(B<n\), order one- and two-coordinate frequencies by increasing \(t(k)\).

For each frequency, use the cosine and sine rows

\[
\sqrt2\cos(\pi k^{\mathsf T}W_i),
\qquad
\sqrt2\sin(\pi k^{\mathsf T}W_i).
\]

These are the real components of frequency imbalance for unit \(i\). Let \(a_h\) collect the \(h\)-th feature across units.

Our example uses cosine and sine of the sum and difference of its two transformed coordinates.

Supply the first \(K=\lfloor n/4\rfloor\) rows to rounding:

- Start fractional assignments at \(u=0\).
- With \(r\) coordinates still between \(-1\) and \(1\), protect the first \(\lfloor r/4\rfloor\) rows.
- Move orthogonally to those rows until a coordinate reaches a boundary.
- Refresh the protected prefix when the active count has halved.

As units become fixed, fewer constraints can be protected. Earlier frequencies retain protection longer.

---

## Fair boundary moves

A permitted direction \(v_b\) changes only active coordinates and preserves protected row sums.

Let \(\delta_b^+\) and \(\delta_b^-\) be distances to the first boundary in its positive and negative directions.

\[
u\leftarrow
\begin{cases}
u+\delta_b^+v_b,
&\text{with probability }\displaystyle\frac{\delta_b^-}{\delta_b^++\delta_b^-},\\[6pt]
u-\delta_b^-v_b,
&\text{with probability }\displaystyle\frac{\delta_b^+}{\delta_b^++\delta_b^-}.
\end{cases}
\]

These probabilities make the expected increment zero. Starting at zero therefore preserves mean-zero assignments.

Directions form an orthonormal basis. Selecting them with probabilities proportional to \(1/(\delta_b^+\delta_b^-)\) equalizes their conditional variance contributions.

Each move fixes a coordinate. The last few coordinates are rounded while preserving their means.

Every original unit receives a fair sign and retains its estimator weight \(2/n\).

---

## Balance at every scale

If every entry of ordered row \(a_h\) has magnitude at most \(\Lambda\), rounding guarantees

\[
\mathbb E[Z_i]=0
\qquad(1\leq i\leq n),
\qquad
\mathbb E\!\left[(a_h^{\mathsf T}Z)^2\right]
\leq32\Lambda^2\min\{h,n\}
\qquad(h\geq1).
\]

Here \(h\) is the row’s position, and \(a_h^{\mathsf T}Z\) is its final signed imbalance. For cosine and sine rows, \(\Lambda=\sqrt2\).

Why does earlier position buy stronger balance?

- Row \(h\) is protected while at least \(4h\) coordinates remain active.
- After protection ends, row variance is bounded by the remaining coordinate variance budget.
- Fewer than \(4h\) coordinates remain, so that budget is proportional to \(h\).

The remaining budget is counted once across all subsequent phases. Charging it separately in each phase would lose this control.

The guarantee includes rows beyond the finite supplied prefix.

---

## From balance to variance

At most \(12Bt(k)\) real rows occur through complexity \(t(k)\). Thus row position grows with interaction count and frequency complexity.

Combining ordered balance with the common-shift identity gives

\[
\mathcal L_{n,d,s}(\pi^\star_{n,d},m)
\leq
3072
\sum_{\substack{k\in\mathbb Z^d\\
1\leq|\operatorname{supp}(k)|\leq2}}
|\widehat F(k)|^2\min\{1,(B/n)t(k)\}.
\]

Each squared coefficient pays for its frequency’s remaining imbalance.

For \(0<s\leq1\), this charge is at most \(a_s(n,d)(1+\pi^2t(k))^s\). The weighted coefficient budget therefore bounds the sum by \(a_s(n,d)\).

In our example, only \(t(k)=1\) contributes. With \(B=1\), its coefficient energy receives a \(1/n\) charge.

Smoothness enters this bound; the assignment rule does not use \(s\).

When \(B\geq n\), independent fair signs give loss at most \(4\), attaining the saturated scale.

---

## A hard function family

To show necessity, spread one smoothness budget across many pair features.

Choose a frequency cutoff \(L\) of order \(\max\{1,\sqrt{n/B}\}\), with enough slack that \(M=BL^2\geq4096n\).

Before sampling covariates, draw independent coefficient signs \(\xi_\alpha\). For \(\alpha=(j,h,k,\ell)\), with \(j<h\) and \(1\leq k,\ell\leq L\), define

\[
V_\alpha(x)=2\cos(\pi kx_j)\cos(\pi\ell x_h),
\qquad
m_\xi(x)=\frac{1}{C_0L^s\sqrt M}\sum_\alpha\xi_\alpha V_\alpha(x).
\]

The vector \(V(x)\) collects all \(M\) features. The denominator shares the budget across them; \(C_0=\sqrt{48+32\pi^2}\).

Every coefficient-sign realization is centered and belongs to \(\mathcal H_{d,s}\).

\[
\mathbb E\!\left[V(X_1)V(X_1)^{\mathsf T}\right]=I_M,
\]

The identity matrix \(I_M\) means each feature has unit second moment and distinct features are orthogonal, including features sharing a coordinate.

---

## Energy and cancellation

Write \(v_i=V(X_i)\), let \(\boldsymbol v=(v_1,\ldots,v_n)\), and use \(r_0=M\) for the feature dimension in this calculation.

For any candidate assignment signs \(z\),

\[
\left\|\sum_{i=1}^n z_i v_i\right\|_2^2
=\mathsf D_{\rm row}(\boldsymbol v)
+\mathsf O_{\rm row}(\boldsymbol v,z).
\]

Here \(\mathsf D_{\rm row}(\boldsymbol v)=\sum_i\|v_i\|_2^2\) is total feature energy.

The cross-unit term is
\(\mathsf O_{\rm row}(\boldsymbol v,z)=\sum_{i\ne i'}z_i z_{i'}\langle v_i,v_{i'}\rangle\).
Only this term changes when signs change.

Define \(\mathsf M_{\rm off}(\boldsymbol v)=\max_z|\mathsf O_{\rm row}(\boldsymbol v,z)|\): the largest possible magnitude of cancellation.

The identity second-moment matrix gives expected total energy \(nr_0=nM\). Even the best signing leaves at least total energy minus \(\mathsf M_{\rm off}\).

How large can cancellation become when signs adapt to all observed vectors?

---

## Absolute projections

For a group of \(n_{\rm loc}\) units, let \(\boldsymbol v_{\rm loc}\) collect its feature vectors.

Let \(\mathsf K_{\rm row}\) be the largest signed-sum norm, and let \(\mathcal B_{\rm dir}\) be the Euclidean unit ball of directions.

\[
\mathsf K_{\rm row}(\boldsymbol v_{\rm loc})
=
\sup_{u_{\rm dir}\in\mathcal B_{\rm dir}}
\sum_{i=1}^{n_{\rm loc}}|\langle u_{\rm dir},v_i^{\rm loc}\rangle|.
\]

For any direction \(u_{\rm dir}\), signs can align all projections. Maximizing over unit directions gives the largest norm.

Bartlett and Mendelson (2002) supply the contraction inequality: after centering and introducing independent fair signs, it controls this supremum of absolute projections by the corresponding linear-projection supremum.

The identity second-moment matrix gives \(\mathbb E|\langle u_{\rm dir},v\rangle|\leq\|u_{\rm dir}\|_2\). Independent fair signs give signed-sum second moment \(n_{\rm loc}r_0\).

Consequently,

\[
\mathbb E\mathsf K_{\rm row}(\boldsymbol v_{\rm loc})
\leq n_{\rm loc}+4\sqrt{n_{\rm loc}r_0}.
\]

The first term bounds population absolute projections; the square-root term bounds how much choosing directions after sampling can add.

---

## Independent groups

Split units randomly into a left group and a right group, independently of their feature vectors. Their sizes are \(n_{\rm left}\) and \(n_{\rm right}\).

Let \(\mathsf H_{\rm cross}\) maximize, over all signed sums \(u_{\rm dir}\) of right-group vectors, the quantity
\(\sum_{i=1}^{n_{\rm left}}|\langle u_{\rm dir},v_i^{\rm left}\rangle|\).

This controls every signed cross-group inner product: left-group signs cannot gain more than aligning these projections.

Conditional on the right group, its signed sums form a finite direction set. The same contraction inequality controls the absolute-projection supremum over that set.

Independence and the preceding signed-norm bound yield

\[
\begin{aligned}
\mathbb E\mathsf H_{\rm cross}(\boldsymbol v_{\rm left},\boldsymbol v_{\rm right})
\leq{}&
n_{\rm left}n_{\rm right}
+4n_{\rm left}\sqrt{n_{\rm right}r_0}\\
&+4n_{\rm right}\sqrt{n_{\rm left}r_0}.
\end{aligned}
\]

This bounds cancellation across independent groups using their sizes and feature dimension.

Every ordered pair of distinct units falls from left to right with probability \(1/4\). Averaging over random splits therefore controls the full cross-unit term with a factor of four.

---

## Unavoidable feature imbalance

The independent-group argument bounds the maximum cross-unit cancellation by

\[
\mathbb E\mathsf M_{\rm off}(\boldsymbol v)
\leq4\mathbb E_{\boldsymbol v}\mathbb E_\eta
\mathsf M_{\rm cross}(\boldsymbol v,\eta)
\leq n^2+16n\sqrt{nr_0}.
\]

Here \(\eta\) denotes the random split, and \(\mathsf M_{\rm cross}\) is the largest absolute signed inner product between its groups.

Compare this with total expected energy \(nr_0=nM\).

When \(r_0=M\geq4096n\), the two cancellation terms satisfy
\(n^2\leq nr_0/4096\) and \(16n\sqrt{nr_0}\leq nr_0/4\).
Together they remove at most half the expected energy.

Thus

\[
\mathbb E_X
 \min_{z\in\{-1,1\}^n}
 \left\|\sum_i z_iV(X_i)\right\|_2^2
\geq\frac{nM}{2}.
\]

Even signs optimized after seeing every covariate cannot cancel enough of the many orthogonal feature directions. Every randomized assignment rule pays at least this much total imbalance.

---

## From imbalance to necessity

Averaging independent coefficient signs removes cross-feature terms:

\[
\mathbb E_\xi\mathcal L_{n,d,s}(\pi,m_\xi)
=\frac{4}{nC_0^2L^{2s}M}
 \mathbb E_{X,Z}
 \left\|\sum_i Z_iV(X_i)\right\|_2^2.
\]

The left side averages loss over legal predictors chosen before sampling. The right side is normalized total feature imbalance under design \(\pi\).

Unavoidable feature imbalance leaves loss at least \(2/(C_0^2L^{2s})\). The cutoff makes this comparable to \(a_s(n,d)=\min\{1,(B/n)^s\}\).

@informal thm:full-design-lower: For \(n,d\geq2\) and \(0<s\leq1\), every fair, outcome-independent design has prior-average loss at least \(c_sb_s(n,d)\) on legal pair-cosine functions with independent coefficient signs drawn before sampling.

Here \(b_s(n,d)=a_s(n,d)\).

Worst-case loss dominates this average over fixed legal functions. Taking the infimum over designs preserves the lower bound.

---

## Causal interpretation

The variance interpretation covers arbitrary square-integrable potential outcomes.

Let \(\mathcal Q_{d,s}\) contain population laws \(P\) with uniform covariates \(U\), finite potential-outcome second moments, and conditional midpoint mean \(m_P\in\mathcal H_{d,s}\).

Their benchmark is

\[
\mathsf V(P)
=\operatorname{Var}_P\!\left(
 \mathbb E_P[O(1)-O(0)\mid U]\right)
+2\mathbb E_P\operatorname{Var}_P(O(1)\mid U)
+2\mathbb E_P\operatorname{Var}_P(O(0)\mid U),
\]

It combines conditional treatment-effect variation with conditional outcome noise.

Cytrynbaum (2026) supplies the identity
\(n\operatorname{Var}_{P,\pi}(\widehat T_P)-\mathsf V(P)=\mathcal L_{n,d,s}(\pi,m_P)\).

Because the Gaussian construction realizes every permitted midpoint function,

\[
\inf_{\pi\in\mathcal D_{n,d,s}}
 \sup_{P\in\mathcal Q_{d,s}}\mathcal V_n(\pi,P)
=R_s(n,d),
\]

Here \(\mathcal V_n(\pi,P)\) is scaled variance above \(\mathsf V(P)\).

Our imbalance characterization is exactly a minimax characterization of actual causal-estimation excess variance.

---

## Dimension frontier

Fix smoothness \(s\in(0,1]\), and let \(d_n\geq2\) be any integer dimension sequence.

\[
R_s(n,d_n)\longrightarrow0
\quad\Longleftrightarrow\quad
\frac{\binom{d_n}{2}}n\longrightarrow0
\quad\Longleftrightarrow\quad
d_n=o(\sqrt n).
\]

The final condition means dimension divided by \(\sqrt n\) tends to zero.

Ordered balancing supplies sufficiency. The independent coefficient prior supplies necessity.

The relevant sample-size comparison is with the number of coordinate pairs under one fixed total smoothness budget.

For the Gaussian outcome family, this is exactly the condition for worst-case \(n\operatorname{Var}(\widehat\theta)-4.01\) to vanish.

---

## Open questions

- Attaining the same scale under nonuniform covariate densities.
- Controlling higher-order interactions, approximation error in pairwise structure, and unknown prognostic intercepts.
- Certifying fairness and imbalance under finite-precision arithmetic, with quantified computational cost.

---

## Takeaways

- Under independent uniform covariates and the centered pooled main-and-pair budget, minimax scaled excess variance is comparable to \(\min\{1,(B/n)^s\}\).
- A common shift separates frequencies. Ordered rounding protects low frequencies longer and counts the remaining variance budget once, giving one fair rule for every \(0<s\leq1\).
- Many orthogonal pair features retain substantial energy under every signing. An independent coefficient prior turns that fact into necessity: vanishing worst-case scaled excess requires and permits \(d=o(\sqrt n)\) at fixed smoothness.

---

## Appendix: Log-free capacity and dimension frontier

Uniform finite-sample bounds, simultaneous attainment, causal interpretation, and the exact dimension condition.

@formal thm:log-free-bivariate-capacity

---

## Appendix: Full-design capacity lower bound

An independent prior certifies the matching lower bound against every admissible assignment rule.

@formal thm:full-design-lower

---

## Appendix: Pair-cosine prior

The exact cutoff and normalization construct the legal function family used in the converse.

@formal def:cosine-prior
