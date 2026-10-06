# Testing Whether Treatment Effects Are Constant

An average treatment benefit can hide differences across groups; we determine how large those differences must be to detect them reliably.

---

## Research question

Let \(P\) be the population law, \(\tau_P(x)\) the conditional mean treatment effect at covariate value \(x\), and \(\lambda\) uniform probability measure on \([0,1]\).

\[
\bar\tau_P=\int_{[0,1]}\tau_P(x)\,d\lambda(x),
\qquad
d(P)
=
\left(
\int_{[0,1]}\{\tau_P(x)-\bar\tau_P\}^{2}\,d\lambda(x)
\right)^{1/2}.
\]

The average effect is \(\bar\tau_P\). The distance \(d(P)\) measures how much conditional mean effects vary across covariates.

The null \(d(P)=0\) permits an unknown, nonzero common effect.

How large must \(d(P)\) be to control false rejection and missed detection uniformly over populations?

---

## Standard approaches

A natural approach estimates the two conditional arm means and tests whether their difference varies.

- Crump et al. (2008) use a sieve Wald test with asymptotic calibration.
- Lu and Song (2026) use orthogonal conditional moments, bounded conditional variances, and conditions supporting accurate nuisance estimation.

Under weaker restrictions, two problems remain:

- Infinite outcome variance destabilizes quadratic statistics.
- Assignment and baseline approximation errors can imitate effect variation.

Can a correction computed directly from observed records control both problems?

---

## Key idea

Subtract a correction built from pairs of distinct observations.

Fine-cell averaging turns baseline contamination into a **product** of assignment and baseline approximation errors.

Clip outcomes to control variability. At finer resolutions, smaller assignment increments allow stronger clipping with little effect on the corrected mean.

Compare corrected scores from independent blocks and reject only when every admissible common effect is ruled out.

Under known uniform covariates, overlap, public smoothness, mean bounds, and conditional moments, this delivers matching detection bounds. Sensitivity is governed by outcome tails and effect smoothness, or by joint assignment–baseline roughness.

---

## Example

Let \(X\) be the covariate, \(A\) the treatment indicator, and \(Y\) the outcome. Write \(e_P\) for treatment probability and \(m_{0,P}\) for the untreated mean.

\[
e_P(x)=\frac12+\frac{\sin(2\pi x)}{10},
\qquad
m_{0,P}(x)=\frac{\cos(2\pi x)}8,
\qquad
\tau_P(x)=\frac{\cos(2\pi x)}8,
\]

These functions specify assignment, baseline, and effect. Outcomes are deterministic given \(X,A\):

\[
Y=m_{0,P}(X)+A\tau_P(X)
\]

Treatment adds the effect to the baseline. Heterogeneity is \(d_0=1/(8\sqrt{2})\).

Replacing the effect by the constant \(1/8\) gives a homogeneous population with identical assignment and baseline.

The treated-outcome score varies in both populations. The correction must remove baseline variation while retaining effect variation.

---

## Model

Observe \(n\) independent records \((X,A,Y)\). Let \(m_{1,P}\) be the treated conditional mean.

\[
\tau_P=m_{1,P}-m_{0,P}.
\]

This is the conditional mean contrast. Consistency and assignment independent of potential outcomes conditional on \(X\) give its causal interpretation.

Our class \(\mathcal M_v\) has public parameters \(v=(p,\alpha,\beta,\gamma)\):

- **Known design:** \(X\) is uniform on \([0,1]\).
- **Overlap:** \(e_P(x)\in[1/4,3/4]\); both treatment arms remain observable everywhere.
- **Separate smoothness:** assignment, baseline, and effect have Hölder exponents \(\alpha,\beta,\gamma\), with radius \(20\). Exponent \(s\) bounds changes by \(20|x-z|^s\).
- **Mean bounds:** baseline and effect are each bounded in absolute value by \(1/2\).

In the example, assignment stays between \(0.4\) and \(0.6\), and baseline and effect amplitudes are \(1/8\).

---

## Outcome moments

Let \(Q_{a,P}(dy\mid x)\) be the conditional outcome distribution given covariate \(x\) and treatment arm \(a\).

\[
\max_{a\in\{0,1\}}
\operatorname*{ess\,sup}_{x\sim\lambda}
\int |y|^p\,Q_{a,P}(dy\mid x)\le 10.
\]

This bounds the raw conditional \(p\)-moment in both arms throughout the covariate interval.

The public domain is \(1<p\le2\), \(0<\alpha,\beta\le1\), and \(1/4\le\gamma\le1\).

For \(p<2\), outcomes may have infinite variance. Conditional means remain well defined.

Both running examples satisfy these restrictions for every admissible tuple.

---

## Main result

Set \(q=(p-1)/p\), the moment index, and \(S=\alpha+\beta\), combined assignment and baseline smoothness.

\[
E_0=\frac{2\gamma q}{2\gamma+q},
\qquad
E_4=\frac{2S}{1+2\alpha+\beta/q+S/(2\gamma)},
\qquad
E=\min\{E_0,E_4\}.
\]

These exponents determine how detectable variation shrinks with sample size. The smaller exponent requires larger variation.

The critical radius \(r_n^*(v)\) is the smallest separation permitting both worst-case errors to be at most \(1/10\), capped at \(D_v=\sup_{P\in\mathcal M_v}d(P)\).

@informal thm:heavy-tail-comparison: For every admissible \(v\) and \(n\ge2\), \(c_v\rho_n(v)\le r_n^*(v)\le C_v\rho_n(v)\), where \(\rho_n(v)=n^{-E(p)}\) and positive constants depend on \(v\), not \(n\).

Here \(E(p)=E\). Our explicit test attains the upper bound; its power guarantee requires its sufficient separation to lie below \(D_v\).

---

## Corrected scores

Split the sample into independent blocks \(\mathcal I_1,\mathcal I_2\), each of size \(s_n=\lfloor n/2\rfloor\).

Let \(M=J_{\mathrm c}\) be the coarse histogram rank. The feature vector \(F_M(x)\) has \(\sqrt M\) in the occupied cell and zeros elsewhere. Clipping \(\ell_T(Y)\) replaces outcomes beyond \([-T,T]\) by the nearest endpoint.

For candidate common effect \(c\), form the treated score:

\[
H_{b,T}(c)=
\frac{1}{s_n}\sum_{i\in\mathcal I_b}
F_{J_{\mathrm c}}(X_i)A_i\{\ell_T(Y_i)-c\},
\]

This averages treated outcomes minus \(c\) into coarse-cell coefficients; \(b\) indexes the block and \(T\) is the clipping cutoff.

Correct it using distinct records:

\[
U_{b,G,T}(c)=
\frac{1}{s_n(s_n-1)}
\sum_{\substack{i,j\in\mathcal I_b\\i\ne j}}
F_{J_{\mathrm c}}(X_i)A_iG(X_i,X_j)
\{\ell_T(Y_j)-cA_j\}.
\]

Record \(i\) supplies treatment information; record \(j\) supplies the outcome contribution. The kernel \(G=\Pi_K\) equals the fine rank \(K=J_{\mathrm f}\) within a shared fine cell and zero otherwise.

The basic corrected score is \(Z_b(c)=H_{b,T_0}(c)-U_{b,\Pi_K,T_0}(c)\), using main cutoff \(T_0\).

---

## Why errors multiply

Without clipping, the treated score contains \(e_P(m_{0,P}+\tau_P-c)\). Even at the true constant in the homogeneous example, its baseline contribution varies.

Let \(e_K=\Pi_K e_P\) be the fine-cell assignment average and \(w_K=e_P(1-e_K)\). Write \(\operatorname{coef}_M(f)\) for integrals of \(f\) against the coarse histogram features.

Pair correction leaves effect coefficients \(\operatorname{coef}_M(w_K(\tau_P-c))\) and this baseline remainder:

\[
\operatorname{coef}_M\bigl((e_P-e_K)m_{0,P}\bigr)
=
\operatorname{coef}_M\bigl(
(e_P-e_K)(m_{0,P}-\Pi_Km_{0,P})
\bigr).
\]

Within each fine cell, \(e_P-e_K\) averages to zero. The projected baseline and coarse feature are constant there, so their contribution vanishes.

Only the two approximation errors remain. Their bounds \(20K^{-\alpha}\) and \(20K^{-\beta}\) multiply to at most \(400K^{-S}\).

---

## Preserving effect variation

The correction must retain signal after weighting and coarse averaging.

Overlap guarantees that the fine-cell average of \(w_K\) is \(e_K(1-e_K)\), at least \(3/16\). Coarse-cell average weights inherit that bound.

Effect smoothness limits what coarse averaging loses.

Let \(\theta_P(c)=\mathbb E[Z_b(c)]\), and let \(B\) bound baseline and clipping bias. For every \(|c|\le1/2\),

\(\|\theta_P(c)\|_2\ge\frac{3}{16}d(P)-16M^{-\gamma}-B.\)

Thus every candidate constant leaves signal once heterogeneity exceeds approximation and bias.

In the cosine example, \(d(P)=d_0\) stays fixed as these errors shrink. In the homogeneous example, the true constant \(c=1/8\) gives \(\|\theta_P(c)\|_2\le B\).

---

## Clipping by resolution

When \(S<\gamma\) and \(\alpha<q\), using the main cutoff throughout the fine correction costs too much variability.

Use ranks \(R_j=2^jM\), refinement depth \(L=\log_2(K/M)\), and projection increments \(D_j=\Pi_{R_j}-\Pi_{R_{j-1}}\).

\[
Z_b(c)=
H_{b,T_0}(c)-U_{b,\Pi_M,T_0}(c)
-\sum_{j=1}^{L}U_{b,D_j,T_j}(c),
\]

This reconstructs the fine correction through successive refinements, each with its own cutoff \(T_j\).

Let \(r_T(x)=\mathbb E_P[Y-\ell_T(Y)\mid X=x]\) be the conditional mean removed by clipping.

An increment's clipping distortion is \(\operatorname{coef}_M((D_je_P)r_{T_j})\). Since \(|D_je_P|\le40R_{j-1}^{-\alpha}\), finer increments tolerate more distortion: they can use smaller cutoffs and therefore less variable outcomes.

When \(S\ge\gamma\) or \(\alpha\ge q\), the single correction suffices.

---

## Clipping and pair cost

Let \(a=s^{-E}\) be the target detection scale, where \(s=s_n\). In the refinement branch, choose \(M\) on scale \(a^{-1/\gamma}\) and \(K\) on scale \(a^{-1/S}\).

These choices put coarse effect error and the nuisance product on scale \(a\).

The moment bound converts cutoff \(T\) into mean distortion of order \(T^{1-p}\) and second-moment cost of order \(T^{2-p}\).

At the finest resolution, assignment amplitude is on scale \(K^{-\alpha}\). Weighted distortion on scale \(a\) therefore permits unweighted distortion on scale \(aK^\alpha\), hence \(a^{\beta/S}\).

Pair variability also pays for matching covariates at fine resolution:

\[
\int_0^1D_j(x,x')^2\,dx'
=
R_j+R_{j-1}-2R_{j-1}
=
R_{j-1}
\quad(1\le j\le L).
\]

This squared-kernel integral grows with rank; \(x'\) is the second record's covariate.

With \(t=(2-p)/(p-1)\), the resulting fine-pair cost is bounded on scale \(a^{-(1+\beta t)/S}\). The \(1\) pays for fine rank; \(\beta t\) pays for tail variability after assignment shrinkage absorbs the \(\alpha\) part.

---

## Testing every constant

Compare corrected scores from independent blocks:

\[
W(c)=\langle Z_1(c),Z_2(c)\rangle.
\]

This estimates squared mean signal: independence gives \(\mathbb E[W(c)]=\|\theta_P(c)\|_2^2\), avoiding a self-product noise contribution.

\[
\phi^*_{n,v}
=
\mathbf 1\!\left\{
\min_{|c|\le1/2}W(c)>h_{n,v}
\right\}.
\]

The test \(\phi^*_{n,v}\) rejects only when every admissible common effect is ruled out. Its public threshold \(h_{n,v}\) accounts for bias and variance.

Each score is affine in \(c\), so minimization requires only the endpoints and any interior quadratic minimum.

The homogeneous example is protected because the candidates include its true constant \(1/8\).

---

## Calibration and power

Controlling the two affine score coefficients controls fluctuations simultaneously over all candidate constants.

Write \(\mathfrak b_{n,v}=B\) for the bias bound and \(\Lambda_{n,v}\) for the bound on score variance in each unit direction.

\[
R_{\mathrm{att}}(n,v)
:=\frac{16}{3}
\left\{
16J_{\mathrm c}^{-\gamma}
+5\mathfrak b_{n,v}
+1024J_{\mathrm c}^{1/4}\sqrt{\Lambda_{n,v}}
\right\}.
\]

This sufficient detectable distance pays for coarse effect approximation, score bias, and stochastic fluctuation.

@informal thm:whole-null-calibration-resolved: For admissible \(v\), size is at most \(0.0075\) for \(n\ge2\); if \(n\ge4\) and \(R_{\mathrm{att}}(n,v)<D_v\), missed detection is at most \(0.0075\) whenever \(d(P)\ge R_{\mathrm{att}}(n,v)\).

Public tuning gives \(R_{\mathrm{att}}(n,v)\le C^{\mathrm{att}}_vn^{-E}\), where \(C^{\mathrm{att}}_v\) is an explicit positive multiplier.

The cosine example is detected once sufficient separation falls below \(d_0\). The sufficient constants are conservative; for \(n=2,3\), the test never rejects.

---

## Two noise balances

Hoeffding (1948) supplies the decomposition into single-record fluctuations and centered pair fluctuations. The latter have conditional mean zero given either record, so their variance benefits from two-record averaging.

Squared signal has scale \(a^2\). The quadratic statistic also pays coarse dimension through \(\sqrt M\).

**Single-record fluctuations:** main clipped variability costs \(a^{-t}\), with averaging over \(s\) records.

\[
E_0\left(2+t+\frac{1}{2\gamma}\right)=1,
\qquad
E\left(2+t+\frac{1}{2\gamma}\right)\le1.
\]

The \(2\) represents squared signal; \(t\) represents tails; \(1/(2\gamma)\) represents coarse resolution.

**Centered pair fluctuations:** the correction costs \(a^{-(1+\beta t)/S}\), with averaging on scale \(s^2\).

\[
E_4\left(2+\frac{1+\beta t}{S}+\frac{1}{2\gamma}\right)=2.
\]

Both constraints must hold, giving \(E=\min\{E_0,E_4\}\).

Why can no test improve these constraints?

---

## Rare-outcome comparison

Keep assignment probability \(1/2\) and control outcomes zero in both populations.

Let \(\varepsilon_{n,v}\) be the probability of a nonzero treated outcome and \(L_{n,v}\) its magnitude. The field \(g^{\mathrm{tent}}_\sigma(x)\) consists of opposite triangular tents on adjacent cells of width \(h\), with fair hidden orientations \(\sigma\).

Conditional on \(X=x,A=1\):

| Treated outcome | Homogeneous null \(P_0\) | Alternative \(P^{\mathrm{tent}}_\sigma\) |
|---|---|---|
| \(0\) | \(1-\varepsilon_{n,v}\) | \(1-\varepsilon_{n,v}\) |
| \(+L_{n,v}\) | \(\varepsilon_{n,v}/2\) | \(\frac{\varepsilon_{n,v}}2(1+g^{\mathrm{tent}}_\sigma(x)/16)\) |
| \(-L_{n,v}\) | \(\varepsilon_{n,v}/2\) | \(\frac{\varepsilon_{n,v}}2(1-g^{\mathrm{tent}}_\sigma(x)/16)\) |

The conditional treated means, which also equal the effects here, are:

\[
\tau_{P^{\mathrm{tent}}_\sigma}(x)
=\frac{\varepsilon_{n,v}L_{n,v}}{16}g^{\mathrm{tent}}_\sigma(x)
=\frac{h^\gamma}{16}g^{\mathrm{tent}}_\sigma(x),
\qquad \tau_{P_0}(x)=0,
\]

The null balances positive and negative outcomes. Each alternative tilts that balance across covariates.

Averaging one record over its fair orientation makes the tilt vanish, reproducing the null distribution exactly.

---

## Rare-outcome balance

Choose the number of cells \(N\), cell width \(h\), rarity, and magnitude as follows:

\[
N=2\left\lceil n^{2q/(2\gamma+q)}\right\rceil,
\qquad
h=\frac1N,
\qquad
\varepsilon_{n,v}=h^{\gamma/q},
\qquad
L_{n,v}=h^{-\gamma/(p-1)}.
\]

These choices give treated conditional \(p\)-moment one and effect amplitude on scale \(h^\gamma\).

Opposite tents have average effect zero and distance \(h^\gamma/(16\sqrt3)\), on scale \(n^{-E_0(p)}\).

A single rare treated outcome cannot reveal an orientation. Repeated rare outcomes in the same cell pair can reveal their shared tilt.

Their encounter scale \(n^2\varepsilon_{n,v}^2h\) stays at most one. The complete-sample alternative mixture remains within total variation \(1/2\) of the homogeneous null: every event probability differs by less than \(1/2\).

This makes variation on scale \(n^{-E_0(p)}\) unavoidable even with known, constant assignment.

---

## Hidden nuisance variation

The second obstruction conceals effect variation behind unknown assignment and baseline variation.

Use fields \(\xi(x),\upsilon(x),\zeta(x)\), with rarity \(\varepsilon\) and outcome magnitude \(L>0\). Their mapping to economically familiar objects is:

| Object | Conditional value |
|---|---|
| Treatment probability | \(e_P(x)=(1+\xi(x))/2\) |
| Untreated mean | \(m_{0,P}(x)=\varepsilon L(\upsilon(x)-\zeta(x))/(1-\xi(x))\) |
| Treated mean | \(m_{1,P}(x)=\varepsilon L(\upsilon(x)+\zeta(x))/(1+\xi(x))\) |

Thus \(\xi\) controls assignment, while \(\upsilon\) and \(\zeta\) together control the arm means.

The observed records have six categories:

| Record category | Conditional probability given \(X=x\) |
|---|---|
| \(A=(1+\ell)/2,\ Y=hL\) | \(\frac{\varepsilon}{4}\{1+\ell\xi(x)+h\upsilon(x)+\ell h\zeta(x)\}\) |
| \(A=(1+\ell)/2,\ Y=0\) | \(\frac{1-\varepsilon}{2}\{1+\ell\xi(x)\}\) |

Here \(\ell,h\in\{-1,1\}\) encode treatment and outcome sign. The first row supplies four categories; the second supplies two.

We construct null and alternative populations whose averaged single-record probabilities agree.

---

## Correlated hidden signs

Let \(g_\sigma\) be opposite triangular tents on paired coarse cells, with fair orientations \(\sigma_j\).

Continuous weights \(f_i(x)\) join neighboring fine cells at rank \(K\), with \(\sum_i f_i(x)^2=1\). Hidden signs generate assignment and outcome fields:

\[
\xi(x)=a\sum_{i=0}^{K}f_i(x)\lambda_i,
\qquad
\upsilon(x)=u\sum_{i=0}^{K}f_i(x)\eta_i,
\]

Here \(a,u\) are field amplitudes, and \(\lambda_i,\eta_i\) are fine-node signs.

For null branch \(\nu=0\) and alternative branch \(\nu=1\), draw each pair independently conditional on the coarse orientations:

\[
\Pr_\nu(\lambda_i=l,\eta_i=h\mid\sigma)
=
\frac{1+\nu\kappa g_\sigma(i/K)lh}{4},
\qquad
l,h\in\{-1,1\},
\quad 0\le i\le K.
\]

The coupling strength is \(\kappa=1/16\). Each sign is fair in both branches.

The null signs have correlation zero. Alternative signs have correlation \(\kappa g_\sigma(i/K)\): assignment and outcome signs become related according to the local orientation.

How can this change generate effects while leaving single records unchanged?

---

## Concealing the effect

Let \(\widetilde g_\sigma(x)=\sum_i g_\sigma(i/K)f_i(x)^2\) interpolate the coarse tents through the fine weights.

Choose the interaction field using:

\[
t_\nu(x)=
-\frac{\nu au\kappa}{1-a^2}\widetilde g_\sigma(x),
\qquad
\zeta(x)=
\xi(x)\upsilon(x)+t_\nu(x)\bigl(1-\xi(x)^2\bigr).
\]

The function \(t_\nu\) adjusts the treatment–outcome interaction. Substitution into the arm means gives \(\tau_P(x)=2\varepsilon Lt_\nu(x)\).

The null has \(t_0=0\), so its two arm means coincide. The alternative retains a centered effect shaped by \(\widetilde g_\sigma\).

To satisfy the separate smoothness and moment restrictions, choose:

- Assignment amplitude \(a=K^{-\alpha}/16\) and baseline amplitude \(b=K^{-\beta}/256\).
- Outcome-field amplitude \(u=1/16\), rarity \(\varepsilon=(16b)^{1/q}\), and magnitude \(L=\varepsilon^{-1/p}\).

Then \(\varepsilon Lu=b\) and \(\varepsilon L^p=1\). Small smooth means coexist with rare, large outcomes, and alternative distances lie between \(2^{-17}K^{-S}\) and \(2^{-14}K^{-S}\).

---

## Cancellation across records

Averaging the fine signs gives mean squared assignment field \(a^2\). The alternative changes the average product \(\xi\upsilon\) by \(au\kappa\widetilde g_\sigma(x)\).

The interaction adjustment cancels precisely that change:

\[
au\kappa\widetilde g_\sigma(x)
 +t_1(x)(1-a^2)=0.
\]

This identity makes all six single-record probabilities agree between the null and alternative mixtures, even with coarse orientations fixed.

More cancellation holds for a local group of records connected through shared fine-node signs within one coarse cell.

With exactly one nonzero outcome, zero-outcome records supply an assignment-only factor. Conditional on assignment signs, the remaining factor is linear in outcome signs.

Both the changed outcome-sign means and \(t_1\) reverse with the coarse orientation. Averaging its two fair values therefore cancels the difference, however many zero outcomes accompany the rare outcome.

Only particular encounters between records can expose the alternative.

---

## Surviving dependence

Two patterns survive the cancellation:

- **Two rare outcomes in one local group:** products of orientation-dependent terms remain. Their squared-likelihood cost is at most a constant times \(a^4u^4\varepsilon^2n^2/K\).
- **Two nonsingleton groups sharing one coarse orientation:** their individual changes multiply after orientation averaging. Their cost is at most a constant times \(a^4u^4\varepsilon^2n^4/(MK^2)\).

Here \(M\) is coarse rank. Squared-likelihood cost measures how much the complete-sample distributions can differ.

In the rough regime \(E_4<E_0\), choose \(M\) proportional to \(K^{S/\gamma}\), ensuring that effects of amplitude \(K^{-S}\) satisfy effect smoothness.

Using the preceding amplitudes and rarity, the dominant cost is at most a constant times \(n^4K^{-2D_p}\), where \(D_p=1+2\alpha+\beta/q+S/(2\gamma)\).

Taking \(K\) proportional to \(n^{2/D_p}\), with a sufficiently large multiplier, makes both costs small:

\[
\operatorname{TV}(\mathbb P_0,\mathbb P_1)<\frac18.
\]

The complete-record null and alternative mixtures \(\mathbb P_0,\mathbb P_1\) then differ in every event probability by less than \(1/8\), while alternatives retain distance on scale \(n^{-E_4(p)}\).

Thus hidden nuisance dependence makes the second rate constraint unavoidable.

---

## Further results

Supplying the whole true propensity gives detection scale \(n^{-E_0}\). It removes the assignment–baseline obstruction while retaining the outcome-tail obstruction.

@informal thm:exact-propensity-preservation-boundary: On \(\mathcal M_v\), unknown assignment probabilities preserve the separation order obtained with the whole true propensity supplied exactly when \(2\alpha/(p-1)+\beta/q+S/(2\gamma)\ge1\), including equality.

When the condition fails, the unknown-propensity radius is larger by a polynomial factor with exponent \(E_0(p)-E_4(p)\).

This comparison holds on the same population class; it identifies when assignment information changes testing sensitivity.

---

## Takeaways

- Under known uniform design, overlap, public smoothness, mean bounds, and conditional moments, detectable effect variation has scale \(n^{-E(p)}\), with \(E(p)=\min\{E_0(p),E_4(p)\}\).
- Pair correction multiplies nuisance errors. Smaller assignment increments permit stronger clipping at fine resolutions while preserving effect signal.
- Independent blocks and minimization handle squared signal and the unknown constant. Rare outcomes and hidden nuisance dependence make both rate constraints unavoidable.

---

## Appendix: Matched separation rates

This statement gives matching detection bounds, the bounded-outcome comparison, and the exact cost of allowing heavier tails.

@formal thm:heavy-tail-comparison

---

## Appendix: Attaining test

This statement gives the explicit test’s size and power guarantees, public tuning bounds, and sufficient thresholds for nonempty power domains.

@formal thm:original-record-attainable-rate

---

## Appendix: Supplied propensity frontier

This statement establishes matching detection bounds when the whole true propensity is supplied, allowing broader continuous nuisance functions.

@formal thm:oracle-frontier-broad-class

---

## Appendix: Assignment information boundary

This statement identifies exactly when unknown assignment probabilities preserve the supplied-propensity separation order.

@formal thm:exact-propensity-preservation-boundary
