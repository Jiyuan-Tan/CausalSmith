# Treatment Effects With Auxiliary Records

Records without outcomes can improve treatment-effect estimates by revealing population frequencies, until rare treated outcomes become the binding constraint.

---

## Motivation

We want a treatment effect averaged across many covariate categories. The usual approach estimates each category’s outcome contrast and averages using population weights.

Empty treatment–category cells leave missing contributions. These biases accumulate across categories.

Here \(n\) is the number of records carrying outcomes, \(d\) is the number of covariate categories, and overlap bounds both treatment probabilities away from zero within every occupied category.

- Zeng et al. (2026) give conventional-estimator bounds with a many-category term of order \(d^2/n^2\) at fixed overlap; their minimax lower bound contains a logarithmic improvement.
- CausalSmith (2026), *Outcome Annotation and Minimax Risk*, shows that adding \(m\) outcome-free records changes the fixed-overlap risk order to

\[
\min\left\{1,\frac1n+\frac{d^2}{(n+m)^2[\log(\exp(1)n)]^2}\right\}
\]

  with constants that may depend on the fixed overlap floor.

Both comparisons allow constants to depend on the overlap floor.

What accuracy is achievable when overlap diminishes, and how much can records without outcomes help?

---

## Key idea

Estimate outcome-success masses and correct them for population frequencies. Use a polynomial correction in sparse cells, where inverse counts leave substantial bias.

For binary treatment and outcomes, let \(n\ge1\) count complete records, \(m\ge0\) auxiliary records, and \(d\ge2\) covariate categories. The known overlap floor is \(0<\epsilon\le1/4\).

The smallest worst-case squared error is within universal constant factors of

\[
r(n,m,d,\epsilon)
=
\min\left\{
1,\frac1S+\left(\frac d{N\epsilon\ell}\right)^2
\right\},
\qquad
N=n+m,\quad S=n\epsilon,\quad
\ell=\log(\exp(1)+S).
\]

Here \(N\) measures frequency information, \(S\) measures rare-arm outcome information, and \(\ell\) is a regularized natural logarithm.

Auxiliary records reduce the many-category term. Complete records determine the remaining outcome term.

---

## Example

At experiment \(k\), let \(t=k+4\):

\[
n_k=t^4,\qquad \epsilon_k=t^{-1},\qquad d_k=t^2,\qquad m_k=t^6.
\]

Treatment becomes rarer while the number of categories grows.

Let \(R\) denote minimax risk: the smallest worst-case squared error over all estimators. Complete records alone give

\[
R(n_k,0,d_k,\epsilon_k)\asymp \frac{1}{t^2(\log t)^2},
\]

where \(\asymp\) means comparison within fixed positive factors.

Adding auxiliary records gives \(R(n_k,m_k,d_k,\epsilon_k)\asymp t^{-3}\).

Frequency information removes the dominant many-category difficulty until rare treated outcomes determine precision: \(1/(n_k\epsilon_k)=t^{-3}\).

---

## Model

A complete record is \((X,A,Y)\): category \(X\), binary treatment \(A\), and binary outcome \(Y\). Its population law is \(P\).

Let \(p_j(P)\) be category \(j\)’s population share and \(\mu_{aj}(P)\) its mean outcome under observed treatment \(a\).

Our population-weighted contrast is

\[
\tau(P)
=
\sum_{j=1}^{d}p_j(P)\{\mu_{1j}(P)-\mu_{0j}(P)\},
\]

so each category’s contrast contributes according to its population share.

Let \(P_{XA}\) be the treatment–covariate distribution and \(\mathcal D\) all observed records:

\[
\mathcal D\sim P^{\otimes n}\otimes P_{XA}^{\otimes m}.
\]

All records are independent draws from one population. Both channels reveal frequencies; only complete records reveal outcomes.

---

## Assumptions

Let \(e_j(P)\) be the probability of treatment within category \(j\). The public overlap restriction guarantees opportunities to observe both arms:

@formal ass:overlap

Category shares and outcome means are otherwise unrestricted. Call this population class \(\mathcal M_{d,\epsilon}\).

In the example, \(\epsilon_k=t^{-1}\): treatment probabilities may diminish, and category shares may still be arbitrarily small.

For a causal interpretation, let \(Y_0,Y_1\) be potential outcomes under a joint law \(H\):

- Consistency, \(Y=AY_1+(1-A)Y_0\): we observe the outcome under the received treatment.
- Conditional exchangeability, \((Y_0,Y_1)\perp\!\!\!\perp A\mid X\): within a category, treatment carries no additional information about potential outcomes.

These conditions identify the population ATE:

\[
\mathbb E_H[Y_1-Y_0]=\tau(P).
\]

The expectation averages the difference between both potential outcomes across the population.

---

## Main result

@informal thm:uniform-annotation-frontier: With independent binary common-population records, \(n\ge1,m\ge0,d\ge2\), and known \(0<\epsilon\le1/4\), a deterministic estimator attains minimax risk within universal constant factors of \(r\) over \(\mathcal M_{d,\epsilon}\).

Write our estimator as \(\widehat\tau\). The minimax comparison permits every estimation rule, including randomization through an independent seed \(U\):

\[
c\,r(n,m,d,\epsilon)
\le R(n,m,d,\epsilon)
\le \sup_{P\in\mathcal M_{d,\epsilon}}
\mathbb E_P\!\left[
\bigl(\widehat\tau(\mathcal D,U)-\tau(P)\bigr)^2
\right]
\le C\,r(n,m,d,\epsilon).
\]

The positive constants \(c,C\) are independent of \(n,m,d,\epsilon\). Our estimator ignores \(U\).

The formula compares achievable worst-case error with a lower bound applying to every estimator.

In the example, it establishes risk order \(t^{-3}\) with auxiliary records.

---

## Independent tasks

Suppress the argument \(P\). Let \(s_{aj}=P(X=j,A=a)\) be an arm–category mass and \(q_{aj}=P(X=j,A=a,Y=1)\) its outcome-success mass.

Complete records estimate \(q_{aj}=s_{aj}\mu_{aj}\). The target needs \(p_j\mu_{aj}=q_{aj}p_j/s_{aj}\).

Since \(p_j=s_{0j}+s_{1j}\), we need successes, an opposite-arm mass, and a reciprocal arm mass.

Sample splitting assigns disjoint records to independent tasks:

| Pool | Records | Task |
|---|---|---|
| Outcome | Complete records | Estimate success masses |
| Pilot | Complete projections and auxiliary records | Locate sparse cells |
| Correction | Complete projections and auxiliary records | Estimate frequency corrections |

The outcome budget is proportional to \(n\); both frequency budgets are proportional to \(N\).

---

## Inverse-count bias

For this calculation, \(Z_j\) counts arm-\(a\) successes in an outcome pool independent of a separate marginal pool. That marginal pool supplies \(K_j\), the arm-\(a\) count, and \(W_j\), the opposite-arm count.

Use independent Poisson sample sizes with means \(u\) for outcomes and \(t\) for marginal records. Within the marginal pool, disjoint arm–category counts are then independent.

The natural correction estimates the population-weighted arm mean \(\psi_a\):

\[
H_j=\frac{Z_j}{u}\left(1+\frac{W_j}{K_j+1}\right),
\qquad
\psi_a=\sum_{j=1}^{d}p_j(P)\mu_{aj}(P).
\]

Adding one defines the denominator for empty cells. Independence gives the exact bias:

\[
\mathbb E\!\left[\sum_{j=1}^{d}H_j\right]-\psi_a
=-\sum_{j=1}^{d}s_{1-a,j}\mu_{aj}e^{-t s_{aj}}.
\]

The exponential is the probability that \(K_j=0\). Missing opposite-arm-weighted contributions all enter with the same sign.

---

## Polynomial correction

Ma et al. (2022) use a Chebyshev construction to correct uncertain inverse action probabilities when the target weights are supplied. Here the population weights must also be learned, and the overlap restriction is conditional within occupied covariate categories.

For a sparse arm mass, choose a scale \(B>0\), set \(z=s_{aj}/B\), and use an integer degree parameter \(L\ge2\). Let \(T_L\) be the Chebyshev polynomial and \(C_L(z)=T_L(1-2z)\).

\[
E_L(z)=\frac{1-C_L(z)}{2L^2z},
\qquad
G_L(z)=\frac{1-E_L(z)}{z}
\quad(z\ne0),
\]

The polynomial correction \(G_L(z)/B\) approximates \(1/s_{aj}\). The fraction left uncorrected is \(E_L(z)=1-zG_L(z)\):

\[
0\le E_L(z)\le\min\{1,(L^2z)^{-1}\}
\quad(0<z\le1),
\qquad E_L(0)=1.
\]

This bounds the residual on the intended sparse-cell interval.

---

## Unbiased polynomial estimation

Plugging a noisy mass estimate into a polynomial introduces additional bias.

Instead, let \(K\) be Poisson with mean \(tzB\), put \(D=tB\), and let \(g_h\) be the coefficients of \(G_L\).

A falling factorial multiplies successive decreasing counts:

\[
(K)_0=1,\qquad
(K)_h=\prod_{i=0}^{h-1}(K-i)\quad(h\ge1),
\qquad
\widehat G=\sum_{h=0}^{L-2}g_h\frac{(K)_h}{D^h}.
\]

Each \((K)_h/D^h\) estimates the monomial \(z^h\) without bias. Thus

\[
\mathbb E[\widehat G]
 =\sum_{h=0}^{L-2}g_hz^h
 =G_L(z).
\]

The approximation leaves a residual; estimating the polynomial adds no bias.

---

## Cellwise choice

Let \(Z_{aj}\) be outcome successes, \(J_{aj}\) pilot counts, and \(K_{aj}\) correction counts. The three pools are independent, with Poisson sample-size means \(u,t_p,t\).

Let \(\widehat G_{aj}\) be the factorial polynomial estimate from \(K_{aj}\). A public pilot threshold \(k_0\) selects

\[
V_{aj}=
\begin{cases}
\displaystyle
\frac{Z_{aj}}u
\left(1+\frac{K_{1-a,j}\widehat G_{aj}}{tB}\right),
&J_{aj}\le k_0,\\[6pt]
\displaystyle
\frac{Z_{aj}}u
\left(1+\frac{K_{1-a,j}}{K_{aj}+1}\right),
&J_{aj}>k_0.
\end{cases}
\]

Each \(V_{aj}\) estimates \(p_j\mu_{aj}\).

Sparse cells receive polynomial correction. Populated cells use inverse counts because their empty-cell bias is already small.

The independent pilot avoids selecting on the correction counts and makes use outside the polynomial’s intended range unlikely.

---

## The bias gain

For one arm and category, abbreviate \(s_j=s_{aj}\), \(v_j=s_{1-a,j}\), and \(\bar\mu_j=\mu_{aj}\). Set \(\zeta_j=s_j/B\).

The polynomial contribution’s bias is \(-v_j\bar\mu_jE_L(\zeta_j)\). When \(0<s_j\le B\),

\[
0\le v_j\bar\mu_jE_L(\zeta_j)
\le\frac{v_jB}{L^2s_j}
\le\frac B{\epsilon L^2}.
\]

The residual bound supplies \(L^{-2}\). Overlap controls the opposite-arm mass relative to the corrected-arm mass: \(\epsilon v_j\le s_j\).

Taking \(B\) proportional to \(L/N\) gives total bias at most a constant times \(d/(N\epsilon L)\).

The gain comes from controlling population-weighted contributions, even where the reciprocal itself is arbitrarily large.

---

## Degree calibration

In the large-information branch, choose the polynomial degree \(L\) proportional to \(\log S\), hence comparable to the theorem’s regularized logarithm \(\ell=\log(\exp(1)+S)\).

- Higher degree reduces bias but increases polynomial count noise exponentially.
- This logarithmic degree bounds the additional noise by a constant times \(\zeta_{\mathrm{rate}}/\sqrt S\), where \(\zeta_{\mathrm{rate}}=d/(N\epsilon L)\) is the bias scale.

Those terms fit inside squared bias plus outcome variance:

\[
\frac{2\zeta_{\mathrm{rate}}}{\sqrt S}
\le\zeta_{\mathrm{rate}}^2+\frac1S.
\]

The certified bounded-information branch outputs zero; bounded loss there is absorbed by one universal comparison constant.

Thus the theorem holds for every allowed \(S>0\).

---

## Original-record estimator

Sum the treated contributions and subtract the control contributions. Clipping projects the contrast onto \([-1,1]\), reducing squared error.

Let \(F\) be this clipped contrast. For the observed records, average over independent Poisson prefix lengths \(J\) in the three finite pools:

\(\widehat\tau(\mathcal D,U)=\mathbb E_J[F(J;\mathcal D)]\).

This averages possible prefix choices. A prefix longer than its pool receives output zero.

The square of an average error is at most the average squared error. Prefix overflow adds only an exponentially small tail.

The resulting estimator is deterministic on the original records and attains the main upper bound.

Why can no other estimator improve its order?

---

## Outcome-information floor

Take two equally likely categories with treatment probability \(\epsilon\). Control means are \(1/2\); treated means are \(1/2+\delta\) or \(1/2-\delta\).

Choose

\[
\delta=\frac1{16\sqrt{\max\{1,S\}}}.
\]

This is the sampling-noise scale of approximately \(S=n\epsilon\) informative treated outcomes.

The targets differ, but frequency information is identical:

\[
\tau(P_+)=\delta,
\qquad
\tau(P_-)=-\delta,
\qquad
(P_+)_{XA}=(P_-)_{XA}.
\]

Auxiliary records cannot distinguish the two populations.

@informal thm:rare-label-floor: For independent binary common-population records with \(n\ge1,m\ge0,d\ge2\) and \(0<\epsilon\le1/4\), minimax risk is at least a universal multiple of \(\min\{1,(n\epsilon)^{-1}\}\), even with the exact treatment–covariate table supplied.

In the running example, this forces risk of at least order \(t^{-3}\).

---

## Hidden target differences

The many-category lower bound constructs population mixtures whose observations are nearly indistinguishable but whose targets are separated.

For this construction, fix \(L\ge2\), \(B>0\), and \(\alpha=B/(100L^2)\).

The reciprocal \(\alpha/[\alpha+(1-\epsilon)v]\) falls too sharply near zero for a degree-\(L\) polynomial to approximate uniformly within \(1/8\). Finite polynomial approximation duality supplies nodes \(v_i\) and signed weights \(\omega_i\):

\[
\begin{gathered}
0\le v_1<\cdots<v_{L+2}\le B,\qquad
\sum_{i=1}^{L+2}|\omega_i|=1,\\
\sum_{i=1}^{L+2}\omega_i v_i^h=0
\quad(h=0,\ldots,L),\\
\sum_{i=1}^{L+2}\omega_i
\frac{\alpha}{\alpha+(1-\epsilon)v_i}\ge\frac18.
\end{gathered}
\]

The signed weights cancel every polynomial through degree \(L\), while retaining a reciprocal difference.

Write \(\sigma\) for these signed weights; integration against \(\sigma\) means their weighted sum.

---

## Common category mixture

Set \(b_0=\alpha/\epsilon\). At latent node \(v_i\), both hypotheses use the same shared frequency table:

| Shared raw quantity | Value |
|---|---|
| Category mass | \(w_*(v_i)=b_0+v_i\) |
| Treated mass | \(S_1(v_i)=\alpha+(1-\epsilon)v_i\) |
| Control mass | \(S_0(v_i)=(1-\epsilon)b_0+\epsilon v_i\) |

Thus \(w_*=S_1+S_0\), and the arm shares satisfy conditional overlap. A core node receives probability \(\alpha|\omega_i|/S_1(v_i)\). Only its treated outcome changes:

| Core sign | Hypothesis 1 | Hypothesis 0 |
|---|---|---|
| \(\omega_i>0\) | treated success | treated failure |
| \(\omega_i<0\) | treated failure | treated success |

All control outcomes and the remaining filler outcomes are zero. Technically, a core node at \(v_i=0\) retains its core flag and is distinct from the filler.

---

## Gap scale

Multiplying the core probability by category mass produces \(w_*(v)\alpha/S_1(v)\): a constant plus a positive multiple of the reciprocal.

The constant cancels under the signed weights. The surviving reciprocal gives expected raw target separation of at least \(b_0/12\) per rare category.

Use this construction when \(S\ge\exp(4096)\) and \(x^2>S^{-1}\), where \(x=d/(N\epsilon\ell)\).

| Quantity | Scale |
|---|---|
| Matching degree \(L\) | Proportional to \(\ell\) |
| Interval endpoint \(B\) | Proportional to \(L/N\) |
| Baseline mass \(b_0\) | Proportional to \(1/(N\epsilon L)\) |
| Independent rare categories \(K_*\) | Proportional to \(\min\{d,1/b_0\}\) |

Their expected raw target gap, denoted \(\Delta_{\mathrm{tar}}\), satisfies

\[
\Delta_{\mathrm{tar}}\ge\frac{K_*b_0}{12}.
\]

This is at least a fixed multiple of \(\min\{x,1\}\).

---

## Population normalization

Raw masses must become a probability distribution without erasing the target gap.

Let \(\bar w\) be the expected raw mass of one rare category. Add a reservoir category and define the total raw mass:

\[
\bar w=\mathbb E[w_*(V)],\qquad
p_*=1-K_*\bar w,\qquad
Q=p_*+\sum_{i=1}^{K_*}w_*(V_i).
\]

The reservoir has mass \(p_*\), propensity \(1/2\), and zero outcomes. Dividing every raw mass by \(Q\) produces a population probability table.

The total \(Q\) has expectation one and is always greater than \(1/2\). Concentration of \(Q\) and the raw targets preserves separation of the normalized targets with high probability.

For every common latent configuration, both hypotheses have the same normalized treatment–covariate table. Consequently, their population mixtures have the same distribution of those tables.

---

## Concealing observable differences

Compare an enlarged experiment before dividing the sampling intensities by \(Q\).

Let \(u=128n\), \(w=128N\), and \(M=u+w\). Write \(\boldsymbol\lambda\) for a latent configuration and \(P_\iota(\boldsymbol\lambda)\) for its normalized population under hypothesis \(\iota\in\{0,1\}\).

Conditional on this population, observe independent Poisson atom counts with means

\[
uQ\,P_\iota(\boldsymbol\lambda)(j,a,y),
\qquad
wQ\,(P_\iota(\boldsymbol\lambda))_{XA}(j,a).
\]

These are intensities proportional to raw complete and marginal masses.

A differing observation includes a treated outcome. Its factor \(S_1(v)\) cancels the reciprocal in the core probability. Remaining discrepancies are affine-mass polynomials multiplied by \(e^{-Mv}\).

For \(j\le L\), moment cancellation gives

\[
\int e^{-Mv}v^j\,d\sigma(v)
=
\int\left(e^{-Mv}
-\sum_{k=0}^{L-j}\frac{(-Mv)^k}{k!}\right)v^j\,d\sigma(v).
\]

Only the remainder distinguishes the mixtures. The two enlarged observation laws differ by less than \(1/64\) on every event.

---

## Sampling transfer

Randomly order each channel’s Poisson counts. Conditional on the latent population, a record’s probability is its raw mass divided by the total \(Q\).

Let \(J_{\mathrm L},J_{\mathrm A}\) be the channel lengths, and \(\mathcal L_{\mathrm{raw}},\mathcal X_{\mathrm{raw}}\) their ordered records:

\[
\begin{aligned}
J_{\mathrm L}&\sim\operatorname{Poi}(uQ),&
\mathcal L_{\mathrm{raw}}\mid J_{\mathrm L}=k
&\sim P_\iota(\boldsymbol\lambda)^{\otimes k},\\
J_{\mathrm A}&\sim\operatorname{Poi}(wQ),&
\mathcal X_{\mathrm{raw}}\mid J_{\mathrm A}=k
&\sim(P_\iota(\boldsymbol\lambda))_{XA}^{\otimes k}.
\end{aligned}
\]

The channels are independent conditional on that population.

Whenever enough records are available, the first \(n\) complete and \(m\) auxiliary records have exactly the original product sampling law.

Because \(Q>1/2\), shortage probability is at most \(2e^{-31n}\), small relative to \(\Delta_{\mathrm{tar}}^2\).

Any original estimator can therefore be run on these prefixes, with zero on shortage. A uniformly better original estimator would contradict the enlarged-experiment testing bound. Hence

\[
R(n,m,d,\epsilon)\ge c\min\{1,x^2\}.
\]

This many-category floor and the outcome floor match the upper bound.

---

## Further results

The exact-frequency benchmark supplies \(P_{XA}\) directly to the estimator \(T^{\mathrm K}\), alongside complete records \(\mathcal L\) and the independent seed \(U\):

\[
R^{\mathrm K}(n,d,\epsilon)
=
\inf_{T^{\mathrm K}}\sup_{P\in\mathcal M_{d,\epsilon}}
\mathbb E_{P^{\otimes n}\otimes\mathrm{Uniform}[0,1]}
\left[
\bigl(T^{\mathrm K}(\mathcal L,P_{XA},U)-\tau(P)\bigr)^2
\right].
\]

This is the smallest worst-case squared error when population category weights and treatment propensities are known.

Its risk order is \(c b(n,\epsilon)\le R^{\mathrm K}(n,d,\epsilon)\le C b(n,\epsilon)\), with universal constants and \(b(n,\epsilon)=\min\{1,(n\epsilon)^{-1}\}\).

For fixed \(n\ge1,d\ge2,0<\epsilon\le1/4\), along integer auxiliary sample sizes,

\[
\lim_{m\to\infty}R(n,m,d,\epsilon)=R^{\mathrm K}(n,d,\epsilon).
\]

Thus increasingly precise frequency information approaches the exact-table experiment while retaining the rare-outcome constraint.

---

## Open questions

- Practical computation and moderate-sample tuning of the certified estimator.
- Adaptive outcome allocation, which changes the passive sampling experiment.
- Confidence intervals and policy objectives, which require additional guarantees.
- Uncertain overlap floors, continuous covariates, multiple treatments, and nonbinary outcomes.

---

## Takeaways

- Complete records supply rare-outcome information; both channels supply population-frequency information.
- Polynomial correction controls weighted sparse-cell error. Logarithmic degree balances the bias gain against count noise.
- Auxiliary records can reach the rare-outcome benchmark. Matching lower bounds show why frequency information cannot improve beyond it.

---

## Appendix: Uniform annotation frontier

This statement gives the uniform minimax comparison, deterministic attainment, and causal interpretation.

@formal thm:uniform-annotation-frontier

---

## Appendix: Rare-outcome risk floor

This statement establishes the outcome-information lower bound, including when the exact marginal table is supplied.

@formal thm:rare-label-floor

---

## Appendix: Annotation resource conditions

The relative-improvement criterion requires both a meaningful initial many-category difficulty and enough auxiliary information to overcome it.

@formal thm:annotation-resource-phases

---

## Appendix: Benchmark recovery

This statement gives fixed-overlap, two-category, and exact-marginal comparisons, including the fixed-parameter auxiliary-sample limit.

@formal prop:benchmark-recovery
