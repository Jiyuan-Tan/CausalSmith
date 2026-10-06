# Recovering Causal Responses When Treatment Is Scarce

We recover a smooth causal response across the covariate domain even when treated observations concentrate in narrow regions.

---

## Motivation

A practitioner wants the mean outcome under treatment at each covariate value:

\[
\mu_1(x)=\mathbb E_P[Y(1)\mid X=x].
\]

Here \(X\) contains covariates, \(Y(1)\) is the potential outcome under treatment, and \(P\) is the population law.

- The usual approach fits a local polynomial to treated outcomes: Fan and Gijbels (1996).
- Many treated observations can still provide little variation in one covariate direction.
- Write \(e(x)=P(A=1\mid X=x)\) for the propensity, the probability of treatment at covariate value \(x\). Dorn (2026), our closest comparator, obtains a pure-power uniform probability guarantee with an additional local restriction: every small neighborhood must give a positive fraction of its covariate mass to treatment probabilities within a fixed factor of that neighborhood's maximum.

Can global control of small treatment probabilities support recovery despite this local geometric difficulty?

---

## Key idea

Give fixed fitting regions equal total weight, then choose the finest resolution with enough treated observations in every region.

Under causal identification, covariate density bounded below, bounded treated means, conditionally sub-Gaussian noise, global overlap tails, and known response smoothness \(\beta>1\), the optimal error scale is

\[
n^{-\beta/(2\beta+d\gamma/(\gamma-1))}.
\]

Here \(n\) is sample size, \(d\) is covariate dimension, and \(\gamma>1\) controls the prevalence of small treatment probabilities.

- One estimator achieves this scale for expected largest error across the domain, uniformly over fixed compact ranges of \(\gamma\).
- Matching pointwise lower bounds hold for every fixed \(\gamma>1\) and every fixed evaluation point.
- Equal weights repair fitting geometry; treatment counts control precision.

---

## Example

Treatment can concentrate in a narrowing strip.

Let \(d\ge2\), let \(X\) be uniform on \([0,1]^d\), and let \(x^\circ=(1/2,\ldots,1/2)\) be its center. Write \(R(x)=\|x-x^\circ\|_\infty\) for distance from the center and \(F_R(t)=P(R(X)\le t)\).

Choose \(1<a<1+d/(\gamma-1)\). Define

\[
S=\left\{x\in\mathcal X:
|x_2-x_2^\circ|\le |x_1-x_1^\circ|^a\right\},
\qquad
e_\star(x)=
\min\left\{1,F_R(R(x))^{1/(\gamma-1)}
+\frac14\mathbf 1_S(x)\right\}.
\]

Here \(\mathcal X=[0,1]^d\), \(S\) is the strip, and \(e_\star(x)\) is treatment probability.

The radial component supplies treatment away from the center; the strip adds treatment close to \(X_2=1/2\). Bounded Bernoulli potential outcomes with constant means isolate the assignment geometry.

---

## Missing coordinate variation

Consider the local fitting neighborhood \(\|X-x^\circ\|_\infty\le h\), where \(h\) is its width scale.

The treated second-coordinate displacement, divided by \(h\), has second moment

\[
\lim_{h\downarrow0}
\frac{
\displaystyle
\int_{\{A=1,\ \|X-x^\circ\|_\infty\le h\}}
\left(\frac{X_2-1/2}{h}\right)^2
\,dP_{\mathrm{strip}}
}{
P_{\mathrm{strip}}\{A=1,\ \|X-x^\circ\|_\infty\le h\}
}
=0.
\]

The denominator normalizes by treated probability in the neighborhood; the numerator averages squared displacement in units of neighborhood width. \(P_{\mathrm{strip}}\) denotes the example’s law.

- Inside the strip, second-coordinate displacement is at most \(h\) to the power \(a\); relative displacement vanishes because \(a>1\).
- The chosen upper bound on \(a\) makes strip treatment dominate radial treatment as the neighborhood shrinks.
- Thus the ordinary local fitting matrix loses variation in coordinate two, despite the global overlap bound.

@figure strip-neighborhood: A box for the local fitting neighborhood \(\|X-x^\circ\|_\infty\le h\) branches to boxes for its narrowing strip and its complement. The strip leads to vanishing second-coordinate displacement relative to \(h\); the complement leads to radial treatment whose share of local treated observations vanishes.

---

## Model

Observe \(n\) independent triples \((X_i,A_i,Y_i)\), collected in \(\mathcal D_n\). Here \(A_i=1\) denotes treatment and \(Y_i\) is the observed outcome.

- **Consistency:** \(Y=AY(1)+(1-A)Y(0)\); the observed outcome corresponds to the realized treatment.
- **Exchangeability:** \((Y(0),Y(1))\perp A\mid X\); conditioning on covariates removes dependence between assignment and potential outcomes.
- The propensity is \(e(x)=P(A=1\mid X=x)\).

Under global overlap control with \(\gamma>1\),

\[
P_X\{x:e(x)=0\}=0,
\qquad
\mu_1(x)=\mathbb E_P[Y\mid A=1,X=x]
\quad\text{for }P_X\text{-almost every }x.
\]

Here \(P_X\) is the covariate distribution. This identifies the causal response through treated outcome regression. Continuity and covariate coverage extend identification to every point of the closed cube.

---

## Assumptions

Fix common constants \(B,L>0\), \(C\ge1\), and \(0<c_f\le1\).

- **Covariate coverage:** the density satisfies \(f(x)\ge c_f\) on \([0,1]^d\), so every region receives covariate probability proportional to its volume.
- **Response control:** the treated mean has magnitude at most \(B\). Centered treated outcomes are conditionally sub-Gaussian: their conditional exponential moments are bounded by \(\exp(\lambda^2B^2/2)\), controlling large noise fluctuations.
- **Known smoothness:** \(\mu_1\in\mathcal H^\beta(L)\), with known \(\beta>1\). Derivatives through \(m=\lceil\beta\rceil-1\) are bounded by \(L\); order-\(m\) derivatives change by at most \(L\|x-x'\|_\infty^{\beta-m}\).

**Global overlap** limits the covariate probability assigned to small treatment probabilities:

\[
P\{e(X)\le t\}\le Ct^{\gamma-1}
\qquad\text{for every }t\in[0,1].
\]

The strip example satisfies this bound with \(C=1\); its constant response satisfies smoothness.

Call the causal law class satisfying these restrictions \(\mathcal P_\gamma\).

---

## Main result

Fix \(\Gamma=[\gamma_{\min},\gamma_{\max}]\), with \(1<\gamma_{\min}<\gamma_{\max}<\infty\).

The effective dimension, benchmark mesh width, and error scale are

\[
D_\gamma=\frac{d\gamma}{\gamma-1},
\qquad
h_{\gamma,n}=n^{-1/(2\beta+D_\gamma)},
\qquad
r_{\gamma,n}=h_{\gamma,n}^{\beta}.
\]

Weak overlap increases effective dimension from \(d\) to \(D_\gamma\), slowing recovery.

@informal thm:adaptive-minimax: Under our fixed-constant causal model with known \(\beta>1\), one count-selected estimator has expected supremum error at most \(K r_{\gamma,n}\) for all sufficiently large \(n\), uniformly over \(\gamma\in\Gamma\) and \(P\in\mathcal P_\gamma\).

There are common constants \(K>0\) and \(n_0\) such that, for every \(n\ge n_0\), \(\gamma\in\Gamma\), and \(P\in\mathcal P_\gamma\),

\[
\mathbb E_{P^{\otimes n}}
\left[
\sup_{x\in\mathcal X}
\left|\widehat\mu_n(x)-\mu_{1,P}(x)\right|
\right]
\le K r_{\gamma,n}.
\]

Here \(\widehat\mu_n\) is our estimator, \(\mu_{1,P}\) is the response under \(P\), and \(P^{\otimes n}\) is the independent-sample law. We average each sample’s largest spatial error.

The estimator uses \(n,d,\beta,B,\mathcal D_n\). The same guarantee covers the strip’s center and the cube’s boundaries.

---

## Stable polynomial geometry

Partition the domain into cubes of side length \(h\), and normalize each cube to the unit cube.

Let \(U(z)=(z^\alpha)_{|\alpha|\le m}\) collect monomials through degree \(m\). Fixed tensor nodes \(v_\ell\), numbered \(\ell=1,\ldots,J\), identify every polynomial in this basis.

Their equally weighted fitting matrix is

\[
G_0=\frac{1}{J}\sum_{\ell=1}^{J}U(v_\ell)U(v_\ell)^\top,
\qquad
\lambda_0=\lambda_{\min}(G_0),
\]

where \(\lambda_0>0\) is its smallest eigenvalue.

- Place a small reference microcube \(V_\ell\) around each node; a **microcell** is its scaled copy inside a partition cube.
- Average observations within each microcell, then give every microcell total weight \(1/J\).
- Every fitting location remains close to its node, so the empirical fitting matrix has smallest eigenvalue at least \(\lambda_0/2\) whenever all counts are positive.

In the strip example, abundant observations near the central hyperplane cannot overwhelm the weights assigned to other locations.

---

## Mesh selection

Stable geometry still needs enough observations in each microcell.

Search candidate dyadic widths \(h\), which halve successively. Let \(\mathcal H_n\) be the candidate collection and \(\mathcal Q_h\) its cube partition.

For cube \(Q\), with corner \(a_Q\), place and count the fitting microcells:

\[
E_{Q\ell}=a_Q+hV_\ell,
\qquad
N_{Q\ell}=\sum_{i=1}^n\mathbf 1_{\{X_i\in E_{Q\ell},\,A_i=1\}}.
\]

Here \(E_{Q\ell}\) is a microcell and \(N_{Q\ell}\) its treated count.

Keep widths satisfying

\[
\mathcal F_n
=
\left\{h\in\mathcal H_n:
\min_{Q\in\mathcal Q_h,\,1\le\ell\le J}N_{Q\ell}
\ge h^{-2\beta}\right\},
\]

so **every** fitting microcell has enough treated observations.

Select the smallest feasible width, \(\widehat h=\min\mathcal F_n\). The threshold makes count-based noise scale \(N_{Q\ell}^{-1/2}\) no larger than approximation scale \(h^\beta\).

Selection uses observed treatment counts and known smoothness.

---

## Response estimator

At \(h=\widehat h>0\), fit a polynomial separately in each cube \(Q\).

Each treated observation in microcell \(E_{Q\ell}\) receives least-squares weight \(1/(JN_{Q\ell})\). Thus each microcell contributes total weight \(1/J\), regardless of its count.

Let \(\widehat c_Q\) be the resulting coefficient vector. Evaluate the polynomial throughout its cube:

\[
\widehat\mu_n(x)
=
\operatorname{clip}_{[-B,B]}
\left\{
U\left(\frac{x-a_Q}{h}\right)^\top\widehat c_Q
\right\},
\qquad
\operatorname{clip}_{[-B,B]}(t)=\max\{-B,\min\{B,t\}\}.
\]

Here \(Q\) contains \(x\), and \((x-a_Q)/h\) is its normalized location.

Clipping projects predictions onto the known response interval. If no width is feasible, output the zero function.

Stable fitting converts smoothness into approximation error bounded by a constant times \(h^\beta\), throughout each cube.

What guarantees enough treatment information at a useful width?

---

## Treatment information

For any covariate region \(E\), let \(u=P(X\in E)\). Global overlap implies

\[
P(A=1,X\in E)
\ge
\frac{\gamma-1}{\gamma}\,
C^{-1/(\gamma-1)}u^{\gamma/(\gamma-1)}.
\]

This bounds treated probability using only the region’s covariate probability: a large region cannot consist entirely of extremely small propensities.

Let \(q_{Q\ell}=P(A=1,X\in E_{Q\ell})\), and \(q_Q=\min_\ell q_{Q\ell}\). Sort the cubes by increasing \(q_Q\); \(q_{(k)}\) is rank \(k\).

To control rank \(k\):

- Select one weakest microcell from each of the \(k\) weakest cubes.
- Their disjoint union has covariate probability at least a constant times \(kh^d\), by coverage.
- Its treated probability is at most \(kq_{(k)}\), since each selected mass is at most \(q_{(k)}\).

Apply the regional bound to that union and divide by \(k\):

\[
q_{(k)}\ge \kappa_\Gamma h^{D_\gamma}k^{1/(\gamma-1)},
\qquad
D_\gamma=\frac{d\gamma}{\gamma-1},
\]

where \(\kappa_\Gamma>0\) is common across \(\Gamma\). Treatment information improves with rank.

---

## Bias–variance balance

The weakest treated microcell has mass at least a constant times \(h^{D_\gamma}\), hence expected count at least a constant times \(nh^{D_\gamma}\).

The benchmark width balances expected count against the feasibility threshold:

\[
n h_{\gamma,n}^{D_\gamma}
=
h_{\gamma,n}^{-2\beta}.
\]

At this width, approximation and sampling noise share scale \(r_{\gamma,n}\).

Count concentration connects this population balance to the selected width. With probability at least \(1-n^{-2}\),

\[
0<\widehat h\le K h_{\gamma,n},
\qquad
N_{Q\ell}\ge \frac{nq_{Q\ell}}5
\quad
\text{for every }Q\in\mathcal Q_{\widehat h}
\text{ and every }\ell.
\]

The first inequality controls approximation error. The second ensures empirical counts retain a fixed fraction of population information, including the improvement with rank.

How does that improvement control the largest noise error?

---

## A summable spatial maximum

Condition on sampled covariates and treatment indicators. In the cube of rank \(k\), each centered coefficient has variance proxy bounded, up to a common constant, by

\[
\min\!\left\{
\widehat h^{2\beta},
n^{-1}\widehat h^{-D_\gamma}k^{-1/(\gamma-1)}
\right\}.
\]

A variance proxy bounds the exponential moments of centered noise. Feasibility supplies the first term; ordered treated masses supply the second.

At the benchmark width, the second term equals the benchmark error squared times a decreasing rank factor.

For one coefficient coordinate, let \(Z_k\) be its centered error in rank-\(k\) cube, and let \(N\) be the number of cubes. For a positive standardized threshold \(u\), exponential tails and a union bound give

\(P(\max_{1\le k\le N}|Z_k|>u r_{\gamma,n}\mid (X_i,A_i)_{i=1}^n)\le 2\sum_{k=1}^N\exp\{-c u^2 k^{1/(\gamma-1)}\}\),

where \(c>0\) is a common constant.

For \(u\ge1\), extending the sum to infinitely many ranks gives an integrable tail bound, uniform over \(\Gamma\). Integrating it bounds the expected maximum by a constant times \(r_{\gamma,n}\).

There are only a fixed number of polynomial coefficients. No independence across cubes is needed.

---

## Finer selected widths

The selector may choose a width finer than the benchmark.

Then more ranks can remain at the common feasibility cap before the decreasing rank bound takes over.

- The number of capped ranks grows as a power of the benchmark-to-selected width ratio.
- Their maximum contributes the square root of its logarithm.
- Beyond those ranks, the exponentially decreasing tail sum again stays controlled.

The resulting conditional coefficient bound is

\[
\mathbb E\!\left[
\max_{Q\in\mathcal Q_{\widehat h}}
\left\|\widehat c_Q-
\mathbb E[\widehat c_Q\mid(X_i,A_i)_{i=1}^n]\right\|_\infty
\,\middle|\,(X_i,A_i)_{i=1}^n
\right]
\le K\widehat h^\beta
\sqrt{1+\max\{0,\log(h_{\gamma,n}/\widehat h)\}}
\le K'r_{\gamma,n}.
\]

Here the vector norm takes the largest absolute coefficient error. The factor \(\widehat h^\beta\) decreases fast enough to absorb the logarithm; \(\widehat h\le K h_{\gamma,n}\) handles coarser selections.

Stable geometry transfers coefficient control to response error. Clipping bounds loss on the exceptional samples, whose probability is at most \(n^{-2}\).

---

## Why the rate is optimal

For every fixed \(\gamma>1\) and every fixed \(x_0\in[0,1]^d\), including boundary points, there are constants \(0<c_\gamma\le K_\gamma<\infty\) such that, for every \(n\ge1\),

\[
\begin{aligned}
c_\gamma r_{\gamma,n}
&\le
\inf_T
\sup_{\substack{P\in\mathcal P_\gamma\\
P\text{ admits a causal completion with}\\
Y(0),Y(1)\in\{0,B\}\ \text{a.s.}}}
\mathbb E_{P^{\otimes n}}
\left|T(\mathcal D_n,x_0)-\mu_{1,P}(x_0)\right|
\\
&\le R_{\mathrm{pt}}(n,\gamma,x_0)
\le R_\infty(n,\gamma)
\le K_\gamma r_{\gamma,n}.
\end{aligned}
\]

The infimum ranges over all sample-based estimators \(T\). The supremum selects the hardest admissible law, already among two-valued potential outcomes. \(R_{\mathrm{pt}}\) and \(R_\infty\) are the minimax expected point error and expected largest spatial error.

The constants may depend on \(\gamma,x_0\), and fixed parameters. This fixed-exponent comparison holds from \(n=1\); the estimator’s upper guarantee has common \(K,n_0\) across \(\Gamma\).

The construction uses uniform covariates and a radial propensity centered at \(x_0\). Set the bump width to \(h=h_{\gamma,n}\), and perturb the response by \(\delta h^\beta\psi((x-x_0)/h)\), where \(\psi\) is a fixed smooth compactly supported bump and \(\delta>0\) is a fixed small constant. Thus the spatial width is \(h\), while the response height is of order \(h^\beta=r_{\gamma,n}\). Treatment mass in the bump region is of order \(h^{D_\gamma}\), so the sample information scales as \(nh^{D_\gamma+2\beta}\). At the benchmark width this remains bounded, and the two laws satisfy \(n\,\operatorname{KL}(P_{0,h},P_{1,h})\le\frac18\). Here \(\operatorname{KL}\) is relative entropy: the samples contain too little information to reliably distinguish the two responses.

---

## Open questions

Can one estimator adapt to both unknown response smoothness \(\beta\) and unknown overlap exponent \(\gamma\)?

- A proposed procedure compares equal-cell fits across polynomial degrees and count-feasible meshes.
- Sample splitting reserves separate observations for fitting and comparison.
- Attainment of the oracle scale, and any unavoidable logarithmic adaptation cost, remain open.

Gaïffas (2005) establishes a logarithmic cost of joint pointwise adaptation in a separate one-dimensional degenerate-design experiment. The corresponding question under global overlap tails remains unresolved.

---

## Takeaways

- **Geometry:** equal microcell weights preserve the covariate variation needed for polynomial fitting, even when treatment concentrates in a strip.
- **Information:** global overlap controls both the weakest treated masses and the number of poorly informed regions; the improving ranks make the spatial noise tail summable.
- **Recovery:** with known smoothness and our fixed model conditions, count selection attains the optimal pure-power expected supremum scale uniformly across compact overlap ranges, with matching fixed-exponent pointwise lower bounds.

---

## Appendix: Adaptive minimax response recovery

One count-selected estimator attains the expected supremum guarantee; bounded two-valued experiments establish matching pointwise minimax lower bounds.

@formal thm:adaptive-minimax

---

## Appendix: Thin-strip enlargement

An admissible global-tail design can violate local anti-concentration and have vanishing normalized treated variation in one coordinate.

@formal prop:strict-enlargement

---

## Appendix: Gaussian source transfer

The expected supremum upper guarantee transfers to fixed-constant Gaussian source envelopes under their retained restrictions.

@formal prop:dorn-a3-free-corollary
