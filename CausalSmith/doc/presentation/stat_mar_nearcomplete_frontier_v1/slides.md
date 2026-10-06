# Treatment Effect Precision With Missing Outcomes

Missing records reveal whose outcomes need correcting; using that information determines how precisely we can estimate a randomized experiment’s treatment effect.

---

## Research question

- We want the population average treatment effect when some primary outcomes never arrive.
- Every record retains baseline category, treatment, a binary surrogate measurement, and arrival status.
- The usual approach estimates outcome means or arrival probabilities within baseline–treatment–surrogate cells.
- Kallus and Mao (2025) establish identification and efficient estimation under conditions on the accuracy of these estimates.
- Arbitrarily rare categories can leave empirical outcome ratios with no arrived outcomes.

Identification survives rare categories. What precision can one estimator guarantee uniformly across such populations?

---

## Key idea

Estimate the arrived contribution directly, then restore the missing contribution using **missing cell membership as its weight**.

For \(n\ge1\) independent records and at most \(d\ge1\) baseline categories, define

\[
r_{n,d,q}
=
\frac{1}{n}
+
(1-q)^2
\min\left\{
1,
\left[\frac{d}{n\log(e+n)}\right]^2
\right\}
=
\frac{1}{n}+g_{n,d,q}^2.
\]

Here \(q\) is the known minimum cell arrival probability. The first term is sampling uncertainty; \(g_{n,d,q}\) is the additional root-error scale from missingness and dimension.

@informal thm:point-frontier: Under independent sampling, fair-coin treatment, consistency, cellwise missing at random, binary outcomes and surrogates, and known \(q\in[1/2,1]\), minimax squared error is bounded above and below by universal positive multiples of \(r_{n,d,q}\).

\[
c\,r_{n,d,q}\le \mathfrak R^*_{n,d,q}\le C\,r_{n,d,q},
\]

\(\mathfrak R^*_{n,d,q}\) is the smallest worst-population mean squared error among all sample-based estimators. Constants \(c,C\) do not depend on \(n,d,q\).

Honest confidence interval length has the square-root order of this benchmark.

---

## Example: two baseline labels

Take a pair from our population construction: two baseline labels, each with mass \(p_j/J\). Here \(p_j\) is their unnormalized mass and \(J\) normalizes the population.

The surrogate and control outcome are zero. Treated outcomes arrive with probability \(q\) at one label and probability one at its partner.

Write \(\mu\) for the treated outcome mean at the missing label. Its centered treatment contribution splits into:

- **Arrived:** \((p_j/J)q(\mu-1/2)\).
- **Missing:** \((p_j/J)(1-q)(\mu-1/2)\).

Centering preserves the target under fair-coin assignment: \(\mathbb E_P[2(2A-1)(Y-1/2)]=\mathbb E_P[Y(1)-Y(0)]=\tau(P)\). The two subtracted halves cancel between the equally likely treatment arms, while centering bounds each cell contribution.

Missing records reveal the second contribution’s weight. Arrived outcomes identify the mean used in both contributions.

The completely observed partner needs no correction. The challenge is recovering the missing label’s contribution when its arrival count is tiny.

---

## Model and assumptions

Let \(P\) be the population law. The target is

\[
\tau(P)=\mathbb E_P\!\left[Y(1)-Y(0)\right].
\]

\(Y(1),Y(0)\) are binary potential outcomes. Their mean difference lies in \([-1,1]\).

We observe \(n\) independent records \(O=(X,A,S,R,RY)\) with common law \(P_O\):

- \(X\): baseline category, with at most \(d\) occupied labels.
- \(A\): an independent fair-coin treatment assignment, independent of baseline and potential measurements.
- \(S\): a binary surrogate, always observed; consistency means \((S,Y)=(S(A),Y(A))\).
- \(R\): outcome-arrival indicator; \(RY\): observed outcome mark.

**Missing at random:** arrived and missing members have the same outcome mean within each observed cell.

\[
R\perp Y\mid(X,A,S).
\]

**Known arrival floor:** \(\rho_P(x,a,s)\) is the arrival probability in cell \((x,a,s)\).

\[
P(X=x,A=a,S=s)>0
\quad\Longrightarrow\quad
\rho_P(x,a,s)\ge q.
\]

Our class \(\mathcal M(d,q)\) imposes these conditions with \(q\in[1/2,1]\), while allowing arbitrary category masses and cell means.

In the example, treated arrival is drawn independently of the outcome; the missing label meets the floor exactly.

---

## Identification

Let \(\mu_P(x,a,s)\) be the mean outcome among arrivals in cell \((x,a,s)\).

\[
\Psi(P_O)
=
\sum_{x=0}^{d-1}\sum_{s=0}^{1}
\left\{
\frac{P_O(X=x,A=1,S=s)}{P_O(A=1)}\mu_P(x,1,s)
-
\frac{P_O(X=x,A=0,S=s)}{P_O(A=0)}\mu_P(x,0,s)
\right\},
\]

This averages arrived cell means using each arm’s distribution of baseline and surrogate measurements, then subtracts control from treatment. Both arm denominators equal one half.

@informal lem:identification-infrastructure: Under independent fair-coin treatment, consistency, missing at random within \((X,A,S)\), and arrival floor \(q\in[1/2,1]\), the observed-law functional \(\Psi(P_O)\) equals the population treatment effect \(\tau(P)\).

Missing at random transfers means to missing members; randomization connects arm means to potential-outcome means.

An identified population ratio can still have an empty sample denominator. We therefore estimate weighted contributions directly.

---

## Missing-mass correction

Index cells by \(j=(x,a,s)\), with treatment coordinate \(a_j=a\). Let \(G_j\) estimate the centered cell mean.

Draw an auxiliary count \(N\sim\operatorname{Poisson}(n/2)\). If \(N\le n\), randomly divide the first \(N\) records into four equally likely streams, each with mean size \(m=n/8\).

- Stream one estimates arrived contributions.
- Stream two supplies \(V_j\): the missing count in cell \(j\), divided by \(m\).
- Streams three and four select and estimate \(G_j\).

\[
\widetilde\tau
=\Pi_{[-1,1]}\!\left[
\frac2m\sum_{i\in\mathcal I_1}(2A_i-1)R_i
\left(Y_i^{\mathrm{obs}}-\frac12\right)
+2\sum_j(2a_j-1)V_jG_j
\right].
\]

\(\mathcal I_1\) is stream one and \(Y_i^{\mathrm{obs}}=(RY)_i\). The first term estimates arrived contributions; the second restores missing contributions. The factor two uses fair-coin assignment.

\(\Pi_{[-1,1]}\) projects onto the treatment-effect range. Set \(\widetilde\tau=0\) if \(N>n\).

For our missing treated label, \(V_j\) estimates \(p_j(1-q)/(2J)\). Thus \(2V_jG_j\) restores its missing contribution.

---

## Where ratios break

Let \(C_j\) and \(U_j\) be stream four’s arrival and arrived-success counts.

The centered ratio \(D_j\) equals \(U_j/C_j-1/2\) when \(C_j>0\), and zero otherwise.

In the untruncated Poisson experiment, counts across cells and streams are independent. Write \(z_j=mP_O((X,A,S)=j,R=1)\) for a cell’s expected arrival count.

Then
\(\mathbb E[D_j]=(\mu_P(x,a,s)-1/2)(1-e^{-z_j})\).

- A positive-count ratio recovers the mean in expectation.
- Zero arrivals occur with probability \(e^{-z_j}\), leaving that fraction of the centered mean unrecovered.

An independent stream-three arrival count \(C'_j\) chooses between a polynomial correction \(H_j\) and the ratio:

\[
G_j
=H_j\mathbf 1\{C'_j\le B/4\}
+D_j\mathbf 1\{C'_j>B/4\}.
\]

Here \(B=256\ell_n\), with \(\ell_n=\log(e+n)\). Sparse cells receive the polynomial; well-populated cells retain the ratio.

---

## Polynomial mean recovery

Choose \(k=\max\{1,\lfloor\ell_n/64\rfloor\}\) and define

\[
Q_k(z)=
\begin{cases}
\dfrac{1-T_k(1-2z/B)}{2k^2z/B},&z\ne0,\\[6pt]
1,&z=0,
\end{cases}
\qquad
1-Q_k(z)=\sum_{v=1}^{k-1}a_vz^v.
\]

\(T_k\) is the degree-\(k\) Chebyshev polynomial, satisfying \(T_k(\cos\theta)=\cos(k\theta)\). The coefficients \(a_v\) specify the correction; \(Q_k\) is its residual mean error.

Use
\(H_j=\sum_{v=1}^{k-1}a_v(U_j-C_j/2)(C_j-1)_{v-1}\).

The falling factorial \((C_j-1)_{v-1}\) multiplies consecutive decreasing counts. Under Poisson sampling, these count products estimate polynomial powers without plug-in bias:

\(\mathbb E[H_j]=(\mu_P(x,a,s)-1/2)[1-Q_k(z_j)]\).

Jiao et al. (2015) supply this polynomial-estimation architecture.

The correction replaces the ratio’s residual \(e^{-z_j}\) with the designed residual \(Q_k(z_j)\).

---

## Weighted error in the example

Return to the treated label with arrival probability \(q\), mean \(\mu\), and mass \(p_j/J\). Write \(z\) for its expected stream-four arrival count.

Its expected **unrecovered missing contribution** is:

- Using the ratio:
  \((p_j/J)(1-q)(\mu-1/2)e^{-z}\).
- Using the polynomial:
  \((p_j/J)(1-q)(\mu-1/2)Q_k(z)\).

The comparison concerns the weighted contribution, even if neither method accurately recovers the individual mean.

For any cell, missing mass is at most
\(\frac{1-q}{q}\frac{z_j}{m}\).
For \(0\le z\le B\), the polynomial satisfies \(z|Q_k(z)|\le B/k^2\).

Thus the doubled missing contribution has residual magnitude at most
\(\frac{1-q}{q m}\frac{B}{k^2}\).

Across at most \(4d\) cells, this gives aggregate bias of order \((1-q)d/(n\ell_n)\). The ratio instead leaves \(ze^{-z}\), whose maximum has constant order.

Small cells can have poor mean recovery because their missing contributions are correspondingly small.

---

## Bias and variability

A higher polynomial degree reduces residual bias, but also introduces higher count products whose variability can grow.

Our construction balances those effects:

- The degree grows only logarithmically, with a small multiplier: \(k=\max\{1,\lfloor\ell_n/64\rfloor\}\).
- The polynomial is designed for expected counts up to \(B=256\ell_n\).
- At large expected counts, the independent selector chooses the polynomial only on a Poisson lower-tail event.
- Independence makes that selection probability multiply the polynomial’s moment contribution. It suppresses dangerous large-count use without selecting unusually favorable correction data.

The resulting bound includes approximation error, count variability, and switching error:

\[
\mathbb E_P\!\left[
  \bigl(\widehat\tau_{\mathrm{MM}}-\tau(P)\bigr)^2
\right]
\le C_U r_{n,d,q},
\]

Here \(C_U\) is universal, and the bound holds for every \(P\in\mathcal M(d,q)\).

Projection and averaging over auxiliary randomization cannot increase squared error. The next definition specifies the procedure in every parameter regime.

---

## The estimator in every regime

The final estimator is

\[
\widehat\tau_{\mathrm{MM}}
=
\begin{cases}
\displaystyle
\Pi_{[-1,1]}\!\left[
\frac2n\sum_{i=1}^n(2A_i-1)Y_i^{\mathrm{obs}}
\right],
&q=1,\\[8pt]
\displaystyle
\Pi_{[-1,1]}\!\left[
\frac2n\sum_{i=1}^n(2A_i-1)R_i
\left(Y_i^{\mathrm{obs}}-\frac12\right)
\right],
&q\ne1\ \text{and}\ (\ell_n<128\ \text{or}\ d\ge n\ell_n),\\[8pt]
\displaystyle
\mathbb E[\widetilde\tau\mid O_1,\ldots,O_n],
&q\ne1,\ \ell_n\ge128,\ d<n\ell_n.
\end{cases}
\]

The branches compute, respectively, the complete-outcome difference, the centered arrived-only contribution, and the conditional average of our corrected estimate.

- At \(q=1\), no correction is needed: precision is \(1/n\), regardless of \(d\).
- At \(d\ge n\ell_n\), the dimension term is capped at \((1-q)^2\); arrived-only estimation already fits that benchmark.
- When \(\ell_n<128\), the finite sample-size range is covered by the universal-constant allowance.
- Otherwise, conditional expectation averages over the Poisson draw and stream assignments.

---

## Hard populations

For a lower bound, use many equal-mass label pairs. Let \(\sigma=-1,+1\) index two alternatives.

Within pair \(j\), \(z_j\in\{-1,1\}\) is a latent sign, distinct from the expected-count notation above. A fair orientation determines which label gets \(u=1\) and which gets \(u=-1\).

Set \(\delta=1-q\), \(b=1-\delta/2\), and \(c_0=1/16\). Treated arrival and outcome means are

\[
\rho_{\sigma,j,u}
=1-\frac{\delta}{2}(1+\sigma z_ju),
\qquad
\mu_{\sigma,j,u}
=\frac{b/2+c_0u}{\rho_{\sigma,j,u}}.
\]

One label arrives with probability \(q\), its partner with probability one. Surrogates and control outcomes are zero; treated arrival is independent of the treated outcome.

The product \(\rho_{\sigma,j,u}\mu_{\sigma,j,u}=b/2+c_0u\) stays fixed. Changing \(\sigma\) changes which outcome mean is associated with missingness.

With a filler label and exact normalization,
\(\tau(P_\sigma)=\mu_0+\frac{\sigma c_0\delta}{qJ}\sum_jp_jz_j\),
where \(\mu_0=b^2/(2q)\).

The effect changes through a signed first mass moment. Can every observed coordinate conceal that change?

---

## Concealing observed patterns

At one label, the four possible observed atoms have \((A,R,RY)\) equal to \((0,1,0),(1,0,0),(1,1,1),(1,1,0)\), respectively. Their coefficients are

\[
v_{\sigma}(z_j,u)
=
\left(
\frac12,
\frac{\delta(1+\sigma z_ju)}4,
\frac b4+\frac{c_0u}{2},
\frac b4-\frac{c_0u}{2}-\frac{\sigma\delta z_ju}{4}
\right).
\]

The surrogate is always zero. Both labels together retain the full observed information.

- **One record:** averaging the fair orientation removes every term proportional to \(u\). Missingness has coefficient \(\delta/4\); arrived success and failure each have coefficient \(b/4\), independent of \(\sigma\).
- **Multiple records:** products can reveal the association. A missing record and an arrived success at the same label produce a sign-dependent term proportional to \(p_j^2z_j\). An \(r\)-record pattern has sign-dependent terms involving \(p_j^rz_j\).

Here is the moment-matching distribution. Take shifted Chebyshev nodes \(x_i=(1+h)/2+(1-h)\cos(i\pi/(K-1))/2\), let \(l_i\) be their Lagrange cardinal polynomials, and put \(D=\sum_i|l_i(0)|\) and \(\nu_i=l_i(0)/D\). Draw \((p_j,z_j)=(B_0x_i,\operatorname{sign}\nu_i)\) with probability \(h|\nu_i|/x_i\), placing the remaining probability at \((0,1)\).

Lagrange interpolation at zero then gives \(\mathbb E[p_j^tz_j]=hB_0^t\sum_i\nu_i x_i^{t-1}\). This equals \(hB_0/D\) for \(t=1\) and vanishes for \(2\le t\le K\): powers visible to observed patterns cancel, while the first signed mass moment that moves the effect remains.

In the auxiliary Poisson likelihood, expanding its common exponential factor introduces higher mass powers. Matching moments cancels every sign-dependent term through order \(K\); the remaining Taylor terms and high-count events are small.

Wu and Yang (2016) supply the moment-matching tools. A parameter-independent ordering of the counts returns the first \(n\) records, preserving closeness and producing samples from the exactly normalized laws.

---

## The effect-separation scale

Let \(L=\log(e+n)\). The construction uses \(K=\lceil8L\rceil\), \(h=K^{-2}\), and \(B_0=\frac{K}{1024n}\).

The number of pairs is
\(M=\min\left\{\left\lfloor\frac{d-1}{2}\right\rfloor,\lfloor nL\rfloor\right\}\).

- The normalization \(D=\sum_i|l_i(0)|\) satisfies \(1\le D\le\cosh 2\). Hence each pair's signed first moment \(\mathbb E[p_jz_j]=hB_0/D\) has order \(1/(nL)\).
- Summing over \(M\) pairs supplies the dimension factor until the number of pairs reaches order \(nL\).
- The effect formula multiplies this sum by \(c_0\delta/q\) and divides by \(J\). Since \(q\ge1/2\), its denominator contributes only constant factors.
- The filler has mass \(f=1-2MhB_0\). Since \(\mathbb E[p_j]=hB_0\), the exact total mass \(J=f+2\sum_jp_j\) is centered at one.

The resulting separation scale is

\[
g_{n,d,q}=(1-q)\min\left\{1,\frac{d}{n\log(e+n)}\right\}
\]

This is the treatment-effect gap’s order: more pairs increase it until saturation, and improving arrival shrinks it by \(1-q\).

Write \(W=\sum_jp_jz_j\). Independence gives mean \(\mu_W=MhB_0/D\), variance at most \(M/(1024^2n^2)\), and \(\mathbb E[J]=1\) with variance at most \(4M/(1024^2n^2)\). For any fixed mixture tolerance \(\beta\), Chebyshev's inequality and a union bound give, for \(n\ge N_\beta\), probability at least \(1-\beta\) that \(W\ge\mu_W/2\) and \(1/2\le J\le3/2\). The exact effect formula then places the two effects on opposite sides of the common center \(\mu_0\), separated by constant multiples of \(g_{n,d,q}\), while the sample mixtures remain within \(\beta\). Calibrated one-label point priors cover \(n<N_\beta\); ordinary sampling lower bounds supply the \(1/n\) term.

---

## Main result: inference

An **honest interval** covers \(\tau(P)\) with probability at least \(1-\alpha\) for every \(P\in\mathcal M(d,q)\), at each sample size.

Let \(\mathfrak L^*_{n,d,q,\alpha}\) be the smallest worst-population expected length among honest connected intervals.

@informal thm:interval-frontier: For fixed \(\alpha\in(0,1/2)\), all \(n,d\ge1\), and known \(q\in[1/2,1]\), minimax honest connected-interval expected length over \(\mathcal M(d,q)\) is bounded above and below by positive multiples of \(\sqrt{r_{n,d,q}}\) depending only on \(\alpha\).

\[
c_\alpha\sqrt{r_{n,d,q}}
\le \mathfrak L^*_{n,d,q,\alpha}
\le C_\alpha\sqrt{r_{n,d,q}}.
\]

The constants depend only on coverage. To attain the upper bound, center at \(\widehat\tau_{\mathrm{MM}}\), intersect with \([-1,1]\), and use radius

\[
h_{n,d,q,\alpha}
=\min\left\{2,\sqrt{\frac{C_Ur_{n,d,q}}{\alpha}}\right\},
\]

\(C_U\) is the uniform risk constant. Markov’s inequality gives coverage, and length is at most twice the radius.

The close populations with separated effects force honest connected intervals to span the same precision scale.

---

## Open questions

- Arrival floors below one half, especially floors approaching zero.
- Adaptation when the arrival floor is unknown.
- Practical tuning: the exhibited polynomial branch requires \(n\ge e^{128}-e\); its risk constant gives the full interval \([-1,1]\) when \(\log(e+n)<128\).
- Efficient evaluation of conditional averaging with numerical error controlled.
- Sharper constants and empirical calibration supported by new risk and coverage guarantees.

---

## Takeaways

- Missing at random identifies the effect, but empty sample cells make uniform precision a separate question.
- Missing membership supplies correction weights. Polynomial count products reduce weighted residual bias without requiring accurate recovery of every cell mean.
- Matched observed-pattern moments conceal an effect gap of scale \(g_{n,d,q}\): optimal squared error is of order \(r_{n,d,q}\), and honest interval length is of order \(\sqrt{r_{n,d,q}}\).

---

## Appendix: Minimax estimation

This statement gives matching finite-sample upper and lower bounds for the smallest worst-population mean squared error.

@formal thm:point-frontier

---

## Appendix: Honest interval length

This statement gives matching bounds for worst-population expected length among connected intervals with uniform coverage.

@formal thm:interval-frontier
