# Treatment Effects With Missing Outcomes

We show how to estimate a population treatment effect when outcomes are selectively missing and many baseline groups have few observed outcomes.

---

## Motivation

A balanced randomized trial records everyone’s treatment, baseline category, and binary short-term measurement. Some binary primary outcomes are missing.

Ordinary adjustment weights observed group means by population group masses. An empty outcome group has no empirical mean; replacing it with zero loses its contribution.

Zeng et al. (2026), in the closest observational setting, give a plug-in squared-error bound of order \(n^{-1}+d^2/n^2\), alongside a logarithmically smaller minimax benchmark.

Here \(n\) is sample size and \(d\) is the number of baseline categories.

**How much precision can we recover when missing outcomes create many empty groups?**

---

## Key idea

Estimate group masses from everyone’s records. Correct sparse-group outcome contributions using polynomials of observed counts.

Let \(q\in(0,1]\) be a supplied lower bound on observation probability in every occupied group.

Our deterministic estimator has mean squared error at most a universal constant times

\[
r_{n,d,q}
:=
\min\left\{
1,\,
\frac{1}{nq}
+
\left[\frac{d}{nq\log(e+nq)}\right]^2
\right\}.
\]

The sampling term uses effective sample size \(N=nq\). The category term measures accumulated adjustment error; polynomial correction supplies its logarithmic improvement.

Under balanced randomization, consistency, independent sampling, and outcomes missing at random within groups, this upper bound holds for every positive \(q\).

It is minimax optimal when \(q\ell^2\le1/64\), where \(\ell=\log(e+N)\).

---

## Example

Consider our rare-category construction: balanced assignment, a constant short-term measurement, and zero control outcomes.

There are \(J\) rare baseline categories, each with mass \(b_0\), and one remaining category.

| Category | Population mass | Treated success mean | Observation probability |
|---|---|---|---|
| Rare category \(x\) | \(b_0\) | \(z_x^{-1}\) | \(qz_x\) |
| Remaining category | \(1-Jb_0\) | \(0\) | \(qH\) |

The fixed category parameters satisfy \(1\le z_x\le H\), \(qH\le1\), and \(Jb_0\le1/2\). Outcomes and observation are independent within categories.

The effect is \(\tau_{\mathrm{act}}(\mathbf z)=b_0\sum_{x=0}^{J-1}z_x^{-1}\).

For a rare treated cell, let \(t_j\) be its expected observed count in the estimation stream:

- The zero-filled ratio contributes \(b_0z_x^{-1}(1-e^{-t_j})\) in expectation.
- Our polynomial statistic contributes \(b_0z_x^{-1}\{1-Q_k(t_j)\}\), where \(Q_k\) is its residual fraction.

The later bound \(t|Q_k(t)|\le B/k^2\) makes the membership-weighted residual summable at scale \(d/\{N\log(e+N)\}\). **The correction changes the expected missing contribution across many cells.**

---

## Model

We observe \(n\) independent records from a common population law \(P\).

Each record is \(O_i=(X_i,A_i,S_i,R_i,R_iY_i)\); the sample is \(\mathbf O_n\).

- \(X_i\): baseline category, with \(d\) possible values.
- \(A_i\): treatment assignment.
- \(S_i\): binary short-term measurement, called the surrogate.
- \(R_i=1\): the binary primary outcome \(Y_i\) is observed.

Let \(Y(a)\) and \(S(a)\) denote potential outcomes and surrogates under arm \(a\).

Our target is

\[
\tau(P):=E_P[Y(1)-Y(0)],
\]

the population mean difference between treated and control potential outcomes.

---

## Assumptions

**Balanced randomization:** treatment is independent of baseline and all potential outcomes and surrogates, with probability one half.

**Consistency:** the realized variables are \(Y=Y(A)\) and \(S=S(A)\).

**Missing at random:** within a treatment–baseline–surrogate cell, observation does not select outcomes.

\[
R\perp\!\!\!\perp Y\mid(X,A,S).
\]

**Positive observation:** write \(p_{axs}(P)\) for cell mass and \(\rho_{axs}(P)\) for its observation probability.

\[
p_{axs}(P)>0
\quad\Longrightarrow\quad
\rho_{axs}(P)\ge q.
\]

Cell masses and observation probabilities can otherwise vary arbitrarily.

In the example, conditional independence guarantees missing at random, and \(qz_x\ge q\) guarantees positive observation.

---

## Identification

Missing at random makes the observed-outcome mean equal the full-cell mean.

\[
\mu_{axs}(P):=E_P[Y\mid A=a,X=x,S=s,R=1],
\qquad
c_{axs}(P):=p_{axs}(P)\mu_{axs}(P).
\]

Here \(\mu_{axs}(P)\) is the observed-outcome mean; \(c_{axs}(P)\) is its population-weighted contribution.

\[
\tau(P)=\Phi(P)
=2\sum_{(a,x,s)\in\mathcal J_d}g(a)c_{axs}(P).
\]

The set \(\mathcal J_d\) contains the \(4d\) treatment–baseline–surrogate cells. The sign \(g(a)=2a-1\) adds treated contributions and subtracts controls. Balanced assignment supplies the factor two; \(\Phi(P)\) names the observable contrast.

**Everyone’s records identify masses. Observed outcomes identify means.**

---

## Main result

Call the preceding sampling, randomization, consistency, and observation conditions the **trial assumptions**.

@informal thm:unrestricted-mixed-count-upper: With independent sampling, balanced randomization, consistency, and missing at random with occupied-cell observation at least \(q\), our deterministic estimator has risk at most \(C r_{n,d,q}\) for all \(n,d\ge1\) and \(0<q\le1\).

The guarantee is

\[
E_P\!\left[
 \bigl(\widehat\tau^{\mathrm{mix}}_{n,d,q}(\mathbf O_n)-\tau(P)\bigr)^2
\right]
\le \mathfrak U_{n,d,q}
\le \overline C\,r_{n,d,q},
\]

where \(\widehat\tau^{\mathrm{mix}}_{n,d,q}\) is our estimator and \(\mathfrak U_{n,d,q}\) is its known deterministic risk bound.

@informal thm:matched-minimax-frontier: In the **rare-arrival regime** \(q\ell^2\le1/64\), under the trial assumptions with \(n,d\ge1\) and \(0<q\le1\), the smallest worst-case mean squared error is between universal positive constants times \(r_{n,d,q}\).

Writing \(\mathfrak R_{n,d,q}\) for that minimax risk,

\[
\underline c\,r_{n,d,q}
\le \mathfrak R_{n,d,q}
\le \overline C\,r_{n,d,q}.
\]

For the rare-category example, the guarantee controls error in the sum of reciprocal category means—even when individual means are poorly estimated.

---

## Separate the estimation tasks

Draw an independent auxiliary prefix length:

\[
K_0\sim\operatorname{Poisson}(n/2).
\]

Assign each prefix record independently to three equally likely streams:

- **Membership:** estimate cell masses, including records with missing outcomes.
- **Pilot:** select which cells need correction.
- **Estimation:** calculate outcome statistics.

Sample splitting separates these tasks. In the uncapped Poisson experiment used for analysis, counts are also independent across cells.

Let \(M_j\) count membership records in cell \(j=(a,x,s)\), and let \(m=n/6\) be expected stream size.

\[
W_j=\frac{M_j}{m}.
\]

The weight \(W_j\) estimates population mass \(p_j=p_{axs}(P)\), independently of outcome correction.

---

## Empty-cell bias

In the estimation stream, let \(C_j\) count observed outcomes and \(U_j\) count observed successes.

The ordinary cell mean is

\[
D_j=
\begin{cases}
U_j/C_j, & C_j>0,\\
0, & C_j=0.
\end{cases}
\]

Write \(\mu_j\) for the cell outcome mean, \(\rho_j\) for its observation probability, and \(t_j=mp_j\rho_j\) for expected observed count.

In the Poisson comparison experiment,

\[
E_{\mathrm{Pois}}D_j=\mu_j(1-e^{-t_j}),
\qquad 0\le D_j\le1.
\]

The lost fraction \(e^{-t_j}\) is the probability of no observed outcome.

In our example, the treated cell has \(p_j=b_0/2\), \(\mu_j=z_x^{-1}\), and \(\rho_j=qz_x\). Its missing effect contribution is \(b_0z_x^{-1}e^{-t_j}\).

**Accurate population weights do not repair an empty outcome cell.**

---

## Polynomial branch

Use polynomial correction when **\(\ell\ge128\) and \(d\ge\sqrt N\)**. For \(N>1\), the remaining regimes use ordinary ratios.

On that elementary branch the certificate is, with effective stream size \(N_0=mq=N/6\) and prefix-tail constant \(\gamma_0=\log 2-1/2\),

\[
\mathfrak U_{n,d,q}
=\min\left\{
4,\,
\left(\frac{8d}{eN_0}\right)^2
+4\left(\frac4{N_0}+\frac1m\right)
+4e^{-n\gamma_0}
\right\}.
\]

If \(d<\sqrt N\), its category term is absorbed by \(N^{-1}\); if \(\ell<128\), bounded \(\ell\) makes it comparable to the advertised \(d^2/(N^2\ell^2)\) term.

Jiao et al. (2015) and Wu and Yang (2019) supply the approximation-to-count-statistic framework for discrete functionals. Here it is adapted to separately estimated membership weights, marked factorial counts, pilot selection, and a capped fixed-sample prefix.

Choose degree \(k=\lfloor\ell/64\rfloor\) and threshold \(B=256\ell\). The Chebyshev polynomial \(T_k\), characterized by \(T_k(\cos u)=\cos(ku)\), is bounded by one in absolute value on \([-1,1]\).

Define the residual polynomial

\[
Q_k(t):=
\begin{cases}
\displaystyle\frac{1-T_k(1-2t/B)}{2k^2t/B},&t>0,\\[6pt]
1,&t=0.
\end{cases}
\]

Here \(t\) is expected observed count. We want a count statistic whose expected residual is \(Q_k(t)\).

**How can we use a polynomial of an unknown count intensity?**

---

## From polynomials to counts

Expand the correction in powers of intensity:

\[
1-Q_k(t)=\sum_{v=1}^{k-1}a_vt^v,
\qquad
G_j=\mathbf1_{\mathsf L_j}H_j+
\mathbf1_{\mathsf L_j^c}D_j
\quad(t\ge0).
\]

The coefficients \(a_v\) define the polynomial statistic \(H_j\). The second equality defines selection: \(\mathsf L_j=\{C'_j\le B/4\}\), where \(C'_j\) is the independent pilot’s observed count.

For integer \(v\ge1\), let \(\mathsf F_{j,v}=U_j\prod_{h=1}^{v-1}\max\{C_j-h,0\}\). This counts ordered distinct outcome tuples whose first member is a success.

\[
E_{\mathrm{Pois}}\mathsf F_{j,v}
=t_j^v\mu_j.
\]

Thus \(H_j=\sum_{v=1}^{k-1}a_v\mathsf F_{j,v}\) satisfies

\[
E_{\mathrm{Pois}}H_j
=\mu_j\{1-Q_k(t_j)\}.
\]

Count products estimate the intensity powers without knowing observation probabilities.

---

## Weighted bias

For intensities \(0\le t\le B\), the Chebyshev bound gives

\[
t|Q_k(t)|\le\frac B{k^2}.
\]

Positive observation connects intensity to population mass: \(t_j\ge mq\,p_j\).

Consequently, the absolute weighted residual \(p_j\mu_j|Q_k(t_j)|\) is at most \(B/(mqk^2)\).

- There are \(4d\) cells to aggregate.
- \(B\) grows with \(\ell\), while \(k^2\) grows with \(\ell^2\).
- The aggregate bias therefore has scale \(d/(N\ell)\), including pilot selection.

In the running example, the missing contribution changes from \(b_0z_x^{-1}e^{-t_j}\) to \(b_0z_x^{-1}Q_k(t_j)\) for the polynomial statistic.

This controls the **weighted sum**; it does not require recovering each rare mean accurately.

---

## Controlling noise

High-degree count products can be noisy. The pilot uses \(H_j\) when \(C'_j\le B/4\) and the stable ratio \(D_j\) otherwise.

Controlled degree bounds polynomial noise when \(t_j\le B\):

\[
E_{\mathrm{Pois}}H_j^2
\le e^{k^2/B+6k}\le e^{\ell/8}
\quad(t_j\le B).
\]

For \(t_j>B\), mistaken polynomial selection is sufficiently unlikely:

\[
\Pr_{\mathrm{Pois}}(\mathsf L_j)E_{\mathrm{Pois}}H_j^2
\le e^{-t_j/8}\le e^{-32\ell}.
\]

For the raw contrast \(\tau_{\mathrm{raw}}=2\sum_jg(a)W_jG_j\), these controls imply, on the polynomial branch,
\(\operatorname{Var}_{\mathrm{Pois}}(\tau_{\mathrm{raw}})\le C\{N^{-1}+(\frac{d}{N\ell})^2\}\).

Its three noise sources are ordinary ratio and membership fluctuations, sparse-cell polynomial fluctuations, and mistaken correction of dense cells.

**The correction’s noise fits within the advertised risk scale.**

---

## Reported estimator

On the polynomial branch, use
\(G_j=\mathbf1\{C'_j\le B/4\}H_j+\mathbf1\{C'_j>B/4\}D_j\).
Otherwise use \(G_j=D_j\).

When \(K_0\le n\) and \(N>1\), aggregate:

\[
\widetilde\tau(\mathbf O_n;\omega)
=
\operatorname{clip}_{[-1,1]}
\left\{
2\sum_{j=(a,x,s)}g(a)W_jG_j
\right\}.
\]

This estimates the identified contrast using independent membership weights and selected outcome statistics.

Clipping replaces values outside the treatment-effect range by the nearest endpoint. Report zero if \(N\le1\) or the prefix exceeds \(n\).

Average over the prefix and stream randomization \(\omega\):

\[
\widehat\tau^{\mathrm{mix}}_{n,d,q}(\mathbf O_n)
:=
E_\omega\!\left[
\widetilde\tau(\mathbf O_n;\omega)\mid\mathbf O_n
\right].
\]

Conditional averaging removes auxiliary variation and cannot increase squared-error risk. The prefix-overflow probability is exponentially small.

---

## Hard rare populations

Return to the example. To prove its difficulty, choose a fixed small \(\eta>0\) and set

\[
K=\lceil\ell\rceil,\qquad H=K^2,\qquad
b_0=\frac{\eta}{N\ell},\qquad
J=\min\left\{d-1,\left\lfloor\frac1{2b_0}\right\rfloor\right\}.
\]

Here \(K\) is the moment-matching degree, \(H\) bounds category parameters, \(b_0\) is rare-category mass, and \(J\) is their number.

Draw each \(Z_x\) once for the whole sample from one of two distributions, \(\Pi_0\) or \(\Pi_1\).

The approximation and moment-matching tools of Wu and Yang (2019) give equal moments through degree \(K\), but

\[
\left|\int z^{-1}\,d\Pi_1(z)-\int z^{-1}\,d\Pi_0(z)\right|
\ge \frac{1}{12}.
\]

Thus ordinary moments agree while the reciprocal means determining the treatment effect differ.

---

## Indistinguishable records

Give the analyst extra information: an independent revealed flag
\(\mathsf B_{\mathrm{act}}\sim\operatorname{Bernoulli}(qH)\).

When the flag is zero, the outcome is missing. When it is one, generate:

\[
\begin{array}{c|ccc}
 & (R,RY)=(1,1) & (R,RY)=(1,0) & (R,RY)=(0,0)\\ \hline
 A=1,\ X=x<J & 1/H & (Z_x-1)/H & 1-Z_x/H\\
 A=0,\ X=x<J & 0 & Z_x/H & 1-Z_x/H\\
 X\ge J,\ \text{either arm} & 0 & 1 & 0
\end{array}
\]

The columns are observed success, observed zero, and missing outcome. Forgetting the flag recovers the actual example.

Each flagged record contributes an affine likelihood factor in \(Z_x\). At most \(K\) flags therefore give a polynomial of degree at most \(K\), hidden by matched moments.

Rare arrival ensures \(qH\le1\); the chosen masses make exceeding \(K\) flags in any rare category unlikely.

**Even this more informative experiment struggles to distinguish the populations.**

---

## Necessary estimation error

Let \(\Delta_{\mathrm{act}}\) be the difference between the two prior mean treatment effects.

\[
\Delta_{\mathrm{act}}\ge\frac{Jb_0}{12}.
\]

The effects concentrate around those means, while the observed sample distributions remain close.

A sufficiently accurate estimator would distinguish the two populations. The testing comparison therefore gives, for sufficiently large \(N\) and \(J\ge2048\),

\[
\frac{(Jb_0)^2}{4096}\le\mathfrak R_{n,d,q}.
\]

Since \(b_0=\eta/(N\ell)\) and rare-category mass is capped, this supplies the squared category contribution, including constant-risk saturation.

The sampling contribution comes from one category with treated success mean \(\mu_{\mathrm{one}}\), zero control outcomes, and independent observation probability \(q\). Only observed treated outcomes inform the mean: their expected number is \(nq/2\).

Together these constructions deliver the matching lower bound.

---

## Honest intervals

For miscoverage \(\alpha\in(0,1)\), use the known deterministic risk bound \(\mathfrak U_{n,d,q}\):

\[
I^{\mathrm{mix}}_\alpha
:=
\left[
\widehat\tau^{\mathrm{mix}}_{n,d,q}
-
\sqrt{\frac{\mathfrak U_{n,d,q}}{\alpha}},
\,
\widehat\tau^{\mathrm{mix}}_{n,d,q}
+
\sqrt{\frac{\mathfrak U_{n,d,q}}{\alpha}}
\right]\cap[-1,1],
\]

an interval centered on our estimator with radius calibrated from worst-case mean squared error.

Markov’s inequality bounds the probability of exceeding this radius by \(\alpha\). Coverage is therefore at least \(1-\alpha\) for every admissible population: the interval is **uniformly honest**.

@informal thm:connected-interval-frontier: Under the trial assumptions, \(n,d\ge1\), \(0<q\le1\), and \(q\ell^2\le1/64\), our interval is uniformly honest and has minimax maximal expected length of order \(\sqrt{r_{n,d,q}}\) for each fixed \(\alpha\in(0,1)\).

Writing \(\mathfrak L_{n,d,q,\alpha}\) for the smallest worst-case expected length among uniformly honest connected intervals, the theorem gives constants depending only on fixed \(\alpha\) such that

\[
\underline c_\alpha\sqrt{r_{n,d,q}}
\le \mathfrak L_{n,d,q,\alpha}
\le \sup_{P\in\mathcal M_{n,d,q}}
E_P\!\left[\operatorname{length}(I^{\mathrm{mix}}_\alpha)\right]
\le \overline C_\alpha\sqrt{r_{n,d,q}}.
\]

Here \(\mathcal M_{n,d,q}\) contains populations satisfying the trial assumptions and rare-arrival restriction; the middle upper bound is our interval’s worst-case expected length.

Why must an honest interval have this much width?

---

## Necessary interval width

Our **joint-law total-variation comparison** transfers coverage between close sample distributions, including procedures with randomized endpoints.

Total variation bounds how much an event’s probability can differ between two experiments.

For every fixed positive coverage level:

- Mix \(\Pi_0\) and \(\Pi_1\) along a finite grid. All grid distributions retain the matched moments.
- Their effect centers span \(\Delta_{\mathrm{act}}\ge Jb_0/12\); effects concentrate near those centers.
- The flag argument keeps all sample distributions close. Coverage of each target neighborhood therefore transfers to a common experiment.
- A connected interval meeting several separated neighborhoods must span their separation.

This forces expected width proportional to the rare-category separation. A grid in the one-category family supplies the sampling-width contribution.

**The interval lower bound uses coverage and connectedness, alongside the same statistical indistinguishability.**

---

## Near-complete observation

When almost every outcome is observed, directly contrast observed successes:

\[
\widehat\tau^{\mathrm{HT}}_n(\mathbf O_n)
:=
\Pi_{[-1,1]}\!\left\{
\frac{2}{n}\sum_{i=1}^n
(2A_i-1)\mathbf{1}\{R_i=1,\ R_iY_i=1\}
\right\},
\qquad n\ge1.
\]

The indicator selects observed successes; treatment signs add treated successes and subtract controls. The operator \(\Pi_{[-1,1]}\) clips to the target range.

Let \(\mathcal M^+_{n,d,q}\) denote the trial model with any positive observation floor, without the restriction \(q\ell^2\le1/64\).

\[
\sup_{P\in\mathcal M^{+}_{n,d,q}}
E_P\!\left[
\left\{
\widehat\tau^{\mathrm{HT}}_n(\mathbf O_n)-\tau(P)
\right\}^{2}
\right]
\le
\frac4n+(1-q)^2,
\]

for every \(d\). Variance is at most \(4/n\); each arm’s missing-success fraction is at most \(1-q\), so absolute contrast bias is at most \(1-q\).

---

## Hard large-category populations

To see why the missing fraction matters, take a uniform baseline distribution over \(d\) categories, balanced assignment, zero surrogates, and zero control outcomes.

Write \(\delta=1-q\).

| Population | Treated outcome in category \(x\) | Treated observation probability |
|---|---|---|
| \(P_\xi\) | Fixed binary value \(\xi_x\) | \(q\) if \(\xi_x=1\); \(1\) if \(\xi_x=0\) |
| \(P_\star\) | Bernoulli mean \(q/(1+q)\) | \((1+q)/2\), independent of outcome |

Controls are always observed. Draw the category values \(\xi_x\) independently as fair coins, once for the entire sample.

Every fixed population satisfies missing at random: outcomes under \(P_\xi\) are constant within cells, and observation under \(P_\star\) is independent of outcomes.

The effects under \(P_\xi\) concentrate near \(1/2\), while \(\tau(P_\star)=q/(1+q)\). Their center separation is

\[
h_{\mathrm{sep}}
:=\frac12-\frac q{1+q}
=\frac{\delta}{2(1+q)}.
\]

Thus separation is at least \(\delta/4\).

---

## Single visits hide selection

A single treated visit has identical observed probabilities under the fair-coin mixture of \(P_\xi\) and under \(P_\star\):

| Recorded status | Probability under either experiment |
|---|---|
| Observed success | \(q/2\) |
| Observed zero | \(1/2\) |
| Missing outcome | \(\delta/2\) |

Only repeated treated visits to the same category reveal the distinction. Their probability is at most \(n^2/(8d)\).

For \(d\ge1024n^2\), this is small. When \(\delta^2>n^{-1}\), effect concentration and the separation force error proportional to \(\delta^2\); otherwise the sampling lower bound suffices.

\[
\max\left\{\frac{1}{256n},\frac{(1-q)^2}{1024}\right\}
\le \mathfrak R^{+}_{n,d,q}
\le \frac{4}{n}+(1-q)^2.
\]

Here \(\mathfrak R^+_{n,d,q}\) is minimax risk without the restriction \(q\ell^2\le1/64\).

@informal prop:unrestricted-uniform-near-complete-elbow: Under the trial assumptions, for any sequence \(0<q_n\le1\), minimax risk is eventually \(O(n^{-1})\) with one constant for every \(d\ge1\) if and only if \(1-q_n=O(n^{-1/2})\).

---

## Open questions

- Match estimation risk and honest interval length throughout intermediate moving-observation and category regimes.
- Characterize the observation requirement along individual smaller-category sequences, and extend the model beyond missing at random.
- Develop practical evaluation: the polynomial branch starts at \(nq\ge e^{128}-e\), and exact conditional averaging enumerates exponentially many assignments.

---

## Takeaways

- Full membership records identify population weights. Empty outcome cells still create accumulated adjustment bias.
- Count polynomials replace that residual bias; controlled degree and independent pilot selection keep noise within the risk bound. Under rare arrival, the resulting rate is minimax optimal.
- Across arbitrary category counts, single visits can hide selective observation. Parametric risk uniformly over all \(d\) requires and is delivered by \(1-q_n=O(n^{-1/2})\).

---

## Appendix: Matched minimax frontier

Under rare arrival, the count estimator attains the smallest possible worst-case squared-error order.

@formal thm:matched-minimax-frontier

On the polynomial branch, the detailed variance allowance is

\[
v_{n,d,q}
=8\left(\frac4{N_0}+\frac1m\right)
+64d(e^{\ell/8}+1)
\left(\frac{B^2}{N_0^2}+\frac{B}{mN_0}\right)
+32e^{-32\ell}\left(1+\frac1m\right).
\]

Here \(N_0=mq=N/6\). The three terms bound ratio and membership noise, sparse-cell correction noise, and mistaken dense-cell correction.

---

## Appendix: Connected interval length frontier

At every fixed coverage level, our honest interval attains the optimal worst-case expected length under rare arrival.

@formal thm:connected-interval-frontier

---

## Appendix: Uniform near-complete arrival elbow

The missing fraction must be of order \(n^{-1/2}\) or smaller to guarantee parametric risk simultaneously over every category count.

@formal prop:unrestricted-uniform-near-complete-elbow

---

## Appendix: Fixed positivity polynomial frontier

Synthetic assignment transfers the count estimator to the observational regression contrast and attains its minimax order at fixed strict positivity.

@formal thm:zeng-fixed-positivity-polynomial-frontier
