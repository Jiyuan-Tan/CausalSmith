# Total Effects From Sampled Networks

Knowing how network arrows were sampled lets us estimate the effect of treating everyone and determine how much collection precision requires.

---

## Motivation

One experiment assigns treatment to some units, but treatment can also affect their neighbors.

We want the population effect of treating everyone rather than no one:

\[
\tau(\theta)
=\frac1n\sum_{i\in V}
\bigl(Y_i(\mathbf1)-Y_i(\mathbf0)\bigr),
\]

Here \(V\) contains \(n\ge4\) units; \(Y_i\) is unit \(i\)’s potential outcome. The assignments \(\mathbf1,\mathbf0\) treat everyone and no one. The fixed schedule \(\theta\) specifies the network and response coefficients.

This target includes both own-treatment effects and spillovers. How can one mixed assignment reveal their sum?

---

## Research question

Cortez-Rodriguez et al. (2023) estimate this contrast by combining outcomes with treatments in known neighborhoods.

- Every possible treatment source enters the score.
- Using an incomplete neighborhood omits contributions from missing sources.
- Outcomes may themselves help reveal missing connections.

Let \(d\) bound both sources per recipient and recipients per source. Let \(q\) be the known probability of retaining each true arrow.

What is the best worst-case squared error when estimators can use sampled arrows, every assignment, and every outcome?

---

## Key idea

Weight each retained arrow by \(1/q\). Its contribution represents retained and omitted arrows on average.

Under bounded additive responses, noiseless outcomes, independent half-probability treatment assignment, and independent arrow retention, optimal squared risk has this order for \(q>0\):

\[
\min\left\{1,\frac{d^2}{n}+\frac{d}{nq}\right\}.
\]

- \(d^2/n\): uncertainty from the experiment even with the full network.
- \(d/(nq)\): the precision cost of sampled network information.
- The cap reflects a causal target bounded in magnitude by one.

The coefficient bound includes the baseline and all treatment effects. At \(q=0\), worst-case risk remains of constant order.

---

## Example

Take the supported case \(d=1\). Each unit has at most one source and reaches at most one recipient.

For a source–recipient arrow \(j\to i\), the recipient response is \(Y_i(Z)=a_i+t_iZ_i+b_{ij}Z_j\): baseline \(a_i\), own effect \(t_i\), and spillover \(b_{ij}\).

Write \(X_j=2Z_j-1\), the source’s treatment sign, and \(W_{ij}\) for whether its arrow is retained.

The corrected spillover contribution is \(2Y_i(Z)W_{ij}X_j/q\). Its expectation is \(b_{ij}\), even though the arrow appears only with probability \(q\).

@informal thm:supported-boundaries: Under the bounded additive model and independent assignment–retention design, \(d=1\) gives \(c/(1+nq)\le R_{n,1}(q)\le C_0/(1+nq)\), with universal positive constants.

Here \(R_{n,1}(q)\) is optimal worst-case squared error. Collection affects precision even with one source per outcome.

---

## Model

The true directed graph \(G\) contains arrows \((j,i)\) from source \(j\) to recipient \(i\).

\[
Y(z)=(Y_i(z))_{i\in V},
\qquad
Y_i(z)=a_i+t_i z_i+\sum_{j:(j,i)\in G}b_{ij}z_j,
\qquad z\in\{0,1\}^V.
\]

The binary vector \(z\) specifies treatment. Baselines \(a_i\), own effects \(t_i\), and spillovers \(b_{ij}\) are fixed and heterogeneous.

- Incoming degree at most \(d\) limits sources per outcome.
- Outgoing degree at most \(d\) limits how widely one treatment propagates.
- The integer \(d\) satisfies \(1\le d\le n-1\).

\[
\max_{i\in V}
\left(
|a_i|+|t_i|+\sum_{j:(j,i)\in G}|b_{ij}|
\right)\le 1,
\]

This bounds outcomes and the target by one in magnitude. In our pair example, it becomes \(|a_i|+|t_i|+|b_{ij}|\le1\). Denote the allowed schedules by \(\mathcal M_{n,d}\).

---

## Observation design

- Every treatment \(Z_j\) is independently assigned with probability one half.
- Every true arrow between distinct units is independently retained with known probability \(q\in[0,1]\).
- Retention is independent of treatment; every recorded arrow is true.

\[
H=\{(j,i)\in G:W_{ij}=1\},
\qquad
O=(H,Z,Y(Z)),
\]

The binary mark \(W_{ij}\) records retention, \(H\) is the sampled graph, and \(O\) is the complete observed record.

We observe every assignment and every noiseless realized outcome. Own-treatment coordinates are always available.

In the pair example, \(Y_i(Z)\) remains observed when \(j\to i\) is missing.

---

## Precision criterion

We compare every estimator of the complete record.

\[
R_{n,d}(q)
=
\inf_T\sup_{\theta\in\mathcal M_{n,d}}\mathcal L(T;\theta,q),
\qquad
\mathcal L(T;\theta,q)
=
\mathbb E_{P_{\theta,q}}
\left[(T(O,\xi)-\tau(\theta))^2\right].
\]

Here \(\mathcal L\) is expected squared error for a fixed schedule. The law \(P_{\theta,q}\) averages over assignment and retention; \(\xi\) is an independent seed allowing randomized estimators.

The supremum chooses the worst allowed schedule; the infimum chooses the best estimator.

A lower bound on \(R_{n,d}(q)\) therefore covers methods that infer missing connections from outcomes.

---

## Main result

Define the precision scale:

\[
F(n,d,q)=
\begin{cases}
\min\left\{1,\dfrac{d^2}{n[1-(1-q)^d]}\right\},&q>0,\\
1,&q=0.
\end{cases}
\]

The factor \(1-(1-q)^d\) is the probability of retaining at least one of \(d\) arrows.

@informal thm:observed-record-precision-frontier: For \(n\ge4\), \(1\le d\le n-1\), and \(q\in[0,1]\), under our bounded additive model and independent assignment–retention design, the observable rule \(T^\star_{n,d,q}\) attains minimax squared risk within universal constants of \(F(n,d,q)\).

\[
cF(n,d,q)
\le R_{n,d}(q)
\le
\sup_{\theta\in\mathcal M_{n,d}}
\mathcal L(T^\star_{n,d,q};\theta,q)
\le C_0F(n,d,q).
\]

The positive constants \(c,C_0\) work uniformly over all admissible parameters. The rule \(T^\star_{n,d,q}\) clips the weighted score when its error bound is below one and returns zero otherwise.

---

## Retention regimes

Why do the two expressions for precision agree?

Put \(p=1-(1-q)^d\), the probability that at least one arrow is retained, and \(\alpha_{\mathrm{ret}}=1-e^{-1}\).

\[
\alpha_{\mathrm{ret}}\min\{1,dq\}\le p\le\min\{1,dq\}.
\]

Thus \(p\asymp\min\{1,dq\}\), where \(\asymp\) means comparison by universal positive constants.

- When \(dq\le1\), \(p\) is comparable to \(dq\), so \(d^2/(np)\) is comparable to \(d/(nq)\).
- When \(dq>1\), \(p\) is bounded away from zero, so \(d^2/(np)\) is comparable to \(d^2/n\).

The larger of the two components determines the order; their sum has the same order. Retention around \(1/d\) marks the transition.

---

## Known-graph score

For every unit, define \(X_j=2Z_j-1\): treated units have sign \(+1\), controls sign \(-1\).

The additive known-neighborhood score of Cortez-Rodriguez et al. (2023) is

\[
T_G
=
\frac2n\sum_{i\in V}Y_i(Z)
\left(X_i+\sum_{j:(j,i)\in G}X_j\right).
\]

Each outcome is multiplied by its own sign and every true source sign, then averaged.

Independence makes these signs extract individual additive effects:

- \(2\mathbb E_Z[Y_i(Z)X_i]=t_i\).
- For a true source \(j\), \(2\mathbb E_Z[Y_i(Z)X_j]=b_{ij}\).
- Baselines disappear because signs have mean zero.

Consequently, \(\mathbb E_Z[T_G]=\tau(\theta)\). The missing ingredient is the true source list.

---

## Correction for missing arrows

Inverse-inclusion weighting, following Horvitz and Thompson (1952), restores the missing contributions:

\[
T_q
=
\frac2n\sum_{i\in V}Y_i(Z)
\left(X_i+q^{-1}\sum_{j:(j,i)\in H}X_j\right),
\qquad q>0.
\]

This observable score weights each retained source sign by \(1/q\); the own-treatment sign needs no correction.

For our pair \(j\to i\):

- Uncorrected contribution: \(\mathbb E[2Y_i(Z)W_{ij}X_j]=qb_{ij}\).
- Corrected contribution: \(\mathbb E[2Y_i(Z)W_{ij}X_j/q]=b_{ij}\).

More generally, for every fixed assignment \(z\), \(\mathbb E_W[T_q(z,W)]=T_G(z)\), where \(\mathbb E_W\) averages retention.

Thus \(\mathbb E_{P_{\theta,q}}[T_q]=\tau(\theta)\). Correction turns missing-arrow bias into additional variance.

---

## Two sources of variation

The weighted score has an exact variance decomposition:

\[
\operatorname{Var}_{P_{\theta,q}}(T_q)
=
\operatorname{Var}_{Z}(T_G)
+\frac{4(1-q)}{n^2q}
\sum_{i\in V}
\bigl|\{j\in V:(j,i)\in G\}\bigr|
\,\mathbb E_Z\!\left[Y_i(Z)^2\right],
\]

The first term averages assignment variation. The second sums independent retention variation over true arrows.

- Expanding \(T_G-\tau\) produces individual signs and products of two signs. Distinct products have zero covariance.
- Incoming degree limits terms per outcome; outgoing degree limits repeated appearances of a treatment sign.
- Together with the coefficient bound, this gives \(\operatorname{Var}_{Z}(T_G)\le5(d+1)^2/n\).
- Since incoming degree is at most \(d\) and \(|Y_i(Z)|\le1\), retention adds at most \(4d(1-q)/(nq)\).

Rare retained arrows receive large weights, explaining the collection cost.

---

## Attaining rule

Combine the two variance bounds into an error envelope computable from \(n,d,q\):

\[
u(n,d,q)
=
\begin{cases}
5(d+1)^2/n+4d(1-q)/(nq),&q>0,\\
+\infty,&q=0.
\end{cases}
\]

The attaining estimator uses this envelope to choose its branch:

\[
T^\star_{n,d,q}(O)=T^{\mathrm{up}}(O)=
\begin{cases}
\max\{-1,\min\{1,T_q(O)\}\},&q>0,\ u(n,d,q)<1,\\
0,&\text{otherwise},
\end{cases}
\]

Clipping restricts the score to \([-1,1]\) and cannot increase squared error because the target lies there. Returning zero has squared error at most one.

@informal thm:observable-upper: For admissible \(n,d,q\), under our bounded additive model and independent assignment–retention design, \(T^{\mathrm{up}}\) has worst-case squared error at most \(\min\{1,u(n,d,q)\}\).

Why can no use of outcomes improve this order uniformly?

---

## Supplied-graph benchmark

First isolate uncertainty intrinsic to the experiment.

Let \(R^G_{n,d}(q)\) be optimal worst-case squared error when the true graph \(G\) is supplied alongside \(O\).

CausalSmith (2026), a supplied research note, provides the quadratic degree benchmark under our response restrictions and assignment law:

\[
R^G_{n,d}(q)\asymp \min\left\{1,\frac{d^2}{n}\right\}
\]

This delivers a lower bound of that order. The known-graph score, clipping, and zero fallback give a matching upper bound.

Supplying \(G\) can only make estimation easier, so its lower bound also applies to the sampled-network experiment.

To establish the additional collection cost, we need schedules whose hidden source associations remain difficult to learn from outcomes.

---

## Hard-to-distinguish effects

Construct \(B\) groups, each with \(d\) sources feeding the same \(d\) recipients. There are \(m=Bd\) sources, with \(2m\le n\).

Before the experiment:

- Allocate source labels uniformly among groups.
- Draw independent group baselines \(U_\ell\), with density \(f(w)=4\cos^2(2\pi w)\) on \([-1/4,1/4]\), zero outside.
- Fix the resulting graph and coefficients.

For spillover sign \(\sigma\in\{-1,1\}\) and amplitude \(0\le h\le1/4\), recipients in group \(\ell\) share

\[
y_\ell=U_\ell+\frac{\sigma h}{2d}X_{\ell,\mathrm{sum}}.
\]

Here \(X_{\ell,\mathrm{sum}}\) sums that group’s source-treatment signs. Each arrow has coefficient \(\sigma h/d\); own effects, source outcomes, and padding outcomes are zero.

Equivalently, every recipient \(i\in C_\ell\) has fixed schedule coefficients

\[
a_i=U_\ell-\frac{\sigma h}{2}\quad(i\in C_\ell),
\qquad t_i=0,
\qquad b_{ij}=\frac{\sigma h}{d}
\]

Thus \(U_\ell\) is drawn before the experiment and becomes part of the fixed intercept, rather than measurement noise.

\[
\theta\in\mathcal M_{n,d},
\qquad
\tau(\theta)=\frac{\sigma mh}{n},
\]

The construction gives allowed schedules with opposite total effects.

---

## Complete outcome likelihood

One retained outgoing arrow reveals a source’s recipient group. This happens independently across sources with probability \(p=1-(1-q)^d\).

Given the detailed graph \(H\) and every assignment \(Z\), define:

- \(u_\ell\): remaining source slots in group \(\ell\); \(M=\sum_\ell u_\ell\).
- \(A_\ell\): sum of revealed source signs.
- \(K\): observed number of treated unrevealed sources.

The conditional density of the distinct group outcomes \(y=(y_1,\ldots,y_B)\) is

\[
\lambda_{\sigma,h}(y\mid H,Z)
=
\frac{
[x^K]\displaystyle\prod_{\ell=1}^B
\left\{
\sum_{k=0}^{u_\ell}
\binom{u_\ell}{k}
f\!\left(y_\ell-\frac{\sigma h(A_\ell+2k-u_\ell)}{2d}\right)x^k
\right\}
}{
\binom{M}{K}
},
\]

Here \(k\) counts hidden treated sources in a group; \(x\) is a polynomial indeterminate. Extracting \([x^K]\) enforces the known global count.

Each possible allocation predicts an outcome shift. The density averages these predictions; observed outcomes reweight the allocations. Copying each \(y_\ell\) to its recipients reconstructs every outcome coordinate.

---

## Baseline smoothing

The unknown baselines prevent noiseless responses from identifying the spillover sign immediately.

Let \(g_d(w)\) be one group’s response density averaged over all equally likely source-sign vectors, with \(w\) a possible response.

Expand the fixed-sign response likelihood relative to \(g_d\) in products of treatment signs. Let \(a_s(w)\) be the coefficient for a product of \(s\) signs.

\[
\gamma_s=\int_{\mathbb R}a_s(w)^2g_d(w)\,dw
\quad(1\le s\le d),
\qquad
\eta=\sum_{s=1}^d\binom ds\gamma_s,
\qquad
\eta_1=\sum_{s=1}^d s\binom ds\gamma_s.
\]

The quantities \(\eta,\eta_1\) measure squared likelihood dependence on signs, with \(\eta_1\) additionally weighting product size.

\[
0\le\eta\le\eta_1\le\frac{12\pi^2h^2}{d}.
\]

Flipping one sign shifts the response by \(h/d\). Smoothness of \(\sqrt f\) bounds the squared likelihood change from that flip; summing over \(d\) coordinates produces the \(h^2/d\) bound.

This controls products of every size, including outcome information beyond the mean.

---

## Hidden allocation averaging

Condition on \(H\). Compare the actual positive-sign law of \((Z,y)\) with a reference \(Q_H\) that keeps the actual assignments and gives groups independent response densities \(g_d\).

Let \(L_+\) be their likelihood ratio and \(\chi_H^2=\mathbb E_{Q_H}[(L_+-1)^2]\), their squared likelihood discrepancy.

When \(4e\eta<1\), with \(e=\exp(1)\),

\[
\mathbb E_H\!\left[\mathbf1\{M\ge m/4\}\chi_H^2\right]
\le
\frac{\exp(eBp\eta_1)}{1-4e\eta}-1.
\]

The average uses the actual detailed retained-graph law.

- Averaging allocations spreads a product of \(k\) hidden signs over \(\binom Mk\) labeled subsets; orthogonality reduces its squared contribution by \(1/\binom Mk\).
- These symmetric products remain functions of the observed count \(K\).
- Hidden dependence contributes through \(1-4e\eta\); revealed associations accumulate through \(Bp\eta_1\).

The comparison retains every assignment and the full outcome likelihood. It therefore includes learning from outcomes and the global count.

---

## Testing scale

Since \(m=Bd\), smoothing gives \(Bp\eta_1\le12\pi^2h^2mp/d^2\).

The accumulating information is therefore controlled by \(h^2mp/d^2\), while the cap on \(h\) keeps \(\eta\) small. Choose

\[
h_\circ(B,d,q)=\frac{1}{100\pi}
\begin{cases}
\min\left\{1,\dfrac{d}{\sqrt{mp}}\right\},&p>0,\\
1,&p=0,
\end{cases}
\]

This is the amplitude that keeps both parts of the likelihood bound small.

At low revelation, \(p<1/2\), with \(m\ge32\):

- The event \(M<m/4\) has probability at most \(1/16\).
- At \(h_\circ\), the average squared likelihood discrepancy on its complement is at most \(1/16\).
- Symmetry of \(f\) and Cauchy–Schwarz bound the complete-record total variation by \(1/16+1/4\le1/2\).

At higher revelation or smaller \(m\), a translation comparison gives the same conclusion even if the source partition is supplied.

Thus \(\operatorname{TV}(P_{+1,h_\circ},P_{-1,h_\circ})\le1/2\), where these are the opposite-sign complete-record laws and total variation is the largest probability difference over observed events.

---

## Matching lower bound

An accurate effect estimate would distinguish positive from negative effects.

For two distributions over allowed schedules with constant targets \(+\Delta\) and \(-\Delta\),

\[
R_{n,d}(q)\ge
\frac{\Delta^2}{2}
\left(1-\operatorname{TV}(\mathsf Q_+,\mathsf Q_-)\right),
\]

Here \(\mathsf Q_+,\mathsf Q_-\) are their complete-record laws, and \(\Delta\) is the target magnitude.

- In our construction, \(\Delta=mh_\circ/n\).
- When \(d^2/n<1/16\), choose enough groups that \(n/4\le m\le n/2\).
- The testing bound gives risk at least \(\Delta^2/4\); because \(m\) is comparable to \(n\), this matches \(F(n,d,q)\) up to constants.
- When \(d^2/n\ge1/16\), the supplied-graph benchmark already gives a constant lower bound, sufficient because \(F\le1\).

The converse covers every use of sampled arrows, assignments, and noiseless outcomes.

---

## Collection and consistency

Retention of order \(1/d\) or greater matches the supplied-graph precision order. Below that transition, \(d/(nq)\) determines the uncapped risk.

Uniform consistency means squared error vanishes uniformly over all allowed schedules.

@informal thm:observed-record-precision-frontier: For admissible sequences \(d_n,q_n\), under our bounded additive model and independent assignment–retention design, uniform consistency is possible exactly when \(d_n^2/n\to0\) and \(d_n/(nq_n)\to0\), assigning the second ratio \(+\infty\) at zero retention.

\[
\frac{d_n^2}{n}\longrightarrow0
\qquad\text{and}\qquad
\begin{cases}
+\infty,&q_n=0,\\[2pt]
\dfrac{d_n}{nq_n},&q_n>0
\end{cases}
\longrightarrow0.
\]

Here \(d_n,q_n\) are degree bounds and retention probabilities as population size grows.

Degree must grow more slowly than \(\sqrt n\), and collection must outpace \(d_n/n\). For our \(d=1\) example, consistency requires \(nq_n\to\infty\): retention can vanish while precision improves.

---

## Open questions

- Estimated or heterogeneous retention, false-positive arrows, and dependent collection from interaction events.
- Alternative assignments, repeated experiments, and responses with treatment interactions.
- Exact minimax constants, confidence intervals, and recovery of individual arrows.

Platform applications require a justified mapping from recorded events to independently retained interference arrows.

---

## Takeaways

- Independent treatment signs extract additive effects; weighting sampled arrows by \(1/q\) restores their contributions on average.
- Under our bounded model and independent design, optimal squared risk combines \(d^2/n\) and \(d/(nq)\), capped at constant order.
- Smooth unknown baselines and hidden source allocations limit complete-record information at scale \(h^2mp/d^2\), yielding the matching lower bound even when outcomes help reveal connections.

---

## Appendix: Observed-record precision frontier

This statement gives the attainable minimax scale, its endpoint comparisons, and the necessary and sufficient conditions for uniform consistency.

@formal thm:observed-record-precision-frontier

---

## Appendix: Observable upper risk bound

This statement bounds the worst-case squared error of the clipped-or-zero inverse-inclusion rule.

@formal thm:observable-upper
