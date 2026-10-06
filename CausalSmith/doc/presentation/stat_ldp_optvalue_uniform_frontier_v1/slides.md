# Estimating Optimal Treatment Welfare Under Local Privacy

A confidential randomized trial can measure the population gain from choosing the better treatment in each stratum, even when treatments tie.

---

## Research question

A trial has \(n\) participants in \(d\) strata. Under population law \(P\), let \(\mu_{aj}(P)\) be the mean outcome under arm \(a\) in stratum \(j\).

With equal population weights, choosing the better arm gives first-best welfare:

\[
V(P)=\frac1d\sum_{j=1}^d\max\{\mu_{0j}(P),\mu_{1j}(P)\},
\qquad
B(P)=\mathbb E_P[Y].
\]

Here \(V(P)\) is the optimal population mean outcome; \(B(P)\) is the observed-outcome mean under fair assignment, and \(Y\) is the recorded outcome.

Luedtke and van der Laan (2016) develop optimal-value inference under conditions accommodating possibly nonunique optimal strategies.

How accurately can a locally private trial report this optimum uniformly over treatment-effect patterns?

---

## Standard approach

Estimate both arm means, choose the larger estimate in each stratum, and average.

Write the treatment contrast as \(\tau_j(P)=\mu_{1j}(P)-\mu_{0j}(P)\).

- A large positive or negative contrast makes the preferred arm stable.
- At a tie, choosing the larger noisy estimate creates an apparent treatment gain.
- A linear expansion around a fixed winning arm misses the change of slope at zero.

Ohnishi and Awan (2025) obtain inverse-resource squared-error order for a locally private ATE, a signed mean contrast.

Welfare depends on contrast **magnitudes**. How can we avoid counting noise as treatment benefit?

---

## Key idea

Let \(F(\tau(P))=d^{-1}\sum_j|\tau_j(P)|\) be the average absolute contrast.

\[
V(P)=B(P)+\frac12F(\tau(P)).
\]

Welfare is the fair-assignment baseline plus half the average contrast magnitude.

Approximate absolute value by a polynomial, then estimate its powers without noise bias.

A fixed noninteractive collection rule supplies the required moments. Resource-dependent analysis uses a polynomial across the whole contrast range, or only near ties.

This yields uniform welfare estimates and honest connected intervals, including at exact ties.

---

## Example

Consider the symmetric trial family \(G_\theta\), where \(\theta_j\in[-1/2,1/2]\) is stratum \(j\)'s contrast.

Control and treatment means are \((1-\theta_j)/2\) and \((1+\theta_j)/2\). Strata have equal weights and assignment is fair.

\[
V(G_\theta)=\frac12+\frac{F(\theta)}2.
\]

The baseline is \(1/2\); all welfare variation comes from

\[
F(\theta)=\frac1d\sum_{j=1}^d|\theta_j|.
\]

Reversing a contrast changes the preferred arm but preserves welfare. Zero creates the kink.

With two strata, welfare is \(1/2+(|\theta_1|+|\theta_2|)/4\). This same family also permits growing \(d\), where polynomial estimation provides the logarithmic improvement.

---

## Model and assumptions

Each participant has stratum \(X\), binary assignment \(A\), binary outcome \(Y\), and binary potential outcomes \(Y^0,Y^1\).

\[
\mu_{aj}(P)=\mathbb E_P[Y^a\mid X=j],
\qquad
\tau_j(P)=\mu_{1j}(P)-\mu_{0j}(P),
\qquad
\tau(P)=(\tau_1(P),\ldots,\tau_d(P)).
\]

These are the arm means, their differences, and the contrast vector.

- **Uniform strata:** public probabilities \(1/d\) fix equal welfare weights.
- **Fair assignment:** treatment is a fair coin conditional on stratum and both potential outcomes.
- **Consistency:** the recorded outcome equals the potential outcome under the assigned arm.
- **Interior means:** arm means lie in \([1/4,3/4]\), bounding contrasts by \(1/2\).
- **Independent sampling:** participant records are independent draws from one population.

Call the causal class \(\mathcal V_d\). In \(G_\theta\), \(|\theta_j|\le1/2\) guarantees interior means; exact ties remain admissible.

---

## Private collection

Participant \(i\) sends one message using rule \(Q_i\), with complete observed record \(o=(X,A,Y)\) as input.

Pure local differential privacy requires

\[
Q_i(E\mid o,\eta,r)\le e^\varepsilon Q_i(E\mid o',\eta,r).
\]

Changing any part of the record changes a message event's probability by at most \(e^\varepsilon\). Here \(E\) is an event, \(o'\) another record, \(\eta\) the preceding-message history, and \(r\) the public seed.

- **Noninteractive collection (NI):** message rules are fixed independently of earlier messages.
- **Sequentially interactive collection (SI):** later rules may depend on earlier messages; each participant is accessed once.
- Public randomness \(R\) and analyst randomness \(U\) are mutually independent and independent of participant records.

Our resource domain is \(n,d\ge2\) and \(0<\varepsilon\le1\).

---

## Main result

Set \(t=n\varepsilon^2\), the effective private resource, and \(L=\log(ed)\), the logarithmic dimension factor.

\[
\rho(t,d)=
\begin{cases}
\displaystyle\frac{d^2}{tL},&t\ge d^2L,\\[3pt]
\displaystyle\min\left\{1,
\left[\frac{\log(e+d^2L/t)}{L}\right]^2\right\},
&0<t<d^2L.
\end{cases}
\]

This is the optimal worst-population squared-error scale, optimizing collection and estimation.

@informal thm:uniform-private-value-frontiers: Under our trial and collection assumptions, \(n,d\ge2\), \(0<\varepsilon\le1\), and the Bernstein limit, NI and SI minimax squared error has order \(\rho(t,d)\), and minimax globally \(0.90\)-honest connected length has order \(\sqrt{\rho(t,d)}\).

“Order” means comparison within universal constant factors. Honest length means minimum worst-population expected length among connected intervals covering every \(P\in\mathcal V_d\) with probability at least \(0.90\).

The result is conditional on the cited, unformalized Bernstein absolute-approximation limit: the best uniform degree-\(K\) polynomial approximation error for \(|x|\) is of order \(1/K\) (Cai--Low 2011, §3.1; Bernstein 1913).

One explicit noninteractive procedure attains both orders. In \(G_\theta\), it covers \(1/2+F(\theta)/2\) uniformly, including zero contrasts.

---

## Private contrast messages

Locally compute \(S=(2A-1)(2Y-1)\). Fair assignment and consistency give \(\mathbb E_P[S\mid X=j]=\tau_j(P)\).

Release a vector \(z\) of \(d\) signs:

\[
Q^{\mathrm{vec}}(z\mid O=(j,A,Y))
=
2^{-d}\bigl(1+\delta(2A-1)(2Y-1)z_j\bigr),
\qquad z\in\{-1,1\}^d,
\]

Here \(O\) is the record and \(\delta=\tanh(\varepsilon/2)\) is privacy attenuation.

Only the participant's stratum coordinate is tilted, with mean \(\delta S\); the others are independent fair signs.

The largest likelihood ratio across records is \((1+\delta)/(1-\delta)=e^\varepsilon\).

Scale coordinate \(j\) of participant \(i\)'s release as \(W_{ij}=bZ_{ij}\), where \(b=d/\delta\):

\[
\mathbb E[W_{ij}]=\tau_j(P),
\qquad
\mathbb E[W_{ij}^{2}]=b^{2}.
\]

Scaling recovers the contrast mean but creates large coordinate noise.

---

## The plug-in limitation

For an evaluation block of \(m\) participants, let \(\overline W_j\) be coordinate \(j\)'s average scaled message.

The natural magnitude estimate is

\[
\widehat F=\frac1d\sum_{j=1}^d|\overline W_j|.
\]

It averages absolute estimated contrasts.

Define the coordinate-mean noise scale \(\sigma^2=b^2/m\), with \(\sigma\) its positive square root. The plug-in squared-error bound is \(\mathbb E_P(\widehat F-F(\tau(P)))^2\le\sigma^2\).

At a tie, positive noise magnitudes survive averaging across strata. Variance reduction alone does not remove this bias.

For large resources and growing dimension, the optimal squared-error scale improves on the coordinate-noise scale by the factor \(L\).

---

## Unbiased contrast powers

Use products from different participants:

\[
\mathsf U_{kj}
=
\binom{m}{k}^{-1}
\sum_{\substack{J\subseteq\{1,\ldots,m\}\\ |J|=k}}
\prod_{i\in J}W_{ij}
\quad(1\le k\le m),
\qquad
\mathsf U_{0j}=1.
\]

Here \(k\) is the power and \(J\) selects \(k\) distinct participants. The statistic averages their coordinate products.

Independence makes expectations multiply:

\[
\mathbb E[\mathsf U_{kj}]=\tau_j(P)^k.
\]

Powers of a noisy sample mean contain noise terms. Distinct-person products remove them.

In \(G_\theta\), these statistics estimate \(\theta_j^k\), including at zero.

---

## Polynomial estimation

Cai and Low (2011) supply the strategy: approximate absolute value and estimate the polynomial's powers without bias.

Let \(q_D(x)=\sum_{v=0}^D a_{Dv}x^v\) be their explicit approximation, with even degree \(D\) and coefficients \(a_{Dv}\).

For radius \(a>0\),

\[
 p_{a,D}(x)=a q_D(x/a),\qquad
 \widehat p_{a,D,j}
 =\sum_{v=0}^D a_{Dv}a^{1-v}\mathsf U_{vj}.
\]

The first expression approximates absolute value on \([-a,a]\); the second replaces powers with unbiased private moments.

Thus \(\mathbb E\widehat p_{a,D,j}=p_{a,D}(\tau_j(P))\): the remaining bias is approximation error.

At \(a=1/2\), absolute bias is at most \(1/(D+1)\) throughout the contrast range.

In \(G_\theta\), the expectation is \(p_{a,D}(\theta_j)\). At a tie, it is a controlled approximation value, rather than the magnitude of a noisy mean.

---

## Averaging across strata

Each participant supplies every coordinate. Why does averaging still reduce polynomial noise?

Sign symmetry gives \(\mathbb E[W_{ij}W_{ij'}]=0\) for different strata \(j,j'\). Their centered correlation is

\[
\gamma_{jj'}
=
-\frac{\tau_j(P)\tau_{j'}(P)}
{\sqrt{(b^2-\tau_j(P)^2)(b^2-\tau_{j'}(P)^2)}}.
\]

Bounded contrasts and large private-message variance imply \(|\gamma_{jj'}|\le1/d\).

Expand a column statistic into products of centered participant signs. Different participant subsets have zero cross terms; a shared subset \(J\) contributes \(\gamma_{jj'}^{|J|}\). Nonlinear statistics therefore retain small cross-column dependence.

For any deterministic column statistics \(T_j^{\mathrm{col}}\),

\[
\operatorname{Var}\left(\frac1d\sum_{j=1}^{d}T_j^{\mathrm{col}}\right)
\le
\frac2d\max_{j\in[d]}\operatorname{Var}(T_j^{\mathrm{col}}).
\]

This bounds the variance of their average, providing the dimension reduction that makes high-degree moments usable.

---

## Lower-resource estimation

When \(t<d^2L\), approximate over the full contrast range with radius \(a=1/2\).

Define \(H=\log(e+\sigma^2L)\), the factor governing moment-variance growth. For the average polynomial estimate,

\[
\mathbb E_P(\widehat F-F(\tau(P)))^2
\le\frac{e^{9DH}}{2d}+\frac1{(D+1)^2}.
\]

The first term bounds aggregate moment variance; the second bounds squared approximation bias.

Choose an even \(D\) proportional to \(L/H\), with a small fixed multiplier, whenever the dimension and moment budget permit.

- Then \(DH\) is a small fraction of \(L\): the denominator \(d\) absorbs exponential moment growth.
- Inverse-degree bias gives squared error at most constant order \((H/L)^2\).
- The noise bound makes \(H\) at most a constant times \(\log(e+d^2L/t)\), producing the lower-resource branch of \(\rho\).

If no useful degree fits, the target rate is bounded below by a fixed positive constant; bounded welfare error suffices.

---

## Localization near ties

When \(t\ge d^2L\) and dimension permits polynomial estimation, shrink the approximation window.

Split participants into independent pilot and evaluation blocks: the pilot selects the branch and the evaluation block estimates its value.

Let \(M_j\) be the pilot mean. Choose threshold \(T_*\) proportional to \(\sigma\sqrt L\), radius \(a=2T_*\), and even degree \(D\) proportional to \(L\), with a small fixed multiplier.

\[
 H_j=\widehat p_{a,D,j}\mathbf1_{\{|M_j|\le T_*\}}
       +\operatorname{sign}(M_j)\overline W_j
          \mathbf1_{\{|M_j|>T_*\}}.
\]

The indicators select a polynomial near zero and a signed evaluation mean elsewhere.

With a reliable sign, absolute value is linear. Concentration makes wrong-sign choices and use of the polynomial far outside its window rare.

Approximation bias is at most constant order \(a/D\), hence \(\sigma/\sqrt L\). Averaging controls moment variance at the same squared scale.

The resulting squared-error bound has order at most \(\sigma^2/L\), delivering \(d^2/(tL)\). In \(G_\theta\), zero contrasts receive the polynomial treatment.

---

## Welfare estimation

A disjoint baseline block uses binary randomized response: each participant releases a noisy sign of the observed outcome.

For \(m_0\) baseline participants with released signs \(\mathsf H_i\),

\[
\widehat B
=\frac12+\frac1{2\delta m_0}
\sum_{i=1}^{m_0}\mathsf H_i.
\]

This estimates \(B(P)\) without bias, with squared error at most \(12/t\).

Combine it with the resource-selected magnitude estimate:

\[
\widetilde V=\widehat B+\frac12\widehat F,
\qquad
\widehat V=\max\{1/4,\min\{3/4,\widetilde V\}\}.
\]

The first expression adds the estimated treatment-selection gain. Clipping to the known welfare range cannot increase error.

For bounded logarithmic dimension, use the plug-in branch; its loss relative to the optimal order is bounded. Constant-output branches handle insufficient resources.

All collection rules are predetermined. Pilot selection happens during analysis, so collection remains noninteractive.

---

## Honest intervals

The uniform squared-error guarantee also supplies a confidence interval.

Take \(q_*\), the interval radius, to be the construction's fixed sufficiently large multiple of \(\sqrt{\rho(t,d)}\).

Report endpoints \(\max\{1/4,\widehat V-q_*\}\) and \(\min\{3/4,\widehat V+q_*\}\).

A coverage failure requires \(|\widehat V-V(P)|>q_*\). Markov's inequality applied to squared error bounds this probability by \(0.10\), uniformly over \(P\in\mathcal V_d\).

Length is at most \(2q_*\), hence at most constant order \(\sqrt{\rho(t,d)}\).

In \(G_\theta\), the interval covers \(1/2+F(\theta)/2\) even when any or all treatments tie.

What prevents another private collection rule from doing better?

---

## Matched welfare alternatives

Cai and Low (2011) supply the approximation-and-moment-matching strategy for the converse.

Define the best degree-\(K\) absolute-value approximation error:

\[
e_K=\inf_{\deg p\le K}\sup_{|x|\le1}\bigl|p(x)-|x|\bigr|.
\]

Here \(p\) ranges over polynomials. The Bernstein premise is \(2k e_{2k}\to\beta_*\), with \(\beta_*>0\); it gives an inverse-degree lower bound for every positive even \(K\).

Choose contrast distributions \(\nu_0,\nu_1\) supported on \([-\alpha,\alpha]\), with \(0<\alpha\le1/2\), satisfying

\[
\int u^v\,\nu_0(du)=\int u^v\,\nu_1(du)
\quad(0\le v\le K),
\qquad
\int |u|\,\nu_1(du)-\int |u|\,\nu_0(du)
=2\alpha e_K.
\]

The distributions agree on low-order powers of contrast \(u\), but disagree on its magnitude.

Draw \(d\) independent contrasts from either distribution and embed them in \(G_\theta\). Welfare centers \(v_0,v_1\) are separated by \(\Delta=v_1-v_0=\alpha e_K\).

---

## Sequential contraction

For any sequential protocol \(Q\), let \(\mathsf M_0^Q,\mathsf M_1^Q\) be its public-seed and message distributions under the two priors.

Write \(k=K+1\) and \(\beta=(e^\varepsilon-1)/(2d)\), the privacy contraction scale.

\[
\operatorname{TV}(\mathsf M_0^Q,\mathsf M_1^Q)
\le
\min\left\{1,\,
d\alpha^k\sqrt{\binom nk}\,\beta^k\right\},
\qquad 1\le k\le n,
\]

Total variation measures transcript distinguishability. Moment matching cancels degrees below \(k\); privacy contracts the remaining sensitivity.

Each new message's likelihood sensitivity has conditional mean zero and magnitude at most \(\beta\), even after earlier messages. This centering prevents adaptation from accumulating cross terms and yields the square-root combinatorial factor.

For tuning, define \(\gamma_{\mathrm{con}}=\alpha\sqrt{et}/(d\sqrt{k})\). A binomial bound gives

\[
\operatorname{TV}(\mathsf M_0^Q,\mathsf M_1^Q)
\le d\alpha^k\sqrt{\binom nk}\,\beta^k
\le d\gamma_{\mathrm{con}}^k.
\]

If \(k>n\), matched moments make the transcripts exactly identical.

---

## High-resource converse

Suppose \(t\ge d^2L\). Define \(z_*=d^2L/t\le1\).

| Quantity | Resource choice and consequence |
|---|---|
| Amplitude \(\alpha\) | A small fixed multiple of \(\sqrt{z_*}\) |
| Matching degree \(K\) | Proportional to \(L\), with \(k=K+1\) |
| Welfare separation \(\Delta=\alpha e_K\) | At least constant order \(\sqrt{z_*}/L\) |
| Transcript factor \(\gamma_{\mathrm{con}}\) | Bounded by a small constant |

Substitution into \(\gamma_{\mathrm{con}}^2=\alpha^2eL/(kz_*)\) cancels the resource ratio: the small amplitude multiplier controls the remaining constant.

Because \(k\) is proportional to \(L\), taking its power overwhelms the factor \(d\). The chosen constants make transcript total variation at most \(1/100\).

Meanwhile \(\sqrt{\rho(t,d)}=\sqrt{z_*}/L\). Thus concealment preserves the welfare separation required for the high-resource lower bound.

---

## Lower-resource converse

Suppose \(t<d^2L\). Now \(z_*=d^2L/t>1\) and \(w=\log(e+z_*)\).

| Quantity | Resource choice and consequence |
|---|---|
| Amplitude \(\alpha\) | A small fixed constant |
| Matching degree \(K\) | Proportional to \(\max\{1,L/w\}\) |
| Welfare separation \(\Delta=\alpha e_K\) | At least constant order \(\min\{1,w/L\}\) |

Lower resource means less moment matching is needed to conceal a fixed-amplitude alternative.

Substitution into \(\gamma_{\mathrm{con}}^2=\alpha^2eL/(kz_*)\) gives the calibrated bound \(\gamma_{\mathrm{con}}\le e^{-w/4}\). The degree choice ensures \(kw\ge32L\), so \(d\gamma_{\mathrm{con}}^k\) is at most \(1/100\).

The preserved separation is at least constant order \(\sqrt{\rho(t,d)}=\min\{1,w/L\}\).

When \(w\ge L\), the matching degree stays bounded and the welfare gap has constant order: this is saturation.

---

## Precision lower bounds

Independent prior coordinates give welfare variance at most \(\alpha^2/(4d)\). Since the gap is at least constant order \(\alpha/K\), welfare concentrates around each center when \(K^2/d\) is small.

Our choices keep \(K\) at most a constant times \(L\), so this holds for sufficiently large dimension.

An estimate accurate relative to \(\Delta\) would distinguish the alternatives. Close transcripts therefore force squared error at least constant order \(\Delta^2\).

For connected intervals, let \(\eta_0\) bound escape from each center's \(\Delta/8\) neighborhood, and \(\omega\) bound transcript total variation.

\[
\sup_{P\in\mathcal V_d}
\mathbb E_{P,Q}\operatorname{length}I(\mathbf Z,R,U)
\ge
\frac{3\Delta}{4}(0.80-2\eta_0-\omega)_+.
\]

Here \(I\) is the reported interval, \(\mathbf Z\) the messages, and \(x_+=\max\{x,0\}\).

Coverage and transcript proximity force intersection with both neighborhoods with positive probability. Connectedness makes the interval span their gap.

A two-population argument supplies the bounded-dimension cases. Together, these establish both lower bounds for every sequential protocol.

---

## Open questions

- Unknown stratum probabilities or treatment propensities: how does estimating the design change private welfare precision?
- Sharper constants and less communication: the explicit construction uses conservative calibration and \(d\)-coordinate messages.
- Repeated participant records, learned-policy regret, and finite-population inference require additional sampling or decision frameworks.

---

## Takeaways

- Optimal welfare is the fair-assignment baseline plus half the average contrast magnitude; treatment ties create the kink.
- Distinct-person products remove moment noise bias. Polynomial approximation handles ties, and weak coordinate dependence makes averaging effective.
- Conditional on the cited, unformalized Bernstein absolute-approximation limit (Cai--Low 2011, §3.1; Bernstein 1913), noninteractive collection attains optimal squared-error and globally honest connected-length orders. Resource-matched welfare alternatives establish the same limits under sequential adaptation.

---

## Appendix: Uniform private welfare frontiers

This statement gives matching welfare estimation and honest-length bounds, simultaneous attainment, and resource and interaction comparisons.

It is conditional on the cited, unformalized Bernstein absolute-approximation limit for the best uniform polynomial approximation of \(|x|\) (Cai--Low 2011, §3.1; Bernstein 1913).

@formal thm:uniform-private-value-frontiers

---

## Appendix: Paired-uniform total-variation frontier

This statement gives matching estimation and honest-length bounds for distance from the uniform law on symbols \((j,s)\), where \(j\) indexes a stratum and \(s\) is a sign; the distance equals half the average contrast magnitude.

It is conditional on the cited, unformalized Bernstein absolute-approximation limit for the best uniform polynomial approximation of \(|x|\) (Cai--Low 2011, §3.1; Bernstein 1913).

@formal thm:paired-uniform-tv-frontier

---

## Appendix: Full-simplex total-variation lower bounds

This statement transfers the paired-family lower bounds to all probability laws on the same \(2d\) symbols; matching upper bounds on this larger model remain open.

It is conditional on the cited, unformalized Bernstein absolute-approximation limit for the best uniform polynomial approximation of \(|x|\) (Cai--Low 2011, §3.1; Bernstein 1913).

@formal thm:full-simplex-tv-converse
