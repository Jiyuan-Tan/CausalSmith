# Learning Treatment Rules With Weak Overlap

When treatment choices are nearly tied, the informative treatment can also be rare—and that changes how quickly we can learn a good rule.

---

## Motivation

A practitioner wants to choose whom to treat using previously collected observations.

- Kitagawa and Tetenov (2018): choose the rule with the highest estimated welfare.
- Athey and Wager (2021): estimate observational welfare using augmented inverse-propensity-weighted (AIPW) scores.
- Luedtke and Chambaz (2017): under strict overlap, fewer near-ties can deliver faster regret rates.

Near-ties can occur precisely where one treatment arm is rarely observed. Inverse-propensity weights then become large, and the bounded-score argument behind strict-overlap rates breaks down.

How does this coincidence change the achievable welfare loss?

---

## Key idea

Count information where the treatment decision is uncertain.

Three quantities determine the difficulty:

- The size of the treatment contrast.
- The population share with a small contrast.
- The chance of observing the arm that reveals which treatment is better.

A restriction on their joint behavior gives a minimax regret lower bound.

For learning, clip inverse weights and control the resulting bias on the region where rare arms and uncertain decisions coincide.

Under explicit nuisance-estimation and sampling-fluctuation conditions, this rule matches the lower-bound polynomial exponent when those additional costs do not bind.

---

## Example

Let the covariate \(X\) be uniform on \([0,1]\). Put the uncertain decision on a small block:

\[
B_n=\{x\in\mathbb R:0\le x\le c_Bh_n^\alpha\}.
\]

Here \(n\) is sample size, \(h_n\) is the contrast size, \(\alpha\ge0\) governs block mass, and \(c_B>0\) controls its scale.

On the block, treatment occurs with probability \(q_n\); untreated outcomes equal zero. Treated outcomes are \(+1\) or \(-1\):

\[
P(Y=1\mid X\in B_n,A=1)=\frac{1+\sigma h_n}{2},
\qquad
P(Y=-1\mid X\in B_n,A=1)=\frac{1-\sigma h_n}{2}.
\]

The sign \(\sigma\in\{1,-1\}\) selects two worlds with contrasts \(+h_n\) and \(-h_n\). They require opposite decisions on the block.

Outside the block, both worlds agree and treatment is better. Only treated observations inside the block reveal the sign.

---

## Model and target

We observe independent draws \(O=(X,A,Y)\) from an observed law \(P\), with outcome \(Y\in[-1,1]\) and treatment indicator \(A\in\{0,1\}\).

The propensity is \(e_P(x)=P(A=1\mid X=x)\). The arm means are \(\mu_a(x)=E_P[Y\mid A=a,X=x]\), and their contrast is \(\tau_P(x)=\mu_1(x)-\mu_0(x)\).

For a binary treatment rule \(\pi\), normalized welfare is

\[
V_P(\pi)=\mathbb E_P\!\left[\pi(X)\tau_P(X)\right].
\]

This averages the contrast for people the rule treats. The oracle \(\pi^\star_P(x)=\mathbf 1\{\tau_P(x)\ge0\}\) treats whenever the contrast is nonnegative.

Its welfare advantage over \(\pi\) is regret:

\[
R_P(\pi)
=
E_P\!\left[
|\tau_P(X)|\,\mathbf 1\{\pi(X)\ne\pi^\star_P(X)\}
\right]
=
\int_{\mathcal X}
|\tau_P(x)|\,\mathbf 1\{\pi(x)\ne\pi^\star_P(x)\}\,dP_X(x).
\]

Here \(P_X\) is the covariate distribution. A wrong assignment costs the absolute contrast at that covariate.

---

## Assumptions

**Margin:** the permitted exponent is any \(\alpha\ge0\). For \(0<u\le u_0\), with \(0<u_0<2\),

\[
P\{0<|\tau_P(X)|\le u\}\le C_m u^\alpha .
\]

The threshold \(u\) selects near-ties; \(C_m>0\) controls their prevalence. In the example, contrast \(h_n\) occurs on a block of mass proportional to \(h_n^\alpha\).

**Joint overlap decay:** let \(p_P(x)=\min\{e_P(x),1-e_P(x)\}\), the probability of the rarer arm. For \(\gamma>0\) and \(0<v\le c_o u^\gamma\),

\[
P\{p_P(X)\le v,\ 0<|\tau_P(X)|\le u\}
   \le C_o u^\alpha v^{1/\gamma},
\]

Here \(v\) selects weak overlap; positive constants \(C_o,c_o\) control the bound and its window. The restriction limits how much arm rarity can coincide with near-ties.

Both arms have positive probability. At zero contrast, either there is no population mass or all candidate rules agree with the oracle.

For the endpoint \(\gamma=0\), assume strict overlap: \(p_P(X)\ge\underline p>0\).

---

## Minimax lower bound

Let \(\mathcal P_{\alpha,\gamma}\) collect laws satisfying these restrictions, and let \(\Pi\) be a nonempty class of measurable treatment rules.

The calibrated exponents are

\[
\beta_{\alpha,\gamma}
=
\begin{cases}
0, & \gamma=0,\\
\dfrac{\alpha\gamma}{\alpha+1}, & \gamma>0,
\end{cases}
\qquad
D_{\alpha,\gamma}=2+\alpha+\beta_{\alpha,\gamma},
\qquad
r_\star(\alpha,\gamma)=\frac{1+\alpha}{D_{\alpha,\gamma}}.
\]

Here \(\beta_{\alpha,\gamma}\) governs informative-arm rarity; \(D_{\alpha,\gamma}\) combines contrast, block mass, and rarity.

The additional requirements are fixed-constant calibrations: take \(\underline p\le1/4\) and choose \(c_B>0\) small enough to satisfy the margin, overlap, and testing bounds. They add no distributional shape restriction. The normalization \(0<u_0<2\) lets the example’s off-block contrast exceed the margin window while respecting bounded outcomes.

@informal thm:minimax-lower: Under the law restrictions, \(0<u_0<2\), \(\underline p\le1/4\), and the small-block constant calibrations, every measurable estimator valued in nonempty \(\Pi\) has worst-case expected regret at least \(c\,n^{-r_\star(\alpha,\gamma)}\) for large \(n\).

\[
M_n(\alpha,\gamma)
=
\inf_{\widehat\pi}
\sup_{P\in\mathcal P_{\alpha,\gamma}}
\mathbb E_P R_P(\widehat\pi)
\ge
c\,n^{-r_\star(\alpha,\gamma)}.
\]

The infimum chooses the best data-dependent rule; the supremum chooses the hardest admissible law. The constant \(c>0\) does not depend on sample size.

---

## Conditional upper bound

For the clipped AIPW welfare maximizer, assume:

- The oracle belongs to \(\Pi\), which has finite Vapnik–Chervonenkis (VC) dimension—a bound on how flexibly rules can label covariates.
- Outcome and propensity estimates are trained outside each evaluation fold, with a fixed number of balanced folds; outcome estimates lie in \([-1,1]\).
- Two uniform fluctuation bounds hold: one over low-regret policies, and one after subtracting a fraction of regret. These are additional assumptions beyond finite VC dimension.

Let \(r_{\mu,n}\) and \(r_{e,n}\) bound root-mean-square outcome-regression and propensity errors. For exponents \(a\ge0\) and \(c\ge1/2\), assume

\[
r_{\mu,n}\le C_\mu n^{-a},
\qquad
r_{\mu,n}r_{e,n}\le C_{\mathrm{prod}}n^{-c}.
\]

The constants \(C_\mu,C_{\mathrm{prod}}\) are fixed and nonnegative.

@informal oeq:feasible-upper: With oracle inclusion, finite VC dimension, bounded cross-fitted nuisances at the supplied rates, fixed balanced folds, both uniform localized fluctuation bounds, and admissible tuning, worst-case expected regret is at most \(C n^{-r_{\mathrm{up}}}(\log n)^p\).

\[
U_n(\alpha,\gamma,a,c;\widehat\eta)\le C n^{-r_{\mathrm{up}}}(\log n)^p,
\]

Here \(U_n\) takes the worst case over laws satisfying these extra conditions for the supplied estimates \(\widehat\eta\); \(p\ge0\) allows logarithmic factors.

For \(\gamma>0\),

\[
r_{\mathrm{up}}
=
r_{\mathrm{feas}}
=
\min\left\{r_\star(\alpha,\gamma),\,g_{\mathrm{joint}}(\alpha,\gamma,a,c)\right\}.
\]

The quantity \(g_{\mathrm{joint}}\) is the best exponent from balancing sampling noise and nuisance bias.

---

## Calibrating arm rarity

Return to the example: contrast size \(h\in(0,1)\), block mass proportional to \(h^\alpha\).

Try an informative-arm probability \(h^\beta\), with \(\beta\ge0\). Checking overlap only at contrast threshold \(u=h\) misses larger windows that also contain the block.

For the exponent calculation, the tight window is

\[
v=h^\beta,
\qquad
u=h^{\beta/\gamma}.
\]

Here \(v\) is the arm-probability threshold and \(u\) the corresponding contrast threshold.

The joint probability allowance accommodates the block mass exactly when

\[
u^\alpha v^{1/\gamma}\ge h^\alpha
\quad\Longleftrightarrow\quad
\beta\le \beta_{\alpha,\gamma}=\frac{\alpha\gamma}{\alpha+1},
\]

Thus \(\beta_{\alpha,\gamma}\) is the largest arm-rarity exponent within this calibration.

The joint restriction limits information loss across contrast windows, rather than only at the block’s own contrast.

---

## Statistical indistinguishability

The example’s two laws differ only in treated observations on \(B_n\).

- Block mass contributes \(h_n^\alpha\).
- Informative-arm probability contributes \(h_n^{\beta_{\alpha,\gamma}}\) when \(\beta_{\alpha,\gamma}>0\); otherwise it is fixed at \(1/4\).
- Distinguishing the conditional means contributes \(h_n^2\).

For the two laws \(P_{n,+}\) and \(P_{n,-}\),

\[
\chi^2(P_{n,+}\,\|\,P_{n,-})
 \le C\,h_n^{2+\alpha+\beta_{\alpha,\gamma}},
\qquad
h_n=n^{-1/(2+\alpha+\beta_{\alpha,\gamma})}.
\]

The chi-square divergence \(\chi^2\) measures statistical distinguishability. This contrast scale keeps the divergence of the full \(n\)-observation samples bounded.

Every test of the sign therefore has a combined error probability bounded away from zero.

---

## From ambiguity to regret

The positive-sign world treats the block; the negative-sign world leaves it untreated.

A wrong assignment costs \(h_n\) per person, on a block with mass proportional to \(h_n^\alpha\).

Under the fixed-constant calibration,

\[
\forall\pi\in\Pi,\qquad
\max_{\sigma\in\{+,-\}}
R_{P_{n,\sigma}}(\pi)
\ge
c\,h_n^{1+\alpha}.
\]

This bounds the worse of the two welfare losses for any fixed policy.

The testing argument extends the ambiguity to data-dependent policies. Substituting \(h_n\) gives the lower-bound scale \(n^{-(1+\alpha)/(2+\alpha+\beta_{\alpha,\gamma})}\).

Under strict overlap, arm rarity adds no exponent. When \(\alpha,\gamma>0\), rarity enlarges the denominator and slows the lower-bound scale.

---

## Clipped contrast score

Clipping replaces a supplied propensity by a value between \(q\) and \(1-q\), preventing arbitrarily large inverse weights.

For supplied regressions and propensity \(\eta=(\mu_0,\mu_1,e)\), with \(q\in(0,1/2]\),

\[
e_q(x;\eta)
=
\min\{1-q,\max\{q,e(x)\}\}.
\]

The function \(e_q\) is the clipped propensity. The AIPW contrast score is

\[
\Gamma_q(O;\eta)
=
\mu_1(X)-\mu_0(X)
+
\frac{A}{e_q(X;\eta)}\{Y-\mu_1(X)\}
-
\frac{1-A}{1-e_q(X;\eta)}\{Y-\mu_0(X)\}.
\]

It starts with the regression contrast and adds weighted outcome residuals from each observed arm.

With true outcome regressions, residuals have conditional mean zero even when clipping binds. With estimated regressions, the remaining bias needs control.

---

## Empirical welfare maximization

Sample splitting trains nuisance functions away from the observations used to evaluate them.

Let \(k(i)\) denote observation \(i\)’s evaluation fold, and \(\widehat\eta^{(-k(i))}\) the estimates trained outside that fold.

\[
\widehat V_{n,q}(\pi)
=
\frac1n\sum_{i=1}^n
\pi(X_i)\,
\Gamma_q\!\left(O_i;\widehat\eta^{(-k(i))}\right).
\]

This estimates welfare by averaging contrast scores for people the candidate rule treats.

Choose the learned policy \(\widehat\pi_n\) to nearly maximize this criterion:

\[
\widehat V_{n,q}(\widehat\pi_n)
\ge
\sup_{\pi\in\Pi}\widehat V_{n,q}(\pi)-\frac1n .
\]

The tolerance \(1/n\) allows a near-maximizer. Oracle inclusion makes the inequality a comparison with the optimal rule.

What separates empirical welfare from actual welfare?

---

## Localized sampling fluctuations

Let \(D_\pi=\{x:\pi(x)\ne\pi^\star_P(x)\}\) be the region where a rule disagrees with the oracle.

On evaluation fold \(k\), hold the trained estimates fixed and define the policy-score difference
\(g_\pi(O)=(\pi(X)-\pi^\star_P(X))\Gamma_q(O;\widehat\eta^{(-k)})\).

It vanishes outside \(D_\pi\). Clipping bounds its magnitude by an envelope \(B=C/q\), and its second moment is at most \(B^2P_X(D_\pi)\).

The margin condition makes low-regret disagreement regions small. Our first extra assumption requires, uniformly over such increment classes,

\[
\mathbb E\left[\sup_{\pi\in\Pi:\,R_P(\pi)\le r}\left|m^{-1}\sum_{i=1}^m g_\pi(O_i)-\int g_\pi(O)\,dP(O)\right|\right]
\le C B m^{-1/2} r^{\alpha/(2+2\alpha)}(\log m)^p .
\]

Here \(m\) is evaluation sample size and \(r\ge0\) is a regret threshold. The supremum ranges over all candidate rules with regret at most \(r\).

The bound controls the largest centered score fluctuation among those rules; it is assumed in addition to finite VC dimension.

---

## From fluctuations to regret

The learned rule is data dependent, so a bound at one fixed regret threshold is insufficient.

Write \(z_\pi\) for the sample average of \(g_\pi\) minus its population mean. Our second extra assumption requires

\[
\mathbb E\sup_{\pi\in\Pi}
\left\{2|z_\pi|-\frac{R_P(\pi)}{4}\right\}_+
\le
C\left(\frac{B^2}{n}\right)^{A_\alpha}(\log n)^p,
\qquad A_\alpha=\frac{1+\alpha}{2+\alpha}.
\]

The positive part \(\{\cdot\}_+\) retains fluctuation exceeding one quarter of a rule’s regret. The supremum covers every candidate rule.

This permits part of the random fluctuation to be absorbed into regret itself. Fixed balanced folds allow the foldwise control to be pooled.

With \(B=C/q\), the sampling contribution is \((nq^2)^{-A_\alpha}\): smaller clipping levels permit larger weights and more noise.

---

## Bias after clipping

For supplied functions \(\bar\eta=(\bar\mu_0,\bar\mu_1,\bar e)\), define

\[
\bar e_q(x)=\min\{1-q,\max\{q,\bar e(x)\}\},
\qquad
\Delta_a(x)=\bar\mu_a(x)-\mu_a(x),
\qquad
b_q(x)=(\bar e_q(x)-e_P(x))\left\{\frac{\Delta_1(x)}{\bar e_q(x)}+\frac{\Delta_0(x)}{1-\bar e_q(x)}\right\}.
\]

Here \(\bar e_q\) is the clipped supplied propensity, \(\Delta_a\) is regression error, and \(b_q\) is the score’s conditional mean minus the true contrast.

- Correct outcome regressions make this drift vanish.
- A clipped supplied propensity equal to the true propensity also makes it vanish.
- Clipping can change the propensity factor even when the supplied propensity is correct.

Ordinary control of the product of estimation errors therefore leaves a clipping contribution.

How can we control that contribution where treatment decisions matter?

---

## Localizing clipping bias

For \(\gamma>0\), choose a contrast window \(0<u\le u_0\) and clipping level \(0<q\le c_o u^\gamma\).

Write \(r=R_P(\pi)\). The weak-overlap part of the disagreement region satisfies

\[
P_X\!\left(D_\pi\cap\{x:p_P(x)\le q\}\right)
\le
\max\{C_o,1\} u^\alpha q^{1/\gamma}+\frac{r}{u}
\]

This bounds the population share where a wrong decision coincides with a rare arm.

- Inside the small-contrast window, joint overlap decay limits that share.
- Outside it, each disagreement costs more than \(u\), so regret limits the share to \(r/u\).

Combining these shares with root-mean-square regression error gives contributions \(r_{\mu,n}u^{\alpha/2}q^{1/(2\gamma)}\) and \(r_{\mu,n}(r/u)^{1/2}\).

A square inequality absorbs part of the latter into regret and leaves \(r_{\mu,n}^2/u\). This is where joint overlap decay repairs the clipping-bias argument.

---

## Regret bound

Under the upper-bound conditions, use deterministic schedules \(q_n,u_n\), with \(\gamma>0\), \(0<u_n\le u_0\), and \(q_n\le c_o u_n^\gamma\).

\[
\mathbb E_P R_P(\widehat\pi_n)
\le
C\left\{
n^{-r_\star}
+(nq_n^2)^{-A_\alpha}
+\frac{r_{\mu,n}r_{e,n}}{q_n}
+r_{\mu,n}u_n^{\alpha/2}q_n^{1/(2\gamma)}
+\frac{r_{\mu,n}^2}{u_n}
\right\}(\log n)^p .
\]

This bounds expected welfare loss. The added \(n^{-r_\star}\) benchmark term caps the reported exponent at \(r_\star\); it is separate from the four sampling-and-bias contributions:

- \((nq_n^2)^{-A_\alpha}\): sampling noise from clipped scores.
- \(r_{\mu,n}r_{e,n}/q_n\): estimation-error product amplified by inverse weights.
- \(r_{\mu,n}u_n^{\alpha/2}q_n^{1/(2\gamma)}\): drift where rare arms and small contrasts coincide.
- \(r_{\mu,n}^2/u_n\): regression error outside the small-contrast window.

Lowering the clip reduces localized clipping bias but increases noise and the amplified product error.

---

## Tuning and regimes

Use schedules \(q_n=q_0 n^{-s_{\mathrm{feas}}}\) and \(u_n=\bar u n^{-t_{\mathrm{feas}}}\), with fixed positive bases satisfying \(0<\bar u\le u_0\) and \(0<q_0\le\min\{1/2,c_o\bar u^\gamma\}\).

The best nuisance-and-clipping exponent is

\[
g_{\mathrm{joint}}
=
\max_{\substack{0\le s\le 1/2\\ 0\le t\le s/\gamma}}
\min\left\{
A_\alpha(1-2s),\,
c-s,\,
a+\frac{s}{2\gamma}+\frac{\alpha t}{2},\,
2a-t
\right\}.
\]

The trial exponents \(s,t\) govern how fast clipping and the contrast window shrink. The four entries correspond, in order, to the four sampling-and-bias terms.

The minimum selects the slowest contribution; maximization chooses the best balance. The constraint \(t\le s/\gamma\) keeps tuning inside the joint-decay window.

- If \(g_{\mathrm{joint}}\ge r_\star\), the conditional upper bound matches the lower-bound polynomial exponent, up to logarithms.
- If \(g_{\mathrm{joint}}<r_\star\), the upper-bound exponent is \(g_{\mathrm{joint}}\).

Under strict overlap, fixed clipping with \(0<q_0\le\underline p/2\) gives \(r_{\mathrm{up}}=r_{\mathrm{feas}}=\min\{A_\alpha,c\}\).

---

## Open questions

When \(g_{\mathrm{joint}}<r_\star\), can a feasible estimator attain \(r_\star\) under comparable nuisance conditions, or is a slower rate unavoidable?

Two routes could resolve this:

- Construct a feasible procedure reaching \(r_\star(\alpha,\gamma)\) under comparable nuisance conditions.
- Establish a lower bound incorporating the difficulty of learning nuisance functions in the weak arm.

---

## Takeaways

- Contrast size, near-tie mass, and informative-arm probability jointly produce the lower-bound exponent \(r_\star(\alpha,\gamma)\).
- Clipping controls inverse weights; joint overlap decay controls the region where clipping interacts with regression error and wrong decisions.
- Under explicit nuisance and fluctuation conditions, tuning matches the lower-bound polynomial exponent when those costs do not bind. Whether the slower bound is unavoidable remains open.

---

## Appendix: Minimax lower bound

The calibrated observed-law class forces worst-case expected regret of at least \(c\,n^{-r_\star(\alpha,\gamma)}\).

@formal thm:minimax-lower

---

## Appendix: Conditional upper bound

The tuned clipped cross-fitted AIPW rule satisfies a uniform upper bound over its explicit side-condition domain.

@formal oeq:feasible-upper
