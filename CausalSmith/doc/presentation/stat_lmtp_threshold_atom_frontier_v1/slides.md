# Inference for Minimum Dose Policies

Raising every treatment below a minimum dose creates a point mass that changes how accurately we can estimate the resulting mean outcome.

---

## Motivation

A practitioner wants to raise low treatment doses while leaving higher doses unchanged.

For natural treatment \(A\), threshold \(\delta\), and assigned treatment \(A^\delta\), the policy is

\[
d_\delta(a)=\max\{a,\delta\},
\qquad
A^\delta=d_\delta(A).
\]

Every dose below \(\delta\) becomes exactly \(\delta\). The policy creates an **atom**: positive probability concentrated at one dose.

We allow a predetermined threshold \(\delta_n\) to change with sample size \(n\), within \(0\leq\delta_n\leq\bar\delta<1\).

---

## Research question

Díaz et al. (2021) develop estimation and root-\(n\) inference for modified treatment policies under regularity conditions.

The usual approach averages predicted responses under the policy and uses regular influence-function inference.

For an exact clamp, that average assigns positive weight to a regression value at one dose. Continuous treatment data supply no observations exactly at that dose.

Gaïffas (2005) studies the related difficulty of estimating a regression value where treatment density becomes small.

**How accurately can we estimate the exact clamp mean, and how short can uniformly valid confidence intervals be?**

---

## Key idea

Separate ordinary mean estimation from learning the response at the threshold.

The threshold regression error matters only after multiplication by the probability moved to that threshold.

Under fixed finite strata, bounded outcomes, known regression smoothness, and polynomial treatment-density thinning, optimal absolute-error risk and honest interval length have scale

\[
r_n=n^{-1/2}+\delta_n^{\kappa+1}h_n^\beta .
\]

Here \(\beta>0\) controls regression smoothness, \(\kappa\geq0\) controls density thinning, and \(h_n\) is the local fitting window.

- \(n^{-1/2}\): ordinary sampling error.
- \(\delta_n^{\kappa+1}\): mass moved by the policy.
- \(h_n^\beta\): error in learning the threshold response.

A shrinking threshold can make the weighted regression error small enough for root-\(n\) accuracy.

---

## Example

Take one stratum, density \(\pi(a)=2a\), and smoothness \(\beta=\kappa=1\). The mass moved to the threshold is \(\delta_n^2\).

Compare Bernoulli outcomes with mean \(m_0(a)=1/2\) against a triangular regression bump centered at \(\delta_n\), with height \(h_n\).

When \(\delta_n\gg n^{-1/4}\),

\[
h_n\asymp (n\delta_n)^{-1/3},
\qquad
K_n\asymp n\delta_n h_n^3,
\qquad
\Delta_n\asymp \delta_n^2h_n.
\]

\(K_n\) is the \(n\)-sample Kullback–Leibler divergence: expected log-likelihood evidence distinguishing the alternatives. \(\Delta_n\) is their difference in clamp means. The symbol \(\asymp\) means bounded above and below by fixed positive multiples.

The window keeps that evidence bounded, while the clamp mean changes by **atom mass times bump height**.

---

## Model and target

Observe \(n\) independent units \(O_i=(X_i,A_i,Y_i)\) from law \(P\). Baseline stratum \(X\) has \(J\) fixed possible values; treatment \(A\) and outcome \(Y\) lie in \([0,1]\).

Write \(p_x=P(X=x)\), \(\pi_x(a)\) for the conditional treatment density, and \(\mu_x^P(a)\) for the continuous conditional outcome regression.

\[
q_x(\delta)=\int_{[0,\delta]}\pi_x(a)\,\mathrm da,
\qquad
\nu_\delta(P)=\mathbb E_P\!\left[Y\mathbf 1\{A>\delta\}\right].
\]

\(q_x(\delta)\) is the collapsed probability within stratum \(x\); \(\nu_\delta(P)\) is the retained outcome contribution.

\[
\theta_\delta(P)
=
\nu_\delta(P)
+
\sum_{x\in\mathcal X}p_xq_x(\delta)\mu_x^P(\delta).
\]

The target adds outcomes retained above the threshold to collapsed mass multiplied by its threshold response. Here \(\mathcal X\) is the stratum set.

---

## Assumptions

**Treatment thinning.** For fixed known \(\kappa\geq0\) and positive envelope constants \(c_-,c_+\),

\[
c_- a^\kappa \leq \pi_x(a) \leq c_+ a^\kappa .
\]

The lower bound guarantees nearby observations; the upper bound controls nearby information and collapsed mass. Every stratum has probability at least a fixed \(p_{\min}>0\).

**Quantitative smoothness.** Fix known \(\beta>0\), radius \(L>0\), and polynomial degree \(\ell=\lceil\beta\rceil-1\).

\[
\left|
\mu_x^P(t)
-
\sum_{j=0}^{\ell}
\frac{(\mu_x^P)^{(j)}(s)}{j!}(t-s)^j
\right|
\le
L|t-s|^\beta .
\]

This Hölder condition bounds the error of a Taylor approximation between doses \(s,t\); \(j\) indexes derivatives.

For our example, it says \(|\mu(t)-\mu(s)|\leq L|t-s|\): nearby means cannot change arbitrarily fast.

Call the laws satisfying these conditions \(\mathcal M\).

---

## Main result

@informal thm:minimax-risk: Under our fixed-stratum Hölder and thinning conditions, every deterministic threshold path in \([0,\bar\delta]\) has minimax absolute-error risk bounded above and below by constants times \(r_n\), for all sufficiently large \(n\).

\(R_n^\star\) is the smallest worst-case expected absolute error among all estimators.

For fixed disjoint split blocks \(B_n\), each containing at least \(\lfloor n/4\rfloor\) observations, our stabilized total Gram estimator attains the upper bound:

\[
c r_n
\leq
R_n^\star
\leq
\sup_{P\in\mathcal M} \mathbb E_P\!\left[
\left|\widehat\theta_{n,B_n}^{\mathrm{TG}}-\theta_{\delta_n}(P)\right|
\right]
\leq
C r_n .
\]

The superscript \(\mathrm{TG}\) labels the estimator constructed below; \(c,C\) are positive comparison constants depending only on fixed model parameters.

Root-\(n\) accuracy depends on whether the weighted threshold-regression error is small enough.

---

## Honest inference

An interval is **honest** when its coverage guarantee holds uniformly over every law in \(\mathcal M\).

@informal thm:honest-length: Under our model conditions, every deterministic threshold path in \([0,\bar\delta]\) and admissible fixed split sequence eventually gives coverage at least \(1-\alpha\) and optimal worst-case expected interval length comparable to \(r_n\).

Fix noncoverage probability \(0<\alpha<1/2\). Our interval \(\mathrm{CI}_n\) satisfies

\[
\inf\Bigl\{
P^{\otimes n}\{\theta_{\delta_n}(P)\in \mathrm{CI}_n(O_1,\ldots,O_n)\}:
P\in\mathcal M
\Bigr\}\geq 1-\alpha,
\]

where \(P^{\otimes n}\) is the law of the independent sample.

\[
c\,r_n
\leq
\sup\Bigl\{
\mathbb E_{P^{\otimes n}}\bigl[\operatorname{len}(\mathrm{CI}_n)\bigr]:
P\in\mathcal M
\Bigr\}
\leq
C\,r_n .
\]

Here \(\operatorname{len}\) means interval length. Every honest interval has worst-case expected length at least \(c\,r_n\). Constants may also depend on \(\alpha\).

---

## Three estimation tasks

Split the sample into fixed disjoint blocks \(I_0,I_1,I_2\), each with at least \(\lfloor n/4\rfloor\) observations, so the three tasks use independent data.

- \(I_0\): estimate the retained contribution by averaging \(Y_i\mathbf 1\{A_i>\delta_n\}\); call this \(\widehat\nu_n\).
- \(I_1\): estimate each joint collapsed mass \(p_xq_x(\delta_n)\) by its sample proportion; call this \(\widehat b_x\).
- \(I_2\): estimate the threshold response; call this \(\widetilde\mu_x\).

Combine them exactly as the target requires:

\[
\widehat\theta_n
=
\Pi_{[0,1]}\!\left[
\widehat\nu_n+\sum_{x\in\mathcal X}\widehat b_x\widetilde\mu_x
\right].
\]

\(\Pi_{[0,1]}\) clips a value to the bounded outcome range.

The difficult task is estimating \(\widetilde\mu_x\) from nearby doses.

---

## Local regression

Fit a degree-\(\ell\) polynomial using doses in \([\delta_n,\delta_n+h_n]\), separately within each stratum, and read its intercept.

Rescale treatment so the threshold becomes zero:

\[
U_i=\frac{A_i-\delta_n}{h_n},
\qquad
v_\ell(u)=(1,u,\ldots,u^\ell)^\top .
\]

\(U_i\) is the local dose coordinate; \(v_\ell\) collects polynomial terms.

On a sufficiently informative realized design, intercept weights \(w_{ix}\) satisfy

\[
\sum_{i\in I_2} w_{ix} U_i^j=\mathbf 1\{j=0\}.
\]

For powers \(j=0,\ldots,\ell\), the weighted fit reproduces the constant and cancels every higher-order polynomial term at the threshold. Only the controlled Taylor remainder remains.

In our \(\beta=1\) example, \(\ell=0\): this is a local average.

---

## Bandwidth choice

A wider window supplies more observations but allows more approximation bias.

- The local count has scale \(n h_n(\delta_n+h_n)^\kappa\).
- Regression noise decreases with the square root of that count.
- Smoothness bounds approximation error on scale \(h_n^\beta\).

Choose \(h_n\) to balance noise and approximation error. For all sufficiently large \(n\),

\[
0<h_n,\qquad
h_n\leq 1-\bar\delta,\qquad
n h_n^{2\beta+1}(\delta_n+h_n)^\kappa=1.
\]

The first two conditions keep the fitting window inside treatment support; the equality makes the two errors comparable.

Multiplying regression error by collapsed mass produces \(\delta_n^{\kappa+1}h_n^\beta\).

How does the window change as the threshold approaches zero?

---

## Bandwidth regimes

The bandwidth transition occurs at

\[
\delta_{\mathrm{edge},n}
=
n^{-1/(2\beta+\kappa+1)} .
\]

This edge scale compares the threshold’s distance from zero with the window needed to learn its response.

| Threshold location | Window width | Why |
|---|---|---|
| \(\delta_n/\delta_{\mathrm{edge},n}\to0\) | \(h_n\) has order \(n^{-1/(2\beta+\kappa+1)}\) | The window dominates the threshold; density across the window has scale \(h_n^\kappa\). |
| \(\delta_n/\delta_{\mathrm{edge},n}\to\infty\) | \(h_n\asymp(n\delta_n^\kappa)^{-1/(2\beta+1)}\) | The threshold dominates the window; density across it has scale \(\delta_n^\kappa\). |

At thresholds comparable to the edge scale, the window also has order \(n^{-1/(2\beta+\kappa+1)}\).

For \(\beta=\kappa=1\), the edge is \(n^{-1/4}\); above it, our example uses \(h_n\asymp (n\delta_n)^{-1/3}\).

---

## Design stabilization

A polynomial fit can fail when its window is empty or dose locations provide too little information to invert the fitting matrix.

Let \(N_x\) be the local observation count and \(G_x\) the sum of local cross-products \(v_\ell(U_i)v_\ell(U_i)^\top\).

Use the fit only on the event \(\Omega_x\) where \(N_x>0\) and every coefficient vector \(v\) satisfies

\[
v^\top G_xv
\geq
\frac{\lambda_\star N_x}{2}\lVert v\rVert_2^2 .
\]

The known positive constant \(\lambda_\star\) supplies a uniform minimum amount of information per observation.

\[
\widetilde\mu_x
=
\begin{cases}
\Pi_{[0,1]}\!\left(\sum_{i\in I_2}w_{ix}Y_i\right),& \Omega_x,\\
1/2,& \Omega_x^{c}.
\end{cases}
\]

Use the clipped intercept when the design passes; otherwise use the bounded midpoint.

The density envelope guarantees population information uniformly as the threshold moves. Failed checks become exponentially rare in the local information count.

---

## Bias and noise

On a passing design, polynomial reproduction removes the Taylor terms. Smoothness and bounded-outcome concentration give the regression radius

\[
B_x
=
Lh_n^\beta\sum_{i\in I_2}|w_{ix}|
+
t_\alpha\left(\sum_{i\in I_2}w_{ix}^2\right)^{1/2}.
\]

- The first term bounds approximation bias using total absolute weight.
- The second bounds noise using the square root of the sum of squared weights.
- \(t_\alpha=\sqrt{\log(12J/\alpha)/2}\) calibrates the concentration allowance.

The design check keeps total absolute weight bounded and squared-weight sum at most a constant divided by \(N_x\).

Bias-aware intervals, as in Armstrong and Kolesár (2018), allow for approximation error explicitly rather than treating the fitted intercept as unbiased.

---

## Interval construction

Let \(b_0=t_\alpha/\sqrt{|I_0|}\) and \(b_1=t_\alpha/\sqrt{|I_1|}\) cover sampling errors in the retained mean and atom masses.

For each stratum, set \(D_x=(\widehat b_x+b_1)B_x+b_1\) on a passing design: multiply regression uncertainty by an upper bound on atom mass, then add mass-estimation uncertainty.

On a failed design, set \(D_x=\widehat b_x+b_1\), allowing for the full bounded-response uncertainty.

\[
\mathrm{CI}_n
=
\left[
\widehat\theta_n-b_0-\sum_{x\in\mathcal X}D_x,\,
\widehat\theta_n+b_0+\sum_{x\in\mathcal X}D_x
\right]\cap[0,1].
\]

This interval covers retained-mean error, mass error, regression bias, regression noise, and failed fits.

The same atom weighting that reduces estimation error also reduces the necessary interval width.

---

## Why the rate is unavoidable

Two pairs of hard-to-distinguish laws isolate the two error sources.

A global Bernoulli regression shift of \(n^{-1/2}\) changes the clamp mean on that scale while leaving bounded statistical evidence in \(n\) observations.

A localized pair \(Q_0,Q_1\) changes regression only near the threshold:

\[
\mu_x^{Q_1}(t)-\mu_x^{Q_0}(t)
=
a\,h_n^\beta b\!\left(\frac{t-\delta_n}{h_n}\right)
\]

Here \(a\) is a fixed small amplitude, and \(b\) is a nonnegative bump with height one at zero and support \([-1,1]\).

The bandwidth balance keeps evidence for this bump bounded. Its threshold height is multiplied by collapsed mass, giving target separation at least a constant times \(\delta_n^{\kappa+1}h_n^\beta\).

An estimator must accommodate these separations; an honest interval must be long enough to cover them.

---

## Threshold regimes

The bandwidth transition concerns nearby information. The risk transition also accounts for the mass weighting that information receives.

\[
\delta_{\mathrm{crit},n}
=
n^{-1/\{2(\beta\kappa+2\beta+\kappa+1)\}},
\qquad
\delta_{\mathrm{edge},n}
=
n^{-1/(2\beta+\kappa+1)} .
\]

The critical scale marks where weighted regression error matches ordinary sampling error. It is asymptotically larger than the edge scale.

| Threshold path | Optimal risk and honest length |
|---|---|
| \(\delta_n/\delta_{\mathrm{crit},n}\to0\) | \(r_n\asymp n^{-1/2}\) |
| \(\delta_n/\delta_{\mathrm{crit},n}\to c_0>0\) | Both error terms are comparable; \(r_n\asymp n^{-1/2}\) |
| \(\delta_n/\delta_{\mathrm{crit},n}\to\infty\), \(\delta_n\to0\) | \(r_n\asymp \delta_n^{\kappa+1}\bigl(n\delta_n^\kappa\bigr)^{-\beta/(2\beta+1)}\) |
| \(\delta_n\to\delta_0>0\) | \(r_n\asymp n^{-\beta/(2\beta+1)}\) |
| \(\delta_n=0\) | Ordinary bounded-mean inference; \(r_n=n^{-1/2}\) |

Here \(c_0\) is a positive limiting ratio and \(\delta_0\) a positive limiting threshold.

---

## Example revisited

For \(\pi(a)=2a\) and \(\beta=\kappa=1\), regression error has scale \(h_n\), but the policy weights it by \(\delta_n^2\).

Above the bandwidth edge \(n^{-1/4}\), the window has order \((n\delta_n)^{-1/3}\). The risk transition occurs at the larger threshold scale:

\[
\delta_n\asymp n^{-1/10}
\quad\Longleftrightarrow\quad
\Delta_n\asymp n^{-1/2}.
\]

Here \(\Delta_n\) is the clamp-mean separation between our triangular-bump alternatives.

- Below the critical scale, shrinking atom mass permits root-\(n\) accuracy.
- Above it, learning the threshold response determines overall difficulty.
- At zero threshold, the atom disappears and the target is the ordinary outcome mean.

---

## Causal assumptions

Let \(P^{\mathrm F}\) be a law including potential outcomes \(Y(a)\), the outcomes a unit would have at each dose \(a\). The causal policy mean is

\[
\psi_\delta(P^{\mathrm F})
=
\mathbb E_{P^{\mathrm F}}\!\left[Y(d_\delta(A))\right].
\]

It averages outcomes after applying the minimum-dose rule to natural treatment.

An unobserved variable \(U\) contains the unit’s response characteristics; \(g_x(a,U)\) gives its response at dose \(a\) in stratum \(x\).

**Consistency:** with probability one, the same equations hold simultaneously for every dose \(a\):

\[
Y(a)=g_X(a,U),
\qquad
Y=g_X(A,U).
\]

**Conditional independence:** \(A\perp U\mid X\). Within each stratum, treatment carries no additional information about response characteristics.

**Mean continuity:** \(m_x^{\mathrm F}(a)=\mathbb E_{P^{\mathrm F}}\{g_x(a,U)\mid X=x\}\) is continuous on \([0,\bar\delta]\). This is the stratum’s average structural response, including at the clamp threshold.

---

## Further results

- **Causal interpretation:** Under the three causal conditions just given and observed law \(P\in\mathcal M\), \(\psi_\delta(P^{\mathrm F})=\theta_\delta(P)\); the same estimator and interval attain matching causal risk and honest-length bounds of order \(r_n\).
- **Continuity alone:** Under the same design conditions, replacing quantitative smoothness by continuity gives matched risk and honest-length scale \(s_n=n^{-1/2}+\delta_n^{\kappa+1}\); at a fixed positive threshold, neither minimax quantity converges to zero.

---

## Open questions

Can we obtain sharp limiting constants for optimal honest interval length, beyond matching its order?

Optimizing local weights against their exact worst-case regression bias gives a starting point.

A complete construction must also incorporate retained-mean uncertainty, atom masses and their uncertainty, aggregation across strata, and protection against failed local designs.

---

## Takeaways

- An exact minimum-dose policy creates a point mass, making a single regression value part of an otherwise ordinary mean.
- The difficulty is local regression error multiplied by mass moved: \(r_n=n^{-1/2}+\delta_n^{\kappa+1}h_n^\beta\).
- Under known smoothness and polynomial thinning, stabilized local fitting and explicit bias allowances attain matching estimation and honest-inference bounds.

---

## Appendix: Minimax clamp frontier

The stabilized estimator attains the best possible worst-case absolute-error order.

@formal thm:minimax-risk

---

## Appendix: Honest length frontier

Uniformly valid confidence intervals attain, and must pay, the same worst-case expected-length order.

@formal thm:honest-length

---

## Appendix: Causal frontier lift

The observed estimator and interval attain the same frontier for the causal clamp mean under the declared causal conditions.

@formal thm:causal-frontier-lift

---

## Appendix: Continuity frontier characterization

Qualitative continuity gives a separate frontier governed by sampling error and collapsed mass.

@formal thm:continuity-only-frontier
