# Efficient Treatment Effects From Private Trial Records

We choose what each participant reports so that a randomized trial estimates its treatment effect as accurately as local privacy permits.

---

## Motivation

A trial records binary treatment \(W_i\) and binary outcome \(Y_i\) for each subject. Treatment has known probability \(p\); control has probability \(q=1-p\).

The target is \(\tau=\mu_1-\mu_0\), the difference between treatment and control success probabilities.

Ohnishi and Awan (2025) add noise to an inverse-probability contribution and average the reports:

\[
\widetilde A_i
=
\frac{W_iY_i}{p}
-
\frac{(1-W_i)Y_i}{q}
+
L_i,
\qquad
\widehat\tau_{\mathrm{OA}}
=
\frac{1}{n}\sum_{i=1}^{n}\widetilde A_i.
\]

Here \(n\) is sample size. The independent centered Laplace noise \(L_i\) has scale \(\Delta_A/\varepsilon\), where \(\Delta_A=p^{-1}+q^{-1}\) and \(\varepsilon>0\) is the privacy budget.

The estimator is unbiased. Its asymptotic variance constant contains the privacy-noise contribution
\[
\frac{2\Delta_A^2}{\varepsilon^2}.
\]
Does this reporting rule give the smallest variance constant?

---

## Research question

Privacy protects the entire assignment–outcome record before the analyst sees it. The reporting rule determines the information available for estimation.

- Additive noise preserves the weighted mean, but its calibration does not optimize information about the treatment effect.
- Steinberger (2024) develops sequential private efficiency and optimizes Fisher information for scalar parameters.
- Our scalar target depends on two unknown means. Their common level is a **nuisance parameter**: shifting both means together leaves their difference unchanged.

What is the smallest attainable squared-error constant when both means are unknown—and can we attain it using only private observations?

---

## Key idea

Choose the release that best reveals the treatment-effect difference while allowing the unknown common level to vary.

- Every private release can be reconstructed from a release using fourteen two-level reporting patterns.
- For each release, find the least informative direction that changes the treatment effect by one unit.
- Choose the release that supplies the most information in that difficult direction.

Write \(\theta=(\mu_0,\mu_1)^\top\) for the two means. The optimized information is \(J^*(\theta,p,\varepsilon)\); its reciprocal \(V^*(\theta,p,\varepsilon)\) is the best stationary contrast variance.

With interior assignment and means, fixed positive privacy, and a fixed measurable rule selecting a mutually optimal release and direction, the same constant bounds all sequential private procedures. A private-pilot estimator attains it.

---

## Example

Take \(p=1/2\), interior means satisfying \(\mu_0+\mu_1=1\), and \(\varepsilon>0\).

The sign \((2W_i-1)(2Y_i-1)\) is positive for control failure or treatment success, and negative otherwise. Its mean is \(\tau\).

Release a sign \(Z_i\), retaining the input with probability \(e^\varepsilon/(e^\varepsilon+1)\) and otherwise flipping it. This is **binary randomized response**.

Its attenuation is \(\kappa_\varepsilon=(e^\varepsilon-1)/(e^\varepsilon+1)\): \(E_\theta[Z_i]=\kappa_\varepsilon\tau\). Thus \(\widehat\tau=\overline Z/\kappa_\varepsilon\), where \(\overline Z\) is the sample average, is unbiased.

\[
V^*(\theta,1/2,\varepsilon)
=
\left(\frac{\cosh(\varepsilon/2)}{\sinh(\varepsilon/2)}\right)^2-\tau^2.
\]

This is the optimal variance constant. The hyperbolic-function ratio equals \(1/\kappa_\varepsilon\), so it is also the variance of the rescaled released sign.

@informal thm:balanced-reduction: With interior means, \(p=1/2\), \(\mu_0+\mu_1=1\), and \(\varepsilon>0\), binary randomized response to the treatment–outcome sign attains the optimal contrast variance.

---

## Model

Let \(Y_i(0)\) and \(Y_i(1)\) be subject \(i\)'s binary potential outcomes. We observe \(Y_i=Y_i(W_i)\), the outcome under the assigned arm.

\[
c=(-1,1)^\top,
\qquad
\tau=E[Y_i(1)-Y_i(0)]=\mu_1-\mu_0=c^\top\theta.
\]

The vector \(c\) takes the treatment mean minus the control mean.

The private record is \(X_i=(W_i,Y_i)\). In the order \((0,0),(0,1),(1,0),(1,1)\), its probability vector is

\[
\pi_\theta=
\begin{pmatrix}
q(1-\mu_0)\\
q\mu_0\\
p(1-\mu_1)\\
p\mu_1
\end{pmatrix}.
\]

These are the probabilities of control failure, control success, treatment failure, and treatment success. Randomization identifies the causal contrast from this four-category distribution.

---

## Assumptions

- **Sampling and assignment:** subjects are independent and identically distributed; assignment is independent of both potential outcomes.
- **Known interior design:** fixed \(0<p<1\) gives both arms positive probability.
- **Interior binary means:** \(0<\mu_0,\mu_1<1\) gives all four records positive probability.
- **Fixed privacy:** \(\varepsilon>0\) stays constant as sample size grows.

Each subject supplies one release. Its rule may depend on earlier private outputs:

\[
Q_i(A\mid x,h)\le \exp(\varepsilon)Q_i(A\mid x',h)
\]

Here \(Q_i\) is the reporting rule, \(A\) is an output event, \(x,x'\) are any two records, and \(h\) is the preceding-release history.

This condition holds at every history and protects assignment and outcome jointly. Smaller \(\varepsilon\) requires more similar reporting probabilities.

The balanced example satisfies these assumptions whenever its complementary means are interior.

---

## Main result

A **strong-saddle selector** is a fixed measurable rule selecting a release and a direction optimal against each other at every interior parameter.

At an interior baseline \(\theta_0\), consider nearby means \(\theta_{n,h}=\theta_0+h/\sqrt n\), where \(h\) shifts the two means on the estimation-error scale.

For a release-and-estimation procedure \(\mathcal P\), let \(U_{n,h}^{\mathcal P}\) be its error multiplied by \(\sqrt n\), centered at the nearby treatment effect.

@informal thm:sequential-minimax: With interior assignment and means, fixed positive privacy, and a measurable strong-saddle selector, every sequential private procedure has local squared-error constant at least \(V^*\), and a regular private-pilot procedure attains it.

\[
V^*(\theta_0,p,\varepsilon)
\le
\sup_{H>0}\;\liminf_{n\to\infty}\;
\sup_{h\in\mathcal H_{n,H}(\theta_0)}
\mathbb E_{\theta_{n,h}}^{\mathcal P}
\!\left[(U_{n,h}^{\mathcal P})^2\right].
\]

Here \(\mathcal H_{n,H}(\theta_0)\) contains interior alternatives with \(\|h\|_2\le H\). The formula takes worst local risk, its lower asymptotic limit, then enlarges the neighborhood.

**Regular** procedures have a common centered limiting error law under fixed local shifts, finite second moments, and negligible squared-error tails uniformly over bounded shifts. Our pilot procedure attains equality in this class.

---

## Contrast information

A **stationary release** \(Q\) uses the same reporting rule for every subject.

Its output Fisher-information matrix \(I_\theta(Q)\) measures what reports reveal about the two means. Its contrast variance is \(c^\top I_\theta(Q)^+c\), where \(+\) denotes the generalized inverse; the variance is infinite if the contrast cannot be identified.

Every direction \(v(t)=(t,t+1)^\top\) changes the treatment effect by one unit because \(c^\top v(t)=1\).

- Changing \(t\) adds a common shift to both means.
- Directional information is \(v(t)^\top I_\theta(Q)v(t)\).
- Minimizing over \(t\) finds the hardest way to change the treatment effect. Its reciprocal is the contrast variance when the contrast is estimable.

In the balanced example, reports reveal \(\kappa_\varepsilon\tau\), even though they do not identify the common level.

---

## Fourteen reporting patterns

A pattern \(S\) is any nonempty proper subset of the four records. There are fourteen such subsets; their collection is \(\mathcal S\).

Let \(b_S(k)\) equal \(e^\varepsilon\) when record \(x_k\) belongs to \(S\), and \(1\) otherwise. A nonnegative weight \(\alpha_S\) scales these probabilities:

\[
Q_\alpha(S\mid x_k)=\alpha_S b_S(k),
\qquad
\Pr_\theta(S)=\alpha_S h_S(\theta).
\]

These formulas give the conditional probability of reporting label \(S\) and its population probability.

Feasible weights satisfy \(\sum_S\alpha_S b_S(k)=1\) for every record. Their set is \(\mathcal A_\varepsilon\).

The factor \(h_S(\theta)=\pi_\theta^\top b_S\) averages the pattern entries over records; \(g_S=\nabla_\theta h_S(\theta)\) measures how it changes with the means.

The two reporting levels have ratio \(e^\varepsilon\), ensuring privacy. We call these rules **staircase releases**.

---

## Privacy geometry

Fix one output \(z\) of an arbitrary private rule. Its four record-specific densities form the vector \((f_1(z),f_2(z),f_3(z),f_4(z))\), measured relative to a common measure \(\nu\).

Write \(r=e^\varepsilon>1\). Privacy forces every density to be at most \(r\) times every other density.

Let \(m_{\mathrm{base}}(z)\) be the smallest entry. For a nonzero vector, define \(y_j(z)=(f_j(z)/m_{\mathrm{base}}(z)-1)/(r-1)\). The privacy bound gives \(0\le y_j(z)\le1\).

\[
f_j(z)=m_{\mathrm{base}}(z)\bigl(1+(r-1)y_j(z)\bigr).
\]

This expresses the density vector through a point in the four-dimensional unit cube. A cube corner sets each coordinate to zero or one, giving exactly the two reporting levels \(1\) and \(r\).

The standard nonnegative mixture over cube corners reproduces every coordinate \(y_j(z)\). Each corner is a two-level reporting pattern, so this already expresses the density vector as a mixture of staircase vectors.

---

## Removing constant patterns

The corner mixture includes the empty and full subsets, whose pattern vectors are constant. Replace their combined constant contribution using a singleton \(S_\dagger\) and its complement:

\[
b_{S_\dagger}(j)+b_{\mathcal X\setminus S_\dagger}(j)=r+1,
\]

At every record one pattern contributes \(r\) and the other contributes \(1\). Giving the pair equal nonnegative weight therefore reproduces the combined constant mass. After this replacement, only the fourteen nonempty proper patterns remain. Denote their resulting nonnegative coefficient densities by \(\lambda_S(z)\).

---

## From densities to releases

The construction gives a nonnegative decomposition of one arbitrary four-entry output-density vector:

\[
f_j(z)=\sum_{S\in\mathcal S}\lambda_S(z)b_S(j)
\quad\text{for \(\nu\)-almost every \(z\), for every \(j\)}.
\]

Each original density is the same mixture of pattern vectors, using the coefficients just constructed.

Integrate over outputs: \(\alpha_S=\int\lambda_S(z)\,d\nu(z)\). Since every original reporting rule sums to one, these integrated weights satisfy \(\sum_S\alpha_S b_S(j)=1\).

For an active pattern, use \(\lambda_S(z)/\alpha_S\) as the density of a random transformation \(K\) from that pattern to the original output.

@informal lem:staircase-refinement: For interior assignment and means and fixed positive privacy, every stationary private release is a random transformation of a fourteen-pattern release that retains at least as much information.

\[
Q=K\circ Q_\alpha,
\qquad
I_\theta(\alpha)-I_\theta(Q)\succeq0.
\]

The first formula reconstructs the original release. The second says that the pattern release has at least as much information in every direction: random transformation can discard information.

Thus optimizing the fourteen patterns covers arbitrary private output spaces.

---

## Finite optimization

@informal thm:finite-oracle: At interior assignment and arm means and fixed positive privacy, the fourteen-pattern optimization gives the smallest contrast variance over every stationary private channel and measurable output space.

\[
J^*(\theta,p,\varepsilon)
=
\max_{\alpha\in\mathcal A_\varepsilon}
\min_{t\in\mathbb R}
\sum_{S\in\mathcal S}
\alpha_S\frac{(g_S^{\top}v(t))^2}{h_S(\theta)},
\qquad
V^*(\theta,p,\varepsilon)
=
\frac{1}{J^*(\theta,p,\varepsilon)}.
\]

The sum is directional information: each label’s probability times its squared directional score.

- The inner minimum allows the unknown common mean to move against us.
- The outer maximum chooses the most informative private release.
- For fixed \(t\), choosing weights is a linear program; for fixed weights, minimizing over \(t\) is a quadratic problem.

A strong-saddle selector returns weights and a minimizing direction, with those weights also maximizing information at that direction.

In the balanced complementary-means example, the optimum is the binary sign release and \(V^*=\kappa_\varepsilon^{-2}-\tau^2\).

---

## Why adaptation cannot improve

The finite optimization supplies one difficult direction \(v(t^*)\) that works against every feasible release:

\[
\max_{\alpha\in\mathcal A_\varepsilon}
F_\theta(\alpha,t^*)
=
J^*(\theta,p,\varepsilon).
\]

Here \(F_\theta(\alpha,t)\) is the directional-information sum, and \(t^*\) is the selected minimizing coordinate. Even the best release cannot exceed \(J^*\) in this direction.

- Freeze the distribution of preceding outputs. Pairing that history with the next report gives a private channel.
- The fourteen-pattern comparison caps its new directional information.
- Each new score—the derivative of the log reporting probability—has conditional mean zero given the past. Information contributions therefore add.

The Bayesian information inequality of Van Trees (2001) converts the accumulated information cap into a squared-error bound. Localization along \(v(t^*)\) gives the main lower bound.

Selecting later rules from earlier reports cannot escape this common difficult direction.

---

## Private pilot

Use the first \(m_n\) subjects to learn the means privately:

\[
m_n\longrightarrow\infty,
\qquad
\frac{m_n}{n}\longrightarrow0,
\]

The pilot grows enough to learn while leaving an asymptotically full main sample. Both stages have observations for \(n\ge2\); the minimax theorem uses \(m_n=\lfloor\sqrt n\rfloor\).

Four-category randomized response reports the true category with probability \(e^\varepsilon/(e^\varepsilon+3)\), and each other category with probability \(1/(e^\varepsilon+3)\).

\[
\widehat u_k=\frac{1}{m_n}\sum_{i=1}^{m_n}\mathbf1\{R_i=k\},
\qquad
\widehat\pi_k
=\frac{(e^\varepsilon+3)\widehat u_k-1}{e^\varepsilon-1},
\qquad k\in\{0,1,2,3\}.
\]

Here \(R_i\) is a pilot report, \(\widehat u_k\) its empirical category frequency, and \(\widehat\pi_k\) the inverted record-probability estimate.

Divide the control-success estimate by \(q\) and treatment-success estimate by \(p\). Clipping keeps the resulting \(\widetilde\theta\) inside the parameter domain.

Evaluate the fixed selector there to obtain \((\widetilde\alpha,\widetilde t,\widetilde J)\): release weights, difficult-direction coordinate, and information.

---

## Estimator

Main-sample reports correct the pilot’s treatment-effect estimate.

For a released pattern \(S\), attach the correction

\[
\widetilde\phi(S)
=\frac{g_S^{\top}v(\widetilde t)}
       {\widetilde J\,h_S(\widetilde\theta)}.
\]

This projects the pattern’s score onto the selected contrast direction and divides by the selected information.

Remaining subjects release labels \(S_i\) through \(Q_{\widetilde\alpha}\). Report

\[
\widehat\tau^*
=\widetilde\theta_1-\widetilde\theta_0
+\frac{1}{n-m_n}\sum_{i=m_n+1}^{n}\widetilde\phi(S_i).
\]

The estimator is the pilot difference plus the average main-sample correction.

Conditional on the pilot reports, the selected release and correction are fixed. Why does their average remove the pilot’s error?

---

## Exact centering

Write \(\vartheta\) for a fixed pilot estimate and \(\xi\) for the true means. Let \(\phi_\vartheta\) be its selected correction.

The probability of pattern \(S\) is \(\omega_{\xi,\vartheta}(S)=\alpha_{\vartheta,S}h_S(\xi)\).

Two identities drive the construction:

- Pattern probabilities are affine in the means: \(h_S(\xi)=h_S(\vartheta)+g_S^\top(\xi-\vartheta)\).
- Minimizing over the common-mean direction gives \(I_\vartheta(\alpha_\vartheta)v(t_\vartheta)=J_\vartheta c\).

Consequently,

\[
\begin{aligned}
\sum_S\omega_{\xi,\vartheta}(S)\phi_\vartheta(S)
&=\frac1{J_\vartheta}
\left\{
\sum_S\alpha_{\vartheta,S}g_S^\top v(t_\vartheta)
+(\xi-\vartheta)^\top
 I_\vartheta(\alpha_\vartheta)v(t_\vartheta)
\right\}\\
&=c^\top(\xi-\vartheta).
\end{aligned}
\]

This computes the correction’s expected value. Channel normalization makes the first term zero; nuisance minimization makes the second term exactly the true-minus-pilot contrast.

Adding the pilot contrast therefore gives conditional expectation \(\tau\) for every pilot realization. Pilot accuracy is needed to approach optimal variance.

---

## Inference

@informal thm:pilot-attainment: With interior assignment and means, fixed positive privacy, a measurable strong-saddle selector, and a diverging pilot of vanishing fraction, our estimator has optimal asymptotic variance \(V^*\), consistent variance estimation, and pointwise valid Wald intervals.

\[
\sqrt n(\widehat\tau^*-\tau)
\rightsquigarrow N\!\left(0,V^*(\theta,p,\varepsilon)\right).
\]

The scaled error converges to a centered normal distribution with optimal variance. The same limiting law holds under fixed local shifts.

Let \(\widehat V^*\) be the empirical variance of the main-sample corrections. It consistently estimates \(V^*\). For error probability \(0<\gamma<1\), let \(z_{1-\gamma/2}\) be the standard-normal critical value:

\[
\left[
\widehat\tau^*-z_{1-\gamma/2}\sqrt{\widehat V^*/n},
\quad
\widehat\tau^*+z_{1-\gamma/2}\sqrt{\widehat V^*/n}
\right].
\]

This interval has coverage tending to \(1-\gamma\) at every fixed interior parameter, including points where the selected patterns change.

Exact centering, bounded corrections, and continuity of the optimized variance allow inference through these changes.

---

## Further results

- **Small releases:** at every interior design point with positive privacy, an optimal stationary release exists with at most five active labels.
- **Prevalence changes design:** at \(p=3/10\) and \(\varepsilon=\log 3\), minimum attaining cardinality is five near \((\mu_0,\mu_1)=(1/2,1/2)\), and three near \((1/10,1/10)\).
- **Prospective precision:** at \((p,\mu_0,\mu_1,\varepsilon)=(1/2,1/2,1/2,1)\), the specified custom-Laplace sample mean has \(V_{\mathrm{OA}}=34>V^*\); under the selector conditions, its asymptotic intervals are about \(2.69\) times as long at equal sample size, requiring about \(7.26\) times as many subjects at equal precision.

---

## Open questions

- Complete classification of optimal patterns and uniform coverage along sequences approaching pattern-change boundaries.
- A numerical reference solver with deterministic tie-breaking and independently checkable selection certificates.
- Boundary arm means, or assignment probabilities and privacy budgets changing with sample size.
- Broader outcome models and repeated releases from the same subject.
- Full-likelihood estimation under the specified custom-Laplace release.

---

## Takeaways

- For independently sampled randomized binary trials with known interior assignment, interior means, and fixed positive privacy, fourteen patterns give the best stationary contrast variance. With a measurable strong-saddle selector, this is also the exact regular local squared-error bound.
- Privacy places each output-density vector inside a scaled cube. Nonnegative corner mixtures, followed by removal of constant patterns, explain why fourteen patterns cover every release.
- A growing private pilot of vanishing fraction selects the release. An exactly centered main-sample correction delivers optimal variance and pointwise Wald inference.

---

## Appendix: Finite staircase oracle

The finite optimization equals the best stationary contrast variance over arbitrary measurable private outputs.

@formal thm:finite-oracle

---

## Appendix: Sequential local minimax efficiency

Every sequential private procedure obeys the local risk bound, and the selected private-pilot procedure attains it within the regular class.

@formal thm:sequential-minimax

---

## Appendix: Private pilot attainment

The selected pilot procedure supplies conditional unbiasedness, regular optimal variance, consistent variance estimation, and pointwise Wald coverage.

@formal thm:pilot-attainment

---

## Appendix: Local support and cardinality transition

At common assignment and privacy settings, certified open neighborhoods require respectively five and three outputs for stationary attainment.

@formal thm:support-transition
