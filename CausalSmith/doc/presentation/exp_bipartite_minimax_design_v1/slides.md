# Choosing Treatment Probabilities Under Interference

Use the links between intervention units and outcome units to allocate treatment chances and obtain conservative confidence intervals.

---

## Motivation

Treatment is assigned to one population; outcomes are measured in another.

An outcome may depend on several interventions. We want to compare treating its entire intervention neighborhood with treating none of it.

- Lu et al. (2025) establish estimation and inference under independent assignment with a common treatment probability.
- Shared interventions make outcome exposures dependent. A common probability ignores differences in those overlaps.
- Direct variance optimization requires unknown potential outcomes.
- Brennan et al. (2022) optimize clustering under bounded linear interference; clustering changes assignment dependence.

Can we use the known links to improve allocation while retaining independent assignment and the same expected treatment total?

---

## Key idea

Keep assignments independent, but choose a separate treatment probability for each intervention.

Let \(G_n\) denote the known graph of intervention–outcome links and \(p\) the vector of proposed treatment probabilities.

Replace unknown outcome-dependent variance terms with a **variance envelope**: an upper bound computed from \(G_n\), \(p\), and a bound on potential outcomes.

- Minimize this envelope before randomization; call a minimizing vector \(p_n^*(G_n)\).
- With a feasible budget and positive probability floor, this is a convex optimization problem.
- With bounded outcomes, bounded neighborhoods and overlap, uniform positivity, and nondegenerate variance, the optimized design supports normal approximation and conservative confidence intervals.

The same computable bound serves allocation and inference.

---

## Example

Suppose every outcome has exactly one intervention neighbor.

Let \(n\) count outcomes, \(s_k\) count outcomes linked to intervention \(k\), and \(\rho\) be the common treatment probability in the homogeneous vector \(p^{\mathrm{hom}}\).

The score \(g_k\) is the marginal change in one quarter of the envelope when probability \(k\) increases.

\[
g_k(G_n,p^{\mathrm{hom}})
=
n^{-1}s_k^2\left((1-\rho)^{-2}-\rho^{-2}\right).
\]

The squared incidence \(s_k^2\) counts ordered outcome pairs sharing intervention \(k\), including each outcome paired with itself.

When \(\rho\neq1/2\), unequal incidences produce unequal marginal scores. Moving probability from a higher-score intervention to a lower-score intervention reduces the envelope while preserving the budget, provided the common probability is interior.

---

## Model

The known graph \(G_n\) links \(m_n\) intervention units in \(I_n\) to \(n\) outcome units in \(O_n\). Outcome \(i\)'s intervention neighborhood is \(N_i(G_n)\).

Potential outcomes are fixed. For assignment vectors \(z,z'\), local interference requires

\[
z_{N_i(G_n)}=z'_{N_i(G_n)}
\quad\Longrightarrow\quad
Y_i\!\left(z_{N_i(G_n)}\right)=Y_i\!\left(z'_{N_i(G_n)}\right).
\]

Thus assignments outside the neighborhood cannot affect outcome \(i\); interference inside it is unrestricted.

Let \(Y_i^1,Y_i^0\) be its all-treated and all-control outcomes. Their population averages \(\mu_1,\mu_0\) define the target \(\tau_n=\mu_1-\mu_0\).

Intervention \(k\) is independently treated with probability \(p_k\). The target-exposure probabilities are

\[
\pi_i^1(p)=\prod_{k\in N_i(G_n)}p_k,
\qquad
\pi_i^0(p)=\prod_{k\in N_i(G_n)}(1-p_k),
\]

Each product is the chance of observing one target outcome. Larger neighborhoods can make both exposures rare.

---

## Feasible designs

Reallocate treatment chances while preserving capacity and allowing both assignment states.

\[
\mathcal P_{n,B_n,\epsilon}
=
\left\{
p\in[0,1]^{m_n}:
\epsilon\le p_k\le 1-\epsilon\ \text{for every } k\in I_n,
\quad
\sum_{k\in I_n}p_k=B_n
\right\}.
\]

This set contains probability vectors satisfying two restrictions:

- \(B_n\) fixes the expected number of treated interventions.
- The floor \(0<\epsilon<1/2\) keeps probabilities away from zero and one.

Feasibility requires \(m_n\epsilon\le B_n\le m_n(1-\epsilon)\).

The homogeneous benchmark assigns every intervention probability \(\rho=B_n/m_n\). Heterogeneous probabilities redistribute the same expected treatment total.

---

## Estimator

Let \(Z\) be the realized assignment vector. Indicators \(T_i(Z)\) and \(C_i(Z)\) record all-treated and all-control neighborhood exposure.

Inverse-probability weighting corrects unequal chances of observing the target outcomes. Its weighted exposure counts are

\[
D_1(p,Z)=\sum_{i\in O_n}\frac{T_i(Z)}{\pi_i^1(p)},
\qquad
D_0(p,Z)=\sum_{i\in O_n}\frac{C_i(Z)}{\pi_i^0(p)}.
\]

The Hájek estimator subtracts separately normalized weighted outcome means:

\[
\widehat\tau_H(p)
=
\mathbf 1\{D_1(p,Z)>0\}
\frac{\displaystyle\sum_{i\in O_n}\frac{T_i(Z)Y_i^{obs}}{\pi_i^1(p)}}{D_1(p,Z)}
-
\mathbf 1\{D_0(p,Z)>0\}
\frac{\displaystyle\sum_{i\in O_n}\frac{C_i(Z)Y_i^{obs}}{\pi_i^0(p)}}{D_0(p,Z)}.
\]

Here \(Y_i^{obs}\) is the observed outcome; the indicators use each ratio when its weighted count is positive.

Normalization reduces sensitivity to random exposure counts. Aronow and Samii (2017) provide the general exposure-weighting framework.

---

## Linearization

Random denominators make the estimator a difference of ratios. Its first-order contribution from outcome \(i\) is

\[
\eta_i(p,Z)
=
\left(\frac{T_i(Z)}{\pi_i^1(p)}-1\right)(Y_i^1-\mu_1)
-
\left(\frac{C_i(Z)}{\pi_i^0(p)}-1\right)(Y_i^0-\mu_0).
\]

This centered contribution combines exposure fluctuations with deviations from the two population means.

The variance scale is

\[
\sigma^2_{G_n,D,p}(Y)
=
n\,\operatorname{Var}_D\!\left(
\frac{1}{n}\sum_{i\in O_n}\eta_i(p,Z)
\right).
\]

Here \(D\) is the randomization law; for independent Bernoulli assignment with vector \(p\), abbreviate this as \(\sigma^2_{G_n,p}(Y)\).

The average of the \(\eta_i\)'s approximates estimation error. Its variance still depends on unobserved outcome deviations.

---

## Assumptions

For growing populations, retain local interference and independent assignment from the model. At every \(n\), use a feasible envelope-minimizing vector \(p_n^*(G_n)\).

- **Bounded outcomes:** \(\lvert Y_i^1\rvert\leq1\) and \(\lvert Y_i^0\rvert\leq1\).
- **Bounded neighborhoods:** \(d_i=|N_i(G_n)|\leq\bar d\), for a fixed bound \(\bar d\).
- **Bounded overlap:** each neighborhood intersects at most \(\bar D\) outcome neighborhoods, for a fixed bound \(\bar D\). Denote the maximum such count by \(\Delta_n\).
- **Uniform positivity:** the probability floors \(\epsilon_n\) remain above a fixed \(\epsilon_0>0\).
- **Nondegenerate variance:** \(\liminf_{n\to\infty}\sigma^2_{G_n,p_n^*(G_n)}(Y)>0\).

In the singleton example, \(d_i=1\). Uniformly bounded incidences \(s_k\) also bound the number of overlapping outcome neighborhoods.

---

## Main result

@informal thm:hetero-clt: Under local interference, independent assignment, bounded outcomes, bounded neighborhoods and overlap, uniform positivity, feasible envelope optimality, and nondegenerate variance, the Hájek estimator is asymptotically normal.

\[
\Pr_{D_n}\!\left(
\frac{\sqrt n\bigl\{\widehat\tau_H(p_n^*(G_n))-\tau_n\bigr\}}
{\sqrt{\sigma^2_{G_n,p_n^*(G_n)}(Y)}}\le s
\right)
\longrightarrow
\Pr\!\left\{N(0,1)\le s\right\}.
\]

Here \(D_n\) is the optimized independent randomization law, \(s\) any real cutoff, and \(N(0,1)\) the standard normal distribution.

The standardized estimation error becomes normal under the assumptions just given.

In the singleton example, bounded \(s_k\), bounded outcomes, uniform positivity, and positive limiting variance deliver this conclusion for the feasible optimal design.

How can we choose probabilities and construct an interval when the variance contains unknown outcomes?

---

## Shared assignments

Let \(S_{ij}(G_n)=N_i(G_n)\cap N_j(G_n)\), the interventions shared by outcomes \(i,j\).

Nonshared assignment factors cancel from normalized joint-exposure probabilities. Define the three covariance loads:

- Treated: \(r_{ij}^1(G_n,p)=\prod_{k\in S_{ij}(G_n)}p_k^{-1}-1\).
- Control: \(r_{ij}^0(G_n,p)=\prod_{k\in S_{ij}(G_n)}(1-p_k)^{-1}-1\).
- Cross-exposure: \(r_{ij}^{10}(G_n)=\mathbf1\{S_{ij}(G_n)\neq\varnothing\}\).

For disjoint neighborhoods, all three are zero. With overlap, treated and control exposures cannot occur together; subtracting the control contribution produces the positive cross-load below.

Under independent assignment, interior probabilities, and bounded outcomes,

\[
\mathbb E_p\!\left[\eta_i(p,Z)\eta_j(p,Z)\right]
=
r_{ij}^1(G_n,p)(Y_i^1-\mu_1)(Y_j^1-\mu_1)
+r_{ij}^0(G_n,p)(Y_i^0-\mu_0)(Y_j^0-\mu_0)
+r_{ij}^{10}(G_n)\!\left\{(Y_i^1-\mu_1)(Y_j^0-\mu_0)+(Y_i^0-\mu_0)(Y_j^1-\mu_1)\right\}.
\]

Expectation \(\mathbb E_p\) is over assignments. This covariance separates computable exposure dependence from unknown outcome deviations.

---

## Variance envelope

Bounded target outcomes imply that each deviation from its population mean has absolute value at most two. Each product of deviations therefore has absolute value at most four.

Replacing the unknown covariance factors by these bounds gives

\[
V_{\mathrm{env}}(G_n,p)
=
\frac{4}{n}\sum_{i,j\in O_n}
\left\{
r_{ij}^1(G_n,p)
+
r_{ij}^0(G_n,p)
+
2r_{ij}^{10}(G_n)
\right\}.
\]

The sum runs over ordered outcome pairs. The factor two counts the two cross-exposure products.

@informal thm:hetero-envelope: Under independent Bernoulli assignment with \(0<p_k<1\) and \(\lvert Y_i^1\rvert,\lvert Y_i^0\rvert\le1\), the graph envelope upper-bounds the variance scale of the Hájek linearization.

\[
\sigma^2_{G_n,p}(Y)\le V_{\mathrm{env}}(G_n,p).
\]

The right side requires only the graph and proposed probabilities. It can be evaluated before observing outcomes.

---

## Optimal allocation

Choose the feasible vector with the smallest computable variance bound:

\[
p_n^*(G_n)
\in
\operatorname{argmin}_{p\in\mathcal P_{n,B_n,\epsilon}}
V_{\mathrm{env}}(G_n,p).
\]

The minimizer preserves the expected treatment budget and respects both probability bounds.

@informal thm:convex-design: If \(0<\epsilon<1/2\) and \(m_n\epsilon\le B_n\le m_n(1-\epsilon)\), the feasible set is nonempty, the envelope is convex, and a global minimizer exists.

The score \(g_k(G_n,p)\) is the derivative of one quarter of the envelope with respect to \(p_k\).

- At an interior optimum, all intervention scores are equal.
- Unequal scores permit a budget-preserving improvement: decrease a higher-score probability and increase a lower-score probability.
- At a probability bound, the corresponding direction may be unavailable.

Because each load uses a shared neighborhood, allocation depends on the full overlap pattern.

---

## Example revisited

For two outcomes sharing their sole intervention \(k\), the loads are \(r_{ij}^1=p_k^{-1}-1\), \(r_{ij}^0=(1-p_k)^{-1}-1\), and \(r_{ij}^{10}=1\).

Their envelope contribution inside the pairwise sum is \(p_k^{-1}+(1-p_k)^{-1}\). Outcomes linked to different interventions contribute zero.

Thus each intervention's contribution is repeated \(s_k^2\) times, explaining the squared incidence in its marginal score.

@informal thm:heterogeneity-separation: If \(m_n>0\), \(0<\epsilon<1/2\), \(\epsilon<\rho=B_n/m_n<1-\epsilon\), \(\rho\neq1/2\), and homogeneous-point scores differ, the optimal envelope is strictly smaller than under homogeneous assignment.

With unequal \(s_k\), these conditions imply

\[
p_n^*(G_n)\neq p^{\mathrm{hom}},\qquad
V_{\mathrm{env}}(G_n,p_n^*(G_n))<V_{\mathrm{env}}(G_n,p^{\mathrm{hom}}),
\]

When \(\rho<1/2\), a reducing transfer favors higher-incidence interventions; when \(\rho>1/2\), it favors lower-incidence interventions.

This guarantees improvement in the envelope, not necessarily in actual variance.

---

## Normal approximation

The inference assumptions control both the size and dependence of the linearized contributions.

- Bounded neighborhoods and uniform positivity bound inverse-exposure weights. Bounded outcomes then bound every centered \(\eta_i\).
- Contributions using disjoint intervention sets are independent. Bounded overlap limits how many contributions can depend on any one contribution.
- Nondegenerate variance makes the variance of their sum grow at least proportionally to \(n\).

A central limit theorem for bounded contributions with bounded dependence therefore gives a normal approximation to their standardized sum.

The same controls make the ratio-estimator remainder negligible. For every \(\delta>0\),

\[
\Pr_{D_n}\!\left(
\left|
\sqrt n\bigl\{\widehat\tau_H(p_n^*(G_n))-\tau_n\bigr\}
-n^{-1/2}\sum_{i\in O_n}\eta_i(p_n^*(G_n),Z)
\right|\ge\delta
\right)\longrightarrow 0,
\]

This says that the scaled estimation error and the scaled linearized sum become indistinguishable, transferring the normal approximation to the Hájek estimator.

---

## Conservative inference

Use the envelope as the variance scale: \(\widehat V_{\mathrm{cons}}(G_n,p)=V_{\mathrm{env}}(G_n,p)\).

Let \(\alpha_{\mathrm{cov}}\in(0,1)\) be the desired noncoverage probability and \(z_{1-\alpha_{\mathrm{cov}}/2}\) its standard-normal critical value.

@informal thm:postdesign-wald: Under the model and inference assumptions, feasible envelope optimality, and the standard-normal critical value, the graph-only Wald interval has asymptotic coverage at least \(1-\alpha_{\mathrm{cov}}\).

\[
1-\alpha_{\mathrm{cov}}
\le
\liminf_{n\to\infty}
\Pr_{p_n}\!\left(
\left|\tau_n-\widehat\tau_H(p_n)\right|
\le
z_{1-\alpha_{\mathrm{cov}}/2}
\sqrt{\frac{\widehat V_{\mathrm{cons}}(G_n,p_n)}{n}}
\right).
\]

Here \(p_n=p_n^*(G_n)\), and probability is over its independent assignments. The expression inside the probability defines the interval around the estimate.

The normal approximation uses the true variance scale; the interval uses an upper bound. That is why coverage is at least nominal.

---

## Open questions

- How closely does envelope reduction track actual variance and coverage? Sparse implementations, computation benchmarks, and simulations remain to be developed.
- Can pre-treatment outcomes or credible structural restrictions support an outcome-informed design criterion?
- How should probability design and inference change under clustered assignments or growing neighborhood and overlap sizes?

---

## Takeaways

- Exposure weighting estimates the population all-treated-versus-all-control contrast. Heterogeneous probabilities allocate the chances of observing those exposures.
- Shared interventions determine covariance loads. Bounded outcomes turn those loads into a computable envelope with a convex, budget-constrained optimum.
- Under bounded local dependence, uniform positivity, and nondegenerate variance, the optimized design supports normal approximation and conservative graph-only confidence intervals.

---

## Appendix: Convex feasible design

A feasible positivity-constrained budget admits a global envelope minimizer, characterized by marginal scores and probability-bound conditions.

@formal thm:convex-design

---

## Appendix: Heterogeneous Hájek central limit theorem

Under bounded local dependence and the full regularity conditions, the optimal-design Hájek estimator admits a first-order approximation and a normal limit.

@formal thm:hetero-clt

---

## Appendix: Post-design Wald coverage

The graph-only variance scale bounds the true scale and yields asymptotic coverage at least the nominal level.

@formal thm:postdesign-wald

---

## Appendix: Surrogate approximation certificate

Bounded outcome degree and positivity control the additive surrogate's envelope loss relative to the exact optimum.

@formal thm:surrogate-certificate
