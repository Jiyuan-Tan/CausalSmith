# Recovering Latent Causes From One Intervention Each

One experiment per hidden variable can reveal the causal graph and recover the variables from a nonlinear mixture.

---

## Motivation

We observe a mixture of hidden causal variables and want to recover both the variables and their directed acyclic graph (DAG).

- Ordinary conditional-independence discovery starts with the causal variables already measured.
- Here, an unknown nonlinear observation map mixes those variables together.
- We observe an observational law \(P^0\) and intervention laws \(P^1,\ldots,P^n\): one perfect intervention per hidden variable, with unknown targets.
- A perfect intervention replaces its target’s conditional distribution by a distribution independent of its parents.

von Kügelgen et al. (2023) establish identification with one intervention per variable in two dimensions; their arbitrary-dimensional result uses two paired interventions per variable. Wendong et al. (2023) use one intervention per variable with the graph and targets supplied.

Can one intervention per variable recover coordinates, targets and the graph in arbitrary dimension?

---

## Key idea

Use each environment’s likelihood ratio as an observable scalar score.

\[
R_i=\frac{dP^i}{dP^0},
\qquad
L_i=\log R_i,
\qquad i\in[n],
\]

Here \(n\) is the number of hidden variables and \([n]=\{1,\ldots,n\}\). The ratio \(R_i\) measures relative likelihood in environment \(i\) versus observation; \(L_i\) is its logarithm.

Compare the distribution of the **same score \(R_i\)** in environments \(j\) and \(0\). Call their Gaussian maximum mean discrepancy (MMD) \(D_{ji}\).

**\(D_{ji}\) is nonnegative and equals zero exactly when those two scalar distributions agree.**

Changing score distributions reveal ancestral order. Conditional percentiles along that order recover individual variables; observational conditional independence then selects their parents.

This succeeds under smooth positive cube support, shared invertible mixing, active parents, fixed score monotonicity signs and separation of ancestral covers. That separation condition is generic within each fixed-sign class.

---

## Example

All three variables take values in \([0,1]\). Let \(1\to2\), with variable \(3\) isolated, identity observation map and environment \(i\) targeting variable \(i\).

Write \(x=V_1\), \(y=V_2\) and \(h(z)=2z-1\). Variables \(1\) and \(3\) have uniform observational densities.

\[
p_2(y\mid x)=1+0.1h(x)h(y),
\]

The child’s density changes with its parent.

\[
q_i(z)=\frac{4\exp(4z)}{\exp(4)-1},
\]

Every intervention replaces its target’s mechanism by this normalized density, which favors larger values.

Although \(R_2=q_2(y)/p_2(y\mid x)\) depends on both variables, intervention \(1\) changes its distribution.

@informal prop:sparse-witness-certificate: In this identity-mixing, identity-target example, the smooth positive fixed-sign construction satisfies \(\frac{5}{100000000}<D_{12}(W^{\mathrm{sp}})\).

Here \(W^{\mathrm{sp}}\) denotes these environment laws. Positive discrepancy reveals that variable \(1\) precedes variable \(2\).

---

## Model

The hidden vector \(V=(V_1,\ldots,V_n)\) lies in \([0,1]^n\). We observe \(X=f(V)\), with the same unknown invertible map \(f\) in every environment.

The observational law factors over the latent DAG \(G\):

\[
P^0
=
f_\#\bigl(p^0(v)\,dv\bigr),
\qquad
p^0(v)=\prod_{i=1}^n p_i(v_i\mid v_{\operatorname{pa}_G(i)}),
\]

Here \(p_i\) is variable \(i\)’s conditional density, \(\operatorname{pa}_G(i)\) is its parent set, and \(f_\#\) means observing a latent draw through \(f\).

Environment \(e\) targets variable \(\pi(e)\), where \(\pi\) is an unknown permutation:

\[
P^e
=
f_\#\bigl(p^{\pi(e)}(v)\,dv\bigr),
\qquad
p^{\pi(e)}(v)
=
q_{\pi(e)}(v_{\pi(e)})
\prod_{\ell\ne \pi(e)}
p_\ell(v_\ell\mid v_{\operatorname{pa}_G(\ell)}).
\]

Only the target’s factor changes, to its parent-independent intervention density \(q_{\pi(e)}\).

---

## Assumptions

- **Smooth positive support:** each \(p_i\) and \(q_i\) is a positive normalized \(C^3\) density on its closed cube. All environments overlap.
- **Shared mixing:** \(f\) and its inverse are \(C^2\); measurement changes cannot explain differences between environments.
- **Causal minimality:** each parent changes its child’s observational conditional distribution after conditioning on the other parents.
- **Fixed ratio signs:** with parents fixed, each target’s log-ratio is strictly monotone in that target.

\[
s_i\,\partial_{v_i}\log\{q_i(v_i)/p_i(v_i\mid v_{\operatorname{pa}_G(i)})\}>0
\]

The prescribed sign \(s_i\in\{-1,1\}\) specifies decreasing or increasing behavior throughout the cube.

In our example, all signs are positive: fixing \(x\), the score for variable \(2\) increases with \(y\). Monotonicity will let a score percentile become a variable percentile.

---

## Main result

An **ancestral cover** is an ancestor–descendant pair with no variable between them in the ancestor order.

**Cover separation:** require \(D_{ji}>0\) whenever target \(\pi(j)\) ancestrally covers target \(\pi(i)\).

@informal thm:exact-ratio-decoder: Under smooth positive cube support, shared \(C^2\) invertible mixing, causal minimality, one perfect intervention per node, fixed ratio signs and cover separation, coordinates, targets and the DAG are identified up to separate \(C^2\) changes and relabeling.

Form the observable graph

\[
H_D=\{j\to i:j\ne i\text{ and }D_{ji}>0\}.
\]

An arrow means intervention \(j\) changes score \(i\)’s distribution. Let \(G^\pi\) be the latent DAG written in environment labels.

\[
\operatorname{TC}(H_D)=\operatorname{TC}(G^\pi).
\]

Transitive closure, \(\operatorname{TC}\), adds an arrow for every directed path. Thus observable score comparisons recover exactly the ancestor order; subsequent rank and pruning steps recover coordinates and direct parents.

---

## Removing the observation map

The shared observation map cancels from the likelihood ratio:

\[
R_e(f(v))
=
\frac{q_{\pi(e)}(v_{\pi(e)})}
{p_{\pi(e)}(v_{\pi(e)}\mid v_{\operatorname{pa}_G(\pi(e))})}.
\]

The numerator is the target’s intervention density; the denominator is its original conditional density.

The common change-of-variables factor and every unchanged mechanism cancel. We therefore obtain a function of the target and its parents **without first recovering the latent coordinates**.

In our example, this gives \(R_2=q_2(y)/p_2(y\mid x)\).

The score still mixes the child with its parents. What can comparing its distributions reveal?

---

## Ancestral order

For \(j\ne i\), compare score \(R_i\)’s distribution under intervention \(j\) with its observational distribution.

- If \(\pi(j)\) is not an ancestor of \(\pi(i)\), intervention \(j\) leaves the joint distribution of target \(\pi(i)\) and its parents unchanged.
- The ratio depends only on those variables, so its distribution also stays unchanged: \(D_{ji}=0\).
- Every detected arrow consequently points from an ancestor to a descendant.
- Cover separation supplies the links needed to recover all ancestry through paths.

A **topological order** places each arrow’s source before its destination. Since the ancestor relations agree, every topological order of \(H_D\) respects the latent DAG.

In our example, \(D_{12}>0\) puts variable \(1\) before variable \(2\); isolated variable \(3\) can appear anywhere.

---

## Conditioning on predecessors

A score is not yet an individual coordinate: its denominator depends on parents. An unconditional percentile generally retains that dependence.

Choose a recovered topological order. Let \(B_i\) contain all environment labels preceding \(i\), and \(L_{B_i}\) their log-score vector.

- The first score depends only on its own variable and is strictly monotone.
- Each later score depends on its own variable and earlier parents.
- Once earlier variables are determined, strict monotonicity uniquely determines the next variable from its score.

The predecessor score vector therefore determines all predecessor latent variables. This successive inversion is why the ordering matters.

**Conditioning on \(L_{B_i}\) fixes every parent of target \(\pi(i)\), using observable quantities.**

In our example, conditioning on \(L_1\) fixes \(V_1=x\).

---

## Conditional ranks

Let \(C_i\) be the conditional cumulative distribution function of \(L_i\) given \(L_{B_i}\), computed **under its own intervention law \(P^i\)**.

\[
U_i=C_i(L_i\mid L_{B_i}).
\]

The recovered coordinate \(U_i\) is the current score’s percentile among intervention draws with the same predecessor scores.

Under \(P^i\), the target has density \(q_{\pi(i)}\), independently of its predecessors. Conditioning fixes its parents; monotonicity then converts the score percentile into a target percentile:

\[
U_i(f(v))=
\begin{cases}
Q_{\pi(i)}(v_{\pi(i)}), & s_{\pi(i)}=1,\\
1-Q_{\pi(i)}(v_{\pi(i)}), & s_{\pi(i)}=-1.
\end{cases}
\]

Here \(Q_a(z)=\int_0^z q_a(u)\,du\) is variable \(a\)’s intervention distribution function.

The parent dependence disappears, and environment \(i\) is aligned with coordinate \(U_i\).

In our example, \(U_2=Q_2(V_2)\): conditioning fixes \(x\), and ranking under intervention \(2\) removes \(x\) from the recovered coordinate.

---

## Parent pruning

The score graph identifies ancestors. Observational conditional independence selects the direct parents.

For coordinate \(i\), search predecessor subsets \(A\subseteq B_i\) satisfying

\[
U_i\mathbin{\perp\!\!\!\perp}_{P^0}U_{B_i\setminus A}\mid U_A.
\]

Here \(U_A\) denotes the coordinates indexed by \(A\). The condition says they explain all remaining dependence between \(U_i\) and its predecessors under observation.

- The model’s factorization makes the true parent set satisfy this condition.
- Positivity and causal minimality make it the unique inclusion-minimal satisfying set.
- Separate invertible coordinate changes preserve conditional independence.

In our example, variable \(1\) remains a parent of variable \(2\); isolated variable \(3\) is removed if it precedes variable \(2\).

Within the same structural class and prescribed signs, equal environment laws imply separate \(C^2\) coordinate changes and simultaneous relabeling of graph and targets.

---

## Cancellation

Causal minimality alone does not guarantee score-law separation.

Keep the example’s graph, interventions and uniform root densities, but replace the child mechanism by

\[
h(y)=2y-1,
\qquad
H(x)=\frac{\exp(4x)-1}{\exp(4)-1}-x,
\qquad
p_2(y\mid x)=1+0.1H(x)h(y).
\]

The function \(H\) replaces the original affine parent effect. The edge remains active, and smooth positivity and fixed signs still hold.

Yet the entire distribution of \(R_2\) agrees between environments \(0\) and \(1\):

\[
D_{12}(W^{\mathrm{can}})=0.
\]

Here \(W^{\mathrm{can}}\) denotes these modified environment laws.

Cover separation is therefore an additional condition. Why can arbitrarily small admissible changes remove such cancellation?

---

## A separating endpoint

Fix any ancestral cover \(j\to i\), using latent labels. Every cover is a direct edge.

Isolate that edge in a comparison mechanism:

\[
p_\ell^{\mathrm{sp}}(v)=
\begin{cases}
1+\dfrac{1}{10}\,h(\operatorname{reflect}(s_j,v_j))\,h(\operatorname{reflect}(s_i,v_i)), & \ell=i,\\
1, & \ell\ne i,
\end{cases}
\qquad
q_\ell^{\mathrm{sp}}(z)=
\dfrac{4\exp(4\,\operatorname{reflect}(s_\ell,z))}{\exp(4)-1},
\]

The superscript \(\mathrm{sp}\) denotes this sparse endpoint. Recall \(h(z)=2z-1\); \(\operatorname{reflect}(s,z)\) is \(z\) for positive sign and \(1-z\) for negative sign.

All other observational mechanisms are uniform. Integrating out their coordinates leaves exactly the example’s two-variable construction, with reflections matching the prescribed signs.

Intervention \(j\) replaces the uniform parent density by the exponential tilt. This changes the weighting of the reciprocal child density in the score’s second moment.

The example’s certificate gives observational minus intervened second moment greater than \(\frac{3}{10000}\). Thus the endpoint separates this arbitrary cover.

---

## Generic separation

A **fixed-sign stratum** is the class of mechanisms with a fixed DAG and signs satisfying smooth positivity, causal minimality and strict score monotonicity.

Move from any original mechanism toward the edge-specific endpoint:

\[
p_\ell^t(v)=(1-t)p_\ell(v)+t\,p_\ell^{\mathrm{sp}}(v),
\qquad
q_\ell^t(z)=(1-t)q_\ell(z)+t\,q_\ell^{\mathrm{sp}}(z),
\qquad \ell\in[n].
\]

Here \(t\) is the mixing weight.

- Convex mixtures preserve normalization, positivity and smoothness.
- For sufficiently small \(t\), strict derivative signs persist, and each original active parent remains active. These nearby mechanisms stay in the original stratum, even though the endpoint suppresses other edges.
- The difference in score second moments is analytic in \(t\) and nonzero at the endpoint. Its zeros are isolated, so arbitrarily small admissible changes separate the chosen edge.
- Separation is stable under small changes. Intersecting the finitely many open dense edge-separation sets separates every cover.

@informal thm:generic-cover-separation: For every finite DAG, target permutation and nonempty fixed-sign stratum, mechanisms separating every ancestral cover form an open dense set in the relative \(C^2\) topology.

“Open” means separation survives small admissible changes; “dense” means separating mechanisms approximate every admissible mechanism. Closeness controls densities and their first two derivatives.

---

## Discrepancy scale

Gaussian MMD compares average features of the scalar scores. Following the kernel comparison of Gretton et al. (2012), use unit-length features \(\Phi(r)\) whose inner products equal \(k(a,b)=\exp(-(a-b)^2)\).

For environment family \(W\), the population discrepancy is

\[
D_{ji}(W)
=
\left\|
\int \Phi(r)\,d\bigl((R_i)_\# P^0\bigr)(r)
-
\int \Phi(r)\,d\bigl((R_i)_\# P^j\bigr)(r)
\right\|_H .
\]

Here \((R_i)_\#P^e\) is score \(i\)’s distribution in environment \(e\); \(H\) is the feature space. This is **unsquared** MMD.

Sample splitting fits \(\widehat R_i\) on training data and compares it on independent evaluation data:

\[
\widehat D_{ji}(\omega;U)
=
\left\|
\frac{1}{N_j}\sum_{r=1}^{N_j}\Phi\!\left(\widehat R_i(X^{(j)}_r(\omega))\right)
-
\frac{1}{N_0}\sum_{r=1}^{N_0}\Phi\!\left(\widehat R_i(X^{(0)}_r(\omega))\right)
\right\|_{\mathcal H}.
\]

Here \(X^{(e)}_r\) is evaluation draw \(r\) in environment \(e\), \(N_e\) its sample size, \(\omega\) the sample realization, and \(U\) specifies the feature map. The norm again gives unsquared MMD, with each environment normalized by its own sample size.

---

## Confidence edges

Assume independent observations within each environment and independence of the complete training and evaluation folds.

With probability at least \(1-\eta\), require every fitted ratio’s integrated absolute error under every environment law to be at most \(a_N(\eta)\), simultaneously.

The confidence radius on the unsquared MMD scale is

\[
\varepsilon_N(\alpha,\eta)
=
2\sqrt 2\,a_N(\eta)
+
\frac{2\{1+\sqrt{2\log(n(n+1)/\alpha)}\}}
{\sqrt{\min_{0\le e\le n}N_e}} .
\]

Here \(\alpha,\eta\in(0,1)\) are evaluation and first-stage failure levels. The first term carries ratio-estimation error; the second controls simultaneous evaluation noise.

Select arrows with positive lower confidence bounds:

\[
\widehat H
=
\left\{
j\to i:
\widehat D_{ji}-\varepsilon_N(\alpha,\eta)>0
\right\}.
\]

The graph \(\widehat H\) records the selected ancestral discoveries.

@informal thm:simultaneous-confidence-edges: In the positive smooth shared-mixing perfect-intervention model with independent sample splitting and simultaneous first-stage \(L^1\) accuracy of probability at least \(1-\eta\), all selected arrows are ancestral with probability at least \(1-\alpha-\eta\).

If every cover also satisfies \(2\varepsilon_N(\alpha,\eta)<D_{ji}\), the selected graph recovers the entire ancestor order by transitive closure with that same probability guarantee.

---

## Takeaways

- One perfect intervention per scalar variable identifies coordinates, targets and the DAG under smooth positive cube support, shared invertible mixing, causal minimality, fixed ratio signs and cover separation. Separation is open dense within each nonempty fixed-sign stratum.
- Likelihood ratios cancel the observation map; their changing laws reveal order. Conditioning fixes parents, and percentiles under each target’s own intervention recover individual coordinates. Observational conditional independence then selects direct parents.
- Independent evaluation data turn fitted-ratio comparisons into simultaneous confidence edges when first-stage ratio error is controlled; covers exceeding twice the confidence radius yield full ancestor-order recovery.

---

## Appendix: Generic cover separation

Ancestral-cover separation is open and dense within every nonempty fixed-sign mechanism stratum.

@formal thm:generic-cover-separation

---

## Appendix: Exact ratio decoding

The environment laws recover ancestor relations, latent coordinates, intervention alignment and exact parents, with uniqueness up to componentwise smooth changes and relabeling.

@formal thm:exact-ratio-decoder

---

## Appendix: Simultaneous confidence edges

A simultaneous first-stage ratio-error guarantee yields familywise-valid ancestral discoveries and order recovery when every cover clears the confidence radius.

@formal thm:simultaneous-confidence-edges
