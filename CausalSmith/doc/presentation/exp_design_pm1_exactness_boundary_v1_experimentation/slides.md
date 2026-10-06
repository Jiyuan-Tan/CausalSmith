# When Covariance Designs Can Be Randomized

An optimized covariance may ask for assignments no experiment can produce; community-size parity tells us when that happens and how to build the best feasible randomization.

---

## Motivation

With interference, one unit’s treatment can affect other units. Choosing correlated assignments can therefore improve experimental design.

- Ugander et al. (2013) use graph-cluster randomization to manage network exposure.
- Thiyageswaran et al. (2026), our closest predecessor, optimize assignment covariance to trade off interference, homophily, and robustness.

Let \(Z\) be the vector of treatment signs, \(+1\) or \(-1\), and \(P\) its randomization law. An actual design produces

\[
X(P)=\mathbb E_P[ZZ^\top].
\]

This matrix records the second moments of treatment assignments.

The standard relaxation optimizes over positive semidefinite matrices with diagonal entries one. Those conditions permit matrices that no binary assignment law can generate.

When does the covariance optimum describe an actual randomization?

---

## Key idea

Consider two equal communities, each containing \(m\ge2\) units, with stronger interactions within communities: \(a>b>0\). The criterion weights \(r\) and \(\kappa\) are nonnegative.

Symmetry reduces the covariance problem to allocating variance among three directions.

Binary assignments add one restriction:

- Even communities can have treatment-sign sum zero.
- Odd communities must retain some variance in their community totals.

That restriction completely characterizes feasibility in this model. We can construct a randomization for every covariance that passes it.

The result is an exact procedure: optimize the covariance, check parity, and correct the allocation if necessary. Even community size always gives zero loss.

---

## Example

Take two communities of three units each, with within-community intensity \(a=2\), across-community intensity \(b=1\), tradeoff weight \(r=8\), and norm weight \(\kappa=0\).

The relaxed optimum asks for zero treatment-sign sum in each community. Three signs cannot sum to zero.

The relaxed criterion value is \(34\); the best feasible randomization has value \(308/9\).

Writing \(\Delta_m^{\pm}(r,\kappa)\) for feasible-minus-relaxed loss,

\[
\Delta_3^{\pm}(8,0)=\tfrac{308}{9}-34=\tfrac29\approx0.222,
\]

This is the cost of requiring an actual assignment law. We will recover both the calculation and the randomization that attains it.

---

## Model

The \(n=2m\) units are fixed. Only their treatment assignment is random. Communities \(A_m\) and \(B_m\) each contain \(m\) units.

For distinct units in the same community, the interaction weight is

\[
W_{ij}=\frac{a}{m};
\]

for units in opposite communities, it is

\[
W_{ij}=\frac{b}{m};
\]

and \(W_{ii}=0\). Homophily means \(a>b>0\): stronger interaction within communities.

Require sign symmetry:

\[
P(Z=z)=P(Z=-z).
\]

Here \(z\) is an assignment realization. Reversing every treatment label leaves its probability unchanged, so each unit is treated with probability one-half. The treated count may vary across realizations.

---

## Design criterion

Let \(L_m\) be the graph Laplacian: weighted degrees on its diagonal and \(-W_{ij}\) off the diagonal. Its pseudoinverse \(L_m^\dagger\) inverts the nonzero graph directions.

For \(r,\kappa\ge0\), minimize

\[
F_{r,\kappa}(X)
=
\operatorname{tr}(L_m X)
+
r\,\operatorname{tr}(L_m^\dagger X)
+
\kappa \|X\|_{S_2}
+
\operatorname{tr}(J_n X).
\]

- The first term penalizes treatment disagreement across strongly connected units.
- The pseudoinverse term weights graph directions with smaller Laplacian eigenvalues more heavily; \(r\) controls that tradeoff.
- \(\|X\|_{S_2}\) is the Frobenius norm, the square root of the sum of squared entries. Here robustness is a chosen norm regularization criterion: \(\kappa\) penalizes concentrated covariance, conditional on the chosen graph.
- \(J_n\) is the all-ones matrix. Its term penalizes the expected squared total treatment-sign sum.

Under sign symmetry, \(X(P)\) is also the assignment covariance.

---

## Symmetry reduction

Average over permutations within each community and over swapping the two communities.

The graph and criterion are unchanged by these relabelings. Convexity means averaging cannot increase the objective.

@informal prop:symmetry-reduction: For \(m\ge2\), \(a>b>0\), and \(r,\kappa\ge0\), averaging within communities and over community swaps preserves both optimal values: the covariance relaxation and the optimization over sign-symmetric assignment laws.

The resulting matrix \(X(u,v)\) has only two off-diagonal entries:

- \(u\): covariance between distinct units in the same community.
- \(v\): covariance between units in opposite communities.

The assignment law can likewise treat units within each community exchangeably: permuting their labels does not change its distribution.

---

## Three variance directions

A symmetric covariance has three kinds of eigenvalues, measuring variance along orthonormal directions:

\[
q=2(m-1),\qquad
x=1-u,\qquad
y=1+(m-1)u-mv,\qquad
z_{\mathrm{sp}}=1+(m-1)u+mv .
\]

- \(x\): variance in contrasts among units within communities; there are \(q\) such directions.
- \(y\): variance in the contrast between communities.
- \(z_{\mathrm{sp}}\): variance in the aggregate direction shared by all units.

The subscript distinguishes \(z_{\mathrm{sp}}\) from an assignment realization \(z\).

Positive semidefiniteness becomes nonnegative variance. The relaxed feasible set is

\[
T_m=\{(x,y,z_{\mathrm{sp}}):x,y,z_{\mathrm{sp}}\ge0,\ qx+y+z_{\mathrm{sp}}=2m\},
\]

This triangle allocates a fixed total variance of \(2m\), because every treatment sign has variance one.

---

## Direction costs

The reduced coefficients are

\[
c_x=q\left((a+b)+\frac{r}{a+b}\right),\qquad
c_y=2b+\frac{r}{2b},\qquad
c_z=2m .
\]

They price the three variance directions. The criterion becomes

\[
\phi_{r,\kappa}(x,y,z_{\mathrm{sp}})
=c_xx+c_yy+c_zz_{\mathrm{sp}}
+\kappa\sqrt{qx^2+y^2+z_{\mathrm{sp}}^2},
\]

Here \(\phi_{r,\kappa}\) is the original objective expressed in variance coordinates.

The costs per unit of total variance are \(c_x/q\), \(c_y\), and \(c_z\). When \(\kappa=0\), the cheapest directions receive all the mass.

The norm term can favor spreading mass across directions. But optimizing these costs still does not enforce binary feasibility.

---

## Main result

Define the parity requirement \(d_m=0\) for even \(m\), and \(d_m=2/m\) for odd \(m\).

The exact implementability loss is

\[
\Delta_m^{\pm}(r,\kappa)
=
\inf_{\substack{(x,y,z_{\mathrm{sp}})\in T_m\\ y+z_{\mathrm{sp}}\ge d_m}}
\phi_{r,\kappa}(x,y,z_{\mathrm{sp}})
-
\inf_{(x,y,z_{\mathrm{sp}})\in T_m}
\phi_{r,\kappa}(x,y,z_{\mathrm{sp}}).
\]

The first minimum is the best actual randomization; the second is the covariance benchmark. They differ only by the parity restriction.

@informal thm:sharp-rho-star: For \(m\ge2\), \(a>b>0\), and \(r,\kappa\ge0\), a finite calculation gives the exact loss. Loss is zero iff some relaxed optimizer passes parity; the relaxed optimizer is unique when \(\kappa>0\).

Even \(m\) gives zero loss throughout. For odd \(m\), we need to explain why parity is both necessary and sufficient.

---

## Why parity is necessary

The community treatment-sign sums are

\[
(S_A,S_B)
=
\left(
\sum_{i\in A_m} Z_i,\,
\sum_{i\in B_m} Z_i
\right).
\]

Their second moments determine the two community-level variances:

\(y=\mathbb E[(S_A-S_B)^2]/(2m)\) measures variation in the community contrast.

\(z_{\mathrm{sp}}=\mathbb E[(S_A+S_B)^2]/(2m)\) measures variation in the aggregate.

Consequently, \(y+z_{\mathrm{sp}}=(\mathbb E[S_A^2]+\mathbb E[S_B^2])/m\).

For odd \(m\), each sum has absolute value at least one. Hence

\[
y+z_{\mathrm{sp}}\ge d_m .
\]

In the example, \(m=3\), so at least \(2/3\) of variance must remain outside the within-community contrasts.

---

## Vertex randomizations

For odd \(m\), the feasible triangle has four vertices. Each has a concrete assignment law.

Choose the community sums in the table, place the required signs uniformly within each community, and apply a fair global sign flip.

| Community sums before the flip | Variance coordinates \((x,y,z_{\mathrm{sp}})\) | Assignment pattern |
|---|---|---|
| \((m,-m)\) | \((0,2m,0)\) | Each community is homogeneous; labels oppose |
| \((m,m)\) | \((0,0,2m)\) | All units have the same label |
| \((1,-1)\) | \(((2m-d_m)/q,d_m,0)\) | Communities are minimally balanced; sums oppose |
| \((1,1)\) | \(((2m-d_m)/q,0,d_m)\) | Communities are minimally balanced; sums agree |

Uniform placement makes unit labels exchangeable within communities. The global flip ensures sign symmetry; these laws also respect community swapping.

The first two laws attain the original community-level corners. The last two attain the endpoints created by the parity restriction.

Every point in the parity-truncated triangle is a convex combination of its vertices.

To implement a desired point:

1. Choose a vertex with the weights of that convex combination.
2. Draw an assignment from that vertex’s law.

Second-moment matrices average under mixtures. The resulting covariance therefore has exactly the desired variance coordinates.

For even \(m\), uniform assignments with sums \((0,0)\) attain the remaining corner, \((m/(m-1),0,0)\). Together with the two homogeneous laws, they generate the entire relaxed triangle.

@informal lem:pm-reduced-slice-characterization: For integer \(m\ge2\), a block-symmetric relaxed covariance is generated by a sign-symmetric, block-exchangeable assignment law iff \(y+z_{\mathrm{sp}}\ge d_m\).

Parity exhausts feasibility because we have constructed every vertex and every mixture of them.

---

## Cut exactness

The cut law \(P_{\mathrm{cut}}\) flips a fair coin between assigning treatment to all of \(A_m\) and assigning it to all of \(B_m\).

Its covariance is \(X_{\mathrm{cut}}=X(1,-1)\), with coordinates \((0,2m,0)\).

If \(c_x/q>c_y+\kappa\) and \(c_z>c_y+\kappa\), moving variance away from the community contrast costs more than it can save in the norm penalty.

A sufficient parameter region is

\[
r< r_{\mathrm{cut}}(m,a,b,\kappa)
:= \max\!\left\{0,\,
\min\!\left(
2b(a+b)\left(1-\frac{\kappa}{a-b}\right),
2b(2m-2b-\kappa)
\right)\right\}.
\]

The threshold \(r_{\mathrm{cut}}\) guarantees those two cost comparisons.

@informal thm:cut-corner-exactness: For \(m\ge2\), \(a>b>0\), \(r,\kappa\ge0\), and \(r<r_{\mathrm{cut}}\), the cut law attains the unique relaxed optimum and \(\Delta_m^{\pm}(r,\kappa)=0\).

---

## Positive loss

At the pure within-community corner, the cost per unit of mass includes the norm contribution: \(c_x/q+\kappa/\sqrt q\).

If both alternatives cost more—\(c_y>c_x/q+\kappa/\sqrt q\) and \(c_z>c_x/q+\kappa/\sqrt q\)—moving mass out of that corner raises the criterion.

The unique relaxed optimum is then \(X_{\mathrm{spread}}=X(-1/(m-1),0)\), with coordinates \((m/(m-1),0,0)\).

For odd \(m\), it fails parity: it assigns no variance to either community total. Every actual design must move some mass into a more expensive direction.

In the example, the costs are \(17/3\), \(6\), and \(6\). With \(\kappa=0\), the within-community direction is strictly cheapest.

Assume odd \(m\) and \(a+3b<2m\). This scale condition leaves room for the within-community direction to be strictly cheapest.

The norm weight must lie below the ceiling

\[
q=2(m-1),\qquad
\kappa_{\mathrm{gap}}(m,a,b)
=
\frac{(2m-a-3b)(a-b)\sqrt q}{a+b},
\]

with \(0\le\kappa<\kappa_{\mathrm{gap}}\).

The cost comparisons give bounds \(R_x^-=2b(a+b)(1+\kappa/((a-b)\sqrt q))\) and \(R_x^+=(a+b)(2m-a-b-\kappa/\sqrt q)\).

They define the stated interval endpoints:

\[
r_{\mathrm{gap}}^-(m,a,b,\kappa)
=
\frac{R_x^-(m,a,b,\kappa)+R_x^+(m,a,b,\kappa)}{2},
\qquad
r_{\mathrm{gap}}^+(m,a,b,\kappa)
=
R_x^+(m,a,b,\kappa).
\]

@informal thm:gap-window: For \(m\ge2\), \(a>b>0\), odd \(m\), \(a+3b<2m\), \(0\le\kappa<\kappa_{\mathrm{gap}}\), and \(r_{\mathrm{gap}}^-<r<r_{\mathrm{gap}}^+\), \(X_{\mathrm{spread}}\) is uniquely relaxed-optimal and \(\Delta_m^{\pm}>0\).

For our example, this interval is \((7.5,9)\), containing \(r=8\).

---

## Solving the relaxation

Use variance masses \(t_x=qx\), \(t_y=y\), and \(t_z=z_{\mathrm{sp}}\), totaling \(M=2m\).

Write their linear costs as \(\alpha=(c_x/q,c_y,c_z)\), and their norm weights as \(\beta=(1/q,1,1)\).

The objective in mass coordinates is

\[
  \Phi(t)=\sum_{i\in\mathcal I}\alpha_i t_i
  +\kappa\sqrt{\sum_{i\in\mathcal I}\beta_i t_i^2}.
\]

Here \(\mathcal I=\{x,y,z_{\mathrm{sp}}\}\) indexes the three directions.

For \(\kappa>0\), enumerate nonempty supports \(S\): candidate sets of directions receiving positive mass. Their common marginal cost \(\lambda\) satisfies

\[
  \sum_{i\in S}\frac{(\lambda-\alpha_i)^2}{\beta_i}=\kappa^2,\qquad
  \alpha_i<\lambda\ \text{for every }i\in S,\qquad
  \lambda\le \alpha_j\ \text{for every }j\notin S .
\]

The equality determines the multiplier; the inequalities check that active directions receive mass and inactive directions need none. Exactly one pair passes these checks.

The selected support \(S\) and common marginal cost \(\lambda\) give the relaxed allocation explicitly:

\[
  t_i^\star=
  \begin{cases}
  \displaystyle
  M\,\frac{(\lambda-\alpha_i)/\beta_i}
  {\sum_{h\in S}(\lambda-\alpha_h)/\beta_h}, & i\in S,\\[1.1em]
  0, & i\notin S .
  \end{cases}
\]

Each active direction receives a share proportional to its cost advantage \(\lambda-\alpha_i\), adjusted by its norm weight \(\beta_i\). The denominator makes the shares sum to total mass \(M\).

The relaxed criterion value is

\[
  \Phi(t^\star)=M\lambda .
\]

Recover variance coordinates as \((t_x^\star/q,t_y^\star,t_z^\star)\), then check parity.

When \(\kappa=0\), put mass only in directions with the smallest \(\alpha_i\). If costs tie, retain a parity-feasible optimum whenever one exists.

---

## Correcting the optimum

If no relaxed optimizer passes parity, convexity puts the feasible optimum on the boundary segment

\[
H_{d_m}=\{(2m-d_m,s,d_m-s):0\le s\le d_m\}
\]

These are mass coordinates. The within-community mass is fixed; \(s\) divides the required remaining mass between the community contrast and aggregate directions.

Set \(M=2m\), \(d=d_m\), \(\delta=\alpha_y-\alpha_z\), and \(A=\beta_x(M-d)^2\). Thus \(\delta\) is their linear cost difference, and \(A\) is the fixed contribution to the squared norm.

For \(\kappa>0\), the minimizing split is

\[
s^\star=
\begin{cases}
0, & \displaystyle \delta\ge \frac{\kappa d}{\sqrt{A+d^2}},\\[0.8em]
d, & \displaystyle \delta\le -\frac{\kappa d}{\sqrt{A+d^2}},\\[0.8em]
\displaystyle
\frac{d-\delta\sqrt{(A+d^2/2)/(\kappa^2-\delta^2/2)}}{2},
& \text{otherwise.}
\end{cases}
\]

A large cost difference selects an endpoint; otherwise the norm penalty favors an interior split. For \(\kappa=0\), choose the cheaper endpoint.

Evaluate the criterion, subtract the relaxed value, and implement the corrected point by mixing vertex laws.

---

## Example completed

Return to \(m=3\), \(a=2\), \(b=1\), \(r=8\), and \(\kappa=0\).

The direction costs are \(17/3\), \(6\), and \(6\). The relaxation puts all six units of variance mass into the cheapest direction: coordinates \((3/2,0,0)\), with value \(34\).

Parity requires moving \(2/3\) of mass out. The corrected coordinates \((4/3,2/3,0)\) have value \(308/9\).

The implementing law is concrete:

- Flip a fair coin between community sums \((1,-1)\) and \((-1,1)\).
- In each community, choose uniformly among assignments with its selected sum.

Then \(\mathbb E[S_A^2]=\mathbb E[S_B^2]=1\), the aggregate sum is zero, and the squared difference of sums is four. Thus \(y=2/3\), \(z_{\mathrm{sp}}=0\), and the fixed total variance gives \(x=4/3\).

\[
\Delta_3^{\pm}(8,0)=\tfrac{308}{9}-34=\tfrac29\approx0.222,
\]

The value calculation and the assignment law attain the same optimum.

---

## Takeaways

- Symmetry turns covariance design into allocating variance among three directions. Binary feasibility adds exactly the community-size parity restriction.
- Homogeneous and minimally balanced community assignments generate every feasible covariance by mixtures. Even communities therefore have zero loss throughout.
- Solve the finite support problem and check parity. If it fails, optimize on one boundary segment, compute the exact loss, and construct its randomization.

---

## Appendix: Cut-corner exactness

The strict cut region makes the two-point cut law attain the unique relaxed optimum with zero implementability loss.

@formal thm:cut-corner-exactness

---

## Appendix: Robust corner exactness

Independent fair assignment is exactly optimal at finite robustness only on the specified parameter locus, and is the limiting relaxed target elsewhere.

@formal thm:robust-corner-exactness

---

## Appendix: Positive-gap window

Odd community size creates a nonempty parameter interval with a unique unattainable relaxed optimum and strictly positive loss.

@formal thm:gap-window

---

## Appendix: Sharp rounding loss

The finite support calculation and parity-boundary correction compute the exact implementability loss for every admissible parameter choice.

@formal thm:sharp-rho-star
