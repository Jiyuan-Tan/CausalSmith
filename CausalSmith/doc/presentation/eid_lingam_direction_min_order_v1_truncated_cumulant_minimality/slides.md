# Distinguishing Directions With Hidden Sources

Higher-order features of two outcomes can rule out the competing direction when the number of hidden sources and their loading conventions are fixed.

---

## Research question

A researcher observes \(X,Y\) and wants to distinguish \(X\to Y\) from \(Y\to X\).

- Independent component analysis separates mixtures using independent, non-Gaussian sources: Comon (1994).
- Hidden sources complicate this approach: with \(m\) middle source slots, there are \(m+2\) sources but only two outcomes. Hoyer et al. (2008) studies this hidden-variable setting.
- Cumulants summarize joint variation: covariance is the second-order block; higher orders supply additional restrictions.
- Chen et al. (2025), our closest comparator, establishes direction separation using cumulant rank restrictions through order \(2m+3\).

With the source count and loading conventions maintained, can fewer orders exclude the opposite representation?

---

## Key idea

Recover the source loading directions jointly across cumulant orders.

The source weights change with the order, but the loading directions stay fixed.

- The forward convention requires a source affecting only \(Y\): a vertical direction.
- The reverse convention requires a source affecting only \(X\): a horizontal direction.
- Recovering a vertical direction without a horizontal one makes every reverse representation incompatible.

@informal thm:generic-apolar-arrow-recovery: For \(m\ge1\), with fixed source count and axis conventions, cumulants through \(2m+2\) generically recover unordered loading directions and exclude every opposite-direction parameter choice producing the same cumulants.

---

## Example

Use the one-middle-slot model: \(m=1\), with forward directions \((1,\gamma)\), \((1,\rho)\), and \((0,1)\).

Here \(\gamma\) is the direct slope and \(\rho\) the middle slope. Take them nonzero and distinct.

Its cumulant coordinates satisfy \(t_{r,a}=c_{0r}\gamma^a+c_{1r}\rho^a+c_{2r}\mathbb 1_{\{a=r\}}\), for \(r=2,3,4\). The weight \(c_{jr}\) is source \(j\)'s order-\(r\) cumulant; the indicator selects the pure-\(Y\) coordinate.

- Third-order information gives one equation for a candidate cubic polynomial.
- Fourth-order information gives two more.
- Generically, their common solution is proportional to \(Q_D=x(y-\gamma x)(y-\rho x)\), in formal variables \(x,y\).

The factors recover the three directions. There is no factor \(y\), so the horizontal direction required by a reverse fit is absent.

---

## Model

Each loading vector specifies how one centered latent source \(S_j\) enters the two outcomes.

**Forward convention, \(X\to Y\):**

\[
(X,Y)^\top=\sum_{j=0}^{m+1} u_j S_j .
\]

Here \(u_0=(1,\gamma)\) is the direct loading, \(u_j=(1,\rho_j)\) are middle loadings, and \(u_{m+1}=(0,1)\) affects only \(Y\).

**Reverse convention, \(Y\to X\):**

\[
(X,Y)^\top=\sum_{j=0}^{m+1} v_j S_j .
\]

Here \(v_0=(1,0)\) affects only \(X\), \(v_j=(\sigma_j,1)\) are middle loadings, and \(v_{m+1}=(\delta,1)\) is the direct loading.

The reverse direct slope is \(\delta\); its middle slopes are \(\sigma_j\). Both conventions maintain exactly \(m+2\) source slots.

---

## Assumptions

Set the retained order to \(K=2m+2\).

- **Independent, centered sources:** contributions to joint cumulants add across sources.
- **Finite moments through \(K\):** every retained cumulant exists.
- **Non-Gaussian sources:** higher-order information can distinguish mixtures beyond covariance.
- **Distinct finite slopes:** different source directions do not merge.
- **Nonzero direct slope and retained source cumulants:** the direct edge is present, and every source contributes at every retained order.

The theorem also excludes additional polynomial equalities among parameters. “Generic” means outside a proper algebraic subset defined by such equalities.

For \(m=1\), distinctness requires \(\gamma\ne\rho\), but permits \(\rho=0\). The theorem's additional restrictions exclude that common-axis exception.

---

## Cumulant information

Let \(P\) be the observed law. The coordinate \(\kappa_{r,a}(P)\) is the joint cumulant with \(r-a\) copies of \(X\) and \(a\) copies of \(Y\).

\[
T_L(P)=\bigl(\kappa_{r,a}(P):2\le r\le L,\ 0\le a\le r\bigr),
\]

This vector collects population cumulants through order \(L\).

The forward map \(\Phi^{\mathrm{right}}_{m,L}\) computes these coordinates from slopes and source cumulants:

\[
\bigl[\Phi^{\mathrm{right}}_{m,L}(\gamma,\rho,c)\bigr]_{r,a}
=
\sum_{j=0}^{m+1}
c_{jr}\,(u_{j1})^{r-a}(u_{j2})^a,
\qquad
2\le r\le L,\quad 0\le a\le r,
\]

Here \(u_{j1},u_{j2}\) are source \(j\)'s loadings on \(X,Y\). Independence makes these weighted contributions additive. The reverse map \(\Phi^{\mathrm{left}}_{m,L}\) uses the reverse loadings and source weights.

---

## Main result

Let \(U_m^{\mathrm{right}}\) be the theorem's open dense set of forward parameters satisfying the assumptions and avoiding the additional algebraic exceptions.

For every generating parameter \(\theta\in U_m^{\mathrm{right}}\), at \(K=2m+2\):

\[
R^{\mathrm{left}}_{m,K}\!\left(\Phi^{\mathrm{right}}_{m,K}(\theta)\right)=\varnothing.
\]

The set \(R^{\mathrm{left}}_{m,K}(t)\), called a **fiber**, consists of all reverse parameter choices producing cumulant vector \(t\). Its emptiness excludes every reverse fit with the maintained source count.

The cumulants also recover the unordered finite slopes \(\{\gamma,\rho_1,\ldots,\rho_m\}\). The reverse conclusion is symmetric.

In the one-slot model, orders through four generically recover \(\{\gamma,\rho\}\) and exclude every reverse fit.

---

## Real source models

Arbitrary algebraic source weights need not be cumulants of actual random variables.

Define \(F^{\mathrm{right}}_{m,K}\) as the real forward parameters with distinct finite slopes, a nonzero direct slope, and source weights realizable by centered, non-Gaussian real sources with finite moments through \(K\).

For each source, realizability requires:

\[
\operatorname{Cum}_r(S_j)=c_{jr},
\qquad 2\leq r\leq L.
\]

Here \(L\) is the retained order, set to \(K\); \(\operatorname{Cum}_r(S_j)\) is source \(j\)'s order-\(r\) cumulant. Define \(F^{\mathrm{left}}_{m,K}\) analogously.

The theorem supplies open real parameter neighborhoods that meet these feasible sets, with every feasible point in those neighborhoods satisfying recovery and separation.

Thus the algebraic conclusion applies to actual source models on nonempty feasible patches.

---

## Shared loading directions

Convert each observed cumulant block into a polynomial:

\[
f_r(x,y)=\sum_{a=0}^{r}\binom{r}{a}t_{r,a}x^{r-a}y^a,
\qquad
t=\Phi^{\mathrm{right}}_{m,K}(\theta),
\]

The formal variables \(x,y\) organize the observed coordinates \(t_{r,a}\); the binomial coefficient supplies the expansion weights.

Substituting the cumulant map gives \(f_r(x,y)=\sum_{j=0}^{m+1}c_{jr}(u_{j1}x+u_{j2}y)^r\).

Each source contributes a weighted power of its loading linear form.

Changing the cumulant order changes the weights and powers, while preserving the directions. This is the structure the recovery equations exploit.

---

## A first attempt

Write \(n=m+2\) for the number of directions.

Seek a homogeneous degree-\(n\) polynomial \(q(x,y)\): every term has total degree \(n\). Its \(n+1\) coefficients are unknown.

Replace \(x,y\) in \(q\) by derivatives to obtain \(q(\partial)\).

Applying this operator to a source contribution multiplies it by \(q(u_j)\), the polynomial evaluated at that source's loading vector. A zero value therefore kills that contribution.

At order \(n\), the condition \(q(\partial)f_n=0\) gives only the scalar equation \(\sum_j c_{jn}q(u_j)=0\).

One equation allows cancellations between sources. It cannot recover the directions.

---

## Independent restrictions

At order \(n+k\), the derivative output is, up to a common nonzero factor, \(\sum_j c_{j,n+k}q(u_j)(u_{j1}x+u_{j2}y)^k\).

Its coefficients give linear restrictions on the same \(n\) values \(q(u_j)\).

- At the highest retained order, \(k=m=n-2\), the output has \(m+1=n-1\) coefficients.
- Distinct directions make any \(n-1\) source columns independent. This is a Vandermonde restriction: successive powers distinguish distinct slopes.
- Nonzero source weights preserve that independence, leaving only one possible combination of the \(q(u_j)\) values.
- The order-\(n\) equation supplies the last restriction. Its weights are separate parameter coordinates, so generically its row rules out that remaining combination.

A determinant measuring this rank is a nonzero polynomial; rank failure requires an additional polynomial equality.

These latent values explain the rank. Solving for \(q\) uses only the observed coefficients of the \(f_r\).

---

## Example: three equations

For \(m=1\), seek a cubic \(q\). The three values to constrain are \(q(u_0)=q(1,\gamma)\), \(q(u_1)=q(1,\rho)\), and \(q(u_2)=q(0,1)\).

After removing common nonzero derivative factors:

- \(f_3\) gives \(c_{03}q(u_0)+c_{13}q(u_1)+c_{23}q(u_2)=0\).
- The \(x\) coefficient from \(f_4\) gives \(c_{04}q(u_0)+c_{14}q(u_1)=0\).
- The \(y\) coefficient gives \(\gamma c_{04}q(u_0)+\rho c_{14}q(u_1)+c_{24}q(u_2)=0\).

The two fourth-order rows are independent and leave one possible combination of the three values.

The third-order weights generically supply an independent row. All three values must then vanish: source contributions cannot cancel across both orders.

---

## Support recovery

Let \(D\) be the collection of true directions. Define \(Q_D\) as the product of one linear factor vanishing on each distinct direction.

The rank argument forces \(q\) to vanish on every direction. A degree-\(n\) polynomial with these \(n\) distinct directional zeros must be proportional to \(Q_D\).

\[
\bigl[q(\partial)f_{n+k}=0\ \text{for every }0\leq k\leq m\bigr]
\quad\Longleftrightarrow\quad
\exists c\in\mathbb C:\ q=cQ_D.
\]

Here \(k\) indexes the retained blocks, \(q\) has degree \(n\), and \(c\) is an arbitrary scale.

Solve these linear equations in \(q\)'s coefficients, then factor the surviving polynomial.

For \(m=1\), its factors are proportional to \(x(y-\gamma x)(y-\rho x)\): the vertical direction and the two unordered finite slopes.

---

## Axis separation

For generic forward parameters, the recovered polynomial satisfies:

\[
Q_D\neq0,\qquad x\mid Q_D,\qquad y\nmid Q_D,
\]

The factor \(x\) records the vertical loading direction. The missing factor \(y\) records the absence of a horizontal direction.

- Every reverse representation contains a horizontal source slot.
- Multiplying one vanishing factor per reverse slot gives a nonzero degree-\(n\) polynomial containing \(y\).
- That polynomial annihilates the same observed cumulant forms.
- Recovery uniqueness would force it to be proportional to \(Q_D\), contradicting the missing \(y\) factor.

This argument excludes every reverse parameter choice, including choices with merged directions or zero source weights.

---

## Example: the exception

In the one-slot model, setting \(\rho=0\) adds a horizontal direction. The support polynomial now contains both \(x\) and \(y\), so the axis contradiction disappears.

The explicit common-axis assignment is:

\[
\rho=\sigma=0,\qquad
\delta\gamma=1,\qquad
d_{0r}=c_{1r},\qquad
d_{1r}=c_{2r},\qquad
d_{2r}=c_{0r}\gamma^r.
\]

Here \(d_{jr}\) are reverse source cumulants. For \(r=2,3,4\), these assignments make both conventions produce the same cumulants.

The reverse fit reassigns the horizontal and vertical sources and rescales the remaining source.

Direction recovery succeeds generically because the recovered support contains only the axis required by the generating convention.

---

## Further results

Recovering directions leaves their structural labels ambiguous.

@informal thm:generic-arrow-recovery-and-fiber-obstruction: For \(m\ge1\), at \(K=2m+2\) on the theorem's generic loci, exchanging a direct slot with a middle slot and their complete source-cumulant sequences preserves the observed cumulants beyond middle-slot relabelling.

For a forward parameter \(\theta\), the exchanged parameter \(\theta'\) satisfies:

\[
\Phi^{\mathrm{right}}_{m,K}(\theta')
=
\Phi^{\mathrm{right}}_{m,K}(\theta),
\]

The equality means that every retained observed cumulant stays the same after exchanging the complete slope-and-weight pairs.

With one middle slot, the recovered pair \(\{\gamma,\rho\}\) does not determine which slope is the direct coefficient.

---

## Takeaways

- With fixed source count and loading conventions, population cumulants through \(2m+2\) generically recover unordered directions and exclude every opposite representation.
- Shared directions turn different cumulant orders into independent restrictions: solve for their common vanishing polynomial, then use the incompatible axis requirement.
- Direction separation identifies the compatible convention while leaving the direct coefficient's structural label ambiguous.

---

## Appendix: Support recovery and separation

The exact statement gives joint-equation uniqueness, loading-support recovery, full opposite-fiber exclusion, and open neighborhoods meeting real feasibility.

@formal thm:generic-apolar-arrow-recovery

---

## Appendix: Same-arrow ambiguity

The exact statement gives direct–middle slot swaps beyond admissible relabelling and the dimension of generic same-arrow fibers.

@formal thm:generic-arrow-recovery-and-fiber-obstruction

---

## Appendix: Exceptional compatibility

The exact statement gives codimension one for the compatibility closure and characterizes its generic parameter preimages.

@formal thm:exceptional-locus-codimension-one

---

## Appendix: Lower real information order

The exact statement gives generic real opposite-fiber exclusion at order \(2m+1\) for \(m\ge3\).

@formal thm:improved-real-information-order
