# Estimating Total Effects Under Network Interference

Low-order treatment interactions let us recover the effect of treating everyone, and shared assignments determine how accurately we can recover it.

---

## Motivation

A practitioner wants to compare treating everyone with treating no one.

\[
\tau_n:=\frac{1}{n}\sum_{i\in V_n}\bigl(Y_i(\mathbf 1)-Y_i(\mathbf 0)\bigr),
\]

Here \(V_n\) contains \(n\) units; \(Y_i(z)\) is unit \(i\)'s outcome under assignment \(z\). The vectors \(\mathbf 1\) and \(\mathbf 0\) treat everyone and no one, respectively.

With interference, neighbors’ treatments also affect outcomes. Comparing treated and untreated units need not recover this total effect.

---

## Research question

Exposure weighting, following Horvitz and Thompson (1952) and Aronow and Samii (2017), can target outcomes whose entire relevant neighborhood is treated or untreated.

Under independent assignment, those configurations become rare as neighborhoods grow.

Cortez-Rodriguez et al. (2023) instead exploit low-order interactions with SNIPE—the shifted-neighbourhood inverse-probability estimator—and establish unbiasedness and variance bounds.

Does this approach achieve the smallest possible worst-case mean squared error, and what determines its dependence on network degree?

---

## Key idea

Recover the total contrast from ordinary low-order assignment variation, then control how often that variation is shared across outcomes.

For fixed interaction order \(\beta\ge1\) and independent treatment probability \(p\in(0,1)\), the minimax error on our bounded classes has scale

\[
B^2\min\left\{1,\frac{dA_d}{n}\right\},
\]

up to positive constants depending only on \((\beta,p)\).

- \(B\) bounds coefficient mass or potential outcomes.
- \(d\) bounds neighborhood size and the number of outcomes one assignment affects.
- \(A_d\) is the expected squared contrast-recovering weight for a full \(d\)-unit neighborhood.

Clipped SNIPE attains this scale. We will explain both the attainable error and why every estimator faces it.

---

## Example

Take fair-coin assignment, \(p=1/2\), and first-order interference, \(\beta=1\).

An outcome consists of a baseline plus individual treatment terms:
\(Y_i(z)=c_{i,\varnothing}+\sum_{j\in N_i}c_{i,\{j\}}z_j\).
Here \(N_i\) is the set of assignments affecting unit \(i\).

The weight is \(g_{i,1,1/2}(Z)=4\sum_{j\in N_i}(Z_j-1/2)\). Multiplying by the outcome and taking expectations removes the baseline and recovers each treatment coefficient.

For a full \(d\)-unit neighborhood, its expected squared weight is

\[
A_d=4d,
\]

so the minimax error has scale \(B^2\min\{1,d^2/n\}\).

Why does population averaging incur another factor of \(d\)?

---

## Model

The graph is known. Its neighborhood \(N_i\) contains the assignments that can affect unit \(i\).

\[
Y_i(z)
:=
\sum_{S\subseteq N_i} c_{i,S}\prod_{j\in S} z_j .
\]

Each binary \(z_j\) records treatment. A subset \(S\) specifies an interaction, and \(c_{i,S}\) is its coefficient; the empty subset supplies the baseline.

**Low order:** coefficients vanish when \(|S|>\beta\). This rules out interactions involving more than \(\beta\) treatments.

**Independent assignment:** each realized \(Z_j\) is Bernoulli with common probability \(p\). We observe \(Y_i^{\mathrm{obs}}=Y_i(Z)\).

Potential outcomes stay fixed; expectations and mean squared errors average over assignment.

---

## Assumptions

**Bounded degree:** each outcome depends on at most \(d\) assignments, and each assignment affects at most \(d\) outcomes.

\[
\max_{i\in V_n}|N_i|\le d
\qquad\text{and}\qquad
\max_{j\in V_n}\bigl|\{i\in V_n:j\in N_i\}\bigr|\le d .
\]

Self-effects count toward both bounds.

**Coefficient-mass envelope:** the absolute coefficients, including the baseline, satisfy

\[
\sum_{S\subseteq N_i}|c_{i,S}|\le B .
\]

Alternatively, the **outcome envelope** requires \(\sup_z|Y_i(z)|\le B\) for every unit.

In our first-order example, the coefficient envelope bounds the absolute baseline plus the absolute individual treatment coefficients. It therefore also bounds every potential outcome by \(B\).

---

## Contrast weights

Center each assignment at its mean \(p\). A product of \(r\) centered treatments changes between everyone treated and everyone untreated by

\[
\Delta_r(p):=(1-p)^r-(-p)^r .
\]

Here \(r\) is the interaction’s size. Write \(\bar\beta_d:=\min\{\beta,d\}\), the largest order that fits inside a neighborhood.

The unit’s contrast-recovering weight is

\[
g_{i,\beta,p}(z)
:=
\sum_{r=1}^{\bar\beta_d}
\frac{\Delta_r(p)}{[p(1-p)]^r}
\sum_{\substack{S\subseteq N_i\\ |S|=r}}
\prod_{j\in S}(z_j-p).
\]

The numerator supplies the desired contrast. The denominator cancels that centered product’s design second moment.

At \(p=1/2,\beta=1\), this becomes four times the sum of centered individual treatments.

---

## Recovery and estimation

Independence makes distinct centered treatment products orthogonal: their expected product is zero.

Let \(g_d\) be the weight on a full \(d\)-coordinate neighborhood. For any low-order outcome polynomial \(f\),

\[
\mathbb E_D[g_d(Z)f(Z)]
=
L_d(f).
\]

Here \(D\) is the product-Bernoulli design, and \(L_d(f)\) is \(f(1,\ldots,1)-f(0,\ldots,0)\).

Orthogonality isolates each centered interaction; its weight returns its endpoint contrast. The same argument applies within each unit’s neighborhood.

Average the weighted observed outcomes:

\[
\widehat\tau_n^{\mathrm{SNIPE}}
:=
\frac{1}{n}
\sum_{i\in V_n}
Y_i^{\mathrm{obs}}\,g_{i,\beta,p}(Z).
\]

This unprojected estimator is design-unbiased for \(\tau_n\). Recovery uses ordinary assignments, without waiting for fully treated or untreated neighborhoods.

---

## Local cost

Orthogonality also gives the expected squared weight for a full neighborhood:

\[
A_d
:=
\sum_{r=1}^{\bar\beta_d}
\binom{d}{r}
\frac{\Delta_r(p)^2}{[p(1-p)]^r}.
\]

The binomial coefficient counts size-\(r\) interactions; each summand is their contribution to the weight’s second moment. Smaller neighborhoods have second moment at most \(A_d\).

The highest contributing order is

\[
k_\star(d,\beta,p)
:=
\max\bigl\{r\in\{1,\ldots,\bar\beta_d\}:\Delta_r(p)\ne0\bigr\}.
\]

For fixed \((\beta,p)\), \(A_d\) is bounded above and below by constant multiples of \(\binom d{k_\star(d,\beta,p)}\).

At \(p=1/2\), even centered orders have zero endpoint contrast. In our first-order example, \(k_\star=1\) and \(A_d=4d\).

---

## Covariance accounting

Write \(W_i=Y_i^{\mathrm{obs}}g_{i,\beta,p}(Z)\), the weighted outcome. Its centered-product expansion still uses only assignments in \(N_i\).

Covariances between two weighted outcomes pair coefficients on the same nonempty subset. For any such subset, at most \(d\) outcomes can contain it:

\[
\sum_{\substack{S\subseteq N_i\\ |S|=r}}
\#\{l\in V_n:S\subseteq N_l\}
\le
d\binom{|N_i|}{r}
\le
d\binom{d}{r}.
\]

Here \(r\ge1\), and \(\#\) counts outcomes sharing \(S\). Any coordinate in \(S\) affects at most \(d\) outcomes.

For each subset, the squared sum of its coefficients across outcomes is at most \(d\) times their sum of squares. Orthogonality therefore gives
\(\sum_{i,l}\operatorname{Cov}_Z(W_i,W_l)\le d\sum_i\operatorname{Var}_Z(W_i)\).

In the first-order fair-coin example, weighted outcomes contain constant, singleton, and pair terms. Constants disappear from covariance; each remaining subset is shared at most \(d\) times.

---

## Variance and clipping

Both envelopes give \(|Y_i(Z)|\le B\). Consequently,
\(\operatorname{Var}_Z(W_i)\le\mathbb E_Z[W_i^2]\le B^2A_d\).

The covariance bound and averaging by \(n\) give mean squared error at most \(B^2dA_d/n\).

In our first-order fair-coin example, local squared size is at most \(4B^2d\); assignment sharing supplies another factor \(d\), giving the bound \(4B^2d^2/n\).

Under the coefficient envelope, \(\tau_n\in[-B,B]\). Clip the estimate:

\[
\widehat\tau_n^{\mathrm{up}}
:=
\Pi_{[-B,B]}
\left(
\widehat\tau_n^{\mathrm{SNIPE}}
\right),
\]

where projection replaces an out-of-range value by the nearest endpoint.

Projection cannot increase squared error and bounds it by a constant multiple of \(B^2\). Under the outcome envelope, use \([-2B,2B]\). Combining the variance and bounded-error guarantees produces the minimum of the two branches.

---

## Main result

Take \(n\ge1\), \(1\le d\le n\), and \(B\ge0\). Let \(\mathcal M_{n,d,\beta}(B)\) collect our known-graph, bounded-degree, low-order coefficient-mass models.

The minimax risk \(R_n^\star\) is the smallest worst-case assignment mean squared error among estimators using the graph, assignments, and observed outcomes.

@informal thm:degree-frontier: For fixed \(\beta\ge1\), \(p\in(0,1)\), \(n\ge1\), \(1\le d\le n\), and \(B\ge0\), our known-graph degree and low-order assumptions with coefficient mass at most \(B\) give matching minimax bounds, attained by clipped SNIPE.

\[
R_n^\star(d,\beta,p,B)
\le
\sup_{(G,c)\in\mathcal M_{n,d,\beta}(B)}
\mathbb E_Z\!\left[
\left(\widehat\tau_n^{\mathrm{up}}-\tau_n\right)^2
\right]
\le
C_{\beta,p}B^2
\min\!\left\{1,\frac{d\binom{d}{k_\star(d,\beta,p)}}{n}\right\},
\]

The constant \(C_{\beta,p}\) depends only on order and assignment probability. Every estimator’s worst-case error is at least a positive constant depending only on \((\beta,p)\) times the same expression.

@informal thm:bounded-outcome-degree-frontier: Under the same fixed order, independent assignment, known-graph degree bounds, \(n\ge1\), \(1\le d\le n\), and \(B\ge0\), uniformly bounded outcomes have the same minimax scale, attained by SNIPE clipped to \([-2B,2B]\).

In the running example, these matching bounds have scale \(B^2\min\{1,d^2/n\}\).

---

## A hard local change

To show that every estimator faces this error, change outcomes substantially at the target assignments while changing them little under the experiment.

Normalize the full-neighborhood weight:

\[
h_d:=\frac{g_d}{A_d},
\]

where \(h_d\) is a low-order outcome perturbation. It satisfies

\[
L_d(h_d)=1,
\qquad
\mathbb E_D[h_d(Z)^2]=A_d^{-1}.
\]

Its endpoint contrast is one, while its average squared size under assignment is only \(A_d^{-1}\).

@informal lem:block-energy-representer: For fixed \(\beta\ge1\), \(p\in(0,1)\), and every \(d\ge1\), \(h_d\) uniquely minimizes design mean square among low-order polynomials whose all-treated-versus-all-control contrast is one.

The same weight that recovers the contrast identifies the direction in which it is hardest to detect a change.

---

## An admissible perturbation

A hard direction must also respect the coefficient envelope.

Let \(h_{d,T}\) be the coefficient on raw treatment monomial \(T\) in \(h_d\). Uniformly over neighborhood size,

\[
\sum_{T\subseteq\{1,\ldots,d\}} |h_{d,T}|
\le
H.
\]

The finite constant \(H\) depends only on \((\beta,p)\).

Why is it uniform? Expanding a size-\(r\) centered product gives absolute coefficient mass \((1+p)^r\). At every contributing order, dividing by its energy contribution costs at most \((1+p)^r/|\Delta_r(p)|\), a fixed-order constant. Normalization by \(A_d\) therefore removes the growth in interaction counts.

Define \(H_{\beta,p}:=\sup_{r\ge1}\sum_T|h_{r,T}|\), which is finite by this bound.

A baseline of magnitude at most \(B/2\), plus a perturbation of amplitude \(\delta\le B/(2H_{\beta,p})\), has coefficient mass at most \(B\).

---

## Hard populations

For \(B>0\), form \(m=\lfloor n/d\rfloor\) complete directed \(d\)-unit blocks, including self-effects. Remaining units have zero outcomes.

Within block \(b\), every outcome is \(U_b+\delta h_d\) or \(U_b-\delta h_d\). Independent block baselines \(U_b\) have a smooth cosine-squared density supported on \([-B/2,B/2]\).

Each block supplies one distinct outcome, repeated \(d\) times. Random baselines hide small sign shifts.

The two signs give models \(M_+\) and \(M_-\) with

\[
\tau_n(M_+)=\rho\delta,
\qquad
\tau_n(M_-)=-\rho\delta.
\]

Here \(\rho=md/n\) is the active population share.

For the induced observation distributions \(\Pi_+\) and \(\Pi_-\),

\[
H^2(\Pi_+,\Pi_-)
\le
\frac{4\pi^2m\delta^2}{B^2A_d}.
\]

The squared Hellinger distance \(H^2\) measures distance between square roots of densities. A small value makes the signs hard to distinguish.

---

## Matching both branches

Choose the perturbation amplitude as

\[
\delta(n,d,\beta,B,p)
:=
B\min\left\{(2H_{\beta,p})^{-1},(4\pi)^{-1}\right\}
\min\left\{1,\sqrt{\frac{A_d}{m}}\right\}.
\]

The first prefactor reserves half the coefficient budget for the baseline and makes the squared Hellinger distance at most one quarter.

The final minimum chooses the largest scale satisfying both restrictions: coefficient admissibility and indistinguishability across \(m\) blocks.

The target gap is \(2\rho\delta\), and

\[
\frac12\le \rho\le 1,
\qquad
\frac{A_d}{m}
=
\frac{dA_d/n}{\rho}.
\]

Thus squared target separation is bounded above and below by positive \((\beta,p)\)-dependent multiples of \(B^2\min\{1,dA_d/n\}\).

An estimate accurate relative to this gap would reveal the sign. The nearby observation distributions prevent uniformly reliable sign recovery, forcing the matching minimax lower bound.

---

## Takeaways

- Low-order structure lets centered neighborhood weights recover the total effect from ordinary independent assignments.
- Orthogonal expansion of **weighted outcomes** controls covariance: local squared size costs \(A_d\), and each nonempty assignment subset is shared at most \(d\) times.
- Clipping and admissible complete-block perturbations match both branches of the minimax scale. For first-order fair-coin assignment, that scale is \(B^2\min\{1,d^2/n\}\).

---

## Appendix: Degree frontier

Matching lower bounds and clipped-SNIPE upper bounds characterize coefficient-mass minimax error.

@formal thm:degree-frontier

---

## Appendix: Bounded-outcome frontier

The outcome envelope shares the minimax scale; when \(d\mid n\), unprojected SNIPE has exact global worst-case risk \(B^2dA_d/n\).

@formal thm:bounded-outcome-degree-frontier

---

## Appendix: Local linear benchmark

Weights multiply outcomes linearly, depend only on assignments in their own block, and are unbiased for every admissible schedule; their complete-block minimax risk is exact.

@formal thm:sharp-local-linear-constant-and-representers
