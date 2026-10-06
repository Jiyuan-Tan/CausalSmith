# Estimating Treatment Effects With Sparse Adjustment Cells

A known bound on how much treatment effects differ across cells can change how accurately we estimate their average.

---

## Motivation

A practitioner wants the average treatment effect after adjusting for a discrete confounder.

- There are \(n\) observations across \(d\) adjustment cells.
- Cell frequencies can be highly uneven.
- Many sampled cells contain treated observations or controls, but no comparison between them.

Population overlap makes adjustment possible in principle. It does not supply observed comparisons in every cell.

---

## Standard approach

Estimate treated and control means within each cell, then average their differences using cell frequencies.

For binary outcomes with fixed overlap, Zeng et al. (2024) establish the usual regression, weighting and doubly robust mean-squared error scale

\[
\frac{d^2}{n^2}+\frac1n ,
\]

where \(d\) counts cells and \(n\) counts observations.

Their unrestricted minimax lower benchmark, before saturation, is smaller:

\[
\frac{d^2}{n^2\log^2 n}+\frac1n ,
\]

These expressions compare ordinary sampling noise with the extra cost of sparse adjustment.

**How can we use sparse cells more effectively—and how does effect heterogeneity change the answer?**

---

## Key idea

We use two different sources of information.

- **Similar effects:** comparisons from cells containing both arms can estimate the population effect even with altered cell weights.
- **Different effects:** polynomial corrections estimate rare cells’ population contributions without dividing by their observed arm counts.

A known heterogeneity bound determines which method to use.

Under fixed overlap and bounded conditional means and variances, our selector attains the better risk benchmark. Upper and lower bounds match at homogeneity, at every fixed positive heterogeneity radius, and in several additional regimes.

---

## Example

At **exact homogeneity**, every supported cell has the same treatment effect.

Let \(N_{ak}\) count observations in arm \(a\) and cell \(k\), and \(N_k=N_{0k}+N_{1k}\).

A **crossed cell** contains both arms: \(I_k=\mathbf 1\{N_{0k}N_{1k}>0\}\). Let \(R_n=\sum_kN_kI_k\) count observations in crossed cells.

\[
T_n^{\mathrm{col}}
:=
\operatorname{clip}_{[-M,M]}
\left(
\frac{\mathbf 1\{R_n>0\}}{R_n}
\sum_{k=1}^d
N_kI_k(\overline Y_{1k}-\overline Y_{0k})
\right),
\]

Here \(\overline Y_{ak}\) is the arm-cell sample mean. The inner value is zero if no cell is crossed; clipping truncates the estimate to the known target range \([-M,M]\).

Every available comparison estimates the same effect. Their weights need not reproduce population cell frequencies.

---

## Model

We observe independent records \(O=(X,A,Y)\):

- \(X\) is the adjustment cell.
- \(A\in\{0,1\}\) is treatment.
- \(Y\) is the outcome; \(Y(a)\) is its potential value under treatment \(a\).

**Consistency:** \(Y=Y(A)\) links observed and potential outcomes.

**Conditional exchangeability:** \((Y(0),Y(1))\perp A\mid X\) rules out remaining treatment selection within cells.

Let \(p_k=P(X=k)\) be cell mass and \(\mu_{ak}=E_P[Y\mid A=a,X=k]\) an arm-cell mean. The identified average treatment effect, or ATE, is

\[
\tau(P)
:=
\sum_{k=1}^{d}p_k(\mu_{1k}-\mu_{0k}).
\]

This averages cell effects using population masses—the adjustment logic of Rosenbaum and Rubin (1983).

---

## Assumptions

**Fixed overlap:** the propensity \(\pi_k=P(A=1\mid X=k)\) satisfies \(\epsilon\le\pi_k\le1-\epsilon\), with fixed \(0<\epsilon<1/2\). Both arms remain possible in every supported cell.

**Known scale:** \(M\ge1\) and \(|\mu_{ak}|\le M/2\), so the ATE lies in \([-M,M]\).

**Bounded noise:**

\[
E_P\!\left[(Y-\mu_{ak})^2\mid A=a,X=k\right]\le M^2 .
\]

This bounds conditional variance; outcomes may be unbounded.

**Known heterogeneity radius:** write \(\tau_k=\mu_{1k}-\mu_{0k}\) and \(\delta_k=\tau_k-\tau(P)\).

\[
\max_{k:p_k>0}|\delta_k|\le \sigma M .
\]

Here \(0\le\sigma\le2\). Our example has \(\sigma=0\); radius two permits unrestricted effects under the mean bound.

Let \(\mathcal P_{d,\epsilon,M,\sigma}\) denote this model class, including the causal conditions. Cell masses are arbitrary.

---

## Main result

Our estimator \(\widehat\tau_n^\star\) selects among polynomial adjustment, crossed-cell averaging and zero, using known \(M,\sigma\).

@informal thm:frontier-upper-all-d: For every \(n,d\ge1\), known \(M\ge1,\sigma\in[0,2]\), consistency, exchangeability, fixed overlap and the mean, variance and heterogeneity bounds give the selector a worst-case MSE of at most \(C_\epsilon M^2r_{n,d,\sigma}\).

\[
r_{n,d,\sigma}
:=
n^{-1}
+
\min\left\{
\sigma^2+\frac{d}{n^2},
\frac{d^2}{n^2\log^2(en)},
1
\right\},
\]

The benchmark \(r_{n,d,\sigma}\) is ordinary sampling noise plus the smallest of borrowing cost, polynomial approximation cost and the outcome-scale cap.

\[
\sup_{P\in\mathcal P_{d,\epsilon,M,\sigma}}
E_{Q_P^{(n)}}\!\left[\left(\widehat\tau_n^{\star}-\tau(P)\right)^2\right]
\le
C_{\epsilon}M^2 r_{n,d,\sigma}.
\]

Here \(Q_P^{(n)}\) is the independent sampling law, and \(C_\epsilon\) depends only on overlap.

---

## Minimax benchmark

**Minimax risk** is the smallest worst-case mean-squared error achievable by any estimator.

Let \(\mathsf R_{n,d,\epsilon,M,\sigma}\) denote that risk over our model class.

@informal thm:two-sided-minimax-bracket-all-d: For every \(n,d\ge1\), \(M\ge1\) and \(0\le\sigma\le2\), our consistency, exchangeability, fixed-overlap, mean, variance and heterogeneity conditions give a two-sided minimax risk bracket.

\[
c_{\epsilon}M^2
\left\{
\frac1n+\min\left(1,\frac d{n^2}\right)
+\sigma^2\min\left(1,\frac{d^2}{n^2\log^2(en)}\right)
\right\}
\le
\mathsf R_{n,d,\epsilon,M,\sigma}.
\]

The constant \(c_\epsilon>0\) depends only on overlap.

The unavoidable cost combines ordinary sampling noise, scarce comparisons even at homogeneity, and radius-sensitive rare-cell difficulty.

The upper bound chooses between methods; the lower bound records difficulties that every method faces.

---

## Borrowing across cells

Conditional on observed cells and treatment assignments, the crossed-cell average targets

\( \sum_k (N_kI_k/R_n)\tau_k \), whenever \(R_n>0\).

Its weights are nonnegative and sum to one.

- At exact homogeneity, they average the common effect.
- Otherwise, every averaged effect is within \(\sigma M\) of the population ATE.
- Thus altered weights contribute at most \(\sigma M\) to the conditional target discrepancy.

\[
\sup_{P\in\mathcal P_{d,\epsilon,M,\sigma}}
E_{Q_P^{(n)}}\!\left[\{T_n^{\mathrm{col}}-\tau(P)\}^2\right]
\le
C_\epsilon M^2\left(\frac1n+\sigma^2+\frac{d}{n^2}\right).
\]

This bounds crossed-cell estimation risk. The squared radius prices borrowing; the other terms price sampling noise and scarce comparisons.

Why is the scarcity cost linear in \(d\)?

---

## Collision intuition

Consider the uniform-cell special case, \(p_k=1/d\), used in the homogeneous lower-bound construction.

- Two independent observations share a cell with probability \(1/d\).
- A sparse sample therefore supplies roughly \(n^2/d\) within-cell pairs.
- Fixed overlap gives a nonvanishing fraction of opposite-arm pairs.

At homogeneity, these comparisons all inform the same effect. Their reciprocal information scale is \(d/n^2\).

In denser samples, ordinary \(1/n\) sampling noise governs the risk; pairs sharing observations do not create independent information indefinitely.

Our occupancy analysis makes this intuition uniform over arbitrary cell masses.

---

## The rare-cell target

Borrowing becomes costly when cell effects differ substantially. We then need each cell’s population-weighted contribution.

Use two population ingredients from the polynomial construction:

- \(s_{ak}=P(A=a,X=k)\): the arm-cell probability.
- \(z_{ak}=E_P[(Y/M)\mathbf1\{A=a,X=k\}]\): the normalized outcome moment in that arm-cell.

Since \(z_{ak}=s_{ak}\mu_{ak}/M\), cell \(k\)’s normalized ATE contribution is

\(p_k(z_{1k}/s_{1k}-z_{0k}/s_{0k})\).

Ordinary adjustment replaces these ratios with sample means. For a rare arm-cell, the denominator can be zero.

We instead approximate the weighted ratios by polynomials in population probabilities.

---

## Heavy and light cells

Split the sample: a pilot block classifies cells, and an independent estimation block estimates their contributions.

**Heavy cells** have enough pilot observations for ordinary adjustment.

\[
\widehat h_k
:=
\frac{N_k^{(1)}}{m_1}\,
\frac{\overline Y_{1k}^{(1)}-\overline Y_{0k}^{(1)}}{M}.
\]

Here \(m_1\) is the estimation-block size, \(N_k^{(1)}\) its cell count, and \(\overline Y_{ak}^{(1)}\) its arm-cell sample mean.

This estimates the cell’s contribution as empirical frequency times its contrast, normalized by \(M\).

**Light cells** receive polynomial corrections. Write \(L=\log(en)\) and use probability scale \(B:=4096L/m_1\).

On the classification event used in the analysis, light cells satisfy \(p_k\le B/4\), hence \(s_{ak}/B\le1/4\).

---

## Estimating probability powers

For each light cell, average products involving distinct observations:

- One outcome observation in arm-cell \((a,k)\).
- \(j\) additional arm-cell memberships.
- One additional cell membership, with either treatment arm.

Their aggregate formula is

\[
U_{k,a,j}
=
\frac{S_{ak}^{(1)}}{M}\cdot
\frac{\bigl(N_{ak}^{(1)}-1\bigr)_{j}\,\bigl(N_k^{(1)}-j-1\bigr)}{(m_1)_{j+2}},
\]

where \(S_{ak}^{(1)}\) is the arm-cell outcome total, \(N_{ak}^{(1)}\) its count, and \((N)_r=N(N-1)\cdots(N-r+1)\).

Independence across distinct observations gives the population expectation

\(E[U_{k,a,j}]=p_k s_{ak}^{\,j}z_{ak}\).

The three factors correspond to the final cell membership, the \(j\) arm-cell memberships and the single outcome observation. One outcome per product means higher polynomial orders require no higher outcome moments.

---

## Weighted reciprocal approximation

The light-cell target contains reciprocals of arm-cell probabilities.

Let \(x=s_{ak}/B\). The coefficient polynomial

\(\sum_{j=0}^{K_n-2}g_{K_n,j}x^j\)

approximates \(1/x\) for \(0<x\le1/4\). Here \(K_n\) is the degree parameter and \(g_{K_n,j}\) are shifted-Chebyshev coefficients.

The useful guarantee is **weighted**:

\(x^2\left|\sum_{j=0}^{K_n-2}g_{K_n,j}x^j-1/x\right|\le K_n^{-2}\).

Uniform accuracy for the reciprocal near zero is unnecessary. The ATE multiplies that reciprocal by \(p_kz_{ak}\).

Bounded means give \(|z_{ak}|\le s_{ak}/2\); overlap gives \(p_k/s_{ak}\le1/\epsilon\). Together they bound the normalized cell-contribution error by \(B/(\epsilon K_n^2)\), including both arms.

---

## Signed polynomial correction

Replace each population product by its unbiased distinct-observation statistic:

\[
\widehat P_k
:=
\sum_{a\in\{0,1\}}(-1)^{1-a}
\sum_{j=0}^{K_n-2}\frac{g_{K_n,j}}{B^{j+1}}U_{k,a,j}.
\]

This is cell \(k\)’s normalized polynomial contribution. The arm signs subtract controls from treated outcomes.

Its expectation is

\(E[\widehat P_k]=\sum_{a\in\{0,1\}}(-1)^{1-a}\frac{p_kz_{ak}}{B}\sum_{j=0}^{K_n-2}g_{K_n,j}(s_{ak}/B)^j\).

Compare this with the target \(p_k(z_{1k}/s_{1k}-z_{0k}/s_{0k})\).

The polynomial replaces each reciprocal; the factorial statistic estimates every resulting probability product without dividing by an observed count.

This follows the large-alphabet approximation strategy of Jiao et al. (2015).

---

## Combining contributions

Add ordinary heavy-cell contributions and polynomial light-cell contributions:

\[
T_n^{\mathrm{poly}}
:=
M\operatorname{clip}_{[-1,1]}
\left(
\sum_{k\in\widehat{\mathcal H}}\widehat h_k
+
\sum_{k\in\widehat{\mathcal L}}\widehat P_k
\right).
\]

The sets \(\widehat{\mathcal H}\) and \(\widehat{\mathcal L}\) are the pilot-classified heavy and light cells.

The sum estimates the ATE in units of \(M\); multiplication returns to outcome units.

The construction estimates the aggregate contribution of rare cells. It does not require a reliable treatment-control contrast in every light cell.

---

## The logarithmic bias gain

A light cell’s normalized approximation error is at most \(B/(\epsilon K_n^2)\).

Summing over at most \(d\) cells gives aggregate bias at most \(dB/(\epsilon K_n^2)\).

Our calibration uses:

- Probability scale \(B:=4096L/m_1\).
- Degree \(K_n:=\lfloor\alpha_0L\rfloor\), with a sufficiently small fixed constant \(\alpha_0\).
- Logarithmic factor \(L=\log(en)\).

The probability scale grows with one logarithm; the approximation denominator grows with its square.

Thus aggregate bias is at most a constant times \(d/(nL)\). Squaring gives the remainder \(d^2/(n^2L^2)\).

The logarithmic improvement comes from weighted approximation accuracy. Can its variance remain controlled?

---

## Variance control

Increasing degree improves approximation but enlarges coefficients.

For a fixed light-cell set \(S\), an estimation block of size \(m\), degree \(K\), and probability scale \(B\), our covariance bound gives

\[
\operatorname{Var}_{Q_P^{(m)}}\!\left(\sum_{k\in S}\widehat P_k\right)
\le
\frac{C_{\epsilon}}{m}
+
C_{\epsilon}6^{2K}
\left\{
dB^2+\frac{d^2K^2B^2}{m}
\right\}.
\]

This bounds the variance of the aggregate light contribution. The factor \(6^{2K}\) records coefficient growth; the remaining terms account for repeated-cell and cross-cell dependence.

With \(m=m_1\), \(B:=4096L/m_1\) and \(K_n:=\lfloor\alpha_0L\rfloor\), the small degree multiplier keeps both correction terms bounded by a constant times \(1/n+d^2/(n^2L^2)\).

Adding squared approximation bias, heavy-cell error and pilot-classification error gives polynomial risk at most a constant times \(M^2\{1/n+\min(1,u_{n,d})\}\), where \(u_{n,d}=d^2/\{n^2\log^2(en)\}\).

---

## Choosing the branch

Compare the polynomial and borrowing remainders:

\[
u_{n,d}:=\frac{d^2}{n^2\log^2(en)}.
\]

This prices rare-cell approximation.

\[
h_{n,d,\sigma}:=\sigma^2+\frac{d}{n^2}.
\]

This prices heterogeneity and scarce crossed-cell comparisons.

\[
\widehat\tau_n^{\star}:=
\begin{cases}
T_n^{\mathrm{col}},&h_{n,d,\sigma}\le\min\{1,u_{n,d}\},\\
T_n^{\mathrm{poly}},&u_{n,d}<\min\{1,h_{n,d,\sigma}\},\\
0,&\text{otherwise}.
\end{cases}
\]

The choice is deterministic in known \(n,d,\sigma\). The zero branch supplies the outcome-scale cap because \(|\tau(P)|\le M\).

The selector converts two complementary estimation mechanisms into the main upper bound.

---

## Lower-bound mechanism

Two binary hard families from Zeng et al. (2024) explain the lower benchmark.

**Homogeneity:** a family with a common cell effect gives the unavoidable scale \(M^2\{n^{-1}+\min(1,d/n^2)\}\).

**Radius-sensitive difficulty:** attenuate a hard binary family’s responses. Let \(\lambda=\sigma/2\).

\[
B'(a)\sim\operatorname{Bernoulli}\!\left\{\frac12+\lambda\left(B(a)-\frac12\right)\right\},
\]

Here \(B(a)\) is a binary potential response and \(B'(a)\) its randomized replacement.

\[
Y(a):=M\{B'(a)-1/2\}.
\]

This centers and scales the replacement into our outcome model.

The same randomization applies to every competing law, so it cannot make them easier to distinguish. It contracts treatment-effect separation by \(\sigma/2\), producing the lower term \(M^2\sigma^2\min\{1,u_{n,d}\}\).

---

## Matched regimes

Keep our model assumptions, known \(M,\sigma\), and fixed overlap.

@informal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d: Under our fixed-overlap model, for every \(\underline\sigma>0\) and \(\underline\sigma\le\sigma\le2\), the known-radius selector is minimax optimal in order for all \(n,d\ge1\), \(M\ge1\).

| Regime | Matched mean-squared risk, up to constants |
|---|---|
| Exact homogeneity: \(\sigma=0\) | \(M^2\{n^{-1}+\min(1,d/n^2)\}\) |
| Unrestricted effects: \(\sigma=2\) | \(M^2\{n^{-1}+\min(1,u_{n,d})\}\) |
| Radius bounded away from zero | \(M^2r_{n,d,\sigma}\) |
| Saturation or baseline dominance | \(M^2r_{n,d,\sigma}\) |

Here \(r_{n,d,\sigma}=n^{-1}+\min\{1,u_{n,d},h_{n,d,\sigma}\}\).

For the last row, define \(b_{n,d}=n^{-1}+d/n^2\). Matching holds when \(1\le u_{n,d}\), \(u_{n,d}\le Kb_{n,d}\), or \(\sigma^2\le Kb_{n,d}\), for any fixed comparison factor \(K\ge0\).

Our homogeneous example has linear sparse-cell cost because available comparisons can estimate one common effect.

---

## Open questions

The remaining matching problem concerns heterogeneity radii that shrink with sample size.

\[
L:=\log(en),\qquad
b:=n^{-1}+\frac{d}{n^2},\qquad
u:=\frac{d^2}{n^2L^2}.
\]

Here \(b\) is the homogeneity baseline and \(u\) the polynomial remainder. A diverging gap between the proved benchmarks can occur only where

\[
b\ll u\ll1,
\qquad
b\ll\sigma^2\ll1,
\]

meaning that both remainders vanish but remain much larger than the baseline.

- Can a stronger lower bound reach the selector benchmark \(M^2\{b+\min(u,\sigma^2)\}\)?
- Can a better estimator approach the product benchmark \(M^2(b+\sigma^2u)\)?
- Unknown \(M,\sigma\), changing overlap and inference require further analysis.

---

## Takeaways

- **Near homogeneity permits borrowing:** altered cell weights cause little bias, and sparse comparisons cost \(d/n^2\).
- **Polynomial adjustment repairs rare-cell ratios:** distinct-observation products estimate a weighted reciprocal approximation; logarithmic degree gives aggregate bias of order \(d/(nL)\).
- **Known heterogeneity determines the choice:** our selector attains the better benchmark, with matching minimax bounds in the homogeneous, fixed-positive-radius, saturation and baseline-dominance regimes.

---

## Appendix: Selector upper bound

With known outcome scale and heterogeneity radius, the selector attains the all-alphabet upper benchmark.

@formal thm:frontier-upper-all-d

---

## Appendix: Radius-sensitive lower bound

Binary hard families transferred through a radius-dependent channel give the all-alphabet lower benchmark.

@formal thm:radius-channel-converse-all-d

---

## Appendix: Two-sided minimax bracket

The constructive upper bound and unavoidable lower bound apply to the same real-outcome model class.

@formal thm:two-sided-minimax-bracket-all-d

---

## Appendix: Matched regimes

The selector is optimal in the matched regimes, and a diverging benchmark gap is localized to shrinking radii.

@formal thm:fixed-interior-tightness-and-shrinking-radius-gap-all-d
