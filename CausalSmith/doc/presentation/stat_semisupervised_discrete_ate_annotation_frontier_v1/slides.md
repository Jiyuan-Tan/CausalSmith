# How Much Are Outcome Labels Worth?

Records without outcomes improve treatment-effect estimates by supplying better weights; outcome labels set the remaining accuracy limit.

---

## Motivation

Chart review makes outcomes expensive; treatment and covariates may already be recorded broadly.

- \(n\) records contain covariates \(X\), treatment \(A\), and outcome \(Y\).
- \(m\) additional records contain only \((X,A)\).
- Treatment and outcome are binary; covariates take \(d\) known values.

Cheng et al. (2021) study this annotation problem in electronic health records.

How accurately can we estimate the average treatment effect (ATE) using these two sources of information?

---

## Standard approach

Estimate treated and control outcome means within each covariate cell, then average:
\(\sum_x\widehat p_x(\widehat\mu_{1x}-\widehat\mu_{0x})\).

Here \(\widehat p_x\) estimates the cell’s population frequency, and \(\widehat\mu_{ax}\) estimates its outcome mean in arm \(a\).

Nearly empty treatment arms make the estimated means unreliable.

Zeng et al. (2026), the closest supervised benchmark, obtain:

- Plug-in mean-squared error (MSE) upper bound of order \(d^2/n^2+1/n\), for all \(d\).
- Minimax lower bound of order \(d^2/(n^2\log^2 n)+1/n\), for \(d\lesssim n\log n\).

Can auxiliary records and better rare-cell estimation close this logarithmic gap?

---

## Key idea

Estimate outcome success masses from labels and treatment weights from pooled records.

Use stabilized inverse counts in common cells and polynomial weights in rare cells.

Write \(N=n+m\) for pooled size and \(\ell_n=\log(en)\). The optimal risk scale is

\[
r_\epsilon(n,m,d)
:=
\min\!\left\{
1,\frac1n+\frac{d^2}{N^2\ell_n^2}
\right\}.
\]

The first term measures outcome uncertainty; the second measures treatment–covariate uncertainty. The cap reflects the bounded target.

Here \(0<\epsilon<1/2\) is fixed: both arms have conditional probability at least \(\epsilon\) in every occupied cell.

@informal thm:sharp-annotation-frontier: For independent same-population samples, \(n\ge1,m\ge0,d\ge2\), and fixed occupied-cell overlap \(0<\epsilon<1/2\), minimax MSE lies between positive \(\epsilon\)-dependent constants times \(r_\epsilon(n,m,d)\).

---

## Example

Take two equally likely cells, treatment probability one-half in each, and zero control outcome means. Let cell one’s treated outcome mean be one.

Here \(p_1=P(X=1)=1/2\), \(e_1=P(A=1\mid X=1)=1/2\), and
\(q_{11}=P(X=1,A=1,Y=1)=1/4\). This is a **joint success mass**, not a conditional mean.

With one labeled record \(\mathcal L_1\) and one auxiliary record \(\mathcal U_1\), consider estimating success mass and multiplying by twice the auxiliary cell indicator:

\[
\mathbb E\!\left[
2\mathbf 1\{\mathcal L_1=((1,1,1))\}
\left(\mathbf 1\{\mathcal U_1=((1,0))\}+\mathbf 1\{\mathcal U_1=((1,1))\}\right)
\right]
=2q_{11}p_1,
\]

This candidate weight has mean \(2p_1\). It adds an unwanted factor \(p_1\), giving \(1/4\).

The correct weight is \(1/e_1=2\): the treated contribution is \(q_{11}/e_1=2q_{11}=1/2\).

Independence lets us multiply estimates. It does not make the candidate weight correct.

---

## Model and assumptions

For population law \(P\), let \(p_x(P)\) be cell \(x\)’s frequency and \(\mu_{ax}(P)\) its conditional outcome mean in arm \(a\). Our target is

\[
\tau(P):=\sum_{x=1}^{d}p_x(P)\bigl(\mu_{1x}(P)-\mu_{0x}(P)\bigr).
\]

This averages within-cell treated–control differences using population frequencies.

- **Sampling:** independent records from one population, with independence between the labeled and auxiliary samples.
- **Unrestricted cells:** outcome means and treatment probabilities may vary freely across cells.
- **Overlap:** in every occupied cell, treatment probability \(e_x\) satisfies

\[
\epsilon \le e_x \le 1-\epsilon .
\]

Overlap guarantees both arms occur; it allows arbitrarily rare cells. Our example satisfies it with \(\epsilon=1/4\).

Consistency equates observed outcomes with received-treatment potential outcomes. Conditional exchangeability makes treatment independent of potential outcomes within cells. Together with overlap, these give \(\tau(P)\) its causal ATE interpretation.

---

## Main result

Let \(\mathcal M_{d,\epsilon}\) denote the unrestricted overlap class.

Minimax risk \(R_\epsilon(n,m,d)\) is the smallest worst-case MSE among all estimators using both samples.

Under our sampling and overlap conditions, for every \(n\ge1,m\ge0,d\ge2\),

\[
c_\epsilon r_\epsilon(n,m,d)
\le R_\epsilon(n,m,d)
\le C_\epsilon r_\epsilon(n,m,d),
\]

The positive constants \(c_\epsilon,C_\epsilon\) depend only on overlap. Our hybrid estimator attains the upper bound; the lower bound applies to every estimator.

At \(m=0\), polynomial correction closes the supervised logarithmic gap. Increasing \(m\) reduces the treatment–covariate term.

For our two-cell setting, minimax MSE is of order \(1/n\) for every auxiliary size: outcome uncertainty already governs the rate.

---

## Independent information pools

Sample splitting assigns independent records to three jobs:

- **Outcome pool:** labels estimate success masses.
- **Pilot pool:** pooled treatment–covariate records select the weighting rule.
- **Weight pool:** separate pooled records estimate the selected weights.

For analysis, Poisson sample sizes make counts independent across cells:

\[
S_{ax}\sim \operatorname{Poi}(u q_{ax}),
\qquad
K_{ax}\sim \operatorname{Poi}(t s_{ax}),
\qquad a\in\{0,1\},\ x\in[d],
\]

Here \(q_{ax}=P(X=x,A=a,Y=1)\) is joint success mass, and \(s_{ax}=P(X=x,A=a)\) is arm mass.

The counts \(S_{ax},K_{ax}\) come from the outcome and weight pools; their effective sizes \(u,t\) are proportional to \(n,N\).

The required arm contribution is \(q_{ax}p_x/s_{ax}=p_x\mu_{ax}\). In our example, \(p_1/s_{11}=2\), exactly the required weight.

---

## Inverse-count baseline

Estimate success mass by \(S_{ax}/u\) and its weight by
\((K_{0x}+K_{1x}+1)/(K_{ax}+1)\).

Adding one keeps the ratio finite when an arm count is zero. Let \(Z^H\) sum the resulting treated minus control contributions.

Under overlap,

\[
\left|E_P Z^H-\tau(P)\right|
\le
C\min\{1,d/t\},
\qquad
\operatorname{Var}_P(Z^H)
\le
C\left(u^{-1}+t^{-1}\right).
\]

The constant \(C\) depends only on overlap. Variance already follows the label and pooled-record budgets.

The obstacle is bias: an arm with few observations leaves some target contribution missing, and these errors can accumulate across cells.

How can we recover more of each rare cell’s contribution?

---

## Polynomial correction

Replace the inverse weight in rare cells by a polynomial in the arm masses.

Let \(L\ge2\) control degree, \(B>0\) be the rare-cell mass scale, and \(T_L\) be the degree-\(L\) Chebyshev polynomial. Define

\[
H_L(z)=\frac{1-T_L(1-2z)}{2L^2},\qquad
E_L(z)=\frac{H_L(z)}z,\qquad
G_L(z)=\frac{1-E_L(z)}z,
\]

The quotients continue as polynomials at zero. The resulting weight is

\[
W_{a,L}(s_0,s_1)=\frac{s_0+s_1}{B}G_L(s_a/B),
\]

Here \(s_0,s_1\) are the cell’s arm masses; \(z=s_a/B\) is its scaled arm mass. The weight approximates \((s_0+s_1)/s_a\).

Jiao et al. (2015) develop polynomial approximation for rare regions of discrete functional estimation.

We need accuracy in the weighted contribution, even where the reciprocal itself is difficult to approximate.

---

## Contribution error

The polynomial leaves a residual fraction \(E_L(z)\). For \(z\in[0,1]\),

\[
0\le E_L(z)\le 1,
\qquad
zG_L(z)+E_L(z)=1,
\]

Thus \(zG_L(z)\) is the recovered fraction. For \(z>0\),

\[
E_L(z)\le (L^2z)^{-1}.
\]

For a cell with \(p_x\le B\), success mass times the polynomial weight equals
\(p_x\mu_{ax}[1-E_L(s_{ax}/B)]\).

The missing contribution is \(p_x\mu_{ax}E_L(s_{ax}/B)\).

- Overlap gives \(s_{ax}\ge\epsilon p_x\).
- Its missing contribution is therefore at most \(B/(\epsilon L^2)\): cell frequency cancels the reciprocal arm mass.

Across \(d\) cells, bias is at most a constant times \(dB/L^2\). We control absolute contribution error without requiring uniformly accurate inverse weights near zero.

---

## Estimating polynomial weights

The coefficients are known; the cell masses are unknown.

Expand the weight in mass powers and replace each power by a falling-factorial count statistic:

\[
\widehat W_{a,L}(K_0,K_1)
=
\sum_{r_0,r_1}c_{a,r_0,r_1}
\frac{(K_0)_{r_0}(K_1)_{r_1}}{t^{r_0+r_1}}.
\]

Here \(c_{a,r_0,r_1}\) are polynomial coefficients and \(r_0,r_1\) index powers.
The falling factorial is \((k)_r=k(k-1)\cdots(k-r+1)\), with \((k)_0=1\).

Poisson factorial moments estimate mass powers without bias, so this estimated weight has expectation \(W_{a,L}\).

Independence from the outcome pool makes its product with \(S_{ax}/u\) estimate exactly the polynomial contribution.

The approximation error survives estimation unchanged; sampling adds variance.

---

## Hybrid estimator

An independent pilot count \(J_x\) selects the branch using threshold \(k_0\):

\[
Z_x
=
\begin{cases}
\dfrac{S_{1x}}u\,\widehat W_{1,L,x}
-
\dfrac{S_{0x}}u\,\widehat W_{0,L,x},
& J_x\le k_0,\\[1.2em]
\dfrac{S_{1x}}u\,\dfrac{K_{0x}+K_{1x}+1}{K_{1x}+1}
-
\dfrac{S_{0x}}u\,\dfrac{K_{0x}+K_{1x}+1}{K_{0x}+1},
& k_0<J_x.
\end{cases}
\]

Each \(Z_x\) estimates one cell’s treated–control contribution: polynomial correction for small pilot counts, stabilized ratios otherwise.

The independent pilot protects the weight calculation from selection using the same counts; calibrated pilot tails control routing errors.

Sum across cells and clip to \([-1,1]\), the ATE’s possible range.

Averaging over Poisson prefix lengths gives the fixed-sample estimator \(\widehat\tau^{\mathrm{mix}}_{n,m,d}\). This transfer costs at most a constant times \(1/n\) in the risk bound.

---

## Variance budgets

Polynomial weights amplify noise exponentially with degree. Write \(A_\star=7056\) for the fixed moment-growth constant.

For the hybrid sum before clipping, the two amplified terms fit two budgets: label variance \(1/n\) and squared bias \((dB/L^2)^2\). Constants are suppressed below.

| Amplified term | Budget that absorbs it | Required calibration |
|---|---|---|
| \(A_\star^L\min\{1,dB\}/u\): outcome noise over rare-cell mass | Split between label variance and squared bias by a quadratic inequality | \(L^4A_\star^{2L}\le n\) |
| \(A_\star^L dB^2\): weight noise across rare cells | Label variance when \(d\le L^4A_\star^L\); squared bias above that cutoff | \(L^6A_\star^{2L}\le n\) for the label-budget case |

The first term’s amplification is paid by its calibration inequality. For the second, many cells make the squared-bias budget large enough to absorb it.

Stable-count variance and pilot remainders fit these same budgets under the remaining calibration.

---

## The logarithmic gain

Choose \(L\) proportional to a sufficiently small multiple of \(\log(en)\). Exponential variance growth then fits the labeled-sample budget.

Choose \(B\) proportional to \(L/N\). More pooled records shrink the mass range requiring polynomial correction.

- Bias is at most a constant times \(dB/L^2\).
- Substituting these choices gives bias at most a constant times \(d/(N\log(en))\).
- Squared bias supplies \(d^2/(N^2\ell_n^2)\); variance fits this term plus \(1/n\).

Outcome labels limit polynomial degree. Auxiliary records reduce the mass scale instead.

The prescribed estimator returns zero when its finite calibration fails; failure occurs only at bounded labeled sizes, which the uniform constant covers.

@informal thm:uniform-mixed-upper: Under independent same-population sampling and fixed overlap \(0<\epsilon<1/2\), the hybrid estimator has worst-case MSE at most \(C_\epsilon r_\epsilon(n,m,d)\) for every \(n\ge1,m\ge0,d\ge2\).

---

## The label floor

For a lower bound, keep the treatment–covariate table fixed and vary only outcomes.

Nearby outcome populations can have ATE separation \(h_n=c_\epsilon/\sqrt n\le1/4\), while their labeled samples remain too close for reliable discrimination.

Their auxiliary samples have identical distributions, regardless of \(m\).

Our two-cell example makes this separation of information visible: changing cell one’s treated outcome mean leaves all four treatment–covariate probabilities equal to \(1/4\).

An estimator resolving nearby ATEs would also distinguish the outcome populations. Squared separation forces the label floor.

@informal lem:parametric-label-floor: For fixed \(0<\epsilon<1/2\), every \(n\ge1,m\ge0,d\ge2\) has minimax MSE at least \(c/n\), regardless of auxiliary size.

How can rare cells force the remaining error term?

---

## Approximation and cancellation

The lower bound uses the difficulty of approximating \(p/(p+a)\) by a degree-\(L\) polynomial.

Here \(p\) is a candidate rare-cell mass, \(B\) bounds its range, and
\(a=\gamma_\epsilon B/L^2\) is a positive smoothing scale. The interval is \([a/\kappa,B]\), with \(\kappa=(1-2\epsilon)/\epsilon\).

At this scale, the reciprocal expression retains a constant approximation gap.

Alternating approximation errors supply candidate masses \(p_i\) and signed weights \(w_i\) satisfying

\[
\sum_{i=0}^{L+1}|w_i|=1,\qquad
\sum_{i=0}^{L+1}w_i p_i^j=0\quad\text{for every }0\le j\le L,
\]

but

\[
c_\epsilon\le \sum_{i=0}^{L+1}w_i\,\frac{p_i}{p_i+a}.
\]

The first formula cancels every polynomial through degree \(L\); the second preserves a positive target gap. This is the raw material for two hard-to-distinguish populations.

---

## Shared-table populations

Let \(\sigma\) place signed weight \(w_i\) at each candidate mass; \(|\sigma|\) places absolute weight \(|w_i|\).

Draw each rare-cell raw mass from

\[
\nu(dp)=\frac{a}{p+a}\,|\sigma|(dp)\quad(p\in I),
\qquad
\nu(\{0\})=1-\int_I\frac{a}{p+a}\,|\sigma|(dp).
\]

Here \(I=[a/\kappa,B]\); the remaining probability makes the cell empty.

For positive mass \(p_i\), set treated mass \(s_i=\epsilon(p_i+a)\). The interval guarantees overlap. Keep control means zero.

If \(h(p_i)\) is the sign of \(w_i\), branch \(b\in\{0,1\}\) assigns

\[
\mu_{1i}^{(b)}=\frac{1+(2b-1)h(p_i)}{2}.
\]

This swaps treated means between zero and one according to the sign.

Generate \(k\) cells, add a reservoir cell, and normalize masses. Both branches share the entire treatment–covariate table; only outcomes differ.

---

## Joint likelihood cancellation

Auxiliary counts can reveal the latent cell mass and help interpret labeled outcomes. Identical auxiliary distributions alone therefore do not establish joint indistinguishability.

Expand the joint Poisson likelihood in that latent mass:

| Part of the expansion | What happens |
|---|---|
| Terms with no outcome-bearing difference | Agree across branches |
| Outcome-bearing terms through degree \(L\) | Cancel against the signed moments |
| Higher-degree terms | Remain; their exponential-series tail must be bounded |

An outcome-bearing term contains treated mass \(\epsilon(p+a)\). The drawing factor \(a/(p+a)\) cancels its first factor of \(p+a\).

What remains at low degrees is a polynomial against the signed weights, so its integral vanishes.

Both labeled and auxiliary counts enter the expansion. The next bound controls their **joint** remainder.

---

## Likelihood remainder

For this lower-bound calculation, let \(u\) and \(v\) be labeled and auxiliary Poisson intensities, proportional to \(n\) and \(N\).

The one-cell likelihood bound requires \((u+v)B\le b_\epsilon L\), with a sufficiently small positive overlap-dependent constant \(b_\epsilon\).

For the two one-cell predictive laws \(\mathsf Q_0,\mathsf Q_1\),

\[
\operatorname{TV}(\mathsf Q_0,\mathsf Q_1)
\le C_\epsilon u a\rho_\epsilon^L,
\qquad 0<\rho_\epsilon<1.
\]

Total variation measures how well the joint observations distinguish the branches.

Why does the remainder decay? The exponential-series terms have factorial denominators. Keeping the largest intensity–mass product a small fraction of \(L\) makes the terms beyond degree \(L\) geometrically small.

The factor \(ua\) reflects that a difference must pass through labeled outcomes. Summing across \(k\) cells gives distance at most \(C_\epsilon uka\,\rho_\epsilon^L\).

---

## Calibration against auxiliary size

Choose the lower-bound scales

\[
L=\left\lceil C_\epsilon^\circ \log(en)\right\rceil,\qquad
B=\frac{b_0L}{n+m},\qquad
a=\frac{\gamma_\epsilon B}{L^2},
\]

Here \(C_\epsilon^\circ,b_0,\gamma_\epsilon\) are positive overlap-dependent constants; the lower bound uses a sufficiently large logarithmic degree.

Because \(u+v\) is proportional to \(N\), the remainder depends on pooled size through \(NB\). Shrinking \(B\) as \(L/N\) preserves the tail condition even when \(m\) is arbitrarily large.

The mass budget keeps \(ka\) bounded. Hence the joint distance bound \(C_\epsilon uka\,\rho_\epsilon^L\) is at most a constant times \(n\rho_\epsilon^L\).

A sufficiently large multiple of \(\log(en)\) makes this at most \(1/8\).

More auxiliary records force smaller hard cells; they do not enlarge the calibrated joint remainder.

---

## Number of rare cells

Each generated cell supplies expected target separation at least a constant times \(a\). Choose

\[
k=\min\left\{d-1,\left\lfloor c_\epsilon^\circ(n+m)L\right\rfloor\right\}.
\]

The first limit reserves a reservoir cell. The second keeps total separation bounded: \(a\) is proportional to \(1/(NL)\).

The raw target centers satisfy

\[
c_\epsilon ka
\le
\left|
\theta_1-\theta_0
\right|,
\]

Here \(\theta_b\) is the expected unnormalized ATE in branch \(b\).

Until the mass cap binds, separation grows with the number of cells. At the cap it stays of constant order.

Thus squared separation is at least a constant times
\(\min\{1,d^2/((n+m)^2\log(en)^2)\}\).

---

## Concentration and testing

Write \(\Delta=|\theta_1-\theta_0|\). Normalizing the generated populations must preserve their target separation.

Raw target and total-mass variances are at most \(C_\epsilon kBa\). Relative to squared separation, the controlling ratio is \(B/(ka)\): enough rare cells make it small.

Use the rare-cell construction when

\[
\min\left\{1,\frac{d^2}{(n+m)^2\log(en)^2}\right\}
>
\frac{C_\epsilon}{n}.
\]

The left side is the alphabet term; the right side is the label scale. In this regime, the calibrated cell count supplies concentration.

The joint distance is at most \(1/8\), so reliable testing is impossible. An estimator resolving the concentrated, separated ATEs would provide such a test.

In the remaining regime, the label floor already covers the alphabet term.

@informal thm:common-marginal-converse: Under independent same-population sampling and fixed overlap \(0<\epsilon<1/2\), for every \(n\ge1,m\ge0,d\ge2\), priors with the same treatment–covariate table distribution yield minimax MSE at least \(c_\epsilon r_\epsilon(n,m,d)\).

---

## Open questions

- Sharper implementable tuning at ordinary sample sizes: the explicit calibration is conservative.
- Continuous covariates and treatments or outcomes with more than two values.
- Adaptive annotation and restrictions connecting cellwise outcome means or treatment probabilities.

---

## Takeaways

- Under independent same-population sampling and fixed overlap, optimal MSE follows \(\min\{1,1/n+d^2/(N^2\ell_n^2)\}\). Labels and pooled records supply different information.
- Polynomial weights reduce missing rare-cell contributions; overlap cancels the problematic reciprocal mass. Factorial moments preserve that calculation after estimation, while outcome variance limits degree.
- Moment cancellation removes low-degree likelihood differences. Shrinking rare-cell mass with pooled size controls the remaining tail; separated, concentrated targets then force the matching lower bound.

---

## Appendix: Sharp annotation frontier

The exact statement gives the finite-sample minimax bracket and its endpoint and sequence consequences.

@formal thm:sharp-annotation-frontier

---

## Appendix: Uniform mixed upper bound

The specified hybrid estimator attains the frontier uniformly over the unrestricted overlap class.

@formal thm:uniform-mixed-upper

---

## Appendix: Common marginal converse

Priors with identical treatment–covariate table distributions deliver the matching minimax lower bound.

@formal thm:common-marginal-converse

---

## Appendix: Known marginal limit

For fixed labeled size and alphabet, increasing auxiliary size converges to the exact known-table minimax risk.

@formal thm:known-marginal-limit
