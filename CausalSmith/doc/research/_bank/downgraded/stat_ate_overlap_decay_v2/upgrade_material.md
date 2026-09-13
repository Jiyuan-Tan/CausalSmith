# Authoritative upgrade material: sharp ATE weak-overlap minimax frontier

This note is the operator-supplied mathematical basis for upgrading the failed
`stat_ate_overlap_decay/v1` run. Treat it as authoritative input, while still
subjecting every claim to the pipeline's normal mathematical, novelty, and Lean
verification gates. Reuse the sound parent artifacts instead of re-deriving
them.

## Repaired experiment

Study the full-population ATE with deterministic public nuisance functions
`(m0,m1,p) = (g0_tilde,g1_tilde,e_tilde)` and global L2 certificates
`||ma-ga||_2 <= ra`, `||p-e||_2 <= re`. The minimax supremum is over admissible
law/public-function pairs, and the public functions are identical within each
lower-bound family.

Require positivity `P(e(X)>0)=1`. Without it, an atom at `e=0` makes the treated
potential-outcome regression unidentifiable while preserving the observed law.

Fix shell constants uniformly across the class:

    c_- u^kappa <= P(u/2 < e <= u) <= c_+ u^kappa,
    0 < u <= lambda_0.

Then positivity plus dyadic summation yields uniform tail order
`P(e<=lambda) asymp lambda^kappa`, and
`E[(e vee lambda)^(-1)] asymp v_kappa(lambda)^2`. Without uniform shell
constants, the comparison fails; an additional fixed mass at epsilon_n gives a
counterexample.

For matching lower bounds assume positive treated-noise allowance and a class
rich enough to contain the explicit constructions. A sufficient fixed-constant
condition is
`c_- <= (1-2^(-kappa))/(4 lambda_0^kappa)` and
`c_+ >= 2^(kappa-1)/lambda_0^kappa`. The upper bound does not need this richness
condition.

## Sharp theorem

Define

    Q_kappa(n,r) =
      n^(-1/2) vee n^(-kappa/2) r^(1-kappa),          0<kappa<1;
      n^(-1/2) sqrt(1 + log_+(n r^2)),                kappa=1;
      n^(-1/2),                                       kappa>1.

The corrected rate is

    rho_n = Q_kappa(n,r1)
            + r1 n^(-kappa/[2(kappa+1)])
            + r1 re^(kappa/(kappa+2))
            + r0 re.

For the repaired uniform public-approximation experiment, both minimax absolute
risk and minimax root mean-squared risk are equivalent to `rho_n`. There is also
a fixed-probability lower bound at this scale. An ordinary clipped doubly robust
average attains absolute-error and uniform-in-probability rates; the median of
five independent block versions attains root-MSE.

The four obstructions are: outcome noise/population averaging; regression error
hidden in a tail region with no treated observations; joint propensity/treated
outcome uncertainty; and the ordinary control-arm nuisance interaction.

## Corrected upper bound

Project the public propensity to
`p_circ = clip(p,0,1-eta_+/2)`, and define
`q_lambda = p_circ vee lambda`, `e_lambda = e vee lambda`. Compare the feasible
clipped score to the score using the same approximate regressions and the true
denominators. For `h1=m1-g1`,

    E[h1^2 (1-D/e_lambda)^2] <= (1+lambda^(-1)) r1^2.

Thus the old stochastic penalty `r1/(sqrt(n) lambda)` improves to
`r1/sqrt(n lambda)` without smoothness or stronger moments. Control the
regression-propensity interaction in first moment:

    E[D |h1| |1/q_lambda - 1/e_lambda|] <= r1 re/lambda.

The resulting bound is

    E|T_lambda-tau| <= C [
      v_kappa(lambda)/sqrt(n)
      + r1/sqrt(n lambda)
      + re/(sqrt(n) lambda^(3/2))
      + r1 lambda^(kappa/2)
      + r1 re/lambda
      + r0 re ].

Let `b_o=n^(-1/(kappa+1))`, `b_e=re^(2/(kappa+2))`, and
`b_g=(n r1^2)^(-1)`. Below a fixed cap, select the maximum of these scales for
`kappa<=1`, and of `b_o,b_e` for `kappa>1`. The propensity-noise term introduces
no extra rate component. Handle cap-binding cases explicitly.

For root-MSE, if five independent block estimators have mean absolute error at
most `K rho_n`, the median tail is at most
`min(1,10(K rho_n/u)^3)`, whose integral gives squared risk at most
`21 K^2 rho_n^2`.

## Least-favourable families

Use a common causal model with masses `P(R=0)=P(R=1)=1/4`, `P(R=2)=1/2`.
On `R=0,1`, let `U` have density proportional to `u^(kappa-1)` on
`(0,lambda_0]`, add an independent uniform coordinate `V`, and set the baseline
propensity to `U` on the two tail reservoirs and to a fixed regular `p_*` on
`R=2`. Keep `R=0` untouched. Perturbations on `R=1` preserve `e>=U/2`; every
individual alternative obeys the same uniform shell bounds. Generate
`Y(1)=g1(X)+sigma Z`, `Y(0)=g0(X)` with conditionally independent Gaussian
treated noise and sufficiently small fixed positive variance.

Required lower-bound components:

1. For `0<kappa<1`, use `g1,+/- = +/- h 1{e0<=s}` with
   `h=r1/(2 sqrt(m_s))` and `s` proportional to `1/(n r1^2)`. Product KL is
   bounded and target separation is
   `n^(-kappa/2) r1^(1-kappa)`; when localization exceeds the tail cap this is
   absorbed by the parametric floor.
2. At `kappa=1`, perturb across scales with
   `f=a/e0 1{s<=e0<=lambda_0}`, `s=(n r1^2)^(-1)`,
   `a` proportional to `1/sqrt(n log(lambda_0/s))`. This proves the genuine
   factor `sqrt(1+log_+(n r1^2))/sqrt(n)`.
3. For the no-treated-observations obstruction use the same two-point
   regression perturbation with `s` proportional to `n^(-1/(kappa+1))`.
   Couple the samples; they differ only if a treated observation lands in the
   perturbed tail. Product TV stays bounded and the target separation is
   `r1 n^(-kappa/[2(kappa+1)])`.
4. For the weak-tail nuisance product, on
   `B_s={R=1, s<U<=2s}` partition `V` into `N` cells with signs `Z_j`. Under
   hypothesis `theta`, bias each sign by fixed `delta=1/4`, set
   `g1=h Z_j`, `h=r1/(2 sqrt(m))`, and
   `e_{theta,Z}=U/(1+theta delta Z_j)`, while publicly supplying
   `m0=m1=0,p=e0`. The cancellation
   `P_theta(Z_j=z)e_{theta,Z}=U/2` makes one-row mixtures identical. Choose
   `s` proportional to `re^(2/(kappa+2))`; target separation is
   `r1 re^(kappa/(kappa+2))`. With `N` sufficiently larger than `n^3`, a
   collision lemma bounds sample-mixture KL and prior target concentration,
   yielding a fuzzy-hypothesis lower bound. Every fixed-sign law—not merely the
   mixture—satisfies the causal and nuisance class.
5. Repeat the cancellation on the regular control region to obtain `r0 re`.
   Obtain the root-n floor with exact nuisance functions by perturbing the
   covariate distribution of a known heterogeneous treatment effect.

The maximum of the component lower bounds is equivalent up to a constant to
their sum.

## Corrected phase diagram and comparison with the failed parent

For polynomial radii, the exponent is

    beta_kappa = min {
      1/2,
      kappa/2 + (1-kappa)a1          [only 0<kappa<1],
      a1 + kappa/[2(kappa+1)],
      a1 + kappa a_e/(kappa+2),
      a0+a_e }.

The failed parent's exponent used `a1+kappa/[2(kappa+2)]` in place of the third
entry. The old proposed frontier is nevertheless correct throughout
`a_e<=1/2`, because the nuisance-product term dominates the old stochastic
penalty. It is false in general: at
`(a0,a1,a_e)=(1/2,1/10,1), kappa=5`, the actual rate is root-n while the old
frontier is `n^(-16/35)`.

Let `B=min(1/2,a1+a_e,a0+a_e)`. If `B<=a1`, there is no polynomial
deterioration. Otherwise, with `x=B-a1>0`, the corrected threshold is the maximum
of

    x/(1/2-a1),  2x/(1-2x),  2x/(a_e-x),

with zero denominators interpreted as infinity. Deterioration occurs exactly
for `0<kappa<kappa_dagger`.

At `kappa=1`, the exact non-polynomial factor is
`sqrt(1+log_+(n r1^2))`; under polynomial radii this produces
`sqrt(log n/n)` only when the rate exponent is `1/2` and `a1<1/2`.

## Honest inference and framing

For fixed `alpha in (0,1/4)` and supplied radii/class constants, construct an
honest confidence interval centered at the median-of-five estimator with
uniform expected length of order `rho_n`. The same two-point and fuzzy families
give the matching lower bound for every honest interval. These are bias-aware
intervals, not a claim of Gaussian/Wald validity. Conditional high-probability
first-stage certificates transfer the probability rate, but do not alone imply
unconditional MSE or finite-sample honest coverage.

Frame the contribution as **Global Prediction Accuracy and the Limits of
Causal Inference under Weak Overlap**: the exact price of knowing only global L2
prediction-error guarantees. Compare carefully with Jin–Syrgkanis,
Bonvini–Kennedy–Dukes–Balakrishnan, Khan–Tamer, Dorn, Heiler–Kazak, and Rothe.
Do not claim priority from the comparison. Explicitly leave adaptation to
unknown tail/radii, interval calibration, bounded-treatment-effect variants,
and arbitrarily restrictive shell constants outside the theorem.

