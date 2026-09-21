# Substrate requirement: bootstrap-smooth-z-estimators

## Goal
Bootstrap validity for finite-dimensional Z-estimators with smooth estimating functions (OLS, IV,
GMM with differentiable moments, logit/probit MLE): a constructor of `BootstrapAsymLinear` for any
continuous linear functional of the estimator, from the conditions users already verify for
asymptotic normality.

## Provides (API contract)
Dependencies are READY (verified 2026-09-17). Data side, in paths this session owns:
`SmoothZEstimatorRegularity ψ θ₀ P` (`Stat/MEstimation/SmoothZEstimator.lean`) with fields
`identification`, `score_meas`, `score_finite_var`, `deriv`, `hasFDeriv`, `deriv_at_target_meas`,
`deriv_at_target_integrable`, `deriv_lipschitz` (an integrable Lipschitz constant for the derivative,
GLOBAL in θ), `jacobianInv`, `jacobian_inverse`, plus `reg.influence`; and
`zEstimator_asymLinear_of_smoothScore` / `..._of_sampleFn`
(`Stat/MEstimation/SmoothZEstimatorSampleFn.lean`), whose only further hypotheses are
`hConsistent` (θ̂ → θ₀ in probability) and `hMoment` (the normalized score at θ̂ is o_P(1)); the √n
rate is derived, no equicontinuity is assumed. Feasible GMM with a general weight matrix:
`feasibleGMM_asymLinear_of_smoothMoment` (`Stat/GMM/SmoothFeasibleGeneral.lean`).
Bootstrap side: everything in `Stat/Bootstrap/` — `BootstrapAsymLinear` and its interval API
(`Stat/Bootstrap/AsymptoticLinear/`), the Efron resampling law and exact moments
(`EfronResampling/`), the a.s. bootstrap mean CLT (`EfronResampling/Mean/`), and from wave 4
(`Stat/Bootstrap/SmoothFunctionOfMeans/`) the reusable bootstrap weak law
`bootstrapMean_sub_dataMean_tendsto_zero_ae`, its vector form
`bootstrapMeanVec_sub_dataMean_tendsto_zero_ae`, conditional Chebyshev tightness
`bootstrapMean_chebyshev` / `scaledBootstrapMeanDifferenceVec_conditionallyBounded`, outer tightness
`scaledBootstrapMeanDifferenceVec_outer_tight`, and `smoothRemainder_isLittleO`.
Setting: parameter space a finite-dimensional normed space `E`; score `ψ : E → X → E`; estimator
as a statistic of the sample vector, `est : (n : ℕ) → (Fin n → X) → E`; target `θ₀`; a continuous
linear functional `c : E →L[ℝ] ℝ` (a coefficient, contrast, or linear combination).
- Constructor `BootstrapAsymLinear.zEstimator`: under
  (i)+(ii) one `SmoothZEstimatorRegularity ψ θ₀ P` value (it already bundles identification,
      measurability, finite score variance, the differentiable score, the integrable Lipschitz
      derivative constant and the Jacobian inverse) — do NOT restate these by hand;
  (iii) `est` solves the estimating equation on the data and on resamples, with probability tending
      to one (data) / bootstrap probability tending to one in μ-probability (resamples);
  (iv) consistency of `est` for `θ₀` on the data, and of the bootstrap replicate `est n x*` for
      `θ₀` in bootstrap probability, in μ-probability;
  (v) non-degeneracy `0 < ∫ (c (J₀⁻¹ ψ θ₀ z))² dP`,
  the scalar estimator `n x ↦ c (est n x)` satisfies
  `BootstrapAsymLinear S (c ∘ est) (c θ₀) (fun z => −c (J₀⁻¹ (ψ θ₀ z)))`.
- User corollaries: percentile and basic CI coverage for `c θ₀`; OLS coefficient instance; the
  feasible (two-step) GMM estimator, reusing `feasibleGMM_asymLinear_of_smoothMoment` for the data side.
- Optional (if within budget): derive (iv) for resamples from compactness of the parameter set,
  unique zero of the population score, continuity in θ, and an integrable envelope
  `sup_θ ‖ψ θ z‖` (bootstrap uniform weak law).

## Statement / milestones
1. Taylor expansion of the sample score around `θ₀` with the Lipschitz derivative; the Jacobian
   average at an intermediate point converges to `J₀` (weak law for `∂ψ(θ₀,·)` plus
   `‖θ̄ − θ₀‖ · mean L`), on the data and on resamples (bootstrap weak law from study
   `bootstrap-smooth-function-of-means`).
2. Invert: `√n (est − θ₀) = −J₀⁻¹ n^{-1/2} ∑ ψ(θ₀, Zᵢ) + o_P(1)`, and the bootstrap analogue
   centred at `est n x`, using bootstrap tightness of `n^{-1/2} ∑ (ψ(θ₀, x*ᵢ) − mean_x ψ(θ₀,·))`.
3. Apply `c`; build the structure.
4. Corollaries and OLS instance.

## Standard reference
Newey & McFadden (1994), *Handbook of Econometrics* Vol. 4, Theorem 3.1 (smooth Z-estimators);
Hahn (1996, Econometric Theory 12:187) for the bootstrap of GMM; van der Vaart & Wellner (1996),
Section 3.9.3; Horowitz (2001), *Handbook of Econometrics* Vol. 5, Section 2.

## Intended reuse
Bootstrap confidence intervals for regression, IV and GMM coefficients in Causalean and CausalSmith.

## May assume / must derive
- May assume: studies `bootstrap-percentile-intervals` and `bootstrap-smooth-function-of-means`;
  the (post-refactor) Causalean Z-estimator regularity structure and asymptotic-linearity results.
- Must derive: both linearizations and the constructor from (i)–(v). No stochastic-equicontinuity
  or bootstrap-Donsker hypothesis may be assumed; smoothness (ii) replaces it.

## Non-goals
- Non-smooth scores (quantile regression), semiparametric or cross-fitted estimators,
  Hadamard-differentiable functionals, bootstrap-t intervals, bootstrapping the J test (needs
  recentred moments, Hall–Horowitz 1996).
