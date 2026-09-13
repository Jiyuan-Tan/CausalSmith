# Minimax Inference For Threshold Clamp Policies

For continuous treatments, we characterize the minimax risk and honest confidence-interval length for a lower-threshold clamp when overlap thins polynomially near the boundary.

---

## Overview

- The policy raises all treatments below the threshold \(\delta_n\), the policy threshold, up to \(\delta_n\).
- This creates a moving atom at the boundary of the post-policy treatment law.
- We estimate the clamp mean by combining a retained-course mean, a lower-tail atom mass, and a boundary regression value.
- The frontier has two pieces: ordinary sampling noise and atom-weighted boundary learning.
- The same frontier governs point estimation, honest interval length, and the causal lift.

@informal thm:minimax-risk: Under the finite-stratum Hölder model with the two-sided polynomial density envelope, the minimax absolute-error risk is at most and at least constant multiples of \(r_n\).

---

## Motivation

- Modified treatment policies are a common way to define feasible effects for continuous treatments.
- A threshold rule is natural when doses below a minimum practical level are reassigned to that minimum.
- In applications, the threshold may move with sample size as investigators probe closer to the support boundary.
- The inferential difficulty is concentrated at the boundary value created by the clamp.
- The question is: how much precision is possible when the data become sparse near that boundary?

@figure clamp-pipeline: Box-and-arrow schematic showing natural treatment A split by threshold δ_n into a retained course above the threshold and a lower-tail atom at δ_n, with the boundary response and retained course combining into the clamp mean.

---

## Related literature

- Díaz et al. (2021), Williams and Díaz (2023), and Hoffman et al. (2024) make modified treatment policies operational for continuous treatments.
- Kennedy et al. (2017) and Bonvini and Kennedy (2026) study continuous-treatment dose-response inference under regular support.
- van der Laan et al. (2022) study stochastic threshold interventions with efficient inference and bands.
- Gaïffas (2005) gives the closest degenerate-design pointwise regression benchmark.
- Low (1997) and Armstrong and Kolesár (2018, 2016) supply the honest interval and modulus perspective.
- Our contribution is the exact deterministic clamp frontier under polynomial thinning and moving thresholds.

---

## Setup

- Observed data are \(O=(X,A,Y)\): finite stratum, continuous treatment, bounded outcome.
- The treatment density in stratum \(x\) is \(\pi_x(a)\).
- The lower-threshold clamp is \(d_\delta(a)=\max\{a,\delta\}\).
- The observed clamp target is the retained mean above the threshold plus the lower-tail atom mass times the boundary regression.
- The first-order object is the atom at \(\delta_n\): its mass shrinks like \(\delta_n^{\kappa+1}\), where \(\kappa\) is the thinning exponent.

@formal def:clamp-functional

---

## Assumptions

- We work with fixed finite strata and i.i.d. sampling.
- Every stratum has nonvanishing mass.
- The treatment density obeys a two-sided envelope \(c_-a^\kappa\le\pi_x(a)\le c_+a^\kappa\) on all of \([0,1]\); it is at the lower endpoint that this thins the design.
- The outcome regression is Hölder smooth with exponent \(\beta\), the smoothness exponent, and radius \(L\).
- These conditions describe the amount of information near the moving threshold.

@formal ass:polynomial-thinning

@formal ass:holder-regression

---

## Information balance

- The threshold regression is learned locally around \(\delta_n\).
- The bandwidth \(h_n\), the local window width, balances local-polynomial bias against local sampling information.
- The resulting Hölder frontier rate combines sampling noise and atom-weighted boundary error.

@formal def:bandwidth

@formal def:frontier

---

## Estimator

- Split the sample into three fixed blocks.
- Use one block for the retained-course mean above \(\delta_n\).
- Use one block for the empirical lower-tail atom masses.
- Use one block for the local-polynomial boundary regression.
- Stabilize by checking the realized total Gram matrix and falling back to a bounded value on singular local designs.

@figure estimator-pipeline: Box-and-arrow schematic showing an observed sample split into retained-mean, atom-mass, Gram-check, and boundary-regression components, then combined into the Total-Gram estimator and bias-aware interval.

---

## Main result

@informal thm:minimax-risk: The total-Gram estimator attains worst-case absolute error at most \(C r_n\), and every estimator has worst-case absolute error at least \(c r_n\), under the stated Hölder clamp model.

@formal thm:minimax-risk

---

## Honest inference

@informal thm:honest-length: The bias-aware interval has uniform coverage at least \(1-\alpha\), expected length at most \(C r_n\), and every uniformly honest interval has expected length at least \(c r_n\).

@formal thm:honest-length

---

## Phase diagram

- The threshold path determines which term in \(r_n\) is visible.
- Near zero, the atom is small enough for root-\(n\) behavior.
- Past the critical scale, the atom-weighted boundary regression term governs the rate.
- At a fixed positive threshold, the rate becomes the usual boundary nonparametric rate.
- At threshold zero, the target is the ordinary observed mean.

@informal thm:phase-diagram: The phase diagram separates regular, critical, vanishing atom-dominated, fixed-threshold, and zero-threshold regimes for \(r_n\).

@formal thm:phase-diagram

---

## Calibration

- The one-stratum example makes the phase boundary concrete.
- Take \(\beta=\kappa=1\) and \(\pi(a)=2a\).
- The localized Bernoulli alternatives keep likelihood distance bounded while moving the target by the atom-weighted boundary amount.
- The critical threshold scale is where this movement matches \(n^{-1/2}\).

@informal prop:one-cell-calibration: In the one-stratum linear-thinning case, \(h_n\asymp (n\delta_n)^{-1/3}\), \(\Delta_n\asymp \delta_n^2h_n\), and \(\delta_n\asymp n^{-1/10}\) is equivalent to \(\Delta_n\asymp n^{-1/2}\).

---

## Key idea

- The clamp mean has two statistically different pieces.
- The retained mean behaves like a bounded sample average.
- The lower-tail atom multiplies the regression value at the threshold.
- A naive boundary plug-in inherits degenerate-design instability near sparse support.
- Total-Gram stabilization uses the realized local design only when it has enough curvature.
- The atom weight shrinks the boundary-regression error from \(h_n^\beta\) to \(\delta_n^{\kappa+1}h_n^\beta\).

---

## Proof sketch

- Upper bounds decompose the estimator into retained-course error, atom-mass error, and boundary-regression error.
- Polynomial thinning gives the local sample size and Gram curvature scale in the threshold window.
- Hölder smoothness gives a deterministic local-polynomial bias bound.
- The lower bound uses two experiments: a global Bernoulli shift for \(n^{-1/2}\), and a localized threshold bump for \(\delta_n^{\kappa+1}h_n^\beta\).
- Low-style honest-length lower bounds transfer these testing separations to interval length.

---

## Causal interpretation

- The full-data class adds potential outcomes through a latent-response representation.
- Consistency links observed outcomes to structural responses at the realized treatment.
- Conditional exchangeability identifies the structural response mean within strata.
- Response continuity aligns the structural mean with the observed regression value on the threshold range.

@informal prop:causal-bridge: Under the declared full-data causal conditions, the causal clamp mean equals the observed clamp target.

@informal prop:observed-margin-surjectivity: Every observed law in the Hölder clamp model has a full-data lift, so the observed and causal minimax criteria coincide.

---

## Causal frontier

@informal thm:causal-frontier-lift: The same total-Gram estimator, bias-aware interval, minimax risk rate, and honest-length rate \(r_n\) hold for the causal clamp mean over the full-data class.

@formal thm:causal-frontier-lift

---

## Continuity-only comparison

- The continuity-only model keeps the same design and thinning conditions.
- It replaces quantitative Hölder smoothness with qualitative continuity of the regression extension.
- The estimator uses the retained mean, atom masses, and a fixed bounded fallback for the atom regression.
- The resulting frontier is driven by sampling noise plus the total lower-tail mass.

@informal prop:continuity-causal-bridge: In the continuity-only full-data class, the causal clamp mean equals the continuity-only observed clamp target.

@informal prop:continuity-observed-margin-surjectivity: The continuity-only observed and causal minimax criteria coincide through observed-margin surjectivity.

@informal thm:continuity-only-frontier: Over the continuity-only class, observed and causal minimax risk and honest-length rates are characterized by \(s_n=n^{-1/2}+\delta_n^{\kappa+1}\), with the stated elbow and fixed-positive-threshold behavior.

@formal thm:continuity-only-frontier

---

## Conclusion

- We characterize estimation and honest inference for the exact lower-threshold clamp under a two-sided polynomial density envelope on \([0,1]\).
- The frontier is \(r_n=n^{-1/2}+\delta_n^{\kappa+1}h_n^\beta\).
- The phase diagram explains how moving thresholds shift the problem between root-\(n\), atom-dominated, and fixed-threshold regimes.
- The causal bridge gives the same rates a full-data interpretation under the stated consistency, exchangeability, and continuity conditions.
- The continuity-only analysis separates the role of qualitative continuity from the quantitative Hölder modulus.
