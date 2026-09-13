# Second-Order Risk in Multi-Arm Randomization

For fixed binary potential outcomes and a prespecified multi-arm contrast, we reduce the minimax design problem to a finite orbit game, identify the first-order constant, and pin down the universal \(n^{-4/3}\) second-order scale.

---

## Overview

- We study randomized experiments with fixed \(n\), fixed \(K\), binary potential outcomes, and a zero-sum contrast \(c\).
- The object is worst-case design-based mean squared error, optimized jointly over randomization and estimation.
- The main reduction replaces labeled schedules by response-type counts.
- The first-order minimax constant is \(C_0(c)=L_c^2/4\).
- A clipped shrinkage estimator improves the first-order envelope at scale \(n^{-4/3}\).
- Exact rational finite programs give computable upper and lower certificates.

@informal thm:exact-response-type-game: The labeled minimax game has exactly the same value as a finite game over response-type counts.

---

## Motivation

- Multi-arm trials often target a prespecified comparison, such as one regimen versus an average of alternatives.
- In an ACTG 175-style four-regimen binary-endpoint setting, the finite population is the enrolled cohort and each unit has one binary potential outcome per regimen.
- The design question is how to randomize before outcomes are seen when the adversary may choose any complete binary schedule.
- Equal allocation is a natural default, but the contrast itself determines which arms matter for minimax risk.
- We ask: what is the best possible worst-case risk, and what randomization-estimator pair attains its first refinements?

---

## Setup

- A response type records a unit's binary potential outcomes across all \(K\) arms.
- A complete schedule assigns one response type to each labeled unit.
- A zero-sum contrast \(c\) turns that schedule into the finite-population target \(\tau_c\), a treatment comparison.
- The minimax risk \(\rho_n(c)\) lets us choose both the assignment law and a clipped estimator.
- Clipping is to the feasible target range, so the estimator lives on the same scale as the contrast.

@formal def:labeled-schedule-game

---

## Orbit reduction

- Unit labels are arbitrary for the target and for worst-case design-based risk.
- Averaging any procedure over common relabelings produces an invariant procedure.
- An invariant procedure depends on the data through allocation counts and arm-success counts.
- The adversary's state becomes the response-type count vector \(m\), not the full labeled schedule.
- This turns a large labeled problem into a finite decision problem.

@figure orbit-game: Boxes labeled labeled schedule, response-type counts, allocation counts and observed successes, finite orbit game, with arrows showing symmetrization from schedules to counts and evaluation in the orbit game.

@formal thm:exact-response-type-game

---

## Multi-arm scope

- For \(K=2\) and \(c=(1,-1)\), the orbit game recovers the two-arm binary target through the counts of positive and negative effect classes.
- For every fixed \(K\ge3\), the same orbit equality holds with \(2^K\) response types.
- This gives one finite minimax representation for binary treatment contrasts with any fixed number of arms.

@informal thm:multiarm-strict-extension: The two-arm benchmark and the fixed-\(K\) multi-arm orbit game live in the same exact response-type framework.

---

## Related literature

- Fisher (1935), Splawa-Neyman (1990), Rubin (1974), and Holland (1986) anchor the design-based potential-outcomes view.
- Horvitz and Thompson (1952), Hansen et al. (1953), and Särndal et al. (1992) provide the finite-population sampling language.
- Kallus (2018, 2020), Bai (2023), and Aronow and Lopatto (2026) give close minimax design and sampling comparisons.
- Sudijono et al. (2026) provide the sharp two-arm binary calibration.
- Our contribution is the exact multi-arm binary orbit game, its first-order constant, the \(n^{-4/3}\) second-order scale, and finite-program certificates.

---

## First-order result

- Let \(L_c\) be the \(\ell_1\) norm of the contrast.
- Allocate independently on active arms with probabilities proportional to \(|c_a|\).
- Estimate the centered contrast with a projected contrast-weighted Horvitz--Thompson rule.
- This procedure attains the finite-sample first-order envelope \(C_0(c)/n\).
- The asymptotic first-order constant is \(C_0(c)=L_c^2/4\).

@formal def:first-order-procedure

@formal thm:first-order-saddle

---

## Key idea

- The contrast-weighted rule equalizes the worst-case contribution of the active arms at first order.
- The naive projected Horvitz--Thompson estimator is centered correctly, but it leaves room near the hardest response-type boundary.
- The shrinkage rule keeps the same assignment design and modifies only the estimator.
- It shrinks the normalized centered score toward zero inside a bandwidth of order \(n^{-1/3}\).
- That local correction produces a risk improvement at order \(n^{-4/3}\).

@figure shrinkage-pipeline: Boxes labeled contrast-weighted assignment, centered arm score, normalized average, clipped shrinkage, projected estimator, with arrows showing the estimator pipeline.

---

## Second-order result

@informal thm:universal-second-order-rate: For every fixed nonzero zero-sum contrast, clipped shrinkage improves the first-order envelope by at least a positive multiple of \(n^{-4/3}\) once \(n\) passes a contrast-dependent threshold, and the improvement is at most a constant multiple of \(n^{-4/3}\).

@formal thm:universal-second-order-rate

- The exponent \(4/3\) is universal for fixed \(K\) and fixed contrast.
- In the ACTG-style running example, a regimen-versus-average contrast falls under this multi-arm conclusion when at least three arms enter the contrast.

---

## Converse

- The lower side embeds a two-arm hard subproblem inside any fixed contrast.
- The comparison scales the two-arm minimax risk by \(C_0(c)\).
- For contrasts with exactly two active arms, the comparison becomes exact.
- A coarse two-arm information bound supplies the \(n^{-4/3}\) converse scale.

@informal thm:embedded-two-arm-converse: Every fixed contrast inherits the two-arm lower difficulty up to the factor \(C_0(c)\), with exact value transfer for two active arms.

@informal thm:coarse-two-arm-minimax-lower: The two-arm binary minimax risk is at least the first-order value minus \(43n^{-4/3}\).

---

## Proof sketch

- First, symmetrization removes unit labels and preserves the target.
- Second, the first-order upper bound follows from contrast-weighted inverse-probability scores and projection to the target interval.
- Third, shrinkage separates schedules into a central region and a separated region.
- In the central region, shrinking the normalized score reduces variance enough to dominate the introduced bias.
- In the separated region, the response-type contrast spacing keeps the shrinkage loss controlled.
- The two-arm lower bound uses a scalar Bayesian information inequality after reducing schedules to effect-class counts.

@informal lem:two-arm-scalar-prior-schedule-kernel: A two-arm prior over effect-class counts induces a complete-schedule prior whose Bayes risk is captured by a scalar binomial experiment.

@informal lem:bayesian-information-inequality: The scalar Bayes risk is bounded below by a prior- and likelihood-information ratio.

---

## Finite certificates

- The orbit game is finite, so rational contrasts admit finite linear programs.
- The primal side chooses allocation-count masses and grid-valued estimator actions.
- The dual side yields response-count multipliers, interpreted as a least-favorable prior certificate.
- Replacing grid actions by their conditional barycenter gives an invariant estimator.
- The upper and lower endpoints differ by a mesh term.

@formal def:rational-contrast-grid-lp

@informal thm:rational-contrast-grid-certificate-sandwich: For every rational contrast, exact rational primal-dual certificates bracket \(\rho_n(c)\) with mesh gap at most \(C_0(c)/(4M^2)\).

---

## Real contrasts

- Rational certificates transfer to real contrasts through square-root risk continuity.
- The distance is half the \(\ell_1\) distance between contrasts, matching the target range.
- Rational approximants can be chosen close enough that the transfer loss is negligible at the \(n^{4/3}\) scale.
- For an exactly rational contrast, the transferred bracket has width at most \(C_0(c)/(4n^2)\) when \(M=n\).

@informal thm:contrast-risk-continuity: Root minimax risk is Lipschitz in the contrast under half-\(\ell_1\) distance.

@formal thm:real-contrast-grid-certificate-transfer

---

## Three-arm diagnostic

- The diagnostic contrast is \(c^\dagger=(1,-1/2,-1/2)\).
- A scalar signed score keeps the target direction but collapses arm-label information.
- At \(n=3\), an estimator reading the full observed arm labels and outcomes attains a strictly smaller worst-case risk than any rule based on the scalar score.
- This shows why the orbit game keeps arm-success counts, rather than only a one-dimensional signed statistic.

@formal prop:k3-scalar-score-not-minimax-preserving

---

## Additional results

- Four further statements package the same ingredients for specific supports and for the three-arm example.

@informal prop:k3-lp-certificate: The three-arm diagnostic LP gives rational upper and lower certificates, with grid error negligible at the second-order scale when \(M=n^2\).

@informal thm:k3-grid-certificate-sandwich: The three-arm grid program has exact rational primal-dual certificates and brackets \(\rho_n^\dagger\) within \(1/(4M^2)\).

@informal thm:second-order-rate-and-certificate-frontier: For contrasts with at least three active arms, normalized improvements have positive bounded subsequential limits and are approximated by rational certificate clusters.

@informal thm:attainment-and-k3-certified-converse: The support-two value transfers exactly from the two-arm game, while shrinkage and finite brackets apply to every fixed nonzero zero-sum contrast.

---

## Takeaways

- The exact orbit reduction is the computational and conceptual spine: labels vanish, response-type counts remain.
- The first-order benchmark is contrast-weighted allocation with constant \(C_0(c)=L_c^2/4\).
- The same allocation, paired with clipped shrinkage, improves worst-case risk on the universal \(n^{-4/3}\) scale.
- Finite rational programs provide procedure and prior certificates for fixed-\(n\) minimax risk.
- For multi-arm binary trials with prespecified contrasts, the contrast support determines whether the exact two-arm transfer applies or only the universal order sandwich with its finite brackets.
