# Substrate requirement: moment-matched-mixture-fuzzy-minimax

## Goal
Build a reusable, model-agnostic Lean library for the moment-matched-prior method: control total variation between prior-predictive mixtures from a likelihood inner-product expansion, and convert mixture indistinguishability plus prior target concentration into a squared-error minimax lower bound by two fuzzy hypotheses.

## Provides (API contract)
- A chi-squared or direct TV bound for one-coordinate prior-predictive mixtures when a dominated likelihood family satisfies `integral (L theta * L theta2) dQ = exp (lambda * theta * theta2)`, the probability priors have bounded support, and their moments agree through degree `L`.
- A product/tensorized corollary for `d` independent coordinates yielding a directly usable estimate of the form `tvDist mixture0 mixture1 <= d * sqrt tail` (a sharper standard tensorization is welcome), with `tail` the explicit exponential-series remainder after the matched degree.
- A generic squared-loss two-fuzzy-hypotheses theorem: induced mixtures at TV distance at most `beta`, target centers separated by `Delta`, and prior target-tail probabilities `alpha_i` outside radii below half the separation imply an explicit lower bound for every estimator worst-case risk.
- Convenient constants for radii `Delta / 4`, tails at most `1 / 8`, and TV at most `1 / 16`, plus a wrapper transferring the result to an infimum over measurable estimators and supremum over a parameter class.

Names may follow the narrowest existing `Causalean.Stat.Minimax` conventions. The declarations must be directly instantiable without reconstructing a paper-specific two-point theorem.

## Statement / milestones
1. Formalize prior-predictive mixture measures for a measurable parameter-indexed probability kernel and prove the integration identities needed for estimator risks and testing events.
2. Under domination, likelihood measurability/integrability, the exponential inner-product identity, bounded support `[-a,a]`, and moment agreement through `L`, expand the mixture likelihood in moments and bound chi-squared/TV by the unmatched exponential-series tail. A general summable-tail theorem followed by an explicit remainder corollary is acceptable.
3. Prove a finite-product mixture bound for product priors and coordinatewise product experiments, including probability, measurability, absolute-continuity, and integrability facts required by `chiSqDiv` and `tvDist`.
4. Prove the generic fuzzy testing reduction for arbitrary measurable estimators, then the Bayes-to-worst-case and estimator-infimum/minimax transfers.
5. Build and review a specialization with `alpha0,alpha1 <= 1/8`, `beta <= 1/16`, and radius `Delta/4`, returning a universal positive multiple of `Delta^2`.

## Standard reference
The classical Le Cam/Tsybakov method of two fuzzy hypotheses and the standard moment-matching prior-mixture argument for nonsmooth functional estimation, including Cai--Low-style polynomial-approximation lower bounds. The analytic identity is the usual Poisson-mixture exponential-kernel calculation.

## Intended reuse
The immediate consumer is the dense-regime lower bound for optimal-policy value with a high-dimensional discrete confounder. It supplies the paper-owned mixture-distance and minimax-transfer bridges while leaving exact Cai--Low approximation-prior existence as a cited hypothesis. The API should also serve entropy/support-size, unseen-species, and other nonsmooth-functional lower bounds.

## May assume / must derive
May assume probability priors and their bounded support/moment matching; a measurable probability kernel/likelihood family; the likelihood inner-product identity; a consumer-supplied explicit series-tail bound; and target-center separation plus prior target-tail inequalities.

Must derive the predictive mixtures and probability status; required density, absolute-continuity, integrability, chi-squared-to-TV, and tensorization steps; the fuzzy inequality for arbitrary measurable estimators; minimax transfer; and the explicit positive constant in the `1/8`, `1/16`, `Delta/4` corollary. Do not assume the final mixture-TV or minimax inequality or a certificate containing them.

## Non-goals
- Do not formalize existence of Cai--Low moment-matching priors or best-polynomial approximation; those are cited inputs.
- Do not import any `CausalSmith/*_Research` module or mention the paper-specific model and construction.
- Do not prove fixed-sample/Poisson de-Poissonization; that is separate reusable transport.

## Known building blocks
- `Causalean.Stat.Minimax.TotalVariation`: `tvDist` and testing inequalities.
- `Causalean.Stat.Minimax.ChiSquared`: `chiSqDiv`, `tvDist_le_half_sqrt_chiSqDiv`, and product divergence facts.
- Mathlib measure integration, kernels, finite products, `Measure.pi`, `Real.exp` power series, and probability-measure APIs.
