## Done
- Ground truth this round: `lake build CausalSmith.Substrate.SupportLocalizedMomentMatchedMixture.Main` succeeds; Lean LSP reports exactly two `sorry` warnings in `Bounds.lean` and no errors.
- `Basic.lean` is closed: support-to-AE conversion, localized nonnegativity, integrability, predictive-density identity, absolute continuity, and measurability are proved.
- `Quadratic.lean` is closed: localized cross-term integrability/identity, four-term quadratic identity, and exponential-series-tail bound are proved.
- The checked sign-count witnesses establish nonnegativity on `[-1,1]` and negativity at `theta = 2`, `Nplus = 0`, `Nminus = 1`.
- Library search confirmed reuse of the reviewed density-to-TV and `tvDist_pi_iid_le` machinery; Mathlib search found `Real.sqrt_mul`. Cai--Low arXiv:1105.3039 LaTeX confirms bounded moment-matched priors and product priors.

## Remaining
- `Bounds.lean` (2): `momentMatchedMixture_tv_le_sqrt_tail_of_supported` and `momentMatchedProductMixture_tv_le_of_supported`.

## Blocked
- The product theorem depends on the one-coordinate theorem, so both should be proved serially in one edit of `Bounds.lean`.

## Decisions
- Preserve all current theorem statements and localized hypotheses; no API change or extra assumption is needed.
- Keep the reviewed namespace and `_of_supported` entry-point names.
- Use one filler for both tightly coupled remaining declarations, mirroring the reviewed `Analytic.lean` and `Product.lean` proof architecture with the localized helpers.