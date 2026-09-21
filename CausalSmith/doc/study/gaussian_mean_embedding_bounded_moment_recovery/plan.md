## Done
- `GaussianFeature.lean`: explicit ℓ² Gaussian feature map, kernel identity, unit norm, continuity, finite-measure Bochner integrability, coordinate CLM, and coordinate/integral interchange are closed.
- `WeightedMoments.lean`: `integrable_gaussianWeightedMonomial` and `gaussianWeightedPolynomial_integral_eq` are closed.
- `WeightedMomentDetermination.lean`: law-equality wrapper is closed.
- `CompactContinuousDetermination.lean`: `measure_eq_of_continuousIntegral_eq` is closed; added a proof-route comment to the remaining theorem.
- `Recovery.lean`: weighted-coordinate recovery, bounded-support law injectivity, raw-second-moment recovery, and positive-norm separation are closed modulo the imported compact approximation theorem.
- Ground-truth verification: `lake build CausalSmith.Substrate.GaussianMeanEmbeddingBoundedMomentRecovery.Recovery` and direct `lake env lean` succeed with exactly one `sorry` warning and no errors.

## Remaining
- `CompactContinuousDetermination.lean`: prove `continuousIntegral_eq_of_gaussianWeightedMoments_eq`.
- After closure: rebuild `Recovery`, scan the whole substrate tree for `sorry`/`admit`/`axiom`, and run `#print axioms` on the recovery headline declarations.

## Blocked
- None.

## Decisions
- Keep finite Borel measures supported on `Set.Icc (-B) B`; retain the stronger law-injectivity API and its moment/norm corollaries.
- Use Weierstrass on `f / gaussianWeight`, then `gaussianWeightedPolynomial_integral_eq` and finite-mass error bounds. Mathlib searches confirmed `exists_polynomial_near_of_continuousOn`, `Measure.restrict_eq_self_of_ae_mem`, `Continuous.integrableOn_Icc`, and `norm_integral_le_of_norm_le_const` as the intended infrastructure.
- Causalean search found no reusable compact Gaussian-moment determination theorem. No specific primary paper was named, so no external source fetch was needed.
- Dispatch one filler: only one open declaration remains and all downstream files share its import closure.