## Done
- `Series.lean`: all Poisson weight, triangular `tsum`, and telescoping/Cauchy–Schwarz lemmas are proved without proof holes.
- `L2Closure.lean`: product-law variance identity, finite-support `MemLp`, truncation convergence, and variance continuity are proved.
- `Foundations.lean` and `Main.lean`: clean umbrella modules.
- Targeted `lake build CausalSmith.Substrate.PoissonAddOnePoincare.Main` succeeds; ground truth contains exactly seven `sorry`s and no other forbidden proof discharges.
- Library search confirmed reuse of `Causalean.Mathlib.Probability.variance_prod_eq_integral_variance_add`, `MeasureTheory.measurePreserving_piFinSuccAbove`, `measurePreserving_piCongrLeft`, and finite-`Measure.pi` integration infrastructure.
- The LaTeX source of arXiv:1401.7568 states the standard Poisson-space inequality `Var F ≤ E ∫ (D_x F)^2 dλ`, matching the scalar API.

## Remaining
- `Scalar.lean` (4): `poisson_addOne_poincare_finiteSupport`, `poisson_addOne_poincare`, `poisson_addOne_poincare_tsum`, `variance_poissonMeasure_zero`.
- `Tensorization.lean` (3): `variance_pi_le_sum_integral_coordinateVariance`, `poissonPi_addOne_poincare`, `nestedPairedPoisson_addOne_poincare`.

## Blocked
- None.

## Decisions
- Retain the genuine graph-domain scalar API requiring `MemLp f 2` and `MemLp (addOne f) 2`; this ensures the energy is meaningful and includes `lambda = 0`.
- Retain both flat `Measure.pi` and nested paired-Poisson corollaries for the intended `Fin d → Bool → Nat × Nat` consumer.
- Dispatch two fillers on disjoint files: scalar closure first-layer work and product tensorization. Helpers may be added locally, but statements and hypotheses must not be weakened.