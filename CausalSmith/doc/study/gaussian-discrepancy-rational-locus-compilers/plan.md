## Done
- Ground truth checked: the umbrella module builds and direct source elaboration succeeds with exactly 17 `sorry` warnings and no errors.
- `GaussianMatrix.lean`: all five analytic-core theorems are proved; no remaining sorries.
- `RationalMap.lean`: denominator clearing, conjunction/union certificates, equality loci, and polynomial-matrix inverse declarations are proved; no remaining sorries.
- Library search confirmed reusable `IsCompact.exists_sInf_image_eq_and_le`, `IsCompact.continuous_sInf`, `Causalean.Stat.Tendsto_inProb.pi_comp_continuousAt`, and `Convex.is_const_of_fderivWithin_eq_zero`.
- Source scan found no forbidden research imports/names and no `admit` or `axiom`. No specific primary paper was named, so external source fetching was skipped.

## Remaining
- `GaussianDiscrepancy.lean`: 9 sorries—`discrepancyAttainedOn_of_isCompact`, `discrepancyAttainedOn_of_compactSublevel`, both attained/compact gap results, stable gap, compact-model loss continuity, population-minimizer characterization, finite population gap, and covariance-loss convergence in probability.
- `RationalIntersection.lean`: 3 sorries—`eval_renameSource` and vector/matrix image-intersection loci.
- `DerivativeCompiler.lean`: 5 sorries—Fréchet derivative certificate equivalence, derivative locus equality, and three certificate-nonzeroness results.
- After closure: rebuild `Main`, scan for `sorry`/`admit`/`axiom`, and run `#print axioms` on headline theorems.

## Blocked
- None.

## Decisions
- Preserve the existing non-vacuous APIs and explicit compactness, attainment, denominator, convexity, and witness hypotheses.
- Dispatch the three downstream files separately; their edit targets are disjoint and their shared lower imports are already closed.
- For model-loss convergence, reshape matrices through the finite coordinate type `V × V` and apply the existing finite-Pi continuous-mapping theorem.