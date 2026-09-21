## Done
- Ground-truth audit: all six substrate files were read; `Coordinate.lean`, `Factorization.lean`, `Leaf.lean`, `Elimination.lean`, and `Main.lean` are sorry-free.
- `Main.lean` closes the factorization, reverse-topological elimination, ancestral marginal, dependent-map, ratio-law, and mixing-map APIs without weakened statements.
- Lean LSP reports zero errors for `Cube.lean`; direct `lake env lean` and targeted `lake build CausalSmith.Substrate.FiniteDagNonancestorMarginalInvariance.Cube` succeed with only the two expected sorry warnings and lint warnings.
- Source audit finds exactly two `sorry`s and no `admit`, declared `axiom`, `opaque`, `extern`, `implemented_by`, forbidden research import, or paper-specific dependency.
- Library search identified `Measure.pi_eval_preimage_null`, `measure_iUnion_null`, `Set.univ_pi_eq_iInter`, and `MeasureTheory.Restrict.sigmaFinite`; the closest Causalean nonancestor result is SCM-typed and therefore not a replacement for this density-only substrate.
- The primary source, [Pearl, Causality, §3.2.2–3.2.3](https://web.cs.ucla.edu/~kaoru/CAUSALITY-REPRINTED-W-CORRECTIONS-2013/causality-ch3-june2013.pdf), explicitly states nondescendant marginal invariance under local mechanism changes and gives truncated factorization in equations (3.10)/(3.14).

## Remaining
- `Cube.lean`: `unitCubeReference_compl`.
- `Cube.lean`: `UnitCubeFactorization.ancestralMarginal_eq`.

## Blocked
- None.

## Decisions
- Preserve the dependent finite-product, σ-finite, `ℝ≥0∞` API and the ambient-space cube represented by a reference measure supported on `[0,1]^V`.
- Use one serialized filler for both remaining declarations because they share one file and import closure; the second theorem depends on the same restricted-measure instance setup as the first.
- For cube support, use an explicit complement/intersection or subset-of-union argument. A naive broad `simp` rewrite stalled on pointwise-order De Morgan normalization.
- Unfold `unitIntervalReference` locally when typeclass inference must expose the σ-finite restricted Lebesgue measure.