## Done
- Ground truth: direct Lean checks of `IIDDQM.lean` and `Variance.lean` plus `lake build CausalSmith.Substrate.AsymptoticLanConvolution` succeed with no errors.
- Source audit finds exactly 2 `sorry`s, both in `IIDDQM.lean`; no `axiom`, `admit`, research imports, or paper-specific types.
- `Basic.lean`: local experiments, guarded likelihood ratios, weak convergence, LAN, regularity, and canonical-gradient pairing are closed.
- `ExponentialTilt.lean`, `LikelihoodNormalization.lean`, `LogTaylor.lean`: likelihood tilting, normalization, and summed-log Taylor infrastructure are closed.
- `TriangularArray.lean`: L²-to-Lindeberg transfer and all i.i.d. row sum, square-sum, truncation, and maximum estimates are closed.
- `Convolution.lean`: subsequential coupling, Le Cam change of measure, analytic factorization, and `regular_convolution_limit` are closed.
- `Variance.lean`: convolution variance addition, moment transfer, dense-score passage, and `regular_asymptoticVariance_ge_gradientNormSq` are closed.

## Remaining
- `IIDDQM.lean` (2): `iid_sqrtLikelihoodIncrement_array_limits`, `iid_logLikelihoodRatio_taylor`.

## Blocked
- None.

## Decisions
- Keep the genuine dominated finite-dimensional DQM API and fixed-direction LAN conclusion unchanged; the remaining work is proof assembly, not API repair.
- The [Cambridge primary preview](https://api.pageplace.de/preview/DT0400.9781107266308_A23760354/preview-9781107266308_A23760354.pdf) was fetched; its accessible pages confirm the cited LAN/convolution chapter organization, though the theorem pages are outside the preview.
- Project search recovered `Causalean.Stat.Concentration.iid_sum_chebyshev`; the scaffold already packages it into the needed triangular-array lemmas, so no duplicate probability framework is warranted.
- Use one filler for both remaining declarations because they form one dependency-ordered chain in the same file/import closure; the array-limit lemma must be closed before assembling the Taylor theorem.