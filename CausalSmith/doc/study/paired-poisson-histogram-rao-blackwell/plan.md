## Done
- `Basic.lean`: histogram fibres, retained prefixes, independent paired averaging, fallback behavior, and estimator measurability are proved.
- `PairingLaw.lean`: coordinatewise pairing measurability and `map_pairRetainedArrays_prod_pi` are proved via the product-regrouping API.
- `FixedRisk.lean`: finite Jensen and `pairedHistogramAverage_productRisk_le` are proved.
- `Risk.lean`: `countLaw`, histogram measurability, total-count law, and the central `pairedPoissonHistogramRisk_le_fixedRisk_add_tails` theorem (including integrability) are proved.
- Ground-truth `lake build CausalSmith.Substrate.PairedPoissonHistogramRaoBlackwell.Main` succeeds (3156 jobs); source grep finds exactly two sorries.
- Library search confirmed the exact public `poisson_two_n_lower_tail` statement. No primary paper was fetched because the requirement names no paper and identifies the argument as standard.

## Remaining
- `Risk.lean`: prove `pairedPoissonHistogramRisk_two_n_le`.
- `Risk.lean`: prove `pairedPoissonHistogramRisk_two_n_exp_le`.
- After zero-sorry closure, promote the paper-neutral dependency closure into Causalean, update root imports/docs/index, then run full-tree build, placeholder grep, and axiom checks.

## Blocked
- None.

## Decisions
- Use one filler for both leaf corollaries because they are short, sequential, and share one import closure; the exponential result directly consumes the first.
- Preserve arbitrary finite alphabets and laws, fallback-zero specialization, and the explicit `B²` penalty. Do not alter the already-proved central theorem or weaken `|theta| ≤ B`.
- Convert `poisson_two_n_lower_tail` from ENNReal to `Measure.real` with `ENNReal.toReal_mono` and `ENNReal.toReal_ofReal`; no new tail certificate is needed.