## Done
- Created `Basic.lean`, `Risk.lean`, `ThreePool.lean`, and umbrella module; targeted `lake build` succeeds with only `sorry` warnings.
- Closed experiment definitions: heterogeneous fixed/randomized pools, product laws, stream/prefix maps, overflow sets, capped statistic, count kernel, Rao--Blackwell statistic, and three-pool data/instances.
- LSP reports zero errors in all three implementation files.

## Remaining
- `Basic.lean`: `measurableSet_prefixNonoverflowSet`, `measurableSet_nonoverflowSet`, `measurableSet_overflowSet`, `nonoverflowSet_eq_compl_overflowSet`, `measurable_streamFamilyToPrefixFamily`, `map_independentPoissonStreamLaw_eq_independentPoissonPrefixLaw`, `measurable_totalizedPrefixFamily`, `measurable_cappedPrefixStatistic`, `cappedPrefixStatistic_eq_off_overflow`, `map_totalizedPrefixFamily_restrict_nonoverflow`.
- `Risk.lean`: Markov-kernel instance, `independentPoissonCountKernel_comp_fixedPoolsLaw`, Rao--Blackwell measurability/integral formula, contraction, restricted-risk lemmas, overflow union bound, and final risk theorem.
- `ThreePool.lean`: `finiteAlphabet_threePoolSharedLaw_risk_le`.

## Blocked
- None.

## Decisions
- Model mutual independence with dependent finite products `Measure.pi`; the API permits heterogeneous alphabets, laws, capacities, and intensities.
- The direct specialization uses a three-constructor index; the last two coordinates share alphabet/law but remain distinct product coordinates.
- Canonical source is the existing two-pool `Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix` implementation. Searches identified `Measure.pi_map_pi`, `Measure.restrict_pi_pi`, and `measureReal_iUnion_fintype_le` as the main finite-product bridges.
- Kept the existing two-pool interface untouched and imported no research modules.