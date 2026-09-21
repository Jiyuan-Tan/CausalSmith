## Done
- `Interval.lean`, `NormalCDF.lean`, `FiniteKernel.lean`, `Existence.lean`, and `Stationary.lean` are closed with no `sorry`/`admit`/custom `axiom`.
- Lean-LSP diagnostics succeed for all seven modules; only `Comparison.lean` reports four expected `sorry` warnings.
- `lake build CausalSmith.Substrate.CertifiedFiniteMarkovExpectation.Main` succeeds (3132 jobs).
- Axiom audit of the normal-CDF, stationary-existence, and reward-enclosure headline theorems reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Library search was rerun. Makur–Singh arXiv:2309.08475 source confirms the convention `P i j ≥ ε ν j`, with complementary contraction coefficient `1 - ε`.

## Remaining
- `Comparison.lean` (4): `lt_of_disjoint_enclosures`, `stationaryBias_lt_of_expectation_lt`, `stationaryExpectation_lt_of_certified_intervals`, and `stationaryBias_lt_of_certified_intervals`.

## Blocked
- None.

## Decisions
- Dispatch one filler for `Comparison.lean`: all four obligations are a single short dependency chain in one file, so concurrent editing would be unsafe and unnecessary.
- Preserve all public statements and exact-rational checks. No stronger assumptions, paper imports, floating-point trust, axioms, or proof-discharge shortcuts.