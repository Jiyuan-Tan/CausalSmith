# Presentation adjudication — 2026-09-07

## P4 crosswalk anchor: `block_orderIso_sum_eq`

- Finding: the graph-derived presentation crosswalk names
  `CausalSmith.Stat.LmtpThresholdAtomFrontier.block_orderIso_sum_eq`, but the owning Lean declaration
  was marked `private`; therefore the strict paper index correctly reported a dangling crosswalk
  declaration.
- Adjudication: this is an accessibility mismatch, not new mathematics and not a crosswalk remapping.
  The graph, accepted full crosswalk, and source `@node` annotation agree on the helper and declaration
  name. Removed only the `private` visibility modifier so the declared public anchor matches them.
- Bank edits: none.
- Lean edits: `Helpers/TotalGram.lean` visibility modifier only; theorem statement and proof unchanged.
- Pipeline edits: none.

## P4 documentation follow-up

- Finding: once public and indexable, the helper correctly entered P4's source-documentation gate.
- Resolution: added a one-sentence docstring that states exactly the finite-sum reindexing equality;
  theorem statement and proof remain unchanged.
