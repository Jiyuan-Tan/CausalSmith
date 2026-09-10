## Done
- Round-10 ground truth: rebuilt `Main` succeeds; sources contain six proof `sorry`s and no `admit`,
  declared `axiom`, `opaque`, `implemented_by`, or research import.
- `Univariate.lean` and `RootData.lean` are complete, including exact-sign transport from a common
  increasing root-multiplicity equivalence.
- `Basic.lean`: exact-sign syntax/DNF, degree-zero elimination, specialization, finite sign-stratum
  assembly, and `SameLastRootData → SameLastSignTable → projection control` are proved.
- `Sets.lean`: Boolean/finite closure, coordinate preimages/products, and Borel closure are proved.
- `CAD.lean`, `Choice.lean`, and `FirstCell.lean`: APIs and all non-headline consequences are in place.
- Causalean retrieval and Mathlib LeanSearch found no real QE/CAD/semialgebraic-selection theorem.
  Re-fetched Strzeboński arXiv:1405.4925 LaTeX; its Hong projection uses coefficients plus principal
  subresultants against derivatives and polynomial pairs to obtain simultaneous delineability.

## Remaining
- `Basic.lean` (2): `exists_lastDegreeLeadingProjectionFamily`;
  `exists_lastRootMultiplicityTransportProjectionFamily_succ`.
- `Sets.lean` (1): `isSemialgebraicSet_coordinateProjection`.
- `CAD.lean` (1): `exists_cylindricalPartition`.
- `Choice.lean` (1): `exists_semialgebraic_selectorOn`.
- `FirstCell.lean` (1): `exists_firstNonemptyCellBridge`.

## Blocked
- The lowest open obligation is finite coefficient control of specialized degree/leading sign.
- The subsequent Hong/principal-subresultant kernel must preserve multiplicities, coincidences, and
  the common order of roots via one increasing equivalence. Projection, CAD, selection, and the
  first-cell bridge remain serially downstream.

## Decisions
- Decomposed the repeatedly stuck parametric root-data theorem into coefficient control and the
  harder simultaneous root-multiplicity/order kernel. The headline now follows by unioning those
  projection families; do not retry it monolithically.
- Dispatch only `exists_lastDegreeLeadingProjectionFamily`, the lowest independent obligation; do
  not edit/build downstream importers concurrently.
- Retain exact signs, genuine projection images, nonempty preconnected CAD cells, and semialgebraic
  selector graphs; do not import research modules or introduce an oracle.
