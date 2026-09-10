## Done
- `Basic.lean`: raw moments, exact measurable-set-supremum TV distance, compatibility with `Causalean.Stat.tvDist`, and the explicit Carleman series are closed.
- `CumulantTransfer.lean`: `cumFromMom_congr_up_to` and `sourceCumulant_eq_of_rawMoment_eq_up_to` are closed.
- `OrthogonalPerturbation.lean`: `exists_bounded_gaussian_orthogonal_perturbation` is closed by the `K+2` disjoint Gaussian-block nullspace construction.
- `Carleman.lean`: `hamburgerCarlemanSeries_eq_top_of_evenMoment_le` is closed by ENNReal comparison with the divergent half-power series.
- `DensityPerturbation.lean`: `gaussianPerturbation_spec` is closed; source has no proof placeholders.
- Round 4 ground truth: `lake env lean .../Main.lean` exits 0 and checks the full import closure; the live tree has exactly one intended `sorry` and no hard errors.

## Remaining
- `Main.lean`: `exists_finiteMoment_near_gaussian_perturbation`.

## Blocked
- No contract-level blocker; all dependency lemmas for the headline assembly are closed.

## Decisions
- Use a bounded signed density `1 + εh` relative to `gaussianReal 0 1`; boundedness yields positivity, TV control, moment domination, and all finite moments.
- Use `K+2` disjoint bounded intervals plus finite-dimensional rank-nullity for `h`; positive Gaussian interval mass certifies nontriviality.
- Use the reusable growth condition `|m_(2n)| ≤ 2(2n)^n` for the explicit Carleman comparison.
- The density layer reuses `KlDensityTiltExpansion.isProbabilityMeasure_tiltMeasure`; project search found no existing theorem bundling its TV, moment, non-equality, and growth conclusions.
- Assemble with `ε = min (1/2) (rho/2)`.  Derive mean/variance from matched moments 1 and 2; rule out `IsGaussianLaw` using `gaussianReal_ext_iff`; use the closed Carleman and cumulant-transfer theorems for the final clauses.
- No external source was fetched: no specific paper is named, and the canonical construction plus exact local APIs are the relevant sources.
- Round 4 dispatches one filler for the sole open headline theorem; no parallel fillers are useful because there is only one `sorry`.
