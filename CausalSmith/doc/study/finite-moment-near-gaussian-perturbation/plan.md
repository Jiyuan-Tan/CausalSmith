## Done
- `Basic.lean`: raw moments, measurable-set TV distance, `tvDist` compatibility, and explicit Carleman series are closed.
- `CumulantTransfer.lean`: both finite raw-moment-to-cumulant transfer results are closed.
- `OrthogonalPerturbation.lean`: bounded nonzero Gaussian-orthogonal profiles for arbitrary `K` are closed.
- `Carleman.lean`: divergence from `|m_(2n)| ≤ 2(2n)^n` is closed.
- `DensityPerturbation.lean`: `gaussianPerturbation_spec` is closed with no placeholders.
- Round 4 ground truth: direct `lake env lean .../Main.lean` exits 0 over the full import closure; source scan finds exactly one `sorry`, in `Main.lean`.

## Remaining
- `Main.lean`: prove `exists_finiteMoment_near_gaussian_perturbation`.

## Blocked
- No contract-level blocker; every dependency needed for headline assembly is closed.

## Decisions
- Keep the genuine bounded density perturbation `1 + εh` and growth bound `|m_(2n)| ≤ 2(2n)^n`.
- Assemble with `ε = min (1/2) (rho/2)`; derive mean and variance from moments 1 and 2.
- Refute `IsGaussianLaw` using `gaussianReal_ext_iff` and the density layer’s measure inequality.
- Finish with the closed Carleman comparison and cumulant-transfer theorems.
- Library search confirmed the relevant local APIs; no external source was fetched because no specific paper is named.
- Dispatch one filler: only one `sorry` remains, so parallel work would not have disjoint useful targets.