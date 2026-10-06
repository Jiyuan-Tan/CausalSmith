# Stat/Concentration vendoring audit trail

The upstream package [auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher)
is vendored whole under `third_party/lean-rademacher/` and required as the `FoML` lake
dependency; this directory adds Causalean-namespace wrappers and Causalean-specific
extensions on top of the `FoML.*` imports ("Phase 4a" of the concentration build-out).

## Upstream

* Repo: `https://github.com/auto-res/lean-rademacher`
* Pinned commit: `72d28921dc960f47691640fb973303a1be9d13ca`
* Date pulled: 2026-05-08
* Upstream Lean toolchain: `leanprover/lean4:v4.27.0-rc1`
* Causalean Lean toolchain: `leanprover/lean4:v4.33.0` (mathlib pinned at `db584cd6`)
* Upstream license: **MIT License** (Copyright (c) 2025 AutoRes) — verified
  in `third_party/lean-rademacher/LICENSE`.

Each ported file carries an `Adapted from auto-res/lean-rademacher`
header citing the upstream file and commit, and a per-deviation
`UPSTREAM-DELTA` block listing API drift and porting changes.

## Vendored files (Phase 4a)

| Causalean file                                  | Upstream source                    | Scope                                        |
|----------------------------------------------|------------------------------------|----------------------------------------------|
| `Rademacher/Rademacher.lean`                 | `FoML/Defs.lean`, parts of `FoML/Rademacher.lean` and `FoML/RademacherVariableProperty.lean` | Definitions only: `Signs`, `empiricalRademacherComplexity`, `rademacherComplexity`. Measurability lemmas as needed. |
| `UniformDeviation/BoundedDifference.lean`    | `FoML/BoundedDifference.lean`      | Bounded-difference predicate and the `uniformDeviation_bounded_difference` lemma. |
| `TailBounds/McDiarmid.lean`                  | `FoML/McDiarmid.lean` (+ deps from `Hoeffding.lean`, `MaximalInequality.lean`, `ExpectationInequalities.lean`) | Headline tail bound only: `mcdiarmid_inequality_pos'`. |
| `Rademacher/Symmetrization.lean`             | `FoML/Symmetrization.lean`         | Headline only: `expectation_le_rademacher` (a.k.a. the symmetrization bound on `E[supₐ |Pₙfₐ − Pfₐ|]`). |
| `Covering/Separable.lean`                    | `FoML/SeparableSpaceSup.lean`      | `separableSpaceSup_eq_real`: countable-dense lifting for `sup` over uncountable separable index. |

## Also vendored

The remaining upstream modules (`FoML/DudleyEntropy`, `CoveringNumber`, `PseudoMetric`,
`Massart`, `LinearPredictorL1/L2`, `MeasurePiLemmas`, `ForMathlib/Probability/Moments`)
ship with the package under `third_party/lean-rademacher/FoML/`; `Covering/DudleyEntropy.lean`,
`Covering/CoveringNumber.lean` and `TailBounds/Massart.lean` here are their Causalean ports.

## Porting policy

* Each ported file's leading docstring documents `UPSTREAM-DELTA:` —
  every non-trivial deviation from the original (mathlib API rename,
  namespace changes, removed unused lemmas, weakened hypotheses, etc.).
* The port is complete and sorry-free; where an upstream proof needed a
  toolchain-drift fix, the fix lives in `third_party/lean-rademacher/` (see its
  `UPSTREAM.md`), and the Causalean wrapper imports the fixed `FoML.*` module.
* Wrappers live under the `Causalean.Stat.Concentration` namespace with imports
  normalised to Causalean conventions; the FoML definitions themselves remain
  root-namespace symbols exposed by the imports.

## Re-syncing with upstream

When a new commit of `auto-res/lean-rademacher` should be pulled:

1. Update the **Pinned commit** field above.
2. For each vendored file, diff the upstream slice between the old and
   new SHA, and update the corresponding `UPSTREAM-DELTA` block.
3. Re-run `lake build Causalean.Stat.Concentration` and the bridge file
   smoke-test to confirm no regression.
