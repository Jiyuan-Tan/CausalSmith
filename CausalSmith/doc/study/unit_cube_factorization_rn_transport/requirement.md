# Substrate requirement: unit_cube_factorization_rn_transport

## Goal
Build reusable measure-theoretic adapters that turn support-local unit-cube density data into a `Causalean.Graph.FiniteDensity.UnitCubeFactorization` and transport canonical Radon--Nikodym ratios through a measurable equivalence specified only on the measures' supports.

## Provides (API contract)
- A coordinatewise clamping/retraction map from a finite real product to `Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)`, with measurability, range, and identity-on-cube lemmas.
- A constructor for `UnitCubeFactorization` from factors that are measurable or continuous on the cube, parent-local on the cube, nonnegative, and normalized in their own coordinate on the cube. The constructor must use a globally measurable clamped extension and preserve the original factor on the cube.
- A theorem identifying `Measure.pi (fun _ => unitIntervalReference)` with Lebesgue volume restricted to the finite unit cube, or an equivalent API sufficient to identify the constructed `withDensity` measure with an existing cube-restricted product-density measure.
- A support-restricted RN transport theorem: if finite measures `μ` and `ν` are supported on `S`, maps `f` and `g` are measurable on the relevant supports and mutually inverse there, then the canonical RN derivative of `map μ f` with respect to `map ν f`, evaluated after `f`, agrees `ν`-a.e. on `S` with the RN derivative of `μ` with respect to `ν`. Expose a pushforward-law corollary for the real-valued RN ratio.

## Statement / milestones
For a finite index type, define the coordinate clamp `clampCube`. Prove that it is measurable, maps every point into the unit cube, and equals the identity on the cube. Given cube-local factors `p i` whose values depend only on `i` and its DAG parents and whose own-coordinate integrals equal one, define global factors by `p i (clampCube v)` (with an `ENNReal.ofReal` wrapper when the input is real-valued). Prove the `Measurable`, `parent_local`, and `normalized` fields required by `UnitCubeFactorization`, and prove that its observational and single-target intervention measures equal the corresponding cube-restricted product-density measures.

For finite measures `μ ≪ ν` concentrated on `S`, and a support-local measurable equivalence `f : α → β`, `g : β → α` between `S` and `T`, prove the RN transport identity without requiring `f` to be a globally measurable embedding. An acceptable proof may pass to subtypes or replace `f` off `S` by a globally measurable embedding, but the final theorem must require only measurability/inverse/injectivity on the support. Deduce equality of `Measure.map (fun x => (μ.rnDeriv ν x).toReal) ν` with the corresponding mapped-measure ratio law after composition with `f`.

All central declarations must be sorry-free and axiom-clean. The final API must compose with `Causalean.Graph.FiniteDensity.Factorization.targetRatio_map_eq`.

## Standard reference
The first component is the standard measurable-extension-by-retraction construction for densities on a compact product cube, together with the finite-product identification of uniform coordinate reference measure. The second component is the standard invariance/change-of-variables property of Radon--Nikodym derivatives under a bimeasurable isomorphism, localized to full-measure supports. Mathlib's global `MeasurableEmbedding.rnDeriv_map` is the reference near-match; the required result is its support-restricted form.

## Intended reuse
The immediate consumer is `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.ratio_nonancestor_zero`. It must internally construct `FiniteDensityObservedWorldBridge W` from the existing `PositiveNormalizedSmoothMechanisms`, `SharedDiffeomorphicMixing`, and `OnePerfectInterventionPerNode` hypotheses, then combine the bridge with `Factorization.targetRatio_map_eq`. No bridge premise may be added to `ratio_nonancestor_zero` or to the frozen `simultaneous_confidence_edges` theorem.

The substrate should live in general Mathlib/Causalean-facing modules and be reusable for finite density-factorized causal models on compact product supports and for other support-local changes of variables.

## May assume / must derive
May assume finite index types and standard Borel coordinate spaces; local continuity or measurability of factors on the cube; nonnegativity, parent locality, and own-coordinate normalization on the cube; finiteness and absolute continuity of the two measures; measurable support sets; concentration of the measures on those supports; and maps that are measurable and mutually inverse on the supports.

Must derive a globally measurable clamped extension, the `UnitCubeFactorization` fields, equality with the cube-restricted product-density measures, the support-local RN transport identity, and its ratio-law pushforward corollary. Must not assume the desired observational/interventional ratio-law equality, a global embedding not supplied by the support-local hypotheses, or any paper conclusion.

The study must not import `CausalSmith/*_Research`. Before coordination, main should extract any needed generic aliases/interfaces from the research folder: the finite real product cube, the cube-restricted product-density form of observational/intervention laws, and the support-local mix/unmix inverse conditions. The promoted theorem should depend only on Mathlib and general Causalean modules, including `Causalean.Graph.FiniteDensity`.

## Non-goals (optional)
Do not reprove finite-DAG ancestral marginal invariance, general disintegration, arbitrary nonsingular transformations, or the paper's decoder theorem. Do not encode the paper's `ObservedWorld`, target permutation, MMD, or canonical observed-law definitions in the promoted substrate.

## Known building blocks (optional)
- `Causalean.Graph.FiniteDensity.UnitCubeFactorization`, `Factorization.targetRatio_map_eq`, and `unitIntervalReference`.
- Mathlib `Measure.restrict_pi_pi`, `Measure.withDensity_congr_ae`, and `Measure.withDensity_absolutelyContinuous'`.
- Mathlib `MeasurableEmbedding.rnDeriv_map` as the global theorem to localize via subtypes or full-measure congruence.
- Coordinate projection to `Set.Icc`, `Continuous.clamp`, finite-product measurability, `Measure.map_map`, and `Measure.map_congr`.
