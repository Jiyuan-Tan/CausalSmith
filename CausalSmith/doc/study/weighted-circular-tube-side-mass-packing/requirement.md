# Substrate requirement: weighted circular-tube side mass and circle packing

## Goal
Build reusable planar geometry and measure lemmas showing (i) that a power-weighted one-sided ball cut by the unit circle has mass comparable to h^κ uniformly along the circle, and (ii) that maximal separated sets on the unit circle have cardinality comparable to h⁻¹.

## Provides (API contract)
- `unitCircle_powerWeighted_sideBall_bounds`: for 2 < κ ≤ κbar, 0 < h0 < 1, x on the unit circle, side sign ε ∈ {inside,outside}, and 0 < h ≤ h0, the Lebesgue integral over `ball x h` intersected with the chosen side of the unit circle of `|‖z‖ - 1|^(κ-2)` is bounded above and below by positive constants times h^κ; constants are uniform in x, κ in (2,κbar], and the side.
- `unitCircle_maximalSeparated_card_bounds`: for sufficiently small h > 0, any finite maximal 3h-separated subset of the unit circle covers the circle at radius 3h and has cardinality between positive constants times h⁻¹. An existence theorem producing such a finite set is also acceptable/useful.
- Supporting measurability, finiteness/positivity, normalization, annular-coordinate, and compactness lemmas needed to make the two results directly usable by downstream probability-measure constructions.

## Statement / milestones
Work in ℝ × ℝ with Euclidean distance and volume. Let S = {z : ‖z‖ = 1}, ρ(z)=‖z‖-1, and wκ(z)=|ρ(z)|^(κ-2). For fixed κbar>2 and h0∈(0,1), derive constants 0<c≤C<∞ such that simultaneously for every κ∈(2,κbar], x∈S, 0<h≤h0, and each side ρ≤0 or ρ>0,

    c h^κ ≤ ∫_{ball(x,h) ∩ side} wκ(z) dz ≤ C h^κ.

Constants may depend on κbar and h0 but not on κ, x, h, or the side. Prove the corresponding weighted annular normalizer is finite and strictly positive when useful.

For the same unit circle, establish universal small-scale constants cpack,Cpack,hstar>0 so a maximal 3h-separated finite set exists for every 0<h≤hstar, covers S by open 3h-balls, and has

    cpack / h ≤ card(sites) ≤ Cpack / h.

Statements may use an equivalent coercion-safe formulation such as inequalities for `(sites.card : ℝ)`.

## Standard reference
Standard polar/annular change of variables in ℝ², local bi-Lipschitz parametrization of the circle, Ahlfors 1-regularity of arc length on S¹, and the usual packing/covering-number comparison for compact 1-manifolds. Mathlib's polar-coordinate and Jacobian infrastructure is an acceptable foundational reference.

## Intended reuse
The immediate consumer constructs normalized score laws around a circular decision boundary and proves pervasive/isolated local-mass profiles plus Θ(h⁻¹) Fano packing. Keep the API paper-agnostic: it must mention only Euclidean geometry, volume/integration, the unit circle (or a more general circle specialization), power weights, and separated/covering finite sets. It must not import or mention any `CausalSmith.*_Research` paper module or `BoundaryLaw`.

## May assume / must derive
May assume standard Mathlib facts about Lebesgue measure, polar coordinates, trigonometry, compactness of spheres, and existence of finite separated nets. Must derive the two-sided h^κ mass scaling, uniformity over κ∈(2,κbar], both sides and circle centers, finite positive normalization, and the Θ(h⁻¹) cardinality bounds. Do not assume the desired mass or packing inequalities as opaque hypotheses.

## Non-goals (optional)
Do not construct the paper's probability `BoundaryLaw`, Gaussian outcome kernels, treatment regions, traces/regressions, isolated-thinning class, or full Fano/Le Cam family. Those are paper-specific consumers to be proved after importing this neutral substrate.

## Known building blocks (optional)
`Mathlib.Analysis.SpecialFunctions.PolarCoord`, `Mathlib.MeasureTheory.Function.Jacobian`, `Mathlib.MeasureTheory.Group.LIntegral`, compactness/totally-bounded separated-net results, and existing sphere/circle metric lemmas. A neutral staged module may import Mathlib and Causalean only.
