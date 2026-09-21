# Substrate requirement: weak-rational-convex-optimization

## Goal
Provide a reusable finite-dimensional theorem turning rational well-bounding data, weak membership, and rational approximate-value access for a globally defined convex function into an erosion-valid weak minimizer with an oracle-polynomial complexity certificate.

## Provides (API contract)
- `WeakRationalConvexOptimizationOracle`: a general interface for rational weak-membership queries to a closed convex body and rational approximate-value queries for a globally defined convex function.
- `WeakRationalConvexOptimizationCertificate`: rational output point/value data together with outer-feasibility and erosion-comparison guarantees.
- `weak_rational_convex_optimization`: from explicit rational center and positive inner/outer radius bounds, the oracle interface, and rational accuracy, produce a certificate whose output length and number of oracle/arithmetic steps are polynomial in dimension, input encoding length, and the logarithm of reciprocal accuracy.

## Statement / milestones
For a nonempty closed convex body C in a finite-dimensional rational Euclidean space, define the outer thickening S(C,α) by distance at most α and the erosion S(C,-α) by containment of the closed α-ball. Assume explicit rational data x₀,r₀,R₀ with 0<r₀≤R₀, B(x₀,r₀)⊆C⊆B(0,R₀), a polynomial-time rational weak-membership oracle for C, and an oracle which at every rational ambient query x and rational δ>0 returns a rational number within δ of a globally defined convex function f(x). For rational α>0, construct rational y with y∈S(C,α) and

    f(y) ≤ f(x) + α

for every x∈S(C,-α). Record a precise oracle-polynomial bound for calls, rational arithmetic steps, and output bit length in the dimension, encodings of x₀,r₀,R₀ and the oracles, and log(1/α). The theorem must expose the erosion comparison rather than strengthen it to comparison with every point of C.

Supporting milestones may formalize rational vectors/balls, weak membership, inner and outer parallel bodies, approximate-value oracle correctness, polynomial encoding bounds, and composition of the returned algorithm/certificate.

## Standard reference
Grötschel, Lovász, and Schrijver, *Geometric Algorithms and Combinatorial Optimization* (1988), Definition 2.1.16 and Problem 2.1.22 in Chapter 2, and Theorem 4.3.13 on pp. 113–114. Preserve its weak/erosion output specification and oracle-polynomial model.

## Intended reuse
Finite rational convex programs whose objectives have exact or approximate rational ambient-space value oracles, including minimax design, robust optimization, partial-identification, and finite statistical decision problems. The immediate consumer is the orbit-compiler theorem in `exp_boundedcluster_endpoint_orbit_minimax`, but no declaration may mention that run, saturation experiments, or its paper-specific types.

## May assume / must derive
May assume the standard GLS weak-optimization theorem as a faithfully typed cited foundation if formalizing the ellipsoid algorithm itself is disproportionate; the interface and all consequences used by consumers must state its exact hypotheses and erosion-valid conclusion. Must derive the rational certificate wrapper, positivity/domain side conditions, outer-feasibility and comparison projections, and explicit composition of polynomial call/bit bounds. Do not silently assume full-dimensionality without the supplied inner ball, exact optimization, rational exact optimizers, or a globally finite perspective unless the consumer supplies one.

## Non-goals (optional)
No strongly polynomial bound, exact optimizer, separation-oracle equivalence beyond what the cited theorem requires, infinite-dimensional optimization, or paper-specific orbit-program construction.

## Known building blocks (optional)
Mathlib finite-dimensional convexity, Euclidean distance/closed balls, rational arithmetic, and polynomial encodings. `Mathlib.Topology.Sion.exists_isSaddlePointOn` handles a separate minimax existence step and is not part of this requirement. Search Causalean's `RationalLP` material for reusable exact rational certificate conventions, without confusing finite LP exactness with the weak convex-oracle theorem.
