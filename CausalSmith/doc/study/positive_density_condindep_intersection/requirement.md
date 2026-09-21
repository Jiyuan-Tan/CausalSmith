# Substrate requirement: positive_density_condindep_intersection

## Goal
Build the reusable graphoid intersection theorem for conditional independence under a strictly positive density with respect to a product reference measure, together with the finite-coordinate projection specialization needed for positive-density Bayesian networks.

## Provides (API contract)
- A measure-level `CondIndepFun` intersection theorem for four random blocks `X`, `Y`, `V`, and `Z`: from `X ⟂ Y | (Z,V)` and `X ⟂ V | (Z,Y)`, conclude `X ⟂ (Y,V) | Z`, provided the joint law of the four blocks has a strictly positive density relative to a product reference measure.
- A decomposition corollary concluding `X ⟂ Y | Z` from the combined conclusion.
- A finite-coordinate theorem for a measure on a finite product space with a strictly positive density, specialized to pairwise-disjoint index blocks. It should accept coordinate projections and expose the two conclusions above in `CondIndepFun`/`CondIndepGiven`-compatible form.
- If required by the proof, intermediate conditional-density or conditional-expectation lemmas showing that positivity permits the two conditional-independence identities to be spliced across the changing conditioning blocks.

## Statement / milestones
Let `ρ` be a finite or probability measure on `X × Y × V × Z`, absolutely continuous with respect to a product reference measure `μX.prod (μY.prod (μV.prod μZ))`, with measurable density `d` satisfying `d ≠ 0` almost everywhere on the reference support. For the coordinate maps, prove

`X ⟂ Y | (Z,V)` and `X ⟂ V | (Z,Y)` imply `X ⟂ (Y,V) | Z`.

Deduce `X ⟂ Y | Z` by decomposition. An equivalent formulation using a reordered product, kernels, conditional expectations, or an everywhere-positive continuous density on compact supports is acceptable if it instantiates cleanly for finite real-coordinate cubes.

For a finite index type and a measure `ρ = μ.withDensity d` on a product coordinate space, prove the corresponding result for projections onto index sets `I`, `J`, `K`, and `L` under explicit pairwise-disjointness hypotheses. In particular, the theorem must reject overlap degeneracies such as `J ⊆ K`, for which the two premises can be tautological while the conclusion is false.

All central declarations must be sorry-free and axiom-clean.

## Standard reference
This is the intersection axiom of a graphoid. Conditional independence is only a semigraphoid in general; a strictly positive joint density upgrades it to a graphoid by validating intersection. The usual proof writes the two conditional-density identities, uses positivity to compare them on the common product support, and concludes that the conditional law of `X` is independent of both `Y` and `V` given `Z`.

## Intended reuse
The immediate consumer is the parent-pruning portion of `CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity.exact_ratio_decoder`. There the blocks are the latent/rank coordinate of node `i`, an omitted parent `b`, `Z = parents(i) \ {b}`, and `W = predecessors(i) \ parents(i)`. The graph/order construction proves these coordinate blocks are disjoint and the positive normalized mechanism gives a strictly positive product density. The result combines weak union (equation (15)) with the ordered local-Markov relation (equation (16)) to obtain equation (18), contradicting causal minimality.

The promoted API should live under `Causalean.Mathlib.CondIndep` or an adjacent general probability module, and should be reusable in positive-density graphical models unrelated to this paper.

## May assume / must derive
May assume standard Borel coordinate spaces, sigma-finite product reference measures, finiteness/probability of the joint measure, measurability and almost-everywhere strict positivity of its density, and explicit pairwise disjointness for finite coordinate blocks. It may assume the two conditional-independence premises.

Must derive the combined conditional independence and decomposition corollary. Must not assume the desired intersection conclusion, silently identify overlapping coordinate blocks, import a paper-specific `CausalSmith/*_Research` module, or package the paper's parent-pruning conclusion as substrate.

Before paper integration, the local helper statement must be corrected to expose the block-disjointness/product-density facts actually used by the frozen proof. Those facts are helper preconditions derived internally from the existing graph order and `PositiveNormalizedSmoothMechanisms`; they must not become new premises of the delivered decoder theorem.

## Non-goals (optional)
Do not formalize arbitrary intersection for singular laws, general graphoid completeness, d-separation, parent recovery, rank construction, or the paper's exact decoder. Do not treat `ProbabilityTheory.CondIndepSets.inter` as the target theorem: that result only intersects event families within one fixed conditional-independence relation.

## Known building blocks (optional)
- `ProbabilityTheory.CondIndepFun` and its conditional-expectation characterization.
- `Causalean.Mathlib.CondIndep.CondExp`, including symmetry, weak union, contraction, and `condIndepFun_iff_condExp_inter_preimage_eq_mul`.
- Product-measure Fubini/Tonelli, `Measure.withDensity`, RN derivatives, and conditional distributions.
- Existing Causalean finite-product projection and density infrastructure in `Causalean.Graph.FiniteDensity` may supply the coordinate-law packaging, but the result itself should remain graph-independent.
