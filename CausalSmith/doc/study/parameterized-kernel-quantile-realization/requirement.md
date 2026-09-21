# Substrate requirement: parameterized-kernel-quantile-realization

## Goal
Construct an axiom-clean measurable randomization of a real-valued Markov kernel by a single independent uniform variable, with joint measurability in the kernel parameter.

## Provides (API contract)
- A parameterized inverse-CDF/quantile map for a Markov kernel `κ : Kernel S ℝ`, measurable as a function of `(s,u)`.
- A theorem that each section pushes the uniform probability measure on `[0,1]` exactly to `κ s` when `κ s` is supported on `[0,1]`.
- A section-range theorem sufficient to choose a faithful unit-interval carrier (pointwise if the construction permits it, otherwise almost surely under the uniform law).
- Convenient measurable-section and `Measure.map` corollaries usable by downstream probability constructions.

## Statement / milestones
For an appropriate measurable parameter space `S` and Markov kernel `κ : Kernel S ℝ`, assume fiberwise support in `Set.Icc (0 : ℝ) 1`. Construct `q : S × ℝ → ℝ` such that `q` is measurable, `u ↦ q (s,u)` lies in `[0,1]` almost surely for every `s`, and
`Measure.map (fun u => q (s,u)) (volume.restrict (Set.Icc 0 1)) = κ s`
for every `s` (with the normalized unit-interval Lebesgue probability measure expressed in the library's canonical form). The implementation should prove measurability of the parameterized generalized inverse rather than postulate a selector.

## Standard reference
The inverse-transform/randomization lemma for probability kernels on standard Borel spaces; in the real-valued case it follows from measurability of distribution functions and the generalized inverse. Kallenberg, *Foundations of Modern Probability*, transfer/randomization results in Chapter 6, is a standard reference.

## Intended reuse
Reusable measurable realization and coupling arguments for parameterized conditional laws. The immediate consumers need a real-valued kernel supported on `[0,1]`, exact sectionwise law realization, and joint measurability in the external parameter. The API must not mention or import any paper-specific model.

## May assume / must derive
May assume the parameter space carries the measurable structure required by Mathlib's kernel API, that `κ` is a Markov kernel, and the explicit fiberwise support hypothesis. Must derive joint measurability, the sectionwise pushforward equality, and the range/support consequence from Mathlib/Causalean primitives. No new axioms, classical witness placeholders, or unproved measurability assumptions may be introduced.

## Non-goals (optional)
Arbitrary non-real standard Borel targets, optimal transport properties, continuity of the quantile in either argument, and paper-specific causal or minimax statements.

## Known building blocks (optional)
`Mathlib.Probability.Kernel.Basic`, `Mathlib.MeasureTheory.Function.DistributionFunction`, `Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar`, fixed-measure quantile and `quantile_map_uniform` results, and `Causalean.Mathlib.CondDistribWitness`. Reuse existing kernel and distribution APIs before introducing wrappers.
