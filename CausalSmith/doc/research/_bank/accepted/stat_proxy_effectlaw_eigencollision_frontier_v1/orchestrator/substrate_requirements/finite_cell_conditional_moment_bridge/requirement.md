# Finite-cell conditional-moment bridge

## Route

`substrate-build:study`

## Downstream blocker

`CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier.observed_vmw_margin_inclusion`
is still a visible `sorry`. Its model assumptions encode conditional independence through
factorization of normalized restricted integrals against all measurable uniformly bounded real
test functions, rather than through Mathlib's `CondIndepFun` API.

The downstream proof needs two reusable, paper-agnostic measure-theory bridges.

## Required substrate

1. A finite-cell/componentwise factorization theorem. For a probability measure `P`, a measurable
   event `C` of positive finite mass, and measurable integrable finite-dimensional random variables,
   turn a bounded-test identity

   ```text
   conditionalMean P C (fun w => f (Z w) * q (X w))
     = conditionalMean P C (f ∘ Z) * conditionalMean P C (q ∘ X)
   ```

   (available for every measurable bounded scalar `f,q`) into the corresponding coordinatewise
   first/cross-moment factorization. The result should compose directly into a finite matrix or
   outer-product equality after applying it to coordinate projections. It must support finite
   Euclidean coordinate types and normalized restricted integrals, without requiring globally
   bounded sample spaces.

2. An almost-sure support-transfer theorem from a positive finite cell and a two-valued arm. Let
   `C` be a measurable positive-mass cell, `A` a measurable event of positive conditional mass in
   `C`, and `Ypot,Yobs : Ω → ℝ`. Assume bounded-test conditional independence of `Ypot` and the
   indicator of `A` inside `C`, consistency `Yobs = Ypot` almost surely on `C ∩ A`, and
   `|Yobs| ≤ R` almost surely on `C ∩ A`. Conclude

   ```text
   ∀ᵐ w ∂P.restrict C, |Ypot w| ≤ R.
   ```

   An equivalent result phrased using `CondIndepFun`, together with a proved adapter from the
   bounded-test normalized-integral identity, is acceptable. The theorem must not assume the desired
   support bound outside the observed arm and must expose all measurability/integrability/positivity
   hypotheses explicitly.

## Expected location and constraints

Place the reusable theorem(s) under a paper-agnostic `Causalean/Mathlib/MeasureTheory/` module (slug
suggestion: `FiniteCellConditionalMoments`). Do not import any `*_Research` module or mention the
proxy-effect-law paper's `FullData`, `UCVMWModel`, matrices, latent classes, or effect radius. Standard
axioms only; no `sorry`, `admit`, custom axiom, or theorem weakening.

After promotion, F will add thin local wrappers for `conditionalMean`, assemble the model-specific
proxy-moment matrices coordinatewise, and derive the potential-outcome envelope in
`TObservedVMWMarginInclusion.lean`.

## Search and substantiality receipts

- Causalean concept/type/goal searches found no bridge from bounded-test normalized-restriction
  equalities to either result.
- Local search found only the definitions and witness-specific finite-sum lemmas.
- Mathlib search found generic event-positivity and finite-partition identities, but they do not
  compose because the assumptions are not presently represented as `CondIndepFun`.
- This is substantial reusable substrate: proving the support-transfer direction requires indicator
  approximation/truncation (or a full conditional-independence adapter), positivity of the selected
  cell/arm, restricted-measure bookkeeping, and almost-everywhere transport. It is not a thin local
  simplification.

## Existing verified progress to preserve

- `two_class_witness_valid` is now closed; state records a passing targeted build.
- Preserve `integral_witnessLaw_restrict`, `witnessLaw_real`, and
  `conditionalMean_witnessLaw` in `Helpers/Witness.lean`.
- Preserve the promoted indexed singular-value Weyl theorem and its local wrapper.
