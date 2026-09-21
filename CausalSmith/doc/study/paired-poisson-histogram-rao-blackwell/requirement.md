# Substrate requirement: paired Poisson-histogram Rao--Blackwell transfer

## Goal

Build a reusable, paper-neutral Lean package that converts an arbitrary estimator based on `n`
paired iid observations into an estimator of two independent Poisson count histograms.  When both
Poisson totals are at least `n`, the count estimator must independently average over compatible
orderings/prefixes in the two samples and pair the retained observations coordinatewise.  Prove that
its squared risk is at most the fixed paired-sample risk plus the two explicit lower-tail penalties.

This is the two-independent-sample analogue of the standard one-sample finite-histogram
Rao--Blackwell/de-Poissonization argument.  The construction must be uniform in both underlying laws:
the resulting count estimator may depend on the fixed-sample estimator and `n`, but not on either
unknown distribution or on the target parameter.

## Provides (API contract)

The promoted package should expose a coherent public API equivalent to the following. Exact names,
argument order, and harmless strengthening may follow Causalean conventions.

- For finite measurable alphabets `X` and `Y`, a measurable function
  `pairedPoissonHistogramEstimator est : (X → ℕ) × (Y → ℕ) → ℝ` for every measurable
  `est : (Fin n → X × Y) → ℝ` (an equivalent curried estimator on
  `(Fin n → X) × (Fin n → Y)` is acceptable).  If both histogram totals are at least `n`, it is the
  independent conditional average of `est` over ordered retained `n`-samples compatible with the two
  histograms, followed by coordinatewise pairing.  If either total is below `n`, it uses a specified
  fallback value, with `0` available as a corollary.

- A law identity connecting separate iid arrays with paired iid observations, for example
  ```lean
  Measure.map (fun z => fun i => (z.1 i, z.2 i))
      ((Measure.pi (fun _ : Fin n => P)).prod
        (Measure.pi (fun _ : Fin n => Q))) =
    Measure.pi (fun _ : Fin n => P.prod Q)
  ```
  under the usual probability hypotheses. Reuse
  `measurePreserving_arrowProdEquivProdArrow` or the existing product-regrouping API rather than
  rebuilding product-measure theory.

- The central pointwise squared-risk theorem.  With
  `countLaw P lam := Measure.map (fun s : FiniteSample X =>
  finiteSampleHistogram s.points) (finitePoissonSampleLaw P lam)` (and analogously for `Q`), prove a
  statement equivalent to
  ```lean
  integral (fun c =>
      (pairedPoissonHistogramEstimator est fallback c - theta) ^ 2)
      ((countLaw P lamP).prod (countLaw Q lamQ))
    ≤ integral (fun z => (est z - theta) ^ 2)
        (Measure.pi (fun _ : Fin n => P.prod Q))
      + (fallback - theta) ^ 2 *
          ((poissonMeasure lamP).real {k | k < n}
            + (poissonMeasure lamQ).real {k | k < n})
  ```
  together with the needed integrability conclusion.  An exact union-probability term is welcome;
  the displayed sum of the two marginal failure probabilities is sufficient.  The theorem must hold
  for arbitrary probability laws `P`, `Q` on the finite alphabets and arbitrary intensities
  `lamP`, `lamQ`.

- A specialization at `lamP = lamQ = 2 * n` and fallback `0`.  If `|theta| ≤ B`, derive the clean
  uniform bound
  ```lean
  poissonRisk ≤ fixedRisk + B^2 *
    (poissonMeasure (2 * n)).real {k | k < n} * 2
  ```
  and a corollary using the existing `poisson_two_n_lower_tail`.  The constant may be stated in the
  exact form naturally supplied by that theorem.

- If it materially shortens consumers, a generic minimax wrapper: for a parameter family supplying
  two probability laws and a uniformly bounded real target, the two-Poisson-count minimax risk is at
  most the fixed paired-sample minimax risk plus the common two-tail penalty.  This wrapper must only
  package the pointwise theorem; it must not mention L1 distance or any research model.

## Statement / milestones

1. Reuse the existing one-sample finite-histogram conditional averaging machinery where possible.
   Define a two-histogram conditional average as the product/iteration of the two one-sample kernels,
   not as an enumeration tied to a particular alphabet.
2. Prove measurability and show that, conditional on totals `N₁,N₂ ≥ n`, independent random orderings
   and retained prefixes have the fixed law of two independent length-`n` iid arrays.
3. Apply conditional Jensen for squared loss to the product kernel.  Regroup the two retained arrays
   into paired observations and identify their law as `pi (fun _ => P.prod Q)`.
4. Split the count experiment into the event that both totals are at least `n` and its complement.
   Bound the complement by the sum of the two marginal Poisson lower tails.  Keep the fallback loss
   explicit before specializing to fallback `0` and a bounded target.
5. Supply the `Pois(2n)` lower-tail corollary from the existing public de-Poissonization theorem; do
   not assume an exponential tail certificate.

## Mathematical validity constraints

- The two Poisson totals are independent and generally unequal.  Do not replace them by a single
  shared Poisson total or Poissonize the paired alphabet `X × Y`; either replacement gives a different
  experiment.
- The count estimator must be parameter-independent.  It cannot use `P`, `Q`, `theta`, a likelihood,
  or a parameter-specific conditional distribution.
- Histogram counts do not determine an ordering.  The construction must average over compatible
  orderings (or use an equivalent law-level conditional kernel), rather than selecting a fixed
  ordering and claiming it is iid.
- The fixed experiment consists of `n` draws from each law, paired coordinatewise.  The proof must
  include the measurable equivalence between two independent iid arrays and an iid array from
  `P.prod Q`.
- On the failure event, the additive loss is `(fallback - theta)^2` times the failure probability.
  For fallback `0`, it is `theta^2`, not an unexplained unit penalty unless `|theta| ≤ 1` is assumed.

## Standard reference

This is the standard histogram sufficiency and Rao--Blackwell argument applied independently to two
samples, followed by fixed-to-Poisson comparison using two independent lower-tail events.  No
paper-specific result is being cited.  The Lean development must derive the theorem from conditional
averaging, Jensen, finite iid product laws, and the existing Poisson-sample/count representation.

## Intended reuse

The immediate consumer has two unknown categorical laws, receives `n` observations from each, and
uses a cited lower bound stated for two independent Poisson count vectors with means `2n P_x` and
`2n Q_x`.  It needs a single parameter-independent count estimator derived from every fixed-sample
estimator.  Other two-sample functional problems (distance, divergence, closeness testing, and
two-population discrete estimation) share exactly this bridge.

## May assume / must derive

May assume existing Mathlib/Causalean results about finite product measures, `FiniteSample`,
`finiteSampleHistogram`, `finitePoissonSampleLaw`, its count/histogram law, probability kernels,
conditional Jensen/Rao--Blackwell contraction, `measurePreserving_arrowProdEquivProdArrow`, and
`poisson_two_n_lower_tail`.

Must derive the two-independent-histogram estimator, its parameter independence and measurability,
the paired fixed-law identity, the product conditional-risk inequality, the two-tail failure split,
and the `Pois(2n)` specialization.  Do not expose any of these as a caller-supplied certificate,
axiom, opaque declaration, cited premise, or unproved assumption.

## Non-goals

- Do not import or mention `CausalSmith/*_Research`, causal models, optimal policies, L1 distance,
  simplex padding, minimax regime splicing, Cai--Low, or Jiao--Han--Weissman.
- Do not prove alphabet-padding monotonicity; that is paper-specific consumer work once this generic
  bridge is available.
- Do not duplicate the existing one-sample histogram package wholesale when its public lemmas can be
  factored or reused.
- Do not claim equality between the two-independent-Poisson experiment and a single Poisson sample
  on `X × Y`.

## Known building blocks and proposed imports

Search and build from:

- `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic`;
- `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization`;
- `Causalean.Stat.FiniteRaoBlackwell`;
- `Causalean.Stat.Minimax.MarkovKernelTransport`;
- Mathlib product-measure, finite-product, conditional-expectation/Jensen, and Poisson modules.

The non-importable research file
`CausalSmith/Stat/STAT_DiscreteAteMinimaxLoggap_Research/Helpers/OneArmRaoBlackwell.lean` is only a
blueprint for the one-sample conditional-average argument.  If useful, first extract its genuinely
paper-neutral one-sample dependency closure into Causalean; the study and promoted result must not
import that research module.

## Extraction boundary

Develop and review the implementation in the normal study location. Promote the complete
paper-neutral dependency closure into Causalean. Promoted modules may import only Mathlib and
Causalean modules and must contain no reference to the immediate research consumer.
