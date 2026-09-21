# Substrate requirement: capped Poisson Rao--Blackwell risk transfer

## Goal

Build a reusable, paper-neutral Lean package that transfers a squared-risk bound from an
uncapped Poisson sample to the Rao--Blackwellized statistic constructed from a fixed iid sample by
retaining only a Poisson-length prefix. Include only a thin product-regrouping convenience result
if it is genuinely absent from the existing library.

## Provides (API contract)

The promoted package should expose a coherent public API equivalent to the following.  Exact
names and harmless strengthening may change to fit Causalean conventions.

- A measurable construction which, from a fixed sample `x : Fin n → X` and an auxiliary count
  `M : ℕ`, returns the prefix of length `M` when `M ≤ n`. The overflow branch `M > n` must remain
  separately visible, preferably with `Option.none` or a sum type, rather than being identified with
  a genuine empty observation.
- For a probability law `P` on `X`, identify the law of that prefix on `{M ≤ n}` with the
  restriction of `finitePoissonSampleLaw P lambda` to the same count event, on the same
  `FiniteSample X` output space. A target statement is
  `map (fun z => cappedPrefix n z.1 z.2)
      (((pi (fun _ : Fin n => P)).prod (poissonMeasure lambda)).restrict
        (Prod.snd ⁻¹' Set.Iic n))
    = (finitePoissonSampleLaw P lambda).restrict
        (FiniteSample.count ⁻¹' Set.Iic n)`,
  up to a harmless swap in product order. The arbitrary overflow totalization is irrelevant only
  because both sides are restricted. The result must cover arbitrary `lambda : ℝ≥0` and must not
  assume a uniform observation law.
- Define, or directly characterize, the fixed-sample Rao--Blackwell statistic obtained by
  integrating a bounded measurable statistic `T` of the prefix over the independent
  Poisson count, using a specified overflow value on `M > n`.
- Prove the squared-loss contraction/transfer for a bounded interval: if measurable `T`, the target
  `theta`, and overflow value `z_over` lie in `[a,b]`, then the fixed-iid-sample risk of the
  auxiliary-kernel mean of `if M ≤ n then T (prefix sample M) else z_over` is at most
  `sqRisk (finitePoissonSampleLaw P lambda) T theta
    + (b-a)^2 * (poissonMeasure lambda).real (Set.Ioi n)`.
  Thus for `[0,1]` the additive term is exactly the overflow probability, not twice that
  probability. State this at the level of measures and kernels/integrals so `P` may be a nonuniform
  categorical law or a product observation--mark law.
- A quantitative corollary for `lambda = n/4`, `n > 0`, bounding the overflow contribution by a
  universal constant times `1/n` (an exponentially smaller bound is welcome).  Derive it from a
  genuine Poisson Chernoff/Bernstein bound; do not assume it as a certificate.
- Audit the existing product regrouping and finite-sum variance API. If a genuinely missing thin
  wrapper is needed, provide a theorem converting a product of two coordinate arrays into an array
  of coordinate pairs before applying `variance_sum_pi`. Do not duplicate the existing independent-
  sum variance machinery. The immediate consumer will prove its paper-owned joint count-table law
  and bias--variance arithmetic locally.

## Statement / milestones

1. Reuse the existing `FiniteMarkedPoissonPartition` finite-sample representation and its
   count-restriction theorem. Define the fixed-prefix map and prove the restricted-law equality on
   the common `FiniteSample X` output space by conditioning on each count `M ≤ n`.
2. Package the auxiliary Poisson count as a probability kernel from the fixed sample.
   Show that its kernel mean is exactly the iterated integral defining the Rao--Blackwell statistic.
3. Apply the existing Markov-kernel Jensen/squared-risk contraction theorem, then split the
   randomized risk into the nonoverflow and overflow events.  Use the restricted-law equality for
   the first term and `[0,1]` loss bounds for the second.
4. Obtain the `Pois(n/4)` overshoot estimate from the public Poisson Bernstein API, including the
   small positive values of `n`. A valid route uses `poisson_upper_bernstein` at `z=n/8`, giving
   `P(M>n) ≤ exp(-n/8)`, followed by a universal `C/n` bound. Do not use the existing `Pois(2n)`
   lower-tail theorem or the atomless-prefix result, whose direction and hypotheses are wrong here.
5. Reuse `measurePreserving_arrowProdEquivProdArrow` to regroup separate iid observation and mark
   arrays into iid pairs. If an API gap remains, add only the smallest generic regrouping wrapper
   needed before applying `ProbabilityTheory.variance_sum_pi`.

## Standard reference

The argument is the standard random-prefix representation of an iid Poisson sample, followed by
conditional Jensen (Rao--Blackwell) for squared loss and an explicit split on the overflow event.
The count-tail input is the ordinary Poisson Chernoff/Bernstein inequality. The product regrouping
step is the canonical equivalence between an array of pairs and a pair of arrays. The Lean
development must derive the displayed restricted-law and risk statements from these standard
principles rather than cite them as assumptions.

## Intended reuse

The immediate consumer instantiates `P` with the product of a nonuniform finite categorical
observation law and a fair binary mark law, then uses a `[0,1]`-projected statistic of the resulting
Poisson sample. Separate observation and mark arrays can be regrouped with
`measurePreserving_arrowProdEquivProdArrow`; the consumer must prove the full joint count-table law
needed for cross-cell independence, since individual cell marginals do not suffice. The promoted
API must remain independent of that estimator, its cell functional, and its tuning constants.

## May assume / must derive

May assume existing Mathlib/Causalean facts about product measures, finite iid samples, probability
kernels, kernel means and Jensen contraction, `finitePoissonSampleLaw`, iid marking/splitting,
Poisson Bernstein tails, interval projection, expectation/variance, and finite independent sums.

Must derive the capped-prefix restricted-law identity, the risk comparison including overflow, and
the quarter-mean overflow estimate. Add a product-regrouping convenience theorem only if exact
search shows it is missing. Do not expose any deliverable as a caller-supplied certificate,
structure field, axiom, cited hypothesis, or unproved assumption.

## Non-goals

- Do not import or mention research modules, causal models, treatment, outcomes, policies,
  Jackson polynomials, factorial estimators, pilots, confounder cells, or minimax rates.
- Do not encode the immediate consumer's cell count table or assert its joint law.
- Do not assume that the capped and uncapped laws are globally equal: they differ on `M > n`.
- Do not replace the overflow term by an unspecified `o(1)` or asymptotic statement.
- Do not require the base observation law to be uniform or finitely supported unless a theorem
  genuinely needs that restriction; isolate any finite/discrete assumptions to the mark space or
  to measurability infrastructure.

## Known building blocks

Search first in:

- `Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Basic` and its partition/splitting and
  de-Poissonization modules;
- `Causalean.Stat.Minimax.MarkovKernelTransport`, especially `kernelMean` and
  `sqRisk_kernelMean_le_comp`;
- `Causalean.Stat.FiniteRaoBlackwell` for finite conditional averaging patterns;
- the public `Causalean.Stat.Concentration.PoissonSelfNormalized.Chernoff` tail API;
- `MeasureTheory.measurePreserving_arrowProdEquivProdArrow` for regrouping separate iid arrays;
- Mathlib's `ProbabilityTheory.variance_sum_pi`, `IndepFun.variance_sum`, and interval projection
  lemmas.

## Extraction boundary

Develop and review the implementation in the normal study location.  Promote the complete
paper-neutral dependency closure into Causalean.  Promoted modules may import only Mathlib and
Causalean modules and must contain no reference to the immediate research consumer.
