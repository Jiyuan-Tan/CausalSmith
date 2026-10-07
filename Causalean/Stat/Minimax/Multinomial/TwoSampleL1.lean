module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.Definitions
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FinitePoissonPrefix
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FixedPoissonBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FuzzyCertificate
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FuzzyRisk
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.LargeSample
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedAlphabetPadding
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedFixedPredictive
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedLargeParameters
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonCountBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonMixtureBridge
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedPoissonPredictive
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedProductPrior
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedSimplex
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetConcentration
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.PairedTargetTail
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarMomentPriors
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonComparison
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPoissonLikelihood
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.ScalarPriorMeasure

/-!
# Minimax lower bound for the L1 distance between two multinomials

Estimating the L1 distance `‖R − S‖₁` between two probability vectors on `k` symbols from two
independent i.i.d. samples of fixed size `n` each. There is a universal constant `c > 0` such that
for every `k ≥ 2` and every `n > k²` the minimax squared risk is at least `c · k / (n log(e k))`.
The proof is the method of two fuzzy hypotheses: moment-matched priors on `[−1, 1]` whose mean
absolute values differ by at least `1/(50 L)` are replicated over balanced pairs of cells, the
fixed-size experiment is compared with a Poissonized one, and the total variation between the two
predictive mixtures is controlled through independent Poisson cell counts.

## Main definitions and results

* `ProbabilitySimplex`, `simplexL1`, `twoSampleLaw`, `twoSampleL1MinimaxRisk` — the exact
  fixed-sample experiment, the target, and its minimax squared risk.
* `twoSampleL1MinimaxRisk_largeSample_lower` — the lower bound `c · k / (n log(e k))` for `k ≥ 2`,
  `n > k²`.
* `FuzzyCertificate`, `FuzzyCertificate.minimax_lower` — a finite two-prior certificate with
  separation `δ` implies minimax risk at least `11 δ² / 512`; `largeSample_fuzzyCertificate`
  constructs one with `δ² ≥ a · k / (n log(e k))`.
* `exists_scalarMomentPriors` — the moment-matched scalar priors for the absolute-value cusp.
* `fixedSampleMixture_tv_le_finitePoisson` — total variation between mixtures of fixed-size
  samples is at most that between Poissonized mixtures plus twice the probability that the
  Poisson count falls below `n`.
* `scalarPoissonPredictive_tv_le`, `pairedPoissonPredictive_tv_le`, `pairedFixedPredictive_tv_le` —
  the predictive total-variation bounds for one balanced pair, the product over pairs, and the
  fixed-sample experiment.
* `pairedProductTarget_variance_le`, `pairedProductTarget_bad_mass_le` — concentration of the L1
  target under the product prior.
* `padSimplex_l1`, `twoSampleLaw_pad` — adding zero-probability cells preserves target and law.

Only the lower bound is proved; no matching upper bound is given.
-/
