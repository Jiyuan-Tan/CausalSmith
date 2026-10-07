module
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1

/-!
# Minimax lower bounds for functionals of finite multinomial distributions

Estimating the L1 distance `‖R − S‖₁` between two probability vectors on `k` symbols from two
independent i.i.d. samples of fixed size `n` each. There is a universal constant `c > 0` such that
for every `k ≥ 2` and every `n > k²` the minimax squared risk is at least `c · k / (n log(e k))`.
The proof is the method of two fuzzy hypotheses: moment-matched priors on `[−1, 1]` whose mean
absolute values differ by at least `1/(50 L)` are replicated over balanced pairs of cells, the
fixed-size experiment is compared with a Poissonized one, and the total variation between the two
predictive mixtures is controlled through independent Poisson cell counts.

## Main results (in `Causalean.Stat.Minimax.Multinomial.TwoSampleL1`)

* `twoSampleL1MinimaxRisk_largeSample_lower` — the `k / (n log(e k))` lower bound above, for the
  minimax risk `twoSampleL1MinimaxRisk n k` of the exact fixed-sample experiment.
* `FuzzyCertificate.minimax_lower` — a pair of finite priors with target centres `δ` apart and
  predictive mixtures within 1/16 in total variation gives minimax risk at least `11 δ² / 512`.

Only the lower bound is proved here; no matching upper bound (estimator) is given. This file
gathers the `TwoSampleL1` development and declares nothing itself.
-/
