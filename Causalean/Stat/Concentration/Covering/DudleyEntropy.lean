module
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.Chaining
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.PartA
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.PartB
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.RiemannIntegral
public import Causalean.Stat.Concentration.Covering.DudleyEntropy.EntropyBound

/-! # Dudley's entropy-integral bound for empirical Rademacher complexity

Dudley's chaining bound. For a function class restricted to a sample of size m, with every
empirical L² norm at most c and the restricted class totally bounded in the empirical
pseudometric, the empirical Rademacher complexity (without the outer absolute value) is at most

    4ε + (12/√m) ∫ from ε to c/2 of √(log N(x)) dx

for every scale 0 < ε < c/2, where N(x) is the covering number of the class at radius x. The
proof builds a dyadic chain of cover approximations, bounds the coarse remainder by the final
radius, bounds each chain increment by Massart's finite-class lemma, and compares the resulting
dyadic entropy sum with the integral.

## Main results

* `dudley_entropy_integral_bound` (`DudleyEntropy.EntropyBound`) — the bound above.
* `partA_sup_bound`, `partB_bound` (`DudleyEntropy.PartA`, `DudleyEntropy.PartB`) — the
  remainder term and the chain-increment term.
* `entropy_sum_to_integral_bound`, `choose_dyadic_scale_for_epsilon`
  (`DudleyEntropy.RiemannIntegral`) — the dyadic entropy sum is dominated by the entropy
  integral, and a dyadic truncation level exists for each cutoff ε.
* `coverApprox`, `chainApprox` (`DudleyEntropy.Chaining`) — the cover representatives and the
  chain they form.
-/
