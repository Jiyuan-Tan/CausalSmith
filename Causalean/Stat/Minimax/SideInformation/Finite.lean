module
public import Causalean.Stat.Minimax.SideInformation.Finite.Approximation
public import Causalean.Stat.Minimax.SideInformation.Finite.Comparison
public import Causalean.Stat.Minimax.SideInformation.Finite.Concentration
public import Causalean.Stat.Minimax.SideInformation.Finite.Coordinates
public import Causalean.Stat.Minimax.SideInformation.Finite.Experiments
public import Causalean.Stat.Minimax.SideInformation.Finite.Fiber
public import Causalean.Stat.Minimax.SideInformation.Finite.Main
public import Causalean.Stat.Minimax.SideInformation.Finite.Measurable
public import Causalean.Stat.Minimax.SideInformation.Finite.Risk
public import Causalean.Stat.Minimax.SideInformation.Finite.Selector
public import Causalean.Stat.Minimax.SideInformation.Finite.SimplexSpecialization
public import Causalean.Stat.Minimax.SideInformation.Finite.Approximation
public import Causalean.Stat.Minimax.SideInformation.Finite.Comparison
public import Causalean.Stat.Minimax.SideInformation.Finite.Concentration
public import Causalean.Stat.Minimax.SideInformation.Finite.Coordinates
public import Causalean.Stat.Minimax.SideInformation.Finite.Experiments
public import Causalean.Stat.Minimax.SideInformation.Finite.Fiber
public import Causalean.Stat.Minimax.SideInformation.Finite.Main
public import Causalean.Stat.Minimax.SideInformation.Finite.Measurable
public import Causalean.Stat.Minimax.SideInformation.Finite.Risk
public import Causalean.Stat.Minimax.SideInformation.Finite.Selector
public import Causalean.Stat.Minimax.SideInformation.Finite.SimplexSpecialization


/-!
# Minimax risk with finite side information: empirical versus exact side law

A statistician observes one draw from a finite labelled law `p(θ)` and wants to estimate a bounded
target `τ(θ) ∈ [l, u]` under squared loss; in addition she has side information about a second
finite law `q(θ)`. In the empirical experiment the side information is `m` i.i.d. draws from
`q(θ)`; in the exact experiment the vector `q(θ)` itself is revealed. For a compact parameter
space with `p`, `q` and `τ` continuous, the minimax risk of the empirical experiment converges, as
`m → ∞`, to the minimax risk of the exact experiment, which equals the supremum over parameters of
the minimax risks on the fibres `{θ : q(θ) = q(θ₀)}`.

## Main results

* `finiteSideInfo_minimax_tendsto` — the convergence theorem;
  `closedSimplex_finiteSideInfo_minimax_tendsto` — its form for a closed model class inside a
  finite probability simplex.
* `exactSideMinimaxValue_le_empiricalSideMinimaxValue` — the lower comparison, by conditional
  averaging of an empirical procedure and convexity of squared loss.
* `empiricalSideMinimax_limsup_le_exact` — the upper comparison, by a finite cover of side-law
  space and concentration of empirical frequencies.
* `exactSideMinimaxValue_eq_iSup_fiber` — the exact minimax value as a supremum of fibrewise values;
  `localMinimaxValue_tendsto_fiber` — minimax values over shrinking neighbourhoods of a side law
  converge to the fibre value.
* `empiricalL1_tail` — `P(‖q̂ − q‖₁ ≥ ε) ≤ 2 |C| exp(−2 m (ε/|C|)²)` for empirical frequencies on
  a finite alphabet `C`.

The remaining modules supply simplex coordinates (`FinitePmf`), bounded decision rules and their
squared risks, the two experiments, a measurable finite-cover selector, and a bridge to measurable
procedures on ambient probability tables.
-/
