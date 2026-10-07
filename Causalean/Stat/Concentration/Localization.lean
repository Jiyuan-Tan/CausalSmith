module
public import Causalean.Stat.Concentration.Localization.Bousquet
public import Causalean.Stat.Concentration.Localization.CountableReduction
public import Causalean.Stat.Concentration.Localization.CriticalRadius
public import Causalean.Stat.Concentration.Localization.ERMOracle
public import Causalean.Stat.Concentration.Localization.LocalizedEnvelopeExpectation
public import Causalean.Stat.Concentration.Localization.NormComparison
public import Causalean.Stat.Concentration.Localization.PeelingProbability
public import Causalean.Stat.Concentration.Localization.PeelingRates
public import Causalean.Stat.Concentration.Localization.SquaredProcess
public import Causalean.Stat.Concentration.Localization.UniformDeviation

/-!
Localization: fast-rate upper bounds for empirical risk minimisation by restricting attention to
a small ball around the target rather than the whole model class. A uniform bound over the
entire class is loose whenever the minimiser is known to lie nearby, and localization tightens
it — the fast rate is governed by the *critical radius*, the fixed point where the local
Rademacher complexity stops growing as fast as the radius itself. The results here are upper
bounds; no matching lower bound is proved.

Provides `criticalRadius` and its `IsStarShapedEnvelope` fixed-point theory, the star-hull constructions
(`starHullBall`, `starHullZeroOut`, `IsStarShapedEnvelope`) that make the local complexity
well behaved, the peeling machinery (`PeelingCondition`, `lipschitzPeelingRate`) that assembles
shell-wise bounds into one statement, Bousquet's inequality as the concentration engine, the
localized uniform-deviation bounds themselves, and the ERM oracle inequality they deliver.

For localization in the population L² norm it also provides the uniform comparison of
empirical and population L² norms over the star hull of a bounded countable class above the
critical radius (`populationNormComparisonEvent`, `populationNormComparisonEvent_compl_le`,
with failure probability 4·exp(−n·δ²/(65536·b²))), its consequence that population
localization at radius r implies empirical localization at radius √2·r
(`population_localization_transfer`), and the supporting countable reduction
(`populationLocalizedRepresentative`), squared-process concentration and dyadic peeling bound.

Following Bartlett–Bousquet–Mendelson (2005) and Koltchinskii; see also Wainwright (2019), ch. 13–14.
-/
