module
public import Causalean.Stat.Concentration.Localization.Bousquet
public import Causalean.Stat.Concentration.Localization.CriticalRadius
public import Causalean.Stat.Concentration.Localization.ERMOracle
public import Causalean.Stat.Concentration.Localization.LocalizedEnvelopeExpectation
public import Causalean.Stat.Concentration.Localization.PeelingRates
public import Causalean.Stat.Concentration.Localization.UniformDeviation

/-!
Localization: sharp rates for empirical risk minimisation by restricting attention to a small
ball around the target rather than the whole model class. A uniform bound over the entire class
is loose whenever the minimiser is known to lie nearby, and localization recovers the missing
sharpness — the fast rate is governed by the *critical radius*, the fixed point where the local
Rademacher complexity stops growing as fast as the radius itself.

Provides `criticalRadius` and its `IsStarShapedEnvelope` fixed-point theory, the star-hull constructions
(`starHullBall`, `starHullZeroOut`, `IsStarShapedEnvelope`) that make the local complexity
well behaved, the peeling machinery (`PeelingCondition`, `lipschitzPeelingRate`) that assembles
shell-wise bounds into one statement, Bousquet's inequality as the concentration engine, the
localized uniform-deviation bounds themselves, and the ERM oracle inequality they deliver.

Following Bartlett–Bousquet–Mendelson (2005) and Koltchinskii; see also Wainwright (2019), ch. 13–14.
-/
