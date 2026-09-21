module
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Analytic
public import Causalean.Stat.Minimax.Mixture.MomentMatched.ExponentialEnergy
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Main
public import Causalean.Stat.Minimax.Mixture.MomentMatched.Product
public import Causalean.Stat.Minimax.Mixture.MomentMatched.SupportLocalized
/-!
# Moment-matched mixtures and fuzzy minimax lower bounds

This umbrella module exports a model-agnostic path from exponential likelihood inner products
and matched bounded-prior moments, through one-coordinate and finite-product total variation,
to explicit squared-error lower bounds for every estimator and for the measurable-estimator
minimax value.
-/
