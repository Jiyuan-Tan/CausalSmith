/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Duality.MomentPrior
public import Causalean.Mathlib.Analysis.Analytic
public import Causalean.Mathlib.Analysis.Approximation
public import Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple.ArgumentPrinciple
public import Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple.Basic
public import Causalean.Mathlib.Analysis.Complex.ArgumentPrinciple.Homotopy
public import Causalean.Mathlib.Analysis.BernoulliKL
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Trigonometric
public import Causalean.Mathlib.Analysis.Calculus.HolderTaylor
public import Causalean.Mathlib.Analysis.IntervalArithmetic
public import Causalean.Mathlib.Analysis.ClipInterval
public import Causalean.Mathlib.Analysis.Complex
public import Causalean.Mathlib.Analysis.Convex.ReciprocalProduct
public import Causalean.Mathlib.Analysis.ConvexProjection
public import Causalean.Mathlib.Analysis.Duality
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Bernstein
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Mesh
public import Causalean.Mathlib.Analysis.NormedSpace.Duality.L1Linf
public import Causalean.Mathlib.Analysis.FrechetFunctionalEquation
public import Causalean.Mathlib.Analysis.GradientCoord
public import Causalean.Mathlib.Analysis.HalfDiscPolar
public import Causalean.Mathlib.Analysis.InnerProductSpace
public import Causalean.Mathlib.Analysis.IntervalArithmetic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson
public import Causalean.Mathlib.Analysis.LineSecondDeriv
public import Causalean.Mathlib.Analysis.LocallyBoundedDerivative
public import Causalean.Mathlib.Analysis.LogRatioStability
public import Causalean.Mathlib.Analysis.MonomialGram
public import Causalean.Mathlib.Analysis.NormedSpace
public import Causalean.Mathlib.Analysis.OffsetPeeling
public import Causalean.Mathlib.Analysis.Analytic.ParametricIntegral.Rational
public import Causalean.Mathlib.Analysis.RankOneGramPseudoinverse
public import Causalean.Mathlib.Analysis.RankOneWaldSmoothness
public import Causalean.Mathlib.Analysis.RectangularSignalSingularValues
public import Causalean.Mathlib.Analysis.RpowArith
public import Causalean.Mathlib.Analysis.SecondOrderDescent
public import Causalean.Mathlib.Analysis.SignedTailRepresentation
public import Causalean.Mathlib.Analysis.SingularValueWeyl
public import Causalean.Mathlib.Analysis.SmoothReciprocal
public import Causalean.Mathlib.Analysis.SpecialFunctions.PowerIntegral
public import Causalean.Mathlib.Analysis.TwoByTwoSpectralProjector
public import Causalean.Mathlib.Analysis.TwoByTwoSpectralRoots
public import Causalean.Mathlib.Analysis.WeightedCauchySchwarz
public import Causalean.Mathlib.Analysis.Complex.Circle.WeightedTube.Basic
public import Causalean.Mathlib.Analysis.Complex.Circle.WeightedTube.Packing
public import Causalean.Mathlib.Analysis.Complex.Circle.WeightedTube.SideMass

/-!
Analytic tools for approximation, convexity, smoothness, matrix perturbation, interval certification, complex root analysis, and Hilbert-space geometry. They provide reusable quantitative estimates for statistical and optimization arguments.
-/
