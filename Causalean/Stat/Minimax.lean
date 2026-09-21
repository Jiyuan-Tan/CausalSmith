/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Minimax.Assouad
public import Causalean.Stat.Minimax.BretagnolleHuber
public import Causalean.Stat.Minimax.ChiSquared
public import Causalean.Stat.Minimax.ChiSquaredFinite
public import Causalean.Stat.Minimax.ChiSquaredKernel
public import Causalean.Stat.Minimax.ChiSquaredTwoPoint
public import Causalean.Stat.Minimax.CoordinatewiseOverlap
public import Causalean.Stat.Minimax.Fano
public import Causalean.Stat.Minimax.FanoInformationRadius
public import Causalean.Stat.Minimax.FiniteKernelBayes
public import Causalean.Stat.Minimax.FinitePosteriorBayesRisk
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.HellingerAffinity
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.KLTail
public import Causalean.Stat.Minimax.LIntegralRisk
public import Causalean.Stat.Minimax.LeCam
public import Causalean.Stat.Minimax.LeCamTwoPoint
public import Causalean.Stat.Minimax.MarkovKernelTransport
public import Causalean.Stat.Minimax.OverlapCoupling
public import Causalean.Stat.Minimax.MinimaxRisk
public import Causalean.Stat.Minimax.MinimaxValue
public import Causalean.Stat.Minimax.Mixture
public import Causalean.Stat.Minimax.Mixture.MomentMatched
public import Causalean.Stat.Minimax.Pinsker
public import Causalean.Stat.Minimax.Scheffe
public import Causalean.Stat.Minimax.SequentialCumulativeRisk
public import Causalean.Stat.Minimax.SideInformation
public import Causalean.Stat.Minimax.SideInformation.Finite
public import Causalean.Stat.Minimax.SquaredLoss
public import Causalean.Stat.Minimax.SquaredLoss.Finite.Core
public import Causalean.Stat.Minimax.SquaredLoss.Finite.Mixing
public import Causalean.Stat.Minimax.SquaredLoss.Finite.PosteriorBarycenter
public import Causalean.Stat.Minimax.SquaredLoss.Finite.Saddle
public import Causalean.Stat.Minimax.TotalVariation
public import Causalean.Stat.Minimax.TsybakovFano
public import Causalean.Stat.Minimax.VanTrees
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Basic
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.GuardedInformation
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.IntegrationByParts
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.Main
public import Causalean.Stat.Minimax.VanTrees.ObservationDependent.WeightedL2
public import Causalean.Stat.Minimax.VanTreesInequality
public import Causalean.Stat.Minimax.VanTreesSmoothModel

/-!
Minimax risk: the best worst-case performance any procedure can achieve over a model class,
and the standard devices for lower-bounding it.

Provides the risk and value definitions themselves, the information-theoretic distances they
are argued through (total variation, Hellinger, chi-squared, KL, with Pinsker, Scheffe and
Bretagnolle-Huber relating them), and the four classical reduction devices: two-point and
multiple-hypothesis testing (Le Cam, Fano, Assouad), and the Bayesian Cramer-Rao route
(van Trees), which bounds Bayes risk by prior plus average experimental information and so
stays finite where the frequentist Cramer-Rao bound degenerates.

Also covers sequential experiments, where a per-round information bound is accumulated into a
cumulative-regret lower bound, and side-information and squared-loss specialisations.
-/
