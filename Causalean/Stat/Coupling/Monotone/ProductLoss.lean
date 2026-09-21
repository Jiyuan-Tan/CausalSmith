/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.FrechetHoeffding
public import Causalean.Stat.Coupling.Monotone.ProductLoss.FrechetHoeffdingAttainment
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Hoeffding
public import Causalean.Stat.Coupling.Monotone.ProductLoss.HoeffdingFubini
public import Causalean.Stat.Coupling.Monotone.ProductLoss.HoeffdingFubiniIntegrability
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Survival
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Coupling
public import Causalean.Stat.Coupling.Monotone.ProductLoss.FrechetHoeffding
public import Causalean.Stat.Coupling.Monotone.ProductLoss.FrechetHoeffdingAttainment
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Hoeffding
public import Causalean.Stat.Coupling.Monotone.ProductLoss.HoeffdingFubini
public import Causalean.Stat.Coupling.Monotone.ProductLoss.HoeffdingFubiniIntegrability
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Optimality
public import Causalean.Stat.Coupling.Monotone.ProductLoss.PIT
public import Causalean.Stat.Coupling.Monotone.ProductLoss.Survival

/-!
# Product-loss monotone couplings

This module collects the coupling construction and optimality theorem showing
that, among all couplings of two real probability measures with finite second
moments, the product expectation is largest at the comonotone quantile coupling
and smallest at the countermonotone quantile coupling.

The leaf files provide the probability integral transform for the quantile,
explicit monotone couplings, sharp Fréchet-Hoeffding cdf bounds, Hoeffding's
covariance identity, and the product-expectation optimality capstone.
-/
