/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.MomentProblems.GaussianPerturbation.Main

/-!
# Finite-moment Gaussian perturbations

This barrel exports the construction of non-Gaussian probability laws arbitrarily close to the
standard Gaussian that preserve any prescribed finite initial segment of raw moments and
cumulants. It also exports the orthogonal perturbation, density, cumulant-transfer, and Carleman
ingredients used by that construction.
-/

public section
