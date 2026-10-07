/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.MinimaxATE.Causal.Bridge_Part3
/-!
# Causal identification for the finite minimax ATE construction

The lower-bound construction for average-treatment-effect estimation uses a finite covariate
set with the uniform distribution, a propensity function m and an outcome regression g, and
works with the observed-data contrast equal to the uniform average over covariate values x of
g(1,x) − g(0,x). This development builds a potential-outcome system with back-door adjustment
that generates the same data and proves that, for a valid pair (m, g) with 0 < m(x) < 1 at every
x, its causal effect E[Y(1) − Y(0)] equals that contrast. Minimax lower bounds for the contrast
are therefore lower bounds for a causal average treatment effect.

## Contents

* `Bridge_Part1` — the causal effect `causalATE` of the constructed system, consistency, and
  coordinate formulas for its covariate, treatment and outcome variables.
* `Bridge_Part2` — conditional expectations of the treatment and outcome noises given the
  covariate.
* `Bridge_Part3` — unconfoundedness, overlap, the propensity score and outcome regression of the
  constructed system (`dgp_assumptions`, `dgp_propScore_eq_m`, `dgp_adjustedCE_eq_g`), and the
  identification theorem `causalATE_eq_ate`.
-/
