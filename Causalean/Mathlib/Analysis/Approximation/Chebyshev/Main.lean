/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Markov

/-!
# Best polynomial approximation, alternation certificates and Markov's inequality

For a continuous function f on a compact interval [r, s] and a degree bound L, a best uniform
polynomial approximant exists, and its error E_L(f) is certified by L + 2 increasing nodes with
signed weights of total absolute mass one that annihilate every polynomial of degree at most L
and whose weighted sum of f has absolute value exactly E_L(f). The same certificate is given for
the rational target x ↦ x/(x + a) whenever the pole −a lies outside the interval. Polynomials of
degree at most L satisfy Markov's inequality: the sup norm of the derivative on [r, s] is at most
2L²/(s − r) times the sup norm of the polynomial.

## Main results

* `exists_bestPolynomial` — existence of a best approximant of degree at most L.
* `exists_alternationDualCertificate`, `exists_finiteMomentDual` — the alternating node-and-weight
  certificate for the best error (`AlternationDualCertificate`, `FiniteMomentDual`).
* `exists_rationalFiniteMomentDual` — the certificate for x ↦ x/(x + a).
* `markov_derivative_unitInterval`, `markov_derivative_Icc` — Markov's inequality on [−1, 1] and
  on a general interval.

This file only gathers the `Alternation` and `Markov` modules.
-/

public section
