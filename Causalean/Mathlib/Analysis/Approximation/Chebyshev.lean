/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AbsoluteValue
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.AffineFourBoundary
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Alternation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Basic
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.BasicBernsteinSzegoTrig
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Bernstein
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevChordGeometry
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ChebyshevOneNorm
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CoefficientEnvelopeFour
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.CosineProjection
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.DuffinSchaeffer
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Equioscillation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedDistance
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.EquispacedLagrange
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ExtremalSignPolynomial
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HalfPlaneDerivativeComparison
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensorExtraction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.HeterogeneousTensorInterpolation
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Interp
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Jackson
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Kernel
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.LobattoLagrange
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Main
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Markov
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Mesh
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PairingRearrangement
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricHeterogeneousTensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.ParametricTensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.PolynomialOneNorm
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Reciprocal
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Szego
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Tensor
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorChebyshev
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorExtraction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TensorGridWeights
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigExtraction
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.TrigPoly
public import Causalean.Mathlib.Analysis.Approximation.Chebyshev.Trigonometric

/-!
# Polynomial approximation on intervals and cubes: Chebyshev, Markov, Jackson

Quantitative theory of uniform approximation by real polynomials. On a compact interval a
continuous function has a best approximant of each degree, whose error equioscillates at L + 2
points (Chebyshev's alternation theorem, necessity direction); polynomials of degree at most L
satisfy Markov's inequality ‖Q′‖ ≤ L²·‖Q‖ on [−1, 1], obtained from the Duffin–Schaeffer bound in
terms of the values at the Chebyshev extrema, and the Szegő inequality for Q(cos t). The exact
best error is computed for 1/x on a positive interval, and |x| on [−1, 1] is approximated to
within 2/(π(2m + 1)) by an explicit even Chebyshev sum. Tensor Jackson kernels give multivariate
polynomials approximating an ℓ¹-Lipschitz function on the cube [−1,1]^d to within 32·d·L/K, with
control of degrees and of the size of the monomial coefficients.

## Contents

* Best approximation and alternation: `Basic` (`exists_bestPolynomial`),
  `ExtremalSignPolynomial`, `Equioscillation` (`exists_equioscillationWitness`), `Alternation`
  (signed Lagrange weights that annihilate degree ≤ L and attain the best error:
  `exists_finiteMomentDual`), `Main`, and `Reciprocal` (`bestUniformApproxError_reciprocal`).
* Derivative and norming inequalities: `TrigPoly` (a trigonometric polynomial of degree n has at
  most 2n zeros per period), `BasicBernsteinSzegoTrig`, `Interp`, `Szego`
  (`szego_deriv_sq_bound`), `Trigonometric`, `Bernstein`, `Mesh` (Ehlich–Zeller: the sup norm on
  [−1, 1] is at most sec(πβ/(2k)) times the maximum over k + 1 Chebyshev–Lobatto nodes, for
  degree β < k), `PairingRearrangement`, `ChebyshevChordGeometry`,
  `HalfPlaneDerivativeComparison`, `DuffinSchaeffer` (`duffinSchaeffer_derivative_le`), `Markov`
  (`markov_derivative_unitInterval`, `markov_derivative_Icc`).
* Explicit approximants: `AbsoluteValue` (`absChebPoly_error_le`), `CosineProjection` (the rank-k
  cosine projection of a γ-Hölder function on [0, 1] has L² error at most 5·H·k^(−γ)).
* Jackson kernels and tensor approximation: `Kernel`, `Jackson`, `Tensor`, `TensorExtraction`
  (`tensorConvolution_approx_lipschitz`), `TrigExtraction`, `AffineFour`, `AffineFourBoundary`,
  `CoefficientEnvelopeFour`, `HeterogeneousTensor`, `HeterogeneousTensorExtraction`,
  `HeterogeneousTensorInterpolation`, `ParametricTensor`, `ParametricHeterogeneousTensor`.
* Interpolation grids and coefficient sizes: `LobattoLagrange`, `EquispacedDistance`,
  `EquispacedLagrange`, `TensorGridWeights`, `TensorChebyshev`, `PolynomialOneNorm`,
  `ChebyshevOneNorm`.

This file only gathers the modules above.
-/
