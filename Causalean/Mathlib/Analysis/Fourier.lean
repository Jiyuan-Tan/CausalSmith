module
public import Causalean.Mathlib.Analysis.Fourier.AngularFourier
public import Causalean.Mathlib.Analysis.Fourier.AngularFourierSobolev
public import Causalean.Mathlib.Analysis.Fourier.AngularFourierWeakDerivative
public import Causalean.Mathlib.Analysis.Fourier.Basic
public import Causalean.Mathlib.Analysis.Fourier.Estimate
public import Causalean.Mathlib.Analysis.Fourier.FourierEndpoints
public import Causalean.Mathlib.Analysis.Fourier.Interpolation
public import Causalean.Mathlib.Analysis.Fourier.MultiplierBounds
public import Causalean.Mathlib.Analysis.Fourier.WeightedSpecialization

/-!
# Fourier energy estimates on the real line and on Euclidean space

Two groups of results. On the real line, for a function g with ∫|g|² and ∫v²|g|² finite, the
weighted energy ∫|v|^κ·|g(v)|² dv with 0 ≤ κ ≤ 2 is at most (∫|g|²)^(1−κ/2)·(∫v²|g|²)^(κ/2); when
g is the inverse Fourier transform of a compactly supported C¹ multiplier G, Plancherel turns
this into a bound by ∫|G|² and (2π)⁻²·∫|G′|², conditional on integrability of the inverse
transforms of G and G′. On finite-dimensional Euclidean space, the unitary angular-frequency
Fourier transform satisfies Plancherel, and for a compactly supported function with weak
derivatives in L² the energy weighted by 1 + |w|²/p equals ∫|G|² plus (1/p)·Σ_r ∫|∂_r G|².

## Contents

* `Fourier.Basic` — the energies `energy` and `weightedEnergy`.
* `Fourier.Interpolation` — `weightedEnergy_le_interpolation` and a scale-dependent additive form.
* `Fourier.FourierEndpoints` — Plancherel and the quadratic-moment identity for the inverse
  transform of a compact C¹ multiplier (`inverse_energy_endpoints`).
* `Fourier.Estimate` — `inverse_weightedEnergy_le`, the interpolation bound in frequency terms.
* `Fourier.MultiplierBounds`, `Fourier.WeightedSpecialization` — L² bounds for a band-limited
  profile divided by a Gaussian characteristic function (`inverseGaussian_weightedEnergy_le`),
  with the factor exp(36·(σ/h)²) explicit.
* `Fourier.AngularFourier` — the transform `angularFourier` on ℝ^p and its Plancherel identity.
* `Fourier.AngularFourierWeakDerivative` — weak coordinate derivatives become multiplication by
  the frequency coordinate.
* `Fourier.AngularFourierSobolev` — the first-order energy identity `angular_first_energy` and
  the resulting bounds `energy_bounds_of_real_slices`.

This file only gathers the modules above.
-/
