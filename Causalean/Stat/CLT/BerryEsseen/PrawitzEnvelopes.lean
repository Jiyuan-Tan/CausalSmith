module
public import Causalean.Stat.CLT.BerryEsseen.PrawitzKernel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Deterministic envelopes for Prawitz smoothing

These explicit analytic functions separate numerical budget proofs from
probabilistic characteristic-function bounds. They contain no convergence
or coverage premises. The original envelope definitions are preserved exactly.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open MeasureTheory

/-- The cubic characteristic-function damping envelope is truncated by
one, the universal modulus bound for a probability characteristic function. -/
noncomputable def prawitzMomentEnvelope (ρ t : ℝ) : ℝ :=
  min 1 (Real.exp (-(t ^ 2 / 2) + ρ * |t| ^ 3 / 5))

/-- The iid Fourier discrepancy envelope combines the Taylor product
bound with the sum of the probability and Gaussian modulus envelopes. -/
noncomputable def prawitzDiscrepancyEnvelope (ρ t : ℝ) : ℝ :=
  min ((ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
      Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10))
    (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)))

/-- The four Prawitz smoothing terms evaluated on explicit cubic moment
envelopes form a deterministic upper bound to be certified analytically. -/
noncomputable def prawitzBerryEsseenEnvelope (ρ U0 U : ℝ) : ℝ :=
  (2 / U) * (∫ t in (0 : ℝ)..U0,
    ‖prawitzKernel (t / U)‖ * prawitzDiscrepancyEnvelope ρ t) +
  (2 / U) * (∫ t in U0..U,
    ‖prawitzKernel (t / U)‖ * prawitzMomentEnvelope ρ t) +
  2 * (∫ t in (0 : ℝ)..U0,
    ‖prawitzKernel (t / U) / (U : ℂ) -
      Complex.I / ((2 * Real.pi * t : ℝ) : ℂ)‖ *
      Real.exp (-(t ^ 2 / 2))) +
  (1 / Real.pi) * (∫ t in Set.Ioi U0,
    Real.exp (-(t ^ 2 / 2)) / t)

end Causalean.Stat.CLT.BerryEsseen
