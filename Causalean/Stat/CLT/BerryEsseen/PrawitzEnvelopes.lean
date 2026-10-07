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

/-- The cubic moment envelope at ratio ρ and frequency t is
min(1, exp(−t²/2 + ρ|t|³/5)): a cubically damped Gaussian factor truncated at
one, the universal modulus bound for a probability characteristic function. -/
noncomputable def prawitzMomentEnvelope (ρ t : ℝ) : ℝ :=
  min 1 (Real.exp (-(t ^ 2 / 2) + ρ * |t| ^ 3 / 5))

/-- The Fourier discrepancy envelope at ratio ρ and frequency t is the smaller
of two quantities: the Taylor product bound
(ρ|t|³/6 + ρ²t⁴/8)·exp(−t²/4 + ρ|t|³/10), and the modulus sum, namely the
cubic moment envelope min(1, exp(−t²/2 + ρ|t|³/5)) plus the Gaussian modulus
exp(−t²/2). -/
noncomputable def prawitzDiscrepancyEnvelope (ρ t : ℝ) : ℝ :=
  min ((ρ * |t| ^ 3 / 6 + ρ ^ 2 * t ^ 4 / 8) *
      Real.exp (-(t ^ 2 / 4) + ρ * |t| ^ 3 / 10))
    (prawitzMomentEnvelope ρ t + Real.exp (-(t ^ 2 / 2)))

/-- The deterministic Prawitz smoothing envelope at ratio ρ, inner cutoff U0
and outer cutoff U is the sum of four explicit terms, with K the Prawitz
filter: (2/U)·∫ over [0, U0] of |K(t/U)| times the discrepancy envelope at
(ρ, t); (2/U)·∫ over [U0, U] of |K(t/U)| times the cubic moment envelope at
(ρ, t); 2·∫ over [0, U0] of |K(t/U)/U − i/(2πt)|·exp(−t²/2); and
(1/π)·∫ over t > U0 of exp(−t²/2)/t. It is a function of three real numbers
only; no probability law enters. The expression is the intended envelope for
0 < U0 ≤ U; outside that range (for instance U = 0, where it divides by zero)
it is only a formal value. -/
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
