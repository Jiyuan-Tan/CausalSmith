module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DongInference
public import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Classical polynomial fact interfaces

The cited Legendre and Hermite propositions are kept verbatim in this neutral
interface module so their proofs can be imported without a cycle through the
remaining cited-source declarations.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- NIST DLMF (2026 access), cite:nistdlmf-legendre, Tables 18.3.1 and 18.6.1,
equation 18.14.1 at zero Jacobi parameters; https://dlmf.nist.gov/18.3.
Orthogonality, reflection symmetry, unit bound, and the normalized left endpoint. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def ClassicalLegendreFacts : Sort 0 :=
  ∀ j k : ℕ,
    ((∫ t in (-1 : ℝ)..1, legendreP j t * legendreP k t) =
      if j = k then 2 / (2 * (j : ℝ) + 1) else 0) ∧
    (∀ t : ℝ, legendreP j (-t) = (-1 : ℝ)^j * legendreP j t) ∧
    (∀ t ∈ Icc (-1 : ℝ) 1, |legendreP j t| ≤ 1) ∧ legendreP j (-1) = (-1 : ℝ)^j

/-- NIST DLMF (2026 access), cite:nistdlmf-hermite, equation 18.12.16 and Table 18.3.1,
probabilists' Hermite row; https://dlmf.nist.gov/18.12.E16.
The generating series and Gaussian-normalized orthogonality. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def ClassicalHermiteFacts : Sort 0 :=
  (∀ z t : ℝ, HasSum (fun j : ℕ =>
    (Polynomial.aeval z (Polynomial.hermite j) : ℝ) * t^j / (Nat.factorial j : ℝ))
      (Real.exp (z*t - t^2/2))) ∧
  (∀ j k : ℕ, (∫ z, (Polynomial.aeval z (Polynomial.hermite j) : ℝ) *
      Polynomial.aeval z (Polynomial.hermite k) ∂gaussianReal 0 1) =
      if j = k then (Nat.factorial j : ℝ) else 0) ∧ Polynomial.hermite 0 = 1

end CausalSmith.Stat.RdTruesideNoiseFrontier
