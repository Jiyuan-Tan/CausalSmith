import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentReduction
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Intrinsic

/-! # Sharp primal and Bernstein-dual characterization -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory

/-- The convex hull of the joint moment/target map. -/
noncomputable def augmentedMomentBody (m : ℕ) (ε : ℝ) :
    Set ((CountIndex m → ℝ) × ℝ) :=
  convexHull ℝ ((fun q => (momentMap m q, causalIntegrand q)) '' overlapSimplex ε)

/-- A measure is concentrated on at most `k` latent laws. -/
def SupportedOnAtMost (ν : Measure CellLaw) (k : ℕ) : Prop :=
  ∃ atoms : Finset CellLaw, atoms.card ≤ k ∧ ν (atoms : Set CellLaw)ᶜ = 0

/-- Complete sharpness, attainment, finite support, and relative-interior duality specification. -/
def SharpPrimalDualSpec (m : ℕ) (ε : ℝ) : Prop :=
  IsCompact (augmentedMomentBody m ε) ∧
  augmentedMomentBody m ε =
    {pair | ∃ ν, IsMixingLaw ε ν ∧
      pair.1 = (fun c => ∫ q, bernsteinCoordinate m c q ∂ν) ∧
      pair.2 = ateFunctional ν} ∧
  (∀ pair ∈ augmentedMomentBody m ε, ∃ ν, IsMixingLaw ε ν ∧
    SupportedOnAtMost ν (countIndexCard m + 1) ∧
    pair.1 = (fun c => ∫ q, bernsteinCoordinate m c q ∂ν) ∧
    pair.2 = ateFunctional ν ∧ MomentReductionConverse m 1 ε ν) ∧
  (∀ b ∈ bernsteinMomentBody m ε,
    sharpAteFiber m ε b = Set.Icc (lowerEndpoint m ε b) (upperEndpoint m ε b) ∧
    ∃ νL ∈ momentFiber m ε b, ∃ νU ∈ momentFiber m ε b,
      ateFunctional νL = lowerEndpoint m ε b ∧
      ateFunctional νU = upperEndpoint m ε b ∧
      SupportedOnAtMost νL (countIndexCard m) ∧
      SupportedOnAtMost νU (countIndexCard m) ∧
      MomentReductionConverse m 1 ε νL ∧ MomentReductionConverse m 1 ε νU) ∧
  (∀ b ∈ intrinsicInterior ℝ (bernsteinMomentBody m ε),
    bernsteinDual m ε b = (lowerEndpoint m ε b, upperEndpoint m ε b) ∧
    (∃ lowerCoeff, IsMinorant m ε lowerCoeff ∧
      coefficientValue lowerCoeff b = lowerEndpoint m ε b) ∧
    (∃ upperCoeff, IsMajorant m ε upperCoeff ∧
      coefficientValue upperCoeff b = upperEndpoint m ε b)) ∧
  (∀ b coeff r,
    b ∈ bernsteinMomentBody m ε →
    IsMinorant m ε coeff → coefficientValue coeff b = lowerEndpoint m ε b →
    Module.finrank ℝ (affineSpan ℝ
      (momentMap m '' {q ∈ overlapSimplex ε |
        (∑ c, coeff c * bernsteinCoordinate m c q) = causalIntegrand q})).direction = r →
    ∃ ν ∈ momentFiber m ε b,
      ateFunctional ν = lowerEndpoint m ε b ∧ SupportedOnAtMost ν (r + 1)) ∧
  (∀ b coeff r,
    b ∈ bernsteinMomentBody m ε →
    IsMajorant m ε coeff → coefficientValue coeff b = upperEndpoint m ε b →
    Module.finrank ℝ (affineSpan ℝ
      (momentMap m '' {q ∈ overlapSimplex ε |
        (∑ c, coeff c * bernsteinCoordinate m c q) = causalIntegrand q})).direction = r →
    ∃ ν ∈ momentFiber m ε b,
      ateFunctional ν = upperEndpoint m ε b ∧ SupportedOnAtMost ν (r + 1))

/-- The joint moment body is compact and equals the probability-measure image;
sharp endpoint measures have the stated Carathéodory support bounds, and the
Bernstein dual is attained on relative-interior fibers. -/
-- @node: thm:sharp-primal-dual
theorem sharp_primal_dual (m : ℕ) (ε : ℝ) :
    (1 ≤ m ∧ 0 < ε ∧ ε < (1 / 2 : ℝ)) → SharpPrimalDualSpec m ε := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
