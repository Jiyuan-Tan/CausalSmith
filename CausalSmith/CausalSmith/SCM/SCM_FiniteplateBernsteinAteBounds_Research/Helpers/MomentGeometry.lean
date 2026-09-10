import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.BernsteinSpan
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Causalean.PO.ID.Partial.Basic

/-! # Bernstein moment geometry and sharp fibers -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open MeasureTheory
open scoped BigOperators

/-- Probability measures on the overlap simplex matching a Bernstein moment vector. -/
def momentFiber (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : Set (Measure CellLaw) :=
  {ν | IsProbabilityMeasure ν ∧ ν (overlapSimplex ε)ᶜ = 0 ∧
    ∀ c, ∫ q, bernsteinCoordinate m c q ∂ν = b c}
  -- @realizes F_m_epsilon(probability measures with Bernstein moments b)
  -- @realizes b(moment constraints b_c=integral B_c dnu)

/-- The compact-convex Bernstein moment body, in its convex-hull presentation. -/
-- @node: def:bernstein-moment-body
noncomputable def bernsteinMomentBody (m : ℕ) (ε : ℝ) : Set (CountIndex m → ℝ) :=
  convexHull ℝ (momentMap m '' overlapSimplex ε)
  -- @realizes B_m_epsilon(convex hull of g_m(K_epsilon))

/-- The attainable ATE values above one observable moment vector. This directly
reuses `Causalean.PartialID.IdentifiedInterval`. -/
-- @node: def:sharp-ate-fiber
noncomputable def sharpAteFiber (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : Set ℝ :=
  Causalean.PartialID.IdentifiedInterval ateFunctional
    (fun ν => ν ∈ momentFiber m ε b)
  -- @realizes Theta_m_epsilon(attainable ATE range over the moment fiber)

/-- Lower sharp endpoint. -/
noncomputable def lowerEndpoint (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : ℝ :=
  sInf (sharpAteFiber m ε b) -- @realizes L_m(infimum over the fiber)

/-- Upper sharp endpoint. -/
noncomputable def upperEndpoint (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : ℝ :=
  sSup (sharpAteFiber m ε b) -- @realizes U_m(supremum over the fiber)

/-- The sharp interval presented by its endpoints. -/
noncomputable def sharpInterval (m : ℕ) (ε : ℝ) (b : CountIndex m → ℝ) : Set ℝ :=
  Set.Icc (lowerEndpoint m ε b) (upperEndpoint m ε b)

/-- Finite Bernstein dot product. -/
noncomputable def coefficientValue {m : ℕ}
    (coeff b : CountIndex m → ℝ) : ℝ :=
  ∑ c, coeff c * b c

/-- Coefficients defining a global Bernstein minorant. -/
def IsMinorant (m : ℕ) (ε : ℝ) (coeff : CountIndex m → ℝ) : Prop :=
  ∀ q ∈ overlapSimplex ε,
    (∑ c, coeff c * bernsteinCoordinate m c q) ≤ causalIntegrand q

/-- Coefficients defining a global Bernstein majorant. -/
def IsMajorant (m : ℕ) (ε : ℝ) (coeff : CountIndex m → ℝ) : Prop :=
  ∀ q ∈ overlapSimplex ε,
    causalIntegrand q ≤ ∑ c, coeff c * bernsteinCoordinate m c q

/-- The lower-minorant and upper-majorant Bernstein dual values. -/
-- @node: def:bernstein-dual
noncomputable def bernsteinDual (m : ℕ) (ε : ℝ)
    (b : CountIndex m → ℝ) : ℝ × ℝ :=
  (sSup {x | ∃ coeff, IsMinorant m ε coeff ∧ coefficientValue coeff b = x},
   sInf {x | ∃ coeff, IsMajorant m ε coeff ∧ coefficientValue coeff b = x})
  -- @realizes D_m(sup minorant and inf majorant values)

/-- Valid pairs of lower and upper count-measurable Bernstein envelopes. -/
-- @node: def:valid-envelope-class
def validEnvelopeClass (m : ℕ) (ε : ℝ) :
    Set ((CountIndex m → ℝ) × (CountIndex m → ℝ)) :=
  {pair | IsMinorant m ε pair.1 ∧ IsMajorant m ε pair.2}
  -- @realizes E_m(valid lower/upper Bernstein envelope pairs)
  -- @realizes ell(lower Bernstein coefficient vector)
  -- @realizes u(upper Bernstein coefficient vector)

/-- Uniform error of an ambient function on the overlap simplex. -/
noncomputable def overlapUniformError (ε : ℝ)
    (h k : CellLaw → ℝ) : ℝ :=
  sSup ((fun q => |h q - k q|) '' overlapSimplex ε)

/-- The infimum uniform approximation error of the causal integrand by the
degree-`m` Bernstein span. -/
-- @node: def:uniform-identification-modulus
noncomputable def uniformIdentificationModulus (m : ℕ) (ε : ℝ) : ℝ :=
  sInf {r | ∃ v ∈ bernsteinSpan m,
    overlapUniformError ε causalIntegrand v = r}
  -- @realizes d_m(infimum sup-norm error over V_m)

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
