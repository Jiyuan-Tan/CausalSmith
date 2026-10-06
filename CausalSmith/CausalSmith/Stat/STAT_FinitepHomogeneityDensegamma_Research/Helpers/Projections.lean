module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Prod

/-! Finite-moment homogeneity testing: Helpers/Projections. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


-- @env: S4
variable (J : ℕ) -- @realizes J(rank natural number; J>0 in geometry lemmas)
/-- Histogram features and score coefficients live in finite-dimensional Euclidean space. This statement assumes [the J parameter](hyp:J). [This is the stated defined object](goal). -/
abbrev Vec (J : ℕ) := EuclideanSpace ℝ (Fin J)
/-- The bundled carrier supplies its declared mathematical structure. This statement assumes [the J parameter](hyp:J). [This is the stated defined object](goal). -/
instance (J : ℕ) : MeasurableSpace (Vec J) := borel (Vec J)
/-- The bundled carrier supplies its declared mathematical structure. This statement assumes [the J parameter](hyp:J). [This is the stated defined object](goal). -/
instance (J : ℕ) : BorelSpace (Vec J) := ⟨rfl⟩
/-- Histogram cells are left closed and right open, with the last cell containing one. This statement assumes [the J parameter](hyp:J), [the j parameter](hyp:j). [This is the stated defined object](goal). -/
def cell (j : Fin J) : Set unitInterval := {x | (j:ℝ)/J ≤ (x:ℝ) ∧ ((x:ℝ) < ((j:ℝ)+1)/J ∨ (j.val+1=J ∧ (x:ℝ) ≤ 1))}
/-- The feature vector has square-root-rank indicators of the exact histogram cells. This statement assumes [the J parameter](hyp:J), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def featureMap (x : unitInterval) : Vec J := WithLp.toLp 2 (fun j => if x ∈ cell J j then Real.sqrt J else 0) -- @realizes F(histogram feature vector)
/-- [Exact uniform-design histogram tools](goal). \(I_{j,J}=[(j-1)/J,j/J)\) for \(j<J\), with \(I_{J,J}=[(J-1)/J,1]\); \(F_J(x)=(\sqrt J\,\mathbf1_{I_{j,J}}(x))_{j=1}^J\), \(\Pi_J(x,z)=\langle F_J(x),F_J(z)\rangle\), and \((\Pi_J f)(x)=\int_0^1\Pi_J(x,z)f(z)\,dz\). This statement assumes [the J parameter](hyp:J), [the x parameter](hyp:x), [the z parameter](hyp:z). -/
-- @node: def:projection
def projKernel (x z : unitInterval) : ℝ := inner ℝ (featureMap J x) (featureMap J z) -- @realizes Pi(exact histogram kernel)
/-- Histogram projection integrates its exact kernel against the input function. This statement assumes [the J parameter](hyp:J), [the f parameter](hyp:f), [the x parameter](hyp:x). [This is the stated defined object](goal). -/
def projOp (f : unitInterval → ℝ) (x : unitInterval) : ℝ := ∫ z, projKernel J x z*f z ∂design
/-- A dyadic increment subtracts the coarse kernel from the doubled-rank kernel. This statement assumes [the J parameter](hyp:J), [the x parameter](hyp:x), [the z parameter](hyp:z). [This is the stated defined object](goal). -/
def diffKernel (J : ℕ) (x z : unitInterval) : ℝ := projKernel (2*J) x z-projKernel J x z

end CausalSmith.Stat.FinitepHomogeneityDensegamma
