import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Multivariate Bernstein coordinates -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open scoped BigOperators

/-- The natural-number count in a cell. -/
def cellCount {m : ℕ} (c : CountIndex m) (x : Cell) : ℕ := (c.1 x).val

/-- A degree-`m` four-cell Bernstein coordinate. -/
noncomputable def bernsteinCoordinate (m : ℕ) (c : CountIndex m) (q : CellLaw) : ℝ :=
  (m.factorial : ℝ) / (∏ x, ((cellCount c x).factorial : ℝ)) *
    ∏ x, q x ^ cellCount c x
  -- @realizes B_c(multinomial Bernstein coordinate)

/-- The vector of all degree-`m` Bernstein coordinates. -/
noncomputable def momentMap (m : ℕ) (q : CellLaw) : CountIndex m → ℝ :=
  fun c => bernsteinCoordinate m c q
  -- @realizes g_m(q mapped to all Bernstein coordinates)

/-- The degree-`m` Bernstein span, as functions on the ambient four-cell space. -/
noncomputable def bernsteinSpan (m : ℕ) : Submodule ℝ (CellLaw → ℝ) :=
  Submodule.span ℝ (Set.range fun c : CountIndex m => bernsteinCoordinate m c)
  -- @realizes V_m(span of degree-m Bernstein coordinates)

/-- Restrictions to the overlap simplex of multivariate polynomials of total degree at most `m`. -/
def polynomialRestrictions (m : ℕ) (ε : ℝ) : Set (CellLaw → ℝ) :=
  {h | ∃ P : MvPolynomial Cell ℝ,
    P.totalDegree ≤ (m : WithBot ℕ) ∧
      ∀ q ∈ overlapSimplex ε, h q = MvPolynomial.eval q P}

/-- Ambient representatives whose restrictions to the overlap simplex lie in the
degree-`m` Bernstein span.  Off the overlap simplex no equality is required. -/
noncomputable def bernsteinRestrictions (m : ℕ) (ε : ℝ) : Set (CellLaw → ℝ) :=
  {h | ∃ v ∈ bernsteinSpan m, Set.EqOn h v (overlapSimplex ε)}

-- @env: S2
variable (m : ℕ) (ε : ℝ)

/-- Bernstein functions are exactly degree-at-most-`m` polynomial restrictions,
while the reciprocal causal contrast is not one of them at finite positive plate size. -/
-- @node: lem:finite-plate-nonpolynomial
lemma finite_plate_nonpolynomial
    (hm : 1 ≤ m) (hε0 : 0 < ε) (hεhalf : ε < (1 / 2 : ℝ)) :
    bernsteinRestrictions m ε = polynomialRestrictions m ε ∧
      causalIntegrand ∉ bernsteinRestrictions m ε := by
  sorry

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
