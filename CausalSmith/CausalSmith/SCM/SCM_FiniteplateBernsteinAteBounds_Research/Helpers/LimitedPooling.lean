import CausalSmith.SCM.SCM_FiniteplateBernsteinAteBounds_Research.Helpers.MomentGeometry
import Mathlib.Topology.Order.Compact

/-! # Homogeneous limited-pooling comparator -/

namespace CausalSmith.SCM.FiniteplateBernsteinAteBounds

open scoped BigOperators

/-- The odd/even limited-pooling weight. -/
noncomputable def poolingWeight (m : ℕ) (r rstar : ℝ) : ℝ :=
  if Odd m then
    1 - (1 - r) * ((rstar - r) / rstar) ^ (m - 1)
  else
    1 - ((rstar - r) / rstar) ^ m
  -- @realizes w_m(odd/even scalar-reference weight)

/-- The limited-pooling lower envelope. -/
noncomputable def lowerLW (m : ℕ) (pstar : ℝ) (q : CellLaw) : ℝ :=
  q (true, true) * poolingWeight m (treatmentProb q) pstar / treatmentProb q - 1 -
    poolingWeight m (1 - treatmentProb q) (1 - pstar) *
      (q (false, true) - (1 - treatmentProb q)) / (1 - treatmentProb q)
  -- @realizes ell_LW(the scalar-reference lower polynomial)

/-- The limited-pooling upper envelope. -/
noncomputable def upperLW (m : ℕ) (pstar : ℝ) (q : CellLaw) : ℝ :=
  1 + poolingWeight m (treatmentProb q) pstar *
      (q (true, true) - treatmentProb q) / treatmentProb q -
    q (false, true) * poolingWeight m (1 - treatmentProb q) (1 - pstar) /
      (1 - treatmentProb q)
  -- @realizes u_LW(the scalar-reference upper polynomial)

lemma lowerLW_coefficients_exist (m : ℕ) (ε pstar : ℝ) :
    ∃ coeff : CountIndex m → ℝ, ∀ q ∈ overlapSimplex ε,
      lowerLW m pstar q = ∑ c, coeff c * bernsteinCoordinate m c q := by
  sorry

lemma upperLW_coefficients_exist (m : ℕ) (ε pstar : ℝ) :
    ∃ coeff : CountIndex m → ℝ, ∀ q ∈ overlapSimplex ε,
      upperLW m pstar q = ∑ c, coeff c * bernsteinCoordinate m c q := by
  sorry

/-- The unique degree-`m` Bernstein coefficient vector of the lower comparator. -/
noncomputable def lowerLWCoeff (m : ℕ) (ε pstar : ℝ) : CountIndex m → ℝ :=
  Classical.choose (lowerLW_coefficients_exist m ε pstar)

/-- The unique degree-`m` Bernstein coefficient vector of the upper comparator. -/
noncomputable def upperLWCoeff (m : ℕ) (ε pstar : ℝ) : CountIndex m → ℝ :=
  Classical.choose (upperLW_coefficients_exist m ε pstar)

/-- The scalar-reference limited-pooling interval. -/
noncomputable def limitedPoolingInterval (m : ℕ) (ε pstar : ℝ)
    (b : CountIndex m → ℝ) : Set ℝ :=
  Set.Icc (coefficientValue (lowerLWCoeff m ε pstar) b)
    (coefficientValue (upperLWCoeff m ε pstar) b)
  -- @realizes I_LW(interval from one reference propensity)
  -- @realizes p_star(reference propensity constrained by consumers to [epsilon,1-epsilon])

lemma limitedPoolingInterval_integral (m : ℕ) (ε pstar : ℝ)
    (b : CountIndex m → ℝ) (ν : MeasureTheory.Measure CellLaw)
    (hν : ν ∈ momentFiber m ε b) :
    limitedPoolingInterval m ε pstar b =
      Set.Icc (∫ q, lowerLW m pstar q ∂ν) (∫ q, upperLW m pstar q ∂ν) := by
  sorry

/-- Intersection of all scalar-reference limited-pooling intervals. -/
-- @node: def:limited-pooling-comparator
noncomputable def limitedPoolingIntersection (m : ℕ) (ε : ℝ)
    (b : CountIndex m → ℝ) : Set ℝ :=
  Set.Icc
    (sSup ((fun pstar => coefficientValue (lowerLWCoeff m ε pstar) b) ''
      Set.Icc ε (1 - ε)))
    (sInf ((fun pstar => coefficientValue (upperLWCoeff m ε pstar) b) ''
      Set.Icc ε (1 - ε)))
  -- @realizes I_LW_cap(max lower and min upper across all p_star)

end CausalSmith.SCM.FiniteplateBernsteinAteBounds
