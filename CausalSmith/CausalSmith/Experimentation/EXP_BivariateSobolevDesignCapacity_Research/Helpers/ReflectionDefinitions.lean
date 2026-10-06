module
public import CausalSmith.Experimentation.EXP_BivariateSobolevDesignCapacity_Research.Helpers.CitedGates

/-! # Even reflection and the exact pooled Fourier budget

Definitions fix the period-two folding map, reflected extension, frequency complexity,
and component and pooled Fourier budgets, independently of the budget proofs.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Experimentation.BivariateSobolevDesignCapacity
variable {d : ℕ}
-- @env: S4
variable {r : ℕ}
/-- Fold y=2u to the closed unit cube, using the half-open representative of u. -/
def fold (u : Torus r) : Cube r :=
  fun h => let v := ((AddCircle.equivIco (1 : ℝ) 0) (u h)).val
           min (2 * v) (2 - 2 * v)
  -- @realizes fold(min(y,2-y), y=2u)
/-- Even period-two extension. -/
def reflExt (m : Cube d → ℝ) (y : Torus d) : ℂ := (m (fold y) : ℂ)
  -- @realizes F(m composed with fold)
/-- Characters of the period-two torus. -/
def ek (k : Fin d → ℤ) (y : Torus d) : ℂ := UnitAddTorus.mFourier k y
  -- @realizes ek(exp(iπ k·y) using y=2u)
/-- Normalized Fourier coefficients of the reflected function. -/
def Fhat (m : Cube d → ℝ) (k : Fin d → ℤ) : ℂ :=
  ∫ y, ek (-k) y * reflExt m y ∂torusMeasure d
  -- @realizes Fhat(normalized Haar Fourier coefficient)
/-- Integer frequencies with their actual nonzero coordinate support. -/
def frequencySupport (k : Fin d → ℤ) : Finset (Fin d) :=
  Finset.univ.filter (fun j => k j ≠ 0) -- @realizes k(integer frequency and support)
/-- Squared Euclidean length of an integer frequency. -/
def frequencySq (k : Fin d → ℤ) : ℝ := ∑ j, (k j : ℝ) ^ 2
/-- Complexity of a nonzero frequency, with the harmless value zero at frequency zero. -/
def frequencyComplexity (k : Fin d → ℤ) : ℝ :=
  frequencySq k / (frequencySupport k).card -- @realizes t(||k||²/|supp k|)
/-- Squared weighted torus norm in a fixed component dimension. -/
def componentFourierBudget (p : ℕ) (s : ℝ) (g : Cube p → ℝ) : ℝ≥0∞ :=
  ∑' a : Fin p → ℤ, ENNReal.ofReal
    ((1 + Real.pi ^ 2 * frequencySq a / (p : ℝ)) ^ s * ‖Fhat g a‖ ^ 2)
/-- The Fourier budget restricted to support sizes one and two. -/
def reflectedBudget (s : ℝ) (m : Cube d → ℝ) : ℝ≥0∞ :=
  ∑' k : Fin d → ℤ, if 1 ≤ (frequencySupport k).card ∧ (frequencySupport k).card ≤ 2 then
    ENNReal.ofReal ((1 + Real.pi ^ 2 * frequencyComplexity k) ^ s * ‖Fhat m k‖ ^ 2)
    else 0

end CausalSmith.Experimentation.BivariateSobolevDesignCapacity
