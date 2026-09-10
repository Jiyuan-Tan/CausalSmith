import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Basic.Cycles
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Causalean.Mathlib.LinearAlgebra.MonomialMatrix

/-!
# Population BACKSHIFT covariance world

The population matrix system, admissible structural matrices, named assumptions, and the
replacement-compatibility recovery map.
-/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix

/-- A real square matrix indexed by the `p` variables. -/
abbrev RealMatrix (p : ℕ) := Matrix (Fin p) (Fin p) ℝ

/-- Environment labels are the finite type with exactly `m` slots.

@realizes E(labels Fin m)
-/
abbrev Environment (m : ℕ) := Fin m

/-- A covariance family whose every environment slot is positive semidefinite.

@realizes Sigma(family in (PSDp)^E)
-/
abbrev PSDCovarianceFamily (p m : ℕ) :=
  {covarianceFamily : Environment m → RealMatrix p //
    ∀ e, (covarianceFamily e).PosSemidef}

/-- The number of honest slots after deleting at most `c` replacements.

@realizes h(h = m - c)
-/
def honestCount (m c : ℕ) : ℕ := m - c

/-- A population multi-environment BACKSHIFT covariance system. -/
structure BackshiftSystem (p m c : ℕ) where
  dimension_at_least_two : 2 ≤ p -- @realizes p(integer p ≥ 2)
  environment_nonempty : 1 ≤ m -- @realizes m(integer m ≥ 1)
  corruption_lt : c < m -- @realizes c(integer 0 ≤ c < m)
  honest : Finset (Environment m) -- @realizes H(subset of E)
  honest_card : honest.card = honestCount m c -- @realizes H(cardinality h)
  covariance : Environment m → RealMatrix p -- @realizes Sigma(carrier E → real p×p matrices)
  covariance_psd : ∀ e, (covariance e).PosSemidef -- @realizes Sigma(range in PSDp)
  structural : RealMatrix p -- @realizes D(carrier real p×p matrix)
  structural_invertible : IsUnit structural.det -- @realizes D(invertible)
  invariantNoise : RealMatrix p -- @realizes Omega(carrier symmetric real p×p matrix)
  invariantNoise_symmetric : invariantNoise.transpose = invariantNoise -- @realizes Omega(symmetric)
  shifts : Environment m → Fin p → ℝ -- @realizes s(carrier H×p → ℝ; range via NonnegativeShifts)

-- @env: S1
variable {p m c : ℕ} (W : BackshiftSystem p m c)

-- @node: def:admissible-matrices
/-- Invertible unit-diagonal matrices satisfying the strict BACKSHIFT cycle-product bound.

@realizes Dcal(invertible, unit diagonal, CP(I-A)<1)
-/
def admissibleSet (p : ℕ) : Set (RealMatrix p) :=
  {A | IsUnit A.det ∧ (∀ i, A i i = 1) ∧ cycleProduct (1 - A) < 1}

-- @node: ass:backshift-normalization
/-- The structural matrix belongs to the BACKSHIFT normalized parameter space. -/
def BackshiftNormalization : Prop := W.structural ∈ admissibleSet p

-- @node: ass:nonnegative-shifts
/-- Honest intervention-variance shifts are coordinatewise nonnegative. -/
def NonnegativeShifts : Prop :=
  ∀ e ∈ W.honest, ∀ k, 0 ≤ W.shifts e k

-- @node: ass:honest-covariance-model
/-- Honest covariances obey the population BACKSHIFT equilibrium equation. -/
def HonestCovarianceModel : Prop :=
  ∀ e ∈ W.honest,
    W.covariance e = W.structural⁻¹ *
      (W.invariantNoise + Matrix.diagonal (W.shifts e)) * W.structural⁻¹.transpose

-- @node: def:compatible-set
/-- Structural matrices compatible with at least `m-c` slots of a covariance family.

@realizes Rc(c-replacement compatibility set)
-/
def compatibleSet (p m c : ℕ)
    (covarianceFamily : PSDCovarianceFamily p m) : Set (RealMatrix p) :=
  {A | A ∈ admissibleSet p ∧
    ∃ K : Finset (Environment m), honestCount m c ≤ K.card ∧
      ∃ Ψ : RealMatrix p, Ψ.PosSemidef ∧
        ∃ t : Environment m → Fin p → ℝ,
          (∀ e ∈ K, ∀ j, 0 ≤ t e j) ∧
          ∀ e ∈ K,
            covarianceFamily.1 e = A⁻¹ * (Ψ + Matrix.diagonal (t e)) * A⁻¹.transpose}

/-- Compatibility can equivalently be read after congruence-transforming each fitted covariance. [This is the asserted conclusion](goal). -/
lemma compatibleSet_transformed_iff (A : RealMatrix p)
    (covarianceFamily : PSDCovarianceFamily p m) :
    A ∈ compatibleSet p m c covarianceFamily ↔
      A ∈ admissibleSet p ∧
      ∃ K : Finset (Environment m), honestCount m c ≤ K.card ∧
        ∃ Ψ : RealMatrix p, Ψ.PosSemidef ∧
          ∃ t : Environment m → Fin p → ℝ,
            (∀ e ∈ K, ∀ j, 0 ≤ t e j) ∧
            ∀ e ∈ K, A * covarianceFamily.1 e * A.transpose = Ψ + Matrix.diagonal (t e) := by
  change (A ∈ admissibleSet p ∧
      ∃ K : Finset (Environment m), honestCount m c ≤ K.card ∧
        ∃ Ψ : RealMatrix p, Ψ.PosSemidef ∧
          ∃ t : Environment m → Fin p → ℝ,
            (∀ e ∈ K, ∀ j, 0 ≤ t e j) ∧
            ∀ e ∈ K, covarianceFamily.1 e =
              A⁻¹ * (Ψ + Matrix.diagonal (t e)) * A⁻¹.transpose) ↔ _
  constructor
  · rintro ⟨hA, K, hK, Ψ, hΨ, t, ht, heq⟩
    refine ⟨hA, K, hK, Ψ, hΨ, t, ht, ?_⟩
    intro e he
    let X := Ψ + Matrix.diagonal (t e)
    have hleft : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA.1
    have hright : A⁻¹.transpose * A.transpose = 1 := by
      rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
    rw [heq e he]
    change A * (A⁻¹ * X * A⁻¹.transpose) * A.transpose = X
    calc
      _ = (A * A⁻¹) * X * (A⁻¹.transpose * A.transpose) := by noncomm_ring
      _ = X := by rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨hA, K, hK, Ψ, hΨ, t, ht, heq⟩
    refine ⟨hA, K, hK, Ψ, hΨ, t, ht, ?_⟩
    intro e he
    let X := covarianceFamily.1 e
    have hleft : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA.1
    have hright : A.transpose * A⁻¹.transpose = 1 := by
      rw [← Matrix.transpose_mul, hleft, Matrix.transpose_one]
    rw [← heq e he]
    change X = A⁻¹ * (A * X * A.transpose) * A⁻¹.transpose
    calc
      _ = (A⁻¹ * A) * X * (A.transpose * A⁻¹.transpose) := by
        rw [hleft, hright, Matrix.one_mul, Matrix.mul_one]
      _ = A⁻¹ * (A * X * A.transpose) * A⁻¹.transpose := by noncomm_ring

end CausalSmith.ExactID.RobustBackshiftUniformDistance
