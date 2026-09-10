import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Certificate

/-! # Explicit covariance witnesses

The four-node profile-collision path and the two three-node witnesses marking
the boundaries of the design restrictions.
-/

open Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- First loading vector in the four-node collision. -/
def collisionA : Fin 4 → ℝ := ![1, 1, 2, 1]

/-- Second loading vector in the four-node collision. -/
def collisionB : Fin 4 → ℝ := ![0, 1, 1, 2]

/-- The legal profile-split parameter domain. -/
def CollisionParameter := {γ : ℝ // -1 < γ ∧ γ < 1}
  -- @realizes gamma(profile split parameter in (-1,1))

-- @node: def:four-node-collision-path
def fourNodeCollisionPath (γ : CollisionParameter) : CovarianceTuple 4 2 where
  cov e :=
    if e = 0 then 1
    else if e = 1 then
      1 + Matrix.vecMulVec collisionA collisionA + Matrix.vecMulVec collisionB collisionB
    else
      1 + 2 • Matrix.vecMulVec collisionA collisionA +
        (2 + γ.1) • Matrix.vecMulVec collisionB collisionB
  symmetric := by
    intro e
    simp only [Matrix.IsHermitian]
    ext i j
    split_ifs <;>
      simp [Matrix.conjTranspose_apply, Matrix.vecMulVec, Matrix.one_apply,
        mul_comm, add_comm, add_left_comm, add_assoc, eq_comm]
  -- @realizes thetagamma(explicit Sigma0, Delta1, Delta2(gamma) path)

/-- The collision parameter at the central profile. -/
def collisionZero : CollisionParameter := ⟨0, by norm_num⟩

/-- Shared raw data for the two three-node boundary examples. -/
structure RestrictionBoundaryData where
  B : RealMatrix 3
  C : RealMatrix 3
  omega0 : Fin 3 → ℝ
  OmegaEta : RealMatrix 3
  target : Finset (Fin 3)
  thetaSigned : CovarianceTuple 3 2
  thetaSplit : CovarianceTuple 3 2

/-- A diagonal covariance tuple from three diagonal vectors. -/
def diagonalTriple (z0 z1 z2 : Fin 3 → ℝ) : CovarianceTuple 3 2 where
  cov e := if e = 0 then Matrix.diagonal z0 else if e = 1 then Matrix.diagonal z1
    else Matrix.diagonal z2
  symmetric := by
    intro e
    simp only [Matrix.IsHermitian]
    ext i j
    split_ifs <;> by_cases hij : i = j <;>
      simp [Matrix.conjTranspose_apply, Matrix.diagonal, hij, eq_comm]

-- @node: def:restriction-boundary-witnesses
noncomputable def restrictionBoundaryWitnesses : RestrictionBoundaryData where
  B := 0 -- @realizes Bmu(boundary witness Bmu = 0)
  C := 0 -- @realizes Cmu(boundary witness Cmu = 0)
  omega0 := ![(3 : ℝ) / 2, (3 : ℝ) / 2, (3 : ℝ) / 2]
    -- @realizes omega0(boundary witness baseline variances 3/2)
  OmegaEta := (1 / 2 : ℝ) • (1 : RealMatrix 3)
    -- @realizes Omegaeta(boundary witness measurement covariance Id/2)
  target := {0, 1} -- @realizes Tmu(boundary witness target {1,2})
  thetaSigned := diagonalTriple ![2, 2, 2] ![3, 3, 2] ![(3 : ℝ) / 2, 2, 2]
    -- @realizes thetaSigned(signed-shift covariance tuple)
  thetaSplit := diagonalTriple ![2, 2, 2] ![3, 2, 2] ![2, 3, 2]
    -- @realizes thetaSplitRef(split-reference covariance tuple)

end CausalSmith.ExactID.CovshiftProfilequotientTargets
