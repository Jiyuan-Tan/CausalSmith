module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.Audit

/-! Algebraic identities for the light-cell population weight.

This module isolates the exact decomposition used in equation (23) of the
writeup.  Later approximation bounds only need to control the two reciprocal
polynomial residuals appearing on the right-hand side.
-/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- The two arm masses of a cell add to its cell mass. -/
lemma armMass_false_add_true {n : ℕ} (P : Law n) (k : Fin n) :
    armMass P false k + armMass P true k = P.cellMass k := by
  simp [armMass]
  ring

/-- For a nonempty post-pilot block, the light-cell scale is strictly positive. -/
lemma lightScale_pos (n : ℕ) (rho : ℝ) (hn : 0 < n) :
    0 < lightScale n rho := by
  have hpost : 0 < postPilotSize n := by
    simp only [postPilotSize, pilotSize]
    omega
  have hblock : 0 < blockMean n := by
    simp only [blockMean]
    positivity
  have hdegree : 0 < degree n rho := by
    simp only [degree]
    omega
  simp only [lightScale]
  positivity

/-- Exact residual decomposition for the light-cell audit weight.

Writing each arm mass as `B * x_a`, the missing cell mass is the sum of the
two reciprocal-polynomial residuals `1 - x_a * GK K x_a`. -/
lemma cellMass_sub_lightAuditWeight {n : ℕ} (rho : ℝ)
    (P : Law n) (k : Fin n) (hn : 0 < n) :
    let B := lightScale n rho
    let x0 := armMass P false k / B
    let x1 := armMass P true k / B
    P.cellMass k - lightAuditWeight n rho P k =
      B * (x1 * (1 - x0 * GK (degree n rho) x0) +
        x0 * (1 - x1 * GK (degree n rho) x1)) := by
  dsimp only
  have hB : lightScale n rho ≠ 0 := (lightScale_pos n rho hn).ne'
  rw [← armMass_false_add_true P k]
  unfold lightAuditWeight
  dsimp only
  field_simp
  ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
