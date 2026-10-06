module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.GKRecurrence
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Upper.LightWeightIdentity

/-! Pointwise light-cell bias bound from the reciprocal-polynomial certificate. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

/-- Equation (23), including the zero-cell endpoint. -/
lemma lightAuditWeight_bias_bound {n : ℕ} (rho : ℝ) (P : Law n)
    (k : Fin n) (hn : 0 < n) (hoverlap : FixedOverlap P)
    (hlight : P.cellMass k ≤ lightScale n rho) :
    0 ≤ P.cellMass k - lightAuditWeight n rho P k ∧
      P.cellMass k - lightAuditWeight n rho P k ≤
        6 * lightScale n rho / (degree n rho : ℝ) ^ 2 := by
  let B := lightScale n rho
  let K := degree n rho
  let p := P.cellMass k
  let pi := P.propensity k
  let x0 := armMass P false k / B
  let x1 := armMass P true k / B
  have hB : 0 < B := lightScale_pos n rho hn
  have hK : 0 < K := by
    simp [K, degree]
  have hp0 : 0 ≤ p := (P.cellMass_range k).1
  by_cases hp : p = 0
  · have hcell : P.cellMass k = 0 := by simpa [p] using hp
    simp [lightAuditWeight, armMass, hcell]
    positivity
  have hp' : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
  obtain ⟨hpi0, hpi1⟩ := hoverlap k hp'
  have hpi0' : 0 < pi := by dsimp [pi]; linarith
  have hpi1' : pi < 1 := by dsimp [pi]; linarith
  have hx0 : 0 < x0 := by
    dsimp [x0, armMass, B, p, pi]
    positivity
  have hx1 : 0 < x1 := by
    dsimp [x1, armMass, B, p, pi]
    positivity
  have hx0le : x0 ≤ 1 := by
    apply (div_le_one hB).2
    dsimp [x0, armMass, B, p, pi] at *
    nlinarith
  have hx1le : x1 ≤ 1 := by
    apply (div_le_one hB).2
    dsimp [x1, armMass, B, p, pi] at *
    nlinarith
  have hr0 := (one_sub_mul_GK_bounds K hK x0 hx0 hx0le).2.2
  have hr1 := (one_sub_mul_GK_bounds K hK x1 hx1 hx1le).2.2
  have hr0nonneg := (one_sub_mul_GK_bounds K hK x0 hx0 hx0le).1
  have hr1nonneg := (one_sub_mul_GK_bounds K hK x1 hx1 hx1le).1
  have hratio10 : x1 ≤ 3 * x0 := by
    dsimp [x0, x1, armMass, B, p, pi] at *
    calc
      P.cellMass k * P.propensity k / lightScale n rho ≤
          (3 * (P.cellMass k * (1 - P.propensity k))) / lightScale n rho := by
        apply (div_le_div_iff_of_pos_right hB).2
        nlinarith
      _ = 3 * (P.cellMass k * (1 - P.propensity k) / lightScale n rho) := by ring
  have hratio01 : x0 ≤ 3 * x1 := by
    dsimp [x0, x1, armMass, B, p, pi] at *
    calc
      P.cellMass k * (1 - P.propensity k) / lightScale n rho ≤
          (3 * (P.cellMass k * P.propensity k)) / lightScale n rho := by
        apply (div_le_div_iff_of_pos_right hB).2
        nlinarith
      _ = 3 * (P.cellMass k * P.propensity k / lightScale n rho) := by ring
  rw [cellMass_sub_lightAuditWeight rho P k hn]
  constructor
  · positivity
  · have hKsq : 0 < (K : ℝ) ^ 2 := by positivity
    have hterm0 :
        x1 * (1 - x0 * GK K x0) ≤ 3 / (K : ℝ) ^ 2 := by
      calc
        _ ≤ x1 * (1 / ((K : ℝ) ^ 2 * x0)) := by gcongr
        _ = (x1 / x0) / (K : ℝ) ^ 2 := by field_simp
        _ ≤ _ := by
          apply (div_le_div_iff_of_pos_right hKsq).2
          exact (div_le_iff₀ hx0).2 hratio10
    have hterm1 :
        x0 * (1 - x1 * GK K x1) ≤ 3 / (K : ℝ) ^ 2 := by
      calc
        _ ≤ x0 * (1 / ((K : ℝ) ^ 2 * x1)) := by gcongr
        _ = (x0 / x1) / (K : ℝ) ^ 2 := by field_simp
        _ ≤ _ := by
          apply (div_le_div_iff_of_pos_right hKsq).2
          exact (div_le_iff₀ hx1).2 hratio01
    calc
      B * (x1 * (1 - x0 * GK K x0) + x0 * (1 - x1 * GK K x1)) ≤
          B * (3 / (K : ℝ) ^ 2 + 3 / (K : ℝ) ^ 2) := by gcongr
      _ = 6 * B / (K : ℝ) ^ 2 := by ring

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
