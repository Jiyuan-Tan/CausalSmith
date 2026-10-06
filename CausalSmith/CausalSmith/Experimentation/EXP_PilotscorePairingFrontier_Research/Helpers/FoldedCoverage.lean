module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedPerturbedPushforward

/-! # Endpoint discrepancy for translated branch images -/

@[expose] public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open scoped BigOperators

/-- Integer translates whose `h`-grid interval `[k h + L, k h + U]` covers `y`. -/
@[no_expose]
noncomputable def gridIntervalIndices (h L U y : ℝ) : Finset ℤ :=
  Finset.Icc (Int.ceil ((y - U) / h)) (Int.floor ((y - L) / h))

private lemma int_Icc_card_real_error (low high : ℝ) (hlh : low ≤ high) :
    |((Finset.Icc (Int.ceil low) (Int.floor high)).card : ℝ) - (high - low)| ≤ 1 := by
  let A := Int.ceil low
  let B := Int.floor high
  have hAlow : low ≤ (A : ℝ) := Int.le_ceil low
  have hAup : (A : ℝ) < low + 1 := Int.ceil_lt_add_one low
  have hBup : (B : ℝ) ≤ high := Int.floor_le high
  have hBlow : high < (B : ℝ) + 1 := Int.lt_floor_add_one high
  by_cases hAB : A ≤ B
  · have hdiff : 0 ≤ B + 1 - A := by omega
    have hcard : ((Finset.Icc A B).card : ℝ) = ((B + 1 - A : ℤ) : ℝ) := by
      rw [Int.card_Icc]
      exact_mod_cast Int.toNat_of_nonneg hdiff
    change |((Finset.Icc A B).card : ℝ) - (high - low)| ≤ 1
    rw [hcard, abs_le]
    constructor <;> push_cast <;> linarith
  · have hBA : B < A := lt_of_not_ge hAB
    have hcard0 : (Finset.Icc A B).card = 0 := by
      rw [Int.card_Icc, Int.toNat_eq_zero]
      omega
    have hsucc : B + 1 ≤ A := by omega
    have hsuccR : (B : ℝ) + 1 ≤ A := by exact_mod_cast hsucc
    change |((Finset.Icc A B).card : ℝ) - (high - low)| ≤ 1
    rw [hcard0]
    norm_num [abs_of_nonpos (sub_nonpos.mpr hlh)]
    linarith

lemma gridIntervalIndices_card_error {h L U y : ℝ}
    (hh : 0 < h) (hLU : L ≤ U) :
    |((gridIntervalIndices h L U y).card : ℝ) - (U - L) / h| ≤ 1 := by
  have horder : (y - U) / h ≤ (y - L) / h := by
    exact (div_le_div_iff_of_pos_right hh).2 (by linarith)
  have hbound := int_Icc_card_real_error ((y - U) / h) ((y - L) / h) horder
  have heq : (y - L) / h - (y - U) / h = (U - L) / h := by
    field_simp [hh.ne']
    ring
  simpa [gridIntervalIndices, heq] using hbound

lemma mem_gridIntervalIndices_iff {h L U y : ℝ} (hh : 0 < h) (k : ℤ) :
    k ∈ gridIntervalIndices h L U y ↔
      y ∈ Set.Icc ((k : ℝ) * h + L) ((k : ℝ) * h + U) := by
  simp only [gridIntervalIndices, Finset.mem_Icc, Set.mem_Icc]
  constructor
  · intro hk
    have hlo : (y - U) / h ≤ (k : ℝ) := (Int.ceil_le.mp hk.1)
    have hhi : (k : ℝ) ≤ (y - L) / h := (Int.le_floor.mp hk.2)
    constructor
    · have := (le_div_iff₀ hh).mp hhi
      linarith
    · have := (div_le_iff₀ hh).mp hlo
      linarith
  · intro hk
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff₀ hh).2
      linarith [hk.2]
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hh).2
      linarith [hk.1]

lemma weighted_gridIntervalIndices_error {h L U s r y : ℝ}
    (hh : 0 < h) (hs : 0 < s) (hr : 0 ≤ r)
    (hlen : U - L = s * r) :
    |h / s * ((gridIntervalIndices h L U y).card : ℝ) - r| ≤ h / s := by
  have hLU : L ≤ U := by nlinarith
  have hcount := gridIntervalIndices_card_error (y := y) hh hLU
  have hid : h / s * ((gridIntervalIndices h L U y).card : ℝ) - r =
      (h / s) * (((gridIntervalIndices h L U y).card : ℝ) - (U - L) / h) := by
    rw [hlen]
    field_simp [hh.ne', hs.ne']
  rw [hid, abs_mul, abs_of_pos (div_pos hh hs)]
  simpa using mul_le_mul_of_nonneg_left hcount (div_nonneg hh.le hs.le)

/-- The density obtained by summing all integer translates of the three unperturbed
affine branch images. -/
@[no_expose]
noncomputable def periodicTriangularDensity (h a y : ℝ) : ℝ :=
  h / (h + 4 * a) *
      (((gridIntervalIndices h 0 (h / 4 + a) y).card : ℝ) +
       ((gridIntervalIndices h (3 * h / 4 - a) h y).card : ℝ)) +
    h / (4 * a - h) *
      ((gridIntervalIndices h (3 * h / 4 - a) (h / 4 + a) y).card : ℝ)

-- keep: reusable quantitative coverage bound for the canonical folded density
lemma periodicTriangularDensity_error {h a y : ℝ}
    (hh : 0 < h) (ha : 0 ≤ a) (hscale : 4 ≤ a / h) :
    |periodicTriangularDensity h a y - 1| ≤
      2 * (h / (h + 4 * a)) + h / (4 * a - h) := by
  have hsout : 0 < h + 4 * a := triangular_outer_slope_positive hh ha
  have hsmid : 0 < 4 * a - h := by
    have := triangular_middle_slope_negative hh hscale
    linarith
  let n₁ : ℝ := (gridIntervalIndices h 0 (h / 4 + a) y).card
  let n₂ : ℝ := (gridIntervalIndices h (3 * h / 4 - a) (h / 4 + a) y).card
  let n₃ : ℝ := (gridIntervalIndices h (3 * h / 4 - a) h y).card
  have he₁ : |h / (h + 4 * a) * n₁ - 1 / 4| ≤ h / (h + 4 * a) := by
    apply weighted_gridIntervalIndices_error hh hsout (by norm_num)
    ring
  have he₂ : |h / (4 * a - h) * n₂ - 1 / 2| ≤ h / (4 * a - h) := by
    apply weighted_gridIntervalIndices_error hh hsmid (by norm_num)
    ring
  have he₃ : |h / (h + 4 * a) * n₃ - 1 / 4| ≤ h / (h + 4 * a) := by
    apply weighted_gridIntervalIndices_error hh hsout (by norm_num)
    ring
  have hid : periodicTriangularDensity h a y - 1 =
      (h / (h + 4 * a) * n₁ - 1 / 4) +
        (h / (4 * a - h) * n₂ - 1 / 2) +
        (h / (h + 4 * a) * n₃ - 1 / 4) := by
    dsimp [periodicTriangularDensity, n₁, n₂, n₃]
    ring
  rw [hid]
  exact (abs_add_three _ _ _).trans (by linarith)

end CausalSmith.Experimentation.PilotscorePairingFrontier
