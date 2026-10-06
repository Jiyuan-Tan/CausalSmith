module
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedCardinality
public import CausalSmith.Experimentation.EXP_PilotscorePairingFrontier_Research.Helpers.FoldedGeometryBounds

/-! # Power-form geometry bounds for the folded family -/

public section

namespace CausalSmith.Experimentation.PilotscorePairingFrontier

open MeasureTheory

lemma reciprocal_rpow_neg_nat (q d : ℕ) (hq : 0 < q) :
    ((q : ℝ)⁻¹) ^ (-(d : ℝ)) = (q : ℝ) ^ d := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [Real.rpow_neg (inv_nonneg.mpr hqR.le), Real.inv_rpow hqR.le]
  simp [Real.rpow_natCast]

lemma FoldedGeometry.card_power_bounds
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B) (hq24 : 24 ≤ q) :
    ((1 / 16 : ℝ) ^ d) * ((q : ℝ)⁻¹) ^ (-(d : ℝ)) ≤ (K : ℝ) ∧
      (K : ℝ) ≤ ((q : ℝ)⁻¹) ^ (-(d : ℝ)) := by
  have hq : 0 < q := lt_of_lt_of_le (by omega) hq24
  have hfloor : q ≤ 16 * (q / 8) := by omega
  have hfloorR : (q : ℝ) / 16 ≤ (q / 8 : ℕ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 16)).2
    have hc : (q : ℝ) ≤ 16 * (q / 8 : ℕ) := by exact_mod_cast hfloor
    nlinarith
  have hqnonneg : (0 : ℝ) ≤ q := by positivity
  have hpow : (0 : ℝ) ≤ (q : ℝ) ^ (d - 1) := by positivity
  have hlower : (q : ℝ) / 16 * (q : ℝ) ^ (d - 1) ≤ K := by
    calc
      (q : ℝ) / 16 * (q : ℝ) ^ (d - 1) ≤
          (q / 8 : ℕ) * (q : ℝ) ^ (d - 1) :=
        mul_le_mul_of_nonneg_right hfloorR hpow
      _ = (((q / 8) * q ^ (d - 1) : ℕ) : ℝ) := by norm_num
      _ ≤ K := by exact_mod_cast hgeo.card_lower hq24
  have hpowstep : (q : ℝ) ^ d = (q : ℝ) * (q : ℝ) ^ (d - 1) := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    simp [pow_succ, mul_comm]
  have hsmall : (1 / 16 : ℝ) ^ d ≤ 1 / 16 := by
    obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    simp only [pow_succ]
    have : (1 / 16 : ℝ) ^ e ≤ 1 := by
      exact pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  constructor
  · rw [reciprocal_rpow_neg_nat q d hq]
    calc
      (1 / 16 : ℝ) ^ d * (q : ℝ) ^ d ≤
          (1 / 16) * (q : ℝ) ^ d :=
        mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = (q : ℝ) / 16 * (q : ℝ) ^ (d - 1) := by
        rw [hpowstep]
        ring
      _ ≤ K := hlower
  · rw [reciprocal_rpow_neg_nat q d hq]
    exact_mod_cast hgeo.card_upper

lemma FoldedGeometry.core_power_lower
    {hd : 0 < d} {q K : ℕ} {Q : Fin K → Set (XSpace d)}
    {psi : Fin K → XSpace d → ℝ} {B : Fin K → Set (XSpace d)}
    (hgeo : FoldedGeometry hd q K Q psi B) (j : Fin K) :
    ((1 / 16 : ℝ) ^ d) * ((q : ℝ)⁻¹) ^ (d : ℝ) ≤
      (cubeMeasure d).real (B j) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hgeo.1
  calc
    (1 / 16 : ℝ) ^ d * ((q : ℝ)⁻¹) ^ (d : ℝ) =
        (((1 / 16 : ℝ) * (q : ℝ)⁻¹) ^ d) := by
      rw [Real.rpow_natCast]
      exact (mul_pow _ _ _).symm
    _ = (((q : ℝ)⁻¹ / 16) ^ d) := by congr 1 <;> ring
    _ ≤ (((q : ℝ)⁻¹ / 8) ^ d) := by
      gcongr
      norm_num
    _ ≤ (cubeMeasure d).real (B j) := hgeo.core_measure_lower j

end CausalSmith.Experimentation.PilotscorePairingFrontier
