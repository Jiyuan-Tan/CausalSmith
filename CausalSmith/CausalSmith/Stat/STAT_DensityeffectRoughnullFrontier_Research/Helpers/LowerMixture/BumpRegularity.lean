module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.Bumps

/-! Uniform regularity of disjoint signed bumps used by the lower experiment. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The bump height is controlled by distance to either endpoint of its cell. -/
-- @node: lowerBump_endpoint_bounds
lemma lowerBump_endpoint_bounds {z : ℝ} (hz : z ∈ Set.Icc 0 1) :
    |lowerBump z| ≤ z ∧ |lowerBump z| ≤ 1 - z := by
  have htw : |2 * z - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  simp only [lowerBump, if_pos hz, abs_mul, abs_of_nonneg hz.1,
    abs_of_nonneg (sub_nonneg.mpr hz.2)]
  have hb := mul_le_mul_of_nonneg_left htw (mul_nonneg hz.1 (sub_nonneg.mpr hz.2))
  constructor <;> nlinarith [hz.1, hz.2]

/-- On its defining cell the cubic has a numerical Lipschitz constant four. -/
-- @node: lowerBump_lipschitz_on_cell
lemma lowerBump_lipschitz_on_cell {z w : ℝ}
    (hz : z ∈ Set.Icc 0 1) (hw : w ∈ Set.Icc 0 1) :
    |lowerBump z - lowerBump w| ≤ 4 * |z - w| := by
  have htw : |2 * z - 1| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  have hprod : |w * (1 - w)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hw.1, abs_of_nonneg (sub_nonneg.mpr hw.2)]
    nlinarith [hw.1, hw.2]
  have hlin : |z * (1 - z) - w * (1 - w)| ≤ 2 * |z - w| := by
    have he : z * (1 - z) - w * (1 - w) =
        (z - w) * (1 - z) + w * (w - z) := by ring
    rw [he]
    calc
      _ ≤ |(z - w) * (1 - z)| + |w * (w - z)| := abs_add_le _ _
      _ = |z - w| * (1 - z) + w * |z - w| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hz.2),
          abs_of_nonneg hw.1, abs_sub_comm w z]
      _ ≤ _ := by nlinarith [abs_nonneg (z - w), hz.1, hw.2]
  have he : lowerBump z - lowerBump w =
      (z * (1 - z) - w * (1 - w)) * (2 * z - 1) +
        (w * (1 - w)) * (2 * (z - w)) := by
    simp only [lowerBump, if_pos hz, if_pos hw]
    ring
  rw [he]
  calc
    _ ≤ |(z * (1 - z) - w * (1 - w)) * (2 * z - 1)| +
        |(w * (1 - w)) * (2 * (z - w))| := abs_add_le _ _
    _ ≤ 2 * |z - w| + 2 * |z - w| := by
      simp only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      apply add_le_add
      · exact (mul_le_mul_of_nonneg_left htw (abs_nonneg _)).trans (by simpa using hlin)
      · rw [← abs_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hprod
          (by positivity : 0 ≤ 2 * |z - w|)
    _ = _ := by ring

/-- Zero extension across both vanishing endpoints preserves a global Lipschitz bound. -/
-- @node: lowerBump_lipschitz
lemma lowerBump_lipschitz (z w : ℝ) :
    |lowerBump z - lowerBump w| ≤ 4 * |z - w| := by
  have hcross (z w : ℝ) (hz : z ∈ Set.Icc 0 1) (hw : w ∉ Set.Icc 0 1) :
      |lowerBump z - lowerBump w| ≤ 4 * |z - w| := by
    have hb := lowerBump_endpoint_bounds hz
    simp only [lowerBump, if_neg hw, sub_zero]
    change |lowerBump z| ≤ 4 * |z - w|
    have ha := le_abs_self (z - w)
    have hn := neg_le_abs (z - w)
    have ha0 := abs_nonneg (z - w)
    have hout : w < 0 ∨ 1 < w := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hw
      exact hw
    rcases hout with hw | hw <;> linarith [hb.1, hb.2]
  by_cases hz : z ∈ Set.Icc 0 1
  · by_cases hw : w ∈ Set.Icc 0 1
    · exact lowerBump_lipschitz_on_cell hz hw
    · exact hcross z w hz hw
  · by_cases hw : w ∈ Set.Icc 0 1
    · simpa only [abs_sub_comm] using hcross w z hw hz
    · simp [lowerBump, hz, hw, abs_nonneg]

/-- When a cell is active, the signed sum is its single active summand. -/
-- @node: signedBumps_eq_active
lemma signedBumps_eq_active (k : ℕ) (signs : Fin k → Bool) (x : ℝ) (i : Fin k)
    (hi : lowerBump ((k : ℝ) * x - i.val) ≠ 0) :
    signedBumps k signs x = signValue (signs i) * lowerBump ((k : ℝ) * x - i.val) := by
  classical
  apply Finset.sum_eq_single i
  · intro l hl hli
    have hz : lowerBump ((k : ℝ) * x - l.val) = 0 := by
      by_contra hn
      exact hli (scaled_bumps_disjoint k x l i hn hi)
    simp [hz]
  · simp

/-- With no active cell, the signed sum vanishes. -/
-- @node: signedBumps_eq_zero
lemma signedBumps_eq_zero (k : ℕ) (signs : Fin k → Bool) (x : ℝ)
    (h : ∀ i : Fin k, lowerBump ((k : ℝ) * x - i.val) = 0) :
    signedBumps k signs x = 0 := by
  unfold signedBumps
  simp only [h, mul_zero, Finset.sum_const_zero]

/-- Disjoint cells give a global Lipschitz constant proportional to rank, independent of signs. -/
-- @node: signedBumps_lipschitz
lemma signedBumps_lipschitz (k : ℕ) (signs : Fin k → Bool) (x y : ℝ) :
    |signedBumps k signs x - signedBumps k signs y| ≤ 4 * k * |x - y| := by
  classical
  have hsign (i : Fin k) : |signValue (signs i)| = 1 := by
    cases signs i <;> norm_num [signValue]
  have hscale (i : Fin k) : |((k : ℝ) * x - i.val) - ((k : ℝ) * y - i.val)| =
      (k : ℝ) * |x - y| := by
    rw [show (k : ℝ) * x - i.val - ((k : ℝ) * y - i.val) = k * (x - y) by ring,
      abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
  have hone (x y : ℝ) (i : Fin k)
      (hi : lowerBump ((k : ℝ) * x - i.val) ≠ 0)
      (hy : ∀ l : Fin k, lowerBump ((k : ℝ) * y - l.val) = 0) :
      |signedBumps k signs x - signedBumps k signs y| ≤ 4 * k * |x - y| := by
    rw [signedBumps_eq_active k signs x i hi, signedBumps_eq_zero k signs y hy,
      sub_zero, abs_mul, hsign, one_mul]
    have h := lowerBump_lipschitz ((k : ℝ) * x - i.val) ((k : ℝ) * y - i.val)
    rw [hy i, sub_zero] at h
    convert h using 1
    simp [← mul_sub, abs_mul, mul_assoc]
  by_cases hx : ∃ i : Fin k, lowerBump ((k : ℝ) * x - i.val) ≠ 0
  · obtain ⟨i, hi⟩ := hx
    by_cases hy : ∃ l : Fin k, lowerBump ((k : ℝ) * y - l.val) ≠ 0
    · obtain ⟨l, hl⟩ := hy
      rw [signedBumps_eq_active k signs x i hi, signedBumps_eq_active k signs y l hl]
      by_cases hil : i = l
      · subst l
        rw [← mul_sub, abs_mul, hsign, one_mul]
        have h := lowerBump_lipschitz ((k : ℝ) * x - i.val) ((k : ℝ) * y - i.val)
        rw [hscale] at h
        nlinarith
      · have hz := lowerBump_nonzero_support hi
        have hw := lowerBump_nonzero_support hl
        have hb := lowerBump_endpoint_bounds ⟨hz.1.le, hz.2.le⟩
        have hc := lowerBump_endpoint_bounds ⟨hw.1.le, hw.2.le⟩
        have htri := abs_sub (signValue (signs i) * lowerBump ((k : ℝ) * x - i.val))
          (signValue (signs l) * lowerBump ((k : ℝ) * y - l.val))
        simp only [abs_mul, hsign, one_mul] at htri
        have hval : i.val ≠ l.val := fun h => hil (Fin.ext h)
        rcases lt_or_gt_of_ne hval with hlt | hgt
        · have hstep : (i.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hlt
          have hdist := neg_le_abs (x - y)
          have hk := Nat.cast_nonneg (α := ℝ) k
          nlinarith [hb.2, hc.1, mul_le_mul_of_nonneg_left hdist hk, abs_nonneg (x - y)]
        · have hstep : (l.val : ℝ) + 1 ≤ i.val := by exact_mod_cast hgt
          have hdist := le_abs_self (x - y)
          have hk := Nat.cast_nonneg (α := ℝ) k
          nlinarith [hb.1, hc.2, mul_le_mul_of_nonneg_left hdist hk, abs_nonneg (x - y)]
    · exact hone x y i hi (by simpa only [not_exists, not_not] using hy)
  · have hz : ∀ i : Fin k, lowerBump ((k : ℝ) * x - i.val) = 0 := by
      simpa only [not_exists, not_not] using hx
    by_cases hy : ∃ l : Fin k, lowerBump ((k : ℝ) * y - l.val) ≠ 0
    · obtain ⟨l, hl⟩ := hy
      simpa only [abs_sub_comm] using hone y x l hl hz
    · rw [signedBumps_eq_zero k signs x hz,
        signedBumps_eq_zero k signs y (by simpa only [not_exists, not_not] using hy)]
      simp [mul_nonneg, Nat.cast_nonneg, abs_nonneg]

/-- Combining the height and Lipschitz bounds gives the rank-scaled one-tenth Hölder modulus. -/
-- @node: signedBumps_holder
lemma signedBumps_holder (k : ℕ) (signs : Fin k → Bool) (x y : ℝ) :
    |signedBumps k signs x - signedBumps k signs y| ≤
      4 * (k : ℝ) ^ (1 / 10 : ℝ) * |x - y| ^ (1 / 10 : ℝ) := by
  have hnon : 0 ≤ (k : ℝ) * |x - y| := by positivity
  have heq : ((k : ℝ) * |x - y|) ^ (1 / 10 : ℝ) =
      (k : ℝ) ^ (1 / 10 : ℝ) * |x - y| ^ (1 / 10 : ℝ) :=
    Real.mul_rpow (Nat.cast_nonneg _) (abs_nonneg _)
  by_cases hsmall : (k : ℝ) * |x - y| ≤ 1
  · have hr := Real.rpow_le_rpow_of_exponent_ge' hnon hsmall
      (by norm_num : (0 : ℝ) ≤ 1 / 10) (by norm_num : (1 / 10 : ℝ) ≤ 1)
    rw [Real.rpow_one, heq] at hr
    have h := signedBumps_lipschitz k signs x y
    nlinarith
  · have hr : 1 ≤ ((k : ℝ) * |x - y|) ^ (1 / 10 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    rw [heq] at hr
    have h := (abs_sub _ _).trans (add_le_add
      (signedBumps_abs_le_one k signs x) (signedBumps_abs_le_one k signs y))
    linarith

end CausalSmith.Stat.DensityEffectRoughNull
