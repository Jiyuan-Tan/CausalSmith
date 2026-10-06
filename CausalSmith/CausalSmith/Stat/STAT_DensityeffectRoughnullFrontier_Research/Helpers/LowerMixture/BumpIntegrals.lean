module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.BumpRegularity

/-! Exact squared moments and antisymmetric rational means of the lower sign families. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Scaling a function supported strictly inside a single cell multiplies its integral by 1/k. -/
-- @node: lower_scaled_cell_integral
lemma lower_scaled_cell_integral (k : ℕ) (i : Fin k) (f : ℝ → ℝ)
    (hs0 : Function.support f ⊆ Set.Ioo 0 1) :
    (∫ x, f ((k : ℝ) * x - i.val) ∂unitVolume) =
      (k : ℝ)⁻¹ * ∫ z, f z ∂unitVolume := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  have hi : (i.val : ℝ) + 1 ≤ k := by exact_mod_cast i.isLt
  have hs : Function.support f ⊆ Set.Ioc (-(i.val : ℝ)) ((k : ℝ) - i.val) := by
    intro z hz
    have h := hs0 hz
    constructor <;> linarith [h.1, h.2, (Nat.cast_nonneg i.val : (0 : ℝ) ≤ i.val)]
  have hs1 : Function.support f ⊆ Set.Ioc (0 : ℝ) 1 := by
    intro z hz
    exact ⟨(hs0 hz).1, (hs0 hz).2.le⟩
  have he : (∫ z, f z) = ∫ z, f z ∂unitVolume := by
    rw [← intervalIntegral.integral_eq_integral_of_support_subset hs1,
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
    rfl
  unfold unitVolume
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_sub _ hk.ne']
  simp only [mul_zero, zero_sub, mul_one, smul_eq_mul]
  rw [intervalIntegral.integral_eq_integral_of_support_subset hs, he]
  rfl

/-- A square of the disjoint signed sum contains no cross-cell terms and no signs. -/
-- @node: signedBumps_sq_eq_sum
lemma signedBumps_sq_eq_sum (k : ℕ) (signs : Fin k → Bool) (x : ℝ) :
    (signedBumps k signs x) ^ 2 = ∑ i : Fin k, (lowerBump ((k : ℝ) * x - i.val)) ^ 2 := by
  classical
  by_cases h : ∃ i : Fin k, lowerBump ((k : ℝ) * x - i.val) ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [signedBumps_eq_active k signs x i hi, mul_pow]
    have hs : (signValue (signs i)) ^ 2 = 1 := by cases signs i <;> norm_num [signValue]
    rw [hs, one_mul]
    symm
    apply Finset.sum_eq_single i
    · intro l hl hli
      have hz : lowerBump ((k : ℝ) * x - l.val) = 0 := by
        by_contra hn
        exact hli (scaled_bumps_disjoint k x l i hn hi)
      simp [hz]
    · simp
  · have hz : ∀ i : Fin k, lowerBump ((k : ℝ) * x - i.val) = 0 := by
      simpa only [not_exists, not_not] using h
    rw [signedBumps_eq_zero k signs x hz]
    simp [hz]

/-- The signed outcome family has the exact bump second moment, independently of all signs. -/
-- @node: signedBumps_squared_integral
lemma signedBumps_squared_integral (k : ℕ) (hk : 0 < k) (signs : Fin k → Bool) :
    (∫ x, (signedBumps k signs x) ^ 2 ∂unitVolume) = 1 / 210 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hi (i : Fin k) : Integrable (fun x => (lowerBump ((k : ℝ) * x - i.val)) ^ 2)
      unitVolume := by
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := lowerBump_abs_le_one ((k : ℝ) * x - i.val)
    have hb := abs_le.mp h
    nlinarith [hb.1, hb.2]
  simp_rw [signedBumps_sq_eq_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin k) : (∫ x, (lowerBump ((k : ℝ) * x - i.val)) ^ 2 ∂unitVolume) =
      (k : ℝ)⁻¹ * (1 / 210) := by
    rw [lower_scaled_cell_integral k i (fun z => (lowerBump z) ^ 2), lower_bump_moments.2]
    intro z hz
    exact lowerBump_nonzero_support (fun h => hz (by simp [h]))
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Reflection around the midpoint negates the zero-extended cubic. -/
-- @node: lowerBump_reflection
lemma lowerBump_reflection (z : ℝ) : lowerBump (1 - z) = -lowerBump z := by
  have he : 1 - z ∈ Set.Icc 0 1 ↔ z ∈ Set.Icc 0 1 := by
    simp only [Set.mem_Icc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  by_cases h : z ∈ Set.Icc 0 1
  · simp only [lowerBump, if_pos h, if_pos (he.mpr h)]
    ring
  · simp [lowerBump, h, he]

/-- Lebesgue integration on the unit interval is invariant under midpoint reflection. -/
-- @node: lower_unit_integral_reflection
lemma lower_unit_integral_reflection (f : ℝ → ℝ) :
    (∫ z, f (1 - z) ∂unitVolume) = ∫ z, f z ∂unitVolume := by
  unfold unitVolume
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    intervalIntegral.integral_comp_sub_left]
  norm_num only [sub_self, sub_zero]
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← integral_Icc_eq_integral_Ioc]

/-- A legal denominator bounds a signed bump's rational transform by two. -/
-- @node: lower_signed_ratio_bound
lemma lower_signed_ratio_bound (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4))
    (s : ℝ) (hs : |s| = 1) (z : ℝ) :
    0 < 1 + tau * (s * lowerBump z) ∧
    |s * lowerBump z / (1 + tau * (s * lowerBump z))| ≤ 2 := by
  have hb : |s * lowerBump z| ≤ 1 := by simpa [abs_mul, hs] using lowerBump_abs_le_one z
  have hr := abs_le.mp hb
  have hd : 3 / 4 ≤ 1 + tau * (s * lowerBump z) := by
    nlinarith [ht.1, ht.2, hr.1, hr.2]
  have hp : 0 < 1 + tau * (s * lowerBump z) := by linarith
  refine ⟨hp, ?_⟩
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).2
  linarith

/-- Antisymmetry makes either signed rational bump have the same negative mean. -/
-- @node: lower_signed_ratio_integral
lemma lower_signed_ratio_integral (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4))
    (s : ℝ) (hs : s = 1 ∨ s = -1) :
    (∫ z, s * lowerBump z / (1 + tau * (s * lowerBump z)) ∂unitVolume) =
      -tau * lowerCphi tau := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hab : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hi : Integrable (fun z => s * lowerBump z / (1 + tau * (s * lowerBump z)))
      unitVolume := by
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      fun_prop) 2
    exact Filter.Eventually.of_forall (fun z => by
      simpa only [Real.norm_eq_abs] using (lower_signed_ratio_bound tau ht s hab z).2)
  have hj : Integrable (fun z => -(s * lowerBump z) / (1 - tau * (s * lowerBump z)))
      unitVolume := by
    have hm : |(-s)| = 1 := by simpa using hab
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      fun_prop) 2
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, neg_mul, mul_neg, add_neg_cancel_right, sub_eq_add_neg] using
      (lower_signed_ratio_bound tau ht (-s) hm z).2
  have he : (∫ z, s * lowerBump z / (1 + tau * (s * lowerBump z)) ∂unitVolume) =
      ∫ z, -(s * lowerBump z) / (1 - tau * (s * lowerBump z)) ∂unitVolume := by
    rw [← lower_unit_integral_reflection (fun z => s * lowerBump z /
      (1 + tau * (s * lowerBump z)))]
    simp_rw [lowerBump_reflection]
    simp only [mul_neg, sub_eq_add_neg]
  have halg (z : ℝ) : s * lowerBump z / (1 + tau * (s * lowerBump z)) +
      -(s * lowerBump z) / (1 - tau * (s * lowerBump z)) =
      -2 * tau * ((lowerBump z) ^ 2 / (1 - tau ^ 2 * (lowerBump z) ^ 2)) := by
    have hp := (lower_signed_ratio_bound tau ht s hab z).1
    have hm := (lower_signed_ratio_bound tau ht (-s) (by simpa using hab) z).1
    have hsquare : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
    have hd : 0 < 1 - tau ^ 2 * (lowerBump z) ^ 2 := by
      have hb := lowerBump_abs_le_one z
      have hbb : (lowerBump z) ^ 2 ≤ 1 := by
        have hbr := abs_le.mp hb
        nlinarith [hbr.1, hbr.2]
      nlinarith [ht.1, ht.2, sq_nonneg (lowerBump z),
        mul_le_mul_of_nonneg_left hbb (sq_nonneg tau)]
    have hmn : 1 - tau * (s * lowerBump z) ≠ 0 := by
      simpa only [neg_mul, mul_neg, sub_eq_add_neg] using hm.ne'
    rw [div_add_div _ _ hp.ne' hmn]
    rw [← mul_div_assoc]
    apply (div_eq_div_iff (mul_ne_zero hp.ne' hmn) hd.ne').2
    rcases hs with rfl | rfl <;> ring
  have havg : (∫ z, s * lowerBump z / (1 + tau * (s * lowerBump z)) ∂unitVolume) +
      (∫ z, -(s * lowerBump z) / (1 - tau * (s * lowerBump z)) ∂unitVolume) =
      -2 * tau * lowerCphi tau := by
    rw [← integral_add hi hj]
    simp_rw [halg]
    rw [integral_const_mul]
    rfl
  rw [← he] at havg
  linarith

/-- Disjointness makes the rational signed family the sum of its cellwise transforms. -/
-- @node: signedBumps_ratio_eq_sum
lemma signedBumps_ratio_eq_sum (tau : ℝ) (k : ℕ) (signs : Fin k → Bool) (x : ℝ) :
    signedBumps k signs x / (1 + tau * signedBumps k signs x) =
      ∑ i : Fin k, signValue (signs i) * lowerBump ((k : ℝ) * x - i.val) /
        (1 + tau * (signValue (signs i) * lowerBump ((k : ℝ) * x - i.val))) := by
  classical
  by_cases h : ∃ i : Fin k, lowerBump ((k : ℝ) * x - i.val) ≠ 0
  · obtain ⟨i, hi⟩ := h
    rw [signedBumps_eq_active k signs x i hi]
    symm
    apply Finset.sum_eq_single i
    · intro l hl hli
      have hz : lowerBump ((k : ℝ) * x - l.val) = 0 := by
        by_contra hn
        exact hli (scaled_bumps_disjoint k x l i hn hi)
      simp [hz]
    · simp
  · have hz : ∀ i : Fin k, lowerBump ((k : ℝ) * x - i.val) = 0 := by
      simpa only [not_exists, not_not] using h
    rw [signedBumps_eq_zero k signs x hz]
    simp [hz]

/-- The rational family is integrable because each signed cell transform is uniformly bounded. -/
-- @node: signedBumps_ratio_integrable
lemma signedBumps_ratio_integrable (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4))
    (k : ℕ) (signs : Fin k → Bool) :
    Integrable (fun x => signedBumps k signs x / (1 + tau * signedBumps k signs x))
      unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  simp_rw [signedBumps_ratio_eq_sum]
  apply integrable_finsetSum
  intro i hi
  apply Integrable.of_bound (by
    apply Measurable.aestronglyMeasurable
    fun_prop) 2
  have hs : |signValue (signs i)| = 1 := by cases signs i <;> norm_num [signValue]
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using
      (lower_signed_ratio_bound tau ht (signValue (signs i)) hs ((k : ℝ) * x - i.val)).2)

/-- Averaging the disjoint rational covariate bumps cancels all signs and the rank. -/
-- @node: signedBumps_ratio_integral
lemma signedBumps_ratio_integral (tau : ℝ) (ht : tau ∈ Set.Icc 0 (1 / 4))
    (k : ℕ) (hk : 0 < k) (signs : Fin k → Bool) :
    (∫ x, signedBumps k signs x / (1 + tau * signedBumps k signs x) ∂unitVolume) =
      -tau * lowerCphi tau := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hs (i : Fin k) : |signValue (signs i)| = 1 := by
    cases signs i <;> norm_num [signValue]
  have hi (i : Fin k) : Integrable (fun x => signValue (signs i) *
      lowerBump ((k : ℝ) * x - i.val) /
        (1 + tau * (signValue (signs i) * lowerBump ((k : ℝ) * x - i.val))))
      unitVolume := by
    apply Integrable.of_bound (by
      apply Measurable.aestronglyMeasurable
      fun_prop) 2
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using
        (lower_signed_ratio_bound tau ht (signValue (signs i)) (hs i)
          ((k : ℝ) * x - i.val)).2)
  simp_rw [signedBumps_ratio_eq_sum]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  have he (i : Fin k) : (∫ x, signValue (signs i) * lowerBump ((k : ℝ) * x - i.val) /
      (1 + tau * (signValue (signs i) * lowerBump ((k : ℝ) * x - i.val))) ∂unitVolume) =
      (k : ℝ)⁻¹ * (-tau * lowerCphi tau) := by
    rw [lower_scaled_cell_integral k i (fun z => signValue (signs i) * lowerBump z /
      (1 + tau * (signValue (signs i) * lowerBump z))), lower_signed_ratio_integral tau ht]
    · cases signs i <;> simp [signValue]
    · intro z hz
      apply lowerBump_nonzero_support
      intro hb
      apply hz
      simp [hb]
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkn : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

end CausalSmith.Stat.DensityEffectRoughNull
