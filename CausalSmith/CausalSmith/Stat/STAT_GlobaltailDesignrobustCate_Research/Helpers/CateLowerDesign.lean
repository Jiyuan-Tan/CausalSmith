module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.LowerPairDesign

/-! # Compatible lower-pair propensity

Roadmap (C21)--(C22): scaling the baseline power propensity preserves its
power tail and provides control overlap, with the prescribed origin convention.
-/
@[expose] public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory

/-- The scaled least-favorable propensity, with the positive origin version
specified in (C21). -/
-- @node: cateLowerPropensity
noncomputable def cateLowerPropensity (d : ℕ) (q s : ℝ) (x : Fin d → ℝ) : ℝ :=
  if x = 0 then s else s * baselinePropensity d q x

/-- The origin convention is measurable. -/
-- @node: cateLowerPropensity_measurable
lemma cateLowerPropensity_measurable (d : ℕ) (q s : ℝ) (hq : 0 < q) :
    Measurable (cateLowerPropensity d q s) := by
  unfold cateLowerPropensity
  first
  | fun_prop
  | exact Measurable.ite (measurableSet_singleton 0) measurable_const
      (measurable_const.mul (baselinePropensity_measurable d q hq))

/-- The scaled propensity is between zero and its scale on the cube. -/
-- @node: cateLowerPropensity_bounds
lemma cateLowerPropensity_bounds (d : ℕ) (q s : ℝ) (hd : 1 ≤ d)
    (hq : 0 < q) (hs : 0 ≤ s) (x : Fin d → ℝ) (hx : x ∈ cube d) :
    0 ≤ cateLowerPropensity d q s x ∧ cateLowerPropensity d q s x ≤ s := by
  have hb := baselinePropensity_unit_interval d q hd hq x hx
  unfold cateLowerPropensity
  split
  · exact ⟨hs, le_rfl⟩
  · exact ⟨mul_nonneg hs hb.1, (mul_le_mul_of_nonneg_left hb.2 hs).trans_eq (mul_one s)⟩

/-- Compatibility of the scale with the control floor yields pointwise
control overlap, including the origin. -/
-- @node: cateLowerPropensity_control_overlap
lemma cateLowerPropensity_control_overlap (d : ℕ) (q s κ : ℝ) (hd : 1 ≤ d)
    (hq : 0 < q) (hs : 0 ≤ s) (hcompat : s ≤ 1 - κ)
    (x : Fin d → ℝ) (hx : x ∈ cube d) :
    κ ≤ 1 - cateLowerPropensity d q s x := by
  have h := (cateLowerPropensity_bounds d q s hd hq hs x hx).2
  linarith

/-- The baseline power is zero at the origin in positive dimension. -/
-- @node: baselinePropensity_zero
lemma baselinePropensity_zero (d : ℕ) (q : ℝ) (hd : 1 ≤ d) (hq : 0 < q) :
    baselinePropensity d q (0 : Fin d → ℝ) = 0 := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  simp [baselinePropensity, maxCoordinate, Real.zero_rpow (ne_of_gt (div_pos hdpos hq))]

/-- Calibrating the scale by `C * s^q = 1` gives the full global-tail
envelope in (C22); above the scale, the probability bound is simply one. -/
-- @node: cateLowerPropensity_global_tail
lemma cateLowerPropensity_global_tail (d : ℕ) (q C s : ℝ) (hd : 1 ≤ d)
    (hq : 0 < q) (hC : 0 ≤ C) (hs : 0 < s) (hcal : C * s ^ q = 1)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real {x | cateLowerPropensity d q s x ≤ t} ≤
      C * t ^ q := by
  have hfinite : volume (cube d) ≠ ⊤ := by simp [cube, Real.volume_Icc_pi]
  have hmass : (volume.restrict (cube d)).real Set.univ = 1 := by
    simp [Measure.real, cube, Real.volume_Icc_pi]
  by_cases hts : t ≤ s
  · have hsub : {x | cateLowerPropensity d q s x ≤ t} ⊆
        {x | baselinePropensity d q x ≤ t / s} := by
      intro x hx
      change baselinePropensity d q x ≤ t / s
      by_cases hx0 : x = 0
      · subst x
        rw [baselinePropensity_zero d q hd hq]
        exact le_of_lt (div_pos ht.1 hs)
      · exact (le_div_iff₀ hs).mpr (by
          simpa [cateLowerPropensity, hx0, mul_comm] using hx)
    calc
      _ ≤ (volume.restrict (cube d)).real {x | baselinePropensity d q x ≤ t / s} :=
        measureReal_mono hsub (by
          apply ne_top_of_le_ne_top _ (measure_mono (Set.subset_univ _))
          simpa using hfinite)
      _ ≤ (t / s) ^ q := baselinePropensity_sublevel_volume d q hd hq _
        ⟨div_pos ht.1 hs, (div_le_one hs).mpr hts⟩
      _ = C * t ^ q := by
        rw [Real.div_rpow ht.1.le hs.le]
        apply (div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hs q))).mpr
        calc
          t ^ q = t ^ q * (C * s ^ q) := by rw [hcal, mul_one]
          _ = C * t ^ q * s ^ q := by ring
  · calc
      _ ≤ (volume.restrict (cube d)).real Set.univ :=
        measureReal_mono (Set.subset_univ _) (by simpa using hfinite)
      _ = 1 := hmass
      _ = C * s ^ q := hcal.symm
      _ ≤ C * t ^ q := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hs.le (le_of_not_ge hts) hq.le) hC

/-- The specified inverse-power scale calibrates the tail constant exactly. -/
-- @node: cateLowerScale_calibration
lemma cateLowerScale_calibration (q C : ℝ) (hq : 0 < q) (hC : 0 < C) :
    C * (C ^ (-1 / q)) ^ q = 1 := by
  rw [← Real.rpow_mul hC.le]
  have hexp : (-1 / q) * q = -1 := div_mul_cancel₀ _ hq.ne'
  rw [hexp, Real.rpow_neg_one, mul_inv_cancel₀ hC.ne']

/-- The paper's compatibility inequality supplies the required control floor. -/
-- @node: cateLowerScale_compatible
lemma cateLowerScale_compatible (q C κ : ℝ) (hq : 0 < q) (hC : 0 < C)
    (hκ : κ < 1) (hcompat : 1 ≤ C * (1 - κ) ^ q) :
    C ^ (-1 / q) ≤ 1 - κ := by
  have hs : 0 < C ^ (-1 / q) := Real.rpow_pos_of_pos hC _
  apply (Real.rpow_le_rpow_iff hs.le (by linarith) hq).mp
  have hcal := cateLowerScale_calibration q C hq hC
  exact (mul_le_mul_iff_right₀ hC).mp (hcal.trans_le hcompat)

/-- The propensity in (C21) satisfies (C22) for the actual scale `C^(-1/q)`. -/
-- @node: cateLowerPropensity_calibrated_global_tail
lemma cateLowerPropensity_calibrated_global_tail (d : ℕ) (q C : ℝ)
    (hd : 1 ≤ d) (hq : 0 < q) (hC : 0 < C)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    (volume.restrict (cube d)).real
      {x | cateLowerPropensity d q (C ^ (-1 / q)) x ≤ t} ≤ C * t ^ q := by
  exact cateLowerPropensity_global_tail d q C _ hd hq hC.le
    (Real.rpow_pos_of_pos hC _) (cateLowerScale_calibration q C hq hC) t ht

end CausalSmith.Stat.GlobalTailDesignRobustCate
