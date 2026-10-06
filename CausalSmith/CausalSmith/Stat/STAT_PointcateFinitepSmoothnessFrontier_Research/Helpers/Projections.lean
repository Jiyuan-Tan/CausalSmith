module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.ProjectionsCore
public import Mathlib.Algebra.Order.Floor.Semifield

/-! Dyadic cell geometry, Holder approximation, and the assembled projection theorem. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (h : ℝ) (J : ℕ)

/-- Every point, including the right endpoint, lies between its cell's closed endpoints. -/
-- @node: cell_closed_bounds
lemma cell_closed_bounds (hh : 0 < h) (j : ℕ) (x : unitInterval)
    (hx : x ∈ window h) :
    1/2-h/2+(cellIndex h j x : ℝ)*cellLen h j ≤ (x : ℝ) ∧
    (x : ℝ) ≤ 1/2-h/2+((cellIndex h j x : ℝ)+1)*cellLen h j := by
  have hd : 0 < cellLen h j := by unfold cellLen; positivity
  have he : (2^j : ℕ)*cellLen h j = h := by
    simp only [cellLen, Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  by_cases hr : (x : ℝ) = 1/2+h/2
  · have hi : cellIndex h j x = 2^j-1 := by
      unfold cellIndex
      have ht : ((x : ℝ)-(1/2-h/2))/cellLen h j = (2^j : ℕ) := by
        rw [div_eq_iff hd.ne']
        rw [he]
        linarith
      rw [ht, Int.floor_toNat, Nat.floor_natCast]
      exact min_eq_left (Nat.sub_le _ _)
    rw [hi, hr]
    have hp : 1 ≤ 2^j := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have hc : ((2^j-1 : ℕ) : ℝ)+1 = (2^j : ℕ) := by
      exact_mod_cast Nat.sub_add_cancel hp
    constructor <;> nlinarith
  · have hb := (cell_mem_iff_interior h hh j (cellIndex h j x)
        (cellIndex_lt h j x) x hr).mp ⟨hx, rfl⟩
    exact ⟨hb.1, hb.2.le⟩

/-- Two points sharing a histogram label are at most one cell length apart. -/
-- @node: cell_distance_le
lemma cell_distance_le (hh : 0 < h) (j : ℕ) (x z : unitInterval)
    (hx : x ∈ window h) (hz : z ∈ cell h j (cellIndex h j x)) :
    |(x : ℝ)-(z : ℝ)| ≤ cellLen h j := by
  have hb := cell_closed_bounds h hh j x hx
  have hb' := cell_closed_bounds h hh j z hz.1
  rw [hz.2] at hb'
  exact abs_le.mpr ⟨by linarith [hb.1, hb'.2], by linarith [hb.2, hb'.1]⟩

/-- A Holder function differs from its histogram cell average by the cell oscillation bound. -/
-- @node: projOp_holder_error
lemma projOp_holder_error (hh : 0 < h ∧ h ≤ 1) (s : ℝ)
    (f : unitInterval → ℝ) (hs : 0 < s ∧ s ≤ 1) (hf : holderBall s f)
    (j : ℕ) (x : unitInterval) (hx : x ∈ window h) :
    |f x - projOp h j f x| ≤ 20 * cellLen h j ^ s := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hd : 0 < cellLen h j := by unfold cellLen; exact div_pos hh.1 (by positivity)
  have hc : MeasurableSet (cell h j (cellIndex h j x)) :=
    (measurable_subtype_coe measurableSet_Icc).inter
      ((measurable_cellIndex h j) (measurableSet_singleton _))
  have hi : Integrable f (design.restrict (cell h j (cellIndex h j x))) := by
    apply Integrable.of_bound hf.1.aestronglyMeasurable 20
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hf.2.1 z)
  have hm : (design.restrict (cell h j (cellIndex h j x))).real Set.univ = cellLen h j := by
    simp only [Measure.real, Measure.restrict_apply_univ,
      design_cell h hh j _ (cellIndex_lt h j x), ENNReal.toReal_ofReal hd.le]
  have hid : f x - projOp h j f x = (cellLen h j)⁻¹ *
      ∫ z in cell h j (cellIndex h j x), (f x - f z) ∂design := by
    rw [projOp_eq_cell_average h j f x hx, integral_sub (integrable_const _) hi,
      integral_const, smul_eq_mul, hm]
    field_simp
  have hb : ∀ᵐ z ∂(design.restrict (cell h j (cellIndex h j x))),
      ‖f x - f z‖ ≤ 20 * cellLen h j ^ s := by
    filter_upwards [ae_restrict_mem hc] with z hz
    rw [Real.norm_eq_abs]
    calc
      _ ≤ 20 * |(x : ℝ)-(z : ℝ)| ^ s := hf.2.2 x z
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (abs_nonneg _) (cell_distance_le h hh.1 j x z hx hz) hs.1.le)
        (by norm_num)
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [hm, Real.norm_eq_abs] at hb'
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  calc
    _ ≤ (cellLen h j)⁻¹ * (20 * cellLen h j ^ s * cellLen h j) :=
      mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hd.le)
    _ = _ := by field_simp

/-- Passing from a dyadic child to its parent divides the label by two. -/
-- @node: cellIndex_parent
lemma cellIndex_parent (hh : 0 < h) (j : ℕ) (x : unitInterval)
    (hx : x ∈ window h) : cellIndex h j x = cellIndex h (j+1) x / 2 := by
  have hd : 0 < cellLen h (j+1) := by unfold cellLen; positivity
  have hl : cellLen h j = cellLen h (j+1) * 2 := by
    simp only [cellLen, pow_succ]
    field_simp
  by_cases hr : (x : ℝ) = 1/2+h/2
  · have hi : ∀ k, cellIndex h k x = 2^k-1 := by
      intro k
      have he : (2^k : ℕ) * cellLen h k = h := by
        simp only [cellLen, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
      have ht : ((x : ℝ)-(1/2-h/2))/cellLen h k = (2^k : ℕ) := by
        have hk : 0 < cellLen h k := by unfold cellLen; positivity
        rw [div_eq_iff hk.ne', he]
        linarith
      simp only [cellIndex, ht, Int.floor_toNat, Nat.floor_natCast]
      exact min_eq_left (Nat.sub_le _ _)
    rw [hi, hi, pow_succ]
    have hp : 0 < 2^j := pow_pos (by decide) _
    omega
  · rw [cellIndex_eq_floor_interior h hh j x hx (lt_of_le_of_ne hx.2 hr),
      cellIndex_eq_floor_interior h hh (j+1) x hx (lt_of_le_of_ne hx.2 hr), hl]
    rw [← div_div, Nat.floor_div_ofNat]

/-- Every child cell is contained in the cell carrying its parent's label. -/
-- @node: cell_child_subset_parent
lemma cell_child_subset_parent (hh : 0 < h) (j : ℕ) (x : unitInterval)
    (hx : x ∈ window h) :
    cell h (j+1) (cellIndex h (j+1) x) ⊆ cell h j (cellIndex h j x) := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  rw [cellIndex_parent h hh j z hz.1, cellIndex_parent h hh j x hx, hz.2]

/-- A band average is bounded by the oscillation on its parent cell. -/
-- @node: bandOp_holder_bound
lemma bandOp_holder_bound (hh : 0 < h ∧ h ≤ 1) (s : ℝ)
    (f : unitInterval → ℝ) (hs : 0 < s ∧ s ≤ 1) (hf : holderBall s f)
    (j : ℕ) (hj : 1 ≤ j) (x : unitInterval) (hx : x ∈ window h) :
    |bandOp h j f x| ≤ 40 * cellLen h j ^ s := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hd : 0 < cellLen h (k+1) := by unfold cellLen; exact div_pos hh.1 (by positivity)
  have hc : MeasurableSet (cell h (k+1) (cellIndex h (k+1) x)) :=
    (measurable_subtype_coe measurableSet_Icc).inter
      ((measurable_cellIndex h (k+1)) (measurableSet_singleton _))
  have hi : Integrable f (design.restrict (cell h (k+1) (cellIndex h (k+1) x))) := by
    apply Integrable.of_bound hf.1.aestronglyMeasurable 20
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hf.2.1 z)
  have hlp : MemLp f 2 (design.restrict (window h)) := by
    apply MemLp.of_bound hf.1.aestronglyMeasurable 20
    exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hf.2.1 z)
  have hm : (design.restrict (cell h (k+1) (cellIndex h (k+1) x))).real Set.univ =
      cellLen h (k+1) := by
    simp only [Measure.real, Measure.restrict_apply_univ,
      design_cell h hh (k+1) _ (cellIndex_lt h (k+1) x), ENNReal.toReal_ofReal hd.le]
  have hid : bandOp h (k+1) f x = (cellLen h (k+1))⁻¹ *
      ∫ z in cell h (k+1) (cellIndex h (k+1) x),
        (f z - projOp h k f x) ∂design := by
    rw [bandOp_eq_sub h (k+1) f hlp x, Nat.add_sub_cancel,
      projOp_eq_cell_average h (k+1) f x hx,
      integral_sub hi (integrable_const _), integral_const, smul_eq_mul, hm]
    field_simp
  have hb : ∀ᵐ z ∂(design.restrict (cell h (k+1) (cellIndex h (k+1) x))),
      ‖f z - projOp h k f x‖ ≤ 20 * cellLen h k ^ s := by
    filter_upwards [ae_restrict_mem hc] with z hz
    have hp := cell_child_subset_parent h hh.1 k x hx hz
    have he : projOp h k f z = projOp h k f x := by
      rw [projOp_eq_cell_average h k f z hz.1,
        projOp_eq_cell_average h k f x hx, hp.2]
    rw [Real.norm_eq_abs, ← he]
    exact projOp_holder_error h hh s f hs hf k z hz.1
  have hb' := norm_integral_le_of_norm_le_const hb
  rw [hm, Real.norm_eq_abs] at hb'
  have hl : cellLen h k = 2 * cellLen h (k+1) := by
    simp only [cellLen, pow_succ]
    field_simp
  have ht : (2 : ℝ)^s ≤ 2 := by
    calc
      _ ≤ (2 : ℝ)^1 := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs.2
      _ = 2 := by simp
  rw [hid, abs_mul, abs_of_pos (inv_pos.mpr hd)]
  calc
    _ ≤ (cellLen h (k+1))⁻¹ * (20 * cellLen h k ^ s * cellLen h (k+1)) :=
      mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hd.le)
    _ = 20 * cellLen h k ^ s := by field_simp
    _ = 20 * (2^s * cellLen h (k+1)^s) := by rw [hl, Real.mul_rpow (by norm_num) hd.le]
    _ ≤ 40 * cellLen h (k+1)^s := by
      nlinarith [Real.rpow_nonneg hd.le s]

/-- Multiplying a child histogram section by its parent gives the parent height times
that child section. -/
-- @node: projKernel_child_parent_mul
lemma projKernel_child_parent_mul (hh : 0 < h) (j : ℕ)
    (x z : unitInterval) :
    projKernel h (j+1) x z * projKernel h j x z =
      (cellLen h j)⁻¹ * projKernel h (j+1) x z := by
  by_cases hc : x ∈ window h ∧ z ∈ window h ∧
      cellIndex h (j+1) x = cellIndex h (j+1) z
  · have hp : cellIndex h j x = cellIndex h j z := by
      rw [cellIndex_parent h hh j x hc.1, cellIndex_parent h hh j z hc.2.1,
        hc.2.2]
    simp [projKernel, hc.1, hc.2.1, hc.2.2, hp]
    ring
  · simp only [projKernel, if_neg hc, zero_mul, mul_zero]

/-- The mixed child-parent section integral equals the inverse parent cell length. -/
-- @node: projKernel_child_parent_integral
lemma projKernel_child_parent_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, projKernel h (j+1) x z * projKernel h j x z ∂design) =
      (cellLen h j)⁻¹ := by
  simp_rw [projKernel_child_parent_mul h hh.1 j]
  rw [integral_const_mul, projKernel_window_integral h hh (j+1) z hz, mul_one]

/-- Expanding the child-minus-parent square gives the exact dyadic band energy. -/
-- @node: bandKernel_sq_integral
lemma bandKernel_sq_integral (hh : 0 < h ∧ h ≤ 1) (j : ℕ) (hj : 1 ≤ j)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, (bandKernel h j x z)^2 ∂design) =
      (2 : ℝ)^(j-1) * h⁻¹ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hm (l : ℕ) : MemLp (fun x => projKernel h l x z) 2
      (design.restrict (window h)) := by
    apply MemLp.of_bound (by fun_prop) |(cellLen h l)⁻¹|
    exact Filter.Eventually.of_forall (fun x => by
      simp only [projKernel]; split_ifs <;> simp)
  have hc := (hm (k+1)).integrable_sq
  have hp := (hm k).integrable_sq
  have hcp : Integrable (fun x => projKernel h (k+1) x z * projKernel h k x z)
      (design.restrict (window h)) := (hm (k+1)).integrable_mul (hm k)
  have hc2 := hcp.const_mul 2
  have hd := hc.sub hc2
  have he : (fun x => (bandKernel h (k+1) x z)^2) =
      (fun x => (projKernel h (k+1) x z)^2 -
        2 * (projKernel h (k+1) x z * projKernel h k x z) +
        (projKernel h k x z)^2) := by
    funext x
    simp only [bandKernel, Nat.add_sub_cancel]
    ring
  rw [he]
  have hi : (∫ x in window h,
      (projKernel h (k+1) x z)^2 -
        2 * (projKernel h (k+1) x z * projKernel h k x z) +
        (projKernel h k x z)^2 ∂design) =
      (∫ x in window h, (projKernel h (k+1) x z)^2 ∂design) -
        2 * (∫ x in window h, projKernel h (k+1) x z * projKernel h k x z ∂design) +
        (∫ x in window h, (projKernel h k x z)^2 ∂design) := by
    integral_linearity
  rw [hi, projKernel_sq_integral h hh (k+1) z hz,
    projKernel_sq_integral h hh k z hz,
    projKernel_child_parent_integral h hh k z hz]
  simp only [Nat.succ_sub_one, cellLen, pow_succ]
  field_simp
  ring

/-- Equal fine labels give equal labels at every coarser resolution. -/
-- @node: cellIndex_ancestor_eq
lemma cellIndex_ancestor_eq (hh : 0 < h) (j k : ℕ) (hjk : j ≤ k)
    (x z : unitInterval) (hx : x ∈ window h) (hz : z ∈ window h)
    (he : cellIndex h k x = cellIndex h k z) :
    cellIndex h j x = cellIndex h j z := by
  induction k, hjk using Nat.le_induction with
  | base => exact he
  | succ k hjk ih =>
    apply ih
    rw [cellIndex_parent h hh k x hx, cellIndex_parent h hh k z hz, he]

/-- A finer histogram section is supported inside the corresponding coarse section. -/
-- @node: projKernel_fine_coarse_mul
lemma projKernel_fine_coarse_mul (hh : 0 < h) (j k : ℕ) (hjk : j ≤ k)
    (x z : unitInterval) :
    projKernel h k x z * projKernel h j x z =
      (cellLen h j)⁻¹ * projKernel h k x z := by
  by_cases hc : x ∈ window h ∧ z ∈ window h ∧ cellIndex h k x = cellIndex h k z
  · have hp := cellIndex_ancestor_eq h hh j k hjk x z hc.1 hc.2.1 hc.2.2
    simp [projKernel, hc.1, hc.2.1, hc.2.2, hp]
    ring
  · simp only [projKernel, if_neg hc, zero_mul, mul_zero]

/-- The mixed section integral has the height of the coarser histogram. -/
-- @node: projKernel_fine_coarse_integral
lemma projKernel_fine_coarse_integral (hh : 0 < h ∧ h ≤ 1)
    (j k : ℕ) (hjk : j ≤ k) (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, projKernel h k x z * projKernel h j x z ∂design) =
      (cellLen h j)⁻¹ := by
  simp_rw [projKernel_fine_coarse_mul h hh.1 j k hjk]
  rw [integral_const_mul, projKernel_window_integral h hh k z hz, mul_one]

/-- Mixed histogram heights cancel between two distinct dyadic bands. -/
-- @node: bandKernel_sections_orthogonal
lemma bandKernel_sections_orthogonal (hh : 0 < h ∧ h ≤ 1)
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k)
    (z : unitInterval) (hz : z ∈ window h) :
    (∫ x in window h, bandKernel h j x z * bandKernel h k x z ∂design) = 0 := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hm (l : ℕ) : MemLp (fun x => projKernel h l x z) 2
      (design.restrict (window h)) := by
    apply MemLp.of_bound (by fun_prop) |(cellLen h l)⁻¹|
    exact Filter.Eventually.of_forall (fun x => by
      simp only [projKernel]; split_ifs <;> simp)
  have hi (a b : ℕ) : Integrable
      (fun x => projKernel h a x z * projKernel h b x z)
      (design.restrict (window h)) := (hm a).integrable_mul (hm b)
  have ordered (a b : ℕ) (hab : a < b) :
      (∫ x in window h, bandKernel h b x z * bandKernel h a x z ∂design) = 0 := by
    have hle : a ≤ b-1 := by omega
    have he : (fun x => bandKernel h b x z * bandKernel h a x z) =
        (fun x => (projKernel h b x z * projKernel h a x z -
          projKernel h b x z * projKernel h (a-1) x z) -
          (projKernel h (b-1) x z * projKernel h a x z -
          projKernel h (b-1) x z * projKernel h (a-1) x z)) := by
      funext x
      simp only [bandKernel]
      ring
    rw [he]
    have hexp : (∫ x in window h,
        (projKernel h b x z * projKernel h a x z -
          projKernel h b x z * projKernel h (a-1) x z) -
          (projKernel h (b-1) x z * projKernel h a x z -
          projKernel h (b-1) x z * projKernel h (a-1) x z) ∂design) =
        ((∫ x in window h, projKernel h b x z * projKernel h a x z ∂design) -
          (∫ x in window h, projKernel h b x z * projKernel h (a-1) x z ∂design)) -
        ((∫ x in window h, projKernel h (b-1) x z * projKernel h a x z ∂design) -
          (∫ x in window h, projKernel h (b-1) x z * projKernel h (a-1) x z ∂design)) := by
      integral_linearity
    rw [hexp, projKernel_fine_coarse_integral h hh a b hab.le z hz,
      projKernel_fine_coarse_integral h hh (a-1) b (by omega) z hz,
      projKernel_fine_coarse_integral h hh a (b-1) hle z hz,
      projKernel_fine_coarse_integral h hh (a-1) (b-1) (by omega) z hz]
    ring
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · calc
      _ = ∫ x in window h, bandKernel h k x z * bandKernel h j x z ∂design := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => mul_comm _ _)
      _ = 0 := ordered j k hlt
  · exact ordered k j hgt

/-- Averaging a function constant on the selected cell returns that constant. -/
-- @node: projOp_of_cell_constant
lemma projOp_of_cell_constant (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (x : unitInterval) (hx : x ∈ window h) (c : ℝ)
    (hc : ∀ z ∈ cell h j (cellIndex h j x), f z = c) :
    projOp h j f x = c := by
  have hm : MeasurableSet (cell h j (cellIndex h j x)) :=
    (measurable_subtype_coe measurableSet_Icc).inter
      ((measurable_cellIndex h j) (measurableSet_singleton _))
  have hd : 0 < cellLen h j := by
    unfold cellLen
    exact div_pos hh.1 (by positivity)
  rw [projOp_eq_cell_average h j f x hx]
  have hi : (∫ z in cell h j (cellIndex h j x), f z ∂design) =
      ∫ _z in cell h j (cellIndex h j x), c ∂design := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hm] with z hz
    exact hc z hz
  rw [hi]
  simp only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
    design_cell h hh j _ (cellIndex_lt h j x), ENNReal.toReal_ofReal hd.le]
  field_simp

/-- A finer cell average preserves every coarser histogram value. -/
-- @node: projOp_fine_coarse
lemma projOp_fine_coarse (hh : 0 < h ∧ h ≤ 1) (j k : ℕ) (hjk : j ≤ k)
    (f : unitInterval → ℝ) (x : unitInterval) (hx : x ∈ window h) :
    projOp h k (projOp h j f) x = projOp h j f x := by
  apply projOp_of_cell_constant h hh k _ x hx
  intro z hz
  have he := cellIndex_ancestor_eq h hh.1 j k hjk z x hz.1 hx hz.2
  rw [projOp_eq_cell_average h j f z hz.1, projOp_eq_cell_average h j f x hx, he]

/-- Fine averaging preserves a section of a coarser histogram kernel. -/
-- @node: projOp_fine_coarse_section
lemma projOp_fine_coarse_section (hh : 0 < h ∧ h ≤ 1) (j k : ℕ) (hjk : j ≤ k)
    (x z : unitInterval) (hz : z ∈ window h) :
    projOp h k (fun t => projKernel h j x t) z = projKernel h j x z := by
  apply projOp_of_cell_constant h hh k _ z hz
  intro t ht
  have he := cellIndex_ancestor_eq h hh.1 j k hjk t z ht.1 hz ht.2
  simp only [projKernel, ht.1, hz, he]

/-- Self-adjointness transfers fine preservation of coarse kernel sections to coarse
averaging of a fine histogram. -/
-- @node: projOp_coarse_fine
lemma projOp_coarse_fine (hh : 0 < h ∧ h ≤ 1) (j k : ℕ) (hjk : j ≤ k)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (x : unitInterval) :
    projOp h j (projOp h k f) x = projOp h j f x := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  have hm : MemLp (fun z => projKernel h j x z) 2
      (design.restrict (window h)) := by
    apply MemLp.of_bound (by fun_prop) |(cellLen h j)⁻¹|
    exact Filter.Eventually.of_forall (fun z => by
      simp only [projKernel]; split_ifs <;> simp)
  have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
  rw [projOp_eq_window_integral, projOp_eq_window_integral,
    ← projOp_self_adjoint h k (fun z => projKernel h j x z) f hm hf]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hw] with z hz
  rw [projOp_fine_coarse_section h hh j k hjk x z hz]

/-- Two dyadic histogram projections compose to the projection at the coarser level. -/
-- @node: projOp_nested
lemma projOp_nested (hh : 0 < h ∧ h ≤ 1) (j k : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (x : unitInterval) (hx : x ∈ window h) :
    projOp h j (projOp h k f) x = projOp h (min j k) f x := by
  rcases le_total j k with hjk | hkj
  · rw [min_eq_left hjk]
    exact projOp_coarse_fine h hh j k hjk f hf x
  · rw [min_eq_right hkj]
    exact projOp_fine_coarse h hh k j hkj f x hx

/-- Histogram averaging distributes over differences of square-integrable inputs. -/
-- @node: projOp_sub
lemma projOp_sub (j : ℕ) (f g : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h))) (x : unitInterval) :
    projOp h j (fun z => f z - g z) x = projOp h j f x - projOp h j g x := by
  simp only [projOp, mul_sub]
  exact integral_sub (integrable_projKernel_mul h j f hf x)
    (integrable_projKernel_mul h j g hg x)

/-- Adjacent histogram differences remain square-integrable on the window. -/
-- @node: bandOp_memLp
lemma bandOp_memLp (j : ℕ) (f : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h))) :
    MemLp (bandOp h j f) 2 (design.restrict (window h)) := by
  have he : bandOp h j f = projOp h j f - projOp h (j-1) f := by
    funext x
    exact bandOp_eq_sub h j f hf x
  rw [he]
  exact (projOp_memLp h j f).sub (projOp_memLp h (j-1) f)

/-- Distinct positive-level histogram bands have zero operator product. -/
-- @node: bandOp_distinct_product
lemma bandOp_distinct_product (hh : 0 < h ∧ h ≤ 1) (j k : ℕ)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h)))
    (x : unitInterval) (hx : x ∈ window h) :
    bandOp h j (bandOp h k f) x = 0 := by
  rw [bandOp_eq_sub h j _ (bandOp_memLp h k f hf)]
  have he : bandOp h k f = fun z => projOp h k f z - projOp h (k-1) f z := by
    funext z
    exact bandOp_eq_sub h k f hf z
  rw [he, projOp_sub h j _ _ (projOp_memLp h k f) (projOp_memLp h (k-1) f),
    projOp_sub h (j-1) _ _ (projOp_memLp h k f) (projOp_memLp h (k-1) f)]
  rw [projOp_nested h hh j k f hf x hx,
    projOp_nested h hh j (k-1) f hf x hx,
    projOp_nested h hh (j-1) k f hf x hx,
    projOp_nested h hh (j-1) (k-1) f hf x hx]
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · rw [min_eq_left (by omega : j ≤ k), min_eq_left (by omega : j ≤ k-1),
      min_eq_left (by omega : j-1 ≤ k), min_eq_left (by omega : j-1 ≤ k-1)]
    ring
  · rw [min_eq_right (by omega : k ≤ j), min_eq_right (by omega : k-1 ≤ j),
      min_eq_right (by omega : k ≤ j-1), min_eq_right (by omega : k-1 ≤ j-1)]
    ring

/-- Subtracting the self-adjoint histogram identities gives band self-adjointness. -/
-- @node: bandOp_self_adjoint
lemma bandOp_self_adjoint (j : ℕ) (f g : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h))) :
    (∫ x in window h, bandOp h j f x * g x ∂design) =
      ∫ x in window h, f x * bandOp h j g x ∂design := by
  have hi (k : ℕ) := (projOp_memLp h k f).integrable_mul hg
  have hi' (k : ℕ) := hf.integrable_mul (projOp_memLp h k g)
  simp_rw [bandOp_eq_sub h j f hf, bandOp_eq_sub h j g hg, sub_mul, mul_sub]
  have hil (k : ℕ) : Integrable (fun x => projOp h k f x * g x)
      (design.restrict (window h)) := hi k
  have hir (k : ℕ) : Integrable (fun x => f x * projOp h k g x)
      (design.restrict (window h)) := hi' k
  rw [integral_sub (hil j) (hil (j-1)), integral_sub (hir j) (hir (j-1)),
    projOp_self_adjoint h j f g hf hg, projOp_self_adjoint h (j-1) f g hf hg]

/-- Self-adjointness and the zero band products give orthogonality in the window. -/
-- @node: bandOp_distinct_orthogonal
lemma bandOp_distinct_orthogonal (hh : 0 < h ∧ h ≤ 1) (j k : ℕ)
    (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k)
    (f g : unitInterval → ℝ)
    (hf : MemLp f 2 (design.restrict (window h)))
    (hg : MemLp g 2 (design.restrict (window h))) :
    (∫ x in window h, bandOp h j f x * bandOp h k g x ∂design) = 0 := by
  rw [bandOp_self_adjoint h j f _ hf (bandOp_memLp h k g hg)]
  calc
    _ = ∫ _x in window h, (0 : ℝ) ∂design := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
        MeasurableSet (window h))] with x hx
      rw [bandOp_distinct_product h hh j k hj hk hjk g hg x hx, mul_zero]
    _ = 0 := integral_zero _ _

/-- The energy of a new band is the increase between adjacent projection energies. -/
-- @node: bandOp_energy_increment
lemma bandOp_energy_increment (hh : 0 < h ∧ h ≤ 1) (j : ℕ)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) =
      (∫ x in window h, (projOp h (j+1) f x)^2 ∂design) -
      ∫ x in window h, (projOp h j f x)^2 ∂design := by
  have hp := projOp_memLp h (j+1) f
  have hq := projOp_memLp h j f
  have hcross : (∫ x in window h, projOp h (j+1) f x * projOp h j f x ∂design) =
      ∫ x in window h, (projOp h j f x)^2 ∂design := by
    rw [projOp_self_adjoint h (j+1) f _ hf hq]
    calc
      _ = ∫ x in window h, f x * projOp h j f x ∂design := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (measurable_subtype_coe measurableSet_Icc :
          MeasurableSet (window h))] with x hx
        rw [projOp_fine_coarse h hh j (j+1) (by omega) f x hx]
      _ = _ := (projOp_energy_pairing h hh j f hf).symm
  have he : (fun x => (bandOp h (j+1) f x)^2) =
      fun x => (projOp h (j+1) f x)^2 -
        2 * (projOp h (j+1) f x * projOp h j f x) + (projOp h j f x)^2 := by
    funext x
    rw [bandOp_eq_sub h (j+1) f hf x, Nat.add_sub_cancel]
    ring
  rw [he]
  have hi := hp.integrable_sq
  have hi' := hq.integrable_sq
  have hiCross : Integrable (fun x => projOp h (j+1) f x * projOp h j f x)
      (design.restrict (window h)) := hp.integrable_mul hq
  have hiTwice := hiCross.const_mul 2
  have hiDiff := hi.sub hiTwice
  have hexp : (∫ x in window h,
      (projOp h (j+1) f x)^2 - 2 * (projOp h (j+1) f x * projOp h j f x) +
        (projOp h j f x)^2 ∂design) =
      (∫ x in window h, (projOp h (j+1) f x)^2 ∂design) -
        2 * (∫ x in window h, projOp h (j+1) f x * projOp h j f x ∂design) +
        (∫ x in window h, (projOp h j f x)^2 ∂design) := by
    integral_linearity
  rw [hexp, hcross]
  ring

/-- The energies of adjacent bands telescope to the finest energy minus the coarse energy. -/
-- @node: bandOp_energy_telescope
lemma bandOp_energy_telescope (hh : 0 < h ∧ h ≤ 1)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∑ j ∈ Finset.range J, ∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) =
      (∫ x in window h, (projOp h J f x)^2 ∂design) -
      ∫ x in window h, (projOp h 0 f x)^2 ∂design := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, bandOp_energy_increment h hh J f hf]
    ring

/-- Projection contraction and nonnegative coarse energy bound the total band energy. -/
-- @node: bandOp_energy_sum_le
lemma bandOp_energy_sum_le (hh : 0 < h ∧ h ≤ 1)
    (f : unitInterval → ℝ) (hf : MemLp f 2 (design.restrict (window h))) :
    (∑ j ∈ Finset.range J, ∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) ≤
      ∫ x in window h, (f x)^2 ∂design := by
  rw [bandOp_energy_telescope h J hh f hf]
  exact le_trans (sub_le_self _ (integral_nonneg (fun x => sq_nonneg (projOp h 0 f x))))
    (projOp_energy_contraction h hh J f hf)

-- @node: lem:dyadic-projection-geometry
/-- Nested projections preserve cell integrals, are self-adjoint and contract L2; their
bands are mutually orthogonal, with exact section norms and Holder approximation. -/
lemma dyadic_projection_geometry (hh : 0 < h ∧ h ≤ 1) -- @realizes h(0<h≤1)
    :
  (∀ (f g : unitInterval → ℝ), MemLp f 2 (design.restrict (window h)) →
    MemLp g 2 (design.restrict (window h)) →
    (∀ j l, l < 2^j → (∫ x in cell h j l, projOp h j f x ∂design) = ∫ x in cell h j l, f x ∂design) ∧
    (∀ j, (∫ x in window h, projOp h j f x * g x ∂design) =
      ∫ x in window h, f x * projOp h j g x ∂design) ∧
    (∀ j k x, x ∈ window h → projOp h j (projOp h k f) x = projOp h (min j k) f x) ∧
    (∀ j k, 1 ≤ j → 1 ≤ k → j ≠ k → ∀ x ∈ window h, bandOp h j (bandOp h k f) x = 0) ∧
    (∀ j, 1 ≤ j → ∀ x ∈ window h, projOp h 0 (bandOp h j f) x = 0) ∧
    (∀ j k, 1 ≤ j → 1 ≤ k → j ≠ k →
      (∫ x in window h, bandOp h j f x * bandOp h k g x ∂design) = 0) ∧
    (∀ j, 1 ≤ j → (∫ x in window h, projOp h 0 f x * bandOp h j g x ∂design) = 0) ∧
    (∀ x ∈ window h, projOp h 0 f x + ∑ j ∈ Finset.range J, bandOp h (j+1) f x = projOp h J f x) ∧
    (∀ j, (∫ x in window h, (projOp h j f x)^2 ∂design) ≤ ∫ x in window h, (f x)^2 ∂design) ∧
    ((∑ j ∈ Finset.range J, ∫ x in window h, (bandOp h (j+1) f x)^2 ∂design) ≤
      ∫ x in window h, (f x)^2 ∂design)) ∧
  (∀ᵐ z ∂(design.restrict (window h)),
    (∫ x in window h, (projKernel h 0 x z)^2 ∂design) = h⁻¹ ∧
    (∀ j, 1 ≤ j → (∫ x in window h, (bandKernel h j x z)^2 ∂design) = (2 : ℝ)^(j-1) * h⁻¹) ∧
    (∀ j k, 1 ≤ j → 1 ≤ k → j ≠ k →
      (∫ x in window h, bandKernel h j x z * bandKernel h k x z ∂design) = 0) ∧
    (∀ j, 1 ≤ j → (∫ x in window h, projKernel h 0 x z * bandKernel h j x z ∂design) = 0)) ∧
  ((∫ z in window h, ∫ x in window h, (projKernel h J x z)^2 ∂design ∂design) = (2 : ℝ)^J) ∧
  (∀ (s : ℝ) (f : unitInterval → ℝ), 0 < s ∧ s ≤ 1 → holderBall s f →
    (∀ j x, x ∈ window h → |f x - projOp h j f x| ≤ 20 * cellLen h j ^ s) ∧
    (∀ j x, 1 ≤ j → x ∈ window h → |bandOp h j f x| ≤ 40 * cellLen h j ^ s)) := by
  have hsectionsFull : ∀ᵐ z ∂(design.restrict (window h)),
      (∫ x in window h, (projKernel h 0 x z)^2 ∂design) = h⁻¹ ∧
      (∀ j, 1 ≤ j → (∫ x in window h, (bandKernel h j x z)^2 ∂design) = (2 : ℝ)^(j-1) * h⁻¹) ∧
      (∀ j k, 1 ≤ j → 1 ≤ k → j ≠ k →
        (∫ x in window h, bandKernel h j x z * bandKernel h k x z ∂design) = 0) ∧
      (∀ j, 1 ≤ j → (∫ x in window h, projKernel h 0 x z * bandKernel h j x z ∂design) = 0) := by
    have hw : MeasurableSet (window h) := measurable_subtype_coe measurableSet_Icc
    filter_upwards [ae_restrict_mem hw] with z hzw
    exact ⟨projKernel_zero_sq_integral h hh z hzw, fun j hj => bandKernel_sq_integral h hh j hj z hzw,
      fun j k hj hk hjk => bandKernel_sections_orthogonal h hh j k hj hk hjk z hzw,
      fun j _ => projKernel_zero_bandKernel_orthogonal h hh j z hzw⟩
  refine ⟨?_, hsectionsFull, projKernel_product_sq_integral h hh J,
    fun s f hs hf => ⟨fun j x hx => projOp_holder_error h hh s f hs hf j x hx,
      fun j x hj hx => bandOp_holder_bound h hh s f hs hf j hj x hx⟩⟩
  intro f g hf hg
  refine ⟨fun j l hl => projOp_cell_integral h hh j l hl f, fun j => projOp_self_adjoint h j f g hf hg, ?_,
    fun j k hj hk hjk x hx => bandOp_distinct_product h hh j k hj hk hjk f hf x hx,
    fun j _ x hx => projOp_zero_bandOp h hh j f hf x hx,
    fun j k hj hk hjk => bandOp_distinct_orthogonal h hh j k hj hk hjk f g hf hg,
    fun j _ => projOp_zero_bandOp_orthogonal h hh j f g hg,
    fun x _ => projOp_telescope h J f hf x,
    fun j => projOp_energy_contraction h hh j f hf, bandOp_energy_sum_le h J hh f hf⟩
  exact fun j k x hx => projOp_nested h hh j k f hf x hx

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
