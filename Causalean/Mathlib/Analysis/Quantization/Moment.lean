module
public import Causalean.Mathlib.Analysis.Quantization.Core
public import Mathlib.MeasureTheory.Integral.Layercake

/-! Absolute-deviation moment inequalities for bounded sets: the tail bound holds for
every subset of a bounded interval, the layer-cake and moment bounds for measurable
subsets. These lemmas do not require a cell to be connected. -/

public section

open MeasureTheory Set
open scoped BigOperators

namespace Causalean.Mathlib.Analysis.Quantization

/-- For a bounded cell, the mass at distance at least `r` from a
point is at least the cell's mass minus the length `2*r` of the central band.
The cell may be disconnected and need not be measurable, in which case its mass is its
Lebesgue outer measure, and the point may lie outside it. -/
theorem cell_tail_lower (a b z r : ℝ)
    (hr : 0 ≤ r) (E : Set ℝ)
    (hsub : E ⊆ Set.Icc a b) :
    volume.real E ≤ 2 * r +
      volume.real (E ∩ {x : ℝ | r ≤ |x - z|}) := by
  -- Split E into the central band and its complement. Bound the band by
  -- volume (Icc (z-r) (z+r)) = 2*r, including its null endpoints.
  let C : Set ℝ := Set.Ioo (z - r) (z + r)
  have hfinite : volume E ≠ ⊤ := by
    exact (measure_lt_top_of_subset hsub (measure_Icc_lt_top (μ := volume)).ne).ne
  have hcover : E ⊆ (E ∩ C) ∪ (E ∩ {x : ℝ | r ≤ |x - z|}) := by
    intro x hx
    by_cases h : |x - z| < r
    · left
      refine ⟨hx, ?_⟩
      have h' := (abs_lt.mp h)
      change z - r < x ∧ x < z + r
      constructor <;> linarith [h'.1, h'.2]
    · right
      exact ⟨hx, le_of_not_gt h⟩
  have hcentral : volume.real (E ∩ C) ≤ 2 * r := by
    calc
      volume.real (E ∩ C) ≤ volume.real C :=
        measureReal_mono inter_subset_right measure_Ioo_lt_top.ne
      _ = 2 * r := by
        dsimp [C]
        rw [Real.volume_real_Ioo_of_le (by linarith)]
        ring
  calc
    volume.real E ≤ volume.real ((E ∩ C) ∪ (E ∩ {x : ℝ | r ≤ |x - z|})) :=
      measureReal_mono hcover (by finiteness)
    _ ≤ volume.real (E ∩ C) + volume.real (E ∩ {x : ℝ | r ≤ |x - z|}) :=
      measureReal_union_le _ _
    _ ≤ 2 * r + volume.real (E ∩ {x : ℝ | r ≤ |x - z|}) := by linarith

/-- Integrating the distance tails up to half the cell's mass gives a lower
bound for the absolute-deviation integral over any bounded measurable cell. -/
theorem measurable_cell_truncated_layer_cake (a b z : ℝ) (hab : a ≤ b)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Set.Icc a b) :
    (∫ r in (0 : ℝ)..volume.real E / 2, (volume.real E - 2 * r)) ≤
      ∫ x in E, |x - z| := by
  -- Use cell_tail_lower at each nonnegative radius, integrate
  -- in r, then Tonelli/layer cake to compare truncated tails with distance.
  let μ : Measure ℝ := volume.restrict E
  let m := volume.real E
  let M := |a - z| + |b - z| + (b - a) + 1
  have hEfin : volume E ≠ ⊤ :=
    (measure_lt_top_of_subset hsub (measure_Icc_lt_top (μ := volume)).ne).ne
  have hm : 0 ≤ m := measureReal_nonneg
  have hmM : m / 2 ≤ M := by
    have hmass : m ≤ b - a := by
      calc
        m ≤ volume.real (Icc a b) :=
          measureReal_mono hsub (measure_Icc_lt_top (μ := volume)).ne
        _ = b - a := Real.volume_real_Icc_of_le hab
    dsimp [M]
    have := abs_nonneg (a - z)
    have := abs_nonneg (b - z)
    linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ x ∈ E, |x - z| ≤ M := by
    intro x hx
    have hxa : a ≤ x := (hsub hx).1
    have hxb : x ≤ b := (hsub hx).2
    have hxle : x - z ≤ M := by
      have := le_abs_self (b - z)
      dsimp [M]
      have := abs_nonneg (a - z)
      linarith
    have hxge : -(M) ≤ x - z := by
      have := neg_le_of_abs_le (le_refl |a - z|)
      have := neg_abs_le (a - z)
      dsimp [M]
      have := abs_nonneg (b - z)
      linarith
    exact abs_le.mpr ⟨hxge, hxle⟩
  have hfint : Integrable (fun x : ℝ => |x - z|) μ := by
    change IntegrableOn (fun x : ℝ => |x - z|) E volume
    exact ((by fun_prop : Continuous (fun x : ℝ => |x - z|)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set hsub
  have hcake := hfint.integral_eq_integral_Ioc_meas_le
    (μ := μ) (M := M) (Filter.Eventually.of_forall (fun x => abs_nonneg _))
    (by filter_upwards [self_mem_ae_restrict hE] with x hx; exact hbound x hx)
  let T : ℝ → ℝ := fun r => volume.real (E ∩ {x : ℝ | r ≤ |x - z|})
  have hanti : Antitone T := by
    intro s t hst
    exact measureReal_mono (by
      intro x hx
      exact ⟨hx.1, hst.trans hx.2⟩)
      (measure_ne_top_of_subset inter_subset_left hEfin)
  have hTmeas : Measurable T := hanti.measurable
  have hTnonneg (r : ℝ) : 0 ≤ T r := measureReal_nonneg
  have hTle (r : ℝ) : T r ≤ m :=
    measureReal_mono inter_subset_left hEfin
  have hTint : IntegrableOn T (Ioc 0 M) volume := by
    apply Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hTmeas.aestronglyMeasurable
    filter_upwards with r
    rw [Real.norm_eq_abs, abs_of_nonneg (hTnonneg r)]
    exact hTle r
  have hcake' : (∫ r in Ioc 0 M, T r) = ∫ x in E, |x - z| := by
    rw [hcake]
    congr 1
    funext r
    change T r = (volume.restrict E).real {x : ℝ | r ≤ |x - z|}
    rw [measureReal_restrict_apply (measurableSet_le measurable_const (by fun_prop))]
    exact congrArg volume.real (Set.inter_comm _ _)
  have hlinearInt : IntegrableOn (fun r : ℝ => m - 2 * r) (Ioc 0 (m / 2)) volume := by
    exact ((by fun_prop : Continuous (fun r : ℝ => m - 2 * r)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  have hTintSmall : IntegrableOn T (Ioc 0 (m / 2)) volume :=
    hTint.mono_set (fun r hr => ⟨hr.1, hr.2.trans hmM⟩)
  have hpoint : ∀ r ∈ Ioc 0 (m / 2), m - 2 * r ≤ T r := by
    intro r hr
    have h := cell_tail_lower a b z r hr.1.le E hsub
    dsimp [m, T]
    linarith
  have hfirst : (∫ r in Ioc 0 (m / 2), m - 2 * r) ≤
      (∫ r in Ioc 0 (m / 2), T r) :=
    setIntegral_mono_on hlinearInt hTintSmall measurableSet_Ioc hpoint
  have hsecond : (∫ r in Ioc 0 (m / 2), T r) ≤ (∫ r in Ioc 0 M, T r) := by
    apply setIntegral_mono_set hTint
    · exact Filter.Eventually.of_forall (fun r => hTnonneg r)
    · exact Filter.Eventually.of_forall (fun r hr => ⟨hr.1, hr.2.trans hmM⟩)
  rw [intervalIntegral.integral_of_le (by linarith : (0 : ℝ) ≤ m / 2)]
  exact hfirst.trans (hsecond.trans_eq hcake')

/-- For [ordered interval endpoints](hyp:a,b,hab), [a reproduction
point](hyp:z), and [a measurable subset of that interval](hyp:E,hE,hsub),
[absolute-deviation loss is at least one quarter of squared Lebesgue mass](goal). -/
theorem measurable_cell_moment (a b z : ℝ) (hab : a ≤ b)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Set.Icc a b) :
    volume.real E ^ 2 / 4 ≤ ∫ x in E, |x - z| := by
  -- Evaluate the affine left-hand integral in
  -- measurable_cell_truncated_layer_cake; it equals volume.real E ^ 2 / 4.
  have heval : (∫ r in (0 : ℝ)..volume.real E / 2,
      (volume.real E - 2 * r)) = volume.real E ^ 2 / 4 := by
    have hmul : (∫ r in (0 : ℝ)..volume.real E / 2, 2 * r) =
        2 * (volume.real E / 2) ^ 2 / 2 := by
      rw [intervalIntegral.integral_const_mul, integral_id]
      ring
    rw [intervalIntegral.integral_sub]
    · rw [intervalIntegral.integral_const, hmul]
      ring
    · exact intervalIntegrable_const
    · exact (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [← heval]
  exact measurable_cell_truncated_layer_cake a b z hab E hE hsub

/-- For a finite family of nonnegative constant weights, separate reproduction
points cannot improve the common measurable cell's quarter-square bound. -/
theorem weighted_measurable_cell_moment (a b : ℝ) (hab : a ≤ b)
    (E : Set ℝ) (hE : MeasurableSet E) (hsub : E ⊆ Set.Icc a b)
    (S : ℕ) (γ : Fin S → ℝ) (hγ : ∀ s, 0 ≤ γ s)
    (z : Fin S → ℝ) :
    ((∑ s : Fin S, γ s) * volume.real E ^ 2 / 4) ≤
      ∑ s : Fin S, γ s * (∫ x in E, |x - z s|) := by
  -- Sum measurable_cell_moment after multiplying by each nonnegative γ s.
  calc
    ((∑ s : Fin S, γ s) * volume.real E ^ 2 / 4) =
        ∑ s : Fin S, γ s * (volume.real E ^ 2 / 4) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ ∑ s : Fin S, γ s * (∫ x in E, |x - z s|) := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_of_nonneg_left
        (measurable_cell_moment a b (z s) hab E hE hsub) (hγ s)

/-- The midpoint realizes the exact quarter-square absolute-deviation
integral on a nondegenerate or degenerate closed interval. -/
theorem interval_midpoint_moment (a b : ℝ) (hab : a ≤ b) :
    (∫ x in a..b, |x - (a + b) / 2|) = (b - a) ^ 2 / 4 := by
  -- Split the interval at its midpoint and integrate the two affine branches.
  let m := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : (∫ x in a..m, |x - m|) = (m - a) ^ 2 / 2 := by
    have heq : (∫ x in a..m, |x - m|) = ∫ x in a..m, m - x := by
      apply intervalIntegral.integral_congr
      intro x hx
      change |x - m| = m - x
      rw [abs_of_nonpos (sub_nonpos.mpr ((Set.uIcc_of_le ham ▸ hx).2))]
      ring
    rw [heq, intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const, integral_id]
      ring
    · exact intervalIntegrable_const
    · exact Continuous.intervalIntegrable continuous_id a m
  have hright : (∫ x in m..b, |x - m|) = (b - m) ^ 2 / 2 := by
    have heq : (∫ x in m..b, |x - m|) = ∫ x in m..b, x - m := by
      apply intervalIntegral.integral_congr
      intro x hx
      change |x - m| = x - m
      rw [abs_of_nonneg (sub_nonneg.mpr ((Set.uIcc_of_le hmb ▸ hx).1))]
    rw [heq, intervalIntegral.integral_sub]
    · simp only [intervalIntegral.integral_const, integral_id]
      ring
    · exact Continuous.intervalIntegrable continuous_id m b
    · exact intervalIntegrable_const
  have hc : Continuous (fun x : ℝ => |x - m|) := by fun_prop
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) a m) (hc.intervalIntegrable (μ := volume) m b)
  change (∫ x in a..b, |x - m|) = (b - a) ^ 2 / 4
  rw [← hsplit, hleft, hright]
  dsimp [m]
  ring

end Causalean.Mathlib.Analysis.Quantization
