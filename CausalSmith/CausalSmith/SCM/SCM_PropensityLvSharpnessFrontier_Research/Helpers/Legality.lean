import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge

/-! # Divergence-ball legality helpers -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Every propensity mixture obeys the calibrated divergence constraint.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: mixtureOneSided_subset_jkBall
lemma mixtureOneSided_subset_jkBall {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    mixtureClassOneSidedSet e P ⊆ jkBallOneSidedSet f e P := by
  intro Q hQ
  have hcap := (mixture_oneSided_iff_cap e P Q hPos).1 hQ
  let _ : IsProbabilityMeasure Q := hcap.1
  let c : ℝ := 1 / e
  have hc : 0 < c := by exact one_div_pos.mpr hPos.1
  have hr_nonneg : ∀ x, 0 ≤ (P.rnDeriv Q x).toReal := fun x => ENNReal.toReal_nonneg
  have hr_cap : ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ c := hcap.2.2
  have hfIcc : ContinuousOn f (Set.Icc 0 c) :=
    hf.1.mono (fun _ ht => ht.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hfIcc
  have hmeas : AEStronglyMeasurable
      (fun x => f ((P.rnDeriv Q x).toReal)) Q := by
    let g : ℝ → ℝ := fun t => f (max t 0)
    have hg : Continuous g := by
      change Continuous (f ∘ fun t : ℝ => max t 0)
      exact hf.1.comp_continuous (continuous_id.max continuous_const)
        (fun t => le_max_right t 0)
    have hrm : AEStronglyMeasurable
        (fun x => (P.rnDeriv Q x).toReal) Q :=
      (ENNReal.measurable_toReal.comp (Measure.measurable_rnDeriv P Q)).aestronglyMeasurable
    apply (hg.comp_aestronglyMeasurable hrm).congr
    filter_upwards with x
    simp [g, max_eq_left (hr_nonneg x)]
  have hfint : Integrable (fun x => f ((P.rnDeriv Q x).toReal)) Q := by
    apply Integrable.of_bound hmeas C
    filter_upwards [hr_cap] with x hx
    exact hC _ ⟨hr_nonneg x, hx⟩
  have hrint : Integrable (fun x => (P.rnDeriv Q x).toReal) Q :=
    Measure.integrable_toReal_rnDeriv
  have hchord : ∀ᵐ x ∂Q,
      f ((P.rnDeriv Q x).toReal) ≤
        (1 - (P.rnDeriv Q x).toReal / c) * f 0 +
          ((P.rnDeriv Q x).toReal / c) * f c := by
    filter_upwards [hr_cap] with x hx
    let r := (P.rnDeriv Q x).toReal
    have hr0 : 0 ≤ r := hr_nonneg x
    have ha : 0 ≤ 1 - r / c := by
      rw [sub_nonneg]
      exact (div_le_one hc).2 hx
    have hb : 0 ≤ r / c := div_nonneg hr0 hc.le
    have hab : (1 - r / c) + r / c = 1 := by ring
    have h := hf.2.1.2 (show (0 : ℝ) ∈ Set.Ici 0 by simp)
      (show c ∈ Set.Ici 0 by exact hc.le) ha hb hab
    have harg : (1 - r / c) * 0 + (r / c) * c = r := by
      field_simp [ne_of_gt hc] <;> ring
    rw [show (1 - r / c) • (0 : ℝ) + (r / c) • c = r by
      simpa only [smul_eq_mul] using harg] at h
    simpa only [smul_eq_mul] using h
  have hmajor_int : Integrable (fun x =>
      (1 - (P.rnDeriv Q x).toReal / c) * f 0 +
        ((P.rnDeriv Q x).toReal / c) * f c) Q := by
    fun_prop
  have hint_le := integral_mono_ae hfint hmajor_int hchord
  have hr_one : ∫ x, (P.rnDeriv Q x).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hcap.2.1]
    simp
  have hreal : (∫ x, f ((P.rnDeriv Q x).toReal) ∂Q) ≤ divRadius f e := by
    have hcalc : (∫ x,
        (1 - (P.rnDeriv Q x).toReal / c) * f 0 +
          ((P.rnDeriv Q x).toReal / c) * f c ∂Q) =
        (1 - 1 / c) * f 0 + (1 / c) * f c := by
      calc
        _ = ∫ x, f 0 + (P.rnDeriv Q x).toReal * ((f c - f 0) / c) ∂Q := by
          apply integral_congr_ae
          filter_upwards with x
          field_simp [ne_of_gt hc]
          <;> ring
        _ = (1 : ℝ) * f 0 + 1 * ((f c - f 0) / c) := by
          rw [integral_add]
          · rw [integral_const, integral_mul_const, hr_one]
            simp
          · fun_prop
          · exact hrint.mul_const _
        _ = (1 - 1 / c) * f 0 + (1 / c) * f c := by
          field_simp [ne_of_gt hc]
          <;> ring
    rw [hcalc] at hint_le
    rw [divRadius]
    dsimp [c] at hint_le
    have heinv : 1 / (1 / e) = e := by
      field_simp [ne_of_gt hPos.1]
    rw [heinv] at hint_le
    linarith
  change JKBallOneSided f e P Q
  refine
    { positivity := hPos
      admissible := hf
      observed_probability := inferInstance
      candidate_probability := inferInstance
      forward_support := hcap.2.1
      divergence_le := ?_ }
  rw [fDiv, if_pos hfint]
  exact_mod_cast hreal

/-- Every dominated-residual propensity mixture obeys the mutual-support
calibrated divergence constraint.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: mixture_subset_jkBall
lemma mixture_subset_jkBall {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    mixtureClassSet e P ⊆ jkBallSet f e P := by
  intro Q hQ
  have hsplit := (mixture_reverse_support e P Q hPos).1 hQ
  have hBallOne := mixtureOneSided_subset_jkBall f e P hPos hf hsplit.1
  exact
    { positivity := hBallOne.positivity
      admissible := hBallOne.admissible
      observed_probability := hBallOne.observed_probability
      candidate_probability := hBallOne.candidate_probability
      mutual_ac := ⟨hsplit.2, hBallOne.forward_support⟩
      divergence_le := hBallOne.divergence_le }

/-- Intersecting a one-sided divergence ball with the propensity-mixture class
recovers the mixture class.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: lawfulCorrectionOneSided_eq_mixtureClassOneSided
lemma lawfulCorrectionOneSided_eq_mixtureClassOneSided
    {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    lawfulCorrectionOneSidedSet f e P = mixtureClassOneSidedSet e P := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · intro Q hQ
    exact ⟨mixtureOneSided_subset_jkBall f e P hPos hf hQ, hQ⟩

/-- Intersecting a mutual-support divergence ball with the dominated-residual
mixture class recovers the mixture class.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: lawfulCorrection_eq_mixtureClass
lemma lawfulCorrection_eq_mixtureClass {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : AdmissibleGenerator f) :
    lawfulCorrectionSet f e P = mixtureClassSet e P := by
  apply Set.Subset.antisymm
  · exact Set.inter_subset_right
  · intro Q hQ
    exact ⟨mixture_subset_jkBall f e P hPos hf hQ, hQ⟩

end CausalSmith.SCM.PropensityLvSharpnessFrontier
