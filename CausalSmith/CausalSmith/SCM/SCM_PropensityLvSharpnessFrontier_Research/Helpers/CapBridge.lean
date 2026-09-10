import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Divergence
import Mathlib.MeasureTheory.Measure.Sub

/-! # Mixture, measure-cap, and likelihood-ratio bridges -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- One-sided mixture membership is equivalent to the measure cap and its
Radon--Nikodym formulation under strict positivity.  For the specified model objects, [the stated conditions](hyp:hPos,hAC), [the stated mathematical relationship holds](goal).
-/
-- @node: cap_iff_measure_le
lemma cap_iff_measure_le {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hPos : StrictPositivity e) (hAC : P.AbsolutelyContinuous Q) :
    (∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e) ↔
      ENNReal.ofReal e • P ≤ Q := by
  have he_top : ENNReal.ofReal e ≠ ⊤ := ENNReal.ofReal_ne_top
  have heP_ac : (ENNReal.ofReal e • P).AbsolutelyContinuous Q := by
    intro s hs
    simp [Measure.smul_apply, hAC hs]
  rw [← Measure.rnDeriv_le_one_iff_le heP_ac]
  constructor
  · intro h
    filter_upwards [h, Measure.rnDeriv_smul_left_of_ne_top P Q he_top,
      P.rnDeriv_ne_top Q] with x hx hscale hfinite
    rw [hscale]
    simp only [Pi.one_apply]
    apply (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top he_top hfinite)
      ENNReal.one_ne_top).mp
    simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.1.le]
    exact (le_div_iff₀' hPos.1).1 hx
  · intro h
    filter_upwards [h, Measure.rnDeriv_smul_left_of_ne_top P Q he_top,
      P.rnDeriv_ne_top Q] with x hx hscale hfinite
    rw [hscale] at hx
    simp only [Pi.one_apply] at hx
    have hr := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top he_top hfinite)
      ENNReal.one_ne_top).2 hx
    simp only [ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal hPos.1.le] at hr
    exact (le_div_iff₀' hPos.1).2 hr

/-- Under strict positivity, arbitrary-residual mixtures are exactly
probability measures dominating the propensity-scaled observed law.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: mixture_oneSided_iff_measure_le
lemma mixture_oneSided_iff_measure_le {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) :
    Q ∈ mixtureClassOneSidedSet e P ↔
      IsProbabilityMeasure Q ∧ ENNReal.ofReal e • P ≤ Q := by
  constructor
  · intro h
    refine ⟨h.candidate_probability, ?_⟩
    obtain ⟨R, hR, hQ⟩ := h.representation (ne_of_lt hPos.2)
    rw [hQ]
    exact Measure.le_add_right le_rfl
  · rintro ⟨hQprob, hle⟩
    let R : Measure Y := (ENNReal.ofReal (1 - e))⁻¹ •
      (Q - ENNReal.ofReal e • P)
    have he_nonneg : 0 ≤ e := hPos.1.le
    have h1e_pos : 0 < ENNReal.ofReal (1 - e) :=
      ENNReal.ofReal_pos.mpr (sub_pos.mpr hPos.2)
    let _ : IsFiniteMeasure (ENNReal.ofReal e • P) :=
      ⟨by simp [Measure.smul_apply]⟩
    have hRprob : IsProbabilityMeasure R := by
      rw [isProbabilityMeasure_iff]
      simp only [R, Measure.smul_apply]
      rw [Measure.sub_apply MeasurableSet.univ hle]
      simp only [measure_univ, Measure.smul_apply, smul_eq_mul, mul_one]
      rw [ENNReal.ofReal_sub 1 he_nonneg]
      have hdiff_ne : 1 - ENNReal.ofReal e ≠ 0 := by
        exact (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hPos.2)).ne'
      simpa using ENNReal.inv_mul_cancel hdiff_ne (by simp)
    have hdecomp :
        Q = ENNReal.ofReal e • P + ENNReal.ofReal (1 - e) • R := by
      rw [show R = (ENNReal.ofReal (1 - e))⁻¹ •
        (Q - ENNReal.ofReal e • P) from rfl]
      symm
      ext s hs
      simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
      rw [← mul_assoc, ENNReal.mul_inv_cancel h1e_pos.ne' ENNReal.ofReal_ne_top,
        one_mul, add_comm]
      exact congrArg (fun m : Measure Y => m s) (Measure.sub_add_cancel_of_le hle)
    exact
      { positivity := Or.inr hPos
        observed_probability := inferInstance
        candidate_probability := hQprob
        representation := fun _ => ⟨R, hRprob, hdecomp⟩
        boundary := fun he => (ne_of_lt hPos.2 he).elim }

/-- For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal). -/
-- @node: mixture_oneSided_iff_cap
lemma mixture_oneSided_iff_cap {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) :
    Q ∈ mixtureClassOneSidedSet e P ↔
      IsProbabilityMeasure Q ∧ P.AbsolutelyContinuous Q ∧
      ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e := by
  rw [mixture_oneSided_iff_measure_le e P Q hPos]
  constructor
  · rintro ⟨hQprob, hle⟩
    let _ : IsProbabilityMeasure Q := hQprob
    have hAC : P.AbsolutelyContinuous Q :=
      (Measure.absolutelyContinuous_smul
        (ne_of_gt (ENNReal.ofReal_pos.mpr hPos.1))).trans
        (Measure.absolutelyContinuous_of_le hle)
    exact ⟨hQprob, hAC, (cap_iff_measure_le e P Q hPos hAC).2 hle⟩
  · rintro ⟨hQprob, hAC, hcap⟩
    let _ : IsProbabilityMeasure Q := hQprob
    exact ⟨hQprob, (cap_iff_measure_le e P Q hPos hAC).1 hcap⟩

/-- Adding reverse support turns the arbitrary residual into a residual
dominated by the observed law.  For the specified model objects, [the stated conditions](hyp:hPos), [the stated mathematical relationship holds](goal).
-/
-- @node: mixture_reverse_support
lemma mixture_reverse_support {Y : Type*} [MeasurableSpace Y]
    (e : ℝ) (P Q : Measure Y) (hPos : StrictPositivity e) :
    Q ∈ mixtureClassSet e P ↔
      Q ∈ mixtureClassOneSidedSet e P ∧ Q.AbsolutelyContinuous P := by
  constructor
  · intro h
    have he : e ≠ 1 := ne_of_lt hPos.2
    obtain ⟨R, hRprob, hRac, hQ⟩ := h.representation he
    constructor
    · exact
        { positivity := Or.inr hPos
          observed_probability := h.observed_probability
          candidate_probability := h.candidate_probability
          representation := fun _ => ⟨R, hRprob, hQ⟩
          boundary := fun he1 => (he he1).elim }
    · intro s hs
      rw [hQ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, hs, hRac hs]
      simp
  · rintro ⟨h, hQP⟩
    have he : e ≠ 1 := ne_of_lt hPos.2
    obtain ⟨R, hRprob, hQ⟩ := h.representation he
    have hRac : R.AbsolutelyContinuous P := by
      intro s hs
      have hQzero : Q s = 0 := hQP hs
      rw [hQ, Measure.add_apply, Measure.smul_apply, Measure.smul_apply] at hQzero
      have hcoef : ENNReal.ofReal (1 - e) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hPos.2))
      have hz : (ENNReal.ofReal e = 0 ∨ P s = 0) ∧ R s = 0 := by
        simpa [hcoef] using hQzero
      exact hz.2
    exact
      { positivity := Or.inr hPos
        observed_probability := h.observed_probability
        candidate_probability := h.candidate_probability
        representation := fun _ => ⟨R, hRprob, hRac, hQ⟩
        boundary := fun he1 => (he he1).elim }

end CausalSmith.SCM.PropensityLvSharpnessFrontier
