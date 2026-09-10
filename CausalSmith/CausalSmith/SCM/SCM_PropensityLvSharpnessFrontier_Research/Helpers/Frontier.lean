import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Legality
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.CapBridge

/-! # Analytic helpers for the generator frontier -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set

/-- Subtracting a linear function through `(1,0)` does not change the
calibrated radius.  For the specified model objects, [the stated conditions](hyp:he), [the stated mathematical relationship holds](goal).
-/
-- @node: divRadius_sub_affine
lemma divRadius_sub_affine (f : ℝ → ℝ) (b e : ℝ) (he : e ≠ 0) :
    divRadius (fun t => f t - b * (t - 1)) e = divRadius f e := by
  unfold divRadius
  field_simp
  ring

/-- Subtracting a linear function through `(1,0)` does not change an
integrable divergence between probability laws.  For the specified model objects, [the stated conditions](hyp:hAC,hfint), [the stated mathematical relationship holds](goal).
-/
-- @node: fDiv_sub_affine
lemma fDiv_sub_affine {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (b : ℝ) (P Q : Measure Y)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hAC : P.AbsolutelyContinuous Q)
    (hfint : Integrable (fun x => f ((P.rnDeriv Q x).toReal)) Q) :
    fDiv (fun t => f t - b * (t - 1)) P Q = fDiv f P Q := by
  have hrint : Integrable (fun x => (P.rnDeriv Q x).toReal) Q :=
    Measure.integrable_toReal_rnDeriv
  have haff : Integrable (fun x => b * ((P.rnDeriv Q x).toReal - 1)) Q := by
    fun_prop
  have hgint : Integrable
      (fun x => f ((P.rnDeriv Q x).toReal) -
        b * ((P.rnDeriv Q x).toReal - 1)) Q := hfint.sub haff
  rw [fDiv, if_pos hgint, fDiv, if_pos hfint]
  congr 1
  rw [integral_sub hfint haff]
  have hr_one : ∫ x, (P.rnDeriv Q x).toReal ∂Q = 1 := by
    rw [Measure.integral_toReal_rnDeriv hAC]
    simp
  have haff_zero : ∫ x, b * ((P.rnDeriv Q x).toReal - 1) ∂Q = 0 := by
    rw [integral_const_mul, integral_sub hrint (integrable_const 1), hr_one]
    simp
  rw [haff_zero, sub_zero]

/-- A finite upper bound on the extended divergence forces the defining
integrand to be integrable.  For the specified model objects, [the stated conditions](hyp:h), [the stated mathematical relationship holds](goal).
-/
-- @node: integrable_of_fDiv_le_real
lemma integrable_of_fDiv_le_real {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (P Q : Measure Y) (C : ℝ)
    (h : fDiv f P Q ≤ (C : EReal)) :
    Integrable (fun x => f ((P.rnDeriv Q x).toReal)) Q := by
  by_contra hnot
  rw [fDiv, if_neg hnot] at h
  exact (not_le_of_gt (EReal.coe_lt_top C)) h

/-- Membership in the hinge frontier makes the one-sided divergence ball
exactly the propensity mixture class.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: hinge_oneSided_exactAt
lemma hinge_oneSided_exactAt {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : f ∈ hingeClassSet (1 / e)) :
    jkBallOneSidedSet f e P = mixtureClassOneSidedSet e P := by
  apply Set.Subset.antisymm
  · intro Q hQ
    letI : IsProbabilityMeasure Q := hQ.candidate_probability
    obtain ⟨b, hzero, hstrict⟩ := hf.affine_hinge
    let g : ℝ → ℝ := fun t => f t - b * (t - 1)
    have he : e ≠ 0 := ne_of_gt hPos.1
    have hfint := integrable_of_fDiv_le_real f P Q (divRadius f e) hQ.divergence_le
    have hdiv_eq : fDiv g P Q = fDiv f P Q :=
      fDiv_sub_affine f b P Q hQ.forward_support hfint
    have hrad : divRadius g e = 0 := by
      rw [divRadius_sub_affine f b e he]
      unfold divRadius
      have hc0 : 0 ≤ 1 / e := (one_div_pos.mpr hPos.1).le
      rw [show f (1 / e) = b * (1 / e - 1) by
        linarith [hzero (1 / e) hc0 (le_refl _)],
        show f 0 = b * (0 - 1) by linarith [hzero 0 (le_refl 0) hc0]]
      field_simp
      ring
    have hgint : Integrable (fun x => g ((P.rnDeriv Q x).toReal)) Q := by
      have hrint : Integrable (fun x => (P.rnDeriv Q x).toReal) Q :=
        Measure.integrable_toReal_rnDeriv
      exact hfint.sub (by fun_prop)
    have hg_nonneg : 0 ≤ᵐ[Q] fun x => g ((P.rnDeriv Q x).toReal) := by
      filter_upwards [] with x
      have hr0 : 0 ≤ (P.rnDeriv Q x).toReal := ENNReal.toReal_nonneg
      by_cases hr : (P.rnDeriv Q x).toReal ≤ 1 / e
      · exact le_of_eq (hzero _ hr0 hr).symm
      · exact (hstrict _ (lt_of_not_ge hr)).le
    have hgintegral_le : (∫ x, g ((P.rnDeriv Q x).toReal) ∂Q) ≤ 0 := by
      have : fDiv g P Q ≤ (0 : EReal) := by
        calc
          fDiv g P Q = fDiv f P Q := hdiv_eq
          _ ≤ (divRadius f e : EReal) := hQ.divergence_le
          _ = (divRadius g e : EReal) := by
            rw [divRadius_sub_affine f b e he]
          _ = 0 := by rw [hrad]; rfl
      rw [fDiv, if_pos hgint] at this
      exact_mod_cast this
    have hgintegral_zero : ∫ x, g ((P.rnDeriv Q x).toReal) ∂Q = 0 :=
      le_antisymm hgintegral_le (integral_nonneg_of_ae hg_nonneg)
    have hgzero : (fun x => g ((P.rnDeriv Q x).toReal)) =ᵐ[Q] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hg_nonneg hgint).1 hgintegral_zero
    have hcap : ∀ᵐ x ∂Q, (P.rnDeriv Q x).toReal ≤ 1 / e := by
      filter_upwards [hgzero] with x hx
      by_contra hr
      have hp := hstrict _ (lt_of_not_ge hr)
      simpa [g, hx] using hp
    exact (mixture_oneSided_iff_cap e P Q hPos).2
      ⟨inferInstance, hQ.forward_support, hcap⟩
  · exact mixtureOneSided_subset_jkBall f e P hPos hf.admissible

/-- Membership in the hinge frontier makes the mutual-support divergence ball
exactly the dominated-residual mixture class.  For the specified model objects, [the stated conditions](hyp:hPos,hf), [the stated mathematical relationship holds](goal).
-/
-- @node: hinge_mutual_exactAt
lemma hinge_mutual_exactAt {Y : Type*} [MeasurableSpace Y]
    (f : ℝ → ℝ) (e : ℝ) (P : Measure Y) [IsProbabilityMeasure P]
    (hPos : StrictPositivity e) (hf : f ∈ hingeClassSet (1 / e)) :
    jkBallSet f e P = mixtureClassSet e P := by
  apply Set.Subset.antisymm
  · intro Q hQ
    have hone : Q ∈ jkBallOneSidedSet f e P :=
      { positivity := hQ.positivity
        admissible := hQ.admissible
        observed_probability := hQ.observed_probability
        candidate_probability := hQ.candidate_probability
        forward_support := hQ.mutual_ac.2
        divergence_le := hQ.divergence_le }
    have hm := hone
    rw [hinge_oneSided_exactAt f e P hPos hf] at hm
    exact (mixture_reverse_support e P Q hPos).2 ⟨hm, hQ.mutual_ac.1⟩
  · exact mixture_subset_jkBall f e P hPos hf.admissible

end CausalSmith.SCM.PropensityLvSharpnessFrontier
