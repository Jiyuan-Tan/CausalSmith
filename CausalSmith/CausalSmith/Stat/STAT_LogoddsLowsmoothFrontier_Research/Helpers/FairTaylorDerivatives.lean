module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.FairNumeratorSmoothness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Actual derivatives in the fair Taylor extension

The two amplitude derivatives and subsequent effect derivative are jointly
smooth on full neighborhoods of the calibration box. These are derivatives
of the actual numerator, with all four parameters allowed to vary.
-/
public section
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Taking a scalar partial derivative preserves joint smoothness of a smooth family.](goal) Under [the stated assumptions](hyp:f,g,x,hg). Under [the stated assumptions](hyp:hf). -/
-- @node: calibration_partial_contDiffAt
lemma calibration_partial_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ → ℝ) (g : E → ℝ) (x : E)
    (hf : ContDiffAt ℝ ⊤ (Function.uncurry f) (x, g x))
    (hg : ContDiffAt ℝ ⊤ g x) :
    ContDiffAt ℝ ⊤ (fun w => deriv (f w) (g w)) x := by
  exact (hf.fderiv hg (by simp)).clm_apply contDiffAt_const

/-- [The first amplitude derivative is smooth jointly in effect, amplitude, center and position.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_amplitude_deriv_contDiffAt
lemma fairNumerator_amplitude_deriv_contDiffAt (v : Fin 4 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100)
    (hξ : v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ =>
      deriv (fun D => fairNumerator (w 0) D (w 2) (w 3)) (w 1)) v := by
  apply calibration_partial_contDiffAt
  · exact (fairNumerator_contDiffAt ![v 0,v 1,v 2,v 3] ht hδ hξ).comp (v, v 1)
      (show ContDiffAt ℝ ⊤ (fun z : (Fin 4 → ℝ) × ℝ =>
        ![z.1 0,z.2,z.1 2,z.1 3]) (v,v 1) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  · fun_prop

/-- [Both amplitude derivatives remain jointly smooth, including at zero amplitude.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_second_amplitude_deriv_contDiffAt
lemma fairNumerator_second_amplitude_deriv_contDiffAt (v : Fin 4 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100)
    (hξ : v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ =>
      deriv (deriv (fun D => fairNumerator (w 0) D (w 2) (w 3))) (w 1)) v := by
  apply calibration_partial_contDiffAt
  · exact (fairNumerator_amplitude_deriv_contDiffAt ![v 0,v 1,v 2,v 3] ht hδ hξ).comp (v, v 1)
      (show ContDiffAt ℝ ⊤ (fun z : (Fin 4 → ℝ) × ℝ =>
        ![z.1 0,z.2,z.1 2,z.1 3]) (v,v 1) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  · fun_prop

/-- [The actual third derivative appearing inside the double Taylor integral is jointly smooth.](goal) Under [the stated assumptions](hyp:hδ). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairNumerator_taylor_deriv_contDiffAt
lemma fairNumerator_taylor_deriv_contDiffAt (v : Fin 4 → ℝ)
    (ht : v 0 ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |v 1| ≤ 1 / 100)
    (hξ : v 2 ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    ContDiffAt ℝ ⊤ (fun w : Fin 4 → ℝ =>
      deriv (fun T => deriv (deriv (fun D => fairNumerator T D (w 2) (w 3)))
        (w 1)) (w 0)) v := by
  apply calibration_partial_contDiffAt
  · exact (fairNumerator_second_amplitude_deriv_contDiffAt ![v 0,v 1,v 2,v 3] ht hδ hξ).comp (v, v 0)
      (show ContDiffAt ℝ ⊤ (fun z : (Fin 4 → ℝ) × ℝ =>
        ![z.2,z.1 1,z.1 2,z.1 3]) (v,v 0) by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop)
  · fun_prop

/-- [A segment from zero to a signed amplitude stays inside its absolute-value bound.](goal) Under [the stated assumptions](hyp:x,hx). -/
-- @node: calibration_segment_abs_le
lemma calibration_segment_abs_le (a x : ℝ) (hx : x ∈ Set.uIcc 0 a) : |x| ≤ |a| := by
  rcases le_total 0 a with ha | ha
  · rw [Set.uIcc_of_le ha] at hx
    rw [abs_of_nonneg hx.1, abs_of_nonneg ha]
    exact hx.2
  · rw [Set.uIcc_of_ge ha] at hx
    rw [abs_of_nonpos hx.2, abs_of_nonpos ha]
    exact neg_le_neg hx.1

/-- [Multiplication by a unit-interval coordinate lies on the signed amplitude segment. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hs). -/
-- @node: calibration_unit_mul_mem_segment
lemma calibration_unit_mul_mem_segment (a s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    s*a ∈ Set.uIcc 0 a := by
  rcases le_total 0 a with ha | ha
  · rw [Set.uIcc_of_le ha]
    exact ⟨mul_nonneg hs.1 ha, by nlinarith [hs.2]⟩
  · rw [Set.uIcc_of_ge ha]
    exact ⟨by nlinarith [hs.2], mul_nonpos_of_nonneg_of_nonpos hs.1 ha⟩

/-- Rescaling the fundamental theorem works for signed increments and at zero. Under the stated assumptions. [The stated hypotheses](hyp:hf) hold, and [the stated conclusion follows](goal). -/
-- @node: calibration_scaled_fundamental_theorem
lemma calibration_scaled_fundamental_theorem (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ Set.uIcc 0 a, ContDiffAt ℝ ⊤ f x) :
    a * (∫ s in (0 : ℝ)..1, deriv f (s*a)) = f a - f 0 := by
  have hmem (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) 1) : s*a ∈ Set.uIcc 0 a := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    rcases le_total 0 a with ha | ha
    · rw [Set.uIcc_of_le ha]
      exact ⟨mul_nonneg hs.1 ha, by nlinarith [hs.2]⟩
    · rw [Set.uIcc_of_ge ha]
      exact ⟨by nlinarith [hs.2], mul_nonpos_of_nonneg_of_nonpos hs.1 ha⟩
  have hc : ContinuousOn (fun s => a * deriv f (s*a)) (Set.uIcc 0 1) := by
    intro s hs
    exact (continuousAt_const.mul
      (((hf _ (hmem s hs)).derivWithin (m := ⊤) (by simp)).continuousAt.comp (f := fun s : ℝ => s*a)
        (by fun_prop : ContinuousAt (fun s : ℝ => s*a) s))).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s => f (s*a)) (f' := fun s => a * deriv f (s*a))
    (fun s hs => by
      simpa only [Function.comp_def, id_eq, one_mul, mul_one, mul_comm] using
        (((hf _ (hmem s hs)).differentiableAt (by simp)).hasDerivAt).comp s
          ((hasDerivAt_id s).mul_const a))
    hc.intervalIntegrable
  simpa only [intervalIntegral.integral_const_mul, one_mul, zero_mul] using h

/-- [The second integral Taylor identity uses the actual zero value and slope;
it remains valid for both signs of the amplitude. [the documented result](goal) Under [the stated assumptions](hyp:hf,hzero,hslope). -/
-- @node: calibration_scaled_second_taylor
lemma calibration_scaled_second_taylor (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x ∈ Set.uIcc 0 a, ContDiffAt ℝ ∞ f x)
    (hzero : f 0 = 0) (hslope : deriv f 0 = 0) :
    a^2 * (∫ v in (0 : ℝ)..1, (1-v)*deriv (deriv f) (v*a)) = f a := by
  have hmem (v : ℝ) (hv : v ∈ Set.uIcc (0 : ℝ) 1) : v*a ∈ Set.uIcc 0 a := by
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    rcases le_total 0 a with ha | ha
    · rw [Set.uIcc_of_le ha]
      exact ⟨mul_nonneg hv.1 ha, by nlinarith [hv.2]⟩
    · rw [Set.uIcc_of_ge ha]
      exact ⟨by nlinarith [hv.2], mul_nonpos_of_nonneg_of_nonpos hv.1 ha⟩
  have hc : ContinuousOn (fun v => a^2*((1-v)*deriv (deriv f) (v*a)))
      (Set.uIcc 0 1) := by
    intro v hv
    have hd := ((hf _ (hmem v hv)).derivWithin (m := ∞) (by simp)).derivWithin (m := ∞) (by simp)
    exact (continuousAt_const.mul ((by fun_prop : ContinuousAt (fun v : ℝ => 1-v) v).mul
      (hd.continuousAt.comp (f := fun v : ℝ => v*a) (by fun_prop : ContinuousAt (fun v : ℝ => v*a) v)))).continuousWithinAt
  have hg (v : ℝ) (hv : v ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun v => (1-v)*deriv f (v*a)*a + f (v*a))
        (a^2*((1-v)*deriv (deriv f) (v*a))) v := by
    have harg := (hasDerivAt_id v).mul_const a
    have h0 := ((hf _ (hmem v hv)).differentiableAt (by simp)).hasDerivAt
    have h1 := (((hf _ (hmem v hv)).derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
    convert ((((hasDerivAt_const v (1 : ℝ)).sub (hasDerivAt_id v)).mul
      (h1.comp v harg)).mul_const a).add (h0.comp v harg) using 1 <;> first | rfl | (dsimp; ring)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hc.intervalIntegrable
  simpa only [intervalIntegral.integral_const_mul, one_mul, zero_mul, sub_self,
    zero_mul, zero_add, hzero, hslope, mul_zero, add_zero, sub_zero] using h

/-- [Two integral Taylor identities recover the actual numerator on both axes,
without division by either parameter. [the documented result](goal) Under [the stated assumptions](hyp:ht,hδ,hξ). -/
-- @node: fairEquation_mul_parameters
lemma fairEquation_mul_parameters (t δ ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) :
    t*δ^2*fairEquation t δ ξ u = fairNumerator t δ ξ u := by
  have hT (T : ℝ) (hT : T ∈ Set.uIcc 0 t) : T ∈ Set.Icc (0 : ℝ) (1/4) := by
    rw [Set.uIcc_of_le ht.1] at hT
    exact ⟨hT.1,hT.2.trans ht.2⟩
  have hD (D : ℝ) (hD : D ∈ Set.uIcc 0 δ) : |D| ≤ 1/100 :=
    (calibration_segment_abs_le δ D hD).trans hδ
  let F : ℝ → ℝ → ℝ := fun s v =>
    (1-v)*deriv (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*δ)) (s*t)
  have hc : ContinuousOn F.uncurry (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    have hp : ContDiffAt ℝ ⊤ (fun z : ℝ × ℝ => ![z.1*t,z.2*δ,ξ,u]) z := by
      apply contDiffAt_pi.mpr
      intro i
      fin_cases i <;> dsimp <;> fun_prop
    have hf := (fairNumerator_taylor_deriv_contDiffAt ![z.1*t,z.2*δ,ξ,u]
      (hT _ (calibration_unit_mul_mem_segment t z.1 hz.1))
      (hD _ (calibration_unit_mul_mem_segment δ z.2 hz.2)) hξ).comp z hp
    exact ((by fun_prop : ContinuousAt (fun z : ℝ × ℝ => 1-z.2) z).mul
      hf.continuousAt).continuousWithinAt
  have hInt : IntegrableOn F.uncurry
      (Set.uIoc (0 : ℝ) 1 ×ˢ Set.uIoc (0 : ℝ) 1) := by
    apply (hc.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self
  have hswap := intervalIntegral_intervalIntegral_swap hInt
  have hInner (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
      t * (∫ s in (0 : ℝ)..1,
        deriv (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*δ)) (s*t)) =
      deriv (deriv (fun D => fairNumerator t D ξ u)) (v*δ) := by
    have h := calibration_scaled_fundamental_theorem
      (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*δ)) t (by
        intro T hTT
        have hp : ContDiffAt ℝ ⊤ (fun T : ℝ => ![T,v*δ,ξ,u]) T := by
          apply contDiffAt_pi.mpr
          intro i
          fin_cases i <;> dsimp <;> fun_prop
        exact (fairNumerator_second_amplitude_deriv_contDiffAt ![T,v*δ,ξ,u]
          (hT T hTT) (hD _ (calibration_unit_mul_mem_segment δ v hv)) hξ).comp T hp)
    simpa only [fairNumerator_second_deriv_zero_effect, sub_zero] using h
  have hTaylor := calibration_scaled_second_taylor
    (fun D => fairNumerator t D ξ u) δ (by
      intro D hDD
      have hp : ContDiffAt ℝ ⊤ (fun D : ℝ => ![t,D,ξ,u]) D := by
        apply contDiffAt_pi.mpr
        intro i
        fin_cases i <;> dsimp <;> fun_prop
      exact ((fairNumerator_contDiffAt ![t,D,ξ,u] ht (hD D hDD) hξ).comp D hp).of_le le_top)
    (fairNumerator_zero_amplitude t ξ u) (fairNumerator_deriv_zero_amplitude t ξ u)
  calc
    t*δ^2*fairEquation t δ ξ u =
        δ^2 * (∫ v in (0 : ℝ)..1, (1-v)*(t * (∫ s in (0 : ℝ)..1,
          deriv (fun T => deriv (deriv (fun D => fairNumerator T D ξ u)) (v*δ)) (s*t)))) := by
      change t*δ^2*(∫ s in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, F s v) = _
      rw [hswap, show t*δ^2 = δ^2*t by ring, mul_assoc,
        ← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp [F]
      rw [intervalIntegral.integral_const_mul]
      ring
    _ = δ^2 * (∫ v in (0 : ℝ)..1,
        (1-v)*deriv (deriv (fun D => fairNumerator t D ξ u)) (v*δ)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro v hv
      dsimp only
      rw [hInner v (by simpa using hv)]
    _ = fairNumerator t δ ξ u := hTaylor

/-- [Away from the axes, the double-integral extension is exactly the normalized numerator.](goal) Under [the stated assumptions](hyp:hδ,hne). Under [the stated assumptions](hyp:ht,hξ). -/
-- @node: fairEquation_eq_div
lemma fairEquation_eq_div (t δ ξ u : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (1 / 4)) (hδ : |δ| ≤ 1 / 100)
    (hξ : ξ ∈ Set.Icc (3 / 10 : ℝ) (1 / 2)) (hne : t*δ ≠ 0) :
    fairEquation t δ ξ u = fairNumerator t δ ξ u / (t*δ^2) := by
  have htne : t ≠ 0 := (mul_ne_zero_iff.mp hne).1
  have hδne : δ ≠ 0 := (mul_ne_zero_iff.mp hne).2
  apply (eq_div_iff (mul_ne_zero htne (pow_ne_zero 2 hδne))).mpr
  simpa only [mul_comm] using fairEquation_mul_parameters t δ ξ u ht hδ hξ

end CausalSmith.Stat.LogoddsLowsmoothFrontier
