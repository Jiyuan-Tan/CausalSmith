module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Laplace
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # Moments of the centered Laplace law

This file records the first two moments and square integrability of the
positive-scale centered Laplace distribution used by the comparator release.
-/

public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory Set Causalean.Stat.Privacy
open scoped ENNReal

private lemma laplacePDF_nonneg' {b : ℝ} (hb : 0 < b) (x : ℝ) :
    0 ≤ laplacePDF b x := by
  unfold laplacePDF
  exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) hb.le))
    (Real.exp_pos _).le

private lemma integrable_sq_mul_laplacePDF (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2 * laplacePDF b x) := by
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x ^ 2 * Real.exp (-x / b))
  have hright : IntegrableOn f (Ioi 0) := by
    have hbase := Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num)
    have hscaled : IntegrableOn
        (fun x : ℝ => Real.exp (-(1 / b * x)) *
          (1 / b * x) ^ ((3 : ℝ) - 1)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff
        (fun x : ℝ => Real.exp (-x) * x ^ ((3 : ℝ) - 1)) 0
        (one_div_pos.mpr hb)).mpr (by simpa using hbase)
    have hs : IntegrableOn
        (fun x : ℝ => (2 * b)⁻¹ *
          (b ^ 2 * (Real.exp (-(1 / b * x)) *
            (1 / b * x) ^ ((3 : ℝ) - 1)))) (Ioi 0) :=
      (hscaled.const_mul (b ^ 2)).const_mul (2 * b)⁻¹
    refine hs.congr_fun ?_ measurableSet_Ioi
    intro x hx
    simp only [f]
    simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
    field_simp [hb.ne']
  have hright_abs : IntegrableOn (fun x => f |x|) (Ioi 0) := by
    refine hright.congr_fun ?_ measurableSet_Ioi
    intro x hx
    change f x = f |x|
    rw [abs_of_pos (by simpa only [mem_Ioi] using hx)]
  have hall : Integrable (fun x => f |x|) := by
    have hleft : IntegrableOn (fun x => f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x :=
        (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright_abs
    rw [← integrableOn_univ]
    simpa only [Iic_union_Ioi] using hleft.union hright_abs
  refine hall.congr (ae_of_all _ fun x => ?_)
  simp only [f, laplacePDF]
  rw [sq_abs]
  ring

/-- A centered Laplace draw has mean zero at every positive scale. For [the displayed inputs and conditions](hyp:b,hb), [the stated result](goal) follows. -/
lemma laplaceMeasure_integral_id (b : ℝ) (hb : 0 < b) :
    ∫ x, x ∂(laplaceMeasure b) = 0 := by
  rw [laplaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplacePDF b).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (laplacePDF_nonneg' hb _), smul_eq_mul]
  have hneg := integral_neg_eq_self (μ := (volume : Measure ℝ))
    (f := fun x : ℝ => laplacePDF b x * x)
  have hodd : (fun x : ℝ => laplacePDF b (-x) * (-x)) =
      fun x => -(laplacePDF b x * x) := by
    funext x
    simp [laplacePDF]
  rw [hodd, integral_neg] at hneg
  linarith

/-- The square of a centered Laplace draw is integrable at every positive scale. For [the displayed inputs and conditions](hyp:b,hb), [the stated result](goal) follows. -/
lemma laplaceMeasure_integrable_sq (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : ℝ => x ^ 2) (laplaceMeasure b) := by
  rw [laplaceMeasure,
    integrable_withDensity_iff_integrable_smul' (measurable_laplacePDF b).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simpa only [ENNReal.toReal_ofReal (laplacePDF_nonneg' hb _), smul_eq_mul, mul_comm] using
    integrable_sq_mul_laplacePDF b hb

/-- The second moment of a centered Laplace draw with positive scale `b` is `2 * b ^ 2`. For [the displayed inputs and conditions](hyp:b,hb), [the stated result](goal) follows. -/
lemma laplaceMeasure_integral_sq (b : ℝ) (hb : 0 < b) :
    ∫ x, x ^ 2 ∂(laplaceMeasure b) = 2 * b ^ 2 := by
  rw [laplaceMeasure, integral_withDensity_eq_integral_toReal_smul
    (measurable_laplacePDF b).ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (laplacePDF_nonneg' hb _), smul_eq_mul]
  let f : ℝ → ℝ := fun x => (2 * b)⁻¹ * (x ^ 2 * Real.exp (-x / b))
  rw [show (fun x : ℝ => laplacePDF b x * x ^ 2) = fun x => f |x| by
    funext x
    simp only [f, laplacePDF, sq_abs]
    ring, integral_comp_abs]
  have hplain : (∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-x / b)) = 2 * b ^ 3 := by
    calc
      _ = ∫ x in Ioi (0 : ℝ), x ^ ((3 : ℝ) - 1) *
          Real.exp (-((1 / b) * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        simp only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two]
        rw [show -x / b = -(1 / b * x) by ring]
      _ = (1 / (1 / b)) ^ (3 : ℝ) * Real.Gamma (3 : ℝ) :=
        Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) (one_div_pos.mpr hb)
      _ = 2 * b ^ 3 := by
        rw [show Real.Gamma (3 : ℝ) = 2 by norm_num]
        field_simp [hb.ne']
        exact Real.rpow_natCast b 3
  rw [show (∫ x in Ioi (0 : ℝ), f x) = (2 * b)⁻¹ * (2 * b ^ 3) by
    rw [integral_const_mul, hplain]]
  field_simp [hb.ne']

/-- Each comparator noise coordinate is almost everywhere measurable. This is recovered from its stipulated nonzero Laplace pushforward law, so no separate measurability assumption is needed. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hnoise,hp,hε), [the aemeasurable](goal).

Under the stated assumptions, the aemeasurable. -/
lemma ComparatorNoise.aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {W Y L : ℕ → Ω → ℝ} {p ε : ℝ}
    (hnoise : ComparatorNoise μ W Y L p ε)
    (hp : InteriorAssignment p) (hε : 0 < ε) (i : ℕ) :
    AEMeasurable (L i) μ := by
  have hsens : 0 < sensitivity p := by
    unfold sensitivity controlProb
    exact add_pos (inv_pos.mpr hp.1) (inv_pos.mpr (sub_pos.mpr hp.2))
  have hscale : 0 < sensitivity p / ε := div_pos hsens hε
  letI : IsProbabilityMeasure (comparatorNoiseLaw p ε) := by
    unfold comparatorNoiseLaw
    exact laplaceMeasure_isProbabilityMeasure _ hscale
  have hne : μ.map (L i) ≠ 0 := by
    rw [hnoise.2.1 i]
    exact IsProbabilityMeasure.ne_zero _
  exact AEMeasurable.of_map_ne_zero hne

/-- Every noisy release coordinate is almost everywhere measurable under the binary-trial and comparator-noise assumptions. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. Under [the stated assumptions](hyp:hmodel,hnoise,hε), [the oa Release Value aemeasurable](goal).

Under the stated assumptions, the oa Release Value aemeasurable. -/
lemma oaReleaseValue_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y0 Y1 W Y L : ℕ → Ω → ℝ} {θ : TrialParameter} {p ε : ℝ}
    (hmodel : LatentBinaryTrialRepresentation μ Y0 Y1 W Y p θ)
    (hnoise : ComparatorNoise μ W Y L p ε) (hε : 0 < ε) (i : ℕ) :
    AEMeasurable (oaReleaseValue W Y L p i) μ := by
  have hY0 : Measurable (Y0 i) := (hmodel.measurable i).fst
  have hY1 : Measurable (Y1 i) := (hmodel.measurable i).snd.fst
  have hW : Measurable (W i) := (hmodel.measurable i).snd.snd
  have hY : Measurable (Y i) := by
    have hformula : Y i = fun ω =>
        W i ω * Y1 i ω + (1 - W i ω) * Y0 i ω := by
      funext ω
      exact hmodel.consistent i ω
    rw [hformula]
    exact (hW.mul hY1).add ((measurable_const.sub hW).mul hY0)
  have hL : AEMeasurable (L i) μ :=
    hnoise.aemeasurable hmodel.assignmentInterior hε i
  unfold oaReleaseValue
  exact (((hW.mul hY).div_const p).sub
    ((measurable_const.sub hW).mul hY |>.div_const (controlProb p))).aemeasurable.add hL

end CausalSmith.Stat.LdpAteEfficiencySurface
