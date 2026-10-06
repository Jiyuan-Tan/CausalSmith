module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.UpperPeeling
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Layercake

/-! # Integrating the selector tail

Roadmap step (6): integration above a positive cutoff turns the quadratic
and cubic probability tails into an expected-loss bound.
-/

public section

set_option linter.style.whitespace false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory Set

/-- The two polynomial tails have finite integrals above a positive cutoff. -/
-- @node: upperExpectation_tail_integral
lemma upperExpectation_tail_integral (A B z : ℝ) (hz : 0 < z) :
    (∫ t : ℝ in Ioi z, A / t^2 + B / t^3) = A/z + B/(2*z^2) := by
  have h2 : IntegrableOn (fun t : ℝ => t ^ (-2:ℝ)) (Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hz
  have h3 : IntegrableOn (fun t : ℝ => t ^ (-3:ℝ)) (Ioi z) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hz
  have heq (t : ℝ) : A / t^2 + B / t^3 =
      A * t ^ (-2:ℝ) + B * t ^ (-3:ℝ) := by
    simp [div_eq_mul_inv]
  simp_rw [heq]
  rw [integral_add (h2.const_mul A) (h3.const_mul B), integral_const_mul,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hz,
    integral_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hz]
  norm_num [Real.rpow_neg, Real.rpow_natCast]
  rw [Real.rpow_neg_one]
  ring

/-- Layer cake splits a bounded nonnegative loss at the cutoff. Integrating
its two tail bounds proves the first inequality in roadmap step (6). -/
-- @node: upperExpectation_bounded_loss
lemma upperExpectation_bounded_loss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ)
    (hi : Integrable T μ) (h0 : ∀ᵐ w ∂μ, 0 ≤ T w)
    (cap : ℝ) (hcap : ∀ᵐ w ∂μ, T w ≤ cap)
    (A B z : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hz : 0 < z)
    (htail : ∀ t ≥ z, μ.real {w | t ≤ T w} ≤ A/t^2 + B/t^3) :
    (∫ w, T w ∂μ) ≤ z + A/z + B/(2*z^2) := by
  by_cases hcz : cap ≤ z
  · have hb := integral_mono_ae hi (integrable_const z) (hcap.mono fun w hw => hw.trans hcz)
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hb
    have h1 : 0 ≤ A/z := by positivity
    have h2 : 0 ≤ B/(2*z^2) := by positivity
    linarith
  have hzc : z ≤ cap := (lt_of_not_ge hcz).le
  let F : ℝ → ℝ := fun t => μ.real {w | t ≤ T w}
  have hFm : Measurable F := by
    apply Measurable.ennreal_toReal
    exact Antitone.measurable (fun s t hst => measure_mono (fun w hw => hst.trans hw))
  have hF1 (t : ℝ) : F t ≤ 1 := by
    exact (measureReal_mono (Set.subset_univ _)).trans_eq (by simp)
  have hFi : IntegrableOn F (Ioc 0 cap) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
    exact hF1 t
  have hFil : IntegrableOn F (Ioc 0 z) := hFi.mono_set (Ioc_subset_Ioc_right hzc)
  have hFir : IntegrableOn F (Ioc z cap) := hFi.mono_set (Ioc_subset_Ioc_left hz.le)
  have hsplit : (∫ t in Ioc 0 cap, F t) =
      (∫ t in Ioc 0 z, F t) + ∫ t in Ioc z cap, F t := by
    rw [← Ioc_union_Ioc_eq_Ioc hz.le hzc]
    exact setIntegral_union (by apply Set.disjoint_left.mpr; intro t ht hs; exact (not_lt_of_ge ht.2) hs.1)
      measurableSet_Ioc hFil hFir
  have hlow : (∫ t in Ioc 0 z, F t) ≤ z := by
    have hb := integral_mono hFil (integrable_const (1:ℝ)) (fun t => hF1 t)
    simpa [Real.volume_Ioc, hz.le] using hb
  let G : ℝ → ℝ := fun t => A / t^2 + B / t^3
  have hGi : IntegrableOn G (Ioi z) := by
    have h2 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hz).const_mul A
    have h3 := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3:ℝ) < -1) hz).const_mul B
    have heq : G = (fun t : ℝ => A * t ^ (-2:ℝ)) +
        (fun t : ℝ => B * t ^ (-3:ℝ)) := by
      ext t
      simp [G, div_eq_mul_inv]
    rw [heq]
    exact h2.add h3
  have hhigh : (∫ t in Ioc z cap, F t) ≤ A/z + B/(2*z^2) := by
    calc
      _ ≤ ∫ t in Ioc z cap, G t := setIntegral_mono_on hFir
        (hGi.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc
        (fun t ht => htail t ht.1.le)
      _ ≤ ∫ t in Ioi z, G t := setIntegral_mono_set hGi
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact add_nonneg (div_nonneg hA (sq_nonneg t))
              (div_nonneg hB (pow_nonneg (hz.trans ht).le 3)))
        (Filter.Eventually.of_forall fun t ht => Ioc_subset_Ioi_self ht)
      _ = _ := upperExpectation_tail_integral A B z hz
  rw [hi.integral_eq_integral_Ioc_meas_le h0 hcap]
  change (∫ t in Ioc 0 cap, F t) ≤ _
  rw [hsplit]
  linarith

/-- The paper's cutoff absorbs both integrated tails into the bias and
inverse effective sample size, with an explicit constant. -/
-- @node: upperExpectation_cutoff_algebra
lemma upperExpectation_cutoff_algebra (H C v : ℝ)
    (hH : 0 ≤ H) (hC : 0 ≤ C) (hv : 0 < v) :
    (16*H + v⁻¹) + (C/v^2)/(16*H + v⁻¹) +
      (C/v^3)/(2*(16*H + v⁻¹)^2) ≤ (16+2*C)*(H + v⁻¹) := by
  let z := 16*H + v⁻¹
  have hz : 0 < z := by dsimp [z]; positivity
  have hvz : v⁻¹ ≤ z := by dsimp [z]; linarith
  have hi : z⁻¹ ≤ v := by
    have hb := one_div_le_one_div_of_le (by positivity : 0 < v⁻¹) hvz
    simpa using hb
  have hi2 : (z⁻¹)^2 ≤ v^2 := pow_le_pow_left₀ (by positivity) hi 2
  have hquad : (C/v^2)/z ≤ C/v := by
    calc
      _ = (C/v^2)*z⁻¹ := by ring
      _ ≤ (C/v^2)*v := mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := by field_simp
  have hcubic : (C/v^3)/(2*z^2) ≤ C/(2*v) := by
    calc
      _ = (C/(2*v^3))*(z⁻¹)^2 := by ring
      _ ≤ (C/(2*v^3))*v^2 := mul_le_mul_of_nonneg_left hi2 (by positivity)
      _ = _ := by field_simp
  have hc : 0 ≤ C/v := by positivity
  have hch : 0 ≤ C*H := mul_nonneg hC hH
  change z + (C/v^2)/z + (C/v^3)/(2*z^2) ≤ _
  dsimp [z] at *
  simp only [div_eq_mul_inv, mul_inv_rev, inv_pow] at *
  norm_num at hcubic ⊢
  nlinarith [inv_pos.mpr hv]

/-- The integrated tail yields the bias-plus-sampling remainder from
roadmap step (6), before applying the schedule. -/
-- @node: upperExpectation_bias_sampling
lemma upperExpectation_bias_sampling {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → ℝ)
    (hi : Integrable T μ) (h0 : ∀ᵐ w ∂μ, 0 ≤ T w)
    (hcap : ∀ᵐ w ∂μ, T w ≤ 3)
    (H C v : ℝ) (hH : 0 ≤ H) (hC : 0 ≤ C) (hv : 0 < v)
    (htail : ∀ t > 0, 16*H ≤ t →
      μ.real {w | t ≤ T w} ≤ C*(1/(v^2*t^2) + 1/(v^3*t^3))) :
    (∫ w, T w ∂μ) ≤ (16+2*C)*(H + v⁻¹) := by
  have hz : 0 < 16*H + v⁻¹ := by positivity
  have hb := upperExpectation_bounded_loss μ T hi h0 3 hcap
    (C/v^2) (C/v^3) (16*H + v⁻¹) (by positivity) (by positivity) hz (by
      intro t ht
      have hht : 16*H ≤ t := by
        have : 0 < v⁻¹ := by positivity
        linarith
      convert htail t (hz.trans_le ht) hht using 1 <;> ring)
  exact hb.trans (upperExpectation_cutoff_algebra H C v hH hC hv)

/-- Applying the proved selector tail bound to layer cake supplies the
expected regularized-loss bound, conditional on the remaining moment inputs. -/
-- @node: upperExpectation_selector_loss
lemma upperExpectation_selector_loss (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hP : LawClass α γ θ n P e)
    (a C : ℝ) (hn : 0 < n) (ha : 0 < a ∧ a ≤ 1/4) (hC : 0 ≤ C)
    (hT : Integrable (fun d => regularizedLoss P a (sortedSelector a e d))
      (sampleLaw P n))
    (hi : ∀ z > 0, Integrable (fun d : Fin n → Observation =>
      (localizedProcess P a z d)^4) (sampleLaw P n))
    (hmoment : ∀ z > 0, (∫ d, (localizedProcess P a z d)^4 ∂sampleLaw P n) ≤
      C*(z^2/((n:ℝ)^2*a^2) + z/((n:ℝ)^3*a^3))) :
    (∫ d, regularizedLoss P a (sortedSelector a e d) ∂sampleLaw P n) ≤
      (16+65536*C)*(biasFunctional P a + ((n:ℝ)*a)⁻¹) := by
  haveI := sampleLaw_isProbability P n hP.wf
  have hb : 0 ≤ biasFunctional P a := by
    unfold biasFunctional
    apply add_nonneg measureReal_nonneg
    apply integral_nonneg
    intro x
    dsimp only
    simp only [Pi.zero_apply]
    split_ifs with hx
    · have hmag := hx.2.1
      have hoff := hx.2.2
      simp only [mul_one]
      linarith
    · simp
  have hbounds := fun (d : Fin n → Observation) => upperPeeling_regularizedLoss_bounds α γ θ n P e hP
    a ha.1 _ (firstScannedMinimizer_mem_thresholdClass a e d)
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn
  convert upperExpectation_bias_sampling (sampleLaw P n) _ hT
    (Filter.Eventually.of_forall fun d => (hbounds d).1)
    (Filter.Eventually.of_forall fun d => (hbounds d).2)
    (biasFunctional P a) (32768*C) ((n:ℝ)*a) hb (by positivity)
    (mul_pos hnR ha.1) (by
      intro z hz hzb
      have htail := upperPeeling_selector_tail_probability α γ θ n P e hP a z C
        hn ha hz hC hzb
        (fun k => hi _ (by positivity))
        (fun k => hmoment _ (by positivity))
      simpa only [mul_pow] using htail) using 1 <;> ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
