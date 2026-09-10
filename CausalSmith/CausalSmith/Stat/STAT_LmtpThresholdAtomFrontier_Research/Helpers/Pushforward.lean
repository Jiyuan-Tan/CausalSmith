/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Basic
import Causalean.Stat.PolynomialTail.PowerIntegral

/-!
# Clamp pushforward and exposure support

The conditional treatment law is represented by its density against Lebesgue
measure. The clamp pushforward is stated as an equality of measures, including
the Dirac mass at the threshold and the two-sided atom-mass bound.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- Conditional natural-treatment measure in stratum `x`. -/
def conditionalTreatmentMeasure (P : ClampLaw J) (x : Fin J) : Measure ℝ :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).withDensity
    (fun a => ENNReal.ofReal (P.pi x a))

/-- Pointwise support expressed by positivity of every open neighborhood. -/
def IsConditionalSupportPoint (μ : Measure ℝ) (a : ℝ) : Prop :=
  ∀ U : Set ℝ, IsOpen U → a ∈ U → 0 < μ U

/-- The threshold clamp produces the retained continuous law plus a Dirac atom,
whose mass is sandwiched by the integrated polynomial envelope. The result uses [the `hmodel` condition](hyp:hmodel), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: prop:pushforward-setup
lemma clamp_pushforward_decomposition
    (P : ClampLaw J) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (x : Fin J) (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    (conditionalTreatmentMeasure P x).map (clampPolicy delta) =
        (conditionalTreatmentMeasure P x).restrict (Set.Ioc delta 1) +
          ENNReal.ofReal (atomMass P x delta) • Measure.dirac delta ∧
      cminus * delta ^ (kappa + 1) / (kappa + 1) ≤ atomMass P x delta ∧
      atomMass P x delta ≤ cplus * delta ^ (kappa + 1) / (kappa + 1) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  have hdelta0 : 0 ≤ delta := hdelta.1
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hdeltaBar_lt.le
  let μ : Measure ℝ := conditionalTreatmentMeasure P x
  have hclamp : Measurable (clampPolicy delta) := by
    exact measurable_id.max measurable_const
  have hmap : μ.map (clampPolicy delta) =
      μ.restrict (Set.Ioi delta) + μ (Set.Iic delta) • Measure.dirac delta := by
    calc
      μ.map (clampPolicy delta) =
          (μ.restrict (Set.Iic delta) + μ.restrict (Set.Iic delta)ᶜ).map
            (clampPolicy delta) := by
              rw [Measure.restrict_add_restrict_compl measurableSet_Iic]
      _ = (μ.restrict (Set.Iic delta)).map (clampPolicy delta) +
          (μ.restrict (Set.Iic delta)ᶜ).map (clampPolicy delta) := by
            rw [Measure.map_add _ _ hclamp]
      _ = (μ.restrict (Set.Iic delta)).map (fun _ => delta) +
          (μ.restrict (Set.Iic delta)ᶜ).map id := by
        congr 1
        · apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Iic] with a ha
          have ha' : a ≤ delta := ha
          exact max_eq_right ha'
        · apply Measure.map_congr
          filter_upwards [ae_restrict_mem measurableSet_Iic.compl] with a ha
          have hda : delta < a := by simpa using ha
          simpa [clampPolicy, max_eq_left hda.le]
      _ = μ (Set.Iic delta) • Measure.dirac delta + μ.restrict (Set.Ioi delta) := by
        simp [Measure.map_const]
      _ = μ.restrict (Set.Ioi delta) + μ (Set.Iic delta) • Measure.dirac delta :=
        add_comm _ _
  have hupper : μ.restrict (Set.Ioi delta) = μ.restrict (Set.Ioc delta 1) := by
    dsimp [μ, conditionalTreatmentMeasure]
    rw [restrict_withDensity measurableSet_Ioi, restrict_withDensity measurableSet_Ioc,
      Measure.restrict_restrict measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioc]
    congr 2
    ext a
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨hda, ha0, ha1⟩
      exact ⟨⟨hda, ha1⟩, ha0, ha1⟩
    · rintro ⟨⟨hda, ha1⟩, ha0, _⟩
      exact ⟨hda, ha0, ha1⟩
  have hpiInt : Integrable (P.pi x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
    · exact (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
        (hmodel.condDensity.1 x)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Icc,
        hmodel.condDensity.2.1 x, hmodel.thinning x] with a ha hnon hthin
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      calc
        P.pi x a ≤ cplus * a ^ kappa := hthin.2
        _ ≤ cplus * 1 := by
          have hcplus : 0 ≤ cplus := by linarith
          gcongr
          exact Real.rpow_le_one ha.1 ha.2 hkappa
        _ = cplus := mul_one _
  have hmass : μ (Set.Iic delta) = ENNReal.ofReal (atomMass P x delta) := by
    dsimp [μ, conditionalTreatmentMeasure]
    rw [withDensity_apply _ measurableSet_Iic,
      ← ofReal_integral_eq_lintegral_ofReal hpiInt.restrict]
    · congr 2
      rw [Measure.restrict_restrict measurableSet_Iic]
      congr 1
      ext a
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨had, ha0, ha1⟩
        exact ⟨ha0, had⟩
      · rintro ⟨ha0, had⟩
        exact ⟨had, ha0, had.trans hdelta1⟩
    · exact (hmodel.condDensity.2.1 x).filter_mono ae_restrict_le
  refine ⟨?_, ?_⟩
  · simpa [μ, hupper, hmass] using hmap
  have hsubset : Set.Icc (0 : ℝ) delta ⊆ Set.Icc (0 : ℝ) 1 := by
    intro a ha
    exact ⟨ha.1, ha.2.trans hdelta1⟩
  have hpiDelta : IntegrableOn (P.pi x) (Set.Icc (0 : ℝ) delta) volume :=
    hpiInt.mono_measure (Measure.restrict_mono_set volume hsubset)
  have hpowInt : IntegrableOn (fun a : ℝ => a ^ kappa) (Set.Icc 0 delta) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hdelta0]
    exact intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)
  have hthinDelta := (hmodel.thinning x).filter_mono
    (ae_mono (Measure.restrict_mono_set volume hsubset))
  have hpowEval : (∫ a in Set.Icc (0 : ℝ) delta, a ^ kappa) =
      delta ^ (kappa + 1) / (kappa + 1) := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hdelta0,
      integral_rpow (Or.inl (by linarith : -1 < kappa))]
    rw [Real.zero_rpow (by linarith : kappa + 1 ≠ 0), sub_zero]
  constructor
  · rw [atomMass]
    calc
      cminus * delta ^ (kappa + 1) / (kappa + 1) =
          cminus * ∫ a in Set.Icc (0 : ℝ) delta, a ^ kappa := by rw [hpowEval]; ring
      _ = ∫ a in Set.Icc (0 : ℝ) delta, cminus * a ^ kappa :=
        by rw [integral_const_mul]
      _ ≤ ∫ a in Set.Icc (0 : ℝ) delta, P.pi x a :=
        integral_mono_ae (hpowInt.const_mul cminus) hpiDelta
          (hthinDelta.mono fun _ ha => ha.1)
  · rw [atomMass]
    calc
      (∫ a in Set.Icc (0 : ℝ) delta, P.pi x a) ≤
          ∫ a in Set.Icc (0 : ℝ) delta, cplus * a ^ kappa :=
        integral_mono_ae hpiDelta (hpowInt.const_mul cplus)
          (hthinDelta.mono fun _ ha => ha.2)
      _ = cplus * ∫ a in Set.Icc (0 : ℝ) delta, a ^ kappa := by rw [integral_const_mul]
      _ = cplus * delta ^ (kappa + 1) / (kappa + 1) := by rw [hpowEval]; ring

/-- Every clamped treatment value is almost surely a support point of the
natural conditional treatment law, including the identity case at zero. The result uses [the `hmodel` condition](hyp:hmodel), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
-- @node: prop:policy-support
lemma clamp_policy_support
    (P : ClampLaw J) (beta kappa L cminus cplus pmin deltaBar alpha : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hreg : RegimeConstants J beta kappa L cminus cplus pmin deltaBar alpha)
    (x : Fin J) (delta : ℝ) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    ∀ᵐ a ∂conditionalTreatmentMeasure P x,
      IsConditionalSupportPoint (conditionalTreatmentMeasure P x)
        (clampPolicy delta a) := by
  rcases hreg with ⟨hJ, hbeta, hkappa, hL, hcminus, hcm, hcp, hpmin,
    hpminJ, hdeltaBar_pos, hdeltaBar_lt, halpha, halpha_lt⟩
  let μ₀ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let f : ℝ → ENNReal := fun a => ENNReal.ofReal (P.pi x a)
  have hf : AEMeasurable f μ₀ := by
    apply AEMeasurable.ennreal_ofReal
    exact aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
      (hmodel.condDensity.1 x)
  have hμ : conditionalTreatmentMeasure P x = μ₀.withDensity f := rfl
  have hinterior : ∀ᵐ a ∂μ₀, a ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [ae_iff, Measure.restrict_apply₀]
    · have hset : {a : ℝ | ¬a ∈ Set.Ioo (0 : ℝ) 1} ∩ Set.Icc 0 1 = {0, 1} := by
        ext a
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Ioo, Set.mem_Icc,
          Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hnot, ha0, ha1⟩
          by_cases hzero : a = 0
          · exact Or.inl hzero
          · right
            have hpos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hzero)
            exact le_antisymm ha1 (le_of_not_gt fun hlt => hnot ⟨hpos, hlt⟩)
        · rintro (rfl | rfl) <;> simp
      rw [hset]
      rw [Set.insert_eq]
      exact measure_union_null Real.volume_singleton Real.volume_singleton
    · exact measurableSet_Ioo.compl.nullMeasurableSet
  have hfpos : ∀ᵐ a ∂μ₀, f a ≠ 0 := by
    filter_upwards [hinterior, hmodel.thinning x] with a ha hthin
    rw [ne_eq, ENNReal.ofReal_eq_zero]
    exact not_le.mpr (lt_of_lt_of_le
      (mul_pos hcminus (Real.rpow_pos_of_pos ha.1 kappa)) hthin.1)
  have hsourceInterior : ∀ᵐ a ∂conditionalTreatmentMeasure P x,
      a ∈ Set.Ioo (0 : ℝ) 1 := by
    rw [hμ]
    exact (withDensity_absolutelyContinuous μ₀ f).ae_le hinterior
  filter_upwards [hsourceInterior] with a ha
  have hdelta01 : delta ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨hdelta.1, le_trans hdelta.2 (le_of_lt hdeltaBar_lt)⟩
  have hy : clampPolicy delta a ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_of_lt_of_le ha.1 (le_max_left _ _)
    · exact max_lt ha.2 (lt_of_le_of_lt hdelta.2 hdeltaBar_lt)
  intro U hU hyU
  have hμ₀U : 0 < μ₀ U := by
    rcases (Metric.isOpen_iff.mp hU) _ hyU with ⟨ε, hε, hball⟩
    let r := min ε (min (clampPolicy delta a) (1 - clampPolicy delta a))
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min hε (lt_min hy.1 (sub_pos.mpr hy.2))
    have hsub : Metric.ball (clampPolicy delta a) r ⊆ U ∩ Set.Icc (0 : ℝ) 1 := by
      intro z hz
      have hz' : |z - clampPolicy delta a| < r := by
        simpa [Real.dist_eq] using hz
      constructor
      · exact hball (Metric.ball_subset_ball (min_le_left _ _) hz)
      · constructor
        · have : -(clampPolicy delta a) < z - clampPolicy delta a :=
            lt_of_le_of_lt (neg_le_neg (min_le_right ε _ |>.trans (min_le_left _ _)))
              (abs_lt.mp hz').1
          linarith
        · have : z - clampPolicy delta a < 1 - clampPolicy delta a :=
            lt_of_lt_of_le (abs_lt.mp hz').2
              (min_le_right ε _ |>.trans (min_le_right _ _))
          linarith
    rw [Measure.restrict_apply hU.measurableSet]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.ball_eq_Ioo, Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith
  rw [hμ]
  rw [pos_iff_ne_zero] at hμ₀U ⊢
  intro hzero
  apply hμ₀U
  rw [← (withDensity_apply_eq_zero' hf).mp hzero]
  apply measure_congr
  filter_upwards [hfpos] with z hz
  apply propext
  constructor
  · exact fun hzU => ⟨hz, hzU⟩
  · exact fun hzU => hzU.2

end


end CausalSmith.Stat.LmtpThresholdAtomFrontier
