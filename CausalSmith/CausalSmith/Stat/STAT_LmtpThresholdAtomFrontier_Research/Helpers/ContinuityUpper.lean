/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.CausalBridgeMeasure
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperEmpirical

/-! # Elementary upper bounds for the continuity-only procedure -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory Set

noncomputable section

/-- The selected continuous conditional-mean version remains in the outcome
range throughout the threshold interval. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `ha` condition](hyp:ha). [This is the stated conclusion](goal).
-/
lemma contRegression_mem_Icc
    (P : ClampLaw J) (kappa cminus cplus pmin deltaBar : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (x : Fin J) (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) deltaBar) :
    contRegression P kappa cminus cplus pmin deltaBar hP x a ∈
      Set.Icc (0 : ℝ) 1 := by
  let m : Fin J → ℝ → ℝ :=
    contRegression P kappa cminus cplus pmin deltaBar hP
  let ce : ClampObs J → ℝ :=
    P.dataMeasure[(fun o : ClampObs J => o.Y) |
      MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance]
  have hspec := Classical.choose_spec hP.continuousVersion
  have hmcont : ∀ y, ContinuousOn (m y) (Set.Icc (0 : ℝ) deltaBar) := hspec.1
  have hver : ce =ᵐ[P.dataMeasure] fun o => m o.X o.A := hspec.2
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  have hYint : Integrable (fun o : ClampObs J => o.Y) P.dataMeasure := by
    refine Integrable.of_bound clampOutcome_measurable.aestronglyMeasurable 1 ?_
    filter_upwards [hP.outcomeSupport] with o ho
    rw [Real.norm_eq_abs, abs_of_nonneg ho.1]
    exact ho.2
  have hce0 : 0 ≤ᵐ[P.dataMeasure] ce :=
    MeasureTheory.condExp_nonneg (hP.outcomeSupport.mono fun _ ho => ho.1)
  have hce1 : ce ≤ᵐ[P.dataMeasure] fun _ => (1 : ℝ) := by
    have hmono := MeasureTheory.condExp_mono
      (m := MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance)
      hYint (integrable_const 1)
      (hP.outcomeSupport.mono fun _ ho => ho.2)
    rw [MeasureTheory.condExp_const clampDesign_measurable.comap_le (1 : ℝ)] at hmono
    exact hmono
  have hmrange : ∀ᵐ o ∂P.dataMeasure, m o.X o.A ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hver, hce0, hce1] with o he h0 h1
    rw [he] at h0 h1
    exact ⟨h0, h1⟩
  let mc : Fin J → ℝ → ℝ := fun y t => clampUnit (m y t)
  have hmccont : ∀ y, ContinuousOn (mc y) (Set.Icc (0 : ℝ) deltaBar) := by
    intro y
    unfold mc clampUnit
    fun_prop
  have hverc : ce =ᵐ[P.dataMeasure] fun o => mc o.X o.A := by
    filter_upwards [hver, hmrange] with o he hm
    rw [he]
    simp [mc, clampUnit, hm.1, hm.2]
  have heq := (cont_regression_extension_unique P kappa cminus cplus pmin deltaBar
    hP hreg m mc hmcont hmccont hver hverc x) ha
  change m x a ∈ Set.Icc (0 : ℝ) 1
  rw [heq]
  exact clampUnit_mem_Icc _

/-- The continuity-only functional is the expectation of the observed outcome
above the threshold and of the selected continuous regression below it. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contClampFunctional_integral_eq
    (P : ClampLaw J) (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    (∫ o, if delta < o.A then o.Y else
      contRegression P kappa cminus cplus pmin deltaBar hP o.X delta
      ∂P.dataMeasure) =
      contClampFunctional P kappa cminus cplus pmin deltaBar hP delta := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  let mu := contRegression P kappa cminus cplus pmin deltaBar hP
  let atomTerm : Fin J → ClampObs J → ℝ := fun x o =>
    if o.X = x ∧ o.A ≤ delta then mu x delta else 0
  rcases hreg with ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin,
    hpmin_le, hdeltaBar, hdeltaBar_one⟩
  have hreg' : ContDesignConstants J kappa cminus cplus pmin deltaBar :=
    ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin, hpmin_le,
      hdeltaBar, hdeltaBar_one⟩
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hdeltaBar_one.le
  have hatomInt (x : Fin J) : Integrable (atomTerm x) P.dataMeasure := by
    have hm : Measurable (atomTerm x) := by
      dsimp [atomTerm]
      have hX : Measurable (fun o : ClampObs J => o.X) :=
        measurable_fst.comp (Measurable.of_comap_le le_rfl)
      have hA : Measurable (fun o : ClampObs J => o.A) :=
        measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl))
      exact Measurable.ite
        ((measurableSet_eq_fun hX measurable_const).inter
          (measurableSet_le hA measurable_const)) measurable_const measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 ?_
    filter_upwards with o
    have hr := contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
      hP hreg' x delta hdelta
    dsimp [atomTerm]
    split_ifs
    · rw [abs_of_nonneg hr.1]
      exact hr.2
    · simp
  have hpoint : ∀ᵐ o ∂P.dataMeasure,
      (if delta < o.A then o.Y else mu o.X delta) =
        o.Y * Set.indicator {o : ClampObs J | delta < o.A}
          (fun _ => (1 : ℝ)) o + ∑ x : Fin J, atomTerm x o := by
    filter_upwards [hP.treatmentSupport] with o ho
    by_cases ha : delta < o.A
    · have hn (x : Fin J) : ¬(o.X = x ∧ o.A ≤ delta) := fun hx => by linarith
      simp [atomTerm, Set.indicator, ha, hn]
    · have hle : o.A ≤ delta := le_of_not_gt ha
      simp [atomTerm, Set.indicator, ha, hle]
  rw [integral_congr_ae hpoint, integral_add]
  · rw [integral_finsetSum Finset.univ]
    · unfold contClampFunctional retainedMean
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hevent : (∫ o,
          (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure) =
          P.px x * atomMass P x delta := by
        have hX : Measurable (fun o : ClampObs J => o.X) :=
          measurable_fst.comp (Measurable.of_comap_le le_rfl)
        have hA : Measurable (fun o : ClampObs J => o.A) :=
          measurable_fst.comp (measurable_snd.comp
            (Measurable.of_comap_le le_rfl))
        have hset : MeasurableSet {o : ClampObs J |
            o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} :=
          (measurableSet_eq_fun hX measurable_const).inter
            (measurableSet_Icc.preimage hA)
        calc
          _ = ∫ o, Set.indicator {o : ClampObs J |
              o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta}
              (fun _ => (1 : ℝ)) o ∂P.dataMeasure := by
            apply integral_congr_ae
            filter_upwards [hP.treatmentSupport] with o ho
            by_cases hx' : o.X = x <;> by_cases ha' : o.A ≤ delta <;>
              simp [Set.indicator, hx', ha', ho.1]
          _ = P.dataMeasure.real {o : ClampObs J |
              o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} := by
            rw [integral_indicator hset]
            simp
          _ = P.px x * atomMass P x delta := by
            rw [(hP.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
            · rfl
            · intro a ha'
              exact ⟨ha'.1, ha'.2.trans hdelta1⟩
      calc
        (∫ o, atomTerm x o ∂P.dataMeasure) =
            mu x delta * ∫ o,
              (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0)
              ∂P.dataMeasure := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with o
          by_cases h : o.X = x ∧ o.A ≤ delta <;> simp [atomTerm, h]
        _ = mu x delta * (P.px x * atomMass P x delta) := by rw [hevent]
        _ = P.px x * atomMass P x delta * mu x delta := by ring
    · exact fun x _ => hatomInt x
  · exact Integrable.of_bound
      ((clampOutcome_measurable.mul
        (Measurable.indicator measurable_const
          (measurableSet_lt measurable_const
            (measurable_fst.comp (measurable_snd.comp
              (Measurable.of_comap_le le_rfl))))))).aestronglyMeasurable 1
      (by filter_upwards [hP.outcomeSupport] with o ho
          by_cases ha : delta < o.A
          · simp [Set.indicator, ha, abs_of_nonneg ho.1, ho.2]
          · simp [Set.indicator, ha])
  · exact integrable_finsetSum Finset.univ fun x _ => hatomInt x

/-- The continuity-only clamp functional lies in the outcome range. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma contClampFunctional_mem_Icc
    (P : ClampLaw J) (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈
      Set.Icc (0 : ℝ) 1 := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  let g : ClampObs J → ℝ := fun o => if delta < o.A then o.Y else
    contRegression P kappa cminus cplus pmin deltaBar hP o.X delta
  have hgmeas : Measurable g := by
    dsimp [g]
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_fst.comp (measurable_snd.comp
          (Measurable.of_comap_le le_rfl)))) clampOutcome_measurable
      ((measurable_of_countable (fun x : Fin J =>
        contRegression P kappa cminus cplus pmin deltaBar hP x delta)).comp
          (measurable_fst.comp (Measurable.of_comap_le le_rfl)))
  have hg0 : 0 ≤ᵐ[P.dataMeasure] g := by
    filter_upwards [hP.outcomeSupport] with o ho
    dsimp [g]
    split_ifs
    · exact ho.1
    · exact (contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
        hP hreg o.X delta hdelta).1
  have hg1 : g ≤ᵐ[P.dataMeasure] fun _ => (1 : ℝ) := by
    filter_upwards [hP.outcomeSupport] with o ho
    dsimp [g]
    split_ifs
    · exact ho.2
    · exact (contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
        hP hreg o.X delta hdelta).2
  rw [← contClampFunctional_integral_eq P kappa cminus cplus pmin deltaBar
    delta hP hreg hdelta]
  constructor
  · exact integral_nonneg_of_ae hg0
  · calc
      (∫ o, g o ∂P.dataMeasure) ≤ ∫ _o, (1 : ℝ) ∂P.dataMeasure :=
        integral_mono_ae
          (Integrable.of_bound hgmeas.aestronglyMeasurable 1
            (hg0.and hg1 |>.mono fun o h => by
              rw [Real.norm_eq_abs, abs_of_nonneg h.1]
              exact h.2)) (integrable_const 1) hg1
      _ = 1 := by simp

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
