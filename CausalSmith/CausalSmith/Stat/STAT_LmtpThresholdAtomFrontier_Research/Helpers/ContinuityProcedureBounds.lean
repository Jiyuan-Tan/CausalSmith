/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.ContinuityUpper
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SampleBlocks
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperTotal
import Causalean.Stat.Concentration.TailBounds.Hoeffding

/-! # Finite-sample bounds for the continuity-only procedure -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Hoeffding's inequality for an empirical average over a deterministic block
of the canonical finite-product sample. The result uses [the `hf` condition](hyp:hf), [the `hf01` condition](hyp:hf01), [the `ht` condition](hyp:ht). [This is the stated conclusion](goal).
-/
lemma blockAverage_hoeffding
    (_HoeffdingBoundedAverage_of_gate : HoeffdingBoundedAverage)
    {X : Type} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    {n : ℕ} (I : Finset (Fin n)) (f : X → ℝ) (hf : Measurable f)
    (hf01 : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : Fin n => P)).real
        {z | |blockAverage I z f - ∫ x, f x ∂P| > t} ≤
      2 * Real.exp (-2 * (I.card : ℝ) * t ^ 2) := by
  classical
  by_cases hI : I.card = 0
  · exact (measureReal_le_one (μ := Measure.pi fun _ : Fin n => P)
      (s := {z | |blockAverage I z f - ∫ x, f x ∂P| > t})).trans (by
        simp [hI])
  let S := Causalean.Stat.iidSample_infinitePi P
  let sumFin : (Fin n → X) → ℝ := fun z => ∑ i ∈ I, f (z i)
  let sumInf : (ℕ → X) → ℝ :=
    Causalean.Stat.Concentration.bernoulliCount S f I.card
  let A : Set ℝ := {y | |(I.card : ℝ)⁻¹ * y - ∫ x, f x ∂P| > t}
  have hA : MeasurableSet A := by
    exact measurableSet_lt measurable_const
      (((measurable_const.mul measurable_id).sub measurable_const).abs)
  have hsumFin : Measurable sumFin := by
    exact Finset.measurable_fun_sum I fun i _ => hf.comp (measurable_pi_apply i)
  have hsumInf : Measurable sumInf := by
    dsimp [sumInf]
    exact Finset.measurable_fun_sum _ fun i _ => hf.comp (S.meas i)
  have hlaw : (Measure.pi (fun _ : Fin n => P)).map sumFin =
      (Measure.infinitePi (fun _ : ℕ => P)).map sumInf := by
    calc
      _ = (Measure.pi (fun _ : Fin I.card => P)).map
          (fun z => ∑ j : Fin I.card, f (z j)) :=
        block_count_law_eq P I f hf
      _ = _ := range_count_transport P I.card f hf
  have htail := Causalean.Stat.Concentration.hoeffding_abs_ge S hf
    (a := 0) (b := 1) (by norm_num) (ae_of_all _ hf01) I.card
    (Nat.pos_of_ne_zero hI) ht.le
  have hfinite : (Measure.pi (fun _ : Fin n => P)).real (sumFin ⁻¹' A) =
      ((Measure.pi (fun _ : Fin n => P)).map sumFin).real A := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal
      (Measure.map_apply hsumFin hA).symm
  have hinf : (Measure.infinitePi (fun _ : ℕ => P)).real (sumInf ⁻¹' A) =
      ((Measure.infinitePi (fun _ : ℕ => P)).map sumInf).real A := by
    simpa only [measureReal_def] using congrArg ENNReal.toReal
      (Measure.map_apply hsumInf hA).symm
  have hle : (Measure.infinitePi (fun _ : ℕ => P)).real (sumInf ⁻¹' A) ≤
      2 * Real.exp (-2 * (I.card : ℝ) * t ^ 2) := by
    refine (measureReal_mono
      (μ := Measure.infinitePi (fun _ : ℕ => P))
      (s₁ := sumInf ⁻¹' A)
      (s₂ := {w | t ≤ |S.sampleMean f I.card w - ∫ x, f x ∂P|}) ?_).trans ?_
    · intro w hw
      change t < |(I.card : ℝ)⁻¹ * sumInf w - ∫ x, f x ∂P| at hw
      change t ≤ |S.sampleMean f I.card w - ∫ x, f x ∂P|
      simpa [S, sumInf, Causalean.Stat.IIDSample.sampleMean,
        Causalean.Stat.Concentration.bernoulliCount] using le_of_lt hw
    · simpa [S, sumInf, A, Causalean.Stat.IIDSample.sampleMean] using htail
  calc
    (Measure.pi (fun _ : Fin n => P)).real
        {z | |blockAverage I z f - ∫ x, f x ∂P| > t} =
        (Measure.pi (fun _ : Fin n => P)).real (sumFin ⁻¹' A) := by
      rfl
    _ = ((Measure.pi (fun _ : Fin n => P)).map sumFin).real A := hfinite
    _ = ((Measure.infinitePi (fun _ : ℕ => P)).map sumInf).real A := by rw [hlaw]
    _ = (Measure.infinitePi (fun _ : ℕ => P)).real (sumInf ⁻¹' A) := hinf.symm
    _ ≤ _ := hle

/-- Outcome support lifts coordinatewise to the canonical finite product for a
continuity-only model. The result uses [the `hP` condition](hyp:hP). [This is the stated conclusion](goal).
-/
lemma cont_iidProduct_outcomeSupport {J n : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar) :
    ∀ᵐ z ∂iidProduct P n, ∀ i : Fin n, (z i).Y ∈ Set.Icc (0 : ℝ) 1 := by
  let _ := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  apply ae_all_iff.mpr
  intro i
  have hmap : (iidProduct P n).map (Function.eval i) = P.dataMeasure := by
    simpa [iidProduct] using (Measure.pi_map_eval (fun _ : Fin n => P.dataMeasure) i)
  have hs := hP.outcomeSupport
  rw [← hmap] at hs
  exact (ae_map_iff (μ := iidProduct P n) (f := Function.eval i)
    (p := fun o : ClampObs J => o.Y ∈ Set.Icc (0 : ℝ) 1)
    (measurable_pi_apply i).aemeasurable
    (measurableSet_Icc.preimage clampOutcome_measurable)).mp hs

/-- The retained-block empirical mean has root-block-size absolute risk in the
continuity-only model. The result uses [the `hP` condition](hyp:hP), [the `hcard` condition](hyp:hcard). [This is the stated conclusion](goal).
-/
lemma cont_retainedEstimate_l1_le {J n : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar delta : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (B : SplitBlocks n) (hcard : 0 < B.I0.card) :
    (∫ z, |retainedEstimate B z delta - retainedMean P delta| ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ := by
  let _ := hP.probability
  let f : ClampObs J → ℝ := fun o => if delta < o.A then clampUnit o.Y else 0
  have hf : Measurable f := by
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))))
      (clampUnit_measurable'.comp clampOutcome_measurable) measurable_const
  have hf0 : ∀ o, 0 ≤ f o := by
    intro o; dsimp [f]; split_ifs
    · exact (clampUnit_mem_Icc o.Y).1
    · norm_num
  have hf1 : ∀ o, f o ≤ 1 := by
    intro o; dsimp [f]; split_ifs
    · exact (clampUnit_mem_Icc o.Y).2
    · norm_num
  have hm : ∫ o, f o ∂P.dataMeasure = retainedMean P delta := by
    calc
      _ = ∫ o, (if delta < o.A then o.Y else 0) ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hP.outcomeSupport] with o ho
        simp [f, clampUnit, ho.1, ho.2]
      _ = _ := by
        unfold retainedMean
        apply integral_congr_ae
        filter_upwards with o
        by_cases ha : delta < o.A <;> simp [Set.indicator, ha]
  have heq : (∫ z, |retainedEstimate B z delta - retainedMean P delta|
      ∂iidProduct P n) =
      ∫ z, |blockAverage B.I0 z f - retainedMean P delta| ∂iidProduct P n := by
    apply integral_congr_ae
    filter_upwards [cont_iidProduct_outcomeSupport P hP] with z hz
    congr 2
    unfold retainedEstimate blockAverage
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [f, clampUnit, (hz i).1, (hz i).2]
  rw [heq]
  exact blockAverage_l1_le P B.I0 hcard f hf hf0 hf1 (retainedMean P delta) hm

/-- A stratum-threshold empirical mass has root-block-size absolute risk in
the continuity-only model. The result uses [the `hP` condition](hyp:hP), [the `hcard` condition](hyp:hcard), [the `hdelta` condition](hyp:hdelta), [the `hdelta1` condition](hyp:hdelta1). [This is the stated conclusion](goal).
-/
lemma cont_atomEstimate_l1_le {J n : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar delta : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (B : SplitBlocks n) (hcard : 0 < B.I1.card) (x : Fin J)
    (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 1) :
    (∫ z, |atomEstimate B z x delta - P.px x * atomMass P x delta|
      ∂iidProduct P n) ≤ (1 / 2 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ := by
  let _ := hP.probability
  let f : ClampObs J → ℝ := fun o => if o.X = x ∧ o.A ≤ delta then 1 else 0
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hf : Measurable f := by
    exact Measurable.ite
      ((measurableSet_eq_fun hX measurable_const).inter
        (measurableSet_le hA measurable_const)) measurable_const measurable_const
  have hf0 : ∀ o, 0 ≤ f o := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hf1 : ∀ o, f o ≤ 1 := by intro o; dsimp [f]; split_ifs <;> norm_num
  have hm : ∫ o, f o ∂P.dataMeasure = P.px x * atomMass P x delta := by
    have hset : MeasurableSet {o : ClampObs J |
        o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} :=
      (measurableSet_eq_fun hX measurable_const).inter
        (measurableSet_Icc.preimage hA)
    calc
      _ = ∫ o, Set.indicator {o : ClampObs J |
          o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} (fun _ => (1 : ℝ)) o
          ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hP.treatmentSupport] with o ho
        by_cases hx : o.X = x <;> by_cases ha : o.A ≤ delta <;>
          simp [f, Set.indicator, hx, ha, ho.1]
      _ = P.dataMeasure.real {o : ClampObs J |
          o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} := by
        rw [integral_indicator hset]
        simp
      _ = _ := by
        rw [(hP.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
        · rfl
        · intro a ha
          exact ⟨ha.1, ha.2.trans hdelta1⟩
  simpa [atomEstimate, f] using
    (blockAverage_l1_le P B.I1 hcard f hf hf0 hf1
      (P.px x * atomMass P x delta) hm)

/-- The polynomial thinning envelope controls each population atom
coefficient in the continuity-only model. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta). [This is the stated conclusion](goal).
-/
lemma cont_atomCoefficient_nonneg_le_envelope {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar delta : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (x : Fin J) (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar) :
    P.px x * atomMass P x delta ∈ Set.Icc 0
      (cplus * delta ^ (kappa + 1) / (kappa + 1)) := by
  rcases hreg with ⟨hJ, hkappa, hcminus, hcminus_le, hcplus, hpmin,
    hpmin_le, hdeltaBar, hdeltaBar1⟩
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hdeltaBar1.le
  have hsubset : Set.Icc (0 : ℝ) delta ⊆ Set.Icc (0 : ℝ) 1 := fun _ ha =>
    ⟨ha.1, ha.2.trans hdelta1⟩
  have hpiInt : Integrable (P.pi x)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top
    · exact (aemeasurable_restrict_of_measurable_subtype measurableSet_Icc
        (hP.condDensity.1 x)).aestronglyMeasurable
    · have hcplus0 : 0 ≤ cplus := by linarith
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        hP.condDensity.2.1 x, hP.thinning x] with a ha hnon hthin
      rw [Real.norm_eq_abs, abs_of_nonneg hnon]
      calc
        P.pi x a ≤ cplus * a ^ kappa := hthin.2
        _ ≤ cplus := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left
            (Real.rpow_le_one ha.1 ha.2 hkappa) hcplus0
  have hpiDelta : IntegrableOn (P.pi x) (Set.Icc (0 : ℝ) delta) volume :=
    hpiInt.mono_measure (Measure.restrict_mono_set volume hsubset)
  have hpowInt : IntegrableOn (fun a : ℝ => a ^ kappa)
      (Set.Icc 0 delta) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hdelta.1]
    exact intervalIntegral.intervalIntegrable_rpow (Or.inl hkappa)
  have hthinDelta := (hP.thinning x).filter_mono
    (ae_mono (Measure.restrict_mono_set volume hsubset))
  have hpowEval : (∫ a in Set.Icc (0 : ℝ) delta, a ^ kappa) =
      delta ^ (kappa + 1) / (kappa + 1) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hdelta.1,
      integral_rpow (Or.inl (by linarith : -1 < kappa))]
    rw [Real.zero_rpow (by linarith : kappa + 1 ≠ 0), sub_zero]
  have hmass0 : 0 ≤ atomMass P x delta := by
    unfold atomMass
    exact integral_nonneg_of_ae
      ((hP.condDensity.2.1 x).filter_mono
        (ae_mono (Measure.restrict_mono_set volume hsubset)))
  have hmassUpper : atomMass P x delta ≤
      cplus * delta ^ (kappa + 1) / (kappa + 1) := by
    unfold atomMass
    calc
      (∫ a in Set.Icc (0 : ℝ) delta, P.pi x a) ≤
          ∫ a in Set.Icc (0 : ℝ) delta, cplus * a ^ kappa :=
        integral_mono_ae hpiDelta (hpowInt.const_mul cplus)
          (hthinDelta.mono fun _ ha => ha.2)
      _ = _ := by rw [integral_const_mul, hpowEval]; ring
  have hXm : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  let _ := hP.probability
  letI : IsProbabilityMeasure (P.dataMeasure.map fun o => o.X) :=
    Measure.isProbabilityMeasure_map hXm.aemeasurable
  have hpx0 : 0 ≤ P.px x := by
    rw [(hP.stratumMass x).1]
    exact measureReal_nonneg
  have hpx1 : P.px x ≤ 1 := by
    rw [(hP.stratumMass x).1]
    exact measureReal_le_one
  exact ⟨mul_nonneg hpx0 hmass0,
    (mul_le_mul_of_nonneg_right hpx1 hmass0).trans (by simpa using hmassUpper)⟩

/-- The fixed one-half fallback has an explicit root-block plus threshold-mass
absolute-risk bound. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hcard0` condition](hyp:hcard0), [the `hcard1` condition](hyp:hcard1). [This is the stated conclusion](goal).
-/
lemma contFallbackEstimator_risk_le_explicit {J n : ℕ} (P : ClampLaw J)
    (B : SplitBlocks n) (kappa cminus cplus pmin deltaBar delta : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hcard0 : 0 < B.I0.card) (hcard1 : 0 < B.I1.card) :
    contEstimatorRisk P n kappa cminus cplus pmin deltaBar delta hP
        (contFallbackEstimator B · delta) ≤
      (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ +
      (J : ℝ) * ((1 / 4 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
        (1 / 2 : ℝ) * (cplus * delta ^ (kappa + 1) / (kappa + 1))) := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let target := contClampFunctional P kappa cminus cplus pmin deltaBar hP delta
  let e0 := fun z : Fin n → ClampObs J =>
    |retainedEstimate B z delta - retainedMean P delta|
  let ex := fun x : Fin J => fun z : Fin n → ClampObs J =>
    |atomEstimate B z x delta - P.px x * atomMass P x delta|
  let env := cplus * delta ^ (kappa + 1) / (kappa + 1)
  have ht := contClampFunctional_mem_Icc P kappa cminus cplus pmin deltaBar
    delta hP hreg hdelta
  have hpoint (z : Fin n → ClampObs J) :
      |contFallbackEstimator B z delta - target| ≤
        e0 z + ∑ x : Fin J, ((1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env) := by
    have hclamp := abs_clampUnit_sub_le
      (retainedEstimate B z delta +
        (1 / 2 : ℝ) * ∑ x : Fin J, atomEstimate B z x delta) target ht
    have hx (x : Fin J) :
        |(1 / 2 : ℝ) * atomEstimate B z x delta -
            P.px x * atomMass P x delta *
              contRegression P kappa cminus cplus pmin deltaBar hP x delta| ≤
          (1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env := by
      let coeff := P.px x * atomMass P x delta
      have hc := cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta
      have hm := contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
        hP hreg x delta hdelta
      have hmhalf : |(1 / 2 : ℝ) -
          contRegression P kappa cminus cplus pmin deltaBar hP x delta| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith [hm.1, hm.2]
      calc
        _ = |(1 / 2 : ℝ) *
              (atomEstimate B z x delta - coeff) +
            coeff * ((1 / 2 : ℝ) -
              contRegression P kappa cminus cplus pmin deltaBar hP x delta)| := by
              congr 1
              dsimp [coeff]
              ring
        _ ≤ |(1 / 2 : ℝ) * (atomEstimate B z x delta - coeff)| +
            |coeff * ((1 / 2 : ℝ) -
              contRegression P kappa cminus cplus pmin deltaBar hP x delta)| :=
          abs_add_le _ _
        _ ≤ (1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env := by
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
            abs_mul, abs_of_nonneg hc.1]
          dsimp [ex, coeff, env]
          nlinarith [mul_le_mul_of_nonneg_left hmhalf hc.1,
            mul_le_mul_of_nonneg_left hc.2 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc
      |contFallbackEstimator B z delta - target| ≤
          |(retainedEstimate B z delta - retainedMean P delta) +
            ∑ x : Fin J, ((1 / 2 : ℝ) * atomEstimate B z x delta -
              P.px x * atomMass P x delta *
                contRegression P kappa cminus cplus pmin deltaBar hP x delta)| := by
        refine hclamp.trans_eq ?_
        congr 1
        dsimp [target]
        unfold contClampFunctional
        rw [Finset.mul_sum, Finset.sum_sub_distrib]
        ring
      _ ≤ e0 z + ∑ x : Fin J,
          |(1 / 2 : ℝ) * atomEstimate B z x delta -
            P.px x * atomMass P x delta *
              contRegression P kappa cminus cplus pmin deltaBar hP x delta| := by
        let fsum := fun x : Fin J =>
          (1 / 2 : ℝ) * atomEstimate B z x delta -
            P.px x * atomMass P x delta *
              contRegression P kappa cminus cplus pmin deltaBar hP x delta
        have hs : |∑ x : Fin J, fsum x| ≤ ∑ x : Fin J, |fsum x| := by
          simpa using Finset.abs_sum_le_sum_abs fsum Finset.univ
        exact (abs_add_le _ _).trans (add_le_add_right hs _)
      _ ≤ _ := by
        exact add_le_add_right (Finset.sum_le_sum fun x _ => hx x) _
  have he0int : Integrable e0 (iidProduct P n) := by
    refine Integrable.of_bound
      ((retainedEstimate_measurable B delta).sub measurable_const).abs.aestronglyMeasurable 2 ?_
    filter_upwards [cont_iidProduct_outcomeSupport P hP] with z hz
    dsimp [e0]
    rw [abs_abs]
    have hr := blockAverage_mem_Icc B.I0 z
      (fun o : ClampObs J => if delta < o.A then clampUnit o.Y else 0) (fun o => by
      split_ifs
      · exact (clampUnit_mem_Icc o.Y)
      · exact ⟨by norm_num, by norm_num⟩)
    have hre : retainedEstimate B z delta = blockAverage B.I0 z
        (fun o : ClampObs J => if delta < o.A then clampUnit o.Y else 0) := by
      unfold retainedEstimate blockAverage
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [clampUnit, (hz i).1, (hz i).2]
    have hm0 : |retainedMean P delta| ≤ 1 := by
      let g := Set.indicator {o : ClampObs J | delta < o.A} (fun o => o.Y)
      have hgmeas : Measurable g := clampOutcome_measurable.indicator
        (measurableSet_lt measurable_const
          (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))))
      have hgint : Integrable g P.dataMeasure := by
        refine Integrable.of_bound hgmeas.aestronglyMeasurable 1 ?_
        filter_upwards [hP.outcomeSupport] with o ho
        by_cases ha : delta < o.A <;> simp [g, Set.indicator, ha, abs_of_nonneg ho.1, ho.2]
      have hg0 : 0 ≤ᵐ[P.dataMeasure] g := by
        filter_upwards [hP.outcomeSupport] with o ho
        by_cases ha : delta < o.A <;> simp [g, Set.indicator, ha, ho.1]
      have hg1 : g ≤ᵐ[P.dataMeasure] fun _ => (1 : ℝ) := by
        filter_upwards [hP.outcomeSupport] with o ho
        by_cases ha : delta < o.A <;> simp [g, Set.indicator, ha, ho.2]
      have hmI : retainedMean P delta ∈ Set.Icc (0 : ℝ) 1 := by
        have hret : retainedMean P delta = ∫ o, g o ∂P.dataMeasure := by
          unfold retainedMean
          apply integral_congr_ae
          filter_upwards with o
          by_cases ha : delta < o.A <;> simp [g, Set.indicator, ha]
        rw [hret]
        exact ⟨integral_nonneg_of_ae hg0,
          (integral_mono_ae hgint (integrable_const 1) hg1).trans_eq (by simp)⟩
      rw [abs_of_nonneg hmI.1]
      exact hmI.2
    rw [hre]
    rw [abs_le]
    have hmBounds := (abs_le.mp hm0)
    exact ⟨by linarith [hr.1, hmBounds.2], by linarith [hr.2, hmBounds.1]⟩
  have hexint (x : Fin J) : Integrable (ex x) (iidProduct P n) := by
    refine Integrable.of_bound
      ((atomEstimate_measurable B x delta).sub measurable_const).abs.aestronglyMeasurable 2 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    change |atomEstimate B z x delta - P.px x * atomMass P x delta| ≤ 2
    have ha := atomEstimate_mem_Icc B z x delta
    have hc := cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta
    have hcoef1 : P.px x * atomMass P x delta ≤ 1 := by
      unfold atomMass
      rw [← (hP.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
      · exact measureReal_le_one
      · intro a ha'
        exact ⟨ha'.1, ha'.2.trans
          (hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le)⟩
    rw [abs_le]
    exact ⟨by linarith [ha.1, hcoef1], by linarith [ha.2, hc.1]⟩
  have hrhsInt : Integrable
      (fun z => e0 z + ∑ x : Fin J,
        ((1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env)) (iidProduct P n) :=
    he0int.add (integrable_finsetSum Finset.univ fun x _ =>
      ((hexint x).const_mul (1 / 2)).add (integrable_const _))
  have hlhsInt : Integrable
      (fun z => |contFallbackEstimator B z delta - target|) (iidProduct P n) := by
    have hest : Measurable (fun z : Fin n → ClampObs J =>
        contFallbackEstimator B z delta) := by
      unfold contFallbackEstimator
      exact clampUnit_measurable'.comp ((retainedEstimate_measurable B delta).add
        (measurable_const.mul (Finset.measurable_fun_sum _ fun x _ =>
          atomEstimate_measurable B x delta)))
    refine Integrable.of_bound
      ((hest.sub measurable_const).abs.aestronglyMeasurable) 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_abs, abs_le]
    have hs := clampUnit_mem_Icc
      (retainedEstimate B z delta + (1 / 2 : ℝ) *
        ∑ x : Fin J, atomEstimate B z x delta)
    change target ∈ Set.Icc (0 : ℝ) 1 at ht
    change contFallbackEstimator B z delta - target ∈ Set.Icc (-1 : ℝ) 1
    exact ⟨by unfold contFallbackEstimator; linarith [hs.1, ht.2],
      by unfold contFallbackEstimator; linarith [hs.2, ht.1]⟩
  unfold contEstimatorRisk
  change (∫ z, |contFallbackEstimator B z delta - target| ∂iidProduct P n) ≤ _
  calc
    _ ≤ ∫ z, (e0 z + ∑ x : Fin J,
        ((1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env)) ∂iidProduct P n :=
      integral_mono_ae hlhsInt hrhsInt (ae_of_all _ hpoint)
    _ = (∫ z, e0 z ∂iidProduct P n) + ∑ x : Fin J,
        ((1 / 2 : ℝ) * ∫ z, ex x z ∂iidProduct P n + (1 / 2 : ℝ) * env) := by
      have hsumInt : Integrable (fun z => ∑ x : Fin J,
          ((1 / 2 : ℝ) * ex x z + (1 / 2 : ℝ) * env)) (iidProduct P n) :=
        integrable_finsetSum Finset.univ fun x _ =>
          ((hexint x).const_mul (1 / 2)).add (integrable_const _)
      rw [integral_add he0int hsumInt, integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro x hx
        rw [integral_add ((hexint x).const_mul (1 / 2)) (integrable_const _),
          integral_const_mul, integral_const]
        simp
      · intro x hx
        exact (hexint x).const_mul (1 / 2) |>.add (integrable_const _)
    _ ≤ (1 / 2 : ℝ) * Real.sqrt (B.I0.card : ℝ)⁻¹ +
        ∑ _x : Fin J, ((1 / 4 : ℝ) * Real.sqrt (B.I1.card : ℝ)⁻¹ +
          (1 / 2 : ℝ) * env) := by
      apply add_le_add
      · exact cont_retainedEstimate_l1_le P hP B hcard0
      · apply Finset.sum_le_sum
        intro x hx
        have h := cont_atomEstimate_l1_le P hP B hcard1 x hdelta.1
          (hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le)
        nlinarith
    _ = _ := by simp [env]; ring

/-- Summing the stratum indicators gives the single threshold indicator. [This is the stated conclusion](goal).
-/
lemma cont_atomTotal_eq_blockAverage {J n : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (delta : ℝ) :
    (∑ x : Fin J, atomEstimate B z x delta) =
      blockAverage B.I1 z (fun o => if o.A ≤ delta then 1 else 0) := by
  classical
  unfold atomEstimate blockAverage
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ x : Fin J, ∑ i ∈ B.I1,
        if (z i).X = x ∧ (z i).A ≤ delta then (1 : ℝ) else 0) =
        ∑ i ∈ B.I1, ∑ x : Fin J,
          if (z i).X = x ∧ (z i).A ≤ delta then (1 : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ B.I1, if (z i).A ≤ delta then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases ha : (z i).A ≤ delta <;> simp [ha]

/-- The population counterpart of the total empirical threshold mass. The result uses [the `hP` condition](hyp:hP), [the `hdelta` condition](hyp:hdelta), [the `hreg` condition](hyp:hreg). [This is the stated conclusion](goal).
-/
lemma cont_atomTotal_integral_eq {J : ℕ} (P : ClampLaw J)
    {kappa cminus cplus pmin deltaBar delta : ℝ}
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar) :
    (∫ o, (if o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure) =
      ∑ x : Fin J, P.px x * atomMass P x delta := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  have hdelta1 : delta ≤ 1 := hdelta.2.trans hreg.2.2.2.2.2.2.2.2.le
  have hX : Measurable (fun o : ClampObs J => o.X) :=
    measurable_fst.comp (Measurable.of_comap_le le_rfl)
  have hA : Measurable (fun o : ClampObs J => o.A) :=
    measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))
  have hone (x : Fin J) :
      (∫ o, (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure) =
        P.px x * atomMass P x delta := by
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
        by_cases hx : o.X = x <;> by_cases ha : o.A ≤ delta <;>
          simp [Set.indicator, hx, ha, ho.1]
      _ = P.dataMeasure.real {o : ClampObs J |
          o.X = x ∧ o.A ∈ Set.Icc (0 : ℝ) delta} := by
        rw [integral_indicator hset]
        simp
      _ = _ := by
        rw [(hP.condDensity.2.2 x).2 (Set.Icc 0 delta) measurableSet_Icc]
        · rfl
        · intro a ha
          exact ⟨ha.1, ha.2.trans hdelta1⟩
  calc
    _ = ∫ o, ∑ x : Fin J,
        (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure := by
      apply integral_congr_ae
      filter_upwards with o
      by_cases ha : o.A ≤ delta <;> simp [ha]
    _ = ∑ x : Fin J, ∫ o,
        (if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) ∂P.dataMeasure := by
      apply integral_finsetSum
      intro x hx
      have hf : Measurable (fun o : ClampObs J =>
          if o.X = x ∧ o.A ≤ delta then (1 : ℝ) else 0) :=
        Measurable.ite
          ((measurableSet_eq_fun hX measurable_const).inter
            (measurableSet_le hA measurable_const)) measurable_const measurable_const
      exact Integrable.of_bound hf.aestronglyMeasurable 1 (by
        filter_upwards with o
        split_ifs <;> norm_num)
    _ = _ := Finset.sum_congr rfl fun x _ => hone x

/-- A deterministic deviation implication used by the two-block interval. The result uses [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `h0` condition](hyp:h0), [the `h1` condition](hyp:h1). [This is the stated conclusion](goal).
-/
lemma contFallbackEstimator_mem_interval_of_good {J n : ℕ} (P : ClampLaw J)
    (B : SplitBlocks n) (kappa cminus cplus pmin deltaBar delta alpha t0 t1 : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContDesignConstants J kappa cminus cplus pmin deltaBar)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (z : Fin n → ClampObs J)
    (h0 : |retainedEstimate B z delta - retainedMean P delta| ≤ t0)
    (h1 : |(∑ x : Fin J, atomEstimate B z x delta) -
      ∑ x : Fin J, P.px x * atomMass P x delta| ≤ t1) :
    contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈
      Set.Icc
        (max 0 (contFallbackEstimator B z delta -
          (t0 + t1 + (∑ x : Fin J, atomEstimate B z x delta) / 2)))
        (min 1 (contFallbackEstimator B z delta +
          (t0 + t1 + (∑ x : Fin J, atomEstimate B z x delta) / 2))) := by
  let E := ∑ x : Fin J, atomEstimate B z x delta
  let M := ∑ x : Fin J, P.px x * atomMass P x delta
  let T := ∑ x : Fin J, P.px x * atomMass P x delta *
    contRegression P kappa cminus cplus pmin deltaBar hP x delta
  let target := contClampFunctional P kappa cminus cplus pmin deltaBar hP delta
  have hE : 0 ≤ E := Finset.sum_nonneg fun x _ =>
    (atomEstimate_mem_Icc B z x delta).1
  have hM : 0 ≤ M := Finset.sum_nonneg fun x _ =>
    (cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta).1
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => mul_nonneg
    (cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta).1
    (contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
      hP hreg x delta hdelta).1
  have hTM : T ≤ M := by
    apply Finset.sum_le_sum
    intro x hx
    have hc := cont_atomCoefficient_nonneg_le_envelope P hP hreg x hdelta
    have hm := contRegression_mem_Icc P kappa cminus cplus pmin deltaBar
      hP hreg x delta hdelta
    simpa using mul_le_of_le_one_right hc.1 hm.2
  have hEM : M - E ≤ t1 := by
    have := (abs_le.mp h1).1
    dsimp [E, M] at this ⊢
    linarith
  have ht1 : 0 ≤ t1 := (abs_nonneg _).trans h1
  have hatom : |(1 / 2 : ℝ) * E - T| ≤ t1 + E / 2 := by
    rw [abs_le]
    constructor <;> dsimp [E, M, T] at * <;> linarith
  have htI := contClampFunctional_mem_Icc P kappa cminus cplus pmin deltaBar
    delta hP hreg hdelta
  have hdev : |contFallbackEstimator B z delta - target| ≤ t0 + t1 + E / 2 := by
    have hc := abs_clampUnit_sub_le
      (retainedEstimate B z delta + (1 / 2 : ℝ) * E) target htI
    calc
      _ ≤ |(retainedEstimate B z delta - retainedMean P delta) +
          ((1 / 2 : ℝ) * E - T)| := by
        refine hc.trans_eq ?_
        congr 1
        dsimp [target, T]
        unfold contClampFunctional
        ring
      _ ≤ |retainedEstimate B z delta - retainedMean P delta| +
          |(1 / 2 : ℝ) * E - T| := abs_add_le _ _
      _ ≤ _ := by linarith
  change target ∈ Set.Icc _ _
  constructor
  · apply max_le htI.1
    dsimp [E] at hdev ⊢
    rw [abs_le] at hdev
    linarith [hdev.2]
  · apply le_min htI.2
    dsimp [E] at hdev ⊢
    rw [abs_le] at hdev
    linarith [hdev.1]

/-- The displayed square-root radius calibrates the two-sided Hoeffding tail
to `alpha / 2`. The result uses [the `hm` condition](hyp:hm), [the `ha` condition](hyp:ha), [the `ha1` condition](hyp:ha1). [This is the stated conclusion](goal).
-/
lemma cont_hoeffding_radius_tail_le (m : ℕ) (alpha : ℝ)
    (hm : 0 < m) (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    2 * Real.exp (-2 * (m : ℝ) *
        (Real.sqrt (Real.log (4 / alpha) / (2 * (m : ℝ)))) ^ 2) ≤
      alpha / 2 := by
  have hmR : 0 < (m : ℝ) := by positivity
  have hquot : 1 < 4 / alpha := by
    rw [lt_div_iff₀ ha]
    linarith
  have hlog : 0 ≤ Real.log (4 / alpha) := (Real.log_pos hquot).le
  rw [Real.sq_sqrt (div_nonneg hlog (by positivity : 0 ≤ 2 * (m : ℝ)))]
  have he : -2 * (m : ℝ) * (Real.log (4 / alpha) / (2 * (m : ℝ))) =
      -Real.log (4 / alpha) := by field_simp
  rw [he, Real.exp_neg, Real.exp_log (by positivity : 0 < 4 / alpha)]
  field_simp
  norm_num

/-- The continuity-only interval covers its model-specific target with the
advertised finite-sample probability. The result uses [the `HoeffdingBoundedAverage_of_gate` condition](hyp:HoeffdingBoundedAverage_of_gate), [the `hP` condition](hyp:hP), [the `hreg` condition](hyp:hreg), [the `hdelta` condition](hyp:hdelta), [the `hcard0` condition](hyp:hcard0), [the `hcard1` condition](hyp:hcard1). [This is the stated conclusion](goal).
-/
lemma contHoeffdingInterval_coverage_model
    (HoeffdingBoundedAverage_of_gate : HoeffdingBoundedAverage)
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n)
    (kappa cminus cplus pmin deltaBar delta alpha : ℝ)
    (hP : ContClampModel P kappa cminus cplus pmin deltaBar)
    (hreg : ContRegimeConstants J kappa cminus cplus pmin deltaBar alpha)
    (hdelta : delta ∈ Set.Icc (0 : ℝ) deltaBar)
    (hcard0 : 0 < B.I0.card) (hcard1 : 0 < B.I1.card) :
    1 - alpha ≤ (iidProduct P n).real {z |
      contClampFunctional P kappa cminus cplus pmin deltaBar hP delta ∈
        contHoeffdingInterval B z delta alpha} := by
  letI : IsProbabilityMeasure P.dataMeasure := hP.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let f0 : ClampObs J → ℝ := fun o => if delta < o.A then clampUnit o.Y else 0
  let f1 : ClampObs J → ℝ := fun o => if o.A ≤ delta then 1 else 0
  let t0 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ)))
  let t1 := Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ)))
  let target := contClampFunctional P kappa cminus cplus pmin deltaBar hP delta
  let good : Set (Fin n → ClampObs J) := {z | target ∈ contHoeffdingInterval B z delta alpha}
  let bad0 : Set (Fin n → ClampObs J) :=
    {z | |blockAverage B.I0 z f0 - ∫ o, f0 o ∂P.dataMeasure| > t0}
  let bad1 : Set (Fin n → ClampObs J) :=
    {z | |blockAverage B.I1 z f1 - ∫ o, f1 o ∂P.dataMeasure| > t1}
  have hf0 : Measurable f0 := by
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))))
      (clampUnit_measurable'.comp clampOutcome_measurable) measurable_const
  have hf1 : Measurable f1 := by
    exact Measurable.ite
      (measurableSet_le
        (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl)))
        measurable_const) measurable_const measurable_const
  have hf001 : ∀ o, f0 o ∈ Set.Icc (0 : ℝ) 1 := by
    intro o; dsimp [f0]; split_ifs
    · exact clampUnit_mem_Icc _
    · exact ⟨by norm_num, by norm_num⟩
  have hf101 : ∀ o, f1 o ∈ Set.Icc (0 : ℝ) 1 := by
    intro o; dsimp [f1]; split_ifs <;> constructor <;> norm_num
  have ht0 : 0 < t0 := by
    dsimp [t0]
    have hq : 1 < 4 / alpha := by
      rw [lt_div_iff₀ hreg.2.1]
      linarith [hreg.2.2]
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos hq) (by positivity))
  have ht1 : 0 < t1 := by
    dsimp [t1]
    have hq : 1 < 4 / alpha := by
      rw [lt_div_iff₀ hreg.2.1]
      linarith [hreg.2.2]
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos hq) (by positivity))
  have hb0 : (iidProduct P n).real bad0 ≤ alpha / 2 := by
    exact (blockAverage_hoeffding HoeffdingBoundedAverage_of_gate P.dataMeasure
      B.I0 f0 hf0 hf001 t0 ht0).trans
        (cont_hoeffding_radius_tail_le B.I0.card alpha hcard0 hreg.2.1 hreg.2.2)
  have hb1 : (iidProduct P n).real bad1 ≤ alpha / 2 := by
    exact (blockAverage_hoeffding HoeffdingBoundedAverage_of_gate P.dataMeasure
      B.I1 f1 hf1 hf101 t1 ht1).trans
        (cont_hoeffding_radius_tail_le B.I1.card alpha hcard1 hreg.2.1 hreg.2.2)
  have hm0 : ∫ o, f0 o ∂P.dataMeasure = retainedMean P delta := by
    calc
      _ = ∫ o, (if delta < o.A then o.Y else 0) ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hP.outcomeSupport] with o ho
        simp [f0, clampUnit, ho.1, ho.2]
      _ = _ := by
        unfold retainedMean
        apply integral_congr_ae
        filter_upwards with o
        by_cases ha : delta < o.A <;> simp [Set.indicator, ha]
  have hm1 : ∫ o, f1 o ∂P.dataMeasure =
      ∑ x : Fin J, P.px x * atomMass P x delta :=
    cont_atomTotal_integral_eq P hP hdelta hreg.1
  have hsub : ∀ᵐ z ∂iidProduct P n, z ∈ goodᶜ → z ∈ bad0 ∪ bad1 := by
    filter_upwards [cont_iidProduct_outcomeSupport P hP] with z hz
    intro hzg
    by_contra hzbad
    have hz0 : |blockAverage B.I0 z f0 - ∫ o, f0 o ∂P.dataMeasure| ≤ t0 :=
      le_of_not_gt (fun h => hzbad (Or.inl h))
    have hz1 : |blockAverage B.I1 z f1 - ∫ o, f1 o ∂P.dataMeasure| ≤ t1 :=
      le_of_not_gt (fun h => hzbad (Or.inr h))
    have hre : retainedEstimate B z delta = blockAverage B.I0 z f0 := by
      unfold retainedEstimate blockAverage
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [f0, clampUnit, (hz i).1, (hz i).2]
    have hmem := contFallbackEstimator_mem_interval_of_good P B kappa cminus cplus
      pmin deltaBar delta alpha t0 t1 hP hreg.1 hdelta z
      (by simpa [hre, hm0] using hz0)
      (by simpa [cont_atomTotal_eq_blockAverage, hm1] using hz1)
    exact hzg hmem
  have hfail : (iidProduct P n).real goodᶜ ≤ alpha := by
    have hm := measure_mono_ae hsub
    have hmreal : (iidProduct P n).real goodᶜ ≤ (iidProduct P n).real (bad0 ∪ bad1) :=
      ENNReal.toReal_mono (measure_ne_top _ _) hm
    exact hmreal.trans ((measureReal_union_le bad0 bad1).trans (by linarith))
  have hgoodMeas : MeasurableSet good := by
    dsimp [good, target]
    simp only [contHoeffdingInterval]
    have hc : Measurable (fun z : Fin n → ClampObs J =>
        contFallbackEstimator B z delta) := by
      unfold contFallbackEstimator
      exact clampUnit_measurable'.comp ((retainedEstimate_measurable B delta).add
        (measurable_const.mul (Finset.measurable_fun_sum _ fun x _ =>
          atomEstimate_measurable B x delta)))
    have hr : Measurable (fun z : Fin n → ClampObs J =>
        Real.sqrt (Real.log (4 / alpha) / (2 * (B.I0.card : ℝ))) +
        Real.sqrt (Real.log (4 / alpha) / (2 * (B.I1.card : ℝ))) +
          (∑ x : Fin J, atomEstimate B z x delta) / 2) :=
      (measurable_const.add measurable_const).add
        ((Finset.measurable_fun_sum _ fun x _ =>
          atomEstimate_measurable B x delta).div_const 2)
    exact (measurableSet_le (measurable_const.max (hc.sub hr)) measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.min (hc.add hr)))
  have hadd := measureReal_add_measureReal_compl (μ := iidProduct P n) hgoodMeas
  have huniv : (iidProduct P n).real Set.univ = 1 := by simp
  rw [huniv] at hadd
  change 1 - alpha ≤ (iidProduct P n).real good
  linarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
