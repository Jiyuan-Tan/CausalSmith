/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestPointwise
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestIntervalBasic
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.WeightedConcentration
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SampleBlocks
import Causalean.Stat.Concentration.TailBounds.Hoeffding

/-! # Finite-sample coverage of the bias-aware interval -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

noncomputable section

/-- Hoeffding for a deterministic block, proved directly from the Causalean
finite-product theorem and hence requiring no external theorem gate. The result uses [the `hf` condition](hyp:hf), [the `hf01` condition](hyp:hf01), [the `ht` condition](hyp:ht). [This is the stated conclusion](goal).
-/
lemma honest_blockAverage_hoeffding
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
          (fun z => ∑ j : Fin I.card, f (z j)) := block_count_law_eq P I f hf
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
        (Measure.pi (fun _ : Fin n => P)).real (sumFin ⁻¹' A) := by rfl
    _ = ((Measure.pi (fun _ : Fin n => P)).map sumFin).real A := hfinite
    _ = ((Measure.infinitePi (fun _ : ℕ => P)).map sumInf).real A := by rw [hlaw]
    _ = (Measure.infinitePi (fun _ : ℕ => P)).real (sumInf ⁻¹' A) := hinf.symm
    _ ≤ _ := hle

/-- The common logarithmic radius gives each of the `2J+1` bad events ample
budget under the union bound. The result uses [the `hJ` condition](hyp:hJ), [the `hm` condition](hyp:hm), [the `ha` condition](hyp:ha), [the `ha1` condition](hyp:ha1). [This is the stated conclusion](goal).
-/
lemma honest_radius_tail_le (J m : ℕ) (alpha : ℝ)
    (hJ : 0 < J) (hm : 0 < m) (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    2 * Real.exp (-2 * (m : ℝ) *
        (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
          Real.sqrt (m : ℝ)) ^ 2) ≤ alpha / (6 * (J : ℝ)) := by
  have hJR : 0 < (J : ℝ) := by positivity
  have hmR : 0 < (m : ℝ) := by positivity
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hq : 1 < 12 * (J : ℝ) / alpha := by
    rw [lt_div_iff₀ ha]
    have : alpha < 6 := lt_trans ha1 (by norm_num)
    nlinarith
  have hlog : 0 ≤ Real.log (12 * (J : ℝ) / alpha) := (Real.log_pos hq).le
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ (m : ℝ)),
    Real.sq_sqrt (div_nonneg hlog (by norm_num : (0 : ℝ) ≤ 2))]
  have he : -2 * (m : ℝ) *
      ((Real.log (12 * (J : ℝ) / alpha) / 2) / (m : ℝ)) =
      -Real.log (12 * (J : ℝ) / alpha) := by field_simp
  rw [he, Real.exp_neg, Real.exp_log (by positivity : 0 < 12 * (J : ℝ) / alpha)]
  field_simp
  norm_num

/-- [honest weighted tail satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `alpha` input](hyp:alpha), [the specified `hJ` input](hyp:hJ), [the specified `ha` input](hyp:ha), [the specified `ha1` input](hyp:ha1). -/
lemma honest_weighted_tail_le (J : ℕ) (alpha : ℝ)
    (hJ : 0 < J) (ha : 0 < alpha) (ha1 : alpha < 1 / 2) :
    2 * Real.exp (-2 *
        (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)) ^ 2) ≤
      alpha / (6 * (J : ℝ)) := by
  have hJR : 0 < (J : ℝ) := by positivity
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
  have hq : 1 < 12 * (J : ℝ) / alpha := by
    rw [lt_div_iff₀ ha]
    have : alpha < 6 := lt_trans ha1 (by norm_num)
    nlinarith
  have hlog : 0 ≤ Real.log (12 * (J : ℝ) / alpha) := (Real.log_pos hq).le
  rw [Real.sq_sqrt (div_nonneg hlog (by norm_num : (0 : ℝ) ≤ 2))]
  have he : -2 * (Real.log (12 * (J : ℝ) / alpha) / 2) =
      -Real.log (12 * (J : ℝ) / alpha) := by ring
  rw [he, Real.exp_neg, Real.exp_log (by positivity : 0 < 12 * (J : ℝ) / alpha)]
  field_simp
  norm_num

/-- Every fixed model law is covered by the bias-aware interval with
probability at least `1-alpha`. The result uses [the `hmodel` condition](hyp:hmodel), [the `hJ` condition](hyp:hJ), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `ha` condition](hyp:ha), [the `ha1` condition](hyp:ha1), [the `hn` condition](hyp:hn), [the `hdelta` condition](hyp:hdelta), [the `hupper` condition](hyp:hupper), [the `hh` condition](hyp:hh), [the `hlambda` condition](hyp:hlambda). [This is the stated conclusion](goal).
-/
lemma honestInterval_coverage_model
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n)
    (beta kappa L cminus cplus pmin delta h alpha : ℝ)
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hJ : 0 < J) (hbeta : 0 < beta) (hL : 0 < L)
    (ha : 0 < alpha) (ha1 : alpha < 1 / 2)
    (hn : 4 ≤ n) (hdelta : 0 ≤ delta) (hupper : delta + h ≤ 1)
    (hh : 0 < h)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus) :
    1 - alpha ≤ (iidProduct P n).real {z |
      clampFunctional P delta ∈
        honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha} := by
  classical
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let t := Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2)
  let b0 := t / Real.sqrt (B.I0.card : ℝ)
  let b1 := t / Real.sqrt (B.I1.card : ℝ)
  let f0 : ClampObs J → ℝ := fun o => if delta < o.A then clampUnit o.Y else 0
  let f1 : Fin J → ClampObs J → ℝ := fun x o =>
    if o.X = x ∧ o.A ≤ delta then 1 else 0
  let bad0 : Set (Fin n → ClampObs J) :=
    {z | |blockAverage B.I0 z f0 - ∫ o, f0 o ∂P.dataMeasure| > b0}
  let bad1 : Fin J → Set (Fin n → ClampObs J) := fun x =>
    {z | |blockAverage B.I1 z (f1 x) - ∫ o, f1 x o ∂P.dataMeasure| > b1}
  let bad2 : Fin J → Set (Fin n → ClampObs J) := fun x => {z |
    GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h ∧
    t * Real.sqrt (∑ i ∈ B.I2,
      (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) ≤
    |∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
      ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A))|}
  let bad := bad0 ∪ (⋃ x, bad1 x) ∪ (⋃ x, bad2 x)
  let good : Set (Fin n → ClampObs J) := {z |
    clampFunctional P delta ∈
      honestInterval B z (ellOf beta) beta kappa L cminus cplus delta h alpha}
  have hcard0 : 0 < B.I0.card := by have := B.card_I0; omega
  have hcard1 : 0 < B.I1.card := by have := B.card_I1; omega
  have ht : 0 < t := by
    dsimp [t]
    have hJR : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have hq : 1 < 12 * (J : ℝ) / alpha := by
      rw [lt_div_iff₀ ha]
      nlinarith
    exact Real.sqrt_pos.2 (div_pos (Real.log_pos hq) (by norm_num))
  have hb0pos : 0 < b0 := div_pos ht (Real.sqrt_pos.2 (by positivity))
  have hb1pos : 0 < b1 := div_pos ht (Real.sqrt_pos.2 (by positivity))
  have hf0 : Measurable f0 := by
    exact Measurable.ite
      (measurableSet_lt measurable_const
        (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))))
      (clampUnit_measurable'.comp clampOutcome_measurable) measurable_const
  have hf1 : ∀ x, Measurable (f1 x) := by
    intro x
    exact Measurable.ite
      ((measurableSet_eq_fun
        (measurable_fst.comp (Measurable.of_comap_le le_rfl)) measurable_const).inter
        (measurableSet_le
          (measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl)))
          measurable_const)) measurable_const measurable_const
  have hf001 : ∀ o, f0 o ∈ Set.Icc (0 : ℝ) 1 := by
    intro o; dsimp [f0]; split_ifs
    · exact clampUnit_mem_Icc _
    · norm_num
  have hf101 : ∀ x o, f1 x o ∈ Set.Icc (0 : ℝ) 1 := by
    intro x o; dsimp [f1]; split_ifs <;> norm_num
  have hbad0 : (iidProduct P n).real bad0 ≤ alpha / (6 * (J : ℝ)) := by
    have hcal := honest_radius_tail_le J (B.I0.card) alpha hJ hcard0 ha ha1
    exact (honest_blockAverage_hoeffding P.dataMeasure B.I0 f0 hf0 hf001 b0
      hb0pos).trans (by simpa [b0, t] using hcal)
  have hbad1 : ∀ x, (iidProduct P n).real (bad1 x) ≤ alpha / (6 * (J : ℝ)) := by
    intro x
    have hcal := honest_radius_tail_le J (B.I1.card) alpha hJ hcard1 ha ha1
    exact (honest_blockAverage_hoeffding P.dataMeasure B.I1 (f1 x) (hf1 x)
      (fun o => hf101 x o) b1 hb1pos).trans (by simpa [b1, t] using hcal)
  have hbad2 : ∀ x, (iidProduct P n).real (bad2 x) ≤ alpha / (6 * (J : ℝ)) := by
    intro x
    exact (block_weighted_tail_on_good_gram P hmodel B x delta h t
      ⟨0, by omega⟩ hlambda ht.le).trans (by
        simpa [t] using honest_weighted_tail_le J alpha hJ ha ha1)
  have hm0 : ∫ o, f0 o ∂P.dataMeasure = retainedMean P delta := by
    calc
      _ = ∫ o, (if delta < o.A then o.Y else 0) ∂P.dataMeasure := by
        apply integral_congr_ae
        filter_upwards [hmodel.outcomeSupport] with o ho
        simp [f0, clampUnit, ho.1, ho.2]
      _ = _ := by
        unfold retainedMean
        apply integral_congr_ae
        filter_upwards with o
        by_cases hd : delta < o.A <;> simp [Set.indicator, hd]
  have hm1 : ∀ x, ∫ o, f1 x o ∂P.dataMeasure = P.px x * atomMass P x delta := by
    intro x
    simpa [f1] using atomEvent_integral_eq P hmodel x (by linarith)
  have hsub : ∀ᵐ z ∂iidProduct P n, z ∈ goodᶜ → z ∈ bad := by
    filter_upwards [iidProduct_outcomeSupport P hmodel] with z hz
    intro hzg
    by_contra hzbad
    have hnb0 : z ∉ bad0 := fun h => hzbad (Or.inl (Or.inl h))
    have hnb1 : ∀ x, z ∉ bad1 x := by
      intro x hx
      exact hzbad (Or.inl (Or.inr (Set.mem_iUnion.2 ⟨x, hx⟩)))
    have hnb2 : ∀ x, z ∉ bad2 x := by
      intro x hx
      exact hzbad (Or.inr (Set.mem_iUnion.2 ⟨x, hx⟩))
    have hret : |retainedEstimate B z delta - retainedMean P delta| ≤ b0 := by
      have hnb0' := hnb0
      dsimp [bad0] at hnb0'
      have := le_of_not_gt hnb0'
      have hre : retainedEstimate B z delta = blockAverage B.I0 z f0 := by
        unfold retainedEstimate blockAverage
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        simp [f0, clampUnit, (hz i).1, (hz i).2]
      simpa [hre, hm0] using this
    have hatom : ∀ x, |atomEstimate B z x delta - P.px x * atomMass P x delta| ≤ b1 := by
      intro x
      have hxnot := hnb1 x
      dsimp [bad1] at hxnot
      have hx := le_of_not_gt hxnot
      simpa [bad1, f1, atomEstimate, hm1 x] using hx
    have hlocal : ∀ x,
        GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h →
        |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
          P.mu x delta| ≤
        L * h ^ beta * ∑ i ∈ B.I2,
            |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| +
          t * Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) := by
      intro x hxg
      have hnoise : |∑ i ∈ B.I2,
          interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
            ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A))| ≤
          t * Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2) := by
        exact le_of_not_ge (fun hge => hnb2 x ⟨hxg, hge⟩)
      exact (localRegression_good_error_le_empirical P hmodel hbeta hL B z x
        hdelta hh hupper hlambda hxg).trans (add_le_add_right hnoise _)
    have hmem := clampFunctional_mem_honestInterval_of_deviations P hmodel
      hdelta (by linarith) hh hbeta.le hL.le ht.le hb0pos.le hb1pos.le B z rfl rfl rfl
      hret hatom hlocal
    exact hzg hmem
  have hbad : (iidProduct P n).real bad ≤ alpha := by
    calc
      _ ≤ (iidProduct P n).real bad0 +
          (iidProduct P n).real (⋃ x, bad1 x) +
          (iidProduct P n).real (⋃ x, bad2 x) := by
        exact (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
      _ ≤ alpha / (6 * (J : ℝ)) +
          ∑ x : Fin J, alpha / (6 * (J : ℝ)) +
          ∑ x : Fin J, alpha / (6 * (J : ℝ)) := by
        gcongr
        · exact (measureReal_iUnion_fintype_le bad1).trans
            (Finset.sum_le_sum fun x _ => hbad1 x)
        · exact (measureReal_iUnion_fintype_le bad2).trans
            (Finset.sum_le_sum fun x _ => hbad2 x)
      _ ≤ alpha := by
        have hJR : 0 < (J : ℝ) := by positivity
        have hJone : (1 : ℝ) ≤ J := by exact_mod_cast hJ
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
        nlinarith
  have hfail : (iidProduct P n).real goodᶜ ≤ alpha := by
    exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans hbad
  have hgoodMeas : MeasurableSet good := by
    dsimp [good]
    simp only [honestInterval]
    let center := fun z : Fin n → ClampObs J =>
      totalGramEstimator B z (ellOf beta) kappa cminus cplus delta h
    let radius := fun z : Fin n → ClampObs J =>
      Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
          Real.sqrt (B.I0.card : ℝ) +
        ∑ x : Fin J, stratumRadius B z x (ellOf beta) beta kappa L
          cminus cplus delta h
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
            Real.sqrt (B.I1.card : ℝ))
    have hc : Measurable center := totalGramEstimator_measurable B
      kappa cminus cplus delta h
    have hr : Measurable radius := by
      exact measurable_const.add (Finset.measurable_fun_sum _ fun x _ =>
        honest_stratumRadius_measurable B x beta kappa L cminus cplus delta h
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2))
          (Real.sqrt (Real.log (12 * (J : ℝ) / alpha) / 2) /
            Real.sqrt (B.I1.card : ℝ)))
    exact (measurableSet_le (measurable_const.max (hc.sub hr)) measurable_const).inter
      (measurableSet_le measurable_const (measurable_const.min (hc.add hr)))
  have hadd := measureReal_add_measureReal_compl (μ := iidProduct P n) hgoodMeas
  have huniv : (iidProduct P n).real Set.univ = 1 := by simp
  rw [huniv] at hadd
  change 1 - alpha ≤ (iidProduct P n).real good
  linarith

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
