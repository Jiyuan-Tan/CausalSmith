/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.RegressionVersion
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.EstimatorMeasurable
import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.SampleBlocks
import Causalean.Mathlib.Probability.WeightedProduct
import Causalean.Stat.Concentration.TailBounds.Bernstein

/-! # Design-measurable weights for the local-regression noise term -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set

noncomputable section

/-- [clamp unit is measurable](goal). -/
lemma clampUnit_measurable' : Measurable clampUnit := by
  unfold clampUnit
  fun_prop

/-- [clamp unit lies in the stated closed interval](goal) for [the specified `t` input](hyp:t). -/
lemma clampUnit_mem_Icc (t : ℝ) : clampUnit t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold clampUnit
  constructor <;> simp

/-- [abs clamp unit sub satisfies the stated upper bound](goal) for [the specified `t` input](hyp:t), [the specified `q` input](hyp:q), [the specified `hq` input](hyp:hq). -/
lemma abs_clampUnit_sub_le (t q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |clampUnit t - q| ≤ |t - q| := by
  have hcq : clampUnit q = q := by simp [clampUnit, hq.1, hq.2]
  calc
    |clampUnit t - q| = |clampUnit t - clampUnit q| := by rw [hcq]
    |min 1 (max 0 t) - min 1 (max 0 q)| ≤
        max |(1 : ℝ) - 1| |max 0 t - max 0 q| :=
      abs_min_sub_min_le_max _ _ _ _
    _ ≤ |t - q| := by
      apply max_le
      · simp
      · exact (abs_max_sub_max_le_max (0 : ℝ) t 0 q).trans (by simp)

/-- [clamp outcome almost everywhere satisfies the stated identity](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel). -/
lemma clampOutcome_ae_eq {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    (fun o : ClampObs J => clampUnit o.Y) =ᵐ[P.dataMeasure] fun o => o.Y := by
  filter_upwards [hmodel.outcomeSupport] with o ho
  simp [clampUnit, ho.1, ho.2]

/-- [the stated i.i.d. product outcome support property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel). -/
lemma iidProduct_outcomeSupport {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) :
    ∀ᵐ z ∂iidProduct P n, ∀ i : Fin n, (z i).Y ∈ Set.Icc (0 : ℝ) 1 := by
  let _ := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  apply ae_all_iff.mpr
  intro i
  have hmap : (iidProduct P n).map (Function.eval i) = P.dataMeasure := by
    simpa [iidProduct] using
      (Measure.pi_map_eval (fun _ : Fin n => P.dataMeasure) i)
  have hs := hmodel.outcomeSupport
  rw [← hmap] at hs
  have hYmeas : Measurable (fun o : ClampObs J => o.Y) := clampOutcome_measurable
  exact (ae_map_iff (μ := iidProduct P n) (f := Function.eval i)
    (p := fun o : ClampObs J => o.Y ∈ Set.Icc (0 : ℝ) 1)
    (measurable_pi_apply i).aemeasurable
    (measurableSet_Icc.preimage hYmeas)).mp hs

/-- [the stated clamp outcome cond exp property holds](goal) for [the specified `J` input](hyp:J), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel), [the specified `x₀` input](hyp:x₀). -/
lemma clampOutcome_condExp {J : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin) (x₀ : Fin J) :
    P.dataMeasure[(fun o : ClampObs J => clampUnit o.Y) |
        MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A)) inferInstance] =ᵐ[P.dataMeasure]
      clampRegressionExtension P ∘ fun o => (o.X, o.A) := by
  exact (condExp_congr_ae (clampOutcome_ae_eq P hmodel)).trans
    (clampRegression_condExp P hmodel x₀)

/-- A canonical observation with the specified design and dummy outcome. -/
def clampDesignLift {J : ℕ} (d : Fin J × ℝ) : ClampObs J :=
  ⟨d.1, d.2, 0⟩

/-- [clamp design lift is measurable](goal) for [the specified `J` input](hyp:J). -/
lemma clampDesignLift_measurable {J : ℕ} : Measurable (clampDesignLift (J := J)) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap clampDesignLift
    (MeasurableSpace.comap (fun o : ClampObs J => (o.X, o.A, o.Y)) inferInstance) ≤ _
  rw [MeasurableSpace.comap_comp]
  simpa [Function.comp_def, clampDesignLift] using
    (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)).comap_le

/-- The realized local-polynomial weight regarded as a function only of the
full design vector. -/
def localRegressionDesignWeight {J n ell : ℕ} (B : SplitBlocks n) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (d : Fin n → Fin J × ℝ) (i : Fin n) : ℝ :=
  if i ∈ B.I2 then
    interceptWeight B (fun j => clampDesignLift (d j)) x ell
      kappa cminus cplus delta h i
  else 0

/-- [local regression design weight is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localRegressionDesignWeight_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h : ℝ) :
    Measurable (localRegressionDesignWeight (ell := ell) B x
      kappa cminus cplus delta h) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ B.I2
  · simp only [localRegressionDesignWeight, hi, if_true]
    apply (interceptWeight_measurable B x kappa cminus cplus delta h i).comp
    exact measurable_pi_lambda _ fun j =>
      clampDesignLift_measurable.comp (measurable_pi_apply j)
  · simp [localRegressionDesignWeight, hi]

/-- [the stated local regression design weight apply property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `i` input](hyp:i). -/
lemma localRegressionDesignWeight_apply {J n ell : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J) (kappa cminus cplus delta h : ℝ)
    (i : Fin n) :
    localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
      (Causalean.Mathlib.Probability.designVector (fun o : ClampObs J => (o.X, o.A)) z) i =
      if i ∈ B.I2 then interceptWeight B z x ell kappa cminus cplus delta h i else 0 := by
  classical
  by_cases hi : i ∈ B.I2
  · simp only [localRegressionDesignWeight, hi, if_true,
      Causalean.Mathlib.Probability.designVector]
    unfold interceptWeight GoodGramEvent localCount localGram scaledDose
    rfl
  · simp [localRegressionDesignWeight, hi]

/-- [the stated weighted centered sum local regression property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `P` input](hyp:P), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma weightedCenteredSum_localRegression {J n ell : ℕ} (B : SplitBlocks n)
    (P : ClampLaw J) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) :
    Causalean.Mathlib.Probability.weightedCenteredSum
      (fun o : ClampObs J => (o.X, o.A)) (fun o => o.Y)
      (clampRegressionExtension P)
      (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h) z =
      ∑ i ∈ B.I2, interceptWeight B z x ell kappa cminus cplus delta h i *
        ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A)) := by
  classical
  unfold Causalean.Mathlib.Probability.weightedCenteredSum
  simp_rw [localRegressionDesignWeight_apply (ell := ell)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter]
  rw [Finset.univ_inter]

/-- [the stated weighted centered sum local regression clamp property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `P` input](hyp:P), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma weightedCenteredSum_localRegression_clamp {J n ell : ℕ} (B : SplitBlocks n)
    (P : ClampLaw J) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) :
    Causalean.Mathlib.Probability.weightedCenteredSum
      (fun o : ClampObs J => (o.X, o.A)) (fun o => clampUnit o.Y)
      (clampRegressionExtension P)
      (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h) z =
      ∑ i ∈ B.I2, interceptWeight B z x ell kappa cminus cplus delta h i *
        (clampUnit (z i).Y - clampRegressionExtension P ((z i).X, (z i).A)) := by
  classical
  unfold Causalean.Mathlib.Probability.weightedCenteredSum
  simp_rw [localRegressionDesignWeight_apply (ell := ell)]
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter]
  rw [Finset.univ_inter]

/-- [local regression weight energy satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `hh` input](hyp:hh), [the specified `hlambda` input](hyp:hlambda). -/
lemma localRegression_weight_energy_le {J n ell : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J) (kappa cminus cplus delta h : ℝ)
    (hh : 0 < h) (hlambda : 0 < lambdaStar ell kappa cminus cplus) :
    ∑ i, (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
      (Causalean.Mathlib.Probability.designVector
        (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2 ≤
      4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2 := by
  classical
  simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow, zero_pow (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hg : GoodGramEvent B z x ell kappa cminus cplus delta h
  · have hc := (goodGram_weight_controls B z x kappa cminus cplus delta h
      hh hlambda hg).2.2
    have hN : (1 : ℝ) ≤ localCount B z x delta h := by exact_mod_cast hg.1
    calc
      _ ≤ (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) /
          (localCount B z x delta h : ℝ) := hc
      _ ≤ 4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2 := by
        exact div_le_self (by positivity) hN
  · have hwzero (i : Fin n) :
        interceptWeight B z x ell kappa cminus cplus delta h i = 0 := by
      unfold interceptWeight
      simp [hg]
    simp [hwzero]
    positivity

/-- [local regression weight energy is integrable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `P` input](hyp:P), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `hh` input](hyp:hh), [the specified `hlambda` input](hyp:hlambda). -/
lemma localRegression_weight_energy_integrable {J n ell : ℕ} (B : SplitBlocks n)
    (P : ClampLaw J) [IsProbabilityMeasure P.dataMeasure]
    (x : Fin J) (kappa cminus cplus delta h : ℝ)
    (hh : 0 < h) (hlambda : 0 < lambdaStar ell kappa cminus cplus) :
    Integrable (fun z : Fin n → ClampObs J =>
      ∑ i, (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2) (iidProduct P n) := by
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let w := localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
  have hmeas : Measurable (fun z : Fin n → ClampObs J =>
      ∑ i, (w (Causalean.Mathlib.Probability.designVector
        (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2) := by
    have hw : Measurable w := localRegressionDesignWeight_measurable B x
      kappa cminus cplus delta h
    have hd := Causalean.Mathlib.Probability.measurable_designVector
      (N := n) (fun o : ClampObs J => (o.X, o.A)) clampDesign_measurable
    exact Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (hw.comp hd)).pow_const 2
  apply Integrable.of_bound hmeas.aestronglyMeasurable
    (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2)
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact localRegression_weight_energy_le B z x kappa cminus cplus delta h hh hlambda

/-- [the stated finite product bernoulli count lower tail property holds](goal) for [the specified `N` input](hyp:N), [the specified `X` input](hyp:X), [the specified `P` input](hyp:P), [the specified `q` input](hyp:q), [the specified `hqmeas` input](hyp:hqmeas), [the specified `hq01` input](hyp:hq01), [the specified `hN` input](hyp:hN), [the specified `p` input](hyp:p), [the specified `hp` input](hyp:hp), [the specified `hmean` input](hyp:hmean). -/
lemma finiteProduct_bernoulliCount_lower_tail
    {N : ℕ} {X : Type*} [MeasurableSpace X]
    (P : Measure X) [IsProbabilityMeasure P] (q : X → ℝ)
    (hqmeas : Measurable q) (hq01 : ∀ x, q x = 0 ∨ q x = 1)
    (hN : 0 < N) (p : ℝ) (hp : 0 < p) (hmean : ∫ x, q x ∂P = p) :
    (Measure.pi (fun _ : Fin N => P)).real
      {z | ∑ i, q (z i) ≤ (N : ℝ) * p / 2} ≤
        2 * Real.exp (-((N : ℝ) * p) / 20) := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin N => P)) := inferInstance
  have hqIcc : ∀ x, q x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    rcases hq01 x with hx | hx <;> simp [hx]
  have hqint : Integrable q P := by
    refine Integrable.of_bound hqmeas.aestronglyMeasurable 1 ?_
    filter_upwards with x
    rcases hq01 x with hx | hx <;> simp [hx]
  have hp_le : p ≤ 1 := by
    calc
      p = ∫ x, q x ∂P := hmean.symm
      _ ≤ ∫ _x, (1 : ℝ) ∂P := integral_mono_ae hqint (integrable_const 1)
        (ae_of_all _ fun x => (hqIcc x).2)
      _ = 1 := by simp
  have henvelope : ∀ᵐ x ∂P, |q x - ∫ y, q y ∂P| ≤ 1 := by
    filter_upwards with x
    rw [hmean]
    exact abs_le.2 ⟨by linarith [(hqIcc x).1], by linarith [(hqIcc x).2]⟩
  have hvar : ∫ x, (q x - ∫ y, q y ∂P) ^ 2 ∂P ≤ p := by
    rw [hmean]
    have hq2int : Integrable (fun x => q x ^ 2) P := by
      exact Integrable.of_bound (hqmeas.pow_const 2).aestronglyMeasurable 1
        (ae_of_all _ fun x => by rcases hq01 x with hx | hx <;> simp [hx])
    calc
      ∫ x, (q x - p) ^ 2 ∂P =
          (∫ x, q x ^ 2 ∂P) - 2 * p * (∫ x, q x ∂P) + p ^ 2 := by
        rw [show (fun x => (q x - p) ^ 2) =
            fun x => q x ^ 2 - 2 * p * q x + p ^ 2 by funext x; ring]
        integral_linearity
        rw [integral_const]
        simp
      _ = p - p ^ 2 := by
        rw [show (∫ x, q x ^ 2 ∂P) = p by
          rw [← hmean]
          apply integral_congr_ae
          filter_upwards with x
          rcases hq01 x with hx | hx <;> simp [hx]]
        rw [hmean]
        ring
      _ ≤ p := by nlinarith [sq_nonneg p]
  let g : Unit → X → ℝ := fun _ => q
  let b : Unit → ℝ := fun _ => 1
  let sigma2 : Unit → ℝ := fun _ => p
  let eta : Unit → ℝ := fun _ => (N : ℝ) * p / 2
  have hbern := Causalean.Stat.Concentration.iid_sum_bernstein_union_bound
    P g (fun _ => hqmeas) (fun _ => hqint) b sigma2 eta
    (fun _ => by simp [b]) (fun _ => hp.le) (fun _ => by dsimp [eta]; positivity)
    hN (fun _ => by simpa [g] using henvelope) (fun _ => by simpa [g] using hvar)
  calc
    _ ≤ (Measure.pi (fun _ : Fin N => P)).real
        {z | ∃ a : Unit, eta a ≤
          |(∑ i, g a (z i)) - (N : ℝ) * ∫ x, g a x ∂P|} := by
      refine measureReal_mono ?_ (measure_ne_top _ _)
      intro z hz
      refine ⟨(), ?_⟩
      simp only [eta, g, hmean]
      change (∑ i, q (z i)) ≤ (N : ℝ) * p / 2 at hz
      have hdiff : (∑ i, q (z i)) - (N : ℝ) * p ≤ 0 := by
        have hNp : 0 ≤ (N : ℝ) * p := by positivity
        linarith
      rw [abs_of_nonpos hdiff]
      linarith
    _ ≤ ∑ a : Unit, 2 * Real.exp
        (-(eta a) ^ 2 / (2 * (2 * (N : ℝ) * sigma2 a + b a * eta a))) := hbern
    _ = 2 * Real.exp (-((N : ℝ) * p) / 20) := by
      simp only [Fintype.sum_unique, eta, sigma2, b]
      have hNp : 0 < (N : ℝ) * p := mul_pos (by exact_mod_cast hN) hp
      congr 2
      field_simp
      ring

/-- [the stated i.i.d. block product law property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `P` input](hyp:P), [the specified `hsampling` input](hyp:hsampling), [the specified `I` input](hyp:I). -/
lemma iid_block_product_law' {J n : ℕ} (P : ClampLaw J)
    (hsampling : IidSampling P n) (I : Finset (Fin n)) :
    (iidProduct P n).map (fun z => fun j : Fin I.card =>
      z ((I.orderIsoOfFin rfl) j)) =
      Measure.pi (fun _ : Fin I.card => P.dataMeasure) := by
  let _ : IsProbabilityMeasure P.dataMeasure := hsampling.1
  simpa [iidProduct] using block_reindexed_law_eq P.dataMeasure I

/-- [the stated local count lower tail property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `P` input](hyp:P), [the specified `hsampling` input](hyp:hsampling), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `p` input](hyp:p), [the specified `hh` input](hyp:hh), [the specified `hp` input](hyp:hp), [the specified `hmean` input](hyp:hmean), [the specified `hcard` input](hyp:hcard). -/
lemma localCount_lower_tail {J n : ℕ} (P : ClampLaw J)
    (hsampling : IidSampling P n) (B : SplitBlocks n) (x : Fin J)
    (delta h p : ℝ) (hh : 0 < h) (hp : 0 < p)
    (hmean : ∫ o, localWindowWeight x delta h o ∂P.dataMeasure = p)
    (hcard : 0 < B.I2.card) :
    (iidProduct P n).real {z |
      (localCount B z x delta h : ℝ) ≤ (B.I2.card : ℝ) * p / 2} ≤
        2 * Real.exp (-((B.I2.card : ℝ) * p) / 20) := by
  letI : IsProbabilityMeasure P.dataMeasure := hsampling.1
  let F : (Fin n → ClampObs J) → (Fin B.I2.card → ClampObs J) :=
    fun z j => z ((B.I2.orderIsoOfFin rfl) j)
  let q := localWindowWeight x delta h
  have hF : Measurable F := measurable_pi_lambda _ fun j => measurable_pi_apply _
  have hqmeas : Measurable q := measurable_localWindowWeight x delta h
  have hq01 : ∀ o, q o = 0 ∨ q o = 1 := by
    intro o
    unfold q localWindowWeight
    split_ifs <;> simp
  let E : Set (Fin B.I2.card → ClampObs J) :=
    {w | ∑ j, q (w j) ≤ (B.I2.card : ℝ) * p / 2}
  have hE : MeasurableSet E := measurableSet_le
    (Finset.measurable_fun_sum _ fun j _ => hqmeas.comp (measurable_pi_apply j))
    measurable_const
  have hsum (z : Fin n → ClampObs J) :
      (∑ j, q (F z j)) = (localCount B z x delta h : ℝ) := by
    change (∑ j : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) j))) = _
    rw [show (∑ j : Fin B.I2.card, q (z ((B.I2.orderIsoOfFin rfl) j))) =
        ∑ i ∈ B.I2, q (z i) by
      calc
        _ = ∑ i : B.I2, q (z i) := Equiv.sum_comp
          (B.I2.orderIsoOfFin rfl).toEquiv (fun i : B.I2 => q (z i))
        _ = _ := (Finset.sum_subtype B.I2 (fun _ => Iff.rfl) (fun i => q (z i))).symm]
    unfold q localWindowWeight localCount
    simp_rw [scaledDose_mem_Icc_iff hh]
    norm_cast
  have hset : {z : Fin n → ClampObs J |
      (localCount B z x delta h : ℝ) ≤ (B.I2.card : ℝ) * p / 2} = F ⁻¹' E := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    change (localCount B z x delta h : ℝ) ≤ _ ↔ (∑ j, q (F z j)) ≤ _
    rw [hsum]
  rw [hset, measureReal_def, ← Measure.map_apply hF hE,
    iid_block_product_law' P hsampling B.I2]
  exact finiteProduct_bernoulliCount_lower_tail P.dataMeasure q hqmeas hq01
    hcard p hp hmean

/-- [local regression weight energy integral satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `P` input](hyp:P), [the specified `hsampling` input](hyp:hsampling), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `p` input](hyp:p), [the specified `hh` input](hyp:hh), [the specified `hlambda` input](hyp:hlambda), [the specified `hp` input](hyp:hp), [the specified `hcard` input](hyp:hcard), [the specified `hmean` input](hyp:hmean). -/
lemma localRegression_weight_energy_integral_le {J n ell : ℕ}
    (P : ClampLaw J) (hsampling : IidSampling P n) (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h p : ℝ)
    (hh : 0 < h) (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hp : 0 < p) (hcard : 0 < B.I2.card)
    (hmean : ∫ o, localWindowWeight x delta h o ∂P.dataMeasure = p) :
    (∫ z, ∑ i,
      (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2 ∂iidProduct P n) ≤
      2 * (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) /
          ((B.I2.card : ℝ) * p) +
        2 * (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) *
          Real.exp (-((B.I2.card : ℝ) * p) / 20) := by
  letI : IsProbabilityMeasure P.dataMeasure := hsampling.1
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let K := 4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2
  let mp := (B.I2.card : ℝ) * p
  let energy : (Fin n → ClampObs J) → ℝ := fun z => ∑ i,
    (localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
      (Causalean.Mathlib.Probability.designVector
        (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2
  let low : Set (Fin n → ClampObs J) :=
    {z | (localCount B z x delta h : ℝ) ≤ mp / 2}
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hmp : 0 < mp := by dsimp [mp]; positivity
  have henergyInt : Integrable energy (iidProduct P n) := by
    exact localRegression_weight_energy_integrable B P x kappa cminus cplus delta h
      hh hlambda
  have hlow : MeasurableSet low := by
    exact measurableSet_le
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (localCount_measurable B x delta h)) measurable_const
  have hpoint (z : Fin n → ClampObs J) :
      energy z ≤ 2 * K / mp + K * low.indicator (fun _ => (1 : ℝ)) z := by
    by_cases hzlow : z ∈ low
    · have he := localRegression_weight_energy_le B z x kappa cminus cplus
        delta h hh hlambda
      simp only [Set.indicator_of_mem hzlow, mul_one]
      have hterm : 0 ≤ 2 * K / mp := by positivity
      exact he.trans (by dsimp [energy, K] at he ⊢; linarith)
    · simp only [Set.indicator_of_notMem hzlow, mul_zero, add_zero]
      by_cases hg : GoodGramEvent B z x ell kappa cminus cplus delta h
      · have he := (goodGram_weight_controls B z x kappa cminus cplus delta h
          hh hlambda hg).2.2
        have hN : mp / 2 < (localCount B z x delta h : ℝ) := by
          exact lt_of_not_ge hzlow
        have hNpos : 0 < (localCount B z x delta h : ℝ) := by exact_mod_cast hg.1
        calc
          energy z = ∑ i ∈ B.I2,
              (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2 := by
            dsimp [energy]
            simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow,
              zero_pow (by norm_num : 2 ≠ 0)]
            rw [← Finset.sum_filter]
            simp
          _ ≤ K / (localCount B z x delta h : ℝ) := by simpa [K] using he
          _ ≤ 2 * K / mp := by
            rw [div_le_iff₀ hNpos, div_mul_eq_mul_div, le_div_iff₀ hmp]
            have hmul := mul_le_mul_of_nonneg_left hN.le hK
            nlinarith
      · have hwzero (i : Fin n) :
            localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
              (Causalean.Mathlib.Probability.designVector
                (fun o : ClampObs J => (o.X, o.A)) z) i = 0 := by
          rw [localRegressionDesignWeight_apply (ell := ell)]
          split_ifs
          · unfold interceptWeight
            simp [hg]
          · rfl
        simp [energy, hwzero]
        positivity
  have hrhsInt : Integrable (fun z => 2 * K / mp +
      K * low.indicator (fun _ => (1 : ℝ)) z) (iidProduct P n) :=
    (integrable_const _).add ((integrable_const 1).indicator hlow |>.const_mul K)
  calc
    ∫ z, energy z ∂iidProduct P n ≤
        ∫ z, (2 * K / mp + K * low.indicator (fun _ => (1 : ℝ)) z)
          ∂iidProduct P n := integral_mono henergyInt hrhsInt hpoint
    _ = 2 * K / mp + K * (iidProduct P n).real low := by
      rw [integral_add, integral_const, integral_const_mul]
      · rw [integral_indicator hlow, integral_const]
        simp [measureReal_def, hlow]
      · exact integrable_const _
      · exact (integrable_const 1).indicator hlow |>.const_mul K
    _ ≤ 2 * K / mp + K * (2 * Real.exp (-mp / 20)) := by
      gcongr
      simpa [low, mp] using
        localCount_lower_tail P hsampling B x delta h p hh hp hmean hcard
    _ = 2 * K / mp + 2 * K * Real.exp (-mp / 20) := by ring
    _ = _ := by simp [K, mp]

/-- [local regression centered absolute-error satisfies the stated upper bound](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `P` input](hyp:P), [the specified `beta` input](hyp:beta), [the specified `kappa` input](hyp:kappa), [the specified `L` input](hyp:L), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `pmin` input](hyp:pmin), [the specified `hmodel` input](hyp:hmodel), [the specified `hsampling` input](hyp:hsampling), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `p` input](hyp:p), [the specified `hh` input](hyp:hh), [the specified `hlambda` input](hyp:hlambda), [the specified `hkappa` input](hyp:hkappa), [the specified `hcplus` input](hyp:hcplus), [the specified `hpmin` input](hyp:hpmin), [the specified `hp` input](hyp:hp), [the specified `hcard` input](hyp:hcard), [the specified `hmean` input](hyp:hmean). -/
lemma localRegression_centered_l1_le {J n ell : ℕ}
    (P : ClampLaw J) {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hsampling : IidSampling P n) (B : SplitBlocks n) (x : Fin J)
    (delta h p : ℝ) (hh : 0 < h)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hkappa : 0 ≤ kappa) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (hp : 0 < p) (hcard : 0 < B.I2.card)
    (hmean : ∫ o, localWindowWeight x delta h o ∂P.dataMeasure = p) :
    (∫ z, |∑ i ∈ B.I2,
      interceptWeight B z x ell kappa cminus cplus delta h i *
        (clampUnit (z i).Y - clampRegressionExtension P ((z i).X, (z i).A))|
      ∂iidProduct P n) ≤
      (1 / 2 : ℝ) * Real.sqrt
        (2 * (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) /
            ((B.I2.card : ℝ) * p) +
          2 * (4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2) *
            Real.exp (-((B.I2.card : ℝ) * p) / 20)) := by
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let design : ClampObs J → Fin J × ℝ := fun o => (o.X, o.A)
  let Y : ClampObs J → ℝ := fun o => clampUnit o.Y
  let w := localRegressionDesignWeight (ell := ell) B x kappa cminus cplus delta h
  let S := Causalean.Mathlib.Probability.weightedCenteredSum design Y
    (clampRegressionExtension P) w
  let energy : (Fin n → ClampObs J) → ℝ := fun z => ∑ i,
    (w (Causalean.Mathlib.Probability.designVector design z) i) ^ 2
  have hw : Measurable w := localRegressionDesignWeight_measurable B x
    kappa cminus cplus delta h
  have hd : Measurable design := clampDesign_measurable
  have hY : Measurable Y := clampUnit_measurable'.comp clampOutcome_measurable
  have hmD := clampRegressionExtension_measurable P hmodel.holder
  have henergyInt : Integrable energy (iidProduct P n) := by
    simpa [energy, w, design] using
      localRegression_weight_energy_integrable B P x kappa cminus cplus delta h hh hlambda
  have hSmeas : Measurable S := by
    dsimp [S]
    unfold Causalean.Mathlib.Probability.weightedCenteredSum
    exact Finset.measurable_fun_sum _ fun i _ =>
      ((measurable_pi_apply i).comp
        (hw.comp (Causalean.Mathlib.Probability.measurable_designVector design hd))).mul
      ((hY.comp (measurable_pi_apply i)).sub
        (hmD.comp (hd.comp (measurable_pi_apply i))))
  have hSsq : Integrable (fun z => (S z) ^ 2) (iidProduct P n) := by
    refine Integrable.mono (henergyInt.const_mul (n : ℝ))
      (hSmeas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _))]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => w (Causalean.Mathlib.Probability.designVector design z) i)
      (fun i => Y (z i) - clampRegressionExtension P (design (z i)))
    have hr : ∑ i, (Y (z i) - clampRegressionExtension P (design (z i))) ^ 2 ≤
        (n : ℝ) := by
      calc
        _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hYi := clampUnit_mem_Icc (z i).Y
          have hmi := clampRegressionExtension_mem_Icc P hmodel.holder (design (z i))
          have hY0 : 0 ≤ Y (z i) := by simpa [Y] using hYi.1
          have hY1 : Y (z i) ≤ 1 := by simpa [Y] using hYi.2
          have hm0 : 0 ≤ clampRegressionExtension P (design (z i)) := hmi.1
          have hm1 : clampRegressionExtension P (design (z i)) ≤ 1 := hmi.2
          have hlo : -(1 : ℝ) ≤ Y (z i) - clampRegressionExtension P (design (z i)) := by
            linarith
          have hhi : Y (z i) - clampRegressionExtension P (design (z i)) ≤ 1 := by
            linarith
          nlinarith [mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)]
        _ = n := by simp
    calc
      S z ^ 2 ≤ energy z * ∑ i,
          (Y (z i) - clampRegressionExtension P (design (z i))) ^ 2 := hcs
      _ ≤ energy z * n := mul_le_mul_of_nonneg_left hr
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ = n * energy z := mul_comm _ _
  have hbase := Causalean.Mathlib.Probability.product_weighted_centered_l1_le
    P.dataMeasure design hd Y hY (fun o => (clampUnit_mem_Icc o.Y).1)
    (fun o => (clampUnit_mem_Icc o.Y).2) (clampRegressionExtension P) hmD
    (clampOutcome_condExp P hmodel x) w hw henergyInt hSsq
  rw [show (∫ z, |∑ i ∈ B.I2,
      interceptWeight B z x ell kappa cminus cplus delta h i *
        (clampUnit (z i).Y - clampRegressionExtension P ((z i).X, (z i).A))|
      ∂iidProduct P n) = ∫ z, |S z| ∂iidProduct P n by
    apply integral_congr_ae
    filter_upwards with z
    congr 1
    simpa [S, design, Y, w] using
      (weightedCenteredSum_localRegression_clamp (ell := ell) B P z x
        kappa cminus cplus delta h).symm]
  refine hbase.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
  exact localRegression_weight_energy_integral_le P hsampling B x
    kappa cminus cplus delta h p hh hlambda hp hcard hmean

/-- The information-balance identity expressed as the reciprocal effective
sample size used by the local-regression variance bound. The result uses [the `hh` condition](hyp:hh), [the `hb` condition](hyp:hb). [This is the stated conclusion](goal).
-/
lemma effectiveSampleSize_eq_rpow {n : ℕ} {beta kappa delta h : ℝ}
    (hh : 0 < h)
    (hb : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1) :
    (n : ℝ) * h * (delta + h) ^ kappa = h ^ (-2 * beta) := by
  have hp := Real.rpow_add hh (2 * beta) 1
  rw [Real.rpow_one] at hp
  have hnhe : (n : ℝ) * (h ^ (2 * beta) * h) * (delta + h) ^ kappa = 1 := by
    rw [← hp]
    exact hb
  have hpow : 0 < h ^ (2 * beta) := Real.rpow_pos_of_pos hh _
  rw [show -2 * beta = -(2 * beta) by ring, Real.rpow_neg hh.le,
    inv_eq_one_div]
  apply (eq_div_iff hpow.ne').2
  nlinarith

/-- [the stated exp neg scaled bound inv property holds](goal) for [the specified `t` input](hyp:t), [the specified `ht` input](hyp:ht). -/
lemma exp_neg_scaled_le_inv {t : ℝ} (ht : 0 < t) :
    Real.exp (-t / 20) ≤ 20 / t := by
  have hu : 0 < t / 20 := div_pos ht (by norm_num)
  have he : t / 20 ≤ Real.exp (t / 20) :=
    le_trans (le_add_of_nonneg_right zero_le_one) (Real.add_one_le_exp (t / 20))
  have hi : Real.exp (-(t / 20)) ≤ (t / 20)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos _) hu).2 he
  rw [inv_div] at hi
  simpa [div_eq_mul_inv] using hi

/-- A deterministic conversion of the count-weighted noise expression to the
balanced bandwidth rate.  The constants include the split-block factor eight
and the elementary exponential bound `exp (-t/20) ≤ 20/t`. The result uses [the `hn` condition](hyp:hn), [the `hh` condition](hyp:hh), [the `hD` condition](hyp:hD), [the `hK` condition](hyp:hK), [the `hm` condition](hyp:hm), [the `hp` condition](hyp:hp), [the `hb` condition](hyp:hb). [This is the stated conclusion](goal).
-/
lemma balancedEffectiveSample_sqrt_le {n : ℕ}
    {beta kappa delta h p m D K : ℝ}
    (hn : 0 < n) (hh : 0 < h) (hD : 0 ≤ D) (hK : 0 < K)
    (hm : (n : ℝ) / 8 ≤ m)
    (hp : K * h * (delta + h) ^ kappa ≤ p)
    (hb : (n : ℝ) * h ^ (2 * beta + 1) * (delta + h) ^ kappa = 1) :
    Real.sqrt (2 * D / (m * p) + 2 * D * Real.exp (-(m * p) / 20)) ≤
      Real.sqrt (336 * D / K) * h ^ beta := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have heff := effectiveSampleSize_eq_rpow hh hb
  have hbase : 0 < K * h * (delta + h) ^ kappa := by
    have heffpos : 0 < (n : ℝ) * h * (delta + h) ^ kappa := by
      rw [heff]
      exact Real.rpow_pos_of_pos hh _
    have htail : 0 < (delta + h) ^ kappa := by
      have heffpos' : 0 < (delta + h) ^ kappa * ((n : ℝ) * h) := by
        simpa [mul_comm] using heffpos
      exact pos_of_mul_pos_left heffpos' (mul_nonneg hnR.le hh.le)
    positivity
  have hp0 : 0 < p := hbase.trans_le hp
  have hm0 : 0 < m := lt_of_lt_of_le (div_pos hnR (by norm_num)) hm
  have ht0 : 0 < m * p := mul_pos hm0 hp0
  have htLower : (K / 8) * h ^ (-2 * beta) ≤ m * p := by
    calc
      (K / 8) * h ^ (-2 * beta) =
          ((n : ℝ) / 8) * (K * h * (delta + h) ^ kappa) := by
            rw [← heff]
            ring
      _ ≤ m * p := mul_le_mul hm hp (by positivity) (by positivity)
  have hinv : (m * p)⁻¹ ≤ (8 / K) * h ^ (2 * beta) := by
    have hi := (inv_le_inv₀ ht0
      (by positivity : 0 < (K / 8) * h ^ (-2 * beta))).2 htLower
    rw [show -2 * beta = -(2 * beta) by ring, Real.rpow_neg hh.le] at hi
    calc
      (m * p)⁻¹ ≤ ((K / 8) * (h ^ (2 * beta))⁻¹)⁻¹ := hi
      _ = (8 / K) * h ^ (2 * beta) := by field_simp
  have hexp : Real.exp (-(m * p) / 20) ≤ 20 * (m * p)⁻¹ := by
    have he := exp_neg_scaled_le_inv ht0
    simpa [div_eq_mul_inv] using he
  have hinside : 2 * D / (m * p) + 2 * D * Real.exp (-(m * p) / 20) ≤
      (336 * D / K) * h ^ (2 * beta) := by
    rw [div_eq_mul_inv]
    calc
      2 * D * (m * p)⁻¹ + 2 * D * Real.exp (-(m * p) / 20) ≤
          2 * D * (m * p)⁻¹ + 2 * D * (20 * (m * p)⁻¹) := by gcongr
      _ = 42 * D * (m * p)⁻¹ := by ring
      _ ≤ 42 * D * ((8 / K) * h ^ (2 * beta)) := by gcongr
      _ = (336 * D / K) * h ^ (2 * beta) := by ring
  calc
    Real.sqrt (2 * D / (m * p) + 2 * D * Real.exp (-(m * p) / 20)) ≤
        Real.sqrt ((336 * D / K) * h ^ (2 * beta)) := Real.sqrt_le_sqrt hinside
    _ = Real.sqrt (336 * D / K) * Real.sqrt (h ^ (2 * beta)) := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ 336 * D / K)]
    _ = Real.sqrt (336 * D / K) * h ^ beta := by
      congr 1
      rw [show 2 * beta = beta * 2 by ring, Real.rpow_mul hh.le, Real.rpow_two]
      exact (Real.sqrt_sq_eq_abs (h ^ beta)).trans
        (abs_of_nonneg (Real.rpow_nonneg hh.le _))

private lemma weightedPolynomial_reproduce {ι : Type} [Fintype ι]
    {ell : ℕ} (I : Finset ι) (w a : ι → ℝ) (c : ℕ → ℝ)
    (delta h : ℝ) (hh : 0 < h)
    (hrepro : ∀ j : Fin (ell + 1),
      ∑ i ∈ I, w i * ((a i - delta) / h) ^ (j : ℕ) =
        if j = 0 then 1 else 0) :
    ∑ i ∈ I, w i *
      (∑ j ∈ Finset.range (ell + 1), c j * (a i - delta) ^ j) = c 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ j ∈ Finset.range (ell + 1),
        ∑ i ∈ I, w i * (c j * (a i - delta) ^ j)) =
        ∑ j ∈ Finset.range (ell + 1), c j * h ^ j *
          (if j = 0 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hre := hrepro ⟨j, Finset.mem_range.mp hj⟩
      have hre' : ∑ i ∈ I, w i * ((a i - delta) / h) ^ j =
          if j = 0 then 1 else 0 := by
        simpa [Fin.ext_iff] using hre
      rw [← hre', Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [div_pow]
      field_simp [hh.ne']
    _ = c 0 := by simp

/-- On a good realized Gram event, the conditional mean part of the local
polynomial estimator has the stated Hölder bias. The result uses [the `hmodel` condition](hyp:hmodel), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
lemma localRegression_holderBias_le {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hbeta : 0 < beta) (hL : 0 < L)
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus)
    (hgood : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h) :
    |(∑ i ∈ B.I2, interceptWeight B z x (ellOf beta) kappa cminus cplus
        delta h i * clampRegressionExtension P ((z i).X, (z i).A)) -
      P.mu x delta| ≤
      (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta := by
  classical
  let ell := ellOf beta
  let w : Fin n → ℝ := fun i =>
    interceptWeight B z x ell kappa cminus cplus delta h i
  let T : ℝ → ℝ := fun a => ∑ j ∈ Finset.range (ell + 1),
    (iteratedDerivWithin j (P.mu x) (Set.Icc (0 : ℝ) 1) delta /
      (Nat.factorial j : ℝ)) * (a - delta) ^ j
  have hdeltaI : delta ∈ Set.Icc (0 : ℝ) 1 := ⟨hdelta, by linarith⟩
  have hrepro := (goodGram_weight_controls B z x kappa cminus cplus delta h
    hh hlambda hgood).1
  have hpoly : ∑ i ∈ B.I2, w i * T (z i).A = P.mu x delta := by
    have hp := weightedPolynomial_reproduce B.I2 w (fun i => (z i).A)
      (fun j => iteratedDerivWithin j (P.mu x) (Set.Icc (0 : ℝ) 1) delta /
        (Nat.factorial j : ℝ)) delta h hh hrepro
    simpa [T, ell, w] using hp
  have hrewrite :
      (∑ i ∈ B.I2, w i * clampRegressionExtension P ((z i).X, (z i).A)) -
          P.mu x delta =
        ∑ i ∈ B.I2, w i * (P.mu x (z i).A - T (z i).A) := by
    rw [← hpoly, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
    · have hu := ha.2
      have hAlo : delta ≤ (z i).A := by
        have := (div_nonneg_iff.mp hu.1).resolve_right
          (fun hn => (not_lt_of_ge hn.2 hh))
        exact sub_nonneg.mp this.1
      have hAhi : (z i).A ≤ delta + h := by
        have := (div_le_iff₀ hh).mp hu.2
        linarith
      have hAI : (z i).A ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨hdelta.trans hAlo, hAhi.trans hupper⟩
      rw [show (z i).X = x from ha.1, clampRegressionExtension_eq P x hAI]
      simp only [w]
      ring
    · have hw0 : w i = 0 := by
        dsimp [w, ell]
        exact interceptWeight_eq_zero_of_inactive B z x (ellOf beta)
          kappa cminus cplus delta h i hgood (fun hi => ha ⟨hi.2.1, hi.2.2⟩)
      simp [hw0]
  rw [hrewrite]
  calc
    |∑ i ∈ B.I2, w i * (P.mu x (z i).A - T (z i).A)| ≤
        ∑ i ∈ B.I2, |w i| * |P.mu x (z i).A - T (z i).A| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans_eq (by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul])
    _ ≤ ∑ i ∈ B.I2, |w i| * (L * h ^ beta) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases ha : (z i).X = x ∧ scaledDose delta h (z i) ∈ Set.Icc (0 : ℝ) 1
      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hu := ha.2
        have hAlo : delta ≤ (z i).A := by
          have hs := (div_nonneg_iff.mp hu.1).resolve_right
            (fun hn => (not_lt_of_ge hn.2 hh))
          exact sub_nonneg.mp hs.1
        have hAhi : (z i).A ≤ delta + h := by
          have hs := (div_le_iff₀ hh).mp hu.2
          linarith
        have hAI : (z i).A ∈ Set.Icc (0 : ℝ) 1 :=
          ⟨hdelta.trans hAlo, hAhi.trans hupper⟩
        have hrem := (hmodel.holder x).2.2.2 delta hdeltaI (z i).A hAI
        have habs : |(z i).A - delta| ≤ h := by
          rw [abs_of_nonneg (sub_nonneg.mpr hAlo)]
          linarith
        have hpw := Real.rpow_le_rpow (abs_nonneg _) habs hbeta.le
        have hrem' : |P.mu x (z i).A - T (z i).A| ≤
            L * |(z i).A - delta| ^ beta := by
          simpa [T, ell, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hrem
        exact hrem'.trans (mul_le_mul_of_nonneg_left hpw hL.le)
      · have hw0 : w i = 0 := by
          dsimp [w, ell]
          exact interceptWeight_eq_zero_of_inactive B z x (ellOf beta)
            kappa cminus cplus delta h i hgood (fun hi => ha ⟨hi.2.1, hi.2.2⟩)
        simp [hw0]
    _ = (∑ i ∈ B.I2, |w i|) * (L * h ^ beta) := by
      rw [Finset.sum_mul]
    _ ≤ (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
          lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta := by
      have hl1 := (goodGram_weight_controls B z x kappa cminus cplus delta h
        hh hlambda hgood).2.1
      have hfac : 0 ≤ L * h ^ beta := mul_nonneg hL.le (Real.rpow_nonneg hh.le _)
      simpa [w, ell, mul_assoc] using mul_le_mul_of_nonneg_right hl1 hfac

/-- Pointwise good-event decomposition of local-regression error into its
centered stochastic sum and deterministic Hölder bias. The result uses [the `hmodel` condition](hyp:hmodel), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
lemma localRegression_good_error_le {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hbeta : 0 < beta) (hL : 0 < L)
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus)
    (hgood : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h) :
    |clampUnit (∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          clampUnit (z i).Y) - P.mu x delta| ≤
      |∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          (clampUnit (z i).Y -
            clampRegressionExtension P ((z i).X, (z i).A))| +
      (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta := by
  have hmu := (hmodel.holder x).2.1 delta ⟨hdelta, by linarith⟩
  refine (abs_clampUnit_sub_le _ _ hmu).trans ?_
  have htri := abs_add_le
    (∑ i ∈ B.I2,
      interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
        (clampUnit (z i).Y -
          clampRegressionExtension P ((z i).X, (z i).A)))
    ((∑ i ∈ B.I2,
      interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
        clampRegressionExtension P ((z i).X, (z i).A)) - P.mu x delta)
  have hid :
      (∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          clampUnit (z i).Y) - P.mu x delta =
      (∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          (clampUnit (z i).Y -
            clampRegressionExtension P ((z i).X, (z i).A))) +
      ((∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          clampRegressionExtension P ((z i).X, (z i).A)) - P.mu x delta) := by
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact htri.trans (add_le_add_right
    (localRegression_holderBias_le P hmodel hbeta hL B z x hdelta hh hupper
      hlambda hgood) _)

/-- The centered local-regression noise at the information-balanced bandwidth
is uniformly of order `h^beta`. The result uses [the `hmodel` condition](hyp:hmodel), [the `hsampling` condition](hyp:hsampling), [the `hn` condition](hyp:hn), [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hbalance` condition](hyp:hbalance). [This is the stated conclusion](goal).
-/
lemma localRegression_centered_balanced_l1_le {J n ell : ℕ}
    (P : ClampLaw J) {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hsampling : IidSampling P n) (B : SplitBlocks n) (x : Fin J)
    (hn : 8 ≤ n) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hcminus : 0 < cminus) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hbalance : (n : ℝ) * h ^ (2 * beta + 1) *
      (delta + h) ^ kappa = 1) :
    (∫ z, |∑ i ∈ B.I2,
      interceptWeight B z x ell kappa cminus cplus delta h i *
        (clampUnit (z i).Y -
          clampRegressionExtension P ((z i).X, (z i).A))| ∂iidProduct P n) ≤
      (1 / 2) * Real.sqrt
        (336 * (4 * (ell + 1 : ℝ) /
          lambdaStar ell kappa cminus cplus ^ 2) /
          (pmin * cminus / (2 * (2 : ℝ) ^ kappa))) * h ^ beta := by
  let p := ∫ o, localWindowWeight x delta h o ∂P.dataMeasure
  let D := 4 * (ell + 1 : ℝ) / lambdaStar ell kappa cminus cplus ^ 2
  let K := pmin * cminus / (2 * (2 : ℝ) ^ kappa)
  have hK : 0 < K := by dsimp [K]; positivity
  have hpLower : K * h * (delta + h) ^ kappa ≤ p := by
    have hl := localWindowWeight_integral_lower P hmodel hkappa hcminus hcplus
      hpmin x hdelta hh hupper
    have hdh : 0 < delta + h := by linarith
    have hrpow : ((delta + h) / 2) ^ kappa =
        (delta + h) ^ kappa / (2 : ℝ) ^ kappa := by
      rw [Real.div_rpow hdh.le (by norm_num : (0 : ℝ) ≤ 2)]
    rw [hrpow] at hl
    dsimp [K, p]
    convert hl using 1 <;> ring
  have hp0 : 0 < p := lt_of_lt_of_le (by
    exact mul_pos (mul_pos hK hh)
      (Real.rpow_pos_of_pos (by linarith) _)) hpLower
  have hcardNat : 0 < B.I2.card := lt_of_lt_of_le (by omega) B.card_I2
  have hcard : (n : ℝ) / 8 ≤ (B.I2.card : ℝ) := by
    have hqcard := B.card_I2
    have hncard : n ≤ 8 * B.I2.card := by omega
    have hncardR : (n : ℝ) ≤ 8 * (B.I2.card : ℝ) := by exact_mod_cast hncard
    linarith
  have hraw := localRegression_centered_l1_le P hmodel hsampling B x delta h p
    hh hlambda hkappa hcplus hpmin hp0 hcardNat rfl
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrate := balancedEffectiveSample_sqrt_le (D := D) (K := K)
    (p := p) (m := (B.I2.card : ℝ)) (Nat.zero_lt_of_lt hn) hh hD hK
    hcard hpLower hbalance
  dsimp [D, K] at hrate
  exact hraw.trans ((mul_le_mul_of_nonneg_left hrate
    (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans_eq (by ring))

/-- Integrated Good/bad decomposition for one stratum's stabilized local
regression.  The only exceptional contribution is the real probability of a
bad Gram event. The result uses [the `hmodel` condition](hyp:hmodel), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda). [This is the stated conclusion](goal).
-/
lemma localRegression_risk_le_noise_bias_bad {J n : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hbeta : 0 < beta) (hL : 0 < L)
    (B : SplitBlocks n) (x : Fin J)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus) :
    (∫ z, |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus
        delta h - P.mu x delta| ∂iidProduct P n) ≤
      (∫ z, |∑ i ∈ B.I2,
        interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
          (clampUnit (z i).Y -
            clampRegressionExtension P ((z i).X, (z i).A))| ∂iidProduct P n) +
      (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta +
      (iidProduct P n).real {z |
        ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h} := by
  let _ := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  let bad : Set (Fin n → ClampObs J) := {z |
    ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h}
  let noise : (Fin n → ClampObs J) → ℝ := fun z => |∑ i ∈ B.I2,
    interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
      (clampUnit (z i).Y - clampRegressionExtension P ((z i).X, (z i).A))|
  let bias := (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus) * L * h ^ beta
  have hbad : MeasurableSet bad := by
    exact (goodGramEvent_measurable B x kappa cminus cplus delta h).compl
  have hnoiseMeas : Measurable noise := by
    dsimp [noise]
    apply Measurable.abs
    refine Finset.measurable_fun_sum _ fun i _ => ?_
    exact (interceptWeight_measurable B x kappa cminus cplus delta h i).mul
      (((clampUnit_measurable'.comp
        (clampOutcome_measurable.comp (measurable_pi_apply i))).sub
        ((clampRegressionExtension_measurable P hmodel.holder).comp
          ((clampDesign_measurable.comp (measurable_pi_apply i))))))
  have hnoiseInt : Integrable noise (iidProduct P n) := by
    let C := 2 * Real.sqrt (ellOf beta + 1 : ℝ) /
      lambdaStar (ellOf beta) kappa cminus cplus
    refine Integrable.of_bound hnoiseMeas.aestronglyMeasurable C ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    by_cases hg : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h
    · calc
        noise z ≤ ∑ i ∈ B.I2,
            |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i| := by
          dsimp [noise]
          calc
            _ ≤ ∑ i ∈ B.I2,
                |interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
                  (clampUnit (z i).Y -
                    clampRegressionExtension P ((z i).X, (z i).A))| :=
              Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro i hi
              rw [abs_mul]
              have hy := clampUnit_mem_Icc (z i).Y
              have hm := clampRegressionExtension_mem_Icc P hmodel.holder ((z i).X, (z i).A)
              have hr : |clampUnit (z i).Y -
                  clampRegressionExtension P ((z i).X, (z i).A)| ≤ 1 := by
                rw [abs_le]
                constructor <;> linarith [hy.1, hy.2, hm.1, hm.2]
              simpa using mul_le_of_le_one_right (abs_nonneg _) hr
        _ ≤ C := (goodGram_weight_controls B z x kappa cminus cplus delta h
          hh hlambda hg).2.1
    · have hw (i : Fin n) : interceptWeight B z x (ellOf beta) kappa cminus cplus
          delta h i = 0 := by simp [interceptWeight, hg]
      simp [noise, hw, C]
      positivity
  have herrMeas : Measurable fun z : Fin n → ClampObs J =>
      |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
        P.mu x delta| :=
    ((localRegressionEstimate_measurable B x kappa cminus cplus delta h).sub
      measurable_const).abs
  have herrInt : Integrable (fun z : Fin n → ClampObs J =>
      |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
        P.mu x delta|) (iidProduct P n) := by
    refine Integrable.of_bound herrMeas.aestronglyMeasurable 1 ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    have he : localRegressionEstimate B z x (ellOf beta) kappa cminus cplus
        delta h ∈ Set.Icc (0 : ℝ) 1 := by
      unfold localRegressionEstimate
      split_ifs
      · exact clampUnit_mem_Icc _
      · norm_num
    have hm := (hmodel.holder x).2.1 delta ⟨hdelta, by linarith⟩
    rw [abs_le]
    constructor <;> linarith [he.1, he.2, hm.1, hm.2]
  have hbias0 : 0 ≤ bias := by dsimp [bias]; positivity
  have hrhsInt : Integrable (fun z => noise z + bias + bad.indicator (fun _ => (1 : ℝ)) z)
      (iidProduct P n) := (hnoiseInt.add (integrable_const bias)).add
        (Integrable.indicator (integrable_const 1) hbad)
  have hae : ∀ᵐ z ∂iidProduct P n,
      |localRegressionEstimate B z x (ellOf beta) kappa cminus cplus delta h -
        P.mu x delta| ≤ noise z + bias + bad.indicator (fun _ => (1 : ℝ)) z := by
    filter_upwards [iidProduct_outcomeSupport P hmodel] with z hz
    by_cases hg : GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h
    · have heqY (i : Fin n) : (z i).Y = clampUnit (z i).Y := by
        simp [clampUnit, (hz i).1, (hz i).2]
      simp only [localRegressionEstimate, hg, if_true]
      have hb := localRegression_good_error_le P hmodel hbeta hL B z x
        hdelta hh hupper hlambda hg
      have hnotbad : z ∉ bad := by simpa [bad] using hg
      rw [Set.indicator_of_notMem hnotbad, add_zero]
      have hsumY : (∑ i ∈ B.I2,
          interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i * (z i).Y) =
          ∑ i ∈ B.I2,
          interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
            clampUnit (z i).Y := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrArg
          (fun y => interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i * y)
          (heqY i)
      rw [hsumY]
      change |clampUnit (∑ i ∈ B.I2,
          interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i *
            clampUnit (z i).Y) - P.mu x delta| ≤ noise z + bias
      exact hb
    · have he : |(1 / 2 : ℝ) - P.mu x delta| ≤ 1 := by
        have hm := (hmodel.holder x).2.1 delta ⟨hdelta, by linarith⟩
        rw [abs_le]
        constructor <;> linarith [hm.1, hm.2]
      have hn0 : 0 ≤ noise z := abs_nonneg _
      have hmem : z ∈ bad := by simpa [bad] using hg
      rw [Set.indicator_of_mem hmem]
      simp only [localRegressionEstimate, hg, if_false]
      exact he.trans (by linarith [hn0, hbias0])
  have hint := integral_mono_ae herrInt hrhsInt hae
  have hnbInt : Integrable (fun z => noise z + bias) (iidProduct P n) :=
    hnoiseInt.add (integrable_const bias)
  have hindInt : Integrable (bad.indicator (fun _ => (1 : ℝ))) (iidProduct P n) :=
    Integrable.indicator (integrable_const 1) hbad
  have houter :
      (∫ z, noise z + bias + bad.indicator (fun _ => (1 : ℝ)) z ∂iidProduct P n) =
      (∫ z, noise z + bias ∂iidProduct P n) +
        ∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂iidProduct P n := by
    simpa only [Pi.add_apply] using integral_add hnbInt hindInt
  have hinner : (∫ z, noise z + bias ∂iidProduct P n) =
      (∫ z, noise z ∂iidProduct P n) + ∫ _z, bias ∂iidProduct P n := by
    simpa only [Pi.add_apply] using integral_add hnoiseInt (integrable_const bias)
  have hindval : (∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂iidProduct P n) =
      (iidProduct P n).real bad := by
    rw [integral_indicator hbad, integral_const]
    simp [measureReal_def]
  rw [houter, hinner, integral_const, hindval] at hint
  simpa [noise, bias, bad, measureReal_def, add_assoc] using hint

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
