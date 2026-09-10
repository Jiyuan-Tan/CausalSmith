/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.HonestExpectedLength

/-! # Disjoint-block factorization for the honest-radius mixed term -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators Matrix

noncomputable section

/-- Local-polynomial intercept weights only depend on observations in the
local-regression block. The result uses [the `hz` condition](hyp:hz), [the `hi` condition](hyp:hi). [This is the stated conclusion](goal).
-/
lemma interceptWeight_congr_I2 {J n ell : ℕ} (B : SplitBlocks n)
    (z z' : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ)
    (hz : ∀ i ∈ B.I2, z' i = z i) (i : Fin n) (hi : i ∈ B.I2) :
    interceptWeight B z' x ell kappa cminus cplus delta h i =
      interceptWeight B z x ell kappa cminus cplus delta h i := by
  classical
  have hcount : localCount B z' x delta h = localCount B z x delta h := by
    unfold localCount
    apply Finset.sum_congr rfl
    intro j hj
    rw [hz j hj]
  have hkernel : localKernelWeight B z' x delta h =
      localKernelWeight B z x delta h := by
    funext j
    by_cases hj : j ∈ B.I2
    · simp [localKernelWeight, hj, hz j hj]
    · simp [localKernelWeight, hj]
  have hgram : localGram B z' x ell delta h = localGram B z x ell delta h := by
    ext a b
    simp only [localGram, Causalean.Stat.Nonparametric.designMatrix]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hj2 : j ∈ B.I2
    · rw [hz j hj2, hkernel]
    · have hk' : localKernelWeight B z' x delta h j = 0 := by
        simp [localKernelWeight, hj2]
      have hk : localKernelWeight B z x delta h j = 0 := by
        simp [localKernelWeight, hj2]
      rw [hk', hk]
      simp
  have hgood : GoodGramEvent B z' x ell kappa cminus cplus delta h ↔
      GoodGramEvent B z x ell kappa cminus cplus delta h := by
    unfold GoodGramEvent
    rw [hcount, hgram]
  have hdesign := hgram
  change Causalean.Stat.Nonparametric.designMatrix ell
      (fun j => scaledDose delta h (z' j)) (localKernelWeight B z' x delta h) =
    Causalean.Stat.Nonparametric.designMatrix ell
      (fun j => scaledDose delta h (z j)) (localKernelWeight B z x delta h) at hdesign
  unfold interceptWeight
  by_cases hg : GoodGramEvent B z x ell kappa cminus cplus delta h
  · rw [if_pos (hgood.mpr hg), if_pos hg]
    unfold Causalean.Stat.Nonparametric.equivKernelWeight
    rw [hdesign, hkernel]
    apply Finset.sum_congr rfl
    intro k hk
    congr 3
    exact congrArg (scaledDose delta h) (hz i hi)
  · rw [if_neg (fun hg' => hg (hgood.mp hg')), if_neg hg]

/-- Exact factorization of the atom-frequency/weight-energy mixed moment
across the disjoint estimation blocks. The result uses [the `hJ` condition](hyp:hJ), [the `hprob` condition](hyp:hprob). [This is the stated conclusion](goal).
-/
lemma integral_atomEstimate_mul_sqrt_weightEnergy
    {J n ell : ℕ} (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (hJ : 0 < J)
    (hprob : IsProbabilityMeasure P.dataMeasure) :
    (∫ z, atomEstimate B z x delta *
        Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2)
        ∂iidProduct P n) =
      (∫ z, atomEstimate B z x delta ∂iidProduct P n) *
        ∫ z, Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2)
          ∂iidProduct P n := by
  classical
  let o0 : ClampObs J := ⟨⟨0, hJ⟩, 0, 0⟩
  let extendBlock (I : Finset (Fin n))
      (u : (i : {i // i ∈ I}) → ClampObs J) : Fin n → ClampObs J :=
    fun i => if hi : i ∈ I then u ⟨i, hi⟩ else o0
  have hextMeas (I : Finset (Fin n)) : Measurable (extendBlock I) := by
    apply measurable_pi_lambda
    intro i
    by_cases hi : i ∈ I
    · simpa [extendBlock, hi] using
        (measurable_pi_apply (⟨i, hi⟩ : {i // i ∈ I}))
    · simp only [extendBlock, hi, dite_false]
      exact measurable_const
  let F : ((i : {i // i ∈ B.I1}) → ClampObs J) → ℝ := fun u =>
    atomEstimate B (extendBlock B.I1 u) x delta
  let G : ((i : {i // i ∈ B.I2}) → ClampObs J) → ℝ := fun u =>
    Real.sqrt (∑ i ∈ B.I2,
      (interceptWeight B (extendBlock B.I2 u) x ell kappa cminus cplus delta h i) ^ 2)
  have hF : Measurable F := by
    exact (atomEstimate_measurable B x delta).comp (hextMeas B.I1)
  have hG : Measurable G := by
    apply Measurable.sqrt
    exact Finset.measurable_fun_sum B.I2 fun i _ =>
      ((interceptWeight_measurable B x kappa cminus cplus delta h i).comp
        (hextMeas B.I2)).pow_const 2
  have hFproj (z : Fin n → ClampObs J) :
      F (Causalean.finsetCoordProj B.I1 z) = atomEstimate B z x delta := by
    unfold F atomEstimate blockAverage
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp [extendBlock, Causalean.finsetCoordProj, hi]
  have hGproj (z : Fin n → ClampObs J) :
      G (Causalean.finsetCoordProj B.I2 z) =
        Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2) := by
    unfold G
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    exact (interceptWeight_congr_I2 (ell := ell) B
      (extendBlock B.I2 (Causalean.finsetCoordProj B.I2 z)) z x
      kappa cminus cplus delta h
      (by
        intro j hj
        dsimp only [extendBlock]
        rw [dif_pos hj]
        rfl) i hi).symm
  have hfactor := integral_mul_I1_I2 P B hprob F G hF hG
  calc
    _ = ∫ z, F (Causalean.finsetCoordProj B.I1 z) *
        G (Causalean.finsetCoordProj B.I2 z) ∂iidProduct P n := by
      apply integral_congr_ae
      filter_upwards with z
      rw [hFproj, hGproj]
    _ = (∫ z, F (Causalean.finsetCoordProj B.I1 z) ∂iidProduct P n) *
        ∫ z, G (Causalean.finsetCoordProj B.I2 z) ∂iidProduct P n := hfactor
    _ = _ := by
      congr 1
      · apply integral_congr_ae
        filter_upwards with z
        rw [hFproj]
      · apply integral_congr_ae
        filter_upwards with z
        rw [hGproj]

/-- At the information-balanced bandwidth, the expected square-root weight
energy has the same `h^beta` scale as the local stochastic error. The result uses [the `hmodel` condition](hyp:hmodel), [the `hsampling` condition](hyp:hsampling), [the `hn` condition](hyp:hn), [the `hbeta` condition](hyp:hbeta), [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hpmin` condition](hyp:hpmin), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh), [the `hupper` condition](hyp:hupper), [the `hlambda` condition](hyp:hlambda), [the `hbalance` condition](hyp:hbalance). [This is the stated conclusion](goal).
-/
lemma integral_sqrt_interceptWeight_energy_balanced_le
    {J n ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin delta h : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (hsampling : IidSampling P n) (B : SplitBlocks n) (x : Fin J)
    (hn : 8 ≤ n) (hbeta : 0 < beta) (hkappa : 0 ≤ kappa)
    (hcminus : 0 < cminus) (hcplus : 0 ≤ cplus) (hpmin : 0 < pmin)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (hupper : delta + h ≤ 1)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hbalance : (n : ℝ) * h ^ (2 * beta + 1) *
      (delta + h) ^ kappa = 1) :
    (∫ z, Real.sqrt (∑ i ∈ B.I2,
      (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2)
      ∂iidProduct P n) ≤
      Real.sqrt
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
  have hraw := integral_sqrt_interceptWeight_energy_le P B x kappa cminus
    cplus delta h p hsampling hh hlambda hp0 hcardNat rfl
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hrate := balancedEffectiveSample_sqrt_le (D := D) (K := K)
    (p := p) (m := (B.I2.card : ℝ)) (Nat.zero_lt_of_lt hn) hh hD hK
    hcard hpLower hbalance
  dsimp [D, K] at hrate
  exact hraw.trans hrate

/-- Integrated version of the good/bad pointwise radius decomposition.  The
mixed stochastic term factors exactly by sample splitting. The result uses [the `hJ` condition](hyp:hJ), [the `hprob` condition](hyp:hprob), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hh` condition](hyp:hh), [the `ht` condition](hyp:ht), [the `hb1` condition](hyp:hb1), [the `hlambda` condition](hyp:hlambda). [This is the stated conclusion](goal).
-/
lemma integral_stratumRadius_le_factored
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (beta kappa L cminus cplus delta h t b1 : ℝ)
    (hJ : 0 < J) (hprob : IsProbabilityMeasure P.dataMeasure)
    (hbeta : 0 ≤ beta) (hL : 0 ≤ L) (hh : 0 < h)
    (ht : 0 ≤ t) (hb1 : 0 ≤ b1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus) :
    (∫ z, stratumRadius B z x (ellOf beta) beta kappa L cminus cplus
        delta h t b1 ∂iidProduct P n) ≤
      ((∫ z, atomEstimate B z x delta ∂iidProduct P n) + b1) *
        (L * h ^ beta *
            (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
              lambdaStar (ellOf beta) kappa cminus cplus) +
          t * (∫ z, Real.sqrt (∑ i ∈ B.I2,
            (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)
              ∂iidProduct P n)) +
        b1 + (iidProduct P n).real {z |
          ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h} := by
  letI : IsProbabilityMeasure P.dataMeasure := hprob
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let energy : (Fin n → ClampObs J) → ℝ := fun z => Real.sqrt (∑ i ∈ B.I2,
    (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)
  let bad : Set (Fin n → ClampObs J) := {z |
    ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h}
  let bias := L * h ^ beta * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus)
  let rhs : (Fin n → ClampObs J) → ℝ := fun z =>
    (atomEstimate B z x delta + b1) * (bias + t * energy z) + b1 +
      bad.indicator (fun _ => (1 : ℝ)) z
  have henergyMeas : Measurable energy := by
    exact (Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable B x kappa cminus cplus delta h i).pow_const 2).sqrt
  have henergyBound : ∀ z, energy z ≤ Real.sqrt
      (4 * (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus ^ 2) := by
    intro z
    apply Real.sqrt_le_sqrt
    have he := localRegression_weight_energy_le (ell := ellOf beta) B z x
      kappa cminus cplus delta h hh hlambda
    simpa only [localRegressionDesignWeight_apply, ite_pow,
      zero_pow (by norm_num : 2 ≠ 0), ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter] using he
  have henergyInt : Integrable energy (iidProduct P n) := by
    refine Integrable.of_bound henergyMeas.aestronglyMeasurable
      (Real.sqrt (4 * (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus ^ 2)) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact henergyBound z
  have hatomInt : Integrable (fun z : Fin n → ClampObs J =>
      atomEstimate B z x delta) (iidProduct P n) := by
    refine Integrable.of_bound (atomEstimate_measurable B x delta).aestronglyMeasurable 1 ?_
    filter_upwards with z
    have hz := atomEstimate_mem_Icc B z x delta
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  have hbadMeas : MeasurableSet bad :=
    (goodGramEvent_measurable B x kappa cminus cplus delta h).compl
  have hbadInt : Integrable (bad.indicator (fun _ => (1 : ℝ))) (iidProduct P n) :=
    (integrable_const 1).indicator hbadMeas
  have hrhsInt : Integrable rhs (iidProduct P n) := by
    dsimp [rhs]
    have hleft := hatomInt.add (integrable_const b1)
    have hright := (integrable_const bias).add (henergyInt.const_mul t)
    exact (hleft.mul_bdd hright.aestronglyMeasurable (by
      filter_upwards with z
      rw [Real.norm_eq_abs]
      have hz := atomEstimate_mem_Icc B z x delta
      change |bias + t * energy z| ≤ _
      rw [abs_of_nonneg (by positivity : 0 ≤ bias + t * energy z)]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (henergyBound z) ht))).add
        (integrable_const b1) |>.add hbadInt
  have hradMeas : Measurable (fun z : Fin n → ClampObs J =>
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h t b1) :=
    honest_stratumRadius_measurable B x beta kappa L cminus cplus delta h t b1
  have hpoint (z : Fin n → ClampObs J) :
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h t b1 ≤ rhs z :=
    stratumRadius_le_good_expression_add_bad B z x beta kappa L cminus cplus
      delta h t b1 hbeta hL hh ht hb1 hlambda
  have hrad0 (z : Fin n → ClampObs J) : 0 ≤
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h t b1 := by
    unfold stratumRadius atomEstimate blockAverage
    split_ifs <;> positivity
  have hradInt : Integrable (fun z : Fin n → ClampObs J =>
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus delta h t b1)
      (iidProduct P n) := hrhsInt.mono' hradMeas.aestronglyMeasurable (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hrad0 z)]
        exact hpoint z)
  have hmixInt : Integrable (fun z : Fin n → ClampObs J =>
      atomEstimate B z x delta * energy z) (iidProduct P n) :=
    henergyInt.bdd_mul (atomEstimate_measurable B x delta).aestronglyMeasurable (by
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_of_nonneg (atomEstimate_mem_Icc B z x delta).1]
      exact (atomEstimate_mem_Icc B z x delta).2)
  have hfactor := integral_atomEstimate_mul_sqrt_weightEnergy (ell := ellOf beta)
    P B x kappa cminus
    cplus delta h hJ hprob
  change (∫ z, atomEstimate B z x delta * energy z ∂iidProduct P n) = _ at hfactor
  have hprodIntegral :
      (∫ z, (atomEstimate B z x delta + b1) * (bias + t * energy z)
        ∂iidProduct P n) =
      ((∫ z, atomEstimate B z x delta ∂iidProduct P n) + b1) *
        (bias + t * ∫ z, energy z ∂iidProduct P n) := by
    have hA : Integrable (fun z : Fin n → ClampObs J =>
        bias * atomEstimate B z x delta) (iidProduct P n) :=
      hatomInt.const_mul bias
    have hB : Integrable (fun z : Fin n → ClampObs J =>
        t * (atomEstimate B z x delta * energy z)) (iidProduct P n) :=
      hmixInt.const_mul t
    have hC : Integrable (fun _z : Fin n → ClampObs J => b1 * bias)
        (iidProduct P n) := integrable_const _
    have hD : Integrable (fun z : Fin n → ClampObs J => b1 * t * energy z)
        (iidProduct P n) := by
      simpa only [mul_assoc] using henergyInt.const_mul (b1 * t)
    rw [show (fun z : Fin n → ClampObs J =>
        (atomEstimate B z x delta + b1) * (bias + t * energy z)) =
      fun z => bias * atomEstimate B z x delta +
        t * (atomEstimate B z x delta * energy z) +
        b1 * bias + b1 * t * energy z by funext z; ring]
    have hABCD := integral_add ((hA.add hB).add hC) hD
    have hABC := integral_add (hA.add hB) hC
    have hAB := integral_add hA hB
    calc
      _ = (∫ z, bias * atomEstimate B z x delta +
            t * (atomEstimate B z x delta * energy z) + b1 * bias
            ∂iidProduct P n) +
            ∫ z, b1 * t * energy z ∂iidProduct P n := by
          simpa only [Pi.add_apply] using hABCD
      _ = ((∫ z, bias * atomEstimate B z x delta +
              t * (atomEstimate B z x delta * energy z) ∂iidProduct P n) +
              ∫ _z, b1 * bias ∂iidProduct P n) +
              ∫ z, b1 * t * energy z ∂iidProduct P n := by
          rw [show (∫ z, bias * atomEstimate B z x delta +
              t * (atomEstimate B z x delta * energy z) + b1 * bias
              ∂iidProduct P n) = _ by simpa only [Pi.add_apply] using hABC]
      _ = (((∫ z, bias * atomEstimate B z x delta ∂iidProduct P n) +
              ∫ z, t * (atomEstimate B z x delta * energy z) ∂iidProduct P n) +
              ∫ _z, b1 * bias ∂iidProduct P n) +
              ∫ z, b1 * t * energy z ∂iidProduct P n := by
          rw [show (∫ z, bias * atomEstimate B z x delta +
              t * (atomEstimate B z x delta * energy z) ∂iidProduct P n) = _ by
                simpa only [Pi.add_apply] using hAB]
      _ = _ := by
        rw [integral_const_mul, integral_const_mul, integral_const,
          integral_const_mul, hfactor]
        simp
        ring
  calc
    _ ≤ ∫ z, rhs z ∂iidProduct P n := integral_mono hradInt hrhsInt hpoint
    _ = _ := by
      dsimp [rhs]
      have hprodInt : Integrable (fun z : Fin n → ClampObs J =>
          (atomEstimate B z x delta + b1) * (bias + t * energy z))
          (iidProduct P n) :=
        (hatomInt.add (integrable_const b1)).mul_bdd
          ((integrable_const bias).add (henergyInt.const_mul t)).aestronglyMeasurable
          (by
            filter_upwards with z
            rw [Real.norm_eq_abs]
            change |bias + t * energy z| ≤ _
            rw [abs_of_nonneg (by positivity : 0 ≤ bias + t * energy z)]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_left (henergyBound z) ht))
      calc
        (∫ z, (atomEstimate B z x delta + b1) * (bias + t * energy z) + b1 +
            bad.indicator (fun _ => (1 : ℝ)) z ∂iidProduct P n) =
            (∫ z, (atomEstimate B z x delta + b1) * (bias + t * energy z) + b1
              ∂iidProduct P n) + ∫ z, bad.indicator (fun _ => (1 : ℝ)) z
              ∂iidProduct P n := integral_add
                (hprodInt.add (integrable_const b1)) hbadInt
        _ = ((∫ z, (atomEstimate B z x delta + b1) * (bias + t * energy z)
              ∂iidProduct P n) + ∫ _z, b1 ∂iidProduct P n) +
              ∫ z, bad.indicator (fun _ => (1 : ℝ)) z ∂iidProduct P n := by
              rw [integral_add hprodInt (integrable_const b1)]
        _ = _ := by
          rw [hprodIntegral, integral_const, integral_indicator hbadMeas, integral_const]
          simp [measureReal_def, energy, bad, bias]

/-- The displayed per-stratum radius is integrable under every product law.
This is the bookkeeping input needed to integrate the finite sum of radii. The result uses [the `hprob` condition](hyp:hprob), [the `hbeta` condition](hyp:hbeta), [the `hL` condition](hyp:hL), [the `hh` condition](hyp:hh), [the `ht` condition](hyp:ht), [the `hb1` condition](hyp:hb1), [the `hlambda` condition](hyp:hlambda). [This is the stated conclusion](goal).
-/
lemma stratumRadius_integrable
    {J n : ℕ} (P : ClampLaw J) (B : SplitBlocks n) (x : Fin J)
    (beta kappa L cminus cplus delta h t b1 : ℝ)
    (hprob : IsProbabilityMeasure P.dataMeasure)
    (hbeta : 0 ≤ beta) (hL : 0 ≤ L) (hh : 0 < h)
    (ht : 0 ≤ t) (hb1 : 0 ≤ b1)
    (hlambda : 0 < lambdaStar (ellOf beta) kappa cminus cplus) :
    Integrable (fun z : Fin n → ClampObs J =>
      stratumRadius B z x (ellOf beta) beta kappa L cminus cplus
        delta h t b1) (iidProduct P n) := by
  letI : IsProbabilityMeasure P.dataMeasure := hprob
  letI : IsProbabilityMeasure (iidProduct P n) := by unfold iidProduct; infer_instance
  let energy : (Fin n → ClampObs J) → ℝ := fun z => Real.sqrt (∑ i ∈ B.I2,
    (interceptWeight B z x (ellOf beta) kappa cminus cplus delta h i) ^ 2)
  have henergyMeas : Measurable energy := by
    exact (Finset.measurable_fun_sum B.I2 fun i _ =>
      (interceptWeight_measurable B x kappa cminus cplus delta h i).pow_const 2).sqrt
  have henergyBound : ∀ z, energy z ≤ Real.sqrt
      (4 * (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus ^ 2) := by
    intro z
    apply Real.sqrt_le_sqrt
    have he := localRegression_weight_energy_le (ell := ellOf beta) B z x
      kappa cminus cplus delta h hh hlambda
    simpa only [localRegressionDesignWeight_apply, ite_pow,
      zero_pow (by norm_num : 2 ≠ 0), ← Finset.sum_filter,
      Finset.filter_mem_eq_inter, Finset.univ_inter] using he
  have henergyInt : Integrable energy (iidProduct P n) := by
    refine Integrable.of_bound henergyMeas.aestronglyMeasurable
      (Real.sqrt (4 * (ellOf beta + 1 : ℝ) /
        lambdaStar (ellOf beta) kappa cminus cplus ^ 2)) ?_
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact henergyBound z
  have hatomInt : Integrable (fun z : Fin n → ClampObs J =>
      atomEstimate B z x delta) (iidProduct P n) := by
    refine Integrable.of_bound
      (atomEstimate_measurable B x delta).aestronglyMeasurable 1 ?_
    filter_upwards with z
    have hz := atomEstimate_mem_Icc B z x delta
    rw [Real.norm_eq_abs, abs_of_nonneg hz.1]
    exact hz.2
  let bad : Set (Fin n → ClampObs J) := {z |
    ¬ GoodGramEvent B z x (ellOf beta) kappa cminus cplus delta h}
  let bias := L * h ^ beta * (2 * Real.sqrt (ellOf beta + 1 : ℝ) /
    lambdaStar (ellOf beta) kappa cminus cplus)
  let rhs : (Fin n → ClampObs J) → ℝ := fun z =>
    (atomEstimate B z x delta + b1) * (bias + t * energy z) + b1 +
      bad.indicator (fun _ => (1 : ℝ)) z
  have hrhsInt : Integrable rhs (iidProduct P n) := by
    have hbadMeas : MeasurableSet bad :=
      (goodGramEvent_measurable B x kappa cminus cplus delta h).compl
    dsimp [rhs]
    exact (((hatomInt.add (integrable_const b1)).mul_bdd
      ((integrable_const bias).add (henergyInt.const_mul t)).aestronglyMeasurable
      (by
        filter_upwards with z
        rw [Real.norm_eq_abs]
        change |bias + t * energy z| ≤ _
        rw [abs_of_nonneg (by positivity : 0 ≤ bias + t * energy z)]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (henergyBound z) ht)))
      |>.add (integrable_const b1)).add ((integrable_const 1).indicator hbadMeas)
  have hradMeas := honest_stratumRadius_measurable (ell := ellOf beta)
    B x beta kappa L cminus cplus
    delta h t b1
  refine hrhsInt.mono' hradMeas.aestronglyMeasurable ?_
  filter_upwards with z
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    unfold stratumRadius atomEstimate blockAverage
    split_ifs <;> positivity)]
  dsimp [rhs, bias, energy, bad]
  exact stratumRadius_le_good_expression_add_bad B z x beta kappa L cminus cplus
    delta h t b1 hbeta hL hh ht hb1 hlambda

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
