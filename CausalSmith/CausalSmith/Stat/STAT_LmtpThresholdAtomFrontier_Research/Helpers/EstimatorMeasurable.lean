/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.TotalGram
import Causalean.Mathlib.Analysis.ConvexProjection

/-! # Measurability of the realized total-Gram estimator -/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators Matrix

noncomputable section

private lemma measurable_obs_X {J : ℕ} : Measurable (fun o : ClampObs J => o.X) := by
  exact measurable_fst.comp (Measurable.of_comap_le le_rfl)

private lemma measurable_obs_A {J : ℕ} : Measurable (fun o : ClampObs J => o.A) := by
  exact measurable_fst.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

private lemma measurable_obs_Y {J : ℕ} : Measurable (fun o : ClampObs J => o.Y) := by
  exact measurable_snd.comp (measurable_snd.comp (Measurable.of_comap_le le_rfl))

/-- [local count is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localCount_measurable {J n : ℕ} (B : SplitBlocks n) (x : Fin J)
    (delta h : ℝ) : Measurable fun z : Fin n → ClampObs J =>
      localCount B z x delta h := by
  classical
  unfold localCount
  refine Finset.measurable_fun_sum _ fun i _ => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_eq_fun
    (measurable_obs_X.comp (measurable_pi_apply i)) measurable_const).inter
      (measurableSet_Icc.preimage
        (measurable_obs_A.comp (measurable_pi_apply i)))

/-- [local gram entry is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `r` input](hyp:r), [the specified `s` input](hyp:s), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localGram_entry_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (r s : Fin (ell + 1)) (delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J => localGram B z x ell delta h r s := by
  classical
  simp only [localGram_apply]
  refine Finset.measurable_fun_sum _ fun i _ => Measurable.ite ?_ ?_ measurable_const
  · exact (measurableSet_eq_fun
      (measurable_obs_X.comp (measurable_pi_apply i)) measurable_const).inter
        (measurableSet_Icc.preimage
          (((measurable_obs_A.comp (measurable_pi_apply i)).sub measurable_const).div_const h))
  · have hd : Measurable (fun z : Fin n → ClampObs J => ((z i).A - delta) / h) :=
      ((measurable_obs_A.comp (measurable_pi_apply i)).sub measurable_const).div_const h
    exact (hd.pow_const (r : ℕ)).mul (hd.pow_const (s : ℕ))

/-- [local gram is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localGram_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J => localGram B z x ell delta h := by
  exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s =>
    localGram_entry_measurable B x r s delta h

/-- [the stated local gram is hermitian property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localGram_isHermitian {J n ell : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J) (delta h : ℝ) :
    (localGram B z x ell delta h).IsHermitian := by
  exact Causalean.Stat.Nonparametric.designMatrix_isHermitian
    (fun i => scaledDose delta h (z i)) (localKernelWeight B z x delta h)

/-- [local gram inv is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localGram_inv_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      (localGram B z x ell delta h)⁻¹ := by
  classical
  simp only [Matrix.inv_def]
  have hG := localGram_measurable (ell := ell) B x delta h
  have hdet : Measurable fun z : Fin n → ClampObs J =>
      (localGram B z x ell delta h).det :=
    continuous_id.matrix_det.measurable.comp hG
  have hadj : Measurable fun z : Fin n → ClampObs J =>
      (localGram B z x ell delta h).adjugate :=
    continuous_id.matrix_adjugate.measurable.comp hG
  convert (measurable_inv.comp hdet).smul hadj using 1
  funext z
  rw [Ring.inverse_eq_inv]
  rfl

/-- [good gram event is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma goodGramEvent_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h : ℝ) :
    MeasurableSet {z : Fin n → ClampObs J |
      GoodGramEvent B z x ell kappa cminus cplus delta h} := by
  classical
  let a : (Fin n → ClampObs J) → ℝ := fun z =>
    lambdaStar ell kappa cminus cplus * (localCount B z x delta h : ℝ) / 2
  let F : (Fin n → ClampObs J) → Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ :=
    fun z => localGram B z x ell delta h - a z • 1
  have ha : Measurable a := by
    dsimp [a]
    exact (measurable_const.mul
      ((measurable_of_countable (fun m : ℕ => (m : ℝ))).comp
        (localCount_measurable B x delta h))).div_const 2
  have hF : Measurable F := by
    dsimp [F]
    exact measurable_pi_lambda _ fun r => measurable_pi_lambda _ fun s => by
      simp only [Matrix.sub_apply, Matrix.smul_apply]
      exact (localGram_entry_measurable B x r s delta h).sub
        (ha.mul measurable_const)
  have hpsd : MeasurableSet {A : Matrix (Fin (ell + 1)) (Fin (ell + 1)) ℝ |
      A.PosSemidef} :=
    Causalean.Mathlib.Analysis.isClosed_posSemidef.measurableSet
  have heq : {z : Fin n → ClampObs J |
      GoodGramEvent B z x ell kappa cminus cplus delta h} =
      {z | 0 < localCount B z x delta h} ∩ F ⁻¹' {A | A.PosSemidef} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    unfold GoodGramEvent
    constructor
    · rintro ⟨hcount, hquad⟩
      refine ⟨hcount, Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_⟩
      · dsimp [F]
        exact (localGram_isHermitian B z x delta h).sub
          (Matrix.isHermitian_one.smul (star_trivial (a z)))
      · intro v
        have hv := hquad v
        dsimp [F, a]
        have hid : star v ⬝ᵥ
            ((localGram B z x ell delta h -
              (lambdaStar ell kappa cminus cplus *
                (localCount B z x delta h : ℝ) / 2) • 1) *ᵥ v) =
          matrixQuadratic (localGram B z x ell delta h) v -
              lambdaStar ell kappa cminus cplus *
                (localCount B z x delta h : ℝ) / 2 * ∑ j, v j ^ 2 := by
          rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
            Matrix.one_mulVec]
          simp only [matrixQuadratic, dotProduct]
          congr 1
          · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            simp
            ring
        rw [hid]
        exact sub_nonneg.mpr hv
    · rintro ⟨hcount, hpsd'⟩
      refine ⟨hcount, fun v => ?_⟩
      have hv := hpsd'.dotProduct_mulVec_nonneg v
      dsimp [F, a] at hv
      have hid : star v ⬝ᵥ
          ((localGram B z x ell delta h -
            (lambdaStar ell kappa cminus cplus *
              (localCount B z x delta h : ℝ) / 2) • 1) *ᵥ v) =
          matrixQuadratic (localGram B z x ell delta h) v -
            lambdaStar ell kappa cminus cplus *
              (localCount B z x delta h : ℝ) / 2 * ∑ j, v j ^ 2 := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
          Matrix.one_mulVec]
        simp only [matrixQuadratic, dotProduct]
        congr 1
        · simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          simp
          ring
      rw [hid] at hv
      exact sub_nonneg.mp hv
  rw [heq]
  exact (measurableSet_lt measurable_const
    (localCount_measurable B x delta h)).inter
    (hpsd.preimage hF)

private lemma scaledDose_measurable {J n : ℕ} (i : Fin n) (delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J => scaledDose delta h (z i) := by
  exact ((measurable_obs_A.comp (measurable_pi_apply i)).sub measurable_const).div_const h

/-- [intercept weight is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `i` input](hyp:i). -/
lemma interceptWeight_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h : ℝ) (i : Fin n) :
    Measurable fun z : Fin n → ClampObs J =>
      interceptWeight B z x ell kappa cminus cplus delta h i := by
  classical
  unfold interceptWeight
  have hs := scaledDose_measurable (J := J) i delta h
  refine Measurable.ite
    (goodGramEvent_measurable B x kappa cminus cplus delta h) ?_ measurable_const
  have hw : Measurable fun z : Fin n → ClampObs J =>
      localKernelWeight B z x delta h i := by
    unfold localKernelWeight
    by_cases hi : i ∈ B.I2
    · simp only [hi, true_and]
      exact Measurable.ite
        ((measurableSet_eq_fun
          (measurable_obs_X.comp (measurable_pi_apply i)) measurable_const).inter
          (measurableSet_Icc.preimage hs)) measurable_const measurable_const
    · simp [hi]
  simp only [Causalean.Stat.Nonparametric.equivKernelWeight]
  refine Finset.measurable_fun_sum _ fun j _ => ?_
  exact (measurable_pi_apply j |>.comp
    (measurable_pi_apply 0 |>.comp
      (localGram_inv_measurable (ell := ell) B x delta h))).mul
    (hw.mul (hs.pow_const (j : ℕ)))

/-- [retained estimate is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `B` input](hyp:B), [the specified `delta` input](hyp:delta). -/
lemma retainedEstimate_measurable {J n : ℕ} (B : SplitBlocks n) (delta : ℝ) :
    Measurable fun z : Fin n → ClampObs J => retainedEstimate B z delta := by
  classical
  unfold retainedEstimate blockAverage
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
  exact Measurable.ite
    (measurableSet_lt measurable_const
      (measurable_obs_A.comp (measurable_pi_apply i)))
    (measurable_obs_Y.comp (measurable_pi_apply i)) measurable_const

/-- [atom estimate is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `delta` input](hyp:delta). -/
lemma atomEstimate_measurable {J n : ℕ} (B : SplitBlocks n)
    (x : Fin J) (delta : ℝ) :
    Measurable fun z : Fin n → ClampObs J => atomEstimate B z x delta := by
  classical
  unfold atomEstimate blockAverage
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ =>
    Measurable.ite ?_ measurable_const measurable_const)
  exact (measurableSet_eq_fun
    (measurable_obs_X.comp (measurable_pi_apply i)) measurable_const).inter
      (measurableSet_le
        (measurable_obs_A.comp (measurable_pi_apply i)) measurable_const)

private lemma clampUnit_measurable : Measurable clampUnit := by
  unfold clampUnit
  fun_prop

/-- [local regression estimate is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
lemma localRegressionEstimate_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      localRegressionEstimate B z x ell kappa cminus cplus delta h := by
  classical
  unfold localRegressionEstimate
  refine Measurable.ite
    (goodGramEvent_measurable B x kappa cminus cplus delta h) ?_ measurable_const
  apply clampUnit_measurable.comp
  refine Finset.measurable_fun_sum _ fun i _ => ?_
  exact (interceptWeight_measurable B x kappa cminus cplus delta h i).mul
    (measurable_obs_Y.comp (measurable_pi_apply i))

/-- [total gram estimator is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h). -/
theorem totalGramEstimator_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (kappa cminus cplus delta h : ℝ) :
    Measurable fun z : Fin n → ClampObs J =>
      totalGramEstimator B z ell kappa cminus cplus delta h := by
  classical
  unfold totalGramEstimator
  apply clampUnit_measurable.comp
  refine (retainedEstimate_measurable B delta).add
    (Finset.measurable_fun_sum _ fun x _ => ?_)
  exact (atomEstimate_measurable B x delta).mul
    (localRegressionEstimate_measurable B x kappa cminus cplus delta h)

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
