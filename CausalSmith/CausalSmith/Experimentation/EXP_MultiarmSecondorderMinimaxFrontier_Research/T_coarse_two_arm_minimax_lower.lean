import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmScheduleKernel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.BayesInformation
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSmoothModel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmVanTreesModel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmVanTreesAssembly
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmSmoothKernel
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmFinitePosterior
import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmPosteriorCompatibility
import Causalean.Stat.Minimax.FinitePosteriorBayesRisk

/-! Fully internal smooth-prior two-arm minimax lower bound. -/

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Experimentation.DesignBased
open MeasureTheory ProbabilityTheory

/-- The effect triple 2 space carries the discrete measurable structure. -/
noncomputable local instance (n : ℕ) : MeasurableSpace (EffectTriple n) := ⊤
/-- [every singleton in the effect triple 2 space is measurable](goal). -/
noncomputable local instance (n : ℕ) : MeasurableSingletonClass (EffectTriple n) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩
/-- [the effect triple 1 collection is nonempty](goal). -/
noncomputable local instance (n : ℕ) : Nonempty (EffectTriple n) :=
  ⟨⟨⟨⟨0, Nat.zero_lt_succ n⟩,
      ⟨⟨0, Nat.zero_lt_succ n⟩, ⟨n, Nat.lt_succ_self n⟩⟩⟩, by simp⟩⟩

-- @node: twoArmSmoothMixedCountLoss_eq_inducedSquaredRisk
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [Mixing the smooth scalar-to-effect kernel and then evaluating count squared loss is exactly the squared risk under the induced finite effect-count prior.](goal) -/
lemma twoArmSmoothMixedCountLoss_eq_inducedSquaredRisk {n : ℕ}
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (π : Measure ℝ)
    [IsProbabilityMeasure π]
    (D : FiniteDesign (Assign 2 n)) (T : Fin (n + 1) → ℝ) :
    Causalean.Stat.mixedKernelLoss π (twoArmSmoothEffectKernel n a ha0 ha1)
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
          (fun theta _x => effectTarget theta)) T =
      Causalean.Stat.squaredRisk
        (Causalean.Stat.inducedFiniteDesign π
          (twoArmSmoothEffectKernel n a ha0 ha1))
        (twoArmCountKernel D) (fun theta _x => effectTarget theta) T := by
  exact Causalean.Stat.mixedKernelLoss_statewiseSquaredLoss_eq_inducedSquaredRisk
    π (twoArmSmoothEffectKernel n a ha0 ha1) (twoArmCountKernel D)
      (fun theta _x => effectTarget theta) T

-- @node: twoArmSmoothRealBayesRisk_eq_scalarBayesRisk
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [The continuous smooth-mixture Bayes risk is the paper's scalar binomial Bayes risk for the induced finite effect-count prior.](goal) -/
lemma twoArmSmoothRealBayesRisk_eq_scalarBayesRisk {n : ℕ}
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (π : Measure ℝ)
    [IsProbabilityMeasure π]
    (D : FiniteDesign (Assign 2 n)) :
    Causalean.Stat.realBayesRisk π (twoArmSmoothEffectKernel n a ha0 ha1)
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
          (fun theta _x => effectTarget theta)) =
      scalarBayesRisk
        (Causalean.Stat.inducedFiniteDesign π
          (twoArmSmoothEffectKernel n a ha0 ha1)) := by
  rw [Causalean.Stat.realBayesRisk_eq_inducedFiniteDesignBayesRisk]
  exact finiteDesignBayesRisk_twoArmCount_eq_scalarBayesRisk _ D

-- @node: twoArmPosteriorTarget_eq_of_scoreCount_eq
/-- [the stated side condition holds](hyp:h), [The observation-dependent posterior target is constant on every retained-count fiber.](goal) -/
lemma twoArmPosteriorTarget_eq_of_scoreCount_eq {n : ℕ} {a θ : ℝ}
    {s t : Unit n → Bool} (h : scoreCount s = scoreCount t) :
    twoArmPosteriorTarget a θ s = twoArmPosteriorTarget a θ t := by
  unfold twoArmPosteriorTarget
  rw [twoArmScoreAverage_eq_count, twoArmScoreAverage_eq_count, h]

-- @node: twoArmSmoothVanTreesErrorLowerBound
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the second arm count satisfies its stated condition](hyp:ha1), [Every estimator of the signed Bernoulli score vector has smooth-prior posterior-target error at least the displayed finite van Trees fraction.](goal) -/
lemma twoArmSmoothVanTreesErrorLowerBound {n : ℕ} (hn : 0 < n)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1 / 2)
    (T : (Unit n → Bool) → ℝ) :
    (1 - a) ^ 2 / ((n : ℝ) / (1 - a ^ 2 / 4) + 40 / a ^ 2) ≤
      ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2))
        twoArmRegularBernoulliLikelihood (twoArmPosteriorTarget a) T z
        ∂((Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
          (-1 / 2) (1 / 2)).prod Measure.count) := by
  let M := twoArmFiniteVanTreesRegularity a ha T
  open Causalean.Stat.Limit.ObservationDependentVanTrees in
    apply finite_vanTrees_lower_bound (by norm_num) M
      (smoothPrior_contDiff (by positivity : 0 < a / 2))
      (support_smoothPrior_subset_Icc (ell := (-1 / 2 : ℝ)) (u := (1 / 2 : ℝ))
        (c := 0) (a := a / 2) (by positivity) (by linarith) (by linarith))
      (hasDerivAt_smoothPrior (by positivity)) (smoothPrior_nonneg (by positivity))
      (integral_smoothPrior_parameterMeasure (by positivity) (by linarith) (by linarith))
      (by
        filter_upwards with s
        have hu : smoothPrior 0 (a / 2) (1 / 2) = 0 := by
          rw [smoothPrior]
          simp only [sub_zero]
          rw [if_neg]
          norm_num
          linarith
        have hl : smoothPrior 0 (a / 2) (-1 / 2) = 0 := by
          rw [smoothPrior]
          simp only [sub_zero]
          rw [if_neg]
          norm_num
          linarith
        constructor
        · rw [hu]
          simp
        · rw [hl]
          simp)
      (smoothPrior_scoreSq_aestronglyMeasurable (by positivity))
      (smoothPrior_scoreSq_integrable (by positivity)) (by linarith) ?_ ?_
      (by
        rw [priorInformation_smoothPrior (by positivity : 0 < a / 2)
          (by linarith) (by linarith)]
        field_simp [ha.ne']
        norm_num)
      ?_
  · let PM := Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
        (-1 / 2) (1 / 2)
    letI : IsFiniteMeasure PM := by
      dsimp [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure]
      infer_instance
    let w := Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2)
    let p := twoArmRegularBernoulliLikelihood (n := n)
    let dg := twoArmPosteriorTargetDeriv (n := n) a
    have hprod := (twoArmFiniteVanTreesRegularity a ha T).hsensitivityInt
    rw [MeasureTheory.integral_prod _ hprod]
    calc
      1 - a = ∫ θ, w θ * (1 - a) ∂PM := by
        rw [MeasureTheory.integral_mul_const,
          Causalean.Stat.Limit.ObservationDependentVanTrees.integral_smoothPrior_parameterMeasure
            (by positivity : 0 < a / 2) (by linarith) (by linarith), one_mul]
      _ ≤ _ := by
        apply MeasureTheory.integral_mono
        · exact (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_integrable_parameterMeasure
            (by positivity : 0 < a / 2)).mul_const (1 - a)
        · exact hprod.integral_prod_left
        · intro θ
          dsimp [w, p, dg]
          rw [MeasureTheory.integral_count]
          simp only [Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField,
            Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
          rw [show (∑ s : Unit n → Bool,
              twoArmPosteriorTargetDeriv a θ s *
                (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior
                  0 (a / 2) θ * twoArmRegularBernoulliLikelihood θ s)) =
              Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior
                0 (a / 2) θ *
                ∑ s : Unit n → Bool,
                  twoArmPosteriorTargetDeriv a θ s *
                    twoArmRegularBernoulliLikelihood θ s by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            ring]
          by_cases hw : 0 < Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior
              0 (a / 2) θ
          · have hθ : |θ| < a / 2 := by
              simpa using
                (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_pos_iff
                  (by positivity : 0 < a / 2)).mp hw
            have hθone : |θ| ≤ 1 := hθ.le.trans (by linarith)
            simp_rw [twoArmRegularBernoulliLikelihood_eq hθone]
            rw [show (∑ s : Unit n → Bool,
                twoArmPosteriorTargetDeriv a θ s * twoArmBernoulliLikelihood θ s) =
                  (twoArmBernoulliVectorDesign n θ hθone).E
                    (twoArmPosteriorTargetDeriv a θ) by
              unfold FiniteDesign.E
              apply Finset.sum_congr rfl
              intro s _
              rw [twoArmBernoulliLikelihood_eq_design θ hθone]
              ring]
            exact mul_le_mul_of_nonneg_left
              (twoArmPosteriorTargetDeriv_mean_lower hn ha.le (by linarith) hθ.le) hw.le
          · have hw0 : Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior
                0 (a / 2) θ = 0 := le_antisymm (le_of_not_gt hw)
              (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
                (by positivity) θ)
            simp [hw0]
  · have hweighted := M.hfisherSqInt.integral_prod_left
    have hweighted' : MeasureTheory.Integrable
        (fun θ => Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior
            0 (a / 2) θ *
          Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
            (Measure.count : Measure (Unit n → Bool))
              (twoArmRegularBernoulliLikelihood (n := n))
              (twoArmBernoulliLikelihoodDeriv (n := n)) θ)
        (Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
          (-1 / 2) (1 / 2)) := by
      apply hweighted.congr
      filter_upwards with θ
      rw [Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation]
      simp_rw [MeasureTheory.integral_count]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      ring
    apply Causalean.Stat.Limit.ObservationDependentVanTrees.average_fisherInformation_le
      (ell := (-1 / 2 : ℝ)) (u := (1 / 2 : ℝ))
      (I := (n : ℝ) / (1 - a ^ 2 / 4))
      (w := Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2))
      (p := twoArmRegularBernoulliLikelihood (n := n))
      (dp := twoArmBernoulliLikelihoodDeriv (n := n))
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
        (by positivity : 0 < a / 2))
      (Causalean.Stat.Limit.ObservationDependentVanTrees.integral_smoothPrior_parameterMeasure
        (by positivity : 0 < a / 2) (by linarith) (by linarith))
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_integrable_parameterMeasure
        (by positivity : 0 < a / 2)) hweighted'
    intro θ hw
    have hθ : |θ| < a / 2 := by
      simpa using
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_pos_iff
          (by positivity : 0 < a / 2)).mp hw
    have hθone : |θ| ≤ 1 := hθ.le.trans (by linarith)
    have hfi_eq :
        Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
            (Measure.count : Measure (Unit n → Bool))
              (twoArmRegularBernoulliLikelihood (n := n))
              (twoArmBernoulliLikelihoodDeriv (n := n)) θ =
          Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
            (Measure.count : Measure (Unit n → Bool))
              (twoArmBernoulliLikelihood (n := n))
              (twoArmBernoulliLikelihoodDeriv (n := n)) θ := by
      unfold Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
      apply MeasureTheory.integral_congr_ae
      filter_upwards with s
      unfold Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
      rw [twoArmRegularBernoulliLikelihood_eq hθone]
    rw [hfi_eq]
    exact twoArmBernoulli_fisherInformation_upper ha.le (by linarith) hθ.le
  · have hp : 0 < Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation
        (-1 / 2) (1 / 2)
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2))
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPriorDeriv 0 (a / 2)) := by
      rw [Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation_smoothPrior
        (by positivity : 0 < a / 2) (by linarith) (by linarith)]
      positivity
    exact add_pos_of_pos_of_nonneg hp (MeasureTheory.integral_nonneg fun θ =>
      mul_nonneg
        (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
          (by positivity) θ)
        (MeasureTheory.integral_nonneg fun _ => mul_nonneg
          (twoArmRegularBernoulliLikelihood_nonneg θ _)
          (sq_nonneg _)))

-- @node: coarseTwoArmNumericalBound
/-- [the population size is positive](hyp:hn), [The elementary `n ≥ 8` estimate converting the smooth-prior fraction to the advertised coarse `n^{-4/3}` lower bound.](goal) -/
lemma coarseTwoArmNumericalBound (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ)⁻¹ - 43 * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤
      (1 - (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 /
        ((n : ℝ) / (1 - (n : ℝ) ^ (-(2 / 3 : ℝ)) / 4) +
          40 * (n : ℝ) ^ (2 / 3 : ℝ)) := by
  let a : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha3 : a ^ 3 = (n : ℝ)⁻¹ := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnR.le (-(1 / 3 : ℝ)) 3]
    norm_num
    exact Real.rpow_neg_one (n : ℝ)
  have ha_le : a ≤ 1 / 2 := by
    have hninv : (n : ℝ)⁻¹ ≤ (8 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ hnR (by norm_num)).2 (by exact_mod_cast hn)
    by_contra h
    have ha_gt : 1 / 2 < a := lt_of_not_ge h
    have ha_sq : (1 / 4 : ℝ) < a ^ 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
    have ha_cube : (1 / 8 : ℝ) < a ^ 3 := by
      have ha_gt' : (2 : ℝ)⁻¹ < a := by simpa [one_div] using ha_gt
      calc
        (1 / 8 : ℝ) < a ^ 2 / 2 := by linarith
        _ < a ^ 2 * a := by
          exact mul_lt_mul_of_pos_left ha_gt' (sq_pos_of_pos ha_pos)
        _ = a ^ 3 := by ring
    norm_num at hninv
    rw [ha3] at ha_cube
    linarith
  have ha2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) = a ^ 2 := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnR.le (-(1 / 3 : ℝ)) 2]
    congr 1
    ring
  have hna : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) * a := by
    dsimp [a]
    calc
      (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ ((1 : ℝ) + -(1 / 3 : ℝ)) := by
        congr 1 <;> ring
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_add hnR _ _
      _ = (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
  have hden_pos : 0 < 1 - a ^ 2 / 4 := by nlinarith [sq_nonneg a]
  have hinv : (1 - a ^ 2 / 4)⁻¹ ≤ 1 + a := by
    rw [show (1 - a ^ 2 / 4)⁻¹ = 1 / (1 - a ^ 2 / 4) by rw [one_div],
      div_le_iff₀ hden_pos]
    nlinarith [sq_nonneg a]
  have hratio :
      1 - 43 * a ≤ (1 - a) ^ 2 / (40 * a + (1 - a ^ 2 / 4)⁻¹) := by
    have hden2 : 0 < 40 * a + (1 - a ^ 2 / 4)⁻¹ := by positivity
    rw [le_div_iff₀ hden2]
    have hden_le : 40 * a + (1 - a ^ 2 / 4)⁻¹ ≤ 1 + 41 * a := by
      linarith
    by_cases h : 0 ≤ 1 - 43 * a
    · calc
        (1 - 43 * a) * (40 * a + (1 - a ^ 2 / 4)⁻¹) ≤
            (1 - 43 * a) * (1 + 41 * a) :=
          mul_le_mul_of_nonneg_left hden_le h
        _ ≤ (1 - a) ^ 2 := by nlinarith [sq_nonneg a]
    · have : (1 - 43 * a) * (40 * a + (1 - a ^ 2 / 4)⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hden2.le
      nlinarith [sq_nonneg (1 - a)]
  rw [ha2, hna]
  have hpow4 : (n : ℝ) ^ (-(4 / 3 : ℝ)) = (n : ℝ)⁻¹ * a := by
    dsimp [a]
    calc
      (n : ℝ) ^ (-(4 / 3 : ℝ)) =
          (n : ℝ) ^ ((-1 : ℝ) + -(1 / 3 : ℝ)) := by congr 1 <;> ring
      _ = (n : ℝ) ^ (-1 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_add hnR _ _
      _ = (n : ℝ)⁻¹ * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_neg_one]
  rw [hpow4]
  have hden_eq :
      (n : ℝ) / (1 - a ^ 2 / 4) + 40 * ((n : ℝ) * a) =
        (n : ℝ) * (40 * a + (1 - a ^ 2 / 4)⁻¹) := by
    field_simp [hden_pos.ne']
    ring
  rw [hden_eq]
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
  calc
    (n : ℝ)⁻¹ - 43 * ((n : ℝ)⁻¹ * a) =
        (n : ℝ)⁻¹ * (1 - 43 * a) := by ring
    _ ≤ (n : ℝ)⁻¹ *
        ((1 - a) ^ 2 / (40 * a + (1 - a ^ 2 / 4)⁻¹)) := by
      gcongr
    _ = (1 - a) ^ 2 /
        ((n : ℝ) * (40 * a + (1 - a ^ 2 / 4)⁻¹)) := by
      field_simp

-- @node: twoArmPosteriorCompat_fraction_le_mixedLoss
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the second arm count satisfies its stated condition](hyp:ha1), [the two arm posterior compat fraction is at most mixed loss](goal). -/
lemma twoArmPosteriorCompat_fraction_le_mixedLoss {n : ℕ} (hn : 0 < n) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) (f : ℕ → ℝ) :
    (1 - a) ^ 2 / ((n : ℝ) / (1 - a ^ 2 / 4) + 40 / a ^ 2) ≤
      Causalean.Stat.mixedKernelLoss (twoArmPosteriorCompat_smoothPriorMeasure a)
        (twoArmSmoothEffectKernel n a ha.le (by linarith))
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
          (fun e _ => effectTarget e))
        (fun x => clip twoArmContrast (f x)) := by
  let PM := Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    (-1 / 2) (1 / 2)
  let w := Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior 0 (a / 2)
  let dens : ℝ → ENNReal := fun θ => ENNReal.ofReal (w θ)
  let π := twoArmPosteriorCompat_smoothPriorMeasure a
  let K := twoArmSmoothEffectKernel n a ha.le (by linarith)
  let loss := Causalean.Stat.statewiseSquaredLoss
    (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n)) (fun e _ => effectTarget e)
  let Tc : Fin (n + 1) → ℝ := fun x => clip twoArmContrast (f x)
  letI : IsProbabilityMeasure π := twoArmPosteriorCompat_smoothPriorMeasure_isProbability a ha (by linarith)
  letI : IsFiniteMeasure PM := by
    dsimp [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure]
    infer_instance
  have hv := twoArmSmoothVanTreesErrorLowerBound hn a ha ha1
    (fun s => Tc (scoreCount s))
  apply hv.trans
  have herr : Integrable
      (Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w
        twoArmRegularBernoulliLikelihood (twoArmPosteriorTarget a)
          (fun s => Tc (scoreCount s))) (PM.prod Measure.count) := by
    exact twoArmErrorSqField_integrable a ha _
  rw [MeasureTheory.integral_prod _ herr]
  simp_rw [MeasureTheory.integral_count]
  have hdens : Measurable dens := by
    exact ENNReal.measurable_ofReal.comp
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_contDiff
        (by positivity : 0 < a / 2)).continuous.measurable
  have htop : ∀ᵐ θ ∂PM, dens θ < ⊤ := Filter.Eventually.of_forall fun θ => by
    simp [dens]
  have hgπ : Integrable (Causalean.Stat.kernelAverageLoss K loss Tc) π :=
    Causalean.Stat.integrable_kernelAverageLoss π K loss Tc
  have hg : Integrable (fun θ => w θ *
      (twoArmSmoothEffectDesign n a θ ha.le (by linarith)).E (loss Tc)) PM := by
    have h := (integrable_withDensity_iff hdens htop).1 hgπ
    apply h.congr
    filter_upwards with θ
    change Causalean.Stat.kernelAverageLoss K loss Tc θ * (dens θ).toReal = _
    rw [Causalean.Stat.kernelAverageLoss_eq_sum]
    dsimp only [K]
    simp_rw [twoArmSmoothEffectKernel_singletonReal]
    unfold FiniteDesign.E
    rw [ENNReal.toReal_ofReal
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
        (by positivity : 0 < a / 2) θ)]
    dsimp only [w]
    ring
  have hmixed : Causalean.Stat.mixedKernelLoss (twoArmPosteriorCompat_smoothPriorMeasure a)
      (twoArmSmoothEffectKernel n a ha.le (by linarith)) loss Tc =
      ∫ θ, w θ * (twoArmSmoothEffectDesign n a θ ha.le (by linarith)).E
        (loss Tc) ∂PM := by
    unfold Causalean.Stat.mixedKernelLoss twoArmPosteriorCompat_smoothPriorMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hdens htop]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal
      (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
        (by positivity : 0 < a / 2) θ)]
    change w θ * Causalean.Stat.kernelAverageLoss K loss Tc θ = _
    rw [Causalean.Stat.kernelAverageLoss_eq_sum]
    dsimp only [K]
    simp_rw [twoArmSmoothEffectKernel_singletonReal]
    unfold FiniteDesign.E
    rfl
  rw [hmixed]
  refine MeasureTheory.integral_mono_of_nonneg ?_ hg ?_
  · exact (show ∀ᵐ θ ∂PM, 0 ≤ ∑ s,
        Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w
          twoArmRegularBernoulliLikelihood (twoArmPosteriorTarget a)
            (fun s => Tc (scoreCount s)) (θ, s) from
      Filter.Eventually.of_forall fun θ => by
        unfold Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField
          Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity
        exact Finset.sum_nonneg fun s _ => mul_nonneg (sq_nonneg _)
          (mul_nonneg
            (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
              (by positivity : 0 < a / 2) θ)
            (twoArmRegularBernoulliLikelihood_nonneg θ s)))
  · filter_upwards with θ
    by_cases hw : w θ = 0
    · unfold Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField
        Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity
      simp [hw]
    · have hwpos : 0 < w θ := lt_of_le_of_ne
          (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_nonneg
            (by positivity : 0 < a / 2) θ) (Ne.symm hw)
      have hθ : |θ| < a / 2 := by
        simpa [w] using
          (Causalean.Stat.Limit.ObservationDependentVanTrees.smoothPrior_pos_iff
            (by positivity : 0 < a / 2)).mp hwpos
      unfold Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField
        Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity
      rw [show (∑ s, (Tc (scoreCount s) - twoArmPosteriorTarget a θ s) ^ 2 *
          (w θ * twoArmRegularBernoulliLikelihood θ s)) =
          w θ * ∑ s, twoArmBernoulliLikelihood θ s *
            (Tc (scoreCount s) - twoArmPosteriorTarget a θ s) ^ 2 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [twoArmRegularBernoulliLikelihood_eq
          (hθ.le.trans (by linarith : a / 2 ≤ 1))]
        ring]
      apply mul_le_mul_of_nonneg_left _ hwpos.le
      exact twoArmPosteriorCompat_error_le_effectRisk hn a θ ha.le ha1 hθ.le f

-- @node: twoArmPosteriorCompat_mixedLoss_clip_le
/-- [the first arm count satisfies its stated condition](hyp:ha0), [the second arm count satisfies its stated condition](hyp:ha1), [the two arm posterior compat mixed loss clip is at most property holds](goal). -/
lemma twoArmPosteriorCompat_mixedLoss_clip_le {n : ℕ} (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (π : Measure ℝ) [IsProbabilityMeasure π] (T : Fin (n + 1) → ℝ) :
    Causalean.Stat.mixedKernelLoss π (twoArmSmoothEffectKernel n a ha0 ha1)
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
          (fun e _ => effectTarget e))
        (fun x => clip twoArmContrast (T x)) ≤
      Causalean.Stat.mixedKernelLoss π (twoArmSmoothEffectKernel n a ha0 ha1)
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n))
          (fun e _ => effectTarget e)) T := by
  let K := twoArmSmoothEffectKernel n a ha0 ha1
  let loss := Causalean.Stat.statewiseSquaredLoss
    (twoArmCountKernel (twoArmPosteriorCompat_zeroAssignDesign n)) (fun e _ => effectTarget e)
  unfold Causalean.Stat.mixedKernelLoss
  apply MeasureTheory.integral_mono
    (Causalean.Stat.integrable_kernelAverageLoss π K loss
      (fun x => clip twoArmContrast (T x)))
    (Causalean.Stat.integrable_kernelAverageLoss π K loss T)
  intro θ
  rw [Causalean.Stat.kernelAverageLoss_eq_sum,
    Causalean.Stat.kernelAverageLoss_eq_sum]
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  dsimp only [loss]
  unfold Causalean.Stat.statewiseSquaredLoss
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (Causalean.Stat.kernelMass_nonneg _ _ _)
  change (Causalean.Mathlib.Analysis.clipIcc
      (-Lc twoArmContrast / 2) (Lc twoArmContrast / 2) (T x) - effectTarget e) ^ 2 ≤ _
  exact Causalean.Mathlib.Analysis.clipIcc_sub_sq_le
    (effectTarget_mem_twoArmRange e) _

-- @node: twoArmPosteriorCompat_fraction_le_rho2
/-- [the population size is positive](hyp:hn), [the parameter lies in the stated interval](hyp:ha), [the second arm count satisfies its stated condition](hyp:ha1), [the two arm posterior compat fraction is at most two-arm minimax risk](goal). -/
lemma twoArmPosteriorCompat_fraction_le_rho2 {n : ℕ} (hn : 0 < n) (a : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 / 2) :
    (1 - a) ^ 2 / ((n : ℝ) / (1 - a ^ 2 / 4) + 40 / a ^ 2) ≤ rho2 n := by
  let π := twoArmPosteriorCompat_smoothPriorMeasure a
  let K := twoArmSmoothEffectKernel n a ha.le (by linarith : a ≤ 1)
  let D := twoArmPosteriorCompat_zeroAssignDesign n
  let L := twoArmCountKernel D
  let target : EffectTriple n → Fin (n + 1) → ℝ := fun e _ => effectTarget e
  let loss := Causalean.Stat.statewiseSquaredLoss L target
  let B := (1 - a) ^ 2 / ((n : ℝ) / (1 - a ^ 2 / 4) + 40 / a ^ 2)
  letI : IsProbabilityMeasure π := twoArmPosteriorCompat_smoothPriorMeasure_isProbability a ha (by linarith)
  have hlower : ∀ T : Fin (n + 1) → ℝ,
      B ≤ Causalean.Stat.mixedKernelLoss π K loss T := by
    intro T
    let f : ℕ → ℝ := fun k => if hk : k < n + 1 then T ⟨k, hk⟩ else 0
    have hclip := twoArmPosteriorCompat_fraction_le_mixedLoss hn a ha ha1 f
    have hmono := twoArmPosteriorCompat_mixedLoss_clip_le (n := n) a ha.le
      (by linarith : a ≤ 1) π (fun x : Fin (n + 1) => f x)
    have hf : (fun x : Fin (n + 1) => f x) = T := by
      funext x
      simp only [f, dif_pos x.isLt]
    dsimp only [B, K, loss, L, D, target]
    rw [hf] at hmono
    exact hclip.trans hmono
  have hreal : B ≤ Causalean.Stat.realBayesRisk π K loss := by
    apply Causalean.Stat.mixedIntegratedLowerBound_le_realBayesRisk
      π K L target (fun T => Causalean.Stat.mixedKernelLoss π K loss T) B
    · intro T
      rfl
    · exact hlower
  have hscalar : B ≤ scalarBayesRisk
      (Causalean.Stat.inducedFiniteDesign π K) := by
    rw [← twoArmSmoothRealBayesRisk_eq_scalarBayesRisk
      a ha.le (by linarith : a ≤ 1) π D]
    exact hreal
  obtain ⟨lift, _, _, _, hkernel⟩ :=
    twoArmScalarPriorScheduleKernel (Causalean.Stat.inducedFiniteDesign π K)
  exact hscalar.trans
    (scalarBayesRisk_le_rho2_of_scheduleKernel
      (Causalean.Stat.inducedFiniteDesign π K) lift hkernel)


-- @node: thm:coarse-two-arm-minimax-lower
/-- [the population size is positive](hyp:hn), [the two-arm minimax risk obeys the stated finite-sample lower bound obtained from the smooth-prior Bayesian information inequality](goal). -/
theorem coarse_two_arm_minimax_lower (n : ℕ) (hn : 8 ≤ n) :
    ((1 - (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 /
      ((n : ℝ) / (1 - (n : ℝ) ^ (-(2 / 3 : ℝ)) / 4) +
        40 * (n : ℝ) ^ (2 / 3 : ℝ))) ≤ rho2 n ∧
    (n : ℝ)⁻¹ - 43 * (n : ℝ) ^ (-(4 / 3 : ℝ)) ≤ rho2 n := by
  let a : ℝ := (n : ℝ) ^ (-(1 / 3 : ℝ))
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by positivity
  have ha_pos : 0 < a := by dsimp [a]; positivity
  have ha3 : a ^ 3 = (n : ℝ)⁻¹ := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnR.le (-(1 / 3 : ℝ)) 3]
    norm_num
    exact Real.rpow_neg_one (n : ℝ)
  have ha_le : a ≤ 1 / 2 := by
    have hninv : (n : ℝ)⁻¹ ≤ (8 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ hnR (by norm_num)).2 (by exact_mod_cast hn)
    by_contra h
    have ha_gt : 1 / 2 < a := lt_of_not_ge h
    have ha_sq : (1 / 4 : ℝ) < a ^ 2 := by nlinarith [sq_nonneg (a - 1 / 2)]
    have ha_cube : (1 / 8 : ℝ) < a ^ 3 := by
      have ha_gt' : (2 : ℝ)⁻¹ < a := by simpa [one_div] using ha_gt
      calc
        (1 / 8 : ℝ) < a ^ 2 / 2 := by linarith
        _ < a ^ 2 * a := mul_lt_mul_of_pos_left ha_gt' (sq_pos_of_pos ha_pos)
        _ = a ^ 3 := by ring
    norm_num at hninv
    rw [ha3] at ha_cube
    linarith
  have ha2 : (n : ℝ) ^ (-(2 / 3 : ℝ)) = a ^ 2 := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast hnR.le (-(1 / 3 : ℝ)) 2]
    congr 1
    ring
  have hna : (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) * a := by
    dsimp [a]
    calc
      (n : ℝ) ^ (2 / 3 : ℝ) = (n : ℝ) ^ ((1 : ℝ) + -(1 / 3 : ℝ)) := by
        congr 1 <;> ring
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) :=
        Real.rpow_add hnR _ _
      _ = (n : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) := by rw [Real.rpow_one]
  have hainv2 : 1 / a ^ 2 = (n : ℝ) ^ (2 / 3 : ℝ) := by
    rw [hna]
    field_simp [ha_pos.ne', hnR.ne']
    rw [ha3]
    exact (inv_mul_cancel₀ hnR.ne').symm
  have hfirst := twoArmPosteriorCompat_fraction_le_rho2 hnpos a ha_pos ha_le
  have hfirst' :
      (1 - (n : ℝ) ^ (-(1 / 3 : ℝ))) ^ 2 /
          ((n : ℝ) / (1 - (n : ℝ) ^ (-(2 / 3 : ℝ)) / 4) +
            40 * (n : ℝ) ^ (2 / 3 : ℝ)) ≤ rho2 n := by
    rw [ha2, ← hainv2]
    rw [show (n : ℝ) ^ (-(1 / 3 : ℝ)) = a by rfl]
    simpa [div_eq_mul_inv] using hfirst
  exact ⟨hfirst', (coarseTwoArmNumericalBound n hn).trans hfirst'⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
