module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.CommonMarginalTransferConcentration

/-! Fixed-sample common-marginal transfer and its canonical calibrated family. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer

/-! The transfer rule is factored from the canonical construction so that the
paper lemma below says only what its frozen statement says: a fixed-sample
risk implication for any supplied recipe carrying the Poisson-prior witness. -/

/-- Fixed-sample transfer for one exact witness of the Poisson-prior
construction, with the labeled and auxiliary intensities fixed at the two
unequal sample-size scales from the paper.  [the stated conditions](hyp:Cfixed,cSmall,cRisk,CBound,rho,calibration) [the stated conclusion](goal). -/
def FixedSampleCommonMarginalTransferRuleAt {eps : Real}
    (Cfixed cSmall cRisk CBound rho : Real)
    (calibration : CommonMarginalCalibration eps) : Prop :=
  ∀ (n m d : Nat) (H : CommonMarginalPriorHandle calibration n m d),
    1 ≤ n → 2 ≤ d →
    CommonMarginalExactPoissonPriorWitness
      calibration.bandwidthConstant (n + m : Nat) H.recipe
      (u := commonMarginalLabeledIntensity Cfixed n)
      (v := commonMarginalAuxiliaryIntensity Cfixed n m)
      (C := CBound) (rho := rho) →
    Causalean.Stat.tvDist H.recipe.rawExperiment0 H.recipe.rawExperiment1 ≤ 1 / 8 →
    H.k * H.B * H.a ≤ cSmall *
      |rawPriorCenter H.recipe true - rawPriorCenter H.recipe false| ^ 2 →
    cRisk *
        |rawPriorCenter H.recipe true - rawPriorCenter H.recipe false| ^ 2 ≤
      minimaxRisk n m d eps

-- @node: helper:common-marginal-explicit-parametric-floor
private lemma commonMarginal_explicit_parametric_floor
    (eps : Real) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (n m d : Nat) (hn : 1 ≤ n) (hd : 2 ≤ d) :
    (1 / 100 : Real) / n ≤ minimaxRisk n m d eps := by
  letI : Nonempty (Fin d) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_two hd⟩⟩
  let delta : Real := (2 / 5) / Real.sqrt n
  have hnR : (0 : Real) < n := by exact_mod_cast hn
  have hd0 : 0 ≤ delta := by dsimp [delta]; positivity
  have hdsq : delta ^ 2 = 4 / (25 * (n : Real)) := by
    dsimp [delta]; rw [div_pow, Real.sq_sqrt hnR.le]; ring
  let hv0 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_null
    (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real)) (g₁ := (1 / 2 : Real))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hdu : (1 / 2 : Real) + delta ≤ 1 := by
    have hs : 1 ≤ Real.sqrt (n : Real) := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    have : delta ≤ 2 / 5 := by dsimp [delta]; exact div_le_self (by norm_num) hs
    linarith
  let hv1 := Causalean.Estimation.MinimaxATE.Parametric.validDGP_pert
    (C := Fin d) (m₀ := (1 / 2 : Real)) (g₀ := (1 / 2 : Real)) (g₁ := (1 / 2 : Real))
    (δ := delta) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hd0 hdu
  let P0 := parametricFloorNullLaw hv0
  let P1 := parametricFloorPertLaw hv1
  let MP0 : ClassLaw d eps := ⟨P0, parametricFloorNullLaw_model hd heps heps2 hv0⟩
  let MP1 : ClassLaw d eps := ⟨P1, parametricFloorPertLaw_model hd heps heps2 hv1⟩
  have hreg : (n : Real) * ((1 / 2 : Real) * delta ^ 2 /
      ((1 / 2 : Real) * (1 - 1 / 2))) ≤ Real.log 2 := by
    rw [hdsq]
    have hlog : (8 / 25 : Real) ≤ Real.log 2 :=
      le_trans (by norm_num) (le_of_lt Real.log_two_gt_d9)
    convert hlog using 1 <;> field_simp [hnR.ne'] <;> ring
  have htvL : Causalean.Stat.tvDist (labeledProductLaw P0 n)
      (labeledProductLaw P1 n) ≤ 1 / 2 := by
    simpa [P0, P1, parametricFloorNullLaw, parametricFloorPertLaw, labeledProductLaw,
      obsLaw, Causalean.Estimation.MinimaxATE.productLaw,
      Causalean.Estimation.MinimaxATE.obsLaw] using
      (Causalean.Estimation.MinimaxATE.Parametric.tvDist_productLaw_le_half
        hv0 hv1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hreg)
  have haux : auxProductLaw P0 m = auxProductLaw P1 m := by
    unfold auxProductLaw
    rw [parametricFloor_auxMarginal_eq hv0 hv1]
  have htv : Causalean.Stat.tvDist (annotationLaw P0 n m)
      (annotationLaw P1 n m) ≤ 1 / 2 := by
    haveI : IsProbabilityMeasure (labeledProductLaw P0 n) := by
      unfold labeledProductLaw; infer_instance
    haveI : IsProbabilityMeasure (labeledProductLaw P1 n) := by
      unfold labeledProductLaw; infer_instance
    haveI : IsProbabilityMeasure (auxProductLaw P1 m) := by
      unfold auxProductLaw; infer_instance
    rw [annotationLaw, haux]
    calc
      _ ≤ Causalean.Stat.tvDist (labeledProductLaw P0 n) (labeledProductLaw P1 n) +
          Causalean.Stat.tvDist (auxProductLaw P1 m) (auxProductLaw P1 m) :=
        Causalean.Stat.Minimax.MomentMatchedMixture.tvDist_prod_le_add _ _ _ _
      _ ≤ 1 / 2 := by
        have hz : Causalean.Stat.tvDist (auxProductLaw P1 m)
            (auxProductLaw P1 m) = 0 := by
          apply le_antisymm
          · unfold Causalean.Stat.tvDist
            exact ciSup_le fun A => by simp
          · exact Causalean.Stat.tvDist_nonneg
        rw [hz]
        linarith
  have hsep : 2 * (delta / 2) ≤
      |ateFunctional MP0.1 - ateFunctional MP1.1| := by
    rw [show ateFunctional MP0.1 = 0 by
          simpa [MP0, P0] using parametricFloorNullLaw_ate hv0,
      show ateFunctional MP1.1 = delta by
          simpa [MP1, P1] using parametricFloorPertLaw_ate hv1]
    rw [show 2 * (delta / 2) = delta by ring, zero_sub, abs_neg, abs_of_nonneg hd0]
  have hlow := annotationMinimaxRisk_ge_two_model_tv MP0 MP1 (s := delta / 2)
    (by positivity) hsep htv
  calc
    1 / 100 / (n : Real) = (delta / 2) ^ 2 / 4 := by
      rw [show (delta / 2) ^ 2 = delta ^ 2 / 4 by ring, hdsq]
      ring
    _ ≤ minimaxRisk n m d eps := hlow

/-! The analytic transfer argument only needs a realized recipe and its
Poisson-prior witness.  Keeping this core at recipe level lets both the
uniform-bandwidth recipe produced by `common_marginal_poisson_prior` and the
separate paper-facing C55 handle reuse the same proof. -/

/-- [Under the stated overlap, positivity, sample-size, witness, affinity, and
variance conditions](hyp:heps,heps2,hCBound,hn,hd,hprior,htv,hvariance),
the recipe's squared raw-center separation [gives the stated fixed-sample
minimax-risk lower bound](goal). -/
lemma fixed_sample_common_marginal_recipe_transfer_rule
    (eps : Real) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (calibration : CommonMarginalCalibration eps) (CBound rho : Real)
    (hCBound : 0 < CBound)
    (n m d L k : Nat) (B a : Real)
    (R : CommonMarginalRecipe calibration n m d L B a k)
    (hn : 1 ≤ n) (hd : 2 ≤ d)
    (hprior : CommonMarginalPoissonPriorWitness R
      (u := commonMarginalLabeledIntensity 65536 n)
      (v := commonMarginalAuxiliaryIntensity 65536 n m)
      (C := CBound) (rho := rho))
    (htv : Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤ 1 / 8)
    (hvariance : k * B * a ≤ (1 / (65536 * CBound)) *
      |rawPriorCenter R true - rawPriorCenter R false| ^ 2) :
    (1 / 65536) *
        |rawPriorCenter R true - rawPriorCenter R false| ^ 2 ≤
      minimaxRisk n m d eps := by
  let Delta := |rawPriorCenter R true - rawPriorCenter R false|
  let u : Real := commonMarginalLabeledIntensity 65536 n
  let v : Real := commonMarginalAuxiliaryIntensity 65536 n m
  have hu : 0 ≤ u := by
    dsimp [u, commonMarginalLabeledIntensity]
    positivity
  have hv : 0 ≤ v := by
    dsimp [v, commonMarginalAuxiliaryIntensity]
    positivity
  have hDelta0 : 0 ≤ Delta := by
    exact abs_nonneg _
  have hDelta_le : Delta ≤ 2 := by
    have hfalse := commonMarginal_rawPriorCenter_abs_le_one R hprior.bounds false
    have htrue := commonMarginal_rawPriorCenter_abs_le_one R hprior.bounds true
    dsimp [Delta]
    rw [abs_le]
    constructor <;> linarith [le_abs_self (rawPriorCenter R false),
      le_abs_self (rawPriorCenter R true), neg_le_of_abs_le hfalse,
      neg_le_of_abs_le htrue]
  letI : IsProbabilityMeasure (commonMarginalRecipePriorOf R false) := by
    dsimp [commonMarginalRecipePriorOf]
    exact R.probability0
  letI : IsProbabilityMeasure (commonMarginalRecipePriorOf R true) := by
    dsimp [commonMarginalRecipePriorOf]
    exact R.probability1
  letI : IsProbabilityMeasure R.prior0 := by
    exact R.probability0
  have hclass : Nonempty (ClassLaw d eps) := by
    rcases hprior.bounds.class0.exists with ⟨P, hP⟩
    exact ⟨⟨P, hP⟩⟩
  letI : Nonempty (ClassLaw d eps) := hclass
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have hfixed : IsFixedTwoPoolExperiment n m
      (commonMarginalFixedKernel n m d)
      (commonMarginalLabeledMarkKernel d) (commonMarginalAuxMarkKernel d) := by
    intro P
    rfl
  have hraw := commonMarginal_orderedRaw_isRandomScale R
    (Real.toNNReal u) (Real.toNNReal v)
  have hpredictive : Causalean.Stat.tvDist
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (commonMarginalRecipePriorOf R false)
        (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v)))
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
        (commonMarginalRecipePriorOf R true)
        (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v))) ≤ 1 / 8 := by
    have hc := commonMarginal_predictive_reconstruction_contraction R hu hv
      hprior.labeledIntensity_eq hprior.auxiliaryIntensity_eq
    simpa [commonMarginalRecipePriorOf] using hc.trans htv
  let cFloor : Real := 1 / 100
  have hcFloor : 0 < cFloor := by dsimp [cFloor]; norm_num
  have hfloor : cFloor / n ≤ minimaxRisk n m d eps := by
    exact commonMarginal_explicit_parametric_floor eps heps heps2 n m d hn hd
  have hfloorRisk : ENNReal.ofReal (cFloor / n) ≤
      minimaxDecisionRisk (commonMarginalFixedKernel n m d)
        (commonMarginalTransferLoss eps) := by
    exact (ENNReal.ofReal_le_ofReal hfloor).trans
      (commonMarginal_ofReal_minimax_le_classGated n m d eps)
  by_cases hDelta_zero : Delta = 0
  · dsimp [Delta] at hDelta_zero ⊢
    rw [hDelta_zero]
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    nlinarith [hfloor, div_pos hcFloor hnR]
  have hDelta : 0 < Delta := lt_of_le_of_ne hDelta0 (Ne.symm hDelta_zero)
  have hvariance' := hvariance
  field_simp at hvariance'
  have htransfer := randomScale_twoFuzzy_minimax_lower_transfer
    (commonMarginalRecipePriorOf R false) (commonMarginalRecipePriorOf R true)
    (commonMarginalOrderedRawKernel R (Real.toNNReal u) (Real.toNNReal v))
    (commonMarginalFixedKernel n m d)
    (commonMarginalLabeledMarkKernel d) (commonMarginalAuxMarkKernel d)
    (fun P => Real.toNNReal (R.rawScale P)) R.rawScale_measurable.real_toNNReal
    (Real.toNNReal u) (Real.toNNReal v) (1 / 2)
    hraw hfixed (commonMarginalTransferLoss eps) 4 (by norm_num)
    (commonMarginalTransferLoss_measurable eps)
    (commonMarginalTransferLoss_le_four eps)
    (fun _ => Classical.arbitrary (Obs d))
    (fun _ => Classical.arbitrary (AuxObs d)) 0
    (ENNReal.ofReal (3 * Delta ^ 2 / 128))
    (ENNReal.ofReal (Delta ^ 2 / 16384))
    (ENNReal.ofReal (1 / (4096 * (n : Real))))
    (ENNReal.ofReal (1 / (4096 * (n : Real))))
    (by
      intro rawRule hrawRule
      refine commonMarginal_raw_fuzzy_lower R hprior.bounds _ (fun P => ?_)
        hDelta
        (by simp [Delta])
        ?_ ?_ hpredictive rawRule hrawRule
      · dsimp only [commonMarginalOrderedRawKernel]
        letI : IsProbabilityMeasure (obsLaw P) := inferInstance
        letI : IsProbabilityMeasure (auxMarginal P).toMeasure := inferInstance
        change IsProbabilityMeasure
          ((Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
              (obsLaw P) (Real.toNNReal u * Real.toNNReal (R.rawScale P))).prod
            (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
              (auxMarginal P).toMeasure
              (Real.toNNReal v * Real.toNNReal (R.rawScale P))))
        exact Measure.prod.instIsProbabilityMeasure _ _
      · exact (commonMarginal_prior_target_concentration R hprior.bounds false
          hDelta hDelta_le).trans (by
            rw [div_le_iff₀ (sq_pos_of_pos hDelta)]
            dsimp [Delta]
            nlinarith [hvariance'])
      · exact (commonMarginal_prior_target_concentration R hprior.bounds true
          hDelta hDelta_le).trans (by
            rw [div_le_iff₀ (sq_pos_of_pos hDelta)]
            dsimp [Delta]
            nlinarith [hvariance']))
    (by
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (ENNReal.ofReal_ne_top)).mp
      rw [ENNReal.toReal_ofReal (by positivity)]
      exact (commonMarginal_prior_scale_tail R hprior.bounds false).trans (by
        dsimp [Delta]
        nlinarith [hvariance']))
    (by
      apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
        (ENNReal.ofReal_ne_top)).mp
      rw [ENNReal.toReal_ofReal (by positivity)]
      exact (commonMarginal_prior_scale_tail R hprior.bounds true).trans (by
        dsimp [Delta]
        nlinarith [hvariance']))
    (by
      intro P hscale
      apply commonMarginal_poisson_lower_tail n hn
      have hucoe : (Real.toNNReal u : Real) = u := Real.coe_toNNReal _ hu
      have hscoe : (1 / 2 : Real) ≤ Real.toNNReal (R.rawScale P) := by
        exact_mod_cast hscale
      calc
        (32768 : Real) * n = u * (1 / 2 : Real) := by
          dsimp [u, commonMarginalLabeledIntensity]
          ring
        _ ≤ u * (Real.toNNReal (R.rawScale P) : Real) :=
          mul_le_mul_of_nonneg_left hscoe hu
        _ = (Real.toNNReal u * Real.toNNReal (R.rawScale P) : NNReal) := by
          rw [NNReal.coe_mul, hucoe])
    (by
      intro P hscale
      refine (measure_mono (Set.Iio_subset_Iio (Nat.le_add_left m n))).trans ?_
      refine (commonMarginal_poisson_lower_tail (n + m) (by omega) _ ?_).trans ?_
      have hvcoe : (Real.toNNReal v : Real) = v := Real.coe_toNNReal _ hv
      have hscoe : (1 / 2 : Real) ≤ Real.toNNReal (R.rawScale P) := by
        exact_mod_cast hscale
      · calc
          (32768 : Real) * ((n + m : Nat) : Real) = v * (1 / 2 : Real) := by
            dsimp [v, commonMarginalAuxiliaryIntensity]
            push_cast
            ring
          _ ≤ v * (Real.toNNReal (R.rawScale P) : Real) :=
            mul_le_mul_of_nonneg_left hscoe hv
          _ = (Real.toNNReal v * Real.toNNReal (R.rawScale P) : NNReal) := by
            rw [NNReal.coe_mul, hvcoe]
      · apply ENNReal.ofReal_le_ofReal
        have hnR : (0 : Real) < n := by exact_mod_cast hn
        have hnmR : (n : Real) ≤ (n + m : Nat) := by exact_mod_cast Nat.le_add_right n m
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith)
  have hdecision : max
      (ENNReal.ofReal (3 * Delta ^ 2 / 128) -
        4 * (ENNReal.ofReal (Delta ^ 2 / 16384) +
          ENNReal.ofReal (1 / (4096 * (n : Real))) +
          ENNReal.ofReal (1 / (4096 * (n : Real)))))
      (ENNReal.ofReal (cFloor / n)) ≤
      ENNReal.ofReal (minimaxRisk n m d eps) :=
    -- The transfer theorem now yields only the penalised raw bound; the floor branch is
    -- discharged here from `hfloorRisk`, which is where that fact actually comes from.
    max_le (htransfer.trans (commonMarginal_classGated_minimax_le n m d eps))
      (hfloorRisk.trans (commonMarginal_classGated_minimax_le n m d eps))
  have hminimax0 : 0 ≤ minimaxRisk n m d eps := by
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    exact (div_pos hcFloor hnR).le.trans hfloor
  apply (ENNReal.ofReal_le_ofReal_iff hminimax0).mp
  refine (show ENNReal.ofReal ((1 / 65536) * Delta ^ 2) ≤
      ENNReal.ofReal (minimaxRisk n m d eps) from ?_)
  by_cases hlarge : 1 / (n : Real) ≤ Delta ^ 2
  · have hlargeENN : ENNReal.ofReal ((1 / 65536) * Delta ^ 2) ≤
        ENNReal.ofReal (3 * Delta ^ 2 / 128) -
          4 * (ENNReal.ofReal (Delta ^ 2 / 16384) +
            ENNReal.ofReal (1 / (4096 * (n : Real))) +
            ENNReal.ofReal (1 / (4096 * (n : Real)))) := by
      have hpenalty :
          4 * (ENNReal.ofReal (Delta ^ 2 / 16384) +
            ENNReal.ofReal (1 / (4096 * (n : Real))) +
            ENNReal.ofReal (1 / (4096 * (n : Real)))) =
          ENNReal.ofReal (4 * (Delta ^ 2 / 16384 +
            1 / (4096 * (n : Real)) + 1 / (4096 * (n : Real)))) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
          ENNReal.toReal_add (by finiteness) (by finiteness)]
        simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤ Delta ^ 2 / 16384),
          ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (4096 * (n : Real))),
          ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 *
            (Delta ^ 2 / 16384 + 1 / (4096 * (n : Real)) +
              1 / (4096 * (n : Real))))]
        norm_num
      rw [hpenalty, ← ENNReal.ofReal_sub _ (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      field_simp [hnR.ne'] at hlarge ⊢
      nlinarith
    exact (hlargeENN.trans (le_max_left _ _)).trans hdecision
  · have hsmallENN : ENNReal.ofReal ((1 / 65536) * Delta ^ 2) ≤
        ENNReal.ofReal (cFloor / n) := by
      apply ENNReal.ofReal_le_ofReal
      have hsmall : Delta ^ 2 < 1 / (n : Real) := lt_of_not_ge hlarge
      have hnR : (0 : Real) < n := by exact_mod_cast hn
      dsimp [cFloor]
      field_simp [hnR.ne'] at hsmall ⊢
      nlinarith
    exact (hsmallENN.trans (le_max_right _ _)).trans hdecision

-- @node: helper:fixed-sample-common-marginal-transfer-rule
/-- Compatibility wrapper for the canonical C55 handle construction.  The
tagged paper lemma below consumes the inequality-only witness directly and
therefore subsumes this exact-bandwidth specialization. -/
private lemma fixed_sample_common_marginal_transfer_rule
    (eps : Real) (heps : 0 < eps) (heps2 : eps < 1 / 2)
    (calibration : CommonMarginalCalibration eps) (CBound rho : Real)
    (hCBound : 0 < CBound) :
    FixedSampleCommonMarginalTransferRuleAt 65536 (1 / (65536 * CBound))
      (1 / 65536) CBound rho calibration := by
  intro n m d H hn hd hprior htv hvariance
  exact fixed_sample_common_marginal_recipe_transfer_rule eps heps heps2
    calibration CBound rho hCBound n m d H.L H.k H.B H.a H.recipe hn hd
    hprior.witness htv hvariance

-- @node: lem:fixed-sample-common-marginal-transfer
/-- The fixed-sample risk transfer for every supplied uniform-intensity recipe.
The variance-bound constant is universal, and the concentration threshold may
depend on it and on `eps`.  The recipe is not selected here: both the exact
`bε L / (u + v)` specialization and C55 recipes allowed by the bandwidth
inequality are covered through `CommonMarginalPoissonPriorWitness`.  [the stated conclusion](goal). -/
lemma fixed_sample_common_marginal_transfer :
    ∃ Cfixed cRisk : Real,
      0 < Cfixed ∧ 0 < cRisk ∧
      ∀ (eps : Real), 0 < eps → eps < 1 / 2 →
        ∀ CBound : Real, 0 < CBound →
          ∃ cSmall : Real, 0 < cSmall ∧
            ∀ (calibration : CommonMarginalCalibration eps) (rho : Real)
              (n m d L k : Nat) (B a : Real)
              (R : CommonMarginalRecipe calibration n m d L B a k),
              1 ≤ n → 2 ≤ d →
              CommonMarginalPoissonPriorWitness R
                (u := commonMarginalLabeledIntensity Cfixed n)
                (v := commonMarginalAuxiliaryIntensity Cfixed n m)
                (C := CBound) (rho := rho) →
              Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤ 1 / 8 →
              k * B * a ≤ cSmall *
                  |rawPriorCenter R true - rawPriorCenter R false| ^ 2 →
              cRisk * |rawPriorCenter R true - rawPriorCenter R false| ^ 2 ≤
                minimaxRisk n m d eps := by
  refine ⟨65536, 1 / 65536, by norm_num, by norm_num, ?_⟩
  intro eps heps heps2
  intro CBound hCBound
  let cSmall : Real := 1 / (65536 * CBound)
  refine ⟨cSmall, by
    dsimp [cSmall]
    positivity, ?_⟩
  intro calibration rho n m d L k B a R hn hd hprior htv hvariance
  exact fixed_sample_common_marginal_recipe_transfer_rule eps heps heps2
    calibration CBound rho hCBound n m d L k B a R hn hd hprior htv
      (by simpa [cSmall] using hvariance)

/-- A single construction chain chooses the fixed intensity and risk constants
first, then an epsilon-only calibration and its variance-absorption threshold,
and finally constructs, for every instance, one paper-facing handle together
with a certificate for that very same recipe.  The transfer rule recorded
beside the family is the rule proved by
`fixed_sample_common_marginal_transfer`, so the producer and consumer use the
identical constants at their respective quantifier levels.  [the stated conclusion](goal). -/
lemma common_marginal_canonical_certificate_family :
    ∃ Cfixed cRisk : Real,
      0 < Cfixed ∧ 0 < cRisk ∧
      ∀ (eps : Real), 0 < eps → eps < 1 / 2 →
        ∃ calibration : CommonMarginalCalibration eps,
          ∃ CBound rho cSmall cFloor : Real,
            0 < CBound ∧ rho ∈ Set.Ioo (0 : Real) 1 ∧
            0 < cSmall ∧ 0 < cFloor ∧ cFloor ≤ cRisk ∧
            FixedSampleCommonMarginalTransferRuleAt
              Cfixed cSmall cRisk CBound rho calibration ∧
            ∀ (n m d : Nat), 1 ≤ n → 2 ≤ d →
              ∃ H : CommonMarginalPriorHandle calibration n m d,
                CommonMarginalCanonicalCertificate
                  Cfixed cSmall cFloor CBound rho H := by
  refine ⟨65536, 1 / 65536, by norm_num, by norm_num, ?_⟩
  intro eps heps heps2
  rcases common_marginal_uniform_intensity eps heps heps2 with
    ⟨calibration, C, rho, hC, hrho, closure, realize⟩
  let cSmall : Real := 1 / (65536 * C)
  let cFloor : Real := 1 / 65536
  have hcSmall : 0 < cSmall := by dsimp [cSmall]; positivity
  have hcFloor : 0 < cFloor := by dsimp [cFloor]; norm_num
  refine ⟨calibration, C, rho, cSmall, cFloor, hC, hrho, hcSmall,
    hcFloor, by rfl, ?_, ?_⟩
  · exact fixed_sample_common_marginal_transfer_rule eps heps heps2
      calibration C rho hC
  · intro n m d hn hd
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hN : (0 : Real) < (n + m : Nat) := by positivity
    have hgapRoot : calibration.dualGap / Real.sqrt n ≤ 1 / 4 := by
      have hs : 1 ≤ Real.sqrt (n : Real) :=
        Real.one_le_sqrt.mpr (by exact_mod_cast hn)
      calc
        calibration.dualGap / Real.sqrt n ≤ calibration.dualGap :=
          div_le_self calibration.dualGap_pos.le hs
        _ ≤ 1 / 4 := calibration.dualGap_le_quarter
    by_cases hreg : commonMarginalParametricRegime calibration n m d
    · let H := parametricCommonMarginalPriorHandle calibration n m d hd hn
        heps heps2 hreg hgapRoot
      refine ⟨H, ?_⟩
      have hdegree : 2 ≤ H.L :=
        commonMarginal_degree_lower closure n H.L hn H.degree_eq
      have hbandConst : 2 * (65536 : Real) * calibration.bandwidthConstant ≤
          calibration.uniformBandwidthConstant := by
        simpa only [show (2 : Real) * 65536 = 131072 by norm_num] using
          closure.bandwidthSlack
      have hband :
          (commonMarginalLabeledIntensity 65536 n +
              commonMarginalAuxiliaryIntensity 65536 n m) * H.B ≤
            calibration.uniformBandwidthConstant * H.L := by
        rw [H.bandwidth_eq]
        unfold commonMarginalLabeledIntensity commonMarginalAuxiliaryIntensity
        push_cast
        have hnN : (n : Real) ≤ (n + m : Nat) := by
          exact_mod_cast Nat.le_add_right n m
        have hb0 := calibration.bandwidthConstant_pos
        have hL0 : (0 : Real) ≤ H.L := by positivity
        calc
          (65536 * (n : Real) + 65536 * ((n : Real) + (m : Real))) *
              (calibration.bandwidthConstant * (H.L : Real) /
                ((n : Real) + (m : Real))) ≤
              (131072 * ((n : Real) + (m : Real))) *
                (calibration.bandwidthConstant * (H.L : Real) /
                  ((n : Real) + (m : Real))) := by
            have hsum : 65536 * (n : Real) + 65536 * ((n : Real) + (m : Real)) ≤
                131072 * ((n : Real) + (m : Real)) := by
              nlinarith [show (0 : Real) ≤ m by positivity]
            exact mul_le_mul_of_nonneg_right hsum
              (div_nonneg
                (mul_nonneg calibration.bandwidthConstant_pos.le (Nat.cast_nonneg _))
                (by positivity))
          _ = 131072 * calibration.bandwidthConstant * H.L := by
            field_simp [show ((n + m : Nat) : Real) ≠ 0 by exact_mod_cast
              (show n + m ≠ 0 by omega)]
          _ ≤ calibration.uniformBandwidthConstant * H.L := by
            exact mul_le_mul_of_nonneg_right closure.bandwidthSlack hL0
      refine
        { degree_ge_two := hdegree
          transferBandwidthConstants := hbandConst
          bandwidthClosure := hband
          rareShiftSmall := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          sameTable := map_auxMarginal_commonMarginalPriorOf_eq H
          poissonPriorWitness := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          bounds := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          mixtureTV := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          centerSeparation := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          varianceAbsorption := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          transferredRisk := by intro h; exact False.elim (H.branchCondition.mp h hreg)
          floorRisk := by
            exact (by
              dsimp [cFloor]
              calc
                (1 / 65536 : Real) / n ≤ (1 / 100 : Real) / n := by
                  gcongr <;> norm_num
                _ ≤ minimaxRisk n m d eps :=
                  commonMarginal_explicit_parametric_floor eps heps heps2 n m d hn hd)
          dimensionNonparametric := by
            intro h; exact False.elim (H.branchCondition.mp h hreg)
          dimensionParametric := by
            intro _
            have hdim := closure.dimensionFloor
            have hreg' := hreg
            unfold commonMarginalParametricRegime at hreg'
            dsimp [cFloor]
            have hn0 : 0 ≤ (n : Real) := hnR.le
            calc
              calibration.dimensionConstant * commonMarginalDimensionTerm n m d ≤
                  calibration.dimensionConstant *
                    (calibration.regimeConstant / (n : Real)) :=
                mul_le_mul_of_nonneg_left hreg'
                  calibration.dimensionConstant_pos.le
              _ = (calibration.dimensionConstant * calibration.regimeConstant) /
                    (n : Real) := by ring
              _ ≤ (1 / 65536) / (n : Real) :=
                div_le_div_of_nonneg_right hdim hn0 }
    · let L := Nat.ceil (calibration.degreeConstant * logEN n)
      let B : Real := calibration.bandwidthConstant * L / (n + m : Nat)
      let a : Real := calibration.gamma * B / (L : Real) ^ 2
      let k := min (d - 1)
        ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
      have hL : 2 ≤ L := commonMarginal_degree_lower closure n L hn rfl
      have hLpos : (0 : Real) < L := by exact_mod_cast (show 0 < L by omega)
      have hB : 0 < B := by
        dsimp [B]
        exact div_pos (mul_pos calibration.bandwidthConstant_pos hLpos)
          (by exact_mod_cast hN)
      have ha : 0 < a := by
        dsimp [a]
        exact div_pos (mul_pos calibration.gamma_pos hB) (sq_pos_of_pos hLpos)
      have hkfit : k + 1 ≤ d := by
        dsimp [k]
        have := min_le_left (d - 1)
          ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
        omega
      have hkFloor : (k : Real) ≤
          calibration.rareCountConstant * (n + m : Nat) * L := by
        calc
          (k : Real) ≤
              (⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊ : Nat) := by
            exact_mod_cast min_le_right (d - 1)
              ⌊calibration.rareCountConstant * (n + m : Nat) * L⌋₊
          _ ≤ calibration.rareCountConstant * (n + m : Nat) * L :=
            Nat.floor_le (mul_nonneg
              (mul_nonneg calibration.rareCountConstant_pos.le (Nat.cast_nonneg _))
              (Nat.cast_nonneg _))
      have hka : (k : Real) * a ≤ calibration.dualGap := by
        have hfactor : 0 ≤ calibration.gamma * calibration.bandwidthConstant /
            (((n + m : Nat) : Real) * L) := by
          exact div_nonneg (mul_nonneg calibration.gamma_pos.le
            calibration.bandwidthConstant_pos.le)
            (mul_nonneg (by exact_mod_cast hN.le) hLpos.le)
        have hm := mul_le_mul_of_nonneg_right hkFloor hfactor
        dsimp [a, B]
        calc
          (k : Real) *
              (calibration.gamma *
                (calibration.bandwidthConstant * (L : Real) / (n + m : Nat)) /
                  (L : Real) ^ 2) =
              (k : Real) * (calibration.gamma * calibration.bandwidthConstant /
                (((n + m : Nat) : Real) * L)) := by
            field_simp [show ((n + m : Nat) : Real) ≠ 0 by exact_mod_cast
              (show n + m ≠ 0 by omega), ne_of_gt hLpos]
          _ ≤ (calibration.rareCountConstant * (n + m : Nat) * L) *
                (calibration.gamma * calibration.bandwidthConstant /
                  (((n + m : Nat) : Real) * L)) := hm
          _ = calibration.rareCountConstant * calibration.gamma *
                calibration.bandwidthConstant := by
            field_simp [show ((n + m : Nat) : Real) ≠ 0 by exact_mod_cast
              (show n + m ≠ 0 by omega), ne_of_gt hLpos]
          _ ≤ calibration.dualGap := closure.rareScale
      have hu : 0 ≤ commonMarginalLabeledIntensity 65536 n := by
        unfold commonMarginalLabeledIntensity; positivity
      have hv : 0 ≤ commonMarginalAuxiliaryIntensity 65536 n m := by
        unfold commonMarginalAuxiliaryIntensity; positivity
      have huv : 0 < commonMarginalLabeledIntensity 65536 n +
          commonMarginalAuxiliaryIntensity 65536 n m := by
        unfold commonMarginalLabeledIntensity commonMarginalAuxiliaryIntensity
        positivity
      have hband :
          (commonMarginalLabeledIntensity 65536 n +
              commonMarginalAuxiliaryIntensity 65536 n m) * B ≤
            calibration.uniformBandwidthConstant * L := by
        dsimp [B]
        unfold commonMarginalLabeledIntensity commonMarginalAuxiliaryIntensity
        push_cast
        have hnN : (n : Real) ≤ (n + m : Nat) := by
          exact_mod_cast Nat.le_add_right n m
        calc
          (65536 * (n : Real) + 65536 * ((n : Real) + (m : Real))) *
              (calibration.bandwidthConstant * (L : Real) /
                ((n : Real) + (m : Real))) ≤
              (131072 * ((n : Real) + (m : Real))) *
                (calibration.bandwidthConstant * (L : Real) /
                  ((n : Real) + (m : Real))) := by
            have hsum : 65536 * (n : Real) + 65536 * ((n : Real) + (m : Real)) ≤
                131072 * ((n : Real) + (m : Real)) := by
              nlinarith [show (0 : Real) ≤ m by positivity]
            exact mul_le_mul_of_nonneg_right hsum
              (div_nonneg
                (mul_nonneg calibration.bandwidthConstant_pos.le (Nat.cast_nonneg _))
                (by positivity))
          _ = 131072 * calibration.bandwidthConstant * L := by
            field_simp [show ((n + m : Nat) : Real) ≠ 0 by exact_mod_cast
              (show n + m ≠ 0 by omega)]
          _ ≤ calibration.uniformBandwidthConstant * L :=
            mul_le_mul_of_nonneg_right closure.bandwidthSlack (Nat.cast_nonneg _)
      rcases realize n m L hn hL
          (commonMarginalLabeledIntensity 65536 n)
          (commonMarginalAuxiliaryIntensity 65536 n m) B a k d hd hu hv huv
          hband hB rfl hka hkfit with ⟨R, hRu, hRv, _, _, bounds⟩
      let H : CommonMarginalPriorHandle calibration n m d :=
        { L := L, B := B, a := a, k := k, recipe := R
          branchCondition := by simp [bounds.finiteAtomConstruction, hreg]
          degree_eq := rfl, bandwidth_eq := rfl, shift_eq := rfl,
          rareCount_eq := rfl }
      have exactWitness : CommonMarginalExactPoissonPriorWitness
          calibration.bandwidthConstant (n + m : Nat) R
          (u := commonMarginalLabeledIntensity 65536 n)
          (v := commonMarginalAuxiliaryIntensity 65536 n m)
          (C := C) (rho := rho) :=
        { sampleSize_pos := hn, degree_ge_two := hL, dimension_ge_two := hd
          labeledIntensity_nonneg := hu, auxiliaryIntensity_nonneg := hv
          totalIntensity_pos := huv, rareCount_fit := hkfit
          bandwidthDenominator_pos := by positivity
          bandwidth_eq := rfl, bandwidth_bound := hband, bandwidth_pos := hB
          shift_eq := rfl, rareShiftSmall := hka
          labeledIntensity_eq := hRu, auxiliaryIntensity_eq := hRv
          bounds := bounds
          witness := ⟨hband, hB, rfl, hka, hRu, hRv, bounds⟩ }
      have htv : Causalean.Stat.tvDist R.rawExperiment0 R.rawExperiment1 ≤ 1 / 8 := by
        calc
          _ ≤ C * commonMarginalLabeledIntensity 65536 n * k * a * rho ^ L :=
            bounds.mixtureTV
          _ = C * (65536 * (n : Real)) * ((k : Real) * a) * rho ^ L := by
            unfold commonMarginalLabeledIntensity
            ring
          _ ≤ C * (65536 * (n : Real)) * calibration.dualGap * rho ^ L := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hka (by positivity)) (pow_nonneg hrho.1.le _)
          _ ≤ 1 / 8 := by simpa [L] using closure.mixtureDecay n hn
      have hkLower := commonMarginal_rareCount_degree_lower hC closure
        n m d L k hn hd rfl rfl hreg
      have hvariance : (k : Real) * B * a ≤
          cSmall * (calibration.dualGap * k * a) ^ 2 := by
        have hK : 0 < cSmall * calibration.dualGap ^ 2 * calibration.gamma := by
          exact mul_pos (mul_pos hcSmall (sq_pos_of_pos calibration.dualGap_pos))
            calibration.gamma_pos
        have hcore : (L : Real) ^ 2 ≤
            (k : Real) * (cSmall * calibration.dualGap ^ 2 * calibration.gamma) := by
          exact (div_le_iff₀ hK).mp (by simpa [cSmall] using hkLower)
        have hmult : 0 ≤ (k : Real) * a ^ 2 / calibration.gamma := by
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
            calibration.gamma_pos.le
        calc
          (k : Real) * B * a =
              ((k : Real) * a ^ 2 / calibration.gamma) * (L : Real) ^ 2 := by
            dsimp [a]
            field_simp [ne_of_gt calibration.gamma_pos, ne_of_gt hLpos]
          _ ≤ ((k : Real) * a ^ 2 / calibration.gamma) *
                ((k : Real) * (cSmall * calibration.dualGap ^ 2 * calibration.gamma)) :=
            mul_le_mul_of_nonneg_left hcore hmult
          _ = cSmall * (calibration.dualGap * k * a) ^ 2 := by
            field_simp [ne_of_gt calibration.gamma_pos]
      have hfloorRisk : cFloor / n ≤ minimaxRisk n m d eps := by
        dsimp [cFloor]
        calc
          (1 / 65536 : Real) / n ≤ (1 / 100 : Real) / n := by
            gcongr <;> norm_num
          _ ≤ minimaxRisk n m d eps :=
            commonMarginal_explicit_parametric_floor eps heps heps2 n m d hn hd
      have htransferred : cFloor * commonMarginalDelta H ^ 2 ≤
          minimaxRisk n m d eps := by
        have hvarianceActual : (k : Real) * B * a ≤ cSmall *
            |rawPriorCenter R true - rawPriorCenter R false| ^ 2 := by
          calc
            (k : Real) * B * a ≤
                cSmall * (calibration.dualGap * k * a) ^ 2 := hvariance
            _ ≤ cSmall *
                |rawPriorCenter R true - rawPriorCenter R false| ^ 2 := by
              have hsep := bounds.separation
              have hlower : 0 ≤ calibration.dualGap * (k : Real) * a := by
                exact mul_nonneg
                  (mul_nonneg calibration.dualGap_pos.le (Nat.cast_nonneg _)) ha.le
              exact mul_le_mul_of_nonneg_left
                ((sq_le_sq₀ hlower (abs_nonneg _)).2 hsep) hcSmall.le
        have htransferredActual : cFloor *
            |rawPriorCenter R true - rawPriorCenter R false| ^ 2 ≤
              minimaxRisk n m d eps := by
          exact fixed_sample_common_marginal_transfer_rule eps heps heps2
            calibration C rho hC n m d H hn hd exactWitness htv (by
              simpa [H, cSmall] using hvarianceActual)
        calc
          cFloor * commonMarginalDelta H ^ 2 ≤ cFloor *
              |rawPriorCenter R true - rawPriorCenter R false| ^ 2 := by
            have hsep := bounds.separation
            have hlower : 0 ≤ commonMarginalDelta H := by
              exact mul_nonneg
                (mul_nonneg calibration.dualGap_pos.le (Nat.cast_nonneg _)) ha.le
            dsimp [commonMarginalDelta, H] at hsep ⊢
            exact mul_le_mul_of_nonneg_left
              ((sq_le_sq₀ hlower (abs_nonneg _)).2 hsep) hcFloor.le
          _ ≤ minimaxRisk n m d eps := htransferredActual
      refine ⟨H, ?_⟩
      exact
        { degree_ge_two := hL
          transferBandwidthConstants := by
            simpa only [show (2 : Real) * 65536 = 131072 by norm_num] using
              closure.bandwidthSlack
          bandwidthClosure := hband
          rareShiftSmall := by intro _; exact hka
          sameTable := map_auxMarginal_commonMarginalPriorOf_eq H
          poissonPriorWitness := by intro _; exact exactWitness
          bounds := by intro _; exact bounds
          mixtureTV := by intro _; exact htv
          centerSeparation := by
            intro _
            simpa [H, commonMarginalDelta] using bounds.separation
          varianceAbsorption := by
            intro _
            simpa [H, commonMarginalDelta] using hvariance
          transferredRisk := by intro _; exact htransferred
          floorRisk := hfloorRisk
          dimensionNonparametric := by
            intro _
            simpa [H, commonMarginalDelta] using
              (commonMarginal_dimension_absorption closure n m d L k hn hd
                rfl rfl a rfl)
          dimensionParametric := by
            intro hfalse
            exact False.elim (hfalse bounds.finiteAtomConstruction) }

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
