/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.UpperNoise
import Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.Tail

/-!
# Random-design weighted concentration on the good-Gram event

This module instantiates Causalean's finite-product conditional Hoeffding theorem.
The local-polynomial weights are stabilized off the good-Gram event so their
realized energy is everywhere positive; the resulting tail is then restricted
back to the good event used by the atom-fallback interval.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators

noncomputable section

private abbrev ClampDesign (J : ℕ) := Fin J × ℝ

/-- On the good-Gram event the exact equivalent-kernel weights have strictly
positive realized squared energy. The result uses [the `hlambda` condition](hyp:hlambda), [the `hgood` condition](hyp:hgood). [This is the stated conclusion](goal).
-/
lemma good_gram_positive_energy {J n ell : ℕ}
    (B : SplitBlocks n) (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) :
    0 < ∑ i, (localRegressionDesignWeight (ell := ell) B x
      kappa cminus cplus delta h
      (Causalean.Mathlib.Probability.designVector
        (fun o : ClampObs J => (o.X, o.A)) z) i) ^ 2 := by
  classical
  have hrep := goodGram_reproduction B z x kappa cminus cplus delta h
    hlambda hgood (0 : Fin (ell + 1))
  simp only [Fin.isValue, if_pos] at hrep
  simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow, zero_pow
    (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_contra hnot
  have hle : (∑ i ∈ B.I2,
      (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2) ≤ 0 :=
    le_of_not_gt hnot
  have hsqzero (i : Fin n) (hi : i ∈ B.I2) :
      (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2 = 0 := by
    apply le_antisymm
    · exact hle.trans' (Finset.single_le_sum
        (fun j _ => sq_nonneg
          (interceptWeight B z x ell kappa cminus cplus delta h j)) hi)
    · exact sq_nonneg _
  have hwzero (i : Fin n) (hi : i ∈ B.I2) :
      interceptWeight B z x ell kappa cminus cplus delta h i = 0 :=
    sq_eq_zero_iff.mp (hsqzero i hi)
  rw [Finset.sum_eq_zero (fun i hi => by simp [hwzero i hi])] at hrep
  norm_num at hrep

/-- Complete-design-measurable local-polynomial weights, replaced off the
good-Gram event by one fixed unit coordinate. -/
def stabilizedWeight {J n ell : ℕ} (B : SplitBlocks n) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (i₀ : Fin n) :
    (Fin n → ClampDesign J) → Fin n → ℝ := by
  classical
  exact fun d i =>
    if GoodGramEvent B (fun j => clampDesignLift (d j)) x ell
        kappa cminus cplus delta h then
      localRegressionDesignWeight (ell := ell) B x
        kappa cminus cplus delta h d i
    else if i = i₀ then 1 else 0

/-- [stabilized weight is measurable](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `i₀` input](hyp:i₀). -/
lemma stabilizedWeight_measurable {J n ell : ℕ} (B : SplitBlocks n)
    (x : Fin J) (kappa cminus cplus delta h : ℝ) (i₀ : Fin n) :
    Measurable (stabilizedWeight (ell := ell) B x
      kappa cminus cplus delta h i₀) := by
  classical
  apply measurable_pi_lambda
  intro i
  refine Measurable.ite ?_ ?_ measurable_const
  · apply (goodGramEvent_measurable B x kappa cminus cplus delta h).preimage
    exact measurable_pi_lambda _ fun j =>
      clampDesignLift_measurable.comp (measurable_pi_apply j)
  · exact (measurable_pi_apply i).comp
      (localRegressionDesignWeight_measurable (ell := ell) B x
        kappa cminus cplus delta h)

/-- [the stated stabilized weight identity on good property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `i₀` input](hyp:i₀), [the specified `hgood` input](hyp:hgood). -/
lemma stabilizedWeight_eq_on_good {J n ell : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (i₀ : Fin n)
    (hgood : GoodGramEvent B z x ell kappa cminus cplus delta h) :
    stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) =
    localRegressionDesignWeight (ell := ell) B x
        kappa cminus cplus delta h
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) := by
  funext i
  have hgood' : GoodGramEvent B
      (fun j => clampDesignLift
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z j)) x ell
        kappa cminus cplus delta h := by
    change GoodGramEvent B z x ell kappa cminus cplus delta h
    exact hgood
  simp [stabilizedWeight, hgood']

/-- [the stated stabilized weight positive energy property holds](goal) for [the specified `J` input](hyp:J), [the specified `n` input](hyp:n), [the specified `ell` input](hyp:ell), [the specified `B` input](hyp:B), [the specified `z` input](hyp:z), [the specified `x` input](hyp:x), [the specified `kappa` input](hyp:kappa), [the specified `cminus` input](hyp:cminus), [the specified `cplus` input](hyp:cplus), [the specified `delta` input](hyp:delta), [the specified `h` input](hyp:h), [the specified `i₀` input](hyp:i₀), [the specified `hlambda` input](hyp:hlambda). -/
lemma stabilizedWeight_positive_energy {J n ell : ℕ} (B : SplitBlocks n)
    (z : Fin n → ClampObs J) (x : Fin J)
    (kappa cminus cplus delta h : ℝ) (i₀ : Fin n)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus) :
    0 < Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.realizedWeightEnergy
      (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀)
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) := by
  classical
  unfold Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.realizedWeightEnergy
  by_cases hgood : GoodGramEvent B z x ell kappa cminus cplus delta h
  · rw [stabilizedWeight_eq_on_good B z x kappa cminus cplus delta h i₀ hgood]
    exact good_gram_positive_energy B z x kappa cminus cplus delta h hlambda hgood
  · have hone : stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z) i₀ = 1 := by
      have hgood' : ¬ GoodGramEvent B
          (fun j => clampDesignLift
            (Causalean.Mathlib.Probability.designVector
              (fun o : ClampObs J => (o.X, o.A)) z j)) x ell
            kappa cminus cplus delta h := by
        change ¬ GoodGramEvent B z x ell kappa cminus cplus delta h
        exact hgood
      simp [stabilizedWeight, hgood']
    have hsingle : (0 : ℝ) <
        (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀
          (Causalean.Mathlib.Probability.designVector
            (fun o : ClampObs J => (o.X, o.A)) z) i₀) ^ 2 := by
      rw [hone]
      norm_num
    exact lt_of_lt_of_le hsingle
      (Finset.single_le_sum (fun i _ => sq_nonneg
        (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀
          (Causalean.Mathlib.Probability.designVector
            (fun o : ClampObs J => (o.X, o.A)) z) i)) (Finset.mem_univ i₀))

/-- The finite-product random-design Hoeffding tail for the stabilized weights.
This is the direct Causalean theorem at the paper's observed-sample abstraction. The result uses [the `hmodel` condition](hyp:hmodel), [the `hlambda` condition](hyp:hlambda), [the `ht` condition](hyp:ht). [This is the stated conclusion](goal).
-/
lemma stabilized_weighted_tail {J n ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (B : SplitBlocks n) (x : Fin J) (delta h t : ℝ) (i₀ : Fin n)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus) (ht : 0 ≤ t) :
    (iidProduct P n).real {z |
      t * Real.sqrt
          (Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.realizedWeightEnergy
            (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀)
            (Causalean.Mathlib.Probability.designVector
              (fun o : ClampObs J => (o.X, o.A)) z)) ≤
        |Causalean.Mathlib.Probability.weightedCenteredSum
          (fun o : ClampObs J => (o.X, o.A)) (fun o => o.Y)
          (clampRegressionExtension P)
          (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀) z|} ≤
      2 * Real.exp (-2 * t ^ 2) := by
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  apply Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.product_weighted_centered_tail_le
    P.dataMeasure (fun o : ClampObs J => (o.X, o.A)) clampDesign_measurable
    (fun o : ClampObs J => o.Y) clampOutcome_measurable
    (hmodel.outcomeSupport.mono fun _ ho => ho.1)
    (hmodel.outcomeSupport.mono fun _ ho => ho.2)
    (clampRegressionExtension P) (clampRegressionExtension_measurable P hmodel.holder)
    (clampRegression_condExp P hmodel x)
    (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀)
    (stabilizedWeight_measurable B x kappa cminus cplus delta h i₀)
    (by
      filter_upwards with z
      exact stabilizedWeight_positive_energy B z x kappa cminus cplus delta h i₀ hlambda)
    ht

/-- Restricting the stabilized tail back to the good-Gram event recovers the
paper's exact local-polynomial weighted residual sum. The result uses [the `hmodel` condition](hyp:hmodel), [the `hlambda` condition](hyp:hlambda), [the `ht` condition](hyp:ht). [This is the stated conclusion](goal).
-/
lemma block_weighted_tail_on_good_gram {J n ell : ℕ} (P : ClampLaw J)
    {beta kappa L cminus cplus pmin : ℝ}
    (hmodel : ClampModel P beta kappa L cminus cplus pmin)
    (B : SplitBlocks n) (x : Fin J) (delta h t : ℝ) (i₀ : Fin n)
    (hlambda : 0 < lambdaStar ell kappa cminus cplus) (ht : 0 ≤ t) :
    (iidProduct P n).real {z |
      GoodGramEvent B z x ell kappa cminus cplus delta h ∧
      t * Real.sqrt (∑ i ∈ B.I2,
          (interceptWeight B z x ell kappa cminus cplus delta h i) ^ 2) ≤
        |∑ i ∈ B.I2,
          interceptWeight B z x ell kappa cminus cplus delta h i *
            ((z i).Y - clampRegressionExtension P ((z i).X, (z i).A))|} ≤
      2 * Real.exp (-2 * t ^ 2) := by
  letI : IsProbabilityMeasure P.dataMeasure := hmodel.probability
  letI : IsProbabilityMeasure (iidProduct P n) := by
    unfold iidProduct
    infer_instance
  have htail := stabilized_weighted_tail P hmodel B x delta h t i₀ hlambda ht
  refine (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans htail
  intro z hz
  rcases hz with ⟨hgood, hbound⟩
  change t * Real.sqrt
      (Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.realizedWeightEnergy
        (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀)
        (Causalean.Mathlib.Probability.designVector
          (fun o : ClampObs J => (o.X, o.A)) z)) ≤
    |Causalean.Mathlib.Probability.weightedCenteredSum
      (fun o : ClampObs J => (o.X, o.A)) (fun o => o.Y)
      (clampRegressionExtension P)
      (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀) z|
  have hw := stabilizedWeight_eq_on_good B z x kappa cminus cplus delta h i₀ hgood
  have hcentered :
      Causalean.Mathlib.Probability.weightedCenteredSum
          (fun o : ClampObs J => (o.X, o.A)) (fun o => o.Y)
          (clampRegressionExtension P)
          (stabilizedWeight (ell := ell) B x kappa cminus cplus delta h i₀) z =
        Causalean.Mathlib.Probability.weightedCenteredSum
          (fun o : ClampObs J => (o.X, o.A)) (fun o => o.Y)
          (clampRegressionExtension P)
          (localRegressionDesignWeight (ell := ell) B x
            kappa cminus cplus delta h) z := by
    unfold Causalean.Mathlib.Probability.weightedCenteredSum
    rw [hw]
  rw [hcentered, weightedCenteredSum_localRegression]
  unfold Causalean.Stat.Concentration.RandomDesignWeightedHoeffding.realizedWeightEnergy
  rw [hw]
  simp_rw [localRegressionDesignWeight_apply (ell := ell), ite_pow, zero_pow
    (by norm_num : 2 ≠ 0)]
  rw [← Finset.sum_filter]
  simpa only [Finset.filter_mem_eq_inter, Finset.univ_inter] using hbound

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
