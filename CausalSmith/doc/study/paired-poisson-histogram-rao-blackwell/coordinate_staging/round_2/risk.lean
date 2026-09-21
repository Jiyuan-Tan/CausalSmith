/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram.FixedRisk
import Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.Depoissonization

/-!
# Paired Poisson-histogram Rao--Blackwell risk transfer

This module defines the histogram law of a finite Poisson sample, proves the
squared-risk transfer for two independent histogram laws with an explicit
fallback penalty, and specializes both means to twice the fixed sample size.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson intensity](hyp:lam),
the [count-histogram law](goal) is the distribution of the unordered histogram of a finite
Poisson sample. -/
noncomputable def countLaw
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    Measure (X → ℕ) :=
  Measure.map (fun s : FiniteSample X => finiteSampleHistogram s.points)
    (finitePoissonSampleLaw P lam)

/-- [The map from a finite sample to its histogram is measurable](goal) over a finite
alphabet with measurable singletons. -/
@[fun_prop]
theorem measurable_finiteSampleHistogram
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] :
    Measurable (fun s : FiniteSample X => finiteSampleHistogram s.points) := by
  -- `FiniteSample X` is countable for finite `X`; use the discrete/countable
  -- measurability instance rather than unfolding the dependent sample type.
  apply measurable_to_countable'
  intro c
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((Sigma.mk m) ⁻¹'
    {s : FiniteSample X | finiteSampleHistogram s.points = c})
  exact (Set.to_countable _).measurableSet

/-- Given [a finite-alphabet probability law](hyp:P) and [a Poisson intensity](hyp:lam),
[the total count under the histogram law has the scalar Poisson distribution with that
intensity](goal). -/
theorem countLaw_map_histogramTotal
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) :
    Measure.map histogramTotal (countLaw P lam) = poissonMeasure lam := by
  -- Compose the two pushforwards with `Measure.map_map`, identify their
  -- composite pointwise by `histogramTotal_finiteSampleHistogram`, and finish
  -- with `finitePoissonSampleLaw_map_count`.
  unfold countLaw
  rw [Measure.map_map (measurable_of_countable histogramTotal)
    measurable_finiteSampleHistogram]
  have hcomp :
      histogramTotal ∘
          (fun s : FiniteSample X => finiteSampleHistogram s.points) =
        FiniteSample.count := by
    funext s
    exact histogramTotal_finiteSampleHistogram s.points
  rw [hcomp]
  exact finitePoissonSampleLaw_map_count P lam

private lemma countLaw_restrict_histogramTotal_eq
    {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0) (N : ℕ) :
    (countLaw P lam).restrict (histogramTotal ⁻¹' ({N} : Set ℕ)) =
      (poissonMeasure lam) {N} •
        Measure.map (fun z : Fin N → X => finiteSampleHistogram z)
          (Measure.pi (fun _ : Fin N => P)) := by
  unfold countLaw
  rw [Measure.restrict_map measurable_finiteSampleHistogram
    ((measurable_of_countable histogramTotal) (measurableSet_singleton N))]
  have hpre :
      (fun s : FiniteSample X => finiteSampleHistogram s.points) ⁻¹'
          (histogramTotal ⁻¹' ({N} : Set ℕ)) =
        FiniteSample.count ⁻¹' ({N} : Set ℕ) := by
    ext s
    simp only [mem_preimage, mem_singleton_iff]
    rw [histogramTotal_finiteSampleHistogram]
  rw [hpre, finitePoissonSampleLaw_restrict_count_eq,
    Measure.map_smul, Measure.map_map measurable_finiteSampleHistogram
      (measurable_fixedSizeEmbed N)]
  rfl

private lemma pairedPoissonHistogramEstimator_sq_sub_le_sum
    {n : ℕ} {X Y : Type*}
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (est : (Fin n → X × Y) → ℝ) (fallback theta : ℝ)
    (cX : X → ℕ) (cY : Y → ℕ) :
    (pairedPoissonHistogramEstimator est fallback (cX, cY) - theta) ^ 2 ≤
      (∑ z : Fin n → X × Y, (est z - theta) ^ 2) +
        (fallback - theta) ^ 2 := by
  classical
  by_cases hX : n ≤ histogramTotal cX
  · by_cases hY : n ≤ histogramTotal cY
    · rw [pairedPoissonHistogramEstimator_of_totals_ge est fallback cX cY hX hY]
      refine (pairedHistogramAverage_sq_sub_le est theta cX cY hX hY).trans ?_
      have hcard :
          (0 : ℝ) < Fintype.card (HistogramFiber cX) *
            Fintype.card (HistogramFiber cY) := by
        letI : Nonempty (HistogramFiber cX) := histogramFiber_nonempty cX
        letI : Nonempty (HistogramFiber cY) := histogramFiber_nonempty cY
        positivity
      apply (div_le_iff₀ hcard).2
      calc
        (∑ x : HistogramFiber cX, ∑ y : HistogramFiber cY,
            (est (pairRetainedArrays (retainedHistogramPrefix hX x)
              (retainedHistogramPrefix hY y)) - theta) ^ 2) ≤
            ∑ x : HistogramFiber cX, ∑ _y : HistogramFiber cY,
              ∑ z : Fin n → X × Y, (est z - theta) ^ 2 := by
          apply Finset.sum_le_sum
          intro x _hx
          apply Finset.sum_le_sum
          intro y _hy
          exact Finset.single_le_sum (fun z _hz => sq_nonneg (est z - theta))
            (Finset.mem_univ
              (pairRetainedArrays (retainedHistogramPrefix hX x)
                (retainedHistogramPrefix hY y)))
        _ = (Fintype.card (HistogramFiber cX) *
              Fintype.card (HistogramFiber cY) : ℝ) *
              ∑ z : Fin n → X × Y, (est z - theta) ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
        _ ≤ (Fintype.card (HistogramFiber cX) *
              Fintype.card (HistogramFiber cY) : ℝ) *
              ((∑ z : Fin n → X × Y, (est z - theta) ^ 2) +
                (fallback - theta) ^ 2) := by
          gcongr
          exact le_add_of_nonneg_right (sq_nonneg _)
      simpa [mul_comm]
    · rw [pairedPoissonHistogramEstimator_of_total_lt est fallback cX cY
          (Or.inr (Nat.lt_of_not_ge hY))]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · rw [pairedPoissonHistogramEstimator_of_total_lt est fallback cX cY
        (Or.inl (Nat.lt_of_not_ge hX))]
    exact le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Given [two finite-alphabet probability laws](hyp:P,Q), [their Poisson
intensities](hyp:lamP,lamQ), [a paired fixed-sample estimator](hyp:est), [a fallback
value](hyp:fallback), and [a real target](hyp:theta), [the paired histogram estimator has
integrable squared loss and risk at most the paired fixed-sample risk plus the fallback
loss times the sum of the two marginal lower-tail probabilities](goal). -/
theorem pairedPoissonHistogramRisk_le_fixedRisk_add_tails
    {n : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lamP lamQ : ℝ≥0) (est : (Fin n → X × Y) → ℝ)
    (fallback theta : ℝ) :
    Integrable
        (fun c => (pairedPoissonHistogramEstimator est fallback c - theta) ^ 2)
        ((countLaw P lamP).prod (countLaw Q lamQ)) ∧
      (∫ c, (pairedPoissonHistogramEstimator est fallback c - theta) ^ 2
          ∂((countLaw P lamP).prod (countLaw Q lamQ))) ≤
        (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
        (fallback - theta) ^ 2 *
          ((poissonMeasure lamP).real {k | k < n} +
            (poissonMeasure lamQ).real {k | k < n}) := by
  -- First rewrite the product count law as the image of the product of the
  -- two `finitePoissonSampleLaw`s (`Measure.map_prod_map` and `Measure.map_map`).
  -- Split that source law over the count pair `(NX, NY)`.  The public lemma
  -- `finitePoissonSampleLaw_restrict_count_eq` identifies each factor on a
  -- singleton count fibre with its Poisson mass times the fixed-size iid law.
  -- For `n ≤ NX` and `n ≤ NY`, simplify the estimator on the two sample
  -- histograms and apply `pairedHistogramAverage_productRisk_le`; otherwise
  -- use `pairedPoissonHistogramEstimator_of_total_lt`.  Sum the successful
  -- bounds using that their Poisson weights have total at most one.  The
  -- failure probability is the union of the two marginal lower-tail events;
  -- bound it by their sum and rewrite the marginals with
  -- `countLaw_map_histogramTotal`.  Since the estimator has finite range
  -- (the fixed estimator's domain is finite, plus the fallback), the squared
  -- loss is bounded and hence integrable under the probability count law.
  classical
  let μP := countLaw P lamP
  let μQ := countLaw Q lamQ
  let μ := μP.prod μQ
  let loss : ((X → ℕ) × (Y → ℕ)) → ℝ := fun c =>
    (pairedPoissonHistogramEstimator est fallback c - theta) ^ 2
  let fixedRisk : ℝ :=
    ∫ z, (est z - theta) ^ 2 ∂Measure.pi (fun _ : Fin n => P.prod Q)
  let fallbackLoss : ℝ := (fallback - theta) ^ 2
  let goodX : Set (X → ℕ) := {c | n ≤ histogramTotal c}
  let goodY : Set (Y → ℕ) := {c | n ≤ histogramTotal c}
  let good : Set ((X → ℕ) × (Y → ℕ)) := goodX ×ˢ goodY
  let cell : (Set.Ici n × Set.Ici n) → Set ((X → ℕ) × (Y → ℕ)) := fun NM =>
    (histogramTotal ⁻¹' ({NM.1.1} : Set ℕ)) ×ˢ
      (histogramTotal ⁻¹' ({NM.2.1} : Set ℕ))
  letI : IsProbabilityMeasure μP := by
    dsimp [μP, countLaw]
    exact Measure.isProbabilityMeasure_map measurable_finiteSampleHistogram.aemeasurable
  letI : IsProbabilityMeasure μQ := by
    dsimp [μQ, countLaw]
    exact Measure.isProbabilityMeasure_map measurable_finiteSampleHistogram.aemeasurable
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hloss_meas : Measurable loss := by
    exact ((measurable_pairedPoissonHistogramEstimator est fallback).sub
      measurable_const).pow_const 2
  have hloss_bound (c : (X → ℕ) × (Y → ℕ)) :
      loss c ≤ (∑ z : Fin n → X × Y, (est z - theta) ^ 2) + fallbackLoss := by
    exact pairedPoissonHistogramEstimator_sq_sub_le_sum
      est fallback theta c.1 c.2
  have hloss_int : Integrable loss μ := by
    apply Integrable.of_bound hloss_meas.aestronglyMeasurable
      ((∑ z : Fin n → X × Y, (est z - theta) ^ 2) + fallbackLoss)
    filter_upwards [] with c
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hloss_bound c
  have hfixed_int : Integrable (fun z : Fin n → X × Y =>
      (est z - theta) ^ 2) (Measure.pi (fun _ : Fin n => P.prod Q)) :=
    Integrable.of_finite
  have hfixed_nonneg : 0 ≤ fixedRisk := by
    exact integral_nonneg fun z => sq_nonneg (est z - theta)
  have hgood_meas : MeasurableSet good := by
    exact (Set.to_countable goodX).measurableSet.prod
      (Set.to_countable goodY).measurableSet
  have hcell_meas (NM : Set.Ici n × Set.Ici n) : MeasurableSet (cell NM) := by
    exact ((measurable_of_countable histogramTotal)
      (measurableSet_singleton NM.1.1)).prod
        ((measurable_of_countable histogramTotal)
          (measurableSet_singleton NM.2.1))
  have hcell_disjoint : Pairwise (Function.onFun Disjoint cell) := by
    intro NM KL hne
    change Disjoint (cell NM) (cell KL)
    rw [Set.disjoint_left]
    intro c hcNM hcKL
    simp only [cell, mem_prod, mem_preimage, mem_singleton_iff] at hcNM hcKL
    apply hne
    ext
    · exact hcNM.1.symm.trans hcKL.1
    · exact hcNM.2.symm.trans hcKL.2
  have hgood_union : good = ⋃ NM, cell NM := by
    ext c
    simp only [good, goodX, goodY, mem_prod, mem_setOf_eq, mem_iUnion,
      cell, mem_preimage, mem_singleton_iff]
    constructor
    · intro hc
      exact ⟨(⟨histogramTotal c.1, hc.1⟩, ⟨histogramTotal c.2, hc.2⟩), rfl, rfl⟩
    · rintro ⟨NM, hNX, hNY⟩
      exact ⟨hNX.symm ▸ NM.1.2, hNY.symm ▸ NM.2.2⟩
  have hcell_mass (NM : Set.Ici n × Set.Ici n) :
      μ.real (cell NM) =
        (poissonMeasure lamP).real {NM.1.1} *
          (poissonMeasure lamQ).real {NM.2.1} := by
    have hPmap := countLaw_map_histogramTotal P lamP
    have hQmap := countLaw_map_histogramTotal Q lamQ
    have hP : μP (histogramTotal ⁻¹' ({NM.1.1} : Set ℕ)) =
        poissonMeasure lamP {NM.1.1} := by
      rw [← hPmap, Measure.map_apply (measurable_of_countable histogramTotal)
        (measurableSet_singleton NM.1.1)]
    have hQ : μQ (histogramTotal ⁻¹' ({NM.2.1} : Set ℕ)) =
        poissonMeasure lamQ {NM.2.1} := by
      rw [← hQmap, Measure.map_apply (measurable_of_countable histogramTotal)
        (measurableSet_singleton NM.2.1)]
    simp only [μ, cell, measureReal_def, Measure.prod_prod, hP, hQ,
      ENNReal.toReal_mul]
  have hcell_le (NM : Set.Ici n × Set.Ici n) :
      (∫ c in cell NM, loss c ∂μ) ≤ μ.real (cell NM) * fixedRisk := by
    have hNX : n ≤ NM.1.1 := by simpa only [Set.mem_Ici] using NM.1.2
    have hNY : n ≤ NM.2.1 := by simpa only [Set.mem_Ici] using NM.2.2
    let histX : (Fin NM.1.1 → X) → (X → ℕ) := finiteSampleHistogram
    let histY : (Fin NM.2.1 → Y) → (Y → ℕ) := finiteSampleHistogram
    have hmapX : Measurable histX := measurable_of_countable _
    have hmapY : Measurable histY := measurable_of_countable _
    have hloss_map : AEStronglyMeasurable loss
        (Measure.map (Prod.map histX histY)
          ((Measure.pi (fun _ : Fin NM.1.1 => P)).prod
            (Measure.pi (fun _ : Fin NM.2.1 => Q)))) :=
      hloss_meas.aestronglyMeasurable
    change (∫ c, loss c ∂μ.restrict (cell NM)) ≤ _
    rw [← Measure.prod_restrict]
    change (∫ c, loss c ∂
      (μP.restrict (histogramTotal ⁻¹' ({NM.1.1} : Set ℕ))).prod
        (μQ.restrict (histogramTotal ⁻¹' ({NM.2.1} : Set ℕ)))) ≤ _
    rw [show μP.restrict (histogramTotal ⁻¹' ({NM.1.1} : Set ℕ)) =
        (poissonMeasure lamP) {NM.1.1} •
          Measure.map histX (Measure.pi (fun _ : Fin NM.1.1 => P)) by
        simpa [μP, histX] using countLaw_restrict_histogramTotal_eq P lamP NM.1.1,
      show μQ.restrict (histogramTotal ⁻¹' ({NM.2.1} : Set ℕ)) =
        (poissonMeasure lamQ) {NM.2.1} •
          Measure.map histY (Measure.pi (fun _ : Fin NM.2.1 => Q)) by
        simpa [μQ, histY] using countLaw_restrict_histogramTotal_eq Q lamQ NM.2.1,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      Measure.map_prod_map _ _ hmapX hmapY, integral_smul_measure,
      integral_map (hmapX.prodMap hmapY).aemeasurable hloss_map,
      ENNReal.toReal_mul, hcell_mass]
    apply mul_le_mul_of_nonneg_left
    · have hfun : (fun z : (Fin NM.1.1 → X) × (Fin NM.2.1 → Y) =>
          loss (Prod.map histX histY z)) =
          fun z => (pairedHistogramAverage est
            (finiteSampleHistogram z.1) (finiteSampleHistogram z.2)
            (by simpa only [histogramTotal_finiteSampleHistogram] using hNX)
            (by simpa only [histogramTotal_finiteSampleHistogram] using hNY) - theta) ^ 2 := by
        funext z
        change (pairedPoissonHistogramEstimator est fallback
          (finiteSampleHistogram z.1, finiteSampleHistogram z.2) - theta) ^ 2 = _
        rw [pairedPoissonHistogramEstimator_of_totals_ge est fallback
          (finiteSampleHistogram z.1) (finiteSampleHistogram z.2)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hNX)
          (by simpa only [histogramTotal_finiteSampleHistogram] using hNY)]
      rw [hfun]
      exact pairedHistogramAverage_productRisk_le P Q est theta hNX hNY
    · exact mul_nonneg measureReal_nonneg measureReal_nonneg
  have hmass_hasSum : HasSum (fun NM : Set.Ici n × Set.Ici n => μ.real (cell NM))
      (μ.real good) := by
    rw [hgood_union]
    simpa [setIntegral_const, smul_eq_mul] using
      (hasSum_integral_iUnion (μ := μ) (f := fun _ => (1 : ℝ))
        hcell_meas hcell_disjoint (integrable_const 1).integrableOn)
  have hgood_le : (∫ c in good, loss c ∂μ) ≤ fixedRisk := by
    have hloss_hasSum : HasSum (fun NM : Set.Ici n × Set.Ici n =>
        ∫ c in cell NM, loss c ∂μ) (∫ c in good, loss c ∂μ) := by
      rw [hgood_union]
      exact hasSum_integral_iUnion hcell_meas hcell_disjoint hloss_int.integrableOn
    rw [← hloss_hasSum.tsum_eq]
    calc
      _ ≤ ∑' NM : Set.Ici n × Set.Ici n, μ.real (cell NM) * fixedRisk :=
        Summable.tsum_le_tsum hcell_le hloss_hasSum.summable
          (hmass_hasSum.summable.mul_right fixedRisk)
      _ = μ.real good * fixedRisk := by
        rw [tsum_mul_right, hmass_hasSum.tsum_eq]
      _ ≤ 1 * fixedRisk := by
        gcongr
        exact (measureReal_mono (subset_univ good)).trans_eq (by simp)
      _ = fixedRisk := one_mul _
  have hbad_integral :
      (∫ c in goodᶜ, loss c ∂μ) = μ.real goodᶜ * fallbackLoss := by
    calc
      _ = ∫ _c in goodᶜ, fallbackLoss ∂μ := by
        apply setIntegral_congr_fun hgood_meas.compl
        intro c hc
        have hfail : histogramTotal c.1 < n ∨ histogramTotal c.2 < n := by
          have hc' : ¬(n ≤ histogramTotal c.1 ∧ n ≤ histogramTotal c.2) := by
            simpa [good, goodX, goodY] using hc
          by_cases hX : n ≤ histogramTotal c.1
          · exact Or.inr (Nat.lt_of_not_ge fun hY => hc' ⟨hX, hY⟩)
          · exact Or.inl (Nat.lt_of_not_ge hX)
        simp [loss, fallbackLoss,
          pairedPoissonHistogramEstimator_of_total_lt est fallback c.1 c.2 hfail]
      _ = μ.real goodᶜ * fallbackLoss := by
        simp [setIntegral_const, smul_eq_mul]
  have hbad_mass : μ.real goodᶜ ≤
      (poissonMeasure lamP).real {k | k < n} +
        (poissonMeasure lamQ).real {k | k < n} := by
    let badX : Set (X → ℕ) := {c | histogramTotal c < n}
    let badY : Set (Y → ℕ) := {c | histogramTotal c < n}
    have hcompl : goodᶜ = (badX ×ˢ Set.univ) ∪ (Set.univ ×ˢ badY) := by
      ext c
      simp only [mem_compl_iff, good, mem_prod, goodX, goodY, mem_setOf_eq,
        mem_union, mem_univ, and_true, true_and, badX, badY]
      constructor
      · intro hc
        by_cases hX : n ≤ histogramTotal c.1
        · exact Or.inr (Nat.lt_of_not_ge fun hY => hc ⟨hX, hY⟩)
        · exact Or.inl (Nat.lt_of_not_ge hX)
      · rintro (hX | hY) hgood
        · exact (Nat.not_lt_of_ge hgood.1) hX
        · exact (Nat.not_lt_of_ge hgood.2) hY
    rw [hcompl]
    refine (measureReal_union_le _ _).trans ?_
    have hPX : μP.real badX = (poissonMeasure lamP).real {k | k < n} := by
      change (countLaw P lamP).real {c | histogramTotal c < n} = _
      change (countLaw P lamP).real (histogramTotal ⁻¹' {k | k < n}) = _
      rw [measureReal_def, measureReal_def, ← countLaw_map_histogramTotal P lamP,
        Measure.map_apply (measurable_of_countable histogramTotal)
          (Set.to_countable {k : ℕ | k < n}).measurableSet]
    have hQY : μQ.real badY = (poissonMeasure lamQ).real {k | k < n} := by
      change (countLaw Q lamQ).real {c | histogramTotal c < n} = _
      change (countLaw Q lamQ).real (histogramTotal ⁻¹' {k | k < n}) = _
      rw [measureReal_def, measureReal_def, ← countLaw_map_histogramTotal Q lamQ,
        Measure.map_apply (measurable_of_countable histogramTotal)
          (Set.to_countable {k : ℕ | k < n}).measurableSet]
    have hleft : μ.real (badX ×ˢ (Set.univ : Set (Y → ℕ))) = μP.real badX := by
      simp [μ, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    have hright : μ.real ((Set.univ : Set (X → ℕ)) ×ˢ badY) = μQ.real badY := by
      simp [μ, measureReal_def, Measure.prod_prod, ENNReal.toReal_mul]
    rw [hleft, hright, hPX, hQY]
  refine ⟨?_, ?_⟩
  · simpa [μ, loss] using hloss_int
  · change (∫ c, loss c ∂μ) ≤ fixedRisk + fallbackLoss *
      ((poissonMeasure lamP).real {k | k < n} +
        (poissonMeasure lamQ).real {k | k < n})
    rw [← integral_add_compl hgood_meas hloss_int]
    calc
      (∫ c in good, loss c ∂μ) + (∫ c in goodᶜ, loss c ∂μ) ≤
          fixedRisk + μ.real goodᶜ * fallbackLoss := add_le_add hgood_le (le_of_eq hbad_integral)
      _ ≤ fixedRisk + fallbackLoss *
          ((poissonMeasure lamP).real {k | k < n} +
            (poissonMeasure lamQ).real {k | k < n}) := by
        apply add_le_add le_rfl
        calc
          μ.real goodᶜ * fallbackLoss = fallbackLoss * μ.real goodᶜ := mul_comm _ _
          _ ≤ fallbackLoss *
              ((poissonMeasure lamP).real {k | k < n} +
                (poissonMeasure lamQ).real {k | k < n}) :=
            mul_le_mul_of_nonneg_left hbad_mass (by
          dsimp [fallbackLoss]
          exact sq_nonneg _)

/-- Given [two finite-alphabet probability laws](hyp:P,Q), [a paired fixed-sample
estimator](hyp:est), [a real target](hyp:theta), [a target-magnitude bound](hyp:B), and
[a certificate of that bound](hyp:htheta), [using zero fallback and Poisson means twice
the sample size gives a risk penalty no larger than twice the squared bound times the
common Poisson lower-tail probability](goal). -/
theorem pairedPoissonHistogramRisk_two_n_le
    {n : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (est : (Fin n → X × Y) → ℝ) (theta B : ℝ) (htheta : |theta| ≤ B) :
    (∫ c, (pairedPoissonHistogramEstimator est 0 c - theta) ^ 2
        ∂((countLaw P (2 * n)).prod (countLaw Q (2 * n)))) ≤
      (∫ z, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
      B ^ 2 * (poissonMeasure (2 * n)).real {k | k < n} * 2 := by
  -- Specialize the central theorem at equal rates and fallback zero, rewrite
  -- the duplicated tail sum, and use `sq_le_sq₀ (abs_nonneg theta) htheta`
  -- (or the equivalent `theta ^ 2 ≤ B ^ 2`) before multiplying by the
  -- nonnegative tail probability.
  have htransfer :=
    (pairedPoissonHistogramRisk_le_fixedRisk_add_tails
      P Q (2 * n) (2 * n) est 0 theta).2
  have hB_nonneg : 0 ≤ B := (abs_nonneg theta).trans htheta
  have htheta_sq : theta ^ 2 ≤ B ^ 2 := by
    rw [← sq_abs theta]
    exact (sq_le_sq₀ (abs_nonneg theta) hB_nonneg).2 htheta
  have htail_nonneg :
      0 ≤ (poissonMeasure (2 * n)).real {k | k < n} := measureReal_nonneg
  calc
    (∫ c,
        (pairedPoissonHistogramEstimator est 0 c - theta) ^ 2
          ∂((countLaw P (2 * n)).prod (countLaw Q (2 * n)))) ≤
        (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
          (0 - theta) ^ 2 *
            ((poissonMeasure (2 * n)).real {k | k < n} +
              (poissonMeasure (2 * n)).real {k | k < n}) := htransfer
    _ = (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
          theta ^ 2 * (poissonMeasure (2 * n)).real {k | k < n} * 2 := by
      ring
    _ ≤ (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
          B ^ 2 * (poissonMeasure (2 * n)).real {k | k < n} * 2 := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right htheta_sq htail_nonneg) (by norm_num)

/-- Given [two finite-alphabet probability laws](hyp:P,Q), [a paired fixed-sample
estimator](hyp:est), [a real target](hyp:theta), [a target-magnitude bound](hyp:B), and
[a certificate of that bound](hyp:htheta), [using zero fallback and Poisson means twice
the sample size gives the explicit exponential risk penalty supplied by the Poisson
lower-tail inequality](goal). -/
theorem pairedPoissonHistogramRisk_two_n_exp_le
    {n : ℕ} {X Y : Type*}
    [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (est : (Fin n → X × Y) → ℝ) (theta B : ℝ) (htheta : |theta| ≤ B) :
    (∫ c, (pairedPoissonHistogramEstimator est 0 c - theta) ^ 2
        ∂((countLaw P (2 * n)).prod (countLaw Q (2 * n)))) ≤
      (∫ z, (est z - theta) ^ 2
        ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
      B ^ 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) * 2 := by
  -- Chain `pairedPoissonHistogramRisk_two_n_le` with
  -- `poisson_two_n_lower_tail`; convert the ENNReal bound to `Measure.real`
  -- using `ENNReal.toReal_mono` and positivity of the exponential term.
  have htailENN := poisson_two_n_lower_tail n
  have htail : (poissonMeasure (2 * n)).real {k | k < n} ≤
      Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
    rw [measureReal_def]
    calc
      ((poissonMeasure (2 * n)) {k | k < n}).toReal ≤
          (ENNReal.ofReal
            (Real.exp (-(n : ℝ) * (1 - Real.log 2)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top htailENN
      _ = Real.exp (-(n : ℝ) * (1 - Real.log 2)) :=
        ENNReal.toReal_ofReal (Real.exp_pos _).le
  calc
    (∫ c,
        (pairedPoissonHistogramEstimator est 0 c - theta) ^ 2
          ∂((countLaw P (2 * n)).prod (countLaw Q (2 * n)))) ≤
        (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
          B ^ 2 * (poissonMeasure (2 * n)).real {k | k < n} * 2 :=
      pairedPoissonHistogramRisk_two_n_le P Q est theta B htheta
    _ ≤ (∫ z, (est z - theta) ^ 2
          ∂Measure.pi (fun _ : Fin n => P.prod Q)) +
          B ^ 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) * 2 := by
      apply add_le_add_right
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htail (sq_nonneg B)) (by norm_num)

end Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram
