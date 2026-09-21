/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.Basic
import Causalean.Stat.Minimax.MarkovKernelTransport

/-!
# Rao--Blackwell risk transfer for independent unequal prefixes

This module randomizes two independent fixed iid pools by two independent
Poisson counts, averages a bounded capped-prefix statistic over those counts,
and proves the conditional Jensen contraction and the resulting
depoissonization risk bound.  Neither the alphabets nor the pool capacities
need agree.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.GraphMapProd
open Causalean.Stat

universe uX uY

variable {X : Type uX} {Y : Type uY}
  [MeasurableSpace X] [MeasurableSpace Y]

/-- Given [the first Poisson intensity](hyp:lambdaX) and [the second Poisson
intensity](hyp:lambdaY), [the independent Poisson-count kernel](goal) keeps both fixed pools
and independently attaches one requested length to each. [It is given by the product Poisson
mechanism with the output rearranged into pool-count pairs](step:1). -/
noncomputable def independentPoissonCountKernel {NX NY : ℕ}
    (lambdaX lambdaY : ℝ≥0) :
    Kernel (FixedPools (X := X) (Y := Y) NX NY)
      (RandomizedPools (X := X) (Y := Y) NX NY) :=
  mechanismKernel ((poissonMeasure lambdaX).prod (poissonMeasure lambdaY))
    (fun z ↦ ((z.1.1, z.2.1), (z.1.2, z.2.2)))

/-- Given [the first Poisson intensity](hyp:lambdaX) and [the second Poisson
intensity](hyp:lambdaY), [the independent Poisson-count kernel is a Markov kernel](goal). -/
instance independentPoissonCountKernel.isMarkovKernel {NX NY : ℕ}
    (lambdaX lambdaY : ℝ≥0) :
    IsMarkovKernel
      (independentPoissonCountKernel (X := X) (Y := Y) (NX := NX) (NY := NY)
        lambdaX lambdaY) := by
  unfold independentPoissonCountKernel
  exact instIsMarkovKernelMechanismKernel _ (by fun_prop)

/-- Given [probability laws for the first and second pools](hyp:P,Q), [the first and second
Poisson intensities](hyp:lambdaX,lambdaY), and [the first and second pool capacities](hyp:NX,NY),
[mixing the independent count kernel over the fixed pools gives exactly the randomized-pool
law](goal). -/
theorem independentPoissonCountKernel_comp_fixedPoolsLaw
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ) :
    independentPoissonCountKernel (X := X) (Y := Y) lambdaX lambdaY ∘ₘ
        fixedPoolsLaw P Q NX NY =
      randomizedPoolsLaw P Q lambdaX lambdaY NX NY := by
  -- Follow `auxPoissonCountKernel_comp_pi`: express the composition product
  -- as the graph push-forward of the fixed-pool/count product, then map by
  -- the measurable reassociation permutation.  Product associativity and
  -- `Measure.map_prod_map` identify the result with `randomizedPoolsLaw`.
  let μX : Measure (Fin NX → X) := Measure.pi (fun _ : Fin NX ↦ P)
  let μY : Measure (Fin NY → Y) := Measure.pi (fun _ : Fin NY ↦ Q)
  let νX : Measure ℕ := poissonMeasure lambdaX
  let νY : Measure ℕ := poissonMeasure lambdaY
  letI : IsProbabilityMeasure (fixedPoolsLaw P Q NX NY) := by
    unfold fixedPoolsLaw
    infer_instance
  let Φ : ((Fin NX → X) × (Fin NY → Y)) × (ℕ × ℕ) →
      ((Fin NX → X) × ℕ) × ((Fin NY → Y) × ℕ) :=
    fun z => ((z.1.1, z.2.1), (z.1.2, z.2.2))
  have hΦ : Measurable Φ := by fun_prop
  have hgraph :
      Measure.map (fun p => (p.1, Φ p))
          ((fixedPoolsLaw P Q NX NY).prod (νX.prod νY)) =
        (fixedPoolsLaw P Q NX NY).compProd
          (independentPoissonCountKernel lambdaX lambdaY) := by
    simpa [independentPoissonCountKernel, Φ, νX, νY] using
      (map_graph_prod_eq_compProd
        (fixedPoolsLaw P Q NX NY) (νX.prod νY) hΦ)
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      (show Measurable (fun p => (p.1, Φ p)) from measurable_fst.prodMk hΦ)] at hsnd
  change Measure.map Φ ((fixedPoolsLaw P Q NX NY).prod (νX.prod νY)) =
    ((fixedPoolsLaw P Q NX NY) ⊗ₘ
      independentPoissonCountKernel lambdaX lambdaY).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  have hperm :
      Measure.map Φ ((μX.prod μY).prod (νX.prod νY)) =
        (μX.prod νX).prod (μY.prod νY) := by
    have hInner : MeasurePreserving
        (fun p : (Fin NY → Y) × (ℕ × ℕ) => (p.2.1, (p.1, p.2.2)))
        (μY.prod (νX.prod νY)) (νX.prod (μY.prod νY)) := by
      have h₁ := (measurePreserving_prodAssoc μY νX νY).symm
        (MeasurableEquiv.prodAssoc :
          (((Fin NY → Y) × ℕ) × ℕ) ≃ᵐ ((Fin NY → Y) × (ℕ × ℕ)))
      have h₂ := (Measure.measurePreserving_swap (μ := μY) (ν := νX)).prod
        (MeasurePreserving.id νY)
      have h₃ := measurePreserving_prodAssoc νX μY νY
      simpa [Function.comp_def, MeasurableEquiv.prodAssoc,
        MeasurableEquiv.prodComm] using h₃.comp (h₂.comp h₁)
    have hOuter := (MeasurePreserving.id μX).prod hInner
    have hFinal := (measurePreserving_prodAssoc μX νX (μY.prod νY)).symm
      (MeasurableEquiv.prodAssoc :
        (((Fin NX → X) × ℕ) × ((Fin NY → Y) × ℕ)) ≃ᵐ
          ((Fin NX → X) × (ℕ × ((Fin NY → Y) × ℕ))))
    have hAll := hFinal.comp
      (hOuter.comp (measurePreserving_prodAssoc μX μY (νX.prod νY)))
    simpa [Φ, Function.comp_def, MeasurableEquiv.prodAssoc,
      MeasurableEquiv.prodComm] using hAll.map_eq
  simpa [fixedPoolsLaw, randomizedPoolsLaw, μX, μY, νX, νY] using
    hsnd.symm.trans hperm

/-- Given [the first Poisson intensity](hyp:lambdaX), [the second Poisson intensity](hyp:lambdaY),
[a two-prefix statistic](hyp:T), and [a fallback value](hyp:zOver), [the independent-prefix
Rao--Blackwell statistic](goal) averages the capped statistic over the two auxiliary Poisson
counts conditional on the fixed pools. [It is given by the kernel mean](step:1). -/
noncomputable def independentPrefixRaoBlackwellStatistic {NX NY : ℕ}
    (lambdaX lambdaY : ℝ≥0)
    (T : (FiniteSample X × FiniteSample Y) → ℝ) (zOver : ℝ) :
    FixedPools (X := X) (Y := Y) NX NY → ℝ :=
  kernelMean (independentPoissonCountKernel lambdaX lambdaY)
    (cappedPrefixStatistic T zOver)

/-- Given [the first and second Poisson intensities](hyp:lambdaX,lambdaY), [a measurable
two-prefix statistic](hyp:hT), and [a fallback value](hyp:zOver), [the independent-prefix
Rao--Blackwell statistic is measurable](goal). -/
@[fun_prop]
theorem measurable_independentPrefixRaoBlackwellStatistic {NX NY : ℕ}
    (lambdaX lambdaY : ℝ≥0)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    (zOver : ℝ) :
    Measurable
      (independentPrefixRaoBlackwellStatistic (NX := NX) (NY := NY)
        lambdaX lambdaY T zOver) := by
  exact measurable_kernelMean _ (measurable_cappedPrefixStatistic hT zOver)

/-- Given [the first and second Poisson intensities](hyp:lambdaX,lambdaY), [a two-prefix
statistic](hyp:T), [a certificate that it is measurable](hyp:hT), [a fallback value](hyp:zOver),
and [fixed pools](hyp:pools), [the Rao--Blackwell statistic equals the integral of the capped
statistic over the independent Poisson counts](goal). -/
theorem independentPrefixRaoBlackwellStatistic_eq_integral {NX NY : ℕ}
    (lambdaX lambdaY : ℝ≥0)
    (T : (FiniteSample X × FiniteSample Y) → ℝ) (hT : Measurable T)
    (zOver : ℝ) (pools : FixedPools (X := X) (Y := Y) NX NY) :
    independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver pools =
      ∫ counts : ℕ × ℕ,
        cappedPrefixStatistic T zOver
          ((pools.1, counts.1), (pools.2, counts.2))
        ∂((poissonMeasure lambdaX).prod (poissonMeasure lambdaY)) := by
  -- Unfold `kernelMean` and the mechanism kernel, rewrite its pointwise value
  -- with `mechanismKernel_apply`, then apply `integral_map`; measurability of
  -- the integrand is `measurable_cappedPrefixStatistic hT zOver`.
  unfold independentPrefixRaoBlackwellStatistic kernelMean
    independentPoissonCountKernel
  rw [mechanismKernel_apply _
    (show Measurable
      (fun z : FixedPools (X := X) (Y := Y) NX NY × (ℕ × ℕ) =>
        ((z.1.1, z.2.1), (z.1.2, z.2.2))) from by fun_prop) pools]
  exact integral_map
    (show Measurable
      (fun counts : ℕ × ℕ =>
        ((pools.1, counts.1), (pools.2, counts.2))) from by fun_prop).aemeasurable
    (measurable_cappedPrefixStatistic hT zOver).aestronglyMeasurable

/-- Given [probability laws for the first and second observations](hyp:P,Q), [the first and
second Poisson intensities](hyp:lambdaX,lambdaY), [the first and second pool capacities](hyp:NX,NY),
[a measurable two-prefix statistic](hyp:hT), [an ordered outcome interval](hyp:hab), [a
certificate that the statistic stays in that interval](hyp:hTmem), [a target in the interval](hyp:htheta),
and [a fallback in the interval](hyp:hzOver), [conditional averaging cannot increase squared
risk](goal). -/
theorem sqRisk_independentPrefixRaoBlackwellStatistic_le_capped
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolsLaw P Q NX NY)
        (independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver) theta ≤
      sqRisk (randomizedPoolsLaw P Q lambdaX lambdaY NX NY)
        (cappedPrefixStatistic T zOver) theta := by
  -- The interval assumptions uniformly bound the capped statistic by
  -- `max |a| |b|`.  Apply `sqRisk_kernelMean_le_comp` to the auxiliary
  -- Markov kernel and rewrite the composed measure using
  -- `independentPoissonCountKernel_comp_fixedPoolsLaw`.
  letI : IsProbabilityMeasure (fixedPoolsLaw P Q NX NY) := by
    unfold fixedPoolsLaw
    infer_instance
  have hCappedBound : UniformlyBounded
      (cappedPrefixStatistic (NX := NX) (NY := NY) T zOver) := by
    refine ⟨max |a| |b|, ?_, ?_⟩
    · exact (abs_nonneg a).trans (le_max_left _ _)
    · intro z
      by_cases hX : z.1.2 ≤ NX
      · by_cases hY : z.2.2 ≤ NY
        · simp only [cappedPrefixStatistic, hX, hY, dite_true]
          exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
        · simp only [cappedPrefixStatistic, hX, hY, dite_true, dite_false]
          exact abs_le_max_abs_abs hzOver.1 hzOver.2
      · simp only [cappedPrefixStatistic, hX, dite_false]
        exact abs_le_max_abs_abs hzOver.1 hzOver.2
  calc
    sqRisk (fixedPoolsLaw P Q NX NY)
        (independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver) theta ≤
      sqRisk
        (independentPoissonCountKernel (X := X) (Y := Y) lambdaX lambdaY ∘ₘ
          fixedPoolsLaw P Q NX NY)
        (cappedPrefixStatistic T zOver) theta := by
      exact sqRisk_kernelMean_le_comp
        (fixedPoolsLaw P Q NX NY)
        (independentPoissonCountKernel lambdaX lambdaY)
        (measurable_cappedPrefixStatistic hT zOver) hCappedBound theta
    _ = sqRisk (randomizedPoolsLaw P Q lambdaX lambdaY NX NY)
        (cappedPrefixStatistic T zOver) theta := by
      rw [independentPoissonCountKernel_comp_fixedPoolsLaw]

/-- Given [probability laws for the first and second pools](hyp:P,Q), [the first and second
Poisson intensities](hyp:lambdaX,lambdaY), [the first and second pool capacities](hyp:NX,NY),
[a measurable two-prefix statistic](hyp:hT), [a fallback value](hyp:zOver), and [a target](hyp:theta),
[the capped risk on the joint nonoverflow event equals the restricted untruncated-prefix
risk](goal). -/
theorem sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    (zOver theta : ℝ) :
    sqRisk
        ((randomizedPoolsLaw P Q lambdaX lambdaY NX NY).restrict
          (nonoverflowSet (X := X) (Y := Y) NX NY))
        (cappedPrefixStatistic T zOver) theta =
      sqRisk
        ((independentPoissonPrefixLaw P Q lambdaX lambdaY).restrict
          ((FiniteSample.count ⁻¹' Set.Iic NX) ×ˢ
            (FiniteSample.count ⁻¹' Set.Iic NY))) T theta := by
  -- Pull squared loss back along `totalizedPrefixPair` using `integral_map`
  -- and `map_totalizedPrefixPair_restrict_nonoverflow`.  On the restricted
  -- source, `cappedPrefixStatistic_eq_off_overflow` gives pointwise equality;
  -- use `ae_restrict_mem`, `nonoverflowSet_eq_compl_overflowSet`, and
  -- `cappedPrefixStatistic_eq_off_overflow` to discharge membership.  This is
  -- the product analogue of
  -- `Causalean.Stat.sqRisk_cappedStatistic_restrict_nonoverflow_eq`.
  let overflowX : FiniteSample X := ⟨0, fun i => Fin.elim0 i⟩
  let overflowY : FiniteSample Y := ⟨0, fun i => Fin.elim0 i⟩
  unfold sqRisk
  rw [← map_totalizedPrefixPair_restrict_nonoverflow
    P Q lambdaX lambdaY NX NY overflowX overflowY]
  rw [integral_map
    (μ := (randomizedPoolsLaw P Q lambdaX lambdaY NX NY).restrict
      (nonoverflowSet (X := X) (Y := Y) NX NY))
    (φ := totalizedPrefixPair overflowX overflowY)
    (f := fun s : FiniteSample X × FiniteSample Y ↦ (T s - theta) ^ 2)
    (measurable_totalizedPrefixPair overflowX overflowY).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_nonoverflowSet NX NY)] with z hz
  rw [nonoverflowSet_eq_compl_overflowSet] at hz
  rw [cappedPrefixStatistic_eq_off_overflow T zOver overflowX overflowY z hz]

/-- Given [probability laws for the first and second prefixes](hyp:P,Q), [the first and
second Poisson intensities](hyp:lambdaX,lambdaY), [the first and second capacities](hyp:NX,NY),
[a measurable two-prefix statistic](hyp:hT), [a uniform bound for that statistic](hyp:hTb),
and [a target](hyp:theta), [restricting to jointly nonoverflowing prefix lengths cannot
increase squared risk](goal). -/
theorem sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (theta : ℝ) :
    sqRisk
        ((independentPoissonPrefixLaw P Q lambdaX lambdaY).restrict
          ((FiniteSample.count ⁻¹' Set.Iic NX) ×ˢ
            (FiniteSample.count ⁻¹' Set.Iic NY))) T theta ≤
      sqRisk (independentPoissonPrefixLaw P Q lambdaX lambdaY) T theta := by
  -- Uniform boundedness makes squared loss integrable.  Split the full
  -- integral into the measurable joint-good restriction and its complement
  -- via `Measure.restrict_add_restrict_compl`, then discard the nonnegative
  -- complementary squared-loss integral.  Equivalently,
  -- `MeasureTheory.setIntegral_le_integral` applies once integrability and
  -- nonnegativity are established; the one-pool template is
  -- `Causalean.Stat.sqRisk_finitePoisson_restrict_nonoverflow_le`.
  obtain ⟨M, hM, hTb⟩ := hTb
  let μ : Measure (FiniteSample X × FiniteSample Y) :=
    independentPoissonPrefixLaw P Q lambdaX lambdaY
  letI : IsProbabilityMeasure μ := by
    unfold μ independentPoissonPrefixLaw
    infer_instance
  let s : Set (FiniteSample X × FiniteSample Y) :=
    (FiniteSample.count ⁻¹' Set.Iic NX) ×ˢ
      (FiniteSample.count ⁻¹' Set.Iic NY)
  have hs : MeasurableSet s := by
    exact (measurable_finiteSample_count measurableSet_Iic).prod
      (measurable_finiteSample_count measurableSet_Iic)
  have hlossInt : Integrable (fun z => (T z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  unfold sqRisk
  change (∫ z, (T z - theta) ^ 2 ∂μ.restrict s) ≤
    ∫ z, (T z - theta) ^ 2 ∂μ
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]
  exact le_add_of_nonneg_right
    (integral_nonneg fun z => sq_nonneg (T z - theta))

/-- Given [probability laws for the first and second observations](hyp:P,Q), [the first and
second Poisson intensities](hyp:lambdaX,lambdaY), [the first and second pool capacities](hyp:NX,NY),
[a measurable two-prefix statistic](hyp:hT), [an ordered outcome interval](hyp:hab), [a
certificate that the statistic stays in that interval](hyp:hTmem), [a target in the interval](hyp:htheta),
and [a fallback in the interval](hyp:hzOver), [the fixed-pool Rao--Blackwell risk is bounded by
the untruncated Poisson-prefix risk plus the squared interval diameter times the two upper
tails](goal). -/
theorem sqRisk_independentPrefixRaoBlackwellStatistic_le
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolsLaw P Q NX NY)
        (independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver) theta ≤
      sqRisk (independentPoissonPrefixLaw P Q lambdaX lambdaY) T theta +
        (b - a) ^ 2 *
          ((poissonMeasure lambdaX).real (Set.Ioi NX) +
            (poissonMeasure lambdaY).real (Set.Ioi NY)) := by
  -- Start with the conditional contraction and split randomized risk over
  -- `nonoverflowSet` and its complement.  Rewrite the good contribution with
  -- the restricted-risk equality and bound it by untruncated risk.  The bad
  -- contribution is the constant fallback loss; bound that loss by the
  -- squared interval diameter and its event probability by the union bound.
  -- `measureReal_union_le` supplies the union bound.  Product-event masses
  -- reduce to the stated Poisson tails using `Measure.prod_apply` and the
  -- probability-one masses of the iid-pool and opposite-arm laws.  Follow the
  -- decomposition in `Causalean.Stat.sqRisk_raoBlackwellStatistic_le`, with
  -- `overflowSet` replacing the one count event.
  have hTb : UniformlyBounded T := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro s
    exact abs_le_max_abs_abs (hTmem s).1 (hTmem s).2
  have hCappedBound : UniformlyBounded
      (cappedPrefixStatistic (NX := NX) (NY := NY) T zOver) := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro z
    by_cases hX : z.1.2 ≤ NX
    · by_cases hY : z.2.2 ≤ NY
      · simp only [cappedPrefixStatistic, hX, hY, dite_true]
        exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
      · simp only [cappedPrefixStatistic, hX, hY, dite_true, dite_false]
        exact abs_le_max_abs_abs hzOver.1 hzOver.2
    · simp only [cappedPrefixStatistic, hX, dite_false]
      exact abs_le_max_abs_abs hzOver.1 hzOver.2
  let μ : Measure (RandomizedPools (X := X) (Y := Y) NX NY) :=
    randomizedPoolsLaw P Q lambdaX lambdaY NX NY
  letI : IsProbabilityMeasure μ := by
    unfold μ randomizedPoolsLaw
    infer_instance
  let s : Set (RandomizedPools (X := X) (Y := Y) NX NY) :=
    nonoverflowSet (X := X) (Y := Y) NX NY
  have hs : MeasurableSet s := measurableSet_nonoverflowSet NX NY
  obtain ⟨M, hM, hCappedBoundM⟩ := hCappedBound
  have hlossInt : Integrable
      (fun z => (cappedPrefixStatistic T zOver z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      (((measurable_cappedPrefixStatistic hT zOver).sub measurable_const).pow_const 2
        ).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hCappedBoundM z) le_rfl)
  have hsplit :
      sqRisk μ (cappedPrefixStatistic T zOver) theta =
        sqRisk (μ.restrict s) (cappedPrefixStatistic T zOver) theta +
          sqRisk (μ.restrict sᶜ) (cappedPrefixStatistic T zOver) theta := by
    unfold sqRisk
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
      integral_add_measure hlossInt.restrict hlossInt.restrict]
  have hsc : sᶜ = overflowSet (X := X) (Y := Y) NX NY := by
    simp only [s, nonoverflowSet_eq_compl_overflowSet, compl_compl]
  have hoverflowSq : (zOver - theta) ^ 2 ≤ (b - a) ^ 2 := by
    have hdist : |zOver - theta| ≤ b - a := by
      simpa [Real.dist_eq] using Real.dist_le_of_mem_Icc hzOver htheta
    rw [← sq_abs (zOver - theta)]
    exact (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hab)).2 hdist
  have hbadEq :
      sqRisk (μ.restrict (overflowSet (X := X) (Y := Y) NX NY))
          (cappedPrefixStatistic T zOver) theta =
        (zOver - theta) ^ 2 *
          μ.real (overflowSet (X := X) (Y := Y) NX NY) := by
    unfold sqRisk
    have hae : ∀ᵐ z ∂μ.restrict (overflowSet (X := X) (Y := Y) NX NY),
        (cappedPrefixStatistic T zOver z - theta) ^ 2 =
          (zOver - theta) ^ 2 := by
      filter_upwards [ae_restrict_mem (measurableSet_overflowSet NX NY)] with z hz
      change NX < z.1.2 ∨ NY < z.2.2 at hz
      rcases hz with hx | hy
      · simp [cappedPrefixStatistic, not_le_of_gt hx]
      · by_cases hx : z.1.2 ≤ NX
        · simp [cappedPrefixStatistic, hx, not_le_of_gt hy]
        · simp [cappedPrefixStatistic, hx]
    rw [integral_congr_ae hae, integral_const]
    simp only [smul_eq_mul, measureReal_def]
    rw [Measure.restrict_apply_univ]
    ring
  have hoverflowMass :
      μ.real (overflowSet (X := X) (Y := Y) NX NY) ≤
        (poissonMeasure lambdaX).real (Set.Ioi NX) +
          (poissonMeasure lambdaY).real (Set.Ioi NY) := by
    let eX : Set (RandomizedPools (X := X) (Y := Y) NX NY) :=
      {z | NX < z.1.2}
    let eY : Set (RandomizedPools (X := X) (Y := Y) NX NY) :=
      {z | NY < z.2.2}
    have hOverflow :
        overflowSet (X := X) (Y := Y) NX NY = eX ∪ eY := by
      rfl
    have heXeq :
        μ.real eX = (poissonMeasure lambdaX).real (Set.Ioi NX) := by
      have hset : eX =
          ((Set.univ : Set (Fin NX → X)) ×ˢ Set.Ioi NX) ×ˢ
            (Set.univ : Set ((Fin NY → Y) × ℕ)) := by
        ext z
        simp [eX]
      simp [hset, μ, randomizedPoolsLaw]
    have heYeq :
        μ.real eY = (poissonMeasure lambdaY).real (Set.Ioi NY) := by
      have hset : eY =
          (Set.univ : Set ((Fin NX → X) × ℕ)) ×ˢ
            ((Set.univ : Set (Fin NY → Y)) ×ˢ Set.Ioi NY) := by
        ext z
        simp [eY]
      simp [hset, μ, randomizedPoolsLaw]
    rw [hOverflow]
    exact (measureReal_union_le eX eY).trans_eq
      (congrArg₂ (· + ·) heXeq heYeq)
  have hbadLe :
      sqRisk (μ.restrict (overflowSet (X := X) (Y := Y) NX NY))
          (cappedPrefixStatistic T zOver) theta ≤
        (b - a) ^ 2 *
          ((poissonMeasure lambdaX).real (Set.Ioi NX) +
            (poissonMeasure lambdaY).real (Set.Ioi NY)) := by
    rw [hbadEq]
    calc
      (zOver - theta) ^ 2 *
          μ.real (overflowSet (X := X) (Y := Y) NX NY) ≤
          (b - a) ^ 2 *
            μ.real (overflowSet (X := X) (Y := Y) NX NY) :=
        mul_le_mul_of_nonneg_right hoverflowSq (by positivity)
      _ ≤ (b - a) ^ 2 *
          ((poissonMeasure lambdaX).real (Set.Ioi NX) +
            (poissonMeasure lambdaY).real (Set.Ioi NY)) :=
        mul_le_mul_of_nonneg_left hoverflowMass (sq_nonneg _)
  calc
    sqRisk (fixedPoolsLaw P Q NX NY)
        (independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver) theta ≤
      sqRisk μ (cappedPrefixStatistic T zOver) theta := by
        exact sqRisk_independentPrefixRaoBlackwellStatistic_le_capped
          P Q lambdaX lambdaY NX NY hT hab hTmem htheta hzOver
    _ = sqRisk (μ.restrict s) (cappedPrefixStatistic T zOver) theta +
          sqRisk (μ.restrict sᶜ) (cappedPrefixStatistic T zOver) theta := hsplit
    _ = sqRisk
          ((independentPoissonPrefixLaw P Q lambdaX lambdaY).restrict
            ((FiniteSample.count ⁻¹' Set.Iic NX) ×ˢ
              (FiniteSample.count ⁻¹' Set.Iic NY))) T theta +
          sqRisk (μ.restrict (overflowSet (X := X) (Y := Y) NX NY))
            (cappedPrefixStatistic T zOver) theta := by
      rw [show μ.restrict s =
          (randomizedPoolsLaw P Q lambdaX lambdaY NX NY).restrict
            (nonoverflowSet (X := X) (Y := Y) NX NY) from rfl,
        sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq
          P Q lambdaX lambdaY NX NY hT zOver theta, hsc]
    _ ≤ sqRisk (independentPoissonPrefixLaw P Q lambdaX lambdaY) T theta +
        (b - a) ^ 2 *
          ((poissonMeasure lambdaX).real (Set.Ioi NX) +
            (poissonMeasure lambdaY).real (Set.Ioi NY)) :=
      add_le_add
        (sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le
          P Q lambdaX lambdaY NX NY hT hTb theta)
        hbadLe

/-! ## Finite-alphabet specialization -/

/-- Given finite measurable alphabets, [probability laws for the two observations](hyp:P,Q),
[the first and second Poisson intensities](hyp:lambdaX,lambdaY), [the first and second pool
capacities](hyp:NX,NY), [a measurable two-prefix statistic](hyp:hT), [an ordered outcome
interval](hyp:hab), [a certificate that the statistic stays in it](hyp:hTmem),
[a target in it](hyp:htheta),
and [a fallback in it](hyp:hzOver), [the unequal-prefix risk transfer bound holds without
coordinatewise pairing](goal). -/
theorem finiteAlphabet_independentUnequalPrefix_risk_le
    [Fintype X] [MeasurableSingletonClass X] [DecidableEq X]
    [Fintype Y] [MeasurableSingletonClass Y] [DecidableEq Y]
    (P : Measure X) [IsProbabilityMeasure P]
    (Q : Measure Y) [IsProbabilityMeasure Q]
    (lambdaX lambdaY : ℝ≥0) (NX NY : ℕ)
    {T : (FiniteSample X × FiniteSample Y) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolsLaw P Q NX NY)
        (independentPrefixRaoBlackwellStatistic lambdaX lambdaY T zOver) theta ≤
      sqRisk (independentPoissonPrefixLaw P Q lambdaX lambdaY) T theta +
        (b - a) ^ 2 *
          ((poissonMeasure lambdaX).real (Set.Ioi NX) +
            (poissonMeasure lambdaY).real (Set.Ioi NY)) := by
  exact sqRisk_independentPrefixRaoBlackwellStatistic_le
    P Q lambdaX lambdaY NX NY hT hab hTmem htheta hzOver

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix
