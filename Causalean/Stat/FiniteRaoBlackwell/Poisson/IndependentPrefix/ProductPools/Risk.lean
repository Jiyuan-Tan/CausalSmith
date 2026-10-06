/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.Basic
public import Causalean.Stat.Minimax.MarkovKernelTransport

/-!
# Rao--Blackwell risk transfer for finite prefix families

This module averages the capped statistic over all independent Poisson counts,
proves squared-risk contraction, and bounds the overflow contribution by the
sum of the heterogeneous marginal Poisson upper tails.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.GraphMapProd
open Causalean.Stat

universe uI uX

variable {I : Type uI} [Fintype I] [DecidableEq I]
  {X : I → Type uX} [∀ i, MeasurableSpace (X i)]

private theorem measurePreserving_splitPiProd
    {A B : I → Type*} [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
    (μ : (i : I) → Measure (A i)) (ν : (i : I) → Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving
      (fun z : (i : I) → A i × B i ↦
        ((fun i ↦ (z i).1), fun i ↦ (z i).2))
      (Measure.pi fun i ↦ (μ i).prod (ν i))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := by fun_prop
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_
      (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi
        fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
       (Measure.FiniteSpanningSetsIn.pi
        fun i ↦ (ν i).toFiniteSpanningSetsIn)) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi
          fun i ↦ (μ i).toFiniteSpanningSetsIn).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi
          fun i ↦ (ν i).toFiniteSpanningSetsIn).isCountablySpanning
    · rintro _ ⟨s, ⟨s, hs, rfl⟩, ⟨_, ⟨t, ht, rfl⟩, rfl⟩⟩
      have hs' : ∀ i, MeasurableSet (s i) := fun i ↦ hs i (Set.mem_univ i)
      have ht' : ∀ i, MeasurableSet (t i) := fun i ↦ ht i (Set.mem_univ i)
      have hpiS : MeasurableSet (Set.univ.pi s) :=
        MeasurableSet.univ_pi (X := A) hs'
      have hpiT : MeasurableSet (Set.univ.pi t) :=
        MeasurableSet.univ_pi (X := B) ht'
      rw [Measure.map_apply (by fun_prop) (hpiS.prod hpiT)]
      rw [show (fun z : (i : I) → A i × B i ↦
          ((fun i ↦ (z i).1), fun i ↦ (z i).2)) ⁻¹'
            (Set.univ.pi s ×ˢ Set.univ.pi t) =
          Set.univ.pi (fun i ↦ s i ×ˢ t i) by
        ext z
        simp [Set.mem_pi, forall_and]]
      rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi]
      simp_rw [Measure.prod_prod]
      exact Finset.prod_mul_distrib.symm

/-- Given [Poisson intensities](hyp:lambda), [the independent Poisson-count kernel](goal) keeps
every fixed pool and independently attaches one requested length in every coordinate. [It is
given by the product Poisson mechanism](step:1). -/
noncomputable def independentPoissonCountKernel {N : I → ℕ}
    (lambda : I → ℝ≥0) : Kernel (FixedPools X N) (RandomizedPools X N) :=
  mechanismKernel (Measure.pi (fun i ↦ poissonMeasure (lambda i)))
    (fun z i ↦ (z.1 i, z.2 i))

/-- Given [Poisson intensities](hyp:lambda), [the independent Poisson-count kernel is a Markov
kernel](goal). -/
instance independentPoissonCountKernel.isMarkovKernel {N : I → ℕ}
    (lambda : I → ℝ≥0) :
    IsMarkovKernel (independentPoissonCountKernel (X := X) (N := N) lambda) := by
  -- Unfold and invoke the Markov instance for `mechanismKernel`; the
  -- coordinatewise reassociation map is measurable by pi measurability.
  unfold independentPoissonCountKernel
  exact instIsMarkovKernelMechanismKernel _ (by fun_prop)

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), and [pool
capacities](hyp:N), [mixing the count kernel over fixed pools gives the randomized-pool
law](goal). -/
theorem independentPoissonCountKernel_comp_fixedPoolsLaw
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ) :
    independentPoissonCountKernel (X := X) lambda ∘ₘ fixedPoolsLaw P N =
      randomizedPoolsLaw P lambda N := by
  -- Express the composition as a graph pushforward.  A measurable
  -- reassociation sends `(pools, counts)` to `fun i ↦ (pools i, counts i)`;
  -- identify its law with the pi of coordinate products via `Measure.pi_map_pi`.
  let μ : Measure (FixedPools X N) := fixedPoolsLaw P N
  let ν : Measure (I → ℕ) := Measure.pi (fun i ↦ poissonMeasure (lambda i))
  let Φ : FixedPools X N × (I → ℕ) → RandomizedPools X N :=
    fun z i ↦ (z.1 i, z.2 i)
  let Ψ : RandomizedPools X N → FixedPools X N × (I → ℕ) :=
    fun z ↦ ((fun i ↦ (z i).1), fun i ↦ (z i).2)
  letI : IsProbabilityMeasure μ := by
    unfold μ fixedPoolsLaw
    infer_instance
  have hΦ : Measurable Φ := by fun_prop
  have hΨ : Measurable Ψ := by fun_prop
  have hgraph :
      Measure.map (fun p ↦ (p.1, Φ p)) (μ.prod ν) =
        μ.compProd (independentPoissonCountKernel lambda) := by
    simpa [independentPoissonCountKernel, μ, ν, Φ] using
      (map_graph_prod_eq_compProd μ ν hΦ)
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      (show Measurable (fun p ↦ (p.1, Φ p)) from measurable_fst.prodMk hΦ)] at hsnd
  change Measure.map Φ (μ.prod ν) =
    (μ ⊗ₘ independentPoissonCountKernel lambda).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  have hsplit :
      Measure.map Ψ (randomizedPoolsLaw P lambda N) = μ.prod ν := by
    simpa [randomizedPoolsLaw, fixedPoolsLaw, μ, ν, Ψ] using
      (measurePreserving_splitPiProd
        (I := I)
        (μ := fun i ↦ Measure.pi (fun _ : Fin (N i) ↦ P i))
        (ν := fun i ↦ poissonMeasure (lambda i))).map_eq
  have hperm : Measure.map Φ (μ.prod ν) = randomizedPoolsLaw P lambda N := by
    rw [← hsplit, Measure.map_map hΦ hΨ]
    have hcomp : Φ ∘ Ψ = id := by
      funext z i
      rfl
    rw [hcomp, Measure.map_id]
  exact hsnd.symm.trans hperm

/-- Given [Poisson intensities](hyp:lambda), [a prefix statistic](hyp:T), and
[an overflow value](hyp:zOver), [the prefix Rao--Blackwell statistic](goal) averages the
capped statistic over all requested lengths conditional on fixed pools. [It is given by the
count-kernel mean](step:1). -/
noncomputable def prefixRaoBlackwellStatistic {N : I → ℕ}
    (lambda : I → ℝ≥0) (T : PrefixFamily X → ℝ) (zOver : ℝ) :
    FixedPools X N → ℝ :=
  kernelMean (independentPoissonCountKernel lambda)
    (cappedPrefixStatistic T zOver)

/-- Given [Poisson intensities](hyp:lambda), [a measurable prefix statistic](hyp:hT), and [an
overflow value](hyp:zOver), [the prefix Rao--Blackwell statistic is measurable](goal). -/
@[fun_prop]
theorem measurable_prefixRaoBlackwellStatistic {N : I → ℕ}
    (lambda : I → ℝ≥0) {T : PrefixFamily X → ℝ} (hT : Measurable T)
    (zOver : ℝ) :
    Measurable (prefixRaoBlackwellStatistic (N := N) lambda T zOver) := by
  -- Unfold and apply `measurable_kernelMean` to the capped measurability lemma.
  exact measurable_kernelMean _ (measurable_cappedPrefixStatistic hT zOver)

/-- Given [Poisson intensities](hyp:lambda), [a prefix statistic](hyp:T), [evidence that it is
measurable](hyp:hT), [an overflow value](hyp:zOver), and [fixed pools](hyp:pools), [the
Rao--Blackwell statistic equals its explicit count integral](goal). -/
theorem prefixRaoBlackwellStatistic_eq_integral {N : I → ℕ}
    (lambda : I → ℝ≥0) (T : PrefixFamily X → ℝ) (hT : Measurable T)
    (zOver : ℝ) (pools : FixedPools X N) :
    prefixRaoBlackwellStatistic lambda T zOver pools =
      ∫ counts : I → ℕ,
        cappedPrefixStatistic T zOver (fun i ↦ (pools i, counts i))
        ∂(Measure.pi (fun i ↦ poissonMeasure (lambda i))) := by
  -- Follow the two-pool theorem: unfold `kernelMean`, rewrite
  -- `mechanismKernel_apply`, then use `integral_map`.
  unfold prefixRaoBlackwellStatistic kernelMean independentPoissonCountKernel
  rw [mechanismKernel_apply _
    (show Measurable
      (fun z : FixedPools X N × (I → ℕ) ↦ fun i ↦ (z.1 i, z.2 i)) from by
        fun_prop) pools]
  exact integral_map
    (show Measurable
      (fun counts : I → ℕ ↦ fun i ↦ (pools i, counts i)) from by
        fun_prop).aemeasurable
    (measurable_cappedPrefixStatistic hT zOver).aestronglyMeasurable

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [pool
capacities](hyp:N), [a measurable prefix statistic](hyp:hT), [a statistic confined to an
interval](hyp:hTmem), and [an overflow value in that interval](hyp:hzOver), [conditional
averaging cannot increase squared risk relative to the capped randomized experiment](goal), for
any target. -/
theorem sqRisk_prefixRaoBlackwellStatistic_le_capped
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ)
    {T : PrefixFamily X → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ}
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolsLaw P N)
        (prefixRaoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (randomizedPoolsLaw P lambda N)
        (cappedPrefixStatistic T zOver) theta := by
  -- Bound the capped statistic by `max |a| |b|`, apply
  -- `sqRisk_kernelMean_le_comp`, and rewrite the composed law.
  letI : IsProbabilityMeasure (fixedPoolsLaw P N) := by
    unfold fixedPoolsLaw
    infer_instance
  have hCappedBound : UniformlyBounded
      (cappedPrefixStatistic (N := N) T zOver) := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro z
    by_cases h : ∀ i, (z i).2 ≤ N i
    · rw [cappedPrefixStatistic, dif_pos h]
      exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
    · rw [cappedPrefixStatistic, dif_neg h]
      exact abs_le_max_abs_abs hzOver.1 hzOver.2
  calc
    sqRisk (fixedPoolsLaw P N)
        (prefixRaoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (independentPoissonCountKernel (X := X) lambda ∘ₘ
        fixedPoolsLaw P N) (cappedPrefixStatistic T zOver) theta := by
      exact sqRisk_kernelMean_le_comp
        (fixedPoolsLaw P N) (independentPoissonCountKernel lambda)
        (measurable_cappedPrefixStatistic hT zOver) hCappedBound theta
    _ = sqRisk (randomizedPoolsLaw P lambda N)
        (cappedPrefixStatistic T zOver) theta := by
      rw [independentPoissonCountKernel_comp_fixedPoolsLaw]

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [pool
capacities](hyp:N), [a measurable prefix statistic](hyp:hT), [an overflow value](hyp:zOver), and
[a target](hyp:theta), [capped risk on joint nonoverflow equals restricted untruncated-prefix
risk](goal). -/
theorem sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ)
    {T : PrefixFamily X → ℝ} (hT : Measurable T) (zOver theta : ℝ) :
    sqRisk ((randomizedPoolsLaw P lambda N).restrict
        (nonoverflowSet (X := X) N))
        (cappedPrefixStatistic T zOver) theta =
      sqRisk ((independentPoissonPrefixLaw P lambda).restrict
        {s : PrefixFamily X | ∀ i, (s i).count ≤ N i}) T theta := by
  -- Pull the loss back through `totalizedPrefixFamily` using `integral_map`;
  -- on the restricted source use `cappedPrefixStatistic_eq_off_overflow`.
  let overflow : PrefixFamily X := fun _ ↦ ⟨0, Fin.elim0⟩
  unfold sqRisk
  rw [← map_totalizedPrefixFamily_restrict_nonoverflow P lambda N overflow]
  rw [integral_map
    (μ := (randomizedPoolsLaw P lambda N).restrict (nonoverflowSet (X := X) N))
    (φ := totalizedPrefixFamily overflow)
    (f := fun s : PrefixFamily X ↦ (T s - theta) ^ 2)
    (measurable_totalizedPrefixFamily overflow).aemeasurable
    ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (measurableSet_nonoverflowSet N)] with z hz
  rw [nonoverflowSet_eq_compl_overflowSet] at hz
  rw [cappedPrefixStatistic_eq_off_overflow T zOver overflow z hz]

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [pool
capacities](hyp:N), [a measurable prefix statistic](hyp:hT), [a uniform bound](hyp:hTb), and [a
target](hyp:theta), [restricting to coordinatewise nonoverflow cannot increase untruncated
Poissonized squared risk](goal). -/
theorem sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ)
    {T : PrefixFamily X → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (theta : ℝ) :
    sqRisk ((independentPoissonPrefixLaw P lambda).restrict
        {s : PrefixFamily X | ∀ i, (s i).count ≤ N i}) T theta ≤
      sqRisk (independentPoissonPrefixLaw P lambda) T theta := by
  -- Establish bounded-loss integrability, split the full measure into the
  -- measurable good set and its complement, and discard the nonnegative term.
  obtain ⟨M, hM, hTb⟩ := hTb
  let μ : Measure (PrefixFamily X) := independentPoissonPrefixLaw P lambda
  letI : IsProbabilityMeasure μ := by
    unfold μ independentPoissonPrefixLaw
    infer_instance
  let s : Set (PrefixFamily X) := {z | ∀ i, (z i).count ≤ N i}
  have hs : MeasurableSet s := measurableSet_prefixNonoverflowSet N
  have hlossInt : Integrable (fun z ↦ (T z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable (fun z ↦ (T z - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable (fun z ↦ (T z - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  unfold sqRisk
  change (∫ z, (T z - theta) ^ 2 ∂μ.restrict s) ≤
    ∫ z, (T z - theta) ^ 2 ∂μ
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]
  exact le_add_of_nonneg_right (integral_nonneg fun z ↦ sq_nonneg (T z - theta))

private theorem measureReal_iUnion_fintype_le {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (μ : Measure Ω) [IsFiniteMeasure μ] (A : ι → Set Ω) :
    μ.real (⋃ i, A i) ≤ ∑ i, μ.real (A i) := by
  simp only [Measure.real]
  rw [← ENNReal.toReal_sum (s := Finset.univ)
    (fun i _ ↦ measure_ne_top μ (A i))]
  exact ENNReal.toReal_mono (by simp [measure_ne_top])
    (measure_iUnion_fintype_le μ A)

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), and [pool
capacities](hyp:N), [the probability of any overflow is bounded by the sum of marginal Poisson
upper-tail probabilities](goal). -/
theorem overflowSet_measureReal_le_sum_poisson_tails
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ) :
    (randomizedPoolsLaw P lambda N).real (overflowSet (X := X) N) ≤
      ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
  -- Rewrite overflow as `⋃ i, {z | N i < (z i).2}`, apply
  -- `measureReal_iUnion_fintype_le`, and evaluate each pi-coordinate cylinder.
  let μ : Measure (RandomizedPools X N) := randomizedPoolsLaw P lambda N
  letI : IsProbabilityMeasure μ := by
    unfold μ randomizedPoolsLaw
    infer_instance
  let E : I → Set (RandomizedPools X N) :=
    fun i ↦ (fun z ↦ (z i).2) ⁻¹' Set.Ioi (N i)
  have hOverflow : overflowSet (X := X) N = ⋃ i, E i := by
    ext z
    simp [overflowSet, E]
  have hcoord (i : I) :
      μ.real (E i) = (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
    have hset : MeasurableSet {w : (Fin (N i) → X i) × ℕ | N i < w.2} :=
      measurableSet_Ioi.preimage measurable_snd
    have hEval : Measure.map (Function.eval i) μ =
        (Measure.pi (fun _ : Fin (N i) ↦ P i)).prod
          (poissonMeasure (lambda i)) := by
      simpa [μ, randomizedPoolsLaw] using
        (measurePreserving_eval
          (μ := fun i ↦ (Measure.pi (fun _ : Fin (N i) ↦ P i)).prod
            (poissonMeasure (lambda i))) i).map_eq
    calc
      μ.real (E i) =
          (Measure.map (Function.eval i) μ).real
            {w : (Fin (N i) → X i) × ℕ | N i < w.2} := by
        rw [map_measureReal_apply (measurable_pi_apply i) hset]
        rfl
      _ = ((Measure.pi (fun _ : Fin (N i) ↦ P i)).prod
            (poissonMeasure (lambda i))).real
          {w : (Fin (N i) → X i) × ℕ | N i < w.2} := by rw [hEval]
      _ = (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
        rw [show {w : (Fin (N i) → X i) × ℕ | N i < w.2} =
            (Set.univ : Set (Fin (N i) → X i)) ×ˢ Set.Ioi (N i) by
          ext w
          simp]
        simp
  rw [show (randomizedPoolsLaw P lambda N) = μ from rfl, hOverflow]
  exact (measureReal_iUnion_fintype_le μ E).trans_eq
    (Finset.sum_congr rfl fun i _ ↦ hcoord i)

/-- Given [coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [pool
capacities](hyp:N), [a measurable prefix statistic](hyp:hT), [an ordered outcome interval](hyp:hab),
[a statistic confined to that interval](hyp:hTmem), [a target in it](hyp:htheta), and [an
overflow value in it](hyp:hzOver), [fixed-pool Rao--Blackwell risk is bounded by untruncated
Poissonized risk plus squared interval diameter times the summed upper tails](goal). -/
theorem sqRisk_prefixRaoBlackwellStatistic_le
    (P : (i : I) → Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → ℝ≥0) (N : I → ℕ)
    {T : PrefixFamily X → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolsLaw P N)
        (prefixRaoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk (independentPoissonPrefixLaw P lambda) T theta +
        (b - a) ^ 2 *
          ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
  -- Split capped risk over nonoverflow/overflow.  Rewrite the good part with
  -- the restricted-law theorem; the bad statistic is constantly `zOver`, so
  -- its loss is at most `(b-a)^2`, then apply the finite union tail bound.
  have hTb : UniformlyBounded T := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro s
    exact abs_le_max_abs_abs (hTmem s).1 (hTmem s).2
  have hCappedBound : UniformlyBounded
      (cappedPrefixStatistic (N := N) T zOver) := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro z
    by_cases h : ∀ i, (z i).2 ≤ N i
    · rw [cappedPrefixStatistic, dif_pos h]
      exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
    · rw [cappedPrefixStatistic, dif_neg h]
      exact abs_le_max_abs_abs hzOver.1 hzOver.2
  let μ : Measure (RandomizedPools X N) := randomizedPoolsLaw P lambda N
  letI : IsProbabilityMeasure μ := by
    unfold μ randomizedPoolsLaw
    infer_instance
  let s : Set (RandomizedPools X N) := nonoverflowSet (X := X) N
  have hs : MeasurableSet s := measurableSet_nonoverflowSet N
  obtain ⟨M, hM, hCappedBoundM⟩ := hCappedBound
  have hlossInt : Integrable
      (fun z ↦ (cappedPrefixStatistic T zOver z - theta) ^ 2) μ := by
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
  have hsc : sᶜ = overflowSet (X := X) N := by
    simp only [s, nonoverflowSet_eq_compl_overflowSet, compl_compl]
  have hoverflowSq : (zOver - theta) ^ 2 ≤ (b - a) ^ 2 := by
    have hdist : |zOver - theta| ≤ b - a := by
      simpa [Real.dist_eq] using Real.dist_le_of_mem_Icc hzOver htheta
    rw [← sq_abs (zOver - theta)]
    exact (sq_le_sq₀ (abs_nonneg _) (sub_nonneg.mpr hab)).2 hdist
  have hbadEq :
      sqRisk (μ.restrict (overflowSet (X := X) N))
          (cappedPrefixStatistic T zOver) theta =
        (zOver - theta) ^ 2 * μ.real (overflowSet (X := X) N) := by
    unfold sqRisk
    have hae : ∀ᵐ z ∂μ.restrict (overflowSet (X := X) N),
        (cappedPrefixStatistic T zOver z - theta) ^ 2 =
          (zOver - theta) ^ 2 := by
      filter_upwards [ae_restrict_mem (measurableSet_overflowSet N)] with z hz
      obtain ⟨i, hi⟩ := hz
      rw [cappedPrefixStatistic, dif_neg]
      exact fun h ↦ (Nat.not_lt_of_ge (h i)) hi
    rw [integral_congr_ae hae, integral_const]
    simp only [smul_eq_mul, measureReal_def]
    rw [Measure.restrict_apply_univ]
    ring
  have hoverflowMass :
      μ.real (overflowSet (X := X) N) ≤
        ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
    simpa [μ] using overflowSet_measureReal_le_sum_poisson_tails P lambda N
  have hbadLe :
      sqRisk (μ.restrict (overflowSet (X := X) N))
          (cappedPrefixStatistic T zOver) theta ≤
        (b - a) ^ 2 *
          ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
    rw [hbadEq]
    calc
      (zOver - theta) ^ 2 * μ.real (overflowSet (X := X) N) ≤
          (b - a) ^ 2 * μ.real (overflowSet (X := X) N) :=
        mul_le_mul_of_nonneg_right hoverflowSq (by positivity)
      _ ≤ (b - a) ^ 2 *
          ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) :=
        mul_le_mul_of_nonneg_left hoverflowMass (sq_nonneg _)
  calc
    sqRisk (fixedPoolsLaw P N)
        (prefixRaoBlackwellStatistic lambda T zOver) theta ≤
      sqRisk μ (cappedPrefixStatistic T zOver) theta := by
        exact sqRisk_prefixRaoBlackwellStatistic_le_capped
          P lambda N hT hTmem hzOver
    _ = sqRisk (μ.restrict s) (cappedPrefixStatistic T zOver) theta +
          sqRisk (μ.restrict sᶜ) (cappedPrefixStatistic T zOver) theta := hsplit
    _ = sqRisk ((independentPoissonPrefixLaw P lambda).restrict
          {z : PrefixFamily X | ∀ i, (z i).count ≤ N i}) T theta +
          sqRisk (μ.restrict (overflowSet (X := X) N))
            (cappedPrefixStatistic T zOver) theta := by
      rw [show μ.restrict s =
          (randomizedPoolsLaw P lambda N).restrict (nonoverflowSet (X := X) N) from rfl,
        sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq
          P lambda N hT zOver theta, hsc]
    _ ≤ sqRisk (independentPoissonPrefixLaw P lambda) T theta +
        (b - a) ^ 2 *
          ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) :=
      add_le_add
        (sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le
          P lambda N hT hTb theta)
        hbadLe

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
