/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Topology.Compactness.Compact

/-!
# Finite atomic one-dimensional Wasserstein: basic objects

This module defines finite atomic probability laws with arbitrary finite slot types, their finite
transport polytope, cumulative distribution functions, and the canonical CDF-sign potential.
The companion transport and duality modules establish the CDF cost formula and exact
Kantorovich--Rubinstein duality. The API is extensional in the represented measure, so
permutations, zero slots, and atom splitting or merging do not affect the distance.
-/

namespace Causalean.Stat.Coupling

open MeasureTheory Set
open scoped BigOperators ENNReal Interval

/-- A labelled finite atomic real law, prior to imposing nonnegativity and unit total mass. -/
structure AtomicLaw (ι : Type*) where
  weight : ι → ℝ
  atom : ι → ℝ

namespace AtomicLaw

/-- Nonnegative weights with total mass one make a finite atomic representation a probability law. -/
def Valid {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) : Prop :=
  (∀ i, 0 ≤ μ.weight i) ∧ ∑ i, μ.weight i = 1

/-- The probability measure represented by a valid finite list of weighted atoms. -/
noncomputable def toMeasure {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (μ.weight i) • Measure.dirac (μ.atom i)

/-- The finite weighted expectation of a scalar test function. -/
def integral {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) (f : ℝ → ℝ) : ℝ :=
  ∑ i, μ.weight i * f (μ.atom i)

/-- For a valid law, finite weighted expectation agrees with integration against its represented
atomic probability measure. -/
theorem integral_eq_measureIntegral {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) (f : ℝ → ℝ) (hf : Continuous f) :
    μ.integral f = ∫ x, f x ∂μ.toMeasure := by
  classical
  rw [toMeasure, integral_finsetSum_measure]
  · simp [integral, integral_smul_measure, integral_dirac,
      ENNReal.toReal_ofReal (hμ.1 _)]
  · intro i hi
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- A valid finite atomic representation defines a probability measure. -/
theorem toMeasure_isProbability {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) : IsProbabilityMeasure μ.toMeasure := by
  constructor
  simp [toMeasure]
  convert congrArg ENNReal.ofReal hμ.2 using 1 <;>
    simp [ENNReal.ofReal_sum_of_nonneg, hμ.1]

/-- A finite transport plan has nonnegative entries and the prescribed two marginals. -/
structure TransportPlan {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) where
  mass : ι → κ → ℝ
  nonneg : ∀ i j, 0 ≤ mass i j
  fst_marginal : ∀ i, ∑ j, mass i j = μ.weight i
  snd_marginal : ∀ j, ∑ i, mass i j = ν.weight j

/-- The absolute-distance cost of a finite transport plan. -/
def transportCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : ℝ :=
  ∑ i, ∑ j, π.mass i j * |μ.atom i - ν.atom j|

/-- Finite-atomic one-Wasserstein distance as the infimum over the transport polytope. -/
noncomputable def w1 {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : ℝ :=
  sInf {c : ℝ | ∃ π : TransportPlan μ ν, transportCost π = c}

/-- Every feasible finite transport plan upper-bounds finite-atomic one-Wasserstein distance. -/
theorem w1_le_transportCost {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) :
    w1 μ ν ≤ transportCost π := by
  unfold w1
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  · exact ⟨π, rfl⟩

/-- The finite transport polytope attains the one-Wasserstein infimum for two valid laws. -/
theorem exists_optimalTransportPlan {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid) :
    ∃ π : TransportPlan μ ν, transportCost π = w1 μ ν := by
  classical
  let S : Set (ι → κ → ℝ) := {m |
    (∀ i j, 0 ≤ m i j) ∧
    (∀ i, ∑ j, m i j = μ.weight i) ∧
    ∀ j, ∑ i, m i j = ν.weight j}
  have hSne : S.Nonempty := by
    refine ⟨fun i j => μ.weight i * ν.weight j, ?_⟩
    refine ⟨fun i j => mul_nonneg (hμ.1 i) (hν.1 j), ?_, ?_⟩
    · intro i
      rw [← Finset.mul_sum, hν.2, mul_one]
    · intro j
      rw [← Finset.sum_mul, hμ.2, one_mul]
  have hweight_le_one (i : ι) : μ.weight i ≤ 1 := by
    rw [← hμ.2]
    exact Finset.single_le_sum (fun j _ => hμ.1 j) (Finset.mem_univ i)
  have hSsub : S ⊆ Set.Icc (fun _ _ => 0) (fun _ _ => 1) := by
    intro m hm
    refine ⟨fun i j => hm.1 i j, fun i j => ?_⟩
    calc
      m i j ≤ ∑ r, m i r :=
        Finset.single_le_sum (fun r _ => hm.1 i r) (Finset.mem_univ j)
      _ = μ.weight i := hm.2.1 i
      _ ≤ 1 := hweight_le_one i
  have hSclosed : IsClosed S := by
    dsimp [S]
    simp only [Set.setOf_and]
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_iInter fun j =>
          isClosed_le
            (continuous_const : Continuous (fun _ : ι → κ → ℝ => (0 : ℝ)))
            (by fun_prop : Continuous (fun m : ι → κ → ℝ => m i j)))
    apply IsClosed.inter
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun i => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ j, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => μ.weight i)))
    · simpa only [Set.iInter_ofPred] using
        (isClosed_iInter fun j => isClosed_eq
          (by fun_prop : Continuous (fun m : ι → κ → ℝ => ∑ i, m i j))
          (by fun_prop : Continuous (fun _ : ι → κ → ℝ => ν.weight j)))
  have hScompact : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_Icc hSclosed hSsub
  let cost : (ι → κ → ℝ) → ℝ := fun m =>
    ∑ i, ∑ j, m i j * |μ.atom i - ν.atom j|
  have hcost_cont : Continuous cost := by
    unfold cost
    fun_prop
  obtain ⟨m, hmS, hmmin⟩ := hScompact.exists_isMinOn hSne hcost_cont.continuousOn
  let π : TransportPlan μ ν :=
    { mass := m
      nonneg := hmS.1
      fst_marginal := hmS.2.1
      snd_marginal := hmS.2.2 }
  refine ⟨π, ?_⟩
  have hvalues_ne : ({c : ℝ | ∃ q : TransportPlan μ ν, transportCost q = c}).Nonempty :=
    ⟨transportCost π, π, rfl⟩
  have hvalues_bdd : BddBelow {c : ℝ | ∃ q : TransportPlan μ ν, transportCost q = c} := by
    refine ⟨0, ?_⟩
    rintro c ⟨q, rfl⟩
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (q.nonneg i j) (abs_nonneg _)
  apply le_antisymm
  · unfold w1
    apply le_csInf hvalues_ne
    rintro c ⟨q, rfl⟩
    simpa [cost, transportCost, π] using
      hmmin ⟨q.nonneg, q.fst_marginal, q.snd_marginal⟩
  · unfold w1
    exact csInf_le hvalues_bdd ⟨π, rfl⟩

/-- The cumulative distribution function of a finite atomic representation. -/
noncomputable def cdf {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) (x : ℝ) : ℝ :=
  ∑ i, if μ.atom i ≤ x then μ.weight i else 0

/-- The pointwise difference of the two finite atomic cumulative distribution functions. -/
noncomputable def cdfGap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  μ.cdf x - ν.cdf x

/-- The signed amount of a transport plan crossing the cut at `x`, counted positively from the
left side of the cut to the right side and negatively in the reverse direction. -/
noncomputable def signedCrossing {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) (x : ℝ) : ℝ :=
  ∑ i, ∑ j, π.mass i j *
    (if μ.atom i ≤ x ∧ x < ν.atom j then 1
      else if ν.atom j ≤ x ∧ x < μ.atom i then -1 else 0)

/-- The unsigned amount of a transport plan crossing the cut at `x`, counting transport in both
directions. -/
noncomputable def crossingEnvelope {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) (x : ℝ) : ℝ :=
  ∑ i, ∑ j, π.mass i j *
    (if μ.atom i ≤ x ∧ x < ν.atom j ∨ ν.atom j ≤ x ∧ x < μ.atom i then 1 else 0)

/-- A transport plan has no counterflow when, at every real cut, mass crosses in at most one of
the two possible directions. -/
def CutMonotone {ι κ : Type*} [Fintype ι] [Fintype κ]
    {μ : AtomicLaw ι} {ν : AtomicLaw κ} (π : TransportPlan μ ν) : Prop :=
  ∀ x,
    (∑ i, ∑ j, if μ.atom i ≤ x ∧ x < ν.atom j then π.mass i j else 0) = 0 ∨
    (∑ i, ∑ j, if ν.atom j ≤ x ∧ x < μ.atom i then π.mass i j else 0) = 0

/-- The sign selector used to build an attaining Kantorovich--Rubinstein potential. -/
noncomputable def cdfSign {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  if 0 < cdfGap μ ν x then 1 else if cdfGap μ ν x < 0 then -1 else 0

private theorem measurable_cdf {ι : Type*} [Fintype ι] (μ : AtomicLaw ι) :
    Measurable μ.cdf := by
  classical
  unfold cdf
  change Measurable (fun x => ∑ i : ι,
    if μ.atom i ≤ x then μ.weight i else 0)
  apply Finset.measurable_sum Finset.univ
  intro i hi
  exact Measurable.ite
    (show MeasurableSet (Ici (μ.atom i)) from measurableSet_Ici)
    measurable_const measurable_const

private theorem measurable_cdfSign {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : Measurable (cdfSign μ ν) := by
  classical
  unfold cdfSign cdfGap
  have hgap : Measurable fun x => μ.cdf x - ν.cdf x :=
    (measurable_cdf μ).sub (measurable_cdf ν)
  exact Measurable.ite (measurableSet_Ioi.preimage hgap) measurable_const
    (Measurable.ite (measurableSet_Iio.preimage hgap) measurable_const measurable_const)

private theorem abs_cdfSign_le_one {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : |cdfSign μ ν x| ≤ 1 := by
  unfold cdfSign
  split_ifs <;> norm_num

/-- [Two finite atomic laws](hyp:μ,ν) have [a CDF-sign selector integrable on every bounded real interval](goal), for the [two interval endpoints](hyp:a,b). -/
theorem cdfSign_intervalIntegrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (a b : ℝ) :
    IntervalIntegrable (cdfSign μ ν) volume a b := by
  rw [intervalIntegrable_iff']
  apply volume.integrableOn_of_bounded (ne_of_lt isCompact_uIcc.measure_lt_top)
  · exact (measurable_cdfSign μ ν).aestronglyMeasurable
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using abs_cdfSign_le_one μ ν x

/-- The piecewise-linear primitive of the sign of the finite atomic CDF difference. -/
noncomputable def krPotential {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, cdfSign μ ν t

/-- [Two finite atomic laws](hyp:μ,ν) determine [a one-Lipschitz CDF-sign potential](goal). -/
theorem krPotential_lipschitz {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : LipschitzWith 1 (krPotential μ ν) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  rw [Real.dist_eq, Real.dist_eq]
  change |(∫ t in (0 : ℝ)..x, cdfSign μ ν t) -
    ∫ t in (0 : ℝ)..y, cdfSign μ ν t| ≤ (1 : ℝ) * |x - y|
  rw [
    intervalIntegral.integral_interval_sub_left
      (cdfSign_intervalIntegrable μ ν 0 x) (cdfSign_intervalIntegrable μ ν 0 y)]
  simpa [Real.norm_eq_abs, abs_sub_comm] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t ht => by simpa [Real.norm_eq_abs] using abs_cdfSign_le_one μ ν t) :
      ‖∫ t in y..x, cdfSign μ ν t‖ ≤ (1 : ℝ) * |x - y|)

/-- The canonical CDF-sign potential is normalized to vanish at zero. -/
@[simp] theorem krPotential_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) : krPotential μ ν 0 = 0 := by
  simp [krPotential]

/-- The finite-sum CDF of a valid atomic representation is the real mass of the corresponding
closed lower ray under its represented measure. -/
theorem cdf_eq_toMeasure_Iic {ι : Type*} [Fintype ι]
    (μ : AtomicLaw ι) (hμ : μ.Valid) (x : ℝ) :
    μ.cdf x = (μ.toMeasure (Iic x)).toReal := by
  /- Expand the finite sum measure, evaluate each Dirac mass on `Iic x`, and use
  `ENNReal.toReal_ofReal` with `hμ.1`. -/
  classical
  simp only [cdf, toMeasure, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iic,
    Set.indicator_apply, Pi.one_apply]
  rw [ENNReal.toReal_sum (by
    intro i hi
    split_ifs <;> simp [ENNReal.ofReal_ne_top])]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hix : μ.atom i ≤ x
  · simp [hix, ENNReal.toReal_ofReal (hμ.1 i)]
  · simp [hix]

/-- [Two finite atomic laws](hyp:μ,ν) that are [valid probability representations](hyp:hμ,hν) of [the same real measure](hyp:h) have [identical cumulative distribution functions](goal), regardless of slots or labels. -/
theorem cdf_eq_of_toMeasure_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (μ : AtomicLaw ι) (ν : AtomicLaw κ) (hμ : μ.Valid) (hν : ν.Valid)
    (h : μ.toMeasure = ν.toMeasure) : μ.cdf = ν.cdf := by
  funext x
  rw [cdf_eq_toMeasure_Iic μ hμ x, cdf_eq_toMeasure_Iic ν hν x, h]

end AtomicLaw

end Causalean.Stat.Coupling
