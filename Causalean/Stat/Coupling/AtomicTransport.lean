module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.Topology.Compactness.Compact

/-!
# Finite atomic laws and their transport polytope

This module defines finite atomic probability laws with arbitrary finite slot types, their
represented measures and finite expectations, transport plans between two such laws, and the
finite transport-polytope primal cost for `|x-y|`.  It defines the finite-atomic one-Wasserstein
distance as the infimum of that cost and proves that an optimal transport plan exists.
-/

@[expose] public section

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

/-- [Two finite atomic laws](hyp:μ,ν) with [finite slot types](hyp:ι,κ) and [nonnegative unit-mass weights](hyp:hμ,hν) have [a transport plan attaining their one-Wasserstein cost](goal). -/
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

end AtomicLaw

end Causalean.Stat.Coupling
