import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Independence.InfinitePi
import Causalean.Stat.Sample
import CausalSmith.SCM.SCM_SelectiveLabelUntrialedImpact_Research.Helpers.ClopperPearson

/-!
# Exact law of an independent Bernoulli count

This file supplies the sampling-law bridge needed by the finite-cell
Clopper--Pearson construction.  It is stated for an abstract independent
family of Bernoulli indicators, so a later sampling carrier can specialize it
to the events that an observation falls in a fixed cell.
-/

namespace CausalSmith.SCM.SelectiveLabelUntrialedImpact

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory unitInterval

/-- The number of successes among the first `n` members of a family of
proposition-valued indicators. -/
noncomputable def indicatorCount {Ω : Type*} (X : ℕ → Ω → Prop) (n : ℕ) : Ω → ℕ :=
  fun ω => Set.ncard {i | i < n ∧ X i ω}

/-- The first-`n` count of an independent family of identically distributed
Bernoulli indicators has the exact binomial law. -/
theorem hasLaw_indicatorCount_binomial
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → Prop) (p : I)
    (hXmeas : ∀ i, Measurable (X i))
    (hXindep : iIndepFun X μ)
    (hXlaw : ∀ i, HasLaw (X i) (Ber(True, False, p)) μ)
    (n : ℕ) :
    HasLaw (indicatorCount X n) (Bin(n, p)) μ := by
  let Y : ℕ → Ω → Prop := fun i ω => i < n ∧ X i ω
  have hYmeas : ∀ i, Measurable (Y i) := by
    intro i
    exact measurable_const.and (hXmeas i)
  have hYindep : iIndepFun Y μ := by
    exact hXindep.comp (fun i x => i < n ∧ x) (fun i => measurable_const.and measurable_id)
  have hYlaw : ∀ i, HasLaw (Y i) (Ber(i < n, False, p)) μ := by
    intro i
    by_cases hi : i < n
    · simpa [Y, hi] using hXlaw i
    · have hconst : HasLaw (fun _ : Ω => False) (Measure.dirac False) μ := by
        let _ : IsProbabilityMeasure μ := hXindep.isProbabilityMeasure
        exact ⟨measurable_const.aemeasurable, by simp⟩
      simpa [Y, hi, ProbabilityTheory.bernoulliMeasure_self_eq_dirac] using hconst
  have hJoint :
      HasLaw (fun ω i => Y i ω) (Measure.infinitePi fun i => Ber(i < n, False, p)) μ :=
    hYindep.hasLaw_infinitePi hYlaw (Measurable.aemeasurable <| measurable_pi_iff.2 hYmeas)
  have hSet :
      HasLaw (fun ω => {i | Y i ω}) setBer(Iio n, p) μ := by
    refine ⟨Measurable.aemeasurable (by fun_prop), ?_⟩
    change μ.map ((fun z : ℕ → Prop => {i | z i}) ∘ (fun ω i => Y i ω)) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (Measurable.aemeasurable (by fun_prop))
        hJoint.aemeasurable,
      hJoint.map_eq, setBernoulli_eq_map]
    congr 1
  have hCount :
      HasLaw (fun ω => Set.ncard {i | Y i ω})
        (setBer(Iio n, p).map Set.ncard) μ := by
    refine ⟨(by fun_prop), ?_⟩
    change μ.map (Set.ncard ∘ fun ω => {i | Y i ω}) = _
    rw [← AEMeasurable.map_map_of_aemeasurable (Measurable.aemeasurable (by fun_prop))
        hSet.aemeasurable,
      hSet.map_eq]
  change HasLaw (fun ω => Set.ncard {i | i < n ∧ X i ω})
    (setBer(Iio n, p).map Set.ncard) μ
  exact hCount

/-- The number of the first `n` observations of an i.i.d. sample which fall in
the measurable event `A`. -/
noncomputable def iidEventCount
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {μ : Measure Ω} {P : Measure 𝒳}
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) (A : Set 𝒳) (n : ℕ) : Ω → ℕ :=
  indicatorCount (fun i ω => S.Z i ω ∈ A) n

/-- For an i.i.d. sample, the number of observations in a measurable event of
probability `p` has the exact binomial law. -/
theorem hasLaw_iidEventCount_binomial
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {μ : Measure Ω} {P : Measure 𝒳}
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P)
    (A : Set 𝒳) (hA : MeasurableSet A) (p : I)
    (hPA : P A = (unitInterval.toNNReal p : ℝ≥0∞)) (n : ℕ) :
    HasLaw (iidEventCount S A n) (Bin(n, p)) μ := by
  let _ : IsProbabilityMeasure μ := S.indep.isProbabilityMeasure
  let _ : IsProbabilityMeasure P := by
    rw [← S.map_eq 0]
    exact Measure.isProbabilityMeasure_map (S.meas 0).aemeasurable
  let X : ℕ → Ω → Prop := fun i ω => S.Z i ω ∈ A
  have hXmeas : ∀ i, Measurable (X i) := by
    intro i
    exact hA.mem.comp (S.meas i)
  have hXindep : iIndepFun X μ :=
    S.indep.comp (fun _ x => x ∈ A) (fun _ => hA.mem)
  have hXlaw : ∀ i, HasLaw (X i) (Ber(True, False, p)) μ := by
    intro i
    refine ⟨(hXmeas i).aemeasurable, ?_⟩
    change μ.map ((fun x => x ∈ A) ∘ S.Z i) = _
    rw [← Measure.map_map hA.mem (S.meas i), S.map_eq]
    classical
    ext s hs
    rw [Measure.map_apply hA.mem hs,
      bernoulliMeasure_apply p hs]
    by_cases ht : True ∈ s <;> by_cases hf : False ∈ s
    · rw [show (fun x => x ∈ A) ⁻¹' s = Set.univ by
        ext x
        by_cases hx : x ∈ A <;> simp [hx, ht, hf]]
      simp [ht, hf]
    · rw [show (fun x => x ∈ A) ⁻¹' s = A by
        ext x
        by_cases hx : x ∈ A <;> simp [hx, ht, hf], hPA]
      simp [ht, hf]
    · rw [show (fun x => x ∈ A) ⁻¹' s = Aᶜ by
        ext x
        by_cases hx : x ∈ A <;> simp [hx, ht, hf],
        measure_compl hA (by rw [hPA]; simp), measure_univ, hPA]
      simp only [ht, hf, ↓reduceIte]
      apply ENNReal.sub_eq_of_eq_add (by simp)
      simpa only [ENNReal.coe_add, ENNReal.coe_one] using
        congrArg (fun q : ℝ≥0 => (q : ℝ≥0∞))
          (unitInterval.toNNReal_symm_add_toNNReal p).symm
    · rw [show (fun x => x ∈ A) ⁻¹' s = ∅ by
        ext x
        by_cases hx : x ∈ A <;> simp [hx, ht, hf]]
      simp [ht, hf]
  change HasLaw (indicatorCount X n) (Bin(n, p)) μ
  exact hasLaw_indicatorCount_binomial X p hXmeas hXindep hXlaw n

/-- The number of the first `n` observations equal to a fixed cell `o`. -/
noncomputable def iidCellCount
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {μ : Measure Ω} {P : Measure 𝒳}
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) (o : 𝒳) (n : ℕ) : Ω → ℕ :=
  iidEventCount S {o} n

/-- For an i.i.d. sample, the count in a measurable singleton cell of mass
`p` has the exact binomial law. -/
theorem hasLaw_iidCellCount_binomial
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {P : Measure 𝒳}
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) (o : 𝒳) (p : I)
    (hPo : P {o} = (unitInterval.toNNReal p : ℝ≥0∞)) (n : ℕ) :
    HasLaw (iidCellCount S o n) (Bin(n, p)) μ :=
  hasLaw_iidEventCount_binomial S {o} (measurableSet_singleton o) p hPo n

/-- The exact cell-count law transports the Clopper--Pearson miss bound from
the binomial measure to the ambient i.i.d. sampling space. -/
theorem iidCellCount_miss_clopperPearsonIntervalAtError_le
    {Ω 𝒳 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    [MeasurableSingletonClass 𝒳] {μ : Measure Ω} {P : Measure 𝒳}
    (S : Causalean.Stat.IIDSample Ω 𝒳 μ P) (o : 𝒳) (p : I)
    (hPo : P {o} = (unitInterval.toNNReal p : ℝ≥0∞))
    (n : ℕ) (marginalError : ℝ≥0∞) :
    μ {ω | p ∉ clopperPearsonIntervalAtError n marginalError (iidCellCount S o n ω)} ≤
      marginalError := by
  have hLaw := hasLaw_iidCellCount_binomial S o p hPo n
  calc
    μ {ω | p ∉ clopperPearsonIntervalAtError n marginalError (iidCellCount S o n ω)} =
        Bin(n, p) {k | p ∉ clopperPearsonIntervalAtError n marginalError k} :=
      hLaw.measure_eq (p := fun k => p ∉ clopperPearsonIntervalAtError n marginalError k)
        MeasurableSet.of_discrete
    _ ≤ marginalError :=
      binomial_miss_clopperPearsonIntervalAtError_le n p marginalError

end CausalSmith.SCM.SelectiveLabelUntrialedImpact
