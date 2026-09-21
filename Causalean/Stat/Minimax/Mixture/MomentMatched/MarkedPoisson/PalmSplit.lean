module
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.AggregatePoisson
public import Causalean.Stat.Minimax.Mixture.MomentMatched.MarkedPoisson.ZeroInflated
public import Causalean.Stat.Minimax.Mixture
public import Mathlib.Probability.Distributions.Binomial

/-!
# Label-gated marked-Poisson mixtures

This module defines a paper-independent four-count experiment.  Its two
labeled treated counts receive opposite homogeneous binary marks, while an
auxiliary treated count and an aggregate control count do not depend on the
branch.  Moment cancellation yields a geometric prior-predictive TV bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- The [marked-Poisson observation](goal) is the four-count outcome consisting of labeled
treated counts with marks one and zero, followed by auxiliary-treated and
aggregate-control counts, and is given by [the Cartesian product of four
natural-number count spaces](step:1). -/
abbrev MarkedPoissonObservation := (ℕ × ℕ) × (ℕ × ℕ)

/-- The [treated mass](goal) at [latent mass](hyp:p) is [the overlap fraction](hyp:ε) times the
mass plus [a shift](hyp:a), as given by [the displayed formula](step:1). -/
def treatedMass (ε a p : ℝ) : ℝ := ε * (p + a)

/-- The [aggregate control mass](goal) [subtracts treated mass from latent cell
mass](step:1). It is evaluated at [an overlap parameter](hyp:ε), [a shift](hyp:a), and [a latent
cell mass](hyp:p). -/
def controlMass (ε a p : ℝ) : ℝ := p - treatedMass ε a p

/-- The [signed branch mark](goal) [equals the mark on the alternative branch and its negation on
the null branch](step:1), for [an outcome-mark branch](hyp:branch) and [a mark value](hyp:h). -/
def branchMark (branch : Bool) (h : ℝ) : ℝ := if branch then h else -h

/-- At [latent mass](hyp:p), the [marked-Poisson observation law](goal) for [overlap
fraction](hyp:ε), [shift](hyp:a), [labeled intensity](hyp:u), [auxiliary intensity](hyp:v),
[mark function](hyp:h), and [branch](hyp:branch) is [the product of four independent Poisson
laws with the corresponding marked rates](step:1).

Real rates are truncated to nonnegative values; later support assumptions ensure that the
intended rates are already nonnegative. -/
noncomputable def markedPoissonLaw
    (ε a u v : ℝ) (h : ℝ → ℝ) (branch : Bool) (p : ℝ) :
    Measure MarkedPoissonObservation :=
  ((poissonMeasure (Real.toNNReal
      (u * treatedMass ε a p * (1 + branchMark branch (h p)) / 2))).prod
    (poissonMeasure (Real.toNNReal
      (u * treatedMass ε a p * (1 - branchMark branch (h p)) / 2)))).prod
    ((poissonMeasure (Real.toNNReal (v * treatedMass ε a p))).prod
      (poissonMeasure (Real.toNNReal ((u + v) * controlMass ε a p))))

/-- The marked-Poisson law [is a probability measure](goal), because [it is a product of four
Poisson probability measures](step:1). The law is indexed by [overlap](hyp:ε), [shift](hyp:a),
[labeled and auxiliary intensities](hyp:u,v), [an outcome-mark function](hyp:h), [a
branch](hyp:branch), and [latent mass](hyp:p). -/
noncomputable instance markedPoissonLaw_isProbabilityMeasure
    (ε a u v : ℝ) (h : ℝ → ℝ) (branch : Bool) (p : ℝ) :
    IsProbabilityMeasure (markedPoissonLaw ε a u v h branch p) := by
  unfold markedPoissonLaw
  infer_instance

/-- A real-valued rate function determines a Poisson probability law for each latent mass, with
negative rates truncated to zero. This kernel is the one-count building block for the marked
Poisson experiment. -/
noncomputable def poissonKernelOfRealRate (r : ℝ → ℝ) : Kernel ℝ ℕ :=
  (Kernel.const ℝ Measure.count).withDensity fun p n =>
    ENNReal.ofReal (Real.exp (-(Real.toNNReal (r p) : ℝ)) *
      (Real.toNNReal (r p) : ℝ) ^ n / Nat.factorial n)

private noncomputable instance poissonKernelOfRealRate_isSFinite (r : ℝ → ℝ) :
    IsSFiniteKernel (poissonKernelOfRealRate r) := by
  unfold poissonKernelOfRealRate
  apply Kernel.IsSFiniteKernel.withDensity
  simp

private theorem poissonKernelOfRealRate_apply
    (r : ℝ → ℝ) (hr : Measurable r) (p : ℝ) :
    poissonKernelOfRealRate r p = poissonMeasure (Real.toNNReal (r p)) := by
  rw [poissonKernelOfRealRate, Kernel.withDensity_apply]
  · apply Measure.ext_of_singleton
    intro n
    rw [withDensity_apply _ (measurableSet_singleton n), poissonMeasure_singleton]
    simp
  · apply measurable_from_prod_countable_left
    intro n
    fun_prop

/-- The [four-count marked-Poisson experiment](goal) sends latent mass to observations using
[overlap fraction](hyp:ε), [shift](hyp:a), [labeled intensity](hyp:u), [auxiliary
intensity](hyp:v), [a measurable mark function](hyp:h,hh), and [a branch](hyp:branch), and is
[formed as the product of the four corresponding Poisson kernels](step:1). -/
noncomputable def markedPoissonKernel
    (ε a u v : ℝ) (h : ℝ → ℝ) (hh : Measurable h) (branch : Bool) :
    Kernel ℝ MarkedPoissonObservation :=
  ((poissonKernelOfRealRate fun p =>
      u * treatedMass ε a p * (1 + branchMark branch (h p)) / 2) ×ₖ
    (poissonKernelOfRealRate fun p =>
      u * treatedMass ε a p * (1 - branchMark branch (h p)) / 2)) ×ₖ
    ((poissonKernelOfRealRate fun p => v * treatedMass ε a p) ×ₖ
      (poissonKernelOfRealRate fun p => (u + v) * controlMass ε a p))

/-- The fibre of the marked-Poisson kernel at [latent mass](hyp:p) [equals the explicit
four-count law](goal) for the same [overlap fraction](hyp:ε), [shift](hyp:a), [labeled
intensity](hyp:u), [auxiliary intensity](hyp:v), [measurable mark function](hyp:h,hh), and
[branch](hyp:branch). -/
theorem markedPoissonKernel_apply
    (ε a u v : ℝ) (h : ℝ → ℝ) (hh : Measurable h)
    (branch : Bool) (p : ℝ) :
    markedPoissonKernel ε a u v h hh branch p =
      markedPoissonLaw ε a u v h branch p := by
  unfold markedPoissonKernel markedPoissonLaw
  rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply]
  rw [poissonKernelOfRealRate_apply _ (by
        cases branch <;> simp [treatedMass, branchMark] <;> fun_prop),
    poissonKernelOfRealRate_apply _ (by
      cases branch <;> simp [treatedMass, branchMark] <;> fun_prop),
    poissonKernelOfRealRate_apply _ (by simp [treatedMass] <;> fun_prop),
    poissonKernelOfRealRate_apply _ (by simp [controlMass, treatedMass] <;> fun_prop)]

namespace NormalizedFiniteSignedMomentCertificate

/-- A [finite signed certificate](hyp:C), with [node index set](hyp:ι) and [matching
degree](hyp:L), induces the [one-coordinate marked-Poisson predictive law](goal) for [overlap
fraction](hyp:ε), [shift](hyp:a), [labeled intensity](hyp:u), [auxiliary intensity](hyp:v), and
[branch](hyp:branch) by [mixing over its zero-inflated variation prior](step:1). -/
noncomputable def markedPoissonPredictive
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v : ℝ) (branch : Bool) : Measure MarkedPoissonObservation :=
  Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    (C.zeroInflatedPrior a)
    (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch)

/-- The one-coordinate marked-Poisson predictive law from [a certificate with its node set and
matching degree](hyp:C,ι,L), at [overlap, shift, intensities, support ratio, support bound, and
branch](hyp:ε,a,u,v,κ,B,branch), [is a probability measure](goal) when [the shift is
positive](hyp:ha), [the support ratio is positive](hyp:hκ), and [the certificate variation has
the stated compact support](hyp:hsupp). -/
theorem markedPoissonPredictive_isProbabilityMeasure
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ) (branch : Bool)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    IsProbabilityMeasure (C.markedPoissonPredictive ε a u v branch) := by
  letI : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    C.zeroInflatedPrior_isProbabilityMeasure a κ B ha hκ hsupp
  exact Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
    (C.zeroInflatedPrior a)
    (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch)
    (fun p => by
      rw [markedPoissonKernel_apply]
      infer_instance)

/-- The [zero-labeled-count event](goal) consists of observations in which [neither outcome mark
has a labeled treated count](step:1). -/
def noLabeledTreated : Set MarkedPoissonObservation :=
  {z | z.1.1 + z.1.2 = 0}

/-- The [event that no labeled treated observation occurs in either outcome
mark is measurable](goal). -/
theorem measurableSet_noLabeledTreated : MeasurableSet noLabeledTreated := by
  exact MeasurableSet.of_discrete

private theorem markedPoissonLaw_singleton_eq_of_noLabeledTreated
    (ε a u v : ℝ) (h : ℝ → ℝ) (p : ℝ) (z : MarkedPoissonObservation)
    (hz : z ∈ noLabeledTreated) :
    markedPoissonLaw ε a u v h false p {z} =
      markedPoissonLaw ε a u v h true p {z} := by
  rcases z with ⟨⟨x, y⟩, ⟨s, t⟩⟩
  simp only [noLabeledTreated, Set.mem_setOf_eq] at hz
  have hx : x = 0 := by omega
  have hy : y = 0 := by omega
  subst x
  subst y
  unfold markedPoissonLaw
  simp_rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [branchMark, poissonMeasure_singleton, mul_comm]
  ring_nf

/-- The two branch-specific predictive laws from [a certificate with its node set and matching
degree](hyp:C,ι,L) [agree after restriction to the event with no labeled treated
count](goal), at [overlap, shift, intensities, support ratio, and support
bound](hyp:ε,a,u,v,κ,B), provided [the shift is positive](hyp:ha), [the support ratio is
positive](hyp:hκ), and [the certificate variation has the stated compact support](hyp:hsupp). -/
theorem restrict_markedPoissonPredictive_noLabeledTreated_eq
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ)
    (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    (C.markedPoissonPredictive ε a u v false).restrict noLabeledTreated =
      (C.markedPoissonPredictive ε a u v true).restrict noLabeledTreated := by
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.restrict_apply (measurableSet_singleton z),
    Measure.restrict_apply (measurableSet_singleton z)]
  by_cases hz : z ∈ noLabeledTreated
  · have hinter : {z} ∩ noLabeledTreated = {z} :=
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hz)
    rw [hinter]
    unfold markedPoissonPredictive
    rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z),
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z)]
    apply lintegral_congr
    intro p
    rw [markedPoissonKernel_apply, markedPoissonKernel_apply]
    exact markedPoissonLaw_singleton_eq_of_noLabeledTreated
      ε a u v C.polarSign p z hz
  · have hinter : {z} ∩ noLabeledTreated = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_singleton_left.mpr hz)
    rw [hinter]
    simp

/-- For [two probability measures](hyp:μ,ν), applying [a common Markov kernel](hyp:K)
[cannot increase their total-variation distance](goal). This is a deprecated local forwarding
name for the general data-processing theorem. -/
@[deprecated Causalean.Stat.tvDist_bind_le (since := "2026-09-19")]
theorem tvDist_bind_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    Causalean.Stat.tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤
      Causalean.Stat.tvDist μ ν :=
  Causalean.Stat.tvDist_bind_le μ ν K

/-- For [an extended-nonnegative scaling coefficient](hyp:c) that [is finite](hyp:hc), [the
real-valued mass of a measure plus that coefficient times the sum of two finite measures equals
the corresponding sum of real-valued masses](goal). -/
theorem measureReal_add_ennreal_smul_add
    {X : Type*} [MeasurableSpace X]
    (μ ν ξ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] (c : ℝ≥0∞) (hc : c ≠ ∞) (A : Set X) :
    (μ + c • (ν + ξ)).real A =
      μ.real A + c.toReal * (ν.real A + ξ.real A) := by
  let _ : IsFiniteMeasure (c • (ν + ξ)) := Measure.smul_finite _ hc
  rw [MeasureTheory.measureReal_add_apply
        (μ₁ := μ) (μ₂ := c • (ν + ξ)),
    MeasureTheory.measureReal_ennreal_smul_apply,
    MeasureTheory.measureReal_add_apply (μ₁ := ν) (μ₂ := ξ)]

/-- For [an outcome-mark branch](hyp:first), [an aggregate Poisson observation](hyp:z), and [a
splitting count](hyp:k), the [Palm-split embedded observation](goal) records the marked
observation obtained by assigning that count to the selected branch. It is the atomic outcome
used to construct the Palm-split law. -/
def palmSplitEmbed
    (first : Bool) (z : AggregatePoissonObservation) (k : ℕ) :
    MarkedPoissonObservation :=
  if k ≤ z.1 then
    if first then ((k + 1, 0), (z.1 - k, z.2))
    else ((0, k + 1), (z.1 - k, z.2))
  else ((0, 0), (0, 0))

/-- For [a binomial success probability](hyp:q), [an outcome-mark branch](hyp:first), and [an
aggregate Poisson observation](hyp:z), the [Palm-split submeasure](goal) distributes
inverse-size-biased binomial mass over its marked split outcomes. It provides the non-null part
of the Palm-split probability law. -/
noncomputable def palmSplitSubmeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  ∑ k ∈ Finset.range (z.1 + 1),
    ENNReal.ofReal
      ((binomial z.1 q).real {k} * (1 / ((k : ℝ) + 1))) •
        Measure.dirac (palmSplitEmbed first z k)

/-- [The total mass of every Palm-split submeasure is at most one](goal). -/
theorem palmSplitSubmeasure_univ_le
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    palmSplitSubmeasure q first z Set.univ ≤ 1 := by
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  calc
    ∑ k ∈ Finset.range (z.1 + 1),
        ENNReal.ofReal ((binomial z.1 q).real {k} * (1 / ((k : ℝ) + 1))) ≤
        ∑ k ∈ Finset.range (z.1 + 1), (binomial z.1 q) {k} := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def]
      apply ENNReal.ofReal_le_ofReal
      have hprob : 0 ≤ (binomial z.1 q).real {k} := measureReal_nonneg
      have hrecip : 1 / ((k : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by norm_num)
      nlinarith
    _ ≤ (binomial z.1 q) Set.univ := by
      rw [sum_measure_singleton]
      exact measure_mono (Set.subset_univ _)
    _ = 1 := by simp

/-- For [a binomial success probability](hyp:q), [an outcome-mark branch](hyp:first), and [an
aggregate Poisson observation](hyp:z), the [Palm-split probability measure](goal) completes the
Palm-split submeasure by placing its remaining mass on the null observation. It is the
probability law used to define the associated Markov kernel. -/
noncomputable def palmSplitMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  palmSplitSubmeasure q first z +
    (1 - palmSplitSubmeasure q first z Set.univ) •
      Measure.dirac ((0, 0), (0, 0))

/-- For [a splitting probability](hyp:q), [a choice of labeled coordinate](hyp:first), and [an
aggregate Poisson observation](hyp:z), [the corresponding Palm-split measure is a probability
measure](goal), because [its total mass is one](step:1). -/
noncomputable instance palmSplitMeasure_isProbabilityMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    IsProbabilityMeasure (palmSplitMeasure q first z) := by
  constructor
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le (palmSplitSubmeasure_univ_le q first z)

/-- For [a binomial success probability](hyp:q) and [an outcome-mark branch](hyp:first), the
[Palm-split kernel](goal) maps each aggregate Poisson observation to its Palm-split probability
law. It transports aggregate predictive laws into the marked-observation experiment. -/
noncomputable def palmSplitKernel
    (q : unitInterval) (first : Bool) :
    Kernel AggregatePoissonObservation MarkedPoissonObservation :=
  Kernel.ofFunOfCountable (palmSplitMeasure q first)

/-- For [a splitting probability](hyp:q) and [a choice of labeled coordinate](hyp:first), [the
Palm-split kernel is a Markov kernel](goal), because [every output Palm-split measure is a
probability measure](step:1). -/
noncomputable instance palmSplitKernel_isMarkovKernel
    (q : unitInterval) (first : Bool) :
    IsMarkovKernel (palmSplitKernel q first) where
  isProbabilityMeasure z := palmSplitMeasure_isProbabilityMeasure q first z

/-- For [an outcome-mark branch](hyp:first), [a selected count](hyp:k), and [the remaining
treated and control counts](hyp:s,t), the [Palm-split target observation](goal) places the
selected count in the branch's labeled coordinate and retains the remaining counts. It names the
singleton event evaluated in the Palm-split identities. -/
def palmSplitTarget
    (first : Bool) (k s t : ℕ) : MarkedPoissonObservation :=
  if first then ((k + 1, 0), (s, t)) else ((0, k + 1), (s, t))

private theorem palmSplitSubmeasure_target
    (q : unitInterval) (first : Bool) (k s t : ℕ) :
    palmSplitSubmeasure q first (k + s, t) {palmSplitTarget first k s t} =
      ENNReal.ofReal
        ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1))) := by
  classical
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem, smul_eq_mul, mul_one]
    cases first <;> simp [palmSplitEmbed, palmSplitTarget]
  · intro j hj hjk
    rw [Measure.smul_apply]
    have hjle : j ≤ k + s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hne : palmSplitEmbed first (k + s, t) j ≠
        palmSplitTarget first k s t := by
      cases first <;> simp [palmSplitEmbed, palmSplitTarget, hjle] at * <;> omega
    simp [hne]
  · simp

private theorem palmSplitSubmeasure_target_eq_ite
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitSubmeasure q first z {palmSplitTarget first k s t} =
      if z = (k + s, t) then
        ENNReal.ofReal
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 := by
  classical
  by_cases hz : z = (k + s, t)
  · subst z
    rw [if_pos rfl]
    exact palmSplitSubmeasure_target q first k s t
  · rw [if_neg hz, palmSplitSubmeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Measure.smul_apply]
    have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hne : palmSplitEmbed first z j ≠ palmSplitTarget first k s t := by
      intro heq
      cases z with
      | mk n c =>
        simp only [palmSplitEmbed, palmSplitTarget, hjle, ↓reduceIte] at heq hz
        cases first <;> simp_all <;> omega
    simp [hne]

private theorem palmSplitMeasure_target_eq_ite
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitMeasure q first z {palmSplitTarget first k s t} =
      if z = (k + s, t) then
        ENNReal.ofReal
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 := by
  have hne : palmSplitTarget first k s t ≠ ((0, 0), (0, 0)) := by
    cases first <;> simp [palmSplitTarget]
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Set.indicator_of_notMem (by simpa using hne.symm), smul_eq_mul,
    mul_zero, add_zero]
  exact palmSplitSubmeasure_target_eq_ite q first z k s t

private theorem palmSplitMeasure_wrong_target
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitMeasure q (!first) z {palmSplitTarget first k s t} = 0 := by
  classical
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hne : palmSplitTarget first k s t ≠ ((0, 0), (0, 0)) := by
    cases first <;> simp [palmSplitTarget]
  rw [Set.indicator_of_notMem (by simpa using hne.symm), smul_eq_mul,
    mul_zero, add_zero]
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hemb : palmSplitEmbed (!first) z j ≠ palmSplitTarget first k s t := by
    cases first <;> simp [palmSplitEmbed, palmSplitTarget, hjle]
  simp [hemb]

private theorem palmSplitMeasure_both_positive
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k l s t : ℕ) :
    palmSplitMeasure q first z {((k + 1, l + 1), (s, t))} = 0 := by
  classical
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Set.indicator_of_notMem (by simp), smul_eq_mul, mul_zero, add_zero]
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hemb : palmSplitEmbed first z j ≠ ((k + 1, l + 1), (s, t)) := by
    cases first <;> simp [palmSplitEmbed, hjle]
  simp [hemb]

private theorem palmSplitMeasure_no_labeled_eq
    (q : unitInterval) (z : AggregatePoissonObservation) (s t : ℕ) :
    palmSplitMeasure q false z {((0, 0), (s, t))} =
      palmSplitMeasure q true z {((0, 0), (s, t))} := by
  classical
  have hsub (first : Bool) :
      palmSplitSubmeasure q first z {((0, 0), (s, t))} = 0 := by
    rw [palmSplitSubmeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Measure.smul_apply]
    have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hemb : palmSplitEmbed first z j ≠ ((0, 0), (s, t)) := by
      cases first <;> simp [palmSplitEmbed, hjle]
    simp [hemb]
  have huniv (first : Bool) :
      palmSplitSubmeasure q first z Set.univ =
        ∑ j ∈ Finset.range (z.1 + 1),
          ENNReal.ofReal
            ((binomial z.1 q).real {j} * (1 / ((j : ℝ) + 1))) := by
    rw [palmSplitSubmeasure, Measure.finsetSum_apply]
    simp
  unfold palmSplitMeasure
  rw [Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, hsub, hsub, huniv, huniv]

/-- [Applying the Palm-split kernel for the opposite labeled coordinate assigns zero real mass to
the specified Palm-split target singleton](goal). -/
theorem palmSplit_bind_wrong_target
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k s t : ℕ) :
    (palmSplitKernel q (!first) ∘ₘ ρ).real
      {palmSplitTarget first k s t} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q (!first) z
      {palmSplitTarget first k s t} = 0 from
    fun z => palmSplitMeasure_wrong_target q first z k s t]
  simp

/-- [A Palm-split kernel followed by any probability law assigns zero real mass to every
singleton whose two labeled counts are both positive](goal). -/
theorem palmSplit_bind_both_positive
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k l s t : ℕ) :
    (palmSplitKernel q first ∘ₘ ρ).real {((k + 1, l + 1), (s, t))} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q first z {((k + 1, l + 1), (s, t))} = 0 from
    fun z => palmSplitMeasure_both_positive q first z k l s t]
  simp

/-- [For a singleton with no labeled counts, the two Palm-split kernels followed by the same
probability law assign equal real mass](goal). -/
theorem palmSplit_bind_no_labeled_eq
    (q : unitInterval) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (s t : ℕ) :
    (palmSplitKernel q false ∘ₘ ρ).real {((0, 0), (s, t))} =
      (palmSplitKernel q true ∘ₘ ρ).real {((0, 0), (s, t))} := by
  rw [measureReal_def, measureReal_def,
    Measure.bind_apply (measurableSet_singleton _) (by fun_prop),
    Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  apply congrArg ENNReal.toReal
  apply lintegral_congr
  intro z
  exact palmSplitMeasure_no_labeled_eq q z s t

/-- [The real-valued mass that a product of two finite measures assigns to a singleton pair is
the product of their respective singleton masses](goal). -/
theorem prod_real_singleton
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : X) (y : Y) :
    (μ.prod ν).real {(x, y)} = μ.real {x} * ν.real {y} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]

private theorem poisson_binomial_split
    (u v r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (ht : 0 < u + v) (k s : ℕ) :
    (poissonMeasure (Real.toNNReal ((u + v) * r))).real {k + s} *
        (binomial (k + s)
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval)).real {k} =
      (poissonMeasure (Real.toNNReal (u * r))).real {k} *
        (poissonMeasure (Real.toNNReal (v * r))).real {s} := by
  rw [poissonMeasure_real_singleton, binomial_real_singleton,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hfacNat :=
    Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k s)
  rw [Nat.add_sub_cancel_left] at hfacNat
  have hfac :
      ((k + s).choose k : ℝ) * (k.factorial : ℝ) * (s.factorial : ℝ) =
        ((k + s).factorial : ℝ) := by
    exact_mod_cast hfacNat
  simp only [Nat.add_sub_cancel_left]
  rw [Real.coe_toNNReal _ (mul_nonneg (add_nonneg hu hv) hr),
    Real.coe_toNNReal _ (mul_nonneg hu hr),
    Real.coe_toNNReal _ (mul_nonneg hv hr)]
  rw [show (1 - u / (u + v) : ℝ) = v / (u + v) by
    field_simp
    ring]
  have hexp : Real.exp (-((u + v) * r)) =
      Real.exp (-(u * r)) * Real.exp (-(v * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, pow_add, mul_pow, mul_pow, div_pow, div_pow]
  field_simp
  rw [← hfac]
  ring

/-- If [the Poisson rate is nonnegative](hyp:hrate) and [the shifted support point is
positive](hyp:hpa), then [the offset-weighted probability of count k+1 equals the stated
size-biased multiple of the probability of count k](goal). -/
theorem poisson_palm
    (ε a u p : ℝ) (hrate : 0 ≤ u * (ε * (p + a)))
    (hpa : 0 < p + a) (k : ℕ) :
    a / (p + a) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k + 1} =
      (u * ε * a / ((k : ℝ) + 1)) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k} := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton,
    Real.coe_toNNReal _ hrate, show k + 1 = Nat.succ k by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- If [the mark sign is either one or minus one](hyp:hsign), then [the difference between the two
branch-specific marked Poisson laws at a Palm-split target factors into the signed product of
three Poisson singleton masses](goal). -/
theorem markedPoissonLaw_real_target_sub
    (ε a u v p sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (first : Bool) (k s t : ℕ) :
    (markedPoissonLaw ε a u v (fun _ => sign) false p).real
        {palmSplitTarget first k s t} -
      (markedPoissonLaw ε a u v (fun _ => sign) true p).real
        {palmSplitTarget first k s t} =
      (if first then -sign else sign) *
        (poissonMeasure
          (Real.toNNReal (u * (ε * (p + a))))).real {k + 1} *
        (poissonMeasure
          (Real.toNNReal (v * (ε * (p + a))))).real {s} *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by
  rcases hsign with rfl | rfl <;> cases first <;>
    simp [markedPoissonLaw, palmSplitTarget, branchMark, treatedMass,
      prod_real_singleton, poissonMeasure_real_singleton,
      zero_pow (by omega : 1 + k ≠ 0)] <;> ring

/-- For [an overlap fraction, positive shift, labeled and auxiliary treated intensities, and
latent mass](hyp:ε,a,u,v,p), if [both intensities are nonnegative](hyp:hu,hv), [their sum is
positive](hyp:ht), [the treated rate is nonnegative](hyp:hr), and [the control rate is
nonnegative](hyp:hc), then for [a selected outcome branch and three count
indices](hyp:first,k,s,t), [the Palm-split aggregate Poisson law assigns the target singleton
the displayed inverse-size-biased product of three Poisson masses](goal). -/
theorem palmSplit_aggregatePoissonLaw_real_target
    (ε a u v p : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hr : 0 ≤ ε * (p + a)) (hc : 0 ≤ controlMass ε a p)
    (first : Bool) (k s t : ℕ) :
    (palmSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) first ∘ₘ
      aggregatePoissonLaw ε a (u + v) p).real
        {palmSplitTarget first k s t} =
      (1 / ((k : ℝ) + 1)) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k} *
        (poissonMeasure (Real.toNNReal (v * (ε * (p + a))))).real {s} *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  let A : Set MarkedPoissonObservation := {palmSplitTarget first k s t}
  have hreal :
      (palmSplitKernel q first ∘ₘ aggregatePoissonLaw ε a (u + v) p).real A =
        ∫ z, (palmSplitMeasure q first z).real A
          ∂aggregatePoissonLaw ε a (u + v) p := by
    rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
    rw [← integral_toReal (by fun_prop)]
    · apply integral_congr_ae
      filter_upwards with z
      rfl
    · filter_upwards with z
      exact measure_lt_top _ _
  change (palmSplitKernel q first ∘ₘ aggregatePoissonLaw ε a (u + v) p).real A = _
  rw [hreal]
  rw [integral_countable (by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ A) (measure_ne_top _ _)).trans_eq
      (by simp))]
  simp only [smul_eq_mul]
  rw [show (fun z : AggregatePoissonObservation =>
      (aggregatePoissonLaw ε a (u + v) p).real {z} *
        (palmSplitMeasure q first z).real A) = fun z =>
      if z = (k + s, t) then
        (aggregatePoissonLaw ε a (u + v) p).real {z} *
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 by
    funext z
    dsimp [A]
    simp only [measureReal_def]
    rw [palmSplitMeasure_target_eq_ite]
    split_ifs with hz
    · rw [ENNReal.toReal_ofReal
        (mul_nonneg measureReal_nonneg (by positivity))]
      rfl
    · simp]
  rw [tsum_ite_eq (k + s, t)]
  rw [aggregatePoissonLaw, prod_real_singleton,
    aggregateTreatedRate, aggregateControlRate]
  have hcontrol : (1 - ε) * p - ε * a = controlMass ε a p := by
    simp [controlMass, treatedMass]
    ring
  rw [hcontrol]
  rw [show (u + v) * ε * (p + a) = (u + v) * (ε * (p + a)) by ring]
  dsimp [q]
  have hsplit := poisson_binomial_split u v (ε * (p + a)) hu hv hr ht k s
  calc
    _ = ((poissonMeasure
          (Real.toNNReal ((u + v) * (ε * (p + a))))).real {k + s} *
          (binomial (k + s)
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval)).real {k}) *
        (1 / ((k : ℝ) + 1)) *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by ring
    _ = _ := by rw [hsplit]; ring



end NormalizedFiniteSignedMomentCertificate
end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
