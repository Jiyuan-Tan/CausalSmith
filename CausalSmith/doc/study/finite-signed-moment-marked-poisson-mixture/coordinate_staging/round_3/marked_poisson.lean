import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.ZeroInflated
import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.AggregatePoisson
import Causalean.Stat.Minimax.Mixture
import Causalean.Stat.Minimax.MomentMatchedMixture.SupportLocalized
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Kernel.WithDensity

/-!
# Label-gated marked-Poisson mixtures

This module defines a paper-independent four-count experiment.  Its two
labeled treated counts receive opposite homogeneous binary marks, while an
auxiliary treated count and an aggregate control count do not depend on the
branch.  Moment cancellation yields a geometric prior-predictive TV bound.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

/-- The [defined object](goal) is determined by the displayed assumptions and is given by [the following defining expression](step:1).  One coordinate of the marked-Poisson experiment: labeled treated counts
with marks one and zero, followed by auxiliary-treated and aggregate-control
counts. -/
abbrev MarkedPoissonObservation := (ℕ × ℕ) × (ℕ × ℕ)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The treated mass attached to latent mass `p`, overlap level `ε`, and shift
`a`. -/
def treatedMass (ε a p : ℝ) : ℝ := ε * (p + a)

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The aggregate control mass left after subtracting the treated mass from
the latent cell mass. -/
def controlMass (ε a p : ℝ) : ℝ := p - treatedMass ε a p

/-- The [defined object](goal) is determined by [the outcome-mark branch](hyp:branch), [the outcome-mark function](hyp:h) and is given by [the following defining expression](step:1).  The signed outcome mark for a branch: the alternative uses `h`, while the
null uses `-h`. -/
def branchMark (branch : Bool) (h : ℝ) : ℝ := if branch then h else -h

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark function](hyp:h), [the outcome-mark branch](hyp:branch), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The explicit law of the four independent Poisson counts at latent `p`.
Real rates are converted to nonnegative rates by `Real.toNNReal`; the main
theorems' support assumptions ensure the intended rates are already
nonnegative. -/
noncomputable def markedPoissonLaw
    (ε a u v : ℝ) (h : ℝ → ℝ) (branch : Bool) (p : ℝ) :
    Measure MarkedPoissonObservation :=
  ((poissonMeasure (Real.toNNReal
      (u * treatedMass ε a p * (1 + branchMark branch (h p)) / 2))).prod
    (poissonMeasure (Real.toNNReal
      (u * treatedMass ε a p * (1 - branchMark branch (h p)) / 2)))).prod
    ((poissonMeasure (Real.toNNReal (v * treatedMass ε a p))).prod
      (poissonMeasure (Real.toNNReal ((u + v) * controlMass ε a p))))

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark function](hyp:h), [the outcome-mark branch](hyp:branch), [the latent mass](hyp:p) and is given by [the following defining expression](step:1).  The marked-Poisson law is a probability measure for every parameter. -/
noncomputable instance markedPoissonLaw_isProbabilityMeasure
    (ε a u v : ℝ) (h : ℝ → ℝ) (branch : Bool) (p : ℝ) :
    IsProbabilityMeasure (markedPoissonLaw ε a u v h branch p) := by
  unfold markedPoissonLaw
  infer_instance

private noncomputable def poissonKernelOfRealRate (r : ℝ → ℝ) : Kernel ℝ ℕ :=
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

/-- The [defined object](goal) is determined by [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark function](hyp:h), [measurability of the mark function](hyp:hh), [the outcome-mark branch](hyp:branch) and is given by [the following defining expression](step:1).  The four-count experiment as a probability kernel from the latent real
mass to marked-Poisson observations. -/
noncomputable def markedPoissonKernel
    (ε a u v : ℝ) (h : ℝ → ℝ) (hh : Measurable h) (branch : Bool) :
    Kernel ℝ MarkedPoissonObservation :=
  ((poissonKernelOfRealRate fun p =>
      u * treatedMass ε a p * (1 + branchMark branch (h p)) / 2) ×ₖ
    (poissonKernelOfRealRate fun p =>
      u * treatedMass ε a p * (1 - branchMark branch (h p)) / 2)) ×ₖ
    ((poissonKernelOfRealRate fun p => v * treatedMass ε a p) ×ₖ
      (poissonKernelOfRealRate fun p => (u + v) * controlMass ε a p))

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark function](hyp:h), [measurability of the mark function](hyp:hh), [the outcome-mark branch](hyp:branch), [the latent mass](hyp:p).  The marked-Poisson kernel's fibre is the explicit four-count law. -/
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

/-- The [defined object](goal) is determined by [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the outcome-mark branch](hyp:branch) and is given by [the following defining expression](step:1).  The one-coordinate prior-predictive marked-Poisson law obtained by mixing
the zero-inflated variation prior over the latent mass. -/
noncomputable def markedPoissonPredictive
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v : ℝ) (branch : Bool) : Measure MarkedPoissonObservation :=
  Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    (C.zeroInflatedPrior a)
    (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch)

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [the outcome-mark branch](hyp:branch), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp).  The one-coordinate marked-Poisson predictive law is a probability measure
under the support assumptions that normalize the zero-inflated prior. -/
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

/-- The [defined object](goal) is determined by the displayed assumptions and is given by [the following defining expression](step:1).  The event that no labeled treated observation appears in either outcome
mark. -/
def noLabeledTreated : Set MarkedPoissonObservation :=
  {z | z.1.1 + z.1.2 = 0}

/-- The [stated conclusion](goal) follows from the displayed assumptions.  The no-labeled-treated event is measurable. -/
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

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the support ratio](hyp:κ), [the support upper bound](hyp:B), [positive shift](hyp:ha), [the support-ratio identity](hyp:hκ), [the compact-support condition](hyp:hsupp).  On the zero-labeled-count event, the two prior-predictive laws agree
exactly; the auxiliary treated and aggregate control counts are branch
invariant. -/
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

private theorem tvDist_bind_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    Causalean.Stat.tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤
      Causalean.Stat.tvDist μ ν := by
  let _ : IsProbabilityMeasure (K ∘ₘ μ) := by infer_instance
  let _ : IsProbabilityMeasure (K ∘ₘ ν) := by infer_instance
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hreal (ρ : Measure X) [IsProbabilityMeasure ρ] :
      (K ∘ₘ ρ).real A = ∫ x, (K x A).toReal ∂ρ := by
    rw [measureReal_def, Measure.bind_apply hA K.aemeasurable,
      integral_toReal (K.measurable_coe hA).aemeasurable]
    filter_upwards with x
    exact measure_lt_top (K x) A
  rw [hreal μ, hreal ν]
  have hrange : ∀ x, (K x A).toReal ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle := ENNReal.toReal_mono (measure_ne_top (K x) _)
        (measure_mono (Set.subset_univ A))
      simpa using hle
  simpa only [zero_add, mul_one, Causalean.Stat.tvDist] using
    Causalean.Stat.tvDist_integral_range μ ν
      (fun x => (K x A).toReal) (K.measurable_coe hA).ennreal_toReal
      0 1 (by norm_num) (by simpa using hrange)

private theorem measureReal_add_ennreal_smul_add
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

private def palmSplitEmbed
    (first : Bool) (z : AggregatePoissonObservation) (k : ℕ) :
    MarkedPoissonObservation :=
  if k ≤ z.1 then
    if first then ((k + 1, 0), (z.1 - k, z.2))
    else ((0, k + 1), (z.1 - k, z.2))
  else ((0, 0), (0, 0))

private noncomputable def palmSplitSubmeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  ∑ k ∈ Finset.range (z.1 + 1),
    ENNReal.ofReal
      ((binomial z.1 q).real {k} * (1 / ((k : ℝ) + 1))) •
        Measure.dirac (palmSplitEmbed first z k)

private theorem palmSplitSubmeasure_univ_le
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

private noncomputable def palmSplitMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  palmSplitSubmeasure q first z +
    (1 - palmSplitSubmeasure q first z Set.univ) •
      Measure.dirac ((0, 0), (0, 0))

private noncomputable instance palmSplitMeasure_isProbabilityMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    IsProbabilityMeasure (palmSplitMeasure q first z) := by
  constructor
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le (palmSplitSubmeasure_univ_le q first z)

private noncomputable def palmSplitKernel
    (q : unitInterval) (first : Bool) :
    Kernel AggregatePoissonObservation MarkedPoissonObservation :=
  Kernel.ofFunOfCountable (palmSplitMeasure q first)

private noncomputable instance palmSplitKernel_isMarkovKernel
    (q : unitInterval) (first : Bool) :
    IsMarkovKernel (palmSplitKernel q first) where
  isProbabilityMeasure z := palmSplitMeasure_isProbabilityMeasure q first z

private def palmSplitTarget
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

private theorem palmSplit_bind_wrong_target
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k s t : ℕ) :
    (palmSplitKernel q (!first) ∘ₘ ρ).real
      {palmSplitTarget first k s t} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q (!first) z
      {palmSplitTarget first k s t} = 0 from
    fun z => palmSplitMeasure_wrong_target q first z k s t]
  simp

private theorem palmSplit_bind_both_positive
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k l s t : ℕ) :
    (palmSplitKernel q first ∘ₘ ρ).real {((k + 1, l + 1), (s, t))} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q first z {((k + 1, l + 1), (s, t))} = 0 from
    fun z => palmSplitMeasure_both_positive q first z k l s t]
  simp

private theorem palmSplit_bind_no_labeled_eq
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

private theorem prod_real_singleton
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

private theorem poisson_palm
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

private theorem markedPoissonLaw_real_target_sub
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

private theorem palmSplit_aggregatePoissonLaw_real_target
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

private theorem node_mem_support
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (i : ι) (hi : C.weight i ≠ 0) :
    C.node i ∈ Set.Icc (a / κ) B := by
  classical
  rw [variation_eq_absoluteMeasure, absoluteMeasure,
    ae_finsetSum_measure_iff] at hsupp
  have h := hsupp i (Finset.mem_univ i)
  have hc : ENNReal.ofReal |C.weight i| ≠ 0 := by simp [hi]
  rw [Measure.ae_ennreal_smul_measure_iff hc, ae_dirac_iff] at h
  · exact h
  · exact measurableSet_Icc

private theorem polarSign_node
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) (i : ι) :
    C.polarSign (C.node i) = Real.sign (C.weight i) := by
  classical
  unfold polarSign
  rw [Finset.sum_eq_single i]
  · simp
  · intro k hk hki
    have hne : C.node i ≠ C.node k := C.node_injective.ne hki.symm
    simp [hne]
  · simp

private theorem zeroInflated_integral_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (f g : ℝ → ℝ) (hf : Integrable f (C.zeroInflatedPrior a))
    (hg : Integrable g (C.zeroInflatedPrior a)) (h0 : f 0 = g 0) :
    (∫ p, f p ∂C.zeroInflatedPrior a) - ∫ p, g p ∂C.zeroInflatedPrior a =
      ∑ i, |C.weight i| * (a / (C.node i + a)) *
        (f (C.node i) - g (C.node i)) := by
  classical
  let dμ := C.signedMeasure.variation.withDensity
      (fun p => ENNReal.ofReal (a / (p + a)))
  let r := ENNReal.ofReal
      (1 - ∫ p, a / (p + a) ∂C.signedMeasure.variation)
  have hzero : C.zeroInflatedPrior a = dμ + r • Measure.dirac 0 := rfl
  have hfd : Integrable f dμ := by
    apply hf.mono_measure
    rw [hzero]
    exact Measure.le_add_right le_rfl
  have hfr : Integrable f (r • Measure.dirac 0) := by
    apply hf.mono_measure
    rw [hzero]
    exact Measure.le_add_left le_rfl
  have hgd : Integrable g dμ := by
    apply hg.mono_measure
    rw [hzero]
    exact Measure.le_add_right le_rfl
  have hgr : Integrable g (r • Measure.dirac 0) := by
    apply hg.mono_measure
    rw [hzero]
    exact Measure.le_add_left le_rfl
  rw [hzero, integral_add_measure hfd hfr, integral_add_measure hgd hgr]
  have hr : (∫ p, f p ∂r • Measure.dirac 0) =
      ∫ p, g p ∂r • Measure.dirac 0 := by
    simp [h0]
  rw [hr]
  simp only [add_sub_add_right_eq_sub]
  dsimp [dμ]
  rw [integral_withDensity_eq_integral_toReal_smul
      (μ := C.signedMeasure.variation)
      (by fun_prop : Measurable (fun p : ℝ => ENNReal.ofReal (a / (p + a))))
      (Filter.Eventually.of_forall fun _ => by finiteness) f,
    integral_withDensity_eq_integral_toReal_smul
      (μ := C.signedMeasure.variation)
      (by fun_prop : Measurable (fun p : ℝ => ENNReal.ofReal (a / (p + a))))
      (Filter.Eventually.of_forall fun _ => by finiteness) g,
    variation_eq_absoluteMeasure, absoluteMeasure,
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by rw [smul_eq_mul, enorm_mul]; finiteness)).smul_measure (by simp)),
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by rw [smul_eq_mul, enorm_mul]; finiteness)).smul_measure (by simp))]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hw : C.weight i = 0
  · simp [hw]
  · have hnode := node_mem_support C a κ B hsupp i hw
    have hp : 0 < C.node i :=
      lt_of_lt_of_le (div_pos ha hκ) hnode.1
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring

private theorem polarSign_zero
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (a κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    C.polarSign 0 = 0 := by
  classical
  unfold polarSign
  apply Finset.sum_eq_zero
  intro i hi
  split_ifs with hnode
  · by_cases hw : C.weight i = 0
    · simp [hw]
    · have hs := node_mem_support C a κ B hsupp i hw
      have hp : 0 < C.node i :=
        lt_of_lt_of_le (div_pos ha hκ) hs.1
      linarith
  · rfl

private theorem markedPredictive_real_singleton_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (z : MarkedPoissonObservation) :
    (C.markedPoissonPredictive ε a u v false).real {z} -
        (C.markedPoissonPredictive ε a u v true).real {z} =
      ∑ i, |C.weight i| * (a / (C.node i + a)) *
        ((markedPoissonLaw ε a u v C.polarSign false (C.node i)).real {z} -
          (markedPoissonLaw ε a u v C.polarSign true (C.node i)).real {z}) := by
  let _ : IsProbabilityMeasure (C.zeroInflatedPrior a) :=
    C.zeroInflatedPrior_isProbabilityMeasure a κ B ha hκ hsupp
  have hreal (branch : Bool) :
      (C.markedPoissonPredictive ε a u v branch).real {z} =
        ∫ p, (markedPoissonLaw ε a u v C.polarSign branch p).real {z}
          ∂C.zeroInflatedPrior a := by
    rw [measureReal_def, markedPoissonPredictive,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z)]
    have htop : ∀ᵐ p ∂C.zeroInflatedPrior a,
        markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch p {z} < ∞ := by
      filter_upwards with p
      rw [markedPoissonKernel_apply]
      exact measure_lt_top _ _
    rw [← integral_toReal
      (Kernel.measurable_coe
        (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign branch)
        (measurableSet_singleton z)).aemeasurable htop]
    apply integral_congr_ae
    filter_upwards with p
    rw [markedPoissonKernel_apply, measureReal_def]
  rw [hreal false, hreal true]
  apply zeroInflated_integral_sub C a κ B ha hκ hsupp
  · apply Integrable.of_bound
      (by
        simpa only [markedPoissonKernel_apply, measureReal_def] using
          (Kernel.measurable_coe
            (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign false)
            (measurableSet_singleton z)).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards with p
    have hle := ENNReal.toReal_mono
      (measure_ne_top (markedPoissonLaw ε a u v C.polarSign false p) _)
      (measure_mono (Set.subset_univ {z}))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, measureReal_def]
    simpa using hle
  · apply Integrable.of_bound
      (by
        simpa only [markedPoissonKernel_apply, measureReal_def] using
          (Kernel.measurable_coe
            (markedPoissonKernel ε a u v C.polarSign C.measurable_polarSign true)
            (measurableSet_singleton z)).ennreal_toReal.aestronglyMeasurable) 1
    filter_upwards with p
    have hle := ENNReal.toReal_mono
      (measure_ne_top (markedPoissonLaw ε a u v C.polarSign true p) _)
      (measure_mono (Set.subset_univ {z}))
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, measureReal_def]
    simpa using hle
  · have hzero := polarSign_zero C a κ B ha hκ hsupp
    simp [markedPoissonLaw, branchMark, hzero]

private theorem markedPredictive_real_both_positive_sub_eq_zero
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v κ B : ℝ) (ha : 0 < a) (hκ : 0 < κ)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (k l s t : ℕ) :
    (C.markedPoissonPredictive ε a u v false).real
        {((k + 1, l + 1), (s, t))} -
      (C.markedPoissonPredictive ε a u v true).real
        {((k + 1, l + 1), (s, t))} = 0 := by
  rw [markedPredictive_real_singleton_sub C ε a u v κ B ha hκ hsupp]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hw : C.weight i = 0
  · simp [hw]
  · have hsign : Real.sign (C.weight i) = 1 ∨
        Real.sign (C.weight i) = -1 :=
      (Real.sign_apply_eq_of_ne_zero _ hw).symm
    have hlaw (branch : Bool) :
        markedPoissonLaw ε a u v C.polarSign branch (C.node i) =
          markedPoissonLaw ε a u v
            (fun _ => Real.sign (C.weight i)) branch (C.node i) := by
      unfold markedPoissonLaw
      rw [polarSign_node]
    rw [hlaw false, hlaw true]
    rcases hsign with hs | hs <;> rw [hs] <;>
      simp [markedPoissonLaw, branchMark, prod_real_singleton,
        poissonMeasure_real_singleton, zero_pow (by omega : k + 1 ≠ 0),
        zero_pow (by omega : l + 1 ≠ 0)]

private theorem max_sub_max_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total x 0 with hx | hx
  · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
  · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

private theorem jordan_integral_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L) (f : ℝ → ℝ) :
    (∫ p, f p ∂C.positivePrior) - ∫ p, f p ∂C.negativePrior =
      2 * ∑ i, C.weight i * f (C.node i) := by
  classical
  rw [positivePrior, negativePrior,
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top),
    integral_finsetSum_measure (fun _ _ =>
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ i, 2 * (C.weight i * f (C.node i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [ENNReal.toReal_ofReal
          (mul_nonneg (by norm_num) (le_max_right _ _)),
        ENNReal.toReal_ofReal
          (mul_nonneg (by norm_num) (le_max_right _ _)),
        ← sub_mul, ← mul_sub, max_sub_max_neg]
      ring
    _ = _ := by rw [Finset.mul_sum]

private noncomputable instance aggregatePoissonKernel_isMarkovKernel
    (ε a t : ℝ) : IsMarkovKernel (aggregatePoissonKernel ε a t) where
  isProbabilityMeasure p := by
    rw [aggregatePoissonKernel_apply]
    infer_instance

private theorem priorPredictive_real_singleton_sub_jordan
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (K : Kernel ℝ X) [IsMarkovKernel K] (z : X) :
    (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive C.positivePrior K).real {z} -
        (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive C.negativePrior K).real {z} =
      2 * ∑ i, C.weight i * (K (C.node i)).real {z} := by
  have hreal (π : Measure ℝ) [IsProbabilityMeasure π] :
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π K).real {z} =
        ∫ p, (K p).real {z} ∂π := by
    rw [measureReal_def,
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
        (measurableSet_singleton z)]
    have htop : ∀ᵐ p ∂π, K p {z} < ∞ := by
      filter_upwards with p
      exact measure_lt_top _ _
    rw [← integral_toReal
      (K.measurable_coe (measurableSet_singleton z)).aemeasurable htop]
    rfl
  rw [hreal C.positivePrior, hreal C.negativePrior]
  exact jordan_integral_sub C (fun p => (K p).real {z})

private theorem palmSplit_aggregatePredictive_real_target_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε a u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (first : Bool) (k s t : ℕ) :
    (palmSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) first ∘ₘ
      aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
        {palmSplitTarget first k s t} -
      (palmSplitKernel
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval) first ∘ₘ
        aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
          {palmSplitTarget first k s t} =
      2 * ∑ i, C.weight i *
        (palmSplitKernel
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval) first ∘ₘ
          aggregatePoissonLaw ε a (u + v) (C.node i)).real
            {palmSplitTarget first k s t} := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  have hcomp (π : Measure ℝ) :
      palmSplitKernel q first ∘ₘ aggregatePoissonPredictive π ε a (u + v) =
        Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive π
          (palmSplitKernel q first ∘ₖ aggregatePoissonKernel ε a (u + v)) := by
    unfold aggregatePoissonPredictive
      Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive
    rw [Measure.bind_bind (Kernel.aemeasurable _) (Kernel.aemeasurable _)]
    rfl
  change
    (palmSplitKernel q first ∘ₘ
        aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
          {palmSplitTarget first k s t} -
      (palmSplitKernel q first ∘ₘ
        aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
          {palmSplitTarget first k s t} =
      2 * ∑ i, C.weight i *
        (palmSplitKernel q first ∘ₘ
          aggregatePoissonLaw ε a (u + v) (C.node i)).real
            {palmSplitTarget first k s t}
  rw [hcomp C.positivePrior, hcomp C.negativePrior,
    priorPredictive_real_singleton_sub_jordan]
  apply congrArg (fun x : ℝ => 2 * x)
  apply Finset.sum_congr rfl
  intro i hi
  rw [Kernel.comp_apply, aggregatePoissonKernel_apply]

private theorem abs_mul_sign (x : ℝ) : |x| * Real.sign x = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    ring
  · simp
  · rw [abs_of_pos hx, Real.sign_of_pos hx, mul_one]

private theorem markedPredictive_real_target_sub
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε κ a B u v : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκeq : κ = (1 - 2 * ε) / ε)
    (ha : 0 < a) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B)
    (first : Bool) (k s t : ℕ) :
    (C.markedPoissonPredictive ε a u v false).real
        {palmSplitTarget first k s t} -
      (C.markedPoissonPredictive ε a u v true).real
        {palmSplitTarget first k s t} =
      (if first then (-1 : ℝ) else 1) * (u * ε * a / 2) *
        ((palmSplitKernel
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval) first ∘ₘ
          aggregatePoissonPredictive C.positivePrior ε a (u + v)).real
            {palmSplitTarget first k s t} -
          (palmSplitKernel
              (⟨u / (u + v), by
                constructor
                · positivity
                · rw [div_le_one ht]
                  linarith⟩ : unitInterval) first ∘ₘ
            aggregatePoissonPredictive C.negativePrior ε a (u + v)).real
              {palmSplitTarget first k s t}) := by
  have hκpos : 0 < κ := by
    rw [hκeq]
    apply div_pos
    · nlinarith
    · exact hε
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  rw [markedPredictive_real_singleton_sub C ε a u v κ B ha hκpos hsupp,
    palmSplit_aggregatePredictive_real_target_sub C ε a u v hu hv ht]
  calc
    _ = ∑ i, (if first then (-1 : ℝ) else 1) * (u * ε * a) *
        (C.weight i *
          (palmSplitKernel q first ∘ₘ
            aggregatePoissonLaw ε a (u + v) (C.node i)).real
              {palmSplitTarget first k s t}) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hw : C.weight i = 0
      · simp [hw]
      · have hnode := node_mem_support C a κ B hsupp i hw
        have hp : 0 < C.node i :=
          lt_of_lt_of_le (div_pos ha hκpos) hnode.1
        have hpa : 0 < C.node i + a := add_pos hp ha
        have hr : 0 ≤ ε * (C.node i + a) := by positivity
        have hrate : 0 ≤ u * (ε * (C.node i + a)) := mul_nonneg hu hr
        have ha_le : a ≤ κ * C.node i := by
          simpa [mul_comm] using (div_le_iff₀ hκpos).mp hnode.1
        have hκε : κ * ε = 1 - 2 * ε := by
          rw [hκeq]
          field_simp
        have hc : 0 ≤ controlMass ε a (C.node i) := by
          simp [controlMass, treatedMass]
          nlinarith [mul_nonneg hε.le hp.le]
        have hsign : Real.sign (C.weight i) = 1 ∨
            Real.sign (C.weight i) = -1 :=
          (Real.sign_apply_eq_of_ne_zero _ hw).symm
        have hlaw (branch : Bool) :
            markedPoissonLaw ε a u v C.polarSign branch (C.node i) =
              markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) branch (C.node i) := by
          unfold markedPoissonLaw
          rw [polarSign_node]
        rw [hlaw false, hlaw true]
        change |C.weight i| * (a / (C.node i + a)) *
            ((markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) false (C.node i)).real
                  {palmSplitTarget first k s t} -
              (markedPoissonLaw ε a u v
                (fun _ => Real.sign (C.weight i)) true (C.node i)).real
                  {palmSplitTarget first k s t}) = _
        rw [markedPoissonLaw_real_target_sub ε a u v (C.node i)
          (Real.sign (C.weight i)) hsign first k s t,
          palmSplit_aggregatePoissonLaw_real_target
            ε a u v (C.node i) hu hv ht hr hc first k s t]
        calc
          _ = |C.weight i| *
              (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) *
              ((a / (C.node i + a)) *
                (poissonMeasure (Real.toNNReal
                  (u * (ε * (C.node i + a))))).real {k + 1}) *
              (poissonMeasure (Real.toNNReal
                (v * (ε * (C.node i + a))))).real {s} *
              (poissonMeasure (Real.toNNReal
                ((u + v) * controlMass ε a (C.node i)))).real {t} := by ring
          _ = |C.weight i| *
              (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) *
              ((u * ε * a / (k + 1)) *
                (poissonMeasure (Real.toNNReal
                  (u * (ε * (C.node i + a))))).real {k}) *
              (poissonMeasure (Real.toNNReal
                (v * (ε * (C.node i + a))))).real {s} *
              (poissonMeasure (Real.toNNReal
                ((u + v) * controlMass ε a (C.node i)))).real {t} := by
            rw [poisson_palm ε a u (C.node i) hrate hpa k]
          _ = _ := by
            rw [show |C.weight i| *
                (if first then -Real.sign (C.weight i) else Real.sign (C.weight i)) =
                (if first then (-1 : ℝ) else 1) * C.weight i by
              cases first <;> simp [abs_mul_sign]]
            ring
    _ = _ := by
      dsimp [q]
      rw [← Finset.mul_sum]
      ring

/-- The [stated conclusion](goal) follows from [the finite node index set](hyp:ι), [the moment-matching degree](hyp:L), [the finite signed certificate](hyp:C), [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [the positive shift](hyp:a), [the support upper bound](hyp:B), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ), [positive shift](hyp:ha), [positive upper bound](hyp:hB), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [positive total intensity](hyp:ht), [the compact-support condition](hyp:hsupp).  The marked-law discrepancy is at most the labeled Palm intensity
`u * ε * a` times the discrepancy between aggregate treated/control mixtures
of the two Jordan priors.  The result includes `u = 0` and `v = 0`; only the
total intensity must be positive. -/
theorem tvDist_markedPoissonPredictive_le_palm_aggregate
    {ι : Type*} [Fintype ι] {L : ℕ}
    (C : NormalizedFiniteSignedMomentCertificate ι L)
    (ε κ a B u v : ℝ)
    (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε)
    (ha : 0 < a) (hB : 0 < B)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hsupp : ∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) :
    Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤
      u * ε * a *
        Causalean.Stat.tvDist
          (aggregatePoissonPredictive C.positivePrior ε a (u + v))
          (aggregatePoissonPredictive C.negativePrior ε a (u + v)) := by
  have hκpos : 0 < κ := by
    rw [hκ]
    apply div_pos
    · nlinarith
    · exact hε
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  let P := aggregatePoissonPredictive C.positivePrior ε a (u + v)
  let N := aggregatePoissonPredictive C.negativePrior ε a (u + v)
  let Kf := palmSplitKernel q true
  let Ks := palmSplitKernel q false
  let Mf := C.markedPoissonPredictive ε a u v false
  let Mt := C.markedPoissonPredictive ε a u v true
  let d : ℝ≥0∞ := ENNReal.ofReal (u * ε * a / 2)
  let _ : IsProbabilityMeasure P :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      C.positivePrior (aggregatePoissonKernel ε a (u + v))
      (fun p => by rw [aggregatePoissonKernel_apply]; infer_instance)
  let _ : IsProbabilityMeasure N :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      C.negativePrior (aggregatePoissonKernel ε a (u + v))
      (fun p => by rw [aggregatePoissonKernel_apply]; infer_instance)
  let _ : IsProbabilityMeasure Mf :=
    C.markedPoissonPredictive_isProbabilityMeasure
      ε a u v κ B false ha hκpos hsupp
  let _ : IsProbabilityMeasure Mt :=
    C.markedPoissonPredictive_isProbabilityMeasure
      ε a u v κ B true ha hκpos hsupp
  have hc : 0 ≤ u * ε * a := by positivity
  have hd : d.toReal = u * ε * a / 2 := by
    change (ENNReal.ofReal (u * ε * a / 2)).toReal = _
    rw [ENNReal.toReal_ofReal]
    positivity
  let _ : IsFiniteMeasure (d • ((Kf ∘ₘ P) + (Ks ∘ₘ N))) :=
    Measure.smul_finite _ (by simp [d])
  let _ : IsFiniteMeasure (d • ((Kf ∘ₘ N) + (Ks ∘ₘ P))) :=
    Measure.smul_finite _ (by simp [d])
  let _ : IsFiniteMeasure
      (Mf + d • ((Kf ∘ₘ P) + (Ks ∘ₘ N))) := by infer_instance
  let _ : IsFiniteMeasure
      (Mt + d • ((Kf ∘ₘ N) + (Ks ∘ₘ P))) := by infer_instance
  have hbalance :
      Mf + d • ((Kf ∘ₘ P) + (Ks ∘ₘ N)) =
        Mt + d • ((Kf ∘ₘ N) + (Ks ∘ₘ P)) := by
    apply Measure.ext_of_measureReal_singleton
    rintro ⟨⟨x, y⟩, ⟨s, t⟩⟩
    rw [measureReal_add_ennreal_smul_add Mf (Kf ∘ₘ P) (Ks ∘ₘ N)
        d (by simp [d]),
      measureReal_add_ennreal_smul_add Mt (Kf ∘ₘ N) (Ks ∘ₘ P)
        d (by simp [d])]
    rcases x with _ | k
    · rcases y with _ | l
      · have hm : Mf.real {((0, 0), (s, t))} =
            Mt.real {((0, 0), (s, t))} := by
          have hr := congrArg (fun μ : Measure MarkedPoissonObservation =>
              μ.real {((0, 0), (s, t))})
            (C.restrict_markedPoissonPredictive_noLabeledTreated_eq
              ε a u v κ B ha hκpos hsupp)
          simpa [Mf, Mt, Measure.restrict_apply,
            noLabeledTreated] using hr
        have hp := palmSplit_bind_no_labeled_eq q P s t
        have hn := palmSplit_bind_no_labeled_eq q N s t
        change Mf.real {((0, 0), (s, t))} +
            d.toReal * ((Kf ∘ₘ P).real {((0, 0), (s, t))} +
              (Ks ∘ₘ N).real {((0, 0), (s, t))}) =
          Mt.real {((0, 0), (s, t))} +
            d.toReal * ((Kf ∘ₘ N).real {((0, 0), (s, t))} +
              (Ks ∘ₘ P).real {((0, 0), (s, t))})
        change (palmSplitKernel q false ∘ₘ P).real {((0, 0), (s, t))} =
            (palmSplitKernel q true ∘ₘ P).real {((0, 0), (s, t))} at hp
        change (palmSplitKernel q false ∘ₘ N).real {((0, 0), (s, t))} =
            (palmSplitKernel q true ∘ₘ N).real {((0, 0), (s, t))} at hn
        rw [hm, ← hp, ← hn]
        ring
      · have hm := markedPredictive_real_target_sub C ε κ a B u v
            hε hεhalf hκ ha hu hv ht hsupp false l s t
        have hPf := palmSplit_bind_wrong_target q false P l s t
        have hNf := palmSplit_bind_wrong_target q false N l s t
        change Mf.real {palmSplitTarget false l s t} +
            d.toReal * ((Kf ∘ₘ P).real {palmSplitTarget false l s t} +
              (Ks ∘ₘ N).real {palmSplitTarget false l s t}) =
          Mt.real {palmSplitTarget false l s t} +
            d.toReal * ((Kf ∘ₘ N).real {palmSplitTarget false l s t} +
              (Ks ∘ₘ P).real {palmSplitTarget false l s t})
        change Mf.real {palmSplitTarget false l s t} -
            Mt.real {palmSplitTarget false l s t} = _ at hm
        have hm' : Mf.real {palmSplitTarget false l s t} -
              Mt.real {palmSplitTarget false l s t} =
            (u * ε * a / 2) *
              ((Ks ∘ₘ P).real {palmSplitTarget false l s t} -
                (Ks ∘ₘ N).real {palmSplitTarget false l s t}) := by
          simpa [q, P, N, Ks, Mf, Mt] using hm
        change (Kf ∘ₘ P).real {palmSplitTarget false l s t} = 0 at hPf
        change (Kf ∘ₘ N).real {palmSplitTarget false l s t} = 0 at hNf
        rw [hPf, hNf, hd]
        nlinarith [hm']
    · rcases y with _ | l
      · have hm := markedPredictive_real_target_sub C ε κ a B u v
            hε hεhalf hκ ha hu hv ht hsupp true k s t
        have hPs := palmSplit_bind_wrong_target q true P k s t
        have hNs := palmSplit_bind_wrong_target q true N k s t
        change Mf.real {palmSplitTarget true k s t} +
            d.toReal * ((Kf ∘ₘ P).real {palmSplitTarget true k s t} +
              (Ks ∘ₘ N).real {palmSplitTarget true k s t}) =
          Mt.real {palmSplitTarget true k s t} +
            d.toReal * ((Kf ∘ₘ N).real {palmSplitTarget true k s t} +
              (Ks ∘ₘ P).real {palmSplitTarget true k s t})
        change Mf.real {palmSplitTarget true k s t} -
            Mt.real {palmSplitTarget true k s t} = _ at hm
        have hm' : Mf.real {palmSplitTarget true k s t} -
              Mt.real {palmSplitTarget true k s t} =
            -(u * ε * a / 2) *
              ((Kf ∘ₘ P).real {palmSplitTarget true k s t} -
                (Kf ∘ₘ N).real {palmSplitTarget true k s t}) := by
          simpa [q, P, N, Kf, Mf, Mt] using hm
        change (Ks ∘ₘ P).real {palmSplitTarget true k s t} = 0 at hPs
        change (Ks ∘ₘ N).real {palmSplitTarget true k s t} = 0 at hNs
        rw [hPs, hNs, hd]
        nlinarith [hm']
      · have hm := markedPredictive_real_both_positive_sub_eq_zero
            C ε a u v κ B ha hκpos hsupp k l s t
        have hPf := palmSplit_bind_both_positive q true P k l s t
        have hNf := palmSplit_bind_both_positive q true N k l s t
        have hPs := palmSplit_bind_both_positive q false P k l s t
        have hNs := palmSplit_bind_both_positive q false N k l s t
        change Mf.real {((k + 1, l + 1), (s, t))} +
            d.toReal * ((Kf ∘ₘ P).real {((k + 1, l + 1), (s, t))} +
              (Ks ∘ₘ N).real {((k + 1, l + 1), (s, t))}) =
          Mt.real {((k + 1, l + 1), (s, t))} +
            d.toReal * ((Kf ∘ₘ N).real {((k + 1, l + 1), (s, t))} +
              (Ks ∘ₘ P).real {((k + 1, l + 1), (s, t))})
        change Mf.real {((k + 1, l + 1), (s, t))} -
            Mt.real {((k + 1, l + 1), (s, t))} = 0 at hm
        change (Kf ∘ₘ P).real {((k + 1, l + 1), (s, t))} = 0 at hPf
        change (Kf ∘ₘ N).real {((k + 1, l + 1), (s, t))} = 0 at hNf
        change (Ks ∘ₘ P).real {((k + 1, l + 1), (s, t))} = 0 at hPs
        change (Ks ∘ₘ N).real {((k + 1, l + 1), (s, t))} = 0 at hNs
        rw [hPf, hNf, hPs, hNs]
        linarith
  change Causalean.Stat.tvDist Mf Mt ≤
    u * ε * a * Causalean.Stat.tvDist P N
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hb := congrArg (fun μ : Measure MarkedPoissonObservation => μ.real A) hbalance
  rw [measureReal_add_ennreal_smul_add Mf (Kf ∘ₘ P) (Ks ∘ₘ N)
      d (by simp [d]),
    measureReal_add_ennreal_smul_add Mt (Kf ∘ₘ N) (Ks ∘ₘ P)
      d (by simp [d])] at hb
  have hf : |(Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A| ≤
      Causalean.Stat.tvDist P N :=
    (Causalean.Stat.abs_measureReal_sub_le_tvDist hA).trans
      (tvDist_bind_le P N Kf)
  have hs : |(Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A| ≤
      Causalean.Stat.tvDist P N :=
    (Causalean.Stat.abs_measureReal_sub_le_tvDist hA).trans
      (tvDist_bind_le P N Ks)
  have hdnonneg : 0 ≤ d.toReal := ENNReal.toReal_nonneg
  rw [hd] at hb hdnonneg
  calc
    |Mf.real A - Mt.real A| =
        (u * ε * a / 2) *
          |((Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A) -
            ((Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A)| := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ u * ε * a / 2), ← abs_mul]
      congr 1
      linarith
    _ ≤ (u * ε * a / 2) *
          (|(Ks ∘ₘ P).real A - (Ks ∘ₘ N).real A| +
            |(Kf ∘ₘ P).real A - (Kf ∘ₘ N).real A|) := by
      gcongr
      exact abs_sub _ _
    _ ≤ u * ε * a * Causalean.Stat.tvDist P N := by
      nlinarith

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the support ratio](hyp:κ), [positive overlap fraction](hyp:hε), [the overlap upper bound](hyp:hεhalf), [the support-ratio identity](hyp:hκ).  For fixed overlap and support-ratio parameters there are positive
constants `b,C₀` and a geometric factor `ρ < 1` such that moment matching
through `L` bounds one-coordinate marked-Poisson TV by
`C₀ * u * a * ρ^L` whenever `(u+v)B ≤ bL`.  The statement includes the edge
cases `u = 0` and `v = 0` as long as total intensity is positive. -/
theorem exists_geometric_markedPoisson_tv_bound
    (ε κ : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hκ : κ = (1 - 2 * ε) / ε) :
    ∃ b C₀ ρ : ℝ, 0 < b ∧ 0 < C₀ ∧ ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ {ι : Type*} [Fintype ι] {L : ℕ}
        (C : NormalizedFiniteSignedMomentCertificate ι L)
        (a B u v : ℝ),
        0 < a → 0 < B → 0 ≤ u → 0 ≤ v → 0 < u + v →
        (∀ᵐ p ∂C.signedMeasure.variation, p ∈ Set.Icc (a / κ) B) →
        (u + v) * B ≤ b * L →
        Causalean.Stat.tvDist
            (C.markedPoissonPredictive ε a u v false)
            (C.markedPoissonPredictive ε a u v true) ≤
          C₀ * u * a * ρ ^ L := by
  rcases exists_geometric_aggregatePoisson_jordan_tv_bound ε κ hε hεhalf hκ with
    ⟨b, D, ρ, hb, hD, hρ, hagg⟩
  refine ⟨b, ε * D, ρ, hb, mul_pos hε hD, hρ, ?_⟩
  intro ι _ L C a B u v ha hB hu hv ht hsupp hband
  calc
    Causalean.Stat.tvDist
        (C.markedPoissonPredictive ε a u v false)
        (C.markedPoissonPredictive ε a u v true) ≤
        u * ε * a * Causalean.Stat.tvDist
          (aggregatePoissonPredictive C.positivePrior ε a (u + v))
          (aggregatePoissonPredictive C.negativePrior ε a (u + v)) :=
      C.tvDist_markedPoissonPredictive_le_palm_aggregate
        ε κ a B u v hε hεhalf hκ ha hB hu hv ht hsupp
    _ ≤ u * ε * a * (D * ρ ^ L) := by
      gcongr
      exact hagg C a B (u + v) ha hB ht hsupp hband
    _ = (ε * D) * u * a * ρ ^ L := by ring

end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
