import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.ZeroInflated
import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.AggregatePoisson.Jordan
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


end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
