import CausalSmith.Experimentation.EXP_SaturationExacthitDeficiencyDesign_Research.Basic
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Decision.Risk.Basic
import Mathlib.Probability.Distributions.Gaussian.Basic

set_option linter.style.openClassical false

/-!
# Finite-prior limit-experiment lower bound

This file contains the paper-owned finite-parameter lower-bound lemma used by
the two LAN theorems.  It is not a cited gate: its hypotheses explicitly record
joint likelihood-ratio convergence, uniform integrability, and uniform finite
loss convergence.
-/

open scoped BigOperators ENNReal
open Filter MeasureTheory

namespace CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign

noncomputable section
open Classical

/-- A randomized action-simplex rule on an arbitrary observation space. -/
def FiniteSimplexRule {Action Omega : Type*} [Fintype Action]
    [MeasurableSpace Omega] (delta : Omega → Action → ℝ) : Prop :=
  (∀ a, Measurable fun x => delta x a) ∧
    (∀ x a, 0 ≤ delta x a) ∧ ∀ x, ∑ a, delta x a = 1

/-- Risk of a finite-action randomized rule under one experiment law. -/
def finiteExperimentRuleRisk {Action Omega : Type*} [Fintype Action]
    [MeasurableSpace Omega] (law : Measure Omega) (delta : Omega → Action → ℝ)
    (loss : Action → ℝ) : ℝ :=
  ∫ x, ∑ a, delta x a * loss a ∂law

/-- Joint weak convergence of a statistic and every finite likelihood-ratio
coordinate, expressed as weak convergence of their mapped laws. -/
def JointStatisticLikelihoodConvergence {Theta : Type*} [Fintype Theta]
    [MeasurableSpace Theta] {Omega : ℕ → Type*}
    [∀ C, MeasurableSpace (Omega C)] (d : ℕ)
    (referenceLaw : ∀ C, Measure (Omega C))
    (statistic : ∀ C, Omega C → Fin d → ℝ)
    (likelihood : ∀ C, Theta → Omega C → ℝ)
    (limitReference : Measure (Fin d → ℝ))
    (limitLikelihood : Theta → (Fin d → ℝ) → ℝ) : Prop :=
  (∀ C, Measurable fun x => (statistic C x, fun theta => likelihood C theta x)) ∧
    (∀ theta, Measurable (limitLikelihood theta)) ∧
    ∀ test : ((Fin d → ℝ) × (Theta → ℝ)) → ℝ,
      Continuous test →
      (∃ bound : ℝ, 0 ≤ bound ∧ ∀ z, |test z| ≤ bound) →
      Tendsto
        (fun C => ∫ x, test (statistic C x, fun theta => likelihood C theta x)
          ∂(referenceLaw C)) atTop
        (nhds (∫ g, test (g, fun theta => limitLikelihood theta g) ∂limitReference))

/-- Uniform-integrability condition on every finite likelihood-ratio sequence. -/
def LikelihoodRatiosUniformlyIntegrable {Theta : Type*} [Fintype Theta]
    {Omega : ℕ → Type*} [∀ C, MeasurableSpace (Omega C)]
    (referenceLaw : ∀ C, Measure (Omega C))
    (likelihood : ∀ C, Theta → Omega C → ℝ) : Prop :=
  ∀ theta, Tendsto (fun R : ℕ => sSup {tail : ℝ | ∃ C : ℕ,
    tail = ∫ x in {x | (R : ℝ) < likelihood C theta x},
      likelihood C theta x ∂(referenceLaw C)}) atTop (nhds 0)

/-- Uniform convergence and a common finite bound for the finite loss tables. -/
def UniformFiniteLossConvergence {Theta Action : Type*}
    [Fintype Theta] [Fintype Action]
    (loss : ℕ → Theta → Action → ℝ) (limitLoss : Theta → Action → ℝ) : Prop :=
  (∀ theta action, Tendsto (fun C => loss C theta action) atTop
      (nhds (limitLoss theta action))) ∧
    (∃ bound : ℝ, 0 ≤ bound ∧ ∀ C theta action,
      0 ≤ loss C theta action ∧ loss C theta action ≤ bound) ∧
    ∀ theta action, 0 ≤ limitLoss theta action

/-- Bayes value of the finite-prior Gaussian-shift limit experiment. -/
def finitePriorLimitBayesValue {Theta Action : Type*}
    [Fintype Theta] [Fintype Action]
    (d : ℕ) (prior : Theta → ℝ) (limitLaw : Theta → Measure (Fin d → ℝ))
    (limitLoss : Theta → Action → ℝ) : ℝ :=
  sInf {risk : ℝ | ∃ delta : (Fin d → ℝ) → Action → ℝ,
    FiniteSimplexRule delta ∧
    risk = ∑ theta, prior theta *
      finiteExperimentRuleRisk (limitLaw theta) delta (limitLoss theta)}

-- @node: lem:lan-finite-prior-lower-bound
/-- Every rule sequence in a dominated finite-parameter experiment has liminf
Bayes risk, and hence liminf maximal risk, at least the Bayes value of its
Gaussian-shift limit experiment. -/
lemma lan_finite_prior_lower_bound {Theta Action : Type*}
    [Fintype Theta] [Nonempty Theta] [MeasurableSpace Theta]
    [Fintype Action] [Nonempty Action]
    {Omega : ℕ → Type*} [∀ C, MeasurableSpace (Omega C)]
    (d : ℕ) (hd : 1 ≤ d) (prior : Theta → ℝ)
    (referenceLaw : ∀ C, Measure (Omega C))
    (localLaw : ∀ C, Theta → Measure (Omega C))
    (likelihood : ∀ C, Theta → Omega C → ℝ)
    (statistic : ∀ C, Omega C → Fin d → ℝ)
    (limitReference : Measure (Fin d → ℝ))
    (limitLaw : Theta → Measure (Fin d → ℝ))
    (limitLikelihood : Theta → (Fin d → ℝ) → ℝ)
    (loss : ℕ → Theta → Action → ℝ) (limitLoss : Theta → Action → ℝ)
    (delta : ∀ C, Omega C → Action → ℝ)
    [ProbabilityTheory.IsGaussian limitReference]
    (hshift : ∃ shift : Theta → Fin d → ℝ, ∀ theta,
      limitLaw theta = Measure.map (fun g i => g i + shift theta i) limitReference)
    (hprior : (∀ theta, 0 ≤ prior theta) ∧ ∑ theta, prior theta = 1)
    (hprob : (∀ C, IsProbabilityMeasure (referenceLaw C)) ∧
      (∀ C theta, IsProbabilityMeasure (localLaw C theta)) ∧
      IsProbabilityMeasure limitReference ∧
      ∀ theta, IsProbabilityMeasure (limitLaw theta))
    (hdominated : ∀ C theta, localLaw C theta ≪ referenceLaw C)
    (hrn : (∀ C theta, Measurable (likelihood C theta)) ∧
      (∀ theta, Measurable (limitLikelihood theta)) ∧
      (∀ C theta, ∀ᵐ x ∂referenceLaw C,
        0 ≤ likelihood C theta x ∧
          likelihood C theta x =
            ((localLaw C theta).rnDeriv (referenceLaw C) x).toReal) ∧
      ∀ theta, ∀ᵐ g ∂limitReference,
        0 ≤ limitLikelihood theta g ∧
          limitLikelihood theta g =
            ((limitLaw theta).rnDeriv limitReference g).toReal)
    (hjoint : JointStatisticLikelihoodConvergence d referenceLaw statistic likelihood
      limitReference limitLikelihood)
    (hui : LikelihoodRatiosUniformlyIntegrable referenceLaw likelihood)
    (hloss : UniformFiniteLossConvergence loss limitLoss)
    (hrule : ∀ C, FiniteSimplexRule (delta C)) :
    finitePriorLimitBayesValue d prior limitLaw limitLoss ≤
      Filter.liminf (fun C => ∑ theta, prior theta *
        finiteExperimentRuleRisk (localLaw C theta) (delta C) (loss C theta)) atTop ∧
    finitePriorLimitBayesValue d prior limitLaw limitLoss ≤
      Filter.liminf (fun C => Finset.univ.sup' Finset.univ_nonempty fun theta =>
        finiteExperimentRuleRisk (localLaw C theta) (delta C) (loss C theta)) atTop := by
  sorry

end

end CausalSmith.Experimentation.SaturationExacthitDeficiencyDesign
