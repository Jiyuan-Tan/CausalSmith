import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Sampling
import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.InformationDistance
import Mathlib.Analysis.MeanInequalities
import Causalean.Stat.Minimax.TotalVariation

/-! # Impossibility under bounded classification information -/

open scoped ENNReal
open MeasureTheory

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

/-- A possibly abstaining rule on the actual observed sample array. -/
abbrev ClassificationRule (d E : ℕ) (n : Environment E → ℕ) :=
  ObservedSampleArray d E n → Option (Finset (Fin d) × Finset (Fin d))

/-- Measurability of every non-abstaining report event.  Since the report
space is finite, this is measurability for the generated discrete σ-algebra. -/
def IsMeasurableClassificationRule {d E : ℕ} {n : Environment E → ℕ}
    (rule : ClassificationRule d E n) : Prop :=
  ∀ q, MeasurableSet {x | rule x = some q}

/-- Event that a rule makes an incorrect non-abstaining report. -/
def ruleIncorrectEvent {d E : ℕ} {n : Environment E → ℕ}
    (θ : CovarianceTuple d E) (r : ℕ) (rule : ClassificationRule d E n) :
    Set (ObservedSampleArray d E n) :=
  {x | ∃ q, rule x = some q ∧ q ≠ completeClassification θ r}

/-- Event that a rule correctly certifies the focal classification. -/
def ruleCorrectEvent {d E : ℕ} {n : Environment E → ℕ}
    (θ : CovarianceTuple d E) (r : ℕ) (rule : ClassificationRule d E n) :
    Set (ObservedSampleArray d E n) :=
  {x | rule x = some (completeClassification θ r)}

-- @node: thm:impossibility-bounded-information
theorem impossibility_bounded_information (d E r : ℕ) (m M α C : ℝ)
    (hd : 2 ≤ d) (hE : 2 ≤ E) (hr0 : 1 ≤ r) (hrd : r < d)
    (hm : 0 < m) (hM : m < M)
    (hC : 0 ≤ C) -- @realizes Cbound(finite nonnegative information bound)
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ κ : ℝ, 0 < κ ∧
      ∀ (nSeq : ℕ → Environment E → ℕ)
        (P : (k : ℕ) → CovarianceTuple d E →
          Measure (ObservedSampleArray d E (nSeq k)))
        (rule : (k : ℕ) → ClassificationRule d E (nSeq k)),
        (∀ k e, 0 < nSeq k e) →
        (∀ k, IsMeasurableClassificationRule (rule k)) →
        (∀ k ζ, ζ ∈ ThetaK d E r m M →
          IndependentEnvironmentSamples (observedSampleExperiment (P k ζ)) ζ) →
        (∀ k ζ, ζ ∈ ThetaK d E r m M →
          P k ζ (ruleIncorrectEvent ζ r (rule k)) ≤ ENNReal.ofReal α) →
        ∀ θSeq : ℕ → CovarianceTuple d E,
          (∀ k, θSeq k ∈ ThetaK d E r m M) →
          (∀ k, classificationInformationDistance m M (nSeq k) (θSeq k) r ≤
            ENNReal.ofReal C) →
          ∀ k, P k (θSeq k) (ruleCorrectEvent (θSeq k) r (rule k)) ≤
            ENNReal.ofReal (1 - κ) := by
  sorry

end CausalSmith.ExactID.CovshiftProfilequotientTargets
