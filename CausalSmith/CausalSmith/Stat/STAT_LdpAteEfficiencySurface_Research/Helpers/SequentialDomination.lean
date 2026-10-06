module
public import CausalSmith.Stat.STAT_LdpAteEfficiencySurface_Research.Helpers.Procedures

/-! # Common domination of sequential transcript experiments

For a fixed procedure and sample size, summing the deterministic-input
transcript laws gives one finite reference measure. Every parameterized
transcript mixture is absolutely continuous with respect to this measure and
therefore has a Radon--Nikodym density on arbitrary measurable output spaces.
-/

@[expose] public section
noncomputable section

namespace CausalSmith.Stat.LdpAteEfficiencySurface

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- The sum of all deterministic-input transcript laws is a common reference
measure for the fixed procedure and sample size. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n), these specify the stated inputs. -/
def transcriptReferenceMeasure {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) : Measure (Transcript (Z n)) :=
  ∑ x : Fin n → Fin 4, P.transcript n x

/-- Every deterministic-input transcript law is dominated by the common
reference measure. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n,x), these specify the stated inputs. -/
-- @node: transcriptComponent_ac_reference
lemma transcriptComponent_ac_reference {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) (x : Fin n → Fin 4) :
    P.transcript n x ≪ transcriptReferenceMeasure P n := by
  apply Measure.AbsolutelyContinuous.mk
  intro A hA href
  simp only [transcriptReferenceMeasure, Measure.coe_finsetSum,
    Finset.sum_apply] at href
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ zero_le)).mp href x
    (Finset.mem_univ x)

/-- Every parameterized transcript law is dominated by the same reference
measure, without any countability assumption on the output sigma-fields. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,n), these specify the stated inputs. -/
-- @node: transcriptLaw_ac_reference
lemma transcriptLaw_ac_reference {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    transcriptLaw P θ p n ≪ transcriptReferenceMeasure P n := by
  unfold transcriptLaw
  apply Measure.AbsolutelyContinuous.mk
  intro A hA href
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_eq_zero_of_right _ (transcriptComponent_ac_reference P n x href)

/-- The reference measure has total mass equal to the number of deterministic
input paths. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,n), these specify the stated inputs. -/
-- @node: transcriptReferenceMeasure_apply_univ
lemma transcriptReferenceMeasure_apply_univ {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) :
    transcriptReferenceMeasure P n Set.univ = Fintype.card (Fin n → Fin 4) := by
  simp only [transcriptReferenceMeasure, Measure.coe_finsetSum,
    Finset.sum_apply]
  simp only [(P.factorizes n _).1.measure_univ, Finset.sum_const, nsmul_eq_mul,
    mul_one]
  norm_cast

/-- the [transcript reference measure is finite](goal) is the mathematical object specified below. For [the displayed quantities and conditions](hyp:P,n), these specify the stated inputs. -/
instance transcriptReferenceMeasure_isFinite {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (n : ℕ) :
    IsFiniteMeasure (transcriptReferenceMeasure P n) := by
  constructor
  rw [transcriptReferenceMeasure_apply_univ]
  exact ENNReal.natCast_lt_top _

/-- the transcript law is finite is the mathematical object specified below. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Law is Finite](goal) is determined by [the displayed parameters](hyp:P,θ,p,n). -/
instance transcriptLaw_isFinite {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    IsFiniteMeasure (transcriptLaw P θ p n) := by
  constructor
  simp only [transcriptLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, (P.factorizes n _).1.measure_univ, mul_one]
  exact ENNReal.sum_lt_top.mpr fun _ _ ↦ ENNReal.ofReal_lt_top

/-- The Radon--Nikodym density of a transcript law against its common finite reference measure. The stated result follows. For the displayed quantities and conditions, these specify the stated inputs. [The transcript Density](goal) is determined by [the displayed parameters](hyp:P,θ,p,n). -/
def transcriptDensity {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    Transcript (Z n) → ℝ≥0∞ :=
  (transcriptLaw P θ p n).rnDeriv (transcriptReferenceMeasure P n)

/-- Integrating the transcript density against the common reference measure
recovers the parameterized transcript law. [The stated result](goal) follows. For [the displayed quantities and conditions](hyp:P,p,n), these specify the stated inputs. -/
-- @node: transcriptLaw_eq_withDensity_reference
lemma transcriptLaw_eq_withDensity_reference {Z : OutputFamily}
    [∀ n i, MeasurableSpace (Z n i)] {ε : ℝ}
    (P : ProcedureSequence Z ε) (θ : TrialParameter) (p : ℝ) (n : ℕ) :
    (transcriptReferenceMeasure P n).withDensity
      (transcriptDensity P θ p n) = transcriptLaw P θ p n := by
  exact Measure.withDensity_rnDeriv_eq (transcriptLaw P θ p n)
    (transcriptReferenceMeasure P n) (transcriptLaw_ac_reference P θ p n)

end CausalSmith.Stat.LdpAteEfficiencySurface
