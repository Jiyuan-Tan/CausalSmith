import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotControl

/-! Exact marked-Poisson laws and conditional factorial moments used by pilot control. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory

-- @node: centeredFactorialPilotExperimentCore
/-- The uncapped marked experiment has the required Poisson total, joint cell-product
law, and coordinatewise conditional factorial-moment identities. This uses [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma centeredFactorialPilotExperimentCore
    {n d : ℕ} (P : DiscreteLaw d) (hn : 0 < n) :
    let m : ℝ := n / 8
    Measure.map Prod.fst (uncappedMarkedCountLaw n P) =
        ProbabilityTheory.poissonMeasure (Real.toNNReal ((n : ℝ) / 4)) ∧
    Measure.map Prod.snd (uncappedMarkedCountLaw n P) =
        pilotEvaluationTableLaw m P ∧
    (∀ x : Fin d, Measure.map (fun z => (z.1 x, z.2 x))
        (pilotEvaluationTableLaw m P) = pilotEvaluationLaw m (cellVector P x)) ∧
    ∀ (x : Fin d) (pilot : Cell → ℕ) (j : Cell) (z : ℝ) (h t : ℕ),
      conditionalEvaluationExpectation m (cellVector P x) pilot (fun eval =>
          centeredFactorial m h (eval j) z) =
        (cellVector P x j - z) ^ h ∧
      conditionalEvaluationExpectation m (cellVector P x) pilot (fun eval =>
          centeredFactorial m h (eval j) z * centeredFactorial m t (eval j) z) =
        ∑ l ∈ Finset.range (min h t + 1),
          (Nat.choose h l : ℝ) * Nat.choose t l * Nat.factorial l *
            (cellVector P x j / m) ^ l *
              (cellVector P x j - z) ^ (h + t - 2 * l) := by
  dsimp only
  have hm : (0 : ℝ) < n / 8 := div_pos (Nat.cast_pos.mpr hn) (by norm_num)
  refine ⟨uncappedMarkedCountLaw_count n P, uncappedMarkedCountLaw_table n P,
    fun x => pilotEvaluationTableLaw_cell (n / 8) P x, ?_⟩
  intro x pilot j z h t
  exact ⟨conditionalEvaluationExpectation_centeredFactorial
      (n / 8) hm (cellVector P x) (fun _ => ENNReal.toReal_nonneg) pilot j z h,
    conditionalEvaluationExpectation_centeredFactorial_mul
      (n / 8) hm (cellVector P x) (fun _ => ENNReal.toReal_nonneg) pilot j z h t⟩

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
