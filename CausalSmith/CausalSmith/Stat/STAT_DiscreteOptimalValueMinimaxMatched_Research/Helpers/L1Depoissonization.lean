import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.L1Embedding
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.CitedGates

/-!
# Fixed/Poisson transfer for the paired L1 experiment

This file specializes the reusable paired-histogram Rao--Blackwell theorem to
the two simplex laws used by the paper.
-/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators

open Causalean.Stat.FiniteRaoBlackwell.PairedPoissonHistogram

/-- [the L1 distance between two probability vectors lies between zero and two](goal). -/
lemma l1Distance_nonneg_le_two {d : ℕ} (P Q : ProbabilitySimplex d) :
    0 ≤ l1Distance P Q ∧ l1Distance P Q ≤ 2 := by
  constructor
  · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  · unfold l1Distance
    calc
      (∑ x : Fin d, |P.1 x - Q.1 x|) ≤
          ∑ x : Fin d, (P.1 x + Q.1 x) := by
        apply Finset.sum_le_sum
        intro x _hx
        calc
          |P.1 x - Q.1 x| ≤ |P.1 x| + |Q.1 x| := abs_sub _ _
          _ = P.1 x + Q.1 x := by
            rw [abs_of_nonneg (P.2.1 x), abs_of_nonneg (Q.2.1 x)]
      _ = 2 := by rw [Finset.sum_add_distrib, P.2.2, Q.2.2]; norm_num

/-- [the family of fixed-sample L1 risks is bounded above](goal). -/
lemma fixedL1Risk_bddAbove {n d : ℕ} (est : FixedL1Estimator n d) :
    BddAbove (Set.range (fixedL1Risk n est)) := by
  classical
  letI (PQ : ProbabilitySimplex d × ProbabilitySimplex d) :
      IsProbabilityMeasure (fixedPairLaw n PQ) := by
    unfold fixedPairLaw
    infer_instance
  let M : ℝ := ∑ z, |est.1 z|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hest (z : Fin n → Fin d × Fin d) : |est.1 z| ≤ M :=
    Finset.single_le_sum (fun w _hw => abs_nonneg (est.1 w)) (Finset.mem_univ z)
  refine ⟨(M + 2) ^ 2, ?_⟩
  rintro _ ⟨PQ, rfl⟩
  have htheta := l1Distance_nonneg_le_two PQ.1 PQ.2
  unfold fixedL1Risk Causalean.Stat.sqRisk
  have hi := norm_integral_le_of_norm_le_const
    (μ := fixedPairLaw n PQ)
    (f := fun z => (est.1 z - l1Distance PQ.1 PQ.2) ^ 2)
    (C := (M + 2) ^ 2) (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
        abs_of_nonneg (add_nonneg hM (by norm_num))]
      exact (abs_sub _ _).trans (add_le_add (hest z)
        (by rw [abs_of_nonneg htheta.1]; exact htheta.2)))
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hi)

/-- [the risk of the paired-histogram estimator in the Poisson experiment is no greater than its fixed-sample counterpart plus the stated tail](goal). -/
lemma poissonL1Risk_pairedHistogram_le {n d : ℕ}
    (est : FixedL1Estimator n d) (PQ : ProbabilitySimplex d × ProbabilitySimplex d) :
    poissonL1Risk n
        ⟨pairedPoissonHistogramEstimator est.1 0,
          measurable_pairedPoissonHistogramEstimator est.1 0⟩ PQ ≤
      fixedL1Risk n est PQ +
        8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
  have htheta := l1Distance_nonneg_le_two PQ.1 PQ.2
  have h := pairedPoissonHistogramRisk_two_n_exp_le
    (simplexPMF PQ.1).toMeasure (simplexPMF PQ.2).toMeasure est.1
      (l1Distance PQ.1 PQ.2) 2 (by
        rw [abs_of_nonneg htheta.1]
        exact htheta.2)
  unfold poissonL1Risk fixedL1Risk Causalean.Stat.sqRisk
  dsimp [poissonPairLaw, fixedPairLaw]
  convert h using 1 <;> ring

/-- [fixed-sample L1 minimax risk is at least the Poissonized risk minus the stated exponential tail](goal). -/
lemma fixedL1MinimaxRisk_ge_poisson_sub_expTail {n d : ℕ}
    (P0 Q0 : ProbabilitySimplex d) :
    poissonL1FiniteRiskMinimaxRisk n d -
        8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
      fixedL1MinimaxRisk n d := by
  classical
  letI : Nonempty (ProbabilitySimplex d × ProbabilitySimplex d) := ⟨(P0, Q0)⟩
  letI : Nonempty (FixedL1Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  unfold fixedL1MinimaxRisk
  apply Causalean.Stat.le_minimaxValue
  intro est
  let poisEst : FiniteRiskL1Estimator n d :=
    ⟨⟨pairedPoissonHistogramEstimator est.1 0,
        measurable_pairedPoissonHistogramEstimator est.1 0⟩, by
      constructor
      · intro PQ
        simpa [poissonPairLaw] using
          (pairedPoissonHistogramRisk_le_fixedRisk_add_tails
            (simplexPMF PQ.1).toMeasure (simplexPMF PQ.2).toMeasure
            (2 * n) (2 * n) est.1 0 (l1Distance PQ.1 PQ.2)).1
      · obtain ⟨M, hM⟩ := fixedL1Risk_bddAbove est
        refine ⟨M + 8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)), ?_⟩
        rintro _ ⟨PQ, rfl⟩
        exact (poissonL1Risk_pairedHistogram_le est PQ).trans
          (by
            simpa [add_comm] using
              (add_le_add_right (hM ⟨PQ, rfl⟩)
                (8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)))))⟩
  have hpmin : poissonL1FiniteRiskMinimaxRisk n d ≤
      Causalean.Stat.worstCaseRisk
        (fun est : FiniteRiskL1Estimator n d => poissonL1Risk n est.1) poisEst := by
    unfold poissonL1FiniteRiskMinimaxRisk
    exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (fun _ _ => by unfold poissonL1Risk Causalean.Stat.sqRisk; positivity) poisEst
  have hpwc : Causalean.Stat.worstCaseRisk
      (fun est : FiniteRiskL1Estimator n d => poissonL1Risk n est.1) poisEst ≤
      Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) est +
        8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
    apply Causalean.Stat.worstCaseRisk_le
    intro PQ
    calc
      poissonL1Risk n poisEst.1 PQ ≤ fixedL1Risk n est PQ +
          8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) :=
        poissonL1Risk_pairedHistogram_le est PQ
      _ ≤ Causalean.Stat.worstCaseRisk (fixedL1Risk (d := d) n) est +
          8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
        gcongr
        exact Causalean.Stat.le_worstCaseRisk (fixedL1Risk_bddAbove est) PQ
  linarith [hpmin.trans hpwc]

/-- If [the Jiao--Han--Weissman Poisson L1 lower bound is available](hyp:h_jhw), and [the stated c0 condition holds](hyp:hc0), and [the stated c0 condition holds](hyp:hC0), then [the stated jhw fixed l1 lower sub exp tail relation holds](goal). -/
lemma jhw_fixedL1_lower_sub_expTail (h_jhw : JhwPoissonL1Lower)
    (c0 C0 : ℝ) (hc0 : 0 < c0) (hC0 : 0 < C0) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ d n : ℕ, 2 ≤ d →
        c0 * d / Real.log (Real.exp 1 * d) ≤ n →
        Real.log (Real.exp 1 * n) ≤ C0 * Real.log (Real.exp 1 * d) →
        ∀ P0 Q0 : ProbabilitySimplex d,
          c1 * min 1 (d / (n * Real.log (Real.exp 1 * n))) -
              8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
            fixedL1MinimaxRisk n d := by
  obtain ⟨c1, hc1, hbound⟩ := h_jhw c0 C0 hc0 hC0
  refine ⟨c1, hc1, ?_⟩
  intro d n hd hn hlog P0 Q0
  exact (sub_le_sub_right (hbound d n hd hn hlog)
    (8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)))).trans
      (fixedL1MinimaxRisk_ge_poisson_sub_expTail P0 Q0)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
