import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmScheduleKernel
import Causalean.Stat.Minimax.FinitePosteriorBayesRisk

/-!
Finite-posterior bridge for the paper's effect-triple/binomial experiment.

This identifies the generic native-real finite-design Bayes risk with the
paper-local `scalarBayesRisk`; it is the finite endpoint needed by the smooth
continuous-prior converse.
-/

open scoped BigOperators

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

open Causalean.Experimentation.DesignBased

/-- The effect triple space carries the discrete measurable structure. -/
noncomputable local instance (n : ℕ) : MeasurableSpace (EffectTriple n) := ⊤
/-- [every singleton in the effect triple space is measurable](goal). -/
noncomputable local instance (n : ℕ) : MeasurableSingletonClass (EffectTriple n) :=
  ⟨fun _ => MeasurableSet.of_discrete⟩

-- @node: twoArmCountKernel
/-- The count-observation kernel associated with the canonical two-arm score experiment. -/
noncomputable def twoArmCountKernel {n : ℕ}
    (D : FiniteDesign (Assign 2 n)) :
    ProbabilityTheory.Kernel (EffectTriple n) (Fin (n + 1)) :=
  (twoArmScoreExperiment D).statisticKernel

/-- The two arm count kernel construction is a Markov kernel. -/
noncomputable instance twoArmCountKernel_isMarkovKernel {n : ℕ}
    (D : FiniteDesign (Assign 2 n)) :
    ProbabilityTheory.IsMarkovKernel (twoArmCountKernel D) := by
  unfold twoArmCountKernel
  infer_instance

-- @node: twoArmCountKernel_mass
/-- [Singleton masses of the count kernel are the statistic masses of the score experiment.](goal) -/
lemma twoArmCountKernel_mass {n : ℕ} (D : FiniteDesign (Assign 2 n))
    (theta : EffectTriple n) (x : Fin (n + 1)) :
    Causalean.Stat.kernelMass (twoArmCountKernel D) theta x =
      (twoArmScoreExperiment D).statisticMass theta x := by
  exact (twoArmScoreExperiment D).statisticKernel_singletonReal theta x

-- @node: twoArmCount_statewiseSquaredLoss_eq_statisticRisk
/-- [Generic statewise squared loss is exactly the paper-local count-statistic risk.](goal) -/
lemma twoArmCount_statewiseSquaredLoss_eq_statisticRisk {n : ℕ}
    (D : FiniteDesign (Assign 2 n)) (T : Fin (n + 1) → ℝ)
    (theta : EffectTriple n) :
    Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
        (fun theta _x => effectTarget theta) T theta =
      (twoArmScoreExperiment D).statisticRisk effectTarget T theta := by
  rw [twoArmScoreExperiment_statisticRisk_eq]
  unfold Causalean.Stat.statewiseSquaredLoss
  simp_rw [twoArmCountKernel_mass, twoArmScoreExperiment_statisticMass]

-- @node: twoArmCount_expectedLoss_eq_scalarPriorRisk_extend
/-- [Expected count-kernel loss agrees with scalar prior risk after extending a finite estimator.](goal) -/
lemma twoArmCount_expectedLoss_eq_scalarPriorRisk_extend {n : ℕ}
    (nu : EffectPrior n) (D : FiniteDesign (Assign 2 n))
    (T : Fin (n + 1) → ℝ) :
    nu.E (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
      (fun theta _x => effectTarget theta) T) =
      scalarPriorRisk nu (extendFinEstimator T) := by
  unfold FiniteDesign.E
  simp_rw [twoArmCount_statewiseSquaredLoss_eq_statisticRisk,
    twoArmScoreExperiment_statisticRisk_eq_scalar]
  unfold scalarPriorRisk
  rfl

-- @node: twoArmCount_expectedLoss_eq_scalarPriorRisk_restrict
/-- [Restricting an arbitrary natural-number estimator to the finite count support preserves risk.](goal) -/
lemma twoArmCount_expectedLoss_eq_scalarPriorRisk_restrict {n : ℕ}
    (nu : EffectPrior n) (D : FiniteDesign (Assign 2 n)) (f : ℕ → ℝ) :
    nu.E (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
      (fun theta _x => effectTarget theta) (fun x : Fin (n + 1) => f (x : ℕ))) =
      scalarPriorRisk nu f := by
  unfold FiniteDesign.E
  simp_rw [twoArmCount_statewiseSquaredLoss_eq_statisticRisk,
    twoArmScoreExperiment_statisticRisk_eq_scalar]
  unfold scalarPriorRisk
  apply Finset.sum_congr rfl
  intro theta _
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ (theta.1.2.2 : ℕ) := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hbound : (theta.1.1 : ℕ) + k < n + 1 := by
    have ht := theta.2
    omega
  rw [extendFinEstimator_of_lt _ hbound]

-- @node: finiteDesignBayesRisk_twoArmCount_eq_scalarBayesRisk
/-- [The generic finite-posterior Bayes risk of the effect-triple/count kernel is exactly the paper's scalar Bayes risk.](goal) -/
lemma finiteDesignBayesRisk_twoArmCount_eq_scalarBayesRisk {n : ℕ}
    (nu : EffectPrior n) (D : FiniteDesign (Assign 2 n)) :
    Causalean.Stat.finiteDesignBayesRisk nu
        (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
          (fun theta _x => effectTarget theta)) =
      scalarBayesRisk nu := by
  rw [scalarBayesRisk_eq_sInf_scalarPriorRisk]
  unfold Causalean.Stat.finiteDesignBayesRisk
  change sInf (Set.range (fun T : Fin (n + 1) → ℝ =>
    nu.E (Causalean.Stat.statewiseSquaredLoss (twoArmCountKernel D)
      (fun theta _x => effectTarget theta) T))) = _
  congr 1
  ext v
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨extendFinEstimator T,
      twoArmCount_expectedLoss_eq_scalarPriorRisk_extend nu D T⟩
  · rintro ⟨f, rfl⟩
    exact ⟨fun x : Fin (n + 1) => f (x : ℕ),
      twoArmCount_expectedLoss_eq_scalarPriorRisk_restrict nu D f⟩

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
