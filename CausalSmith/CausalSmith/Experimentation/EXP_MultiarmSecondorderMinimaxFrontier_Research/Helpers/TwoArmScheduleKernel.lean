import CausalSmith.Experimentation.EXP_MultiarmSecondorderMinimaxFrontier_Research.Helpers.TwoArmScheduleKernelCore
import Causalean.Mathlib.Analysis.ClipInterval

open scoped BigOperators
open Finset

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

-- @node: canonicalScheduleKernel_nonneg
/-- [the canonical schedule kernel is nonnegative](goal). -/
lemma canonicalScheduleKernel_nonneg {n : ℕ} (theta : EffectTriple n)
    (z : Schedule 2 n) : 0 ≤ canonicalScheduleKernel theta z := by
  classical
  unfold canonicalScheduleKernel
  split_ifs
  · positivity
  · exact le_rfl

-- @node: canonicalScoreMass_sum
/-- [the canonical score mass sums](goal). -/
lemma canonicalScoreMass_sum {n : ℕ} (theta : EffectTriple n)
    (A : Assign 2 n) :
    ∑ s : Unit n → Bool, ∑ z : Schedule 2 n,
      (if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel theta z else 0) = 1 := by
  classical
  rw [Finset.sum_comm]
  calc
    (∑ z : Schedule 2 n, ∑ s : Unit n → Bool,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel theta z else 0) =
        ∑ z : Schedule 2 n, canonicalScheduleKernel theta z := by
          apply Finset.sum_congr rfl
          intro z _
          simp
    _ = 1 := canonicalScheduleKernel_sum theta

-- @node: canonicalNuLift
/-- The canonical nu lift property holds. -/
noncomputable def canonicalNuLift {n : ℕ} (nu : EffectPrior n) :
    Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n) where
  p z := ∑ theta, nu.p theta * canonicalScheduleKernel theta z
  p_nonneg z := Finset.sum_nonneg fun theta _ ↦
    mul_nonneg (nu.p_nonneg theta) (canonicalScheduleKernel_nonneg theta z)
  p_sum := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, canonicalScheduleKernel_sum, mul_one]
    exact nu.p_sum

-- @node: scoreCount
/-- The score count adds the positive-effect count to the number of successful zero-effect score bits. -/
def scoreCount {n : ℕ} (s : Unit n → Bool) : Fin (n + 1) :=
  ⟨(Finset.univ.filter fun i ↦ s i).card,
    Nat.lt_succ_iff.mpr (by
      simpa using Finset.card_le_card
        (Finset.filter_subset (fun i ↦ s i) Finset.univ))⟩

-- @node: twoArmScoreExperiment
/-- The two-arm score experiment draws an effect-count triple from the prior and then draws its transformed score count from the induced binomial law. -/
noncomputable def twoArmScoreExperiment {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) :
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment
      (EffectTriple n) PUnit.{1} (Assign 2 n × (Unit n → Bool)) (Fin (n + 1)) where
  allocations := {PUnit.unit}
  allocations_nonempty := by simp
  observationMass theta _ obs := D.p obs.1 *
    ∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z obs.1 i) = obs.2 then canonicalScheduleKernel theta z else 0
  observationMass_nonneg theta _ obs := mul_nonneg (D.p_nonneg obs.1)
    (Finset.sum_nonneg fun z _ ↦ by
      split_ifs
      · exact canonicalScheduleKernel_nonneg theta z
      · exact le_rfl)
  observationMass_sum theta _ := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, canonicalScoreMass_sum]
    simpa using D.p_sum
  statistic _ obs := scoreCount obs.2
  fallbackObservation := (fun _ ↦ 0, fun _ ↦ false)

-- @node: twoArmScoreExperiment_jointMass
/-- [the two arm score experiment joint mass property holds](goal). -/
lemma twoArmScoreExperiment_jointMass {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (theta : EffectTriple n) (obs : Assign 2 n × (Unit n → Bool)) :
    (twoArmScoreExperiment D).jointMass theta (PUnit.unit, obs) =
      D.p obs.1 * ∑ z : Schedule 2 n,
        if (fun i ↦ twoArmS z obs.1 i) = obs.2 then
          canonicalScheduleKernel theta z else 0 := by
  simp [twoArmScoreExperiment,
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.jointMass,
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.uniformAllocationMass]

-- @node: twoArmCanonicalScore_mass_eq_statisticFactor
/-- [the two arm canonical score mass equals statistic factor](goal). -/
lemma twoArmCanonicalScore_mass_eq_statisticFactor {n : ℕ}
    (theta : EffectTriple n) (A : Assign 2 n) (s : Unit n → Bool) :
    (∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel theta z else 0) =
      (∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
        if (scoreCount s : ℕ) = (theta.1.1 : ℕ) + k then
          binomialHalf (theta.1.2.2 : ℕ) k else 0) /
        Nat.choose n (scoreCount s : ℕ) := by
  let x := scoreCount s
  rw [← twoArmXMass_eq_binomial_sum theta A x]
  rw [← twoArmCanonicalConditionalScore_mass theta A x s]
  · apply Finset.sum_congr rfl
    intro z _
    by_cases hs : (fun i ↦ twoArmS z A i) = s
    · have hx : twoArmX z A = x := by
        apply Fin.ext
        change (Finset.univ.filter fun i ↦ twoArmS z A i).card =
          (Finset.univ.filter fun i ↦ s i).card
        congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [congrFun hs i]
      simp [hs, hx]
    · simp [hs]
  · rfl

-- @node: twoArmScoreFactorization
/-- The two arm score factorization property holds. -/
noncomputable def twoArmScoreFactorization {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) :
    (twoArmScoreExperiment D).SufficientFactorization where
  carrierWeight sample := D.p sample.2.1 /
    Nat.choose n (scoreCount sample.2.2 : ℕ)
  carrierWeight_nonneg sample := div_nonneg (D.p_nonneg sample.2.1) (by positivity)
  statisticFactor theta x :=
    ∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
      if (x : ℕ) = (theta.1.1 : ℕ) + k then
        binomialHalf (theta.1.2.2 : ℕ) k else 0
  statisticFactor_nonneg theta x := Finset.sum_nonneg fun k _ ↦ by
    split_ifs
    · unfold binomialHalf
      positivity
    · exact le_rfl
  jointMass_factor theta sample := by
    rcases sample with ⟨u, A, s⟩
    cases u
    rw [twoArmScoreExperiment_jointMass]
    rw [twoArmCanonicalScore_mass_eq_statisticFactor]
    simp only [Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.sampleStatistic,
      twoArmScoreExperiment]
    simp only [div_eq_mul_inv]
    ac_rfl

-- @node: scoreToObserved
/-- A transformed score and treatment assignment determine the corresponding observed outcome. -/
def scoreToObserved {n : ℕ} (A : Assign 2 n) (s : Unit n → Bool) :
    ObservedOutcome n := fun i ↦ if A i = 0 then s i else !(s i)

-- @node: scoreToObserved_twoArmS
/-- [the score to observed two arm s property holds](goal). -/
lemma scoreToObserved_twoArmS {n : ℕ} (z : Schedule 2 n) (A : Assign 2 n) :
    scoreToObserved A (fun i ↦ twoArmS z A i) = obsOutcome z A := by
  funext i
  by_cases hA : A i = 0
  · simp [scoreToObserved, twoArmS, obsOutcome, potentialOutcome, hA]
  · have hA1 : A i = 1 := Fin.eq_one_of_ne_zero _ hA
    simp [scoreToObserved, twoArmS, obsOutcome, potentialOutcome, hA, hA1]

-- @node: scoreFullEstimator
/-- The score full estimator property holds. -/
noncomputable def scoreFullEstimator {n : ℕ}
    (est : Estimator 2 n twoArmContrast) :
    PUnit.{1} × (Assign 2 n × (Unit n → Bool)) → ℝ :=
  fun sample ↦ est sample.2.1 (scoreToObserved sample.2.1 sample.2.2)

-- @node: effectTarget
/-- The two-arm effect target is the positive-effect share minus the negative-effect share. -/
noncomputable def effectTarget {n : ℕ} (theta : EffectTriple n) : ℝ :=
  ((((theta.1.1 : ℕ) : ℝ) - ((theta.1.2.1 : ℕ) : ℝ)) / n)

-- @node: twoArmScoreExperiment_fullRisk_eq
/-- [the two arm score experiment full risk equals property holds](goal). -/
lemma twoArmScoreExperiment_fullRisk_eq {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (est : Estimator 2 n twoArmContrast) (theta : EffectTriple n) :
    (twoArmScoreExperiment D).fullRisk effectTarget
        (scoreFullEstimator est) theta =
      ∑ A : Assign 2 n, D.p A * ∑ z : Schedule 2 n,
        canonicalScheduleKernel theta z *
          ((est A (obsOutcome z A) : ℝ) - effectTarget theta) ^ 2 := by
  classical
  unfold Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.fullRisk
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Fintype.sum_prod_type]
  simp only [scoreFullEstimator]
  simp_rw [Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.jointMass,
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.uniformAllocationMass,
    twoArmScoreExperiment]
  simp only [Finset.mem_singleton, ↓reduceIte, Finset.card_singleton,
    Nat.cast_one, inv_one, one_mul]
  change (∑ A : Assign 2 n, ∑ s : Unit n → Bool,
    (D.p A * ∑ z : Schedule 2 n,
      if (fun i ↦ twoArmS z A i) = s then canonicalScheduleKernel theta z else 0) *
      ((est A (scoreToObserved A s) : ℝ) - effectTarget theta) ^ 2) = _
  apply Finset.sum_congr rfl
  intro A _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (fun i ↦ twoArmS z A i)]
  · rw [scoreToObserved_twoArmS]
    simp
  · intro s _ hs
    simp [Ne.symm hs]
  · simp

-- @node: twoArmScoreFactorization_fiberCarrierMass
/-- [the two arm score factorization fiber carrier mass property holds](goal). -/
lemma twoArmScoreFactorization_fiberCarrierMass {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (x : Fin (n + 1)) :
    (twoArmScoreFactorization D).fiberCarrierMass x = 1 := by
  classical
  unfold Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.SufficientFactorization.fiberCarrierMass
  rw [Fintype.sum_prod_type]
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [Fintype.sum_prod_type]
  simp only [twoArmScoreFactorization,
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.sampleStatistic,
    twoArmScoreExperiment]
  rw [Finset.sum_comm]
  have hx : (x : ℕ) ≤ n := Nat.le_of_lt_succ x.isLt
  have hchoose : (Nat.choose n (x : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hx).ne'
  calc
    (∑ s : Unit n → Bool, ∑ A : Assign 2 n,
      if scoreCount s = x then D.p A / Nat.choose n (scoreCount s : ℕ) else 0) =
        ∑ s : Unit n → Bool,
          if scoreCount s = x then (1 : ℝ) / Nat.choose n (x : ℕ) else 0 := by
            apply Finset.sum_congr rfl
            intro s _
            by_cases hs : scoreCount s = x
            · simp only [hs, if_pos]
              rw [← Finset.sum_div, D.p_sum]
            · simp [hs]
    _ = (Nat.choose n (x : ℕ) : ℝ) / Nat.choose n (x : ℕ) := by
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero,
        Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype]
      rw [show Fintype.card {s : Unit n → Bool // scoreCount s = x} =
          Nat.choose n (x : ℕ) by
        rw [← twoArmScoreSupport_card n x]
        apply Fintype.card_congr
        exact Equiv.subtypeEquiv (Equiv.refl _) (by
          intro s
          rw [Fin.ext_iff]
          rfl)]
      rw [div_eq_mul_inv]
      simp
      change (Nat.choose n (x : ℕ) : ℝ) *
        (Nat.choose n (x : ℕ) : ℝ)⁻¹ =
        (Nat.choose n (x : ℕ) : ℝ) *
          (Nat.choose n (x : ℕ) : ℝ)⁻¹
      rfl
    _ = 1 := div_self hchoose

-- @node: twoArmScoreExperiment_statisticMass
/-- [the two arm score experiment statistic mass property holds](goal). -/
lemma twoArmScoreExperiment_statisticMass {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (theta : EffectTriple n) (x : Fin (n + 1)) :
    (twoArmScoreExperiment D).statisticMass theta x =
      ∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
        if (x : ℕ) = (theta.1.1 : ℕ) + k then
          binomialHalf (theta.1.2.2 : ℕ) k else 0 := by
  rw [(twoArmScoreFactorization D).statisticMass_eq_factor_mul_fiberCarrierMass]
  rw [twoArmScoreFactorization_fiberCarrierMass]
  simp [twoArmScoreFactorization]

-- @node: twoArmScoreExperiment_statisticRisk_eq
/-- [the two arm score experiment statistic risk equals property holds](goal). -/
lemma twoArmScoreExperiment_statisticRisk_eq {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (f : Fin (n + 1) → ℝ) (theta : EffectTriple n) :
    (twoArmScoreExperiment D).statisticRisk effectTarget f theta =
      ∑ x : Fin (n + 1),
        (∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
          if (x : ℕ) = (theta.1.1 : ℕ) + k then
            binomialHalf (theta.1.2.2 : ℕ) k else 0) *
          (f x - effectTarget theta) ^ 2 := by
  classical
  have hrisk :
      (twoArmScoreExperiment D).statisticRisk effectTarget f theta =
        ∑ x : Fin (n + 1),
          (twoArmScoreExperiment D).statisticMass theta x *
            (f x - effectTarget theta) ^ 2 := by
    simp only [Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.statisticRisk,
      Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.statisticMass,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro z _
    rw [Finset.sum_eq_single ((twoArmScoreExperiment D).sampleStatistic z)]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  rw [hrisk]
  simp_rw [twoArmScoreExperiment_statisticMass]

-- @node: canonicalScheduleKernel_mul_sq_target
/-- [the canonical schedule kernel times squared target property holds](goal). -/
lemma canonicalScheduleKernel_mul_sq_target {n : ℕ}
    (theta : EffectTriple n) (z : Schedule 2 n) (A : Assign 2 n)
    (est : Estimator 2 n twoArmContrast) :
    canonicalScheduleKernel theta z *
        ((est A (obsOutcome z A) : ℝ) - effectTarget theta) ^ 2 =
      canonicalScheduleKernel theta z *
        ((est A (obsOutcome z A) : ℝ) - tauC twoArmContrast z) ^ 2 := by
  by_cases hz : hasEffectTriple theta z
  · rw [twoArmTau_eq_effectTriple hz]
    rfl
  · simp [canonicalScheduleKernel, hz]

-- @node: twoArmScoreExperiment_fullRisk_eq_labeled
/-- [the two arm score experiment full risk equals labeled](goal). -/
lemma twoArmScoreExperiment_fullRisk_eq_labeled {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (est : Estimator 2 n twoArmContrast) (theta : EffectTriple n) :
    (twoArmScoreExperiment D).fullRisk effectTarget
        (scoreFullEstimator est) theta =
      ∑ z : Schedule 2 n, canonicalScheduleKernel theta z *
        labeledRisk twoArmContrast (D, est) z := by
  rw [twoArmScoreExperiment_fullRisk_eq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  unfold labeledRisk Causalean.Experimentation.DesignBased.FiniteDesign.mse
    Causalean.Experimentation.DesignBased.FiniteDesign.E
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [canonicalScheduleKernel_mul_sq_target theta z A est]
  ring

-- @node: canonicalNuLift_expectedRisk
/-- [the canonical nu lift expected risk property holds](goal). -/
lemma canonicalNuLift_expectedRisk {n : ℕ} (nu : EffectPrior n)
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (est : Estimator 2 n twoArmContrast) :
    nu.E (fun theta ↦ (twoArmScoreExperiment D).fullRisk effectTarget
        (scoreFullEstimator est) theta) =
      (canonicalNuLift nu).E
        (fun z ↦ labeledRisk twoArmContrast (D, est) z) := by
  simp_rw [twoArmScoreExperiment_fullRisk_eq_labeled]
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  change (∑ theta : EffectTriple n, nu.p theta *
      ∑ z : Schedule 2 n, canonicalScheduleKernel theta z *
        labeledRisk twoArmContrast (D, est) z) =
    ∑ z : Schedule 2 n, (∑ theta : EffectTriple n,
      nu.p theta * canonicalScheduleKernel theta z) *
        labeledRisk twoArmContrast (D, est) z
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro theta _
  ring

-- @node: extendFinEstimator
/-- A score-count estimator on the finite support is extended to all natural counts by using zero outside that support. -/
noncomputable def extendFinEstimator {n : ℕ} (g : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  fun x ↦ if hx : x < n + 1 then g ⟨x, hx⟩ else 0

-- @node: extendFinEstimator_of_lt
/-- [the observed count satisfies its stated condition](hyp:hx), [the extend fin estimator when is less than property holds](goal). -/
lemma extendFinEstimator_of_lt {n x : ℕ} (g : Fin (n + 1) → ℝ)
    (hx : x < n + 1) : extendFinEstimator g x = g ⟨x, hx⟩ := by
  simp [extendFinEstimator, hx]

-- @node: twoArmScoreExperiment_statisticRisk_eq_scalar
/-- [the two arm score experiment statistic risk equals scalar](goal). -/
lemma twoArmScoreExperiment_statisticRisk_eq_scalar {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (g : Fin (n + 1) → ℝ) (theta : EffectTriple n) :
    (twoArmScoreExperiment D).statisticRisk effectTarget g theta =
      ∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
        binomialHalf (theta.1.2.2 : ℕ) k *
          (extendFinEstimator g ((theta.1.1 : ℕ) + k) -
            effectTarget theta) ^ 2 := by
  classical
  rw [twoArmScoreExperiment_statisticRisk_eq]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ (theta.1.2.2 : ℕ) := by
    simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
  have hbound : (theta.1.1 : ℕ) + k < n + 1 := by
    have ht := theta.2
    omega
  rw [Finset.sum_eq_single ⟨(theta.1.1 : ℕ) + k, hbound⟩]
  · simp [extendFinEstimator, hbound]
  · intro x _ hx
    have hne : (x : ℕ) ≠ (theta.1.1 : ℕ) + k := by
      intro h
      exact hx (Fin.ext h)
    simp [hne]
  · simp

-- @node: twoArmRaoBlackwellThroughX
/-- [the two arm rao blackwell through x property holds](goal). -/
lemma twoArmRaoBlackwellThroughX {n : ℕ} (nu : EffectPrior n) :
    RaoBlackwellThroughX nu (canonicalNuLift nu) := by
  intro D est
  let E : Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment
      (EffectTriple n) PUnit.{1} (Assign 2 n × (Unit n → Bool)) (Fin (n + 1)) :=
    twoArmScoreExperiment D
  let F : E.SufficientFactorization := twoArmScoreFactorization D
  let g : Fin (n + 1) → ℝ :=
    E.raoBlackwellEstimator F (scoreFullEstimator est)
  refine ⟨extendFinEstimator g, ?_⟩
  rw [← canonicalNuLift_expectedRisk nu D est]
  change _ ≤ nu.E (E.fullRisk effectTarget (scoreFullEstimator est))
  have hRB := E.priorRisk_raoBlackwellEstimator_le F nu effectTarget
    (scoreFullEstimator est)
  apply le_trans ?_ hRB
  unfold Causalean.Experimentation.DesignBased.FiniteDesign.E
  apply Finset.sum_le_sum
  intro theta _
  rw [twoArmScoreExperiment_statisticRisk_eq_scalar]
  rfl

-- @node: twoArmLc_eq_two
/-- [the two arm contrast norm equals two](goal). -/
lemma twoArmLc_eq_two : Lc twoArmContrast = 2 := by
  norm_num [Lc, twoArmContrast, ratContrastToReal, twoArmContrastQ,
    Fin.sum_univ_succ]

-- @node: effectTarget_mem_twoArmRange
/-- [the effect target belongs to two arm range](goal). -/
lemma effectTarget_mem_twoArmRange {n : ℕ} (theta : EffectTriple n) :
    effectTarget theta ∈ Set.Icc (-Lc twoArmContrast / 2) (Lc twoArmContrast / 2) := by
  rw [twoArmLc_eq_two]
  norm_num only [neg_div, neg_neg, OfNat.ofNat_eq_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)]
  cases n with
  | zero =>
      have ht := theta.2
      simp only [Nat.cast_zero, div_zero, effectTarget]
      constructor <;> norm_num
  | succ n =>
      have ht := theta.2
      have hp : (theta.1.1 : ℕ) ≤ n + 1 := by omega
      have hm : (theta.1.2.1 : ℕ) ≤ n + 1 := by omega
      have hnpos : (0 : ℝ) < n + 1 := by positivity
      have hpR : ((theta.1.1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast hp
      have hmR : ((theta.1.2.1 : ℕ) : ℝ) ≤ n + 1 := by exact_mod_cast hm
      constructor
      · dsimp [effectTarget]
        simp only [Nat.cast_add, Nat.cast_one]
        apply (le_div_iff₀ hnpos).2
        linarith
      · dsimp [effectTarget]
        simp only [Nat.cast_add, Nat.cast_one]
        apply (div_le_iff₀ hnpos).2
        linarith

-- @node: observedScore
/-- The observed score equals the outcome on the first arm and its complement on the second arm. -/
def observedScore {n : ℕ} (A : Assign 2 n) (y : ObservedOutcome n) :
    Unit n → Bool := fun i ↦ if A i = 0 then y i else !(y i)

-- @node: scalarClippedEstimator
/-- The scalar clipped estimator property holds. -/
noncomputable def scalarClippedEstimator {n : ℕ} (f : ℕ → ℝ) :
    Estimator 2 n twoArmContrast := fun A y ↦
  ⟨clip twoArmContrast (f ((Finset.univ.filter fun i ↦ observedScore A y i).card)),
    clip_mem twoArmContrast _⟩

-- @node: scoreFullEstimator_scalarClipped
/-- [the score full estimator scalar clipped property holds](goal). -/
lemma scoreFullEstimator_scalarClipped {n : ℕ} (f : ℕ → ℝ)
    (sample : PUnit.{1} × (Assign 2 n × (Unit n → Bool))) :
    scoreFullEstimator (scalarClippedEstimator f) sample =
      clip twoArmContrast (f (scoreCount sample.2.2)) := by
  rcases sample with ⟨u, A, s⟩
  cases u
  change clip twoArmContrast
      (f ((Finset.univ.filter fun i ↦
        observedScore A (scoreToObserved A s) i).card)) =
    clip twoArmContrast (f ((Finset.univ.filter fun i ↦ s i).card))
  congr 2
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : A i = 0
  · simp [observedScore, scoreToObserved, hA]
  · simp [observedScore, scoreToObserved, hA]

-- @node: scalarPriorRisk
/-- Scalar prior risk averages squared error over effect-count triples and the induced binomial score count. -/
noncomputable def scalarPriorRisk {n : ℕ} (nu : EffectPrior n)
    (f : ℕ → ℝ) : ℝ :=
  ∑ theta, nu.p theta * ∑ k ∈ Finset.range (((theta.1).2.2 : ℕ) + 1),
    binomialHalf ((theta.1).2.2 : ℕ) k *
      (f (((theta.1).1 : ℕ) + k) - effectTarget theta) ^ 2

-- @node: scalarPriorRisk_nonneg
/-- [the scalar prior risk is nonnegative](goal). -/
lemma scalarPriorRisk_nonneg {n : ℕ} (nu : EffectPrior n) (f : ℕ → ℝ) :
    0 ≤ scalarPriorRisk nu f := by
  unfold scalarPriorRisk
  exact Finset.sum_nonneg fun theta _ ↦ mul_nonneg (nu.p_nonneg theta)
    (Finset.sum_nonneg fun k _ ↦ mul_nonneg (by
      unfold binomialHalf
      positivity) (sq_nonneg _))

-- @node: scalarBayesRisk_eq_sInf_scalarPriorRisk
/-- [the scalar bayes risk equals s inf scalar prior risk](goal). -/
lemma scalarBayesRisk_eq_sInf_scalarPriorRisk {n : ℕ} (nu : EffectPrior n) :
    scalarBayesRisk nu = sInf {v : ℝ | ∃ f : ℕ → ℝ, v = scalarPriorRisk nu f} := by
  rfl

-- @node: clippedFullRisk_eq_statisticRisk
/-- [the clipped full risk equals statistic risk](goal). -/
lemma clippedFullRisk_eq_statisticRisk {n : ℕ}
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (f : ℕ → ℝ) (theta : EffectTriple n) :
    (twoArmScoreExperiment D).fullRisk effectTarget
        (scoreFullEstimator (scalarClippedEstimator f)) theta =
      (twoArmScoreExperiment D).statisticRisk effectTarget
        (fun x ↦ clip twoArmContrast (f x)) theta := by
  unfold Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.fullRisk
    Causalean.Stat.FiniteRaoBlackwell.FiniteUniformExperiment.statisticRisk
  apply Finset.sum_congr rfl
  intro sample _
  rw [scoreFullEstimator_scalarClipped]
  rfl

-- @node: clippedScalarPriorRisk_le
/-- [the clipped scalar prior risk is at most property holds](goal). -/
lemma clippedScalarPriorRisk_le {n : ℕ} (nu : EffectPrior n) (f : ℕ → ℝ) :
    scalarPriorRisk nu (fun x ↦ clip twoArmContrast (f x)) ≤
      scalarPriorRisk nu f := by
  unfold scalarPriorRisk
  apply Finset.sum_le_sum
  intro theta _
  apply mul_le_mul_of_nonneg_left _ (nu.p_nonneg theta)
  apply Finset.sum_le_sum
  intro k _
  apply mul_le_mul_of_nonneg_left _
  · unfold binomialHalf
    positivity
  · change (Causalean.Mathlib.Analysis.clipIcc
      (-Lc twoArmContrast / 2) (Lc twoArmContrast / 2)
      (f ((theta.1.1 : ℕ) + k)) - effectTarget theta) ^ 2 ≤ _
    exact Causalean.Mathlib.Analysis.clipIcc_sub_sq_le
      (effectTarget_mem_twoArmRange theta) _

-- @node: canonicalNuLift_clippedRisk_le
/-- [the canonical nu lift clipped risk is at most property holds](goal). -/
lemma canonicalNuLift_clippedRisk_le {n : ℕ} (nu : EffectPrior n)
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n))
    (f : ℕ → ℝ) :
    (canonicalNuLift nu).E (fun z ↦
        labeledRisk twoArmContrast (D, scalarClippedEstimator f) z) ≤
      scalarPriorRisk nu f := by
  rw [← canonicalNuLift_expectedRisk]
  simp_rw [clippedFullRisk_eq_statisticRisk,
    twoArmScoreExperiment_statisticRisk_eq_scalar]
  calc
    nu.E (fun theta ↦ ∑ k ∈ Finset.range ((theta.1.2.2 : ℕ) + 1),
      binomialHalf (theta.1.2.2 : ℕ) k *
        (extendFinEstimator (fun x ↦ clip twoArmContrast (f x))
          ((theta.1.1 : ℕ) + k) - effectTarget theta) ^ 2) =
        scalarPriorRisk nu (fun x ↦ clip twoArmContrast (f x)) := by
          unfold Causalean.Experimentation.DesignBased.FiniteDesign.E scalarPriorRisk
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
    _ ≤ scalarPriorRisk nu f := clippedScalarPriorRisk_le nu f

-- @node: fullScheduleBayesRisk_canonicalNuLift_eq
/-- [the full schedule bayes risk canonical nu lift equals property holds](goal). -/
lemma fullScheduleBayesRisk_canonicalNuLift_eq {n : ℕ} (nu : EffectPrior n)
    (D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n)) :
    fullScheduleBayesRisk (canonicalNuLift nu) D = scalarBayesRisk nu := by
  have hscalarBdd : BddBelow
      {v : ℝ | ∃ f : ℕ → ℝ, v = scalarPriorRisk nu f} := by
    refine ⟨0, ?_⟩
    rintro v ⟨f, rfl⟩
    exact scalarPriorRisk_nonneg nu f
  have hscalarNe :
      {v : ℝ | ∃ f : ℕ → ℝ, v = scalarPriorRisk nu f}.Nonempty :=
    ⟨scalarPriorRisk nu (fun _ ↦ 0), ⟨fun _ ↦ 0, rfl⟩⟩
  have hfullBdd : BddBelow {v : ℝ | ∃ est : Estimator 2 n twoArmContrast,
      v = (canonicalNuLift nu).E
        (fun z ↦ labeledRisk twoArmContrast (D, est) z)} := by
    refine ⟨0, ?_⟩
    rintro v ⟨est, rfl⟩
    exact Finset.sum_nonneg fun z _ ↦ mul_nonneg
      ((canonicalNuLift nu).p_nonneg z) (D.mse_nonneg _ _)
  have hfullNe : {v : ℝ | ∃ est : Estimator 2 n twoArmContrast,
      v = (canonicalNuLift nu).E
        (fun z ↦ labeledRisk twoArmContrast (D, est) z)}.Nonempty :=
    ⟨(canonicalNuLift nu).E (fun z ↦
      labeledRisk twoArmContrast (D, scalarClippedEstimator (fun _ ↦ 0)) z),
      ⟨scalarClippedEstimator (fun _ ↦ 0), rfl⟩⟩
  unfold fullScheduleBayesRisk
  rw [scalarBayesRisk_eq_sInf_scalarPriorRisk]
  apply le_antisymm
  · apply le_csInf hscalarNe
    rintro v ⟨f, rfl⟩
    exact (csInf_le hfullBdd
      ⟨scalarClippedEstimator f, rfl⟩).trans
        (canonicalNuLift_clippedRisk_le nu D f)
  · apply le_csInf hfullNe
    rintro v ⟨est, rfl⟩
    obtain ⟨f, hf⟩ := twoArmRaoBlackwellThroughX nu D est
    exact (csInf_le hscalarBdd ⟨f, rfl⟩).trans hf

-- @node: lem:two-arm-scalar-prior-schedule-kernel
/-- [Every effect-triple prior has a complete-schedule lift whose Bayes risk is exactly the scalar binomial-experiment Bayes risk for every assignment law.](goal) -/
lemma twoArmScalarPriorScheduleKernel {n : ℕ} (nu : EffectPrior n) :
    ∃ lift : Causalean.Experimentation.DesignBased.FiniteDesign (Schedule 2 n),
      IsCanonicalNuLift nu lift ∧
      (∀ theta : EffectTriple n, HasTwoArmScalarKernel theta) ∧
      RaoBlackwellThroughX nu lift ∧
      (∀ D : Causalean.Experimentation.DesignBased.FiniteDesign (Assign 2 n),
        fullScheduleBayesRisk lift D = scalarBayesRisk nu) := by
  refine ⟨canonicalNuLift nu, ?_, ?_, ?_, ?_⟩
  · intro z
    rfl
  · exact fun theta ↦ hasTwoArmScalarKernel_canonical theta
  · exact twoArmRaoBlackwellThroughX nu
  · exact fullScheduleBayesRisk_canonicalNuLift_eq nu

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
