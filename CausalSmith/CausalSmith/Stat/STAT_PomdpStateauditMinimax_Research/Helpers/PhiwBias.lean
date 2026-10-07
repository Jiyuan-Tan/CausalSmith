module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwStationary
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.AuditedProjectionRisk
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-! # Expectation and contraction bias for arbitrary finite action alphabets. -/

public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-- The policy-induced state kernel is stochastic for every probability policy. -/
lemma policyKernel_probabilityVector_fin {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (p : Policy nX k) (hp : PolicyVector p) (s : JointState nX nH) :
    ProbabilityVector (policyKernel M p s) := by
  constructor
  · intro s'
    unfold policyKernel
    exact Finset.sum_nonneg fun a _ =>
      mul_nonneg ((hp s.1).1 a) ENNReal.toReal_nonneg
  · unfold policyKernel
    rw [Finset.sum_comm]
    calc
      ∑ a : Fin k, ∑ s' : JointState nX nH,
          p s.1 a * (M.K s a {q | q.2 = s'}).toReal =
          ∑ a : Fin k, p s.1 a * ∑ s' : JointState nX nH,
            (M.K s a {q | q.2 = s'}).toReal := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
      _ = ∑ a : Fin k, p s.1 a := by
        apply Finset.sum_congr rfl
        intro a _
        letI : IsProbabilityMeasure (M.K s a) := hK.1 s a
        have hsum : ∑ s' : JointState nX nH, M.K s a {q | q.2 = s'} = 1 := by
          have hpre := MeasureTheory.sum_measure_preimage_singleton
            (s := Finset.univ) (f := Prod.snd) (μ := M.K s a)
            (fun y _ => (measurableSet_singleton (x := y)).preimage measurable_snd)
          change ∑ s' : JointState nX nH, M.K s a (Prod.snd ⁻¹' {s'}) = 1
          simpa using hpre
        rw [← ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), hsum]
        simp
      _ = 1 := (hp s.1).2

/-- A mature full-path score is the corresponding target-policy window. -/
lemma phiwScore_observedRecord_eq_windowScore {T nX nH k depth : Nat}
    (M : PomdpModel T nX nH k) (t : Fin T) (hdepth : depth ≤ t.val)
    (w : FullPath T nX nH k) :
    phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t =
      windowScore M ⟨t.val - depth, by omega⟩ t w := by
  unfold phiwScore observedRecord obsProj windowScore
  congr 1
  apply Finset.prod_congr
  · ext q
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro q _
    rfl

/-- The expectation of a target-policy likelihood-ratio window is its iterated
target reward regression, averaged from the stationary behavior law. -/
lemma integral_windowScore_eq_stationary_targetIter {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (hStart : StationaryStart M)
    (j t : Fin T) (hjt : j.val ≤ t.val) :
    ∫ w, windowScore M j t w ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s *
        ((targetStep M)^[t.val - j.val] (rewardRegression M)) s := by
  have hfac := (full_history_factorization M hK hA hY hOverlap hStart).2.2
    j t hjt Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ, Measure.restrict_univ] at hfac
  rw [hfac, integral_currentState_eq_stationary M hK hA hStart]

lemma targetStep_iter_eq_markovOperatorIter {T nX nH k depth : Nat}
    (M : PomdpModel T nX nH k) (F : JointState nX nH → ℝ) :
    ((targetStep M)^[depth] F) =
      markovOperatorIter (policyKernel M M.e) depth F := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      simp only [markovOperatorIter_succ]
      rw [ih]
      rfl

lemma sum_stationary_mul_targetStep_iter {T nX nH k depth : Nat}
    (M : PomdpModel T nX nH k) (d : JointState nX nH → ℝ)
    (hd : IsStationary (policyKernel M M.e) d)
    (F : JointState nX nH → ℝ) :
    ∑ s, d s * ((targetStep M)^[depth] F) s = ∑ s, d s * F s := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply']
      unfold targetStep
      calc
        ∑ s, d s * ∑ x, policyKernel M M.e s x * ((targetStep M)^[depth] F) x =
            ∑ s, ∑ x, d s * (policyKernel M M.e s x *
              ((targetStep M)^[depth] F) x) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.mul_sum]
        _ = ∑ x, ∑ s, d s * (policyKernel M M.e s x *
              ((targetStep M)^[depth] F) x) := Finset.sum_comm
        _ = ∑ x, (∑ s, d s * policyKernel M M.e s x) *
              ((targetStep M)^[depth] F) x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro s _
          ring
        _ = ∑ x, d x * ((targetStep M)^[depth] F) x := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hd.2 x]
        _ = _ := ih

/-- Conditional target reward regression is uniformly bounded by one. -/
lemma rewardRegression_abs_le_one {T nX nH k : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (s : JointState nX nH) : |rewardRegression M s| ≤ 1 := by
  unfold rewardRegression
  calc
    |∑ a : Fin k, M.e s.1 a * ∫ q, q.1 ∂(M.K s a)| ≤
        ∑ a : Fin k, |M.e s.1 a * ∫ q, q.1 ∂(M.K s a)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : Fin k, M.e s.1 a * |∫ q, q.1 ∂(M.K s a)| := by
      apply Finset.sum_congr rfl
      intro a _
      rw [abs_mul, abs_of_nonneg ((hM.overlap.1 s.1).1 a)]
    _ ≤ ∑ a : Fin k, M.e s.1 a * 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (hM.moment s a).2.2.1
        ((hM.overlap.1 s.1).1 a)
    _ = 1 := by simpa using (hM.overlap.1 s.1).2

/-- The stationary behavior and target expectations of a depth-`depth` target
iterate differ by the geometric mixing bias. -/
lemma stationary_targetIter_bias_le {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) :
    |(∑ s, stationaryLaw (policyKernel M M.b) s *
        ((targetStep M)^[depth] (rewardRegression M)) s) - targetValue M| ≤
      2 * mixingAlpha t0 ^ depth := by
  letI : Nonempty (JointState nX nH) := ⟨(⟨0, hnX⟩, ⟨0, hnH⟩)⟩
  let dB := stationaryLaw (policyKernel M M.b)
  let dE := stationaryLaw (policyKernel M M.e)
  let F := (targetStep M)^[depth] (rewardRegression M)
  have hdB : ProbabilityVector dB := hM.start.1.1
  have hdE : ProbabilityVector dE := (target_stationary_law_of_class M hM.t0_pos hM).1
  have hgosc : OscillationBound 2 (rewardRegression M) := by
    intro x y
    calc
      |rewardRegression M x - rewardRegression M y| ≤
          |rewardRegression M x| + |rewardRegression M y| := abs_sub _ _
      _ ≤ 2 := by linarith [rewardRegression_abs_le_one M hM x,
        rewardRegression_abs_le_one M hM y]
  have hFosc : OscillationBound (mixingAlpha t0 ^ depth * 2) F := by
    rw [show F = markovOperatorIter (policyKernel M M.e) depth
      (rewardRegression M) from targetStep_iter_eq_markovOperatorIter M _]
    apply oscillationBound_markovOperatorIter
      (policyKernel M M.e)
      (policyKernel_probabilityVector_fin M hM.pomdp M.e hM.overlap.1)
      (Real.exp_nonneg _)
    · intro p q hp hq
      simpa [tvNorm, applyKernel, mixingAlpha,
        Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.markovStep,
        Matrix.vecMul, dotProduct] using
        hM.contraction M.e (Or.inr rfl) p q hp hq
    · exact hgosc
  have htv : tvNorm (dB - dE) ≤ 1 := by
    unfold tvNorm
    calc
      (1 / 2 : ℝ) * ∑ s, |dB s - dE s| ≤
          (1 / 2 : ℝ) * ∑ s, (dB s + dE s) := by
        gcongr with s
        exact (abs_sub (dB s) (dE s)).trans_eq
          (by rw [abs_of_nonneg (hdB.1 s), abs_of_nonneg (hdE.1 s)])
      _ = 1 := by rw [Finset.sum_add_distrib, hdB.2, hdE.2]; norm_num
  have htarget : targetValue M = ∑ s, dE s * F s := by
    unfold targetValue
    symm
    exact sum_stationary_mul_targetStep_iter M dE
      (target_stationary_law_of_class M hM.t0_pos hM) _
  rw [htarget]
  have hrewrite : (∑ s, dB s * F s) - ∑ s, dE s * F s =
      ∑ s, (dB s - dE s) * F s := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  change |(∑ s, dB s * F s) - ∑ s, dE s * F s| ≤ _
  rw [hrewrite]
  calc
    |∑ s, (dB s - dE s) * F s| ≤
        (mixingAlpha t0 ^ depth * 2) * tvNorm (dB - dE) := by
      simpa [tvNorm] using
        (abs_sum_sub_mul_le_oscillation_halfL1 hdB hdE hFosc)
    _ ≤ (mixingAlpha t0 ^ depth * 2) * 1 := by
      exact mul_le_mul_of_nonneg_left htv
        (mul_nonneg (pow_nonneg (Real.exp_nonneg _) _) (by norm_num))
    _ = 2 * mixingAlpha t0 ^ depth := by ring

end CausalSmith.Stat.PomdpStateauditMinimax
