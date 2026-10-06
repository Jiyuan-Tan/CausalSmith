module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import Causalean.Mathlib.Probability.Certified.Existence

/-!
# Binary POMDP kernel regularity

Probability policies give stochastic transition rows and unit-range reward
regressions. Contracted target kernels have stationary probability laws.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators

/-- Probability target policies preserve the unit range of kernel rewards. [Under the listed formal conditions](hyp:hK,hE), [the stated conclusion holds](goal).-/
-- @node: rewardRegression_unit
lemma rewardRegression_unit {T : Nat} (M : RawPomdpExperiment T 2 2)
    (hK : PomdpKernelLaw M) (hE : PolicyVector M.e) :
    ∀ s, rewardRegression M s ∈ Set.Icc (0 : ℝ) 1 := by
  have hmean (s : JointState 2 2) (a : Bool) :
      (∫ p, p.1 ∂M.K s a) ∈ Set.Icc (0 : ℝ) 1 := by
    letI : MeasureTheory.IsProbabilityMeasure (M.K s a) := hK.1 s a
    have hae : ∀ᵐ p ∂M.K s a, p.1 ∈ Set.Icc (0 : ℝ) 1 := by
      apply (MeasureTheory.mem_ae_iff_prob_eq_one
        (measurable_fst measurableSet_Icc)).2
      exact hK.2.1 s a
    have hn : 0 ≤ ∫ p, p.1 ∂M.K s a :=
      MeasureTheory.integral_nonneg_of_ae (hae.mono (by intro p hp; exact hp.1))
    have hnorm := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := M.K s a) (f := fun p => p.1) (C := 1) (hae.mono (by
        intro p hp
        simpa only [Real.norm_eq_abs] using
          (abs_le.mpr ⟨by linarith [hp.1], hp.2⟩ : |p.1| ≤ 1)))
    constructor
    · exact hn
    · simpa only [MeasureTheory.probReal_univ, mul_one, Real.norm_eq_abs]
        using le_trans (le_abs_self _) hnorm
  have hr (s : JointState 2 2) : rewardRegression M s ∈ Set.Icc (0 : ℝ) 1 := by
    have hp := hE s.1
    constructor
    · unfold rewardRegression
      apply Finset.sum_nonneg
      intro a _
      exact mul_nonneg (hp.1 a) (hmean s a).1
    · unfold rewardRegression
      calc
        (∑ a : Bool, M.e s.1 a * ∫ p, p.1 ∂M.K s a) ≤
            ∑ a : Bool, M.e s.1 a * 1 := by
          apply Finset.sum_le_sum
          intro a _
          exact mul_le_mul_of_nonneg_left (hmean s a).2 (hp.1 a)
        _ = 1 := by simpa only [mul_one] using hp.2
  exact hr

-- @node: targetValue_mem_unitInterval
/-- Unit-range kernel rewards and probability policies keep the target value in `[0,1]`. [Under the listed formal conditions](hyp:hK,hπ,hE), [the stated conclusion holds](goal).-/
lemma targetValue_mem_unitInterval {T : Nat} (M : RawPomdpExperiment T 2 2)
    (hK : PomdpKernelLaw M)
    (hπ : IsStationary (policyKernel M M.e)
      (stationaryLaw (policyKernel M M.e)))
    (hE : PolicyVector M.e) : targetValue M ∈ Set.Icc (0 : ℝ) 1 := by
  have hr := rewardRegression_unit M hK hE
  have hpi := hπ.1
  constructor
  · unfold targetValue
    apply Finset.sum_nonneg
    intro s _
    exact mul_nonneg (hpi.1 s) (hr s).1
  · unfold targetValue
    calc
      (∑ s, stationaryLaw (policyKernel M M.e) s * rewardRegression M s) ≤
          ∑ s, stationaryLaw (policyKernel M M.e) s * 1 := by
        apply Finset.sum_le_sum
        intro s _
        exact mul_le_mul_of_nonneg_left (hr s).2 (hpi.1 s)
      _ = 1 := by simpa only [mul_one] using hpi.2

-- @node: policyKernel_stochastic_of_kernelLaw
/-- A probability reward-successor kernel and a probability policy induce stochastic rows. [Under the listed formal conditions](hyp:hK,hp), [the stated conclusion holds](goal).-/
lemma policyKernel_stochastic_of_kernelLaw {T : Nat} (M : RawPomdpExperiment T 2 2)
    (hK : PomdpKernelLaw M) (p : Policy 2) (hp : PolicyVector p) :
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStochasticMatrix
      (policyKernel M p) := by
  constructor
  · intro s sp
    unfold policyKernel
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg ((hp s.1).1 a) MeasureTheory.measureReal_nonneg
  · intro s
    have hrow (a : Bool) :
        (∑ sp : JointState 2 2, (M.K s a {q | q.2 = sp}).toReal) = 1 := by
      letI : MeasureTheory.IsProbabilityMeasure (M.K s a) := hK.1 s a
      have hsum := MeasureTheory.sum_measureReal_preimage_singleton
        (μ := M.K s a) (f := fun q : Step 2 2 => q.2)
        (Finset.univ : Finset (JointState 2 2)) (by
          intro sp _
          exact measurable_snd (MeasurableSet.singleton sp))
      simpa [MeasureTheory.measureReal_def, Set.preimage] using hsum
    calc
      (∑ sp, policyKernel M p s sp) =
          ∑ a : Bool, p s.1 a * ∑ sp : JointState 2 2,
            (M.K s a {q | q.2 = sp}).toReal := by
        unfold policyKernel
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ = ∑ a : Bool, p s.1 a := by simp_rw [hrow, mul_one]
      _ = 1 := (hp s.1).2

-- @node: targetStationary_of_class
/-- The contracted target kernel has the selected stationary probability law. [Under the listed formal conditions](hyp:hM), [the stated conclusion holds](goal).-/
lemma targetStationary_of_class {T : Nat} {t0 zeta : ℝ}
    (M : RawPomdpExperiment T 2 2) (hM : BinaryPomdpClass t0 zeta M) :
    IsStationary (policyKernel M M.e) (stationaryLaw (policyKernel M M.e)) := by
  have hα0 : 0 ≤ mixingAlpha t0 := by
    unfold mixingAlpha
    exact (Real.exp_pos _).le
  have hα1 : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    have hrec : 0 < 1 / t0 := one_div_pos.mpr hM.t0_pos
    have h := Real.exp_lt_exp.mpr (show -(1 / t0) < (0 : ℝ) by linarith)
    simpa only [Real.exp_zero] using h
  obtain ⟨pi, hpi, _⟩ :=
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.existsUnique_stationary_of_contractsL1
      (policyKernel_stochastic_of_kernelLaw M hM.pomdp_kernel M.e hM.policy_overlap.1)
      hα0 hα1 hM.target_contraction
  exact stationaryLaw_isStationary_of_exists ⟨pi, hpi⟩

end CausalSmith.Stat.PomdpBinaryhiddenRate
