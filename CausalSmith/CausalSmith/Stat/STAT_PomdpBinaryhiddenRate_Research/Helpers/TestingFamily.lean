module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingFamilyBasics
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Helpers.TestingKL

/-!
# Testing-family membership and separation

Assemble the positive testing pair and its observed-data divergence bound.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open MeasureTheory

-- @node: lem:testing-family-membership
/-- Both testing laws satisfy all six model conditions, have exact target
separation, and are close after projection to observed data. Their policies
coincide and their stationary joint-state laws coincide. [Under the listed formal conditions](hyp:ht0,hzeta,hT), [the stated conclusion holds](goal).-/
lemma testingFamily_membership (T : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 ≤ zeta) (hT : 12 ≤ T) :
    let Mp := testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT)
    let Mm := testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)
    BinaryPomdpClass t0 zeta Mp ∧
    BinaryPomdpClass t0 zeta Mm ∧
    |targetValue Mp - targetValue Mm| = 1 / (8 * Real.sqrt T) ∧
    InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≠ ⊤ ∧
    (InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm)).toReal ≤ 1 / 12 ∧
    Mp.e = Mp.b ∧ Mm.e = Mm.b ∧
    stationaryLaw (policyKernel Mp Mp.e) = stationaryLaw (policyKernel Mp Mp.b) ∧
    stationaryLaw (policyKernel Mm Mm.e) = stationaryLaw (policyKernel Mm Mm.b) ∧
    (∀ C : ℝ, 1 < C →
      ∀ s, stationaryLaw (policyKernel Mp Mp.e) s ≤
        C * stationaryLaw (policyKernel Mp Mp.b) s ∧
      stationaryLaw (policyKernel Mm Mm.e) s ≤
        C * stationaryLaw (policyKernel Mm Mm.b) s) := by
  dsimp
  have hMp : BinaryPomdpClass t0 zeta
      (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT)) := by
    exact testingExperiment_class_of_history T t0 zeta (vT T) ht0 hzeta
      (Or.inl rfl) (vT_bound T hT)
  have hMm : BinaryPomdpClass t0 zeta
      (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)) := by
    exact testingExperiment_class_of_history T t0 zeta (-(vT T)) ht0 hzeta
      (Or.inr rfl) (neg_vT_bound T hT)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hMp
  · exact hMm
  · have hSp : IsStationary
        (policyKernel (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT))
          (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT)).e)
        (stationaryLaw (policyKernel
          (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT))
          (testingExperiment T (vT T) (Or.inl rfl) (vT_bound T hT)).e)) := by
      exact stationaryLaw_isStationary_of_exists
        ⟨testingNextStateMass,
          testingExperiment_stationary T (vT T) (Or.inl rfl) (vT_bound T hT)⟩
    have hSm : IsStationary
        (policyKernel (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT))
          (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)).e)
        (stationaryLaw (policyKernel
          (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT))
          (testingExperiment T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)).e)) := by
      exact stationaryLaw_isStationary_of_exists
        ⟨testingNextStateMass,
          testingExperiment_stationary T (-(vT T)) (Or.inr rfl) (neg_vT_bound T hT)⟩
    rw [testingExperiment_targetValue_eq T (vT T) (Or.inl rfl)
      (vT_bound T hT) hSp,
      testingExperiment_targetValue_eq T (-(vT T)) (Or.inr rfl)
        (neg_vT_bound T hT) hSm]
    have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2
      (by exact_mod_cast (by omega : 0 < T))
    have hvnonneg : 0 ≤ vT T := by unfold vT; positivity
    rw [show (1 / 2 + vT T) - (1 / 2 + -(vT T)) = 2 * vT T by ring,
      abs_of_nonneg (mul_nonneg (by norm_num) hvnonneg)]
    unfold vT
    field_simp
    <;> ring
  · exact testingObservedLaw_klDiv_ne_top T (vT T) (-(vT T))
      (Or.inl rfl) (vT_bound T hT) (Or.inr rfl) (neg_vT_bound T hT)
  · have hbound := testingObservedLaw_klDiv_le T (vT T) (-(vT T))
        (Or.inl rfl) (vT_bound T hT) (Or.inr rfl) (neg_vT_bound T hT)
    have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.2
      (by exact_mod_cast (by omega : 0 < T))
    have hsquare : (Real.sqrt (T : ℝ)) ^ 2 = T :=
      Real.sq_sqrt (Nat.cast_nonneg T)
    have hbudget : (T : ℝ) * (4 * (vT T - -(vT T)) ^ 2) = 1 / 16 := by
      unfold vT
      field_simp
      nlinarith [hsquare]
    rw [hbudget] at hbound
    have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal (1 / 16 : ℝ) ≠ ⊤)
      hbound
    calc
      _ ≤ (1 / 16 : ℝ) := by simpa using hreal
      _ ≤ 1 / 12 := by norm_num
  · rfl
  · rfl
  · rfl
  · rfl
  · intro C hC s
    constructor
    · exact coincidentPolicy_occupancy_bound _ hMp.stationary_start rfl C hC s
    · exact coincidentPolicy_occupancy_bound _ hMm.stationary_start rfl C hC s

end CausalSmith.Stat.PomdpBinaryhiddenRate
