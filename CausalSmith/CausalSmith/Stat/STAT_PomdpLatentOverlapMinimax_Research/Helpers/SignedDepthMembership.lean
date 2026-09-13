import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthStationarity
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthFilterRecursion

/-! # Model-class membership of the signed-depth family -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Assuming [the h C condition](hyp:hC), [the signed Depth eps bound assertion holds](goal). -/
lemma signedDepth_eps_bound {C : ℝ} (hC : 1 ≤ C) : 1 + epsC C ≤ C := by
  unfold epsC
  by_cases h : (C - 1) / 2 ≤ 1 / 2
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right (le_of_not_ge h)]
    linarith

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth initial apply assertion holds](goal). -/
lemma signedDepth_initial_apply {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (h : Fin (2 * (Q + 1))) :
    (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).init (0, h) =
      depthMass t0 Q (latentDepth Q h) *
        (1 + signedValue (latentSign Q h) * epsC C *
          policyFactor zeta ^ (-(latentDepth Q h : ℤ))) / 2 := by
  change ((signedDepthFinite T t0 zeta C Q v).init (0, h)).toReal = _
  rw [signedDepthFinite_init_toReal ht0 hzeta hC v h]
  rfl

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth stationary overlap base assertion holds](goal). -/
lemma signedDepth_stationary_overlap_base {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (h : Fin (2 * (Q + 1))) :
    stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).e) (0, h) ≤
      (1 + epsC C) * (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).init (0, h) := by
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  have hp : 1 / policyFactor zeta ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 hL.le
  have he : epsC C ∈ Set.Icc (0 : ℝ) (1 / 2) :=
    ⟨epsC_nonneg hC, epsC_le_half C⟩
  have hw : 0 ≤ depthMass t0 Q (latentDepth Q h) := depthMass_nonneg ht0 _ _
  have hLpow : 1 ≤ policyFactor zeta ^ latentDepth Q h := one_le_pow₀ hL.le
  have hrpow : (policyFactor zeta ^ latentDepth Q h)⁻¹ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (inv_le_one₀ (by positivity)).2 hLpow⟩
  have hepow_le : epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹ ≤ epsC C :=
    mul_le_of_le_one_right he.1 hrpow.2
  rw [signedDepth_target_eq_actionOne ht0 hzeta hC hQ]
  rw [signedDepth_stationaryLaw_apply ht0 hzeta hC hQ (by constructor <;> norm_num)]
  rw [signedDepth_initial_apply ht0 hzeta hC hQ]
  unfold signedDepthStationaryWeight
  rw [show policyFactor zeta ^ (-(latentDepth Q h : ℤ)) =
      (policyFactor zeta ^ latentDepth Q h)⁻¹ by rw [zpow_neg, zpow_natCast]]
  cases hs : latentSign Q h <;> simp [signedValue, hs]
  · have hbase : 0 ≤ depthMass t0 Q (latentDepth Q h) *
        (1 - epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹) / 2 := by
      apply div_nonneg
      · exact mul_nonneg hw (sub_nonneg.mpr
          (hepow_le.trans (he.2.trans (by norm_num))))
      · norm_num
    calc
      depthMass t0 Q (latentDepth Q h) * (1 - epsC C) / 2 ≤
          depthMass t0 Q (latentDepth Q h) *
            (1 - epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹) / 2 := by
              gcongr
      _ ≤ (1 + epsC C) * (depthMass t0 Q (latentDepth Q h) *
            (1 - epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹) / 2) := by
              nlinarith [mul_nonneg he.1 hbase]
  · have hbase : 0 ≤ depthMass t0 Q (latentDepth Q h) * (1 + epsC C) / 2 := by
      exact div_nonneg (mul_nonneg hw (add_nonneg zero_le_one he.1)) (by norm_num)
    have hfac : 1 ≤ 1 + epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹ := by
      nlinarith [mul_nonneg he.1 hrpow.1]
    calc
      depthMass t0 Q (latentDepth Q h) * (1 + epsC C) / 2 ≤
          (depthMass t0 Q (latentDepth Q h) * (1 + epsC C) / 2) *
            (1 + epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹) :=
              (le_mul_of_one_le_right hbase hfac)
      _ = (1 + epsC C) * (depthMass t0 Q (latentDepth Q h) *
            (1 + epsC C * (policyFactor zeta ^ latentDepth Q h)⁻¹) / 2) := by ring

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth policy Overlap assertion holds](goal). -/
lemma signedDepth_policyOverlap {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    PolicyOverlap (policyFactor zeta) (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) := by
  have heq := signedDepth_target_eq_actionOne
    (T := T) (Q := Q) (t0 := t0) (zeta := zeta) (C := C) (v := v)
      ht0 hzeta hC hQ
  have hbq := signedDepth_behaviour_eq_actionOne
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  unfold PolicyOverlap
  rw [heq, hbq]
  constructor
  · exact actionOnePolicy_policyVector (by constructor <;> norm_num)
  · intro x a
    have hL : 0 < policyFactor zeta := by
      unfold policyFactor
      exact Real.exp_pos _
    have hL1 : 1 < policyFactor zeta := by
      rw [policyFactor, Real.one_lt_exp_iff]
      exact hzeta
    cases a
    · simp only [actionOnePolicy, Bool.false_eq_true, if_false]
      simpa using mul_nonneg hL.le (sub_nonneg.mpr ((div_le_one hL).2 hL1.le))
    · simp [actionOnePolicy, hL.ne']

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth uniform Contraction assertion holds](goal). -/
lemma signedDepth_uniformContraction {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    UniformContraction (mixingAlpha t0) (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) := by
  intro p hp
  rcases hp with rfl | rfl
  · rw [signedDepth_behaviour_eq_actionOne ht0 hzeta hC hQ]
    apply signedDepth_uniformContraction_actionOne ht0 hzeta hC hQ
    have hL : 1 < policyFactor zeta := by
      rw [policyFactor, Real.one_lt_exp_iff]
      exact hzeta
    constructor
    · positivity
    · exact (div_le_one (by positivity)).2 hL.le
  · rw [signedDepth_target_eq_actionOne ht0 hzeta hC hQ]
    apply signedDepth_uniformContraction_actionOne ht0 hzeta hC hQ
    constructor <;> norm_num

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth reward Regression assertion holds](goal). -/
lemma signedDepth_rewardRegression {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (h : Fin (2 * (Q + 1))) :
    rewardRegression (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (0, h) =
      signedValue v * c0 t0 * signedValue (latentSign Q h) *
        (if latentDepth Q h = Q then 1 else 0) := by
  unfold rewardRegression
  rw [signedDepth_target_eq_actionOne ht0 hzeta hC hQ]
  rw [Fintype.sum_bool]
  simp [actionOnePolicy]
  change (∫ q, q.1 ∂((((signedDepthFinite T t0 zeta C Q v).kernel
    (0, h) true).map (fun p ↦ ((signedDepthFinite T t0 zeta C Q v).rew p.1, p.2))).toMeasure)) = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
    (measurable_fst.aestronglyMeasurable), PMF.integral_eq_sum]
  simp only [smul_eq_mul]
  simp_rw [signedDepthFinite_kernel_toReal ht0 hC]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  calc
    ∑ x, ∑ y, (signedDepthRewardWeight t0 Q v h x *
        signedDepthStateWeight t0 C Q h true y) *
          (signedDepthFinite T t0 zeta C Q v).rew x =
        (∑ x, (signedDepthFinite T t0 zeta C Q v).rew x *
          signedDepthRewardWeight t0 Q v h x) *
          (∑ y, signedDepthStateWeight t0 C Q h true y) := by
            rw [Finset.sum_comm, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = _ := by
      rw [sum_signedDepthStateWeight, mul_one]
      simp only [signedDepthFinite]
      simpa [mul_assoc] using
        (sum_rewardValue_mul_signedDepthRewardWeight t0 Q v h)

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth target Value assertion holds](goal). -/
lemma signedDepth_targetValue {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    targetValue (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) =
      signedValue v * c0 t0 * epsC C * depthMass t0 Q Q := by
  unfold targetValue
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  rw [signedDepth_target_eq_actionOne ht0 hzeta hC hQ]
  simp_rw [signedDepth_stationaryLaw_apply (r := (1 : ℝ)) ht0 hzeta hC hQ
    (by constructor <;> norm_num)]
  simp_rw [signedDepth_rewardRegression ht0 hzeta hC hQ]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ signedDepthStationaryWeight t0 C 1 Q h *
      (signedValue v * c0 t0 * signedValue (latentSign Q h) *
        if latentDepth Q h = Q then 1 else 0))
    (fun z ↦ signedDepthStationaryWeight t0 C 1 Q (depthSignEquiv Q z) *
      (signedValue v * c0 t0 * signedValue
        (latentSign Q (depthSignEquiv Q z)) *
          if latentDepth Q (depthSignEquiv Q z) = Q then 1 else 0))
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  let q : Fin (Q + 1) := ⟨Q, by omega⟩
  rw [Fintype.sum_eq_single q]
  · simp [q, signedDepthStationaryWeight, latentDepth_depthSignEquiv,
      latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one, signedValue]
    cases v <;> simp <;> ring
  · intro i hi
    have hiQ : (i : Nat) ≠ Q := by
      intro hv
      apply hi
      exact Fin.ext hv
    simp [signedDepthStationaryWeight, latentDepth_depthSignEquiv, hiQ]

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth behavior stationary eq init assertion holds](goal). -/
lemma signedDepth_behavior_stationary_eq_init {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (s : JointState 1 (2 * (Q + 1))) :
    stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
      (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b) s =
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).init s := by
  rcases s with ⟨x, h⟩
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  rw [signedDepth_behaviour_eq_actionOne ht0 hzeta hC hQ]
  rw [signedDepth_stationaryLaw_apply (r := 1 / policyFactor zeta) ht0 hzeta hC hQ]
  · rw [signedDepth_initial_apply ht0 hzeta hC hQ]
    simp [signedDepthStationaryWeight, one_div, inv_pow]
  · constructor
    · have hL0 : 0 < policyFactor zeta := by
        unfold policyFactor
        positivity
      exact (one_div_pos.mpr hL0).le
    · have hL : 1 < policyFactor zeta := by
        rw [policyFactor, Real.one_lt_exp_iff]
        exact hzeta
      exact (div_le_one (by positivity)).2 hL.le

/-- The signed-depth chronological law starts from its behavior-stationary distribution. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h Q condition](hyp:hQ). [the stated conclusion](goal). -/
lemma signedDepth_stationaryStart {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    StationaryStart (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) := by
  let r : ℝ := 1 / policyFactor zeta
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [r]
      exact (one_div_pos.mpr (by unfold policyFactor; positivity)).le
    · dsimp [r]
      have hL : 1 < policyFactor zeta := by
        rw [policyFactor, Real.one_lt_exp_iff]
        exact hzeta
      exact (div_le_one (by positivity)).2 hL.le
  have hd : IsStationary
      (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b)
      (fun s ↦ signedDepthStationaryWeight t0 C r Q s.2) := by
    rw [signedDepth_behaviour_eq_actionOne ht0 hzeta hC hQ]
    exact signedDepthStationaryWeight_isStationary ht0 hzeta hC hQ hr
  have hsel : IsStationary
      (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b)
      (stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b)) :=
    stationaryLaw_isStationary_of_exists ⟨_, hd⟩
  have heq : stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
      (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b) =
      (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).init := by
    funext s
    exact signedDepth_behavior_stationary_eq_init ht0 hzeta hC hQ s
  apply embed_stationaryStart (signedDepthFinite T t0 zeta C Q v)
  · rwa [heq] at hsel
  · exact heq

-- @node: lem:signed-depth-membership
/-- The signed-depth construction belongs to the model class and has the stated
stationary law, latent-overlap ratio, common revealed inputs, and target value. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h Q condition](hyp:hQ). [the stated conclusion](goal). -/
lemma signedDepth_membership {T Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hQ : 1 ≤ Q) (v : Bool) :
    LatentOverlapClass t0 zeta C (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ) ∧
    (∀ h : Fin (2 * (Q + 1)),
      stationaryLaw (policyKernel (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)
          (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ).b) (0, h) =
        depthMass t0 Q (latentDepth Q h) *
          (1 + signedValue (latentSign Q h) * epsC C *
            policyFactor zeta ^ (-(latentDepth Q h : ℤ))) / 2) ∧
    (∀ r : ℝ, r ∈ Set.Icc (0 : ℝ) 1 → ∀ h : Fin (2 * (Q + 1)),
      stationaryLaw (policyKernel (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)
          (actionOnePolicy r)) (0, h) =
        depthMass t0 Q (latentDepth Q h) *
          (1 + signedValue (latentSign Q h) * epsC C *
            r ^ latentDepth Q h) / 2) ∧
    (∀ s, stationaryLaw (policyKernel (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)
        (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ).e) s ≤
      (1 + epsC C) * stationaryLaw
        (policyKernel (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ)
          (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ).b) s) ∧
    1 + epsC C ≤ C ∧
    targetValue (signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ) =
      signedValue v * c0 t0 * epsC C * depthMass t0 Q Q := by
  have hfamily :
      signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ =
        signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ := rfl
  rw [hfamily]
  have hpolicy := signedDepth_policyOverlap (T := T) (Q := Q) (v := v)
    ht0 hzeta hC.le hQ
  have huniform := signedDepth_uniformContraction (T := T) (Q := Q) (v := v)
    ht0 hzeta hC.le hQ
  have hover : ∀ s, stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ).e) s ≤
      C * stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ)
        (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ).b) s := by
    intro s
    rcases s with ⟨x, h⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    rw [signedDepth_behavior_stationary_eq_init ht0 hzeta hC.le hQ]
    calc
      stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ)
          (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ).e) (0, h) ≤
          (1 + epsC C) * (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ).init (0, h) :=
        signedDepth_stationary_overlap_base ht0 hzeta hC.le hQ h
      _ ≤ C * (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ).init (0, h) := by
        apply mul_le_mul_of_nonneg_right (signedDepth_eps_bound hC.le)
        change 0 ≤ ((signedDepthFinite T t0 zeta C Q v).init (0, h)).toReal
        exact ENNReal.toReal_nonneg
  have hclass : LatentOverlapClass t0 zeta C (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC.le hQ) := {
    t0_pos := ht0
    zeta_pos := hzeta
    pomdp_kernel := embed_pomdpKernelLaw _
    sequential_ignorability := embed_sequentialIgnorability _
    stationary_start := signedDepth_stationaryStart ht0 hzeta hC.le hQ
    bounded_reward := embed_boundedReward _
    policy_overlap := hpolicy
    uniform_contraction := huniform
    latent_stationary_overlap := ⟨hC.le, hover⟩ }
  refine ⟨hclass, ?_, ?_, ?_, signedDepth_eps_bound hC.le,
    signedDepth_targetValue ht0 hzeta hC.le hQ⟩
  · intro h
    rw [signedDepth_behavior_stationary_eq_init ht0 hzeta hC.le hQ]
    exact signedDepth_initial_apply ht0 hzeta hC.le hQ h
  · intro r hr h
    exact signedDepth_stationaryLaw_apply ht0 hzeta hC.le hQ hr h
  · intro s
    rcases s with ⟨x, h⟩
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    rw [signedDepth_behavior_stationary_eq_init ht0 hzeta hC.le hQ]
    exact signedDepth_stationary_overlap_base ht0 hzeta hC.le hQ h


/-- At [a positive horizon](hyp:hT), the explicit signed-depth family is packaged as
[a model-class index](goal). -/
noncomputable def signedDepthModel (T Q : Nat) (t0 zeta C : ℝ) (v : Bool)
    (hT : 1 ≤ T) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hQ : 1 ≤ Q) :
    ModelIndex T t0 zeta C where
  horizon_pos := hT
  nX := 1
  nH := 2 * (Q + 1)
  raw := signedDepthFamily T t0 zeta C Q v ht0 hzeta hC hQ
  mem := (signedDepth_membership ht0 hzeta hC hQ v).1

end CausalSmith.Stat.PomdpLatentOverlapMinimax
