module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthWeights

/-! # Stationarity and contraction for the signed-depth family -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- For [the t0 input](hyp:t0), [the C input](hyp:C), [the r input](hyp:r), [the Q input](hyp:Q), [the h input](hyp:h), [this defines the signed Depth Stationary Weight object](goal). -/
noncomputable def signedDepthStationaryWeight (t0 C r : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) : ℝ :=
  depthMass t0 Q (latentDepth Q h) *
    (1 + signedValue (latentSign Q h) * epsC C * r ^ latentDepth Q h) / 2

/-- Assuming [the hr condition](hyp:hr), [the action One Policy policy Vector assertion holds](goal). -/
lemma actionOnePolicy_policyVector {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    PolicyVector (actionOnePolicy r) := by
  intro x
  constructor
  · intro a
    cases a <;> simp [actionOnePolicy, hr.1, hr.2, sub_nonneg.mpr hr.2]
  · simp [actionOnePolicy]

/-- Assuming [the ht0 condition](hyp:ht0), [the h C condition](hyp:hC), [the hr condition](hyp:hr), [the signed Depth Stationary Weight probability Vector assertion holds](goal). -/
lemma signedDepthStationaryWeight_probabilityVector {t0 C r : ℝ} {Q : Nat}
    (ht0 : 0 < t0) (hC : 1 ≤ C) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ProbabilityVector (fun s : JointState 1 (2 * (Q + 1)) ↦
      signedDepthStationaryWeight t0 C r Q s.2) := by
  constructor
  · intro s
    unfold signedDepthStationaryWeight
    apply div_nonneg
    · apply mul_nonneg (depthMass_nonneg ht0 _ _)
      cases hsign : latentSign Q s.2 <;> simp [signedValue, hsign]
      · have hp : 0 ≤ r ^ latentDepth Q s.2 := pow_nonneg hr.1 _
        have he := epsC_le_half C
        nlinarith [mul_nonneg (epsC_nonneg hC) hp,
          mul_le_mul_of_nonneg_left
            (pow_le_one₀ (n := latentDepth Q s.2) hr.1 hr.2) (epsC_nonneg hC)]
      · have hp : 0 ≤ r ^ latentDepth Q s.2 := pow_nonneg hr.1 _
        exact add_nonneg zero_le_one (mul_nonneg (epsC_nonneg hC) hp)
    · norm_num
  · rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_one]
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm
      (fun s ↦ signedDepthStationaryWeight t0 C r Q s)
      (fun z ↦ signedDepthStationaryWeight t0 C r Q (depthSignEquiv Q z))
      (fun s ↦ by rw [Equiv.apply_symm_apply])]
    simp only [signedDepthStationaryWeight, latentDepth_depthSignEquiv]
    rw [Fintype.sum_prod_type]
    have hsignsum (j : Fin (Q + 1)) :
        ∑ u : Fin 2, (1 + signedValue (latentSign Q (depthSignEquiv Q (j, u))) *
          epsC C * r ^ (j : Nat)) / 2 = 1 := by
      rw [Fin.sum_univ_two]
      simp [latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one, signedValue]
      ring
    apply Eq.trans ?_ (sum_depthMass ht0 Q)
    apply Finset.sum_congr rfl
    intro j _
    calc
      ∑ u : Fin 2, depthMass t0 Q (j : Nat) *
          (1 + signedValue (latentSign Q (depthSignEquiv Q (j, u))) *
            epsC C * r ^ (j : Nat)) / 2 =
          depthMass t0 Q (j : Nat) *
            ∑ u : Fin 2, (1 + signedValue (latentSign Q (depthSignEquiv Q (j, u))) *
              epsC C * r ^ (j : Nat)) / 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro u _
            ring
      _ = depthMass t0 Q (j : Nat) := by rw [hsignsum, mul_one]

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth policy Kernel apply assertion holds](goal). -/
lemma signedDepth_policyKernel_apply {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) (p : Policy 1)
    (h h' : Fin (2 * (Q + 1))) :
    policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) p (0, h) (0, h') =
      ∑ a : Bool, p 0 a * signedDepthStateWeight t0 C Q h a h' := by
  unfold policyKernel signedDepthFamilyAtLeastOne embed
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  change ((((signedDepthFinite T t0 zeta C Q v).kernel (0, h) a).map
      (fun q ↦ ((signedDepthFinite T t0 zeta C Q v).rew q.1, q.2))).toMeasure
        {q | q.2 = (0, h')}).toReal = _
  rw [PMF.toMeasure_map_apply _ _ _ (measurable_of_finite _)
    (by measurability : MeasurableSet {q : Step 1 (2 * (Q + 1)) | q.2 = (0, h')})]
  rw [PMF.toMeasure_apply_fintype, Fintype.sum_prod_type]
  classical
  simp only [Set.indicator, Set.mem_preimage, Set.mem_ofPred_eq, Prod.mk.injEq,
    true_and, Pi.zero_apply]
  rw [ENNReal.toReal_sum]
  · calc
      ∑ x, (∑ y, if y = (0, h') then
          (signedDepthFinite T t0 zeta C Q v).kernel (0, h) a (x, y) else 0).toReal =
          ∑ x, ((signedDepthFinite T t0 zeta C Q v).kernel
            (0, h) a (x, (0, h'))).toReal := by
            apply Finset.sum_congr rfl
            intro x _
            rw [ENNReal.toReal_sum (fun y _ ↦ by
              split <;> simp [PMF.apply_ne_top])]
            simp only [apply_ite, ENNReal.toReal_zero]
            rw [Finset.sum_ite_eq' Finset.univ
              ((0, h') : JointState 1 (2 * (Q + 1)))]
            simp
      _ = signedDepthStateWeight t0 C Q h a h' := by
        simp_rw [signedDepthFinite_kernel_toReal ht0 hC]
        rw [← Finset.sum_mul, sum_signedDepthRewardWeight, one_mul]
  · intro x _
    apply ENNReal.sum_ne_top.mpr
    intro y _
    split <;> simp [PMF.apply_ne_top]

/-- Assuming [the ht0 condition](hyp:ht0), [the depth Mass reset balance assertion holds](goal). -/
lemma depthMass_reset_balance {t0 : ℝ} (ht0 : 0 < t0) (Q : Nat) :
    (∑ j : Fin (Q + 1), if (j : Nat) = Q then depthMass t0 Q j
      else (1 - mixingAlpha t0) * depthMass t0 Q j) = depthMass t0 Q 0 := by
  have ha0 := mixingAlpha_pos ht0
  have ha1 := mixingAlpha_lt_one ht0
  have hden : 1 - mixingAlpha t0 ^ (Q + 1) ≠ 0 := by
    have hp : mixingAlpha t0 ^ (Q + 1) < 1 :=
      pow_lt_one₀ ha0.le ha1 (by omega)
    linarith
  let q : Fin (Q + 1) := ⟨Q, by omega⟩
  calc
    (∑ j : Fin (Q + 1), if (j : Nat) = Q then depthMass t0 Q j
        else (1 - mixingAlpha t0) * depthMass t0 Q j) =
        ∑ j : Fin (Q + 1), ((1 - mixingAlpha t0) * depthMass t0 Q j +
          if j = q then mixingAlpha t0 * depthMass t0 Q j else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases hj : (j : Nat) = Q
            · have hjq : j = q := Fin.ext hj
              have hqval : (q : Nat) = Q := rfl
              simp [hjq, hqval]
              ring
            · have hjq : j ≠ q := by
                intro h
                apply hj
                simpa [q] using congrArg Fin.val h
              simp [hj, hjq]
    _ = (1 - mixingAlpha t0) * ∑ j : Fin (Q + 1), depthMass t0 Q j +
          mixingAlpha t0 * depthMass t0 Q Q := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_ite_eq' Finset.univ q]
      simp [q]
    _ = (1 - mixingAlpha t0) + mixingAlpha t0 * depthMass t0 Q Q := by
      rw [sum_depthMass ht0, mul_one]
    _ = depthMass t0 Q 0 := by
      unfold depthMass
      field_simp [hden]
      ring

/-- [the latent Depth le assertion holds](goal). -/
lemma latentDepth_le (Q : Nat) (h : Fin (2 * (Q + 1))) : latentDepth Q h ≤ Q := by
  unfold latentDepth
  omega

/-- [the depth Mass succ assertion holds](goal). -/
lemma depthMass_succ (t0 : ℝ) (Q j : Nat) :
    depthMass t0 Q (j + 1) = mixingAlpha t0 * depthMass t0 Q j := by
  unfold depthMass
  rw [pow_succ]
  ring

/-- For [the C input](hyp:C), [the Q input](hyp:Q), [the s' input](hyp:s'), [this defines the signed Depth Refresh object](goal). -/
noncomputable def signedDepthRefresh (C : ℝ) (Q : Nat)
    (s' : JointState 1 (2 * (Q + 1))) : ℝ :=
  if latentDepth Q s'.2 = 0 then resetSignWeight C (latentSign Q s'.2) else 0

/-- For [the C input](hyp:C), [the r input](hyp:r), [the Q input](hyp:Q), [the s input](hyp:s), [the s' input](hyp:s'), [this defines the signed Depth Residual Kernel object](goal). -/
noncomputable def signedDepthResidualKernel (C r : ℝ) (Q : Nat)
    (s s' : JointState 1 (2 * (Q + 1))) : ℝ :=
  if latentDepth Q s.2 = Q then signedDepthRefresh C Q s'
  else if latentDepth Q s'.2 = latentDepth Q s.2 + 1 then
    if latentSign Q s'.2 = latentSign Q s.2 then r + (1 - r) / 2 else (1 - r) / 2
  else 0

/-- Assuming [the h C condition](hyp:hC), [the hr condition](hyp:hr), [the signed Depth Residual Kernel probability Vector assertion holds](goal). -/
lemma signedDepthResidualKernel_probabilityVector {C r : ℝ} {Q : Nat}
    (hC : 1 ≤ C) (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (s : JointState 1 (2 * (Q + 1))) :
    ProbabilityVector (signedDepthResidualKernel C r Q s) := by
  constructor
  · intro s'
    have hmr : 0 ≤ 1 - r := sub_nonneg.mpr hr.2
    by_cases hterm : latentDepth Q s.2 = Q
    · rw [signedDepthResidualKernel, if_pos hterm]
      unfold signedDepthRefresh
      split_ifs
      · exact resetSignWeight_nonneg hC _
      · exact le_rfl
    · rw [signedDepthResidualKernel, if_neg hterm]
      by_cases hadv : latentDepth Q s'.2 = latentDepth Q s.2 + 1
      · rw [if_pos hadv]
        by_cases hsign : latentSign Q s'.2 = latentSign Q s.2
        · rw [if_pos hsign]
          exact add_nonneg hr.1 (div_nonneg hmr (by norm_num))
        · rw [if_neg hsign]
          exact div_nonneg hmr (by norm_num)
      · rw [if_neg hadv]
  · rcases s with ⟨x, h⟩
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_one]
    rw [Fintype.sum_equiv (depthSignEquiv Q).symm
      (fun h' ↦ signedDepthResidualKernel C r Q (x, h) (0, h'))
      (fun z ↦ signedDepthResidualKernel C r Q (x, h) (0, depthSignEquiv Q z))
      (fun h' ↦ by rw [Equiv.apply_symm_apply])]
    rw [Fintype.sum_prod_type]
    by_cases hterm : latentDepth Q h = Q
    · rw [Fintype.sum_eq_single (0 : Fin (Q + 1))]
      · simp [signedDepthResidualKernel, hterm, signedDepthRefresh,
          latentDepth_depthSignEquiv, latentSign_depthSignEquiv_zero,
          latentSign_depthSignEquiv_one]
        simpa [Fin.sum_univ_two, add_comm] using (sum_resetSignWeight (C := C))
      · intro i hi
        have hi0 : (i : Nat) ≠ 0 := by
          intro hv
          apply hi
          exact Fin.ext hv
        simp [signedDepthResidualKernel, hterm, signedDepthRefresh,
          latentDepth_depthSignEquiv, hi0]
    · have hlt : latentDepth Q h < Q := lt_of_le_of_ne (latentDepth_le Q h) hterm
      let j : Fin (Q + 1) := ⟨latentDepth Q h + 1, by omega⟩
      rw [Fintype.sum_eq_single j]
      · simp [signedDepthResidualKernel, hterm, latentDepth_depthSignEquiv, j,
          latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one]
        cases hs : latentSign Q h <;> simp [hs]
        <;> ring
      · intro i hij
        have hne : (i : Nat) ≠ latentDepth Q h + 1 := by
          intro hi
          apply hij
          apply Fin.ext
          simpa [j] using hi
        simp [signedDepthResidualKernel, hterm, latentDepth_depthSignEquiv, hne]

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the hr condition](hyp:hr), [the signed Depth policy Kernel refresh assertion holds](goal). -/
lemma signedDepth_policyKernel_refresh {T Q : Nat} {t0 zeta C r : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r) =
      fun s s' ↦ (1 - mixingAlpha t0) * signedDepthRefresh C Q s' +
        mixingAlpha t0 * signedDepthResidualKernel C r Q s s' := by
  funext s s'
  rcases s with ⟨x, h⟩
  rcases s' with ⟨x', h'⟩
  have hx : x = 0 := Subsingleton.elim _ _
  have hx' : x' = 0 := Subsingleton.elim _ _
  subst x
  subst x'
  rw [signedDepth_policyKernel_apply ht0 hzeta hC hQ]
  simp [signedDepthStateWeight, signedDepthRefresh, signedDepthResidualKernel,
    actionOnePolicy]
  split_ifs <;> ring

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the hr condition](hyp:hr), [the signed Depth uniform Contraction action One assertion holds](goal). -/
lemma signedDepth_uniformContraction_actionOne {T Q : Nat} {t0 zeta C r : ℝ}
    {v : Bool} (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ∀ nu nu', ProbabilityVector nu → ProbabilityVector nu' →
      tvNorm (applyKernel nu
          (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r)) -
        applyKernel nu'
          (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r))) ≤
        mixingAlpha t0 * tvNorm (nu - nu') := by
  rw [signedDepth_policyKernel_refresh ht0 hzeta hC hQ hr]
  exact tvNorm_contraction_of_refresh (mixingAlpha t0) (mixingAlpha_pos ht0).le
    (signedDepthRefresh C Q) (signedDepthResidualKernel C r Q)
    (signedDepthResidualKernel_probabilityVector hC hr)

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the hr condition](hyp:hr), [the signed Depth Stationary Weight is Stationary assertion holds](goal). -/
lemma signedDepthStationaryWeight_isStationary {T Q : Nat} {t0 zeta C r : ℝ}
    {v : Bool} (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    IsStationary
      (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r))
      (fun s ↦ signedDepthStationaryWeight t0 C r Q s.2) := by
  refine ⟨signedDepthStationaryWeight_probabilityVector ht0 hC hr, ?_⟩
  intro s'
  rcases s' with ⟨x', h'⟩
  have hx' : x' = 0 := Subsingleton.elim _ _
  subst x'
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_one]
  simp_rw [signedDepth_policyKernel_apply ht0 hzeta hC hQ]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ signedDepthStationaryWeight t0 C r Q h *
      ∑ a : Bool, actionOnePolicy r 0 a * signedDepthStateWeight t0 C Q h a h')
    (fun z ↦ signedDepthStationaryWeight t0 C r Q (depthSignEquiv Q z) *
      ∑ a : Bool, actionOnePolicy r 0 a *
        signedDepthStateWeight t0 C Q (depthSignEquiv Q z) a h')
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp only [signedDepthStationaryWeight, latentDepth_depthSignEquiv]
  by_cases hj' : latentDepth Q h' = 0
  · calc
      (∑ j : Fin (Q + 1), ∑ u : Fin 2,
          depthMass t0 Q (j : Nat) *
              (1 + signedValue (latentSign Q (depthSignEquiv Q (j, u))) *
                epsC C * r ^ (j : Nat)) / 2 *
            ∑ a : Bool, actionOnePolicy r 0 a *
              signedDepthStateWeight t0 C Q (depthSignEquiv Q (j, u)) a h') =
          ∑ j : Fin (Q + 1),
            (if (j : Nat) = Q then depthMass t0 Q j
              else (1 - mixingAlpha t0) * depthMass t0 Q j) *
                resetSignWeight C (latentSign Q h') := by
          apply Finset.sum_congr rfl
          intro j _
          simp [signedDepthStateWeight, hj', actionOnePolicy,
            latentDepth_depthSignEquiv, latentSign_depthSignEquiv_zero,
            latentSign_depthSignEquiv_one, signedValue]
          ring
      _ = depthMass t0 Q 0 * resetSignWeight C (latentSign Q h') := by
        rw [← Finset.sum_mul, depthMass_reset_balance ht0]
      _ = depthMass t0 Q (latentDepth Q h') *
          (1 + signedValue (latentSign Q h') * epsC C *
            r ^ latentDepth Q h') / 2 := by
        rw [hj']
        simp [resetSignWeight]
        ring
  · let d := latentDepth Q h'
    have hd0 : 0 < d := Nat.pos_of_ne_zero hj'
    have hdQ : d ≤ Q := latentDepth_le Q h'
    let j : Fin (Q + 1) := ⟨d - 1, by omega⟩
    have hjval : (j : Nat) + 1 = d := by dsimp [j]; omega
    have hjQ : (j : Nat) ≠ Q := by omega
    have htarget : latentDepth Q h' = (j : Nat) + 1 := by simpa [d] using hjval.symm
    rw [Fintype.sum_eq_single j]
    · simp [signedDepthStateWeight, hj', actionOnePolicy,
        latentDepth_depthSignEquiv, latentSign_depthSignEquiv_zero,
        latentSign_depthSignEquiv_one, signedValue, hjQ, htarget]
      rw [depthMass_succ, pow_succ]
      cases hs : latentSign Q h' <;> simp [signedValue, hs]
      <;> ring
    · intro i hij
      have hne : d ≠ (i : Nat) + 1 := by
        intro heq
        apply hij
        apply Fin.ext
        omega
      have hne' : latentDepth Q h' ≠ (i : Nat) + 1 := by simpa [d] using hne
      simp [signedDepthStateWeight, hj', actionOnePolicy,
        latentDepth_depthSignEquiv, hne']

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the hr condition](hyp:hr), [the signed Depth stationary Law apply assertion holds](goal). -/
lemma signedDepth_stationaryLaw_apply {T Q : Nat} {t0 zeta C r : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q)
    (hr : r ∈ Set.Icc (0 : ℝ) 1)
    (h : Fin (2 * (Q + 1))) :
    stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (actionOnePolicy r)) (0, h) = signedDepthStationaryWeight t0 C r Q h := by
  let d : JointState 1 (2 * (Q + 1)) → ℝ :=
    fun s ↦ signedDepthStationaryWeight t0 C r Q s.2
  have hd : IsStationary
      (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r)) d :=
    signedDepthStationaryWeight_isStationary ht0 hzeta hC hQ hr
  have hsel : IsStationary
      (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r))
      (stationaryLaw (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ)
        (actionOnePolicy r))) := stationaryLaw_isStationary_of_exists ⟨d, hd⟩
  have heq := stationary_unique_of_contraction
    (policyKernel (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ) (actionOnePolicy r))
    (mixingAlpha t0) (mixingAlpha_lt_one ht0)
    (signedDepth_uniformContraction_actionOne ht0 hzeta hC hQ hr) hsel hd
  change stationaryLaw _ (0, h) = d (0, h)
  rw [heq]

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth behaviour eq action One assertion holds](goal). -/
lemma signedDepth_behaviour_eq_actionOne {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).b =
      actionOnePolicy (1 / policyFactor zeta) := by
  funext x a
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  change ((signedDepthFinite T t0 zeta C Q v).b 0 a).toReal = _
  rw [signedDepthFinite_b_toReal hzeta v a]
  cases a <;> simp [signedDepthBehaviourWeight, actionOnePolicy]

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the h Q condition](hyp:hQ), [the signed Depth target eq action One assertion holds](goal). -/
lemma signedDepth_target_eq_actionOne {T Q : Nat} {t0 zeta C : ℝ} {v : Bool}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (hQ : 1 ≤ Q) :
    (signedDepthFamilyAtLeastOne T t0 zeta C Q v ht0 hzeta hC hQ).e = actionOnePolicy 1 := by
  funext x a
  have hx : x = 0 := Subsingleton.elim _ _
  subst x
  change (pmfOfRealWeight (fun a : Bool ↦ if a then 1 else 0) a).toReal = _
  have hnonneg : ∀ a : Bool, 0 ≤ (if a then (1 : ℝ) else 0) := by intro a; cases a <;> simp
  have hsum : ∑ a : Bool, (if a then (1 : ℝ) else 0) = 1 := by simp
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hnonneg hsum a,
    ENNReal.toReal_ofReal (hnonneg a)]
  cases a <;> simp [actionOnePolicy]


end CausalSmith.Stat.PomdpLatentOverlapMinimax
