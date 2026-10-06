module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepth

set_option linter.style.longLine false

/-! # Normalization of the signed-depth raw weights -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators ENNReal

/-- Unpack the hidden coordinate into its depth and its two-valued sign bit. -/
def depthSignEquiv (Q : Nat) :
    Fin (Q + 1) × Fin 2 ≃ Fin (2 * (Q + 1)) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm (Q + 1) 2))

/-- [the latent Depth depth Sign Equiv assertion holds](goal). -/
lemma latentDepth_depthSignEquiv (Q : Nat) (z : Fin (Q + 1) × Fin 2) :
    latentDepth Q (depthSignEquiv Q z) = z.1.val := by
  simp [depthSignEquiv, latentDepth]
  omega

/-- [the latent Sign depth Sign Equiv zero assertion holds](goal). -/
lemma latentSign_depthSignEquiv_zero (Q : Nat) (j : Fin (Q + 1)) :
    latentSign Q (depthSignEquiv Q (j, 0)) = false := by
  simp [depthSignEquiv, latentSign]

/-- [the latent Sign depth Sign Equiv one assertion holds](goal). -/
lemma latentSign_depthSignEquiv_one (Q : Nat) (j : Fin (Q + 1)) :
    latentSign Q (depthSignEquiv Q (j, 1)) = true := by
  simp [depthSignEquiv, latentSign]

/-- Assuming [the ht0 condition](hyp:ht0), [the mixing Alpha pos assertion holds](goal). -/
lemma mixingAlpha_pos {t0 : ℝ} (ht0 : 0 < t0) : 0 < mixingAlpha t0 := by
  unfold mixingAlpha
  positivity

/-- Assuming [the ht0 condition](hyp:ht0), [the mixing Alpha lt one assertion holds](goal). -/
lemma mixingAlpha_lt_one {t0 : ℝ} (ht0 : 0 < t0) : mixingAlpha t0 < 1 := by
  rw [mixingAlpha, Real.exp_lt_one_iff]
  exact neg_neg_of_pos (one_div_pos.mpr ht0)

/-- Assuming [the h C condition](hyp:hC), [the eps C nonneg assertion holds](goal). -/
lemma epsC_nonneg {C : ℝ} (hC : 1 ≤ C) : 0 ≤ epsC C := by
  unfold epsC
  positivity

/-- [the eps C le half assertion holds](goal). -/
lemma epsC_le_half (C : ℝ) : epsC C ≤ 1 / 2 := min_le_right _ _

/-- Assuming [the ht0 condition](hyp:ht0), [the c0 nonneg assertion holds](goal). -/
lemma c0_nonneg {t0 : ℝ} (ht0 : 0 < t0) : 0 ≤ c0 t0 := by
  unfold c0
  linarith [mixingAlpha_lt_one ht0]

/-- Assuming [the ht0 condition](hyp:ht0), [the c0 le one assertion holds](goal). -/
lemma c0_le_one {t0 : ℝ} (ht0 : 0 < t0) : c0 t0 ≤ 1 := by
  unfold c0
  have := mixingAlpha_pos ht0
  linarith

/-- Assuming [the h C condition](hyp:hC), [the reset Sign Weight nonneg assertion holds](goal). -/
lemma resetSignWeight_nonneg {C : ℝ} (hC : 1 ≤ C) (u : Bool) :
    0 ≤ resetSignWeight C u := by
  cases u <;> simp [resetSignWeight, signedValue]
  · linarith [epsC_le_half C]
  · linarith [epsC_nonneg hC]

/-- [the sum reset Sign Weight assertion holds](goal). -/
lemma sum_resetSignWeight {C : ℝ} : ∑ u : Bool, resetSignWeight C u = 1 := by
  rw [Fintype.sum_bool]
  simp [resetSignWeight, signedValue]
  ring

/-- Assuming [the ht0 condition](hyp:ht0), [the signed Depth Reward Weight nonneg assertion holds](goal). -/
lemma signedDepthRewardWeight_nonneg {t0 : ℝ} (ht0 : 0 < t0) (Q : Nat)
    (v : Bool) (h : Fin (2 * (Q + 1))) (r : Fin 2) :
    0 ≤ signedDepthRewardWeight t0 Q v h r := by
  have hc0 := c0_nonneg ht0
  have hc1 := c0_le_one ht0
  generalize hu : latentSign Q h = u
  fin_cases r <;> cases v <;> cases u <;>
    by_cases hQ : latentDepth Q h = Q <;>
    simp [signedDepthRewardWeight, signedValue, hQ, hu] <;> linarith

/-- [the sum signed Depth Reward Weight assertion holds](goal). -/
lemma sum_signedDepthRewardWeight (t0 : ℝ) (Q : Nat) (v : Bool)
    (h : Fin (2 * (Q + 1))) :
    ∑ r : Fin 2, signedDepthRewardWeight t0 Q v h r = 1 := by
  rw [Fin.sum_univ_two]
  generalize hu : latentSign Q h = u
  cases v <;> cases u <;>
    by_cases hQ : latentDepth Q h = Q <;>
    simp [signedDepthRewardWeight, signedValue, hQ, hu] <;> ring

/-- Assuming [the hzeta condition](hyp:hzeta), [the signed Depth Behaviour Weight nonneg assertion holds](goal). -/
lemma signedDepthBehaviourWeight_nonneg {zeta : ℝ} (hzeta : 0 < zeta) (a : Bool) :
    0 ≤ signedDepthBehaviourWeight zeta a := by
  have hL : 1 < policyFactor zeta := by
    rw [policyFactor, Real.one_lt_exp_iff]
    exact hzeta
  cases a
  · simp [signedDepthBehaviourWeight]
    simpa only [one_div] using
      (div_le_one (by linarith : 0 < policyFactor zeta)).2 hL.le
  · simp [signedDepthBehaviourWeight]
    positivity

/-- [the sum signed Depth Behaviour Weight assertion holds](goal). -/
lemma sum_signedDepthBehaviourWeight (zeta : ℝ) :
    ∑ a : Bool, signedDepthBehaviourWeight zeta a = 1 := by
  rw [Fintype.sum_bool]
  simp [signedDepthBehaviourWeight]

/-- Assuming [the ht0 condition](hyp:ht0), [the h C condition](hyp:hC), [the h' condition](hyp:h'), [the signed Depth State Weight nonneg assertion holds](goal). -/
lemma signedDepthStateWeight_nonneg {t0 C : ℝ} (ht0 : 0 < t0) (hC : 1 ≤ C)
    (Q : Nat) (h : Fin (2 * (Q + 1))) (a : Bool) (h' : Fin (2 * (Q + 1))) :
    0 ≤ signedDepthStateWeight t0 C Q h a h' := by
  have ha0 : 0 ≤ mixingAlpha t0 := (mixingAlpha_pos ht0).le
  have ha1 : 0 ≤ 1 - mixingAlpha t0 := sub_nonneg.mpr (mixingAlpha_lt_one ht0).le
  have hr : 0 ≤ resetSignWeight C (latentSign Q h') := resetSignWeight_nonneg hC _
  unfold signedDepthStateWeight
  split_ifs <;> positivity

/-- Summing the two sign targets at a fixed target depth leaves only the reset or advance depth
mass. [the stated conclusion](goal). -/
lemma sum_signedDepthStateWeight_at_depth {t0 C : ℝ} (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) (j' : Fin (Q + 1)) :
    (∑ u' : Fin 2, signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (j', u'))) =
      if latentDepth Q h = Q then
        if j'.val = 0 then 1 else 0
      else
        (if j'.val = 0 then 1 - mixingAlpha t0 else 0) +
          (if j'.val = latentDepth Q h + 1 then mixingAlpha t0 else 0) := by
  rw [Fin.sum_univ_two]
  by_cases hterm : latentDepth Q h = Q
  · by_cases hj0 : j'.val = 0
    · cases a <;> generalize hu : latentSign Q h = u <;> cases u <;>
        simp [signedDepthStateWeight, latentDepth_depthSignEquiv,
          latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one,
          resetSignWeight, signedValue, hu, hterm, Fin.ext_iff, hj0] <;> ring
    · cases a <;> generalize hu : latentSign Q h = u <;> cases u <;>
        simp [signedDepthStateWeight, latentDepth_depthSignEquiv,
          latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one,
          resetSignWeight, signedValue, hu, hterm, Fin.ext_iff, hj0]
  · by_cases hj0 : j'.val = 0 <;>
      by_cases hjnext : j'.val = latentDepth Q h + 1 <;>
      cases a <;> generalize hu : latentSign Q h = u <;> cases u <;>
      simp [signedDepthStateWeight, latentDepth_depthSignEquiv,
        latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one,
        resetSignWeight, signedValue, hu, hterm, Fin.ext_iff, hj0, hjnext] <;> ring

/-- [the sum signed Depth State Weight assertion holds](goal). -/
lemma sum_signedDepthStateWeight (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) :
    ∑ h' : Fin (2 * (Q + 1)), signedDepthStateWeight t0 C Q h a h' = 1 := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h' ↦ signedDepthStateWeight t0 C Q h a h')
    (fun z ↦ signedDepthStateWeight t0 C Q h a (depthSignEquiv Q z))
    (fun h' ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_signedDepthStateWeight_at_depth]
  by_cases hterm : latentDepth Q h = Q
  · simp [hterm]
  · have hjlt : latentDepth Q h < Q := by
      have hjle : latentDepth Q h ≤ Q := by
        unfold latentDepth
        omega
      omega
    simp [hterm, Finset.sum_add_distrib]
    have hnext : latentDepth Q h + 1 < Q + 1 := by omega
    let jnext : Fin (Q + 1) := ⟨latentDepth Q h + 1, hnext⟩
    have hind (j' : Fin (Q + 1)) :
        (j'.val = latentDepth Q h + 1) = (j' = jnext) := by
      apply propext
      simp [jnext, Fin.ext_iff]
    simp_rw [hind]
    simp

/-- Assuming [the ht0 condition](hyp:ht0), [the h C condition](hyp:hC), [the signed Depth Kernel Raw nonneg assertion holds](goal). -/
lemma signedDepthKernelRaw_nonneg {t0 C : ℝ} (ht0 : 0 < t0) (hC : 1 ≤ C)
    (Q : Nat) (v : Bool) (h : Fin (2 * (Q + 1))) (a : Bool)
    (p : Fin 2 × JointState 1 (2 * (Q + 1))) :
    0 ≤ signedDepthRewardWeight t0 Q v h p.1 *
      signedDepthStateWeight t0 C Q h a p.2.2 :=
  mul_nonneg (signedDepthRewardWeight_nonneg ht0 Q v h p.1)
    (signedDepthStateWeight_nonneg ht0 hC Q h a p.2.2)

/-- [the sum signed Depth Kernel Raw assertion holds](goal). -/
lemma sum_signedDepthKernelRaw (t0 C : ℝ) (Q : Nat) (v : Bool)
    (h : Fin (2 * (Q + 1))) (a : Bool) :
    ∑ p : Fin 2 × JointState 1 (2 * (Q + 1)),
      signedDepthRewardWeight t0 Q v h p.1 *
        signedDepthStateWeight t0 C Q h a p.2.2 = 1 := by
  rw [Fintype.sum_prod_type]
  apply Eq.trans ?_ (sum_signedDepthRewardWeight t0 Q v h)
  apply Finset.sum_congr rfl
  intro r _
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_nsmul]
  rw [← Finset.mul_sum, sum_signedDepthStateWeight, mul_one]

/-- Assuming [the ht0 condition](hyp:ht0), [the depth Mass nonneg assertion holds](goal). -/
lemma depthMass_nonneg {t0 : ℝ} (ht0 : 0 < t0) (Q j : Nat) :
    0 ≤ depthMass t0 Q j := by
  have ha0 := (mixingAlpha_pos ht0).le
  have ha1 := (mixingAlpha_lt_one ht0).le
  have hden : 0 < 1 - mixingAlpha t0 ^ (Q + 1) := by
    have hp := pow_lt_one₀ ha0 (mixingAlpha_lt_one ht0) (by omega : Q + 1 ≠ 0)
    linarith
  unfold depthMass
  positivity

/-- Assuming [the ht0 condition](hyp:ht0), [the sum depth Mass assertion holds](goal). -/
lemma sum_depthMass {t0 : ℝ} (ht0 : 0 < t0) (Q : Nat) :
    ∑ j : Fin (Q + 1), depthMass t0 Q j.val = 1 := by
  let alpha := mixingAlpha t0
  have halpha : alpha ≠ 1 := ne_of_lt (mixingAlpha_lt_one ht0)
  have hden : 1 - alpha ^ (Q + 1) ≠ 0 := by
    have hp : alpha ^ (Q + 1) < 1 :=
      pow_lt_one₀ (mixingAlpha_pos ht0).le (mixingAlpha_lt_one ht0) (by omega)
    linarith
  rw [Fin.sum_univ_eq_sum_range]
  simp only [depthMass]
  have hterm (j : Nat) :
      (1 - mixingAlpha t0) * mixingAlpha t0 ^ j /
          (1 - mixingAlpha t0 ^ (Q + 1)) =
        ((1 - mixingAlpha t0) / (1 - mixingAlpha t0 ^ (Q + 1))) *
          mixingAlpha t0 ^ j := by ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  rw [geom_sum_eq halpha (Q + 1)]
  change (1 - alpha) / (1 - alpha ^ (Q + 1)) *
      ((alpha ^ (Q + 1) - 1) / (alpha - 1)) = 1
  field_simp
  ring

/-- [the sum signed Depth Init Weight at depth assertion holds](goal). -/
lemma sum_signedDepthInitWeight_at_depth (t0 zeta C : ℝ) (Q : Nat)
    (j : Fin (Q + 1)) :
    ∑ u : Fin 2, signedDepthInitWeight t0 zeta C Q (depthSignEquiv Q (j, u)) =
      depthMass t0 Q j.val := by
  rw [Fin.sum_univ_two]
  simp [signedDepthInitWeight, latentDepth_depthSignEquiv,
    latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one, signedValue]
  ring

/-- Assuming [the ht0 condition](hyp:ht0), [the sum signed Depth Init Weight assertion holds](goal). -/
lemma sum_signedDepthInitWeight {t0 zeta C : ℝ} (ht0 : 0 < t0) (Q : Nat) :
    ∑ h : Fin (2 * (Q + 1)), signedDepthInitWeight t0 zeta C Q h = 1 := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ signedDepthInitWeight t0 zeta C Q h)
    (fun z ↦ signedDepthInitWeight t0 zeta C Q (depthSignEquiv Q z))
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_signedDepthInitWeight_at_depth]
  exact sum_depthMass ht0 Q

/-- Assuming [the ht0 condition](hyp:ht0), [the hzeta condition](hyp:hzeta), [the h C condition](hyp:hC), [the signed Depth Init Weight nonneg assertion holds](goal). -/
lemma signedDepthInitWeight_nonneg {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (Q : Nat)
    (h : Fin (2 * (Q + 1))) : 0 ≤ signedDepthInitWeight t0 zeta C Q h := by
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor]
    exact (Real.one_le_exp_iff.mpr hzeta.le)
  have hpow : policyFactor zeta ^ (-(latentDepth Q h : ℤ)) ≤ 1 :=
    zpow_le_one_of_nonpos₀ hL (by omega)
  have hpow0 : 0 ≤ policyFactor zeta ^ (-(latentDepth Q h : ℤ)) := by positivity
  have he0 := epsC_nonneg hC
  have he1 := epsC_le_half C
  have hepow : epsC C * policyFactor zeta ^ (-(latentDepth Q h : ℤ)) ≤ 1 := by
    calc
      epsC C * policyFactor zeta ^ (-(latentDepth Q h : ℤ)) ≤ epsC C :=
        mul_le_of_le_one_right he0 hpow
      _ ≤ 1 / 2 := he1
      _ ≤ 1 := by norm_num
  have hfac : 0 ≤ 1 + signedValue (latentSign Q h) * epsC C *
      policyFactor zeta ^ (-(latentDepth Q h : ℤ)) := by
    cases hs : latentSign Q h
    · simp only [signedValue, Bool.false_eq_true, if_false, neg_mul]
      nlinarith
    · simp only [signedValue, if_true, one_mul]
      positivity
  unfold signedDepthInitWeight
  exact div_nonneg (mul_nonneg (depthMass_nonneg ht0 Q _) hfac) (by norm_num)

/-- The normalized kernel stored in `signedDepthFinite` is pointwise its raw reward/transition
product. [the ht0 condition](hyp:ht0); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthFinite_kernel_toReal {T Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hC : 1 ≤ C) (v : Bool)
    (h : Fin (2 * (Q + 1))) (a : Bool)
    (p : Fin 2 × JointState 1 (2 * (Q + 1))) :
    ((signedDepthFinite T t0 zeta C Q v).kernel (0, h) a p).toReal =
      signedDepthRewardWeight t0 Q v h p.1 *
        signedDepthStateWeight t0 C Q h a p.2.2 := by
  simp only [signedDepthFinite]
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one
    (fun p : Fin 2 × JointState 1 (2 * (Q + 1)) ↦
      signedDepthRewardWeight t0 Q v h p.1 * signedDepthStateWeight t0 C Q h a p.2.2)
    (signedDepthKernelRaw_nonneg ht0 hC Q v h a)
    (sum_signedDepthKernelRaw t0 C Q v h a)]
  rw [ENNReal.toReal_ofReal (signedDepthKernelRaw_nonneg ht0 hC Q v h a p)]

/-- The normalized initial PMF is pointwise the signed-depth initial raw weight. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthFinite_init_toReal {T Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C) (v : Bool)
    (h : Fin (2 * (Q + 1))) :
    ((signedDepthFinite T t0 zeta C Q v).init (0, h)).toReal =
      signedDepthInitWeight t0 zeta C Q h := by
  have hnonneg : ∀ s : JointState 1 (2 * (Q + 1)),
      0 ≤ signedDepthInitWeight t0 zeta C Q s.2 :=
    fun s ↦ signedDepthInitWeight_nonneg ht0 hzeta hC Q s.2
  have hsum : ∑ s : JointState 1 (2 * (Q + 1)),
      signedDepthInitWeight t0 zeta C Q s.2 = 1 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_nsmul]
    exact sum_signedDepthInitWeight ht0 Q
  simp only [signedDepthFinite]
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _ hnonneg hsum]
  rw [ENNReal.toReal_ofReal (signedDepthInitWeight_nonneg ht0 hzeta hC Q h)]

/-- The normalized behavior PMF is pointwise the raw Bernoulli action weight. [the hzeta condition](hyp:hzeta). [the stated conclusion](goal). -/
lemma signedDepthFinite_b_toReal {T Q : Nat} {t0 zeta C : ℝ}
    (hzeta : 0 < zeta) (v : Bool) (a : Bool) :
    ((signedDepthFinite T t0 zeta C Q v).b 0 a).toReal =
      signedDepthBehaviourWeight zeta a := by
  simp only [signedDepthFinite]
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
    (signedDepthBehaviourWeight_nonneg hzeta) (sum_signedDepthBehaviourWeight zeta)]
  rw [ENNReal.toReal_ofReal (signedDepthBehaviourWeight_nonneg hzeta a)]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
