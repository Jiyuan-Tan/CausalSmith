import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthFilterRecursion

set_option linter.style.longLine false

/-! # Depthwise sign invariant for the signed-depth observed filter -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators

/-- The action-history factor appropriate to a hidden depth `j` after `k` observations. -/
noncomputable def signedDepthActionFactor (zeta : ℝ) (j : Nat) {k : Nat}
    (o : Fin k → Bool × Fin 2) : ℝ :=
  policyFactor zeta ^ (-(j - min j k : ℤ)) *
    ∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ k - min j k ≤ i.val),
      if (o i).1 then 1 else 0

/-- Unsigned filter mass at one decoded depth. -/
noncomputable def signedDepthUnsignedMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (j : Fin (Q + 1)) : ℝ :=
  ∑ u : Fin 2,
    signedDepthFilterMass N t0 zeta C Q v o (depthSignEquiv Q (j, u))

/-- Signed filter mass at one decoded depth. -/
noncomputable def signedDepthSignedMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (j : Fin (Q + 1)) : ℝ :=
  ∑ u : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (j, u))) *
    signedDepthFilterMass N t0 zeta C Q v o (depthSignEquiv Q (j, u))

/-- At an empty observed history, the signed-to-unsigned ratio at depth `j` is the stationary
pre-sample factor `epsC * policyFactor ^ (-j)`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthMass_invariant_zero {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : Fin 0 → Bool × Fin 2) (j : Fin (Q + 1)) :
    signedDepthSignedMass N t0 zeta C Q v o j =
      epsC C * signedDepthActionFactor zeta j.val o *
        signedDepthUnsignedMass N t0 zeta C Q v o j := by
  rw [signedDepthSignedMass, signedDepthUnsignedMass]
  simp_rw [signedDepthFilterMass_zero ht0 hzeta hC]
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  simp [signedDepthActionFactor, signedDepthInitWeight, latentDepth_depthSignEquiv,
    latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one, signedValue]
  ring

/-- The closed action-history factor obeys the reset recursion at depth zero. [the stated conclusion](goal). -/
lemma signedDepthActionFactor_zero (zeta : ℝ) {k : Nat}
    (o : Fin k → Bool × Fin 2) : signedDepthActionFactor zeta 0 o = 1 := by
  simp [signedDepthActionFactor, Nat.not_le_of_lt]

/-- The closed action-history factor obeys the one-step advance recursion. [the stated conclusion](goal). -/
lemma signedDepthActionFactor_succ (zeta : ℝ) (j k : Nat)
    (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthActionFactor zeta (j + 1) o =
      signedDepthActionFactor zeta j (fun i ↦ o i.castSucc) *
        (if (o (Fin.last k)).1 then 1 else 0) := by
  unfold signedDepthActionFactor
  have hmin : min (j + 1) (k + 1) = min j k + 1 := by omega
  have hsub : ((j + 1 : Nat) : ℤ) - (min (j + 1) (k + 1) : Nat) =
      (j : ℤ) - (min j k : Nat) := by omega
  rw [hsub]
  have hthreshold : (k + 1) - min (j + 1) (k + 1) = k - min j k := by omega
  have hp :
      (∏ i ∈ Finset.univ.filter
          (fun i : Fin (k + 1) ↦ k + 1 - min (j + 1) (k + 1) ≤ i.val),
          if (o i).1 then (1 : ℝ) else 0) =
        (∏ i ∈ Finset.univ.filter (fun i : Fin k ↦ k - min j k ≤ i.val),
          if (o i.castSucc).1 then (1 : ℝ) else 0) *
            (if (o (Fin.last k)).1 then 1 else 0) := by
    simp_rw [Finset.prod_filter]
    rw [Fin.prod_univ_castSucc]
    simp only [hthreshold]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro i _
      simp
    · simp
  rw [hp]
  ring

/-- Summing a raw filter update over target signs gives the unsigned depth update. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_succ_raw {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) (j' : Fin (Q + 1)) :
    signedDepthUnsignedMass N t0 zeta C Q v o j' =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 *
        ∑ h : Fin (2 * (Q + 1)),
          signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
            signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
              (∑ u' : Fin 2,
                signedDepthStateWeight t0 C Q h (o (Fin.last k)).1
                  (depthSignEquiv Q (j', u'))) := by
  unfold signedDepthUnsignedMass
  simp_rw [signedDepthFilterMass_succ_raw ht0 hzeta hC]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Summing a raw filter update against the target sign gives the signed depth update. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthSignedMass_succ_raw {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) (j' : Fin (Q + 1)) :
    signedDepthSignedMass N t0 zeta C Q v o j' =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 *
        ∑ h : Fin (2 * (Q + 1)),
          signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
            signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
              (∑ u' : Fin 2,
                signedValue (latentSign Q (depthSignEquiv Q (j', u'))) *
                  signedDepthStateWeight t0 C Q h (o (Fin.last k)).1
                    (depthSignEquiv Q (j', u'))) := by
  unfold signedDepthSignedMass
  simp_rw [signedDepthFilterMass_succ_raw ht0 hzeta hC]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- At reset depth zero, the signed and unsigned updates have exact ratio `epsC`. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthMass_invariant_reset {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthSignedMass N t0 zeta C Q v o 0 =
      epsC C * signedDepthUnsignedMass N t0 zeta C Q v o 0 := by
  rw [signedDepthSignedMass_succ_raw ht0 hzeta hC,
    signedDepthUnsignedMass_succ_raw ht0 hzeta hC]
  have hreset (h : Fin (2 * (Q + 1))) :
      (∑ u' : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (0, u'))) *
        signedDepthStateWeight t0 C Q h (o (Fin.last k)).1
          (depthSignEquiv Q (0, u'))) =
        epsC C *
          ∑ u' : Fin 2, signedDepthStateWeight t0 C Q h (o (Fin.last k)).1
            (depthSignEquiv Q (0, u')) := by
    rw [sum_signedValue_mul_signedDepthStateWeight_reset,
      sum_signedDepthStateWeight_reset]
    by_cases hQ : latentDepth Q h = Q <;> simp [hQ] <;> ring
  simp_rw [hreset]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.sum_congr rfl
  intro u _
  ring

/-- The unsigned mass at a positive target depth comes only from the preceding depth, through a
fair reward and one advance. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hj condition](hyp:hj). [the stated conclusion](goal). -/
lemma signedDepthUnsignedMass_advance {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k j : Nat} (hj : j < Q) (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthUnsignedMass N t0 zeta C Q v o ⟨j + 1, by omega⟩ =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * mixingAlpha t0 * (1 / 2) *
        signedDepthUnsignedMass N t0 zeta C Q v (fun i ↦ o i.castSucc) ⟨j, by omega⟩ := by
  let j0 : Fin (Q + 1) := ⟨j, by omega⟩
  let j1 : Fin (Q + 1) := ⟨j + 1, by omega⟩
  change signedDepthUnsignedMass N t0 zeta C Q v o j1 =
    signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * mixingAlpha t0 * (1 / 2) *
      signedDepthUnsignedMass N t0 zeta C Q v (fun i ↦ o i.castSucc) j0
  rw [signedDepthUnsignedMass_succ_raw ht0 hzeta hC]
  simp_rw [sum_signedDepthStateWeight_pos t0 C Q _ _ j1 (by simp [j1])]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
      signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
        (if latentDepth Q h = Q then 0
        else if j1.val = latentDepth Q h + 1 then mixingAlpha t0 else 0))
    (fun z ↦ signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
        (depthSignEquiv Q z) *
      signedDepthRewardWeight t0 Q v (depthSignEquiv Q z) (o (Fin.last k)).2 *
        (if latentDepth Q (depthSignEquiv Q z) = Q then 0
        else if j1.val = latentDepth Q (depthSignEquiv Q z) + 1 then
          mixingAlpha t0 else 0))
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  have hdepth (u : Fin 2) : latentDepth Q (depthSignEquiv Q (j0, u)) < Q := by
    simp [j0, latentDepth_depthSignEquiv, hj]
  have hjEq (d : Fin (Q + 1)) : (j1.val = d.val + 1) = (d = j0) := by
    apply propext
    simp [j0, j1, Fin.ext_iff, eq_comm]
  simp_rw [latentDepth_depthSignEquiv, hjEq]
  have hcollapse (d : Fin (Q + 1)) :
      (if d.val = Q then (0 : ℝ) else if d = j0 then mixingAlpha t0 else 0) =
        if d = j0 then mixingAlpha t0 else 0 := by
    by_cases hd : d = j0
    · subst d
      simp [j0, ne_of_lt hj]
    · simp [hd]
  simp_rw [hcollapse]
  have hinner (d : Fin (Q + 1)) :
      (∑ u : Fin 2,
        signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
            (depthSignEquiv Q (d, u)) *
          signedDepthRewardWeight t0 Q v (depthSignEquiv Q (d, u))
            (o (Fin.last k)).2 *
            (if d = j0 then mixingAlpha t0 else 0)) =
        if d = j0 then mixingAlpha t0 * (1 / 2) *
          ∑ u : Fin 2, signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
            (depthSignEquiv Q (j0, u)) else 0 := by
    by_cases hd : d = j0
    · subst d
      simp [signedDepthRewardWeight, latentDepth_depthSignEquiv, j0, ne_of_lt hj]
      ring
    · simp [hd]
  simp_rw [hinner]
  simp
  unfold signedDepthUnsignedMass
  rw [Fin.sum_univ_two]
  ring

/-- The signed mass at a positive target depth comes from the preceding signed mass precisely
when the newly observed action preserves the sign. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the hj condition](hyp:hj). [the stated conclusion](goal). -/
lemma signedDepthSignedMass_advance {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k j : Nat} (hj : j < Q) (o : Fin (k + 1) → Bool × Fin 2) :
    signedDepthSignedMass N t0 zeta C Q v o ⟨j + 1, by omega⟩ =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * mixingAlpha t0 * (1 / 2) *
        (if (o (Fin.last k)).1 then
          signedDepthSignedMass N t0 zeta C Q v (fun i ↦ o i.castSucc) ⟨j, by omega⟩
        else 0) := by
  let j0 : Fin (Q + 1) := ⟨j, by omega⟩
  let j1 : Fin (Q + 1) := ⟨j + 1, by omega⟩
  change signedDepthSignedMass N t0 zeta C Q v o j1 =
    signedDepthBehaviourWeight zeta (o (Fin.last k)).1 * mixingAlpha t0 * (1 / 2) *
      (if (o (Fin.last k)).1 then
        signedDepthSignedMass N t0 zeta C Q v (fun i ↦ o i.castSucc) j0 else 0)
  rw [signedDepthSignedMass_succ_raw ht0 hzeta hC]
  simp_rw [sum_signedValue_mul_signedDepthStateWeight_pos t0 C Q _ _ j1
    (by simp [j1])]
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc) h *
      signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
        (if latentDepth Q h = Q then 0
        else if j1.val = latentDepth Q h + 1 then
          mixingAlpha t0 *
            (if (o (Fin.last k)).1 then signedValue (latentSign Q h) else 0)
        else 0))
    (fun z ↦ signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
        (depthSignEquiv Q z) *
      signedDepthRewardWeight t0 Q v (depthSignEquiv Q z) (o (Fin.last k)).2 *
        (if latentDepth Q (depthSignEquiv Q z) = Q then 0
        else if j1.val = latentDepth Q (depthSignEquiv Q z) + 1 then
          mixingAlpha t0 *
            (if (o (Fin.last k)).1 then
              signedValue (latentSign Q (depthSignEquiv Q z)) else 0)
        else 0))
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  have hjEq (d : Fin (Q + 1)) : (j1.val = d.val + 1) = (d = j0) := by
    apply propext
    simp [j0, j1, Fin.ext_iff, eq_comm]
  simp_rw [latentDepth_depthSignEquiv, hjEq]
  have hcollapse (d : Fin (Q + 1)) (u : Fin 2) :
      (if d.val = Q then (0 : ℝ)
      else if d = j0 then mixingAlpha t0 *
        (if (o (Fin.last k)).1 then
          signedValue (latentSign Q (depthSignEquiv Q (d, u))) else 0)
      else 0) =
      if d = j0 then mixingAlpha t0 *
        (if (o (Fin.last k)).1 then
          signedValue (latentSign Q (depthSignEquiv Q (d, u))) else 0)
      else 0 := by
    by_cases hd : d = j0
    · subst d
      simp [j0, ne_of_lt hj]
    · simp [hd]
  simp_rw [hcollapse]
  have hdepth (u : Fin 2) : latentDepth Q (depthSignEquiv Q (j0, u)) < Q := by
    simp [j0, latentDepth_depthSignEquiv, hj]
  have hinner (d : Fin (Q + 1)) :
      (∑ u : Fin 2,
        signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
            (depthSignEquiv Q (d, u)) *
          signedDepthRewardWeight t0 Q v (depthSignEquiv Q (d, u))
            (o (Fin.last k)).2 *
          (if d = j0 then mixingAlpha t0 *
            (if (o (Fin.last k)).1 then
              signedValue (latentSign Q (depthSignEquiv Q (d, u))) else 0)
          else 0)) =
        if d = j0 then mixingAlpha t0 * (1 / 2) *
          (if (o (Fin.last k)).1 then
            ∑ u : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (j0, u))) *
              signedDepthFilterMass N t0 zeta C Q v (fun i ↦ o i.castSucc)
                (depthSignEquiv Q (j0, u))
          else 0) else 0 := by
    by_cases hd : d = j0
    · subst d
      by_cases ha : (o (Fin.last k)).1 <;>
        simp [ha, signedDepthRewardWeight, latentDepth_depthSignEquiv, j0,
          ne_of_lt hj] <;> ring
    · simp [hd]
  simp_rw [hinner]
  simp
  unfold signedDepthSignedMass
  rw [Fin.sum_univ_two]
  ring

/-- At every depth, the signed filter mass is the unsigned mass times the exact surviving
pre-sample/reset sign bias and observed action-history factor. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthMass_invariant {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (j : Fin (Q + 1)) :
    signedDepthSignedMass N t0 zeta C Q v o j =
      epsC C * signedDepthActionFactor zeta j.val o *
        signedDepthUnsignedMass N t0 zeta C Q v o j := by
  induction k generalizing j with
  | zero => exact signedDepthMass_invariant_zero ht0 hzeta hC v o j
  | succ k ih =>
      by_cases hj0 : j.val = 0
      · have hj : j = 0 := Fin.ext hj0
        have hreset := signedDepthMass_invariant_reset (N := N) (Q := Q)
          ht0 hzeta hC v o
        simpa [hj, signedDepthActionFactor_zero] using hreset
      · let d := j.val - 1
        have hdQ : d < Q := by
          have hjle : j.val ≤ Q := by omega
          omega
        let j0 : Fin (Q + 1) := ⟨d, by omega⟩
        let j1 : Fin (Q + 1) := ⟨d + 1, by omega⟩
        have hj1 : j1 = j := by
          apply Fin.ext
          simp [j1, d]
          omega
        rw [← hj1]
        rw [signedDepthSignedMass_advance ht0 hzeta hC v hdQ,
          signedDepthUnsignedMass_advance ht0 hzeta hC v hdQ,
          ih (fun i ↦ o i.castSucc) j0,
          signedDepthActionFactor_succ]
        by_cases ha : (o (Fin.last k)).1 <;> simp [ha]
        ring

/-- Restricting the full hidden-state filter to terminal depth is its unsigned depth-`Q`
aggregate. [the stated conclusion](goal). -/
lemma sum_terminalFilterMass_eq_unsignedMass
    (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      signedDepthUnsignedMass N t0 zeta C Q v o (Fin.last Q) := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0)
    (fun z ↦ if latentDepth Q (depthSignEquiv Q z) = Q then
      signedDepthFilterMass N t0 zeta C Q v o (depthSignEquiv Q z) else 0)
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp_rw [latentDepth_depthSignEquiv]
  have hd (d : Fin (Q + 1)) : (d.val = Q) = (d = Fin.last Q) := by
    apply propext
    simp [Fin.ext_iff]
  simp_rw [hd]
  simp [signedDepthUnsignedMass]

/-- Restricting the signed full hidden-state filter to terminal depth is its signed depth-`Q`
aggregate. [the stated conclusion](goal). -/
lemma sum_terminalSignedFilterMass_eq_signedMass
    (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then
        signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      signedDepthSignedMass N t0 zeta C Q v o (Fin.last Q) := by
  rw [Fintype.sum_equiv (depthSignEquiv Q).symm
    (fun h ↦ if latentDepth Q h = Q then
      signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h else 0)
    (fun z ↦ if latentDepth Q (depthSignEquiv Q z) = Q then
      signedValue (latentSign Q (depthSignEquiv Q z)) *
        signedDepthFilterMass N t0 zeta C Q v o (depthSignEquiv Q z) else 0)
    (fun h ↦ by rw [Equiv.apply_symm_apply])]
  rw [Fintype.sum_prod_type]
  simp_rw [latentDepth_depthSignEquiv]
  have hd (d : Fin (Q + 1)) : (d.val = Q) = (d = Fin.last Q) := by
    apply propext
    simp [Fin.ext_iff]
  simp_rw [hd]
  simp [signedDepthSignedMass]

/-- The signed terminal-depth filter mass is exactly `epsC` times the depth-`Q` action-history
factor and the unsigned terminal-depth mass. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_terminalMass_invariant {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then
        signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      epsC C * signedDepthActionFactor zeta Q o *
        ∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then signedDepthFilterMass N t0 zeta C Q v o h else 0 := by
  rw [sum_terminalSignedFilterMass_eq_signedMass,
    sum_terminalFilterMass_eq_unsignedMass]
  simpa using signedDepthMass_invariant ht0 hzeta hC v o (Fin.last Q)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
