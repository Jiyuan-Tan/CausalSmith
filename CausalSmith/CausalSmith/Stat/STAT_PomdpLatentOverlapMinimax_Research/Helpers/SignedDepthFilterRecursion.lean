import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePrefixMarginal
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepth
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.SignedDepthWeights

set_option linter.style.longLine false

/-! # One-step finite filters for the signed-depth family -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators ENNReal

/-- Partition a payoff at the next reward symbol by the one-coordinate extension of a fixed
observed prefix. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_prefix_nextPayoff_as_extensions
    {nX nH nR : Nat} [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (U k : Nat) (o : Fin k → Bool × Fin nR) (phi : Fin nR → ℝ) :
    (∑ tau : FiniteTrajectory (U + (k + 1)) nX nH nR,
      if (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o then
        finitePathWeightFrom kernel p b tau *
          phi (finiteObservedPrefixExtra U (k + 1) tau (Fin.last k)).2 else 0) =
      ∑ ar : Bool × Fin nR,
        phi ar.2 *
          ∑ tau : FiniteTrajectory (U + (k + 1)) nX nH nR,
            if finiteObservedPrefixExtra U (k + 1) tau = Fin.snoc o ar then
              finitePathWeightFrom kernel p b tau else 0 := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tau _
  let ar0 := finiteObservedPrefixExtra U (k + 1) tau (Fin.last k)
  have hext (ar : Bool × Fin nR) :
      finiteObservedPrefixExtra U (k + 1) tau = Fin.snoc o ar ↔
        (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o ∧
          ar0 = ar := by
    constructor
    · intro h
      constructor
      · funext j
        simpa [ar0] using congrFun h j.castSucc
      · simpa [ar0] using congrFun h (Fin.last k)
    · rintro ⟨hpre, har⟩
      funext j
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · simpa [ar0] using har
      · simpa using congrFun hpre i
  simp_rw [hext]
  by_cases hpre :
      (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o
  · simp [hpre, ar0]
    ring
  · simp [hpre]

/-- Split a state path into all coordinates before its last coordinate and its last coordinate. -/
def finiteStatePrefixLastEquiv (k nX nH : Nat) :
    (Fin (k + 2) → JointState nX nH) ≃
      (Fin (k + 1) → JointState nX nH) × JointState nX nH where
  toFun sigma := (fun j ↦ sigma j.castSucc, sigma (Fin.last (k + 1)))
  invFun z := Fin.snoc z.1 z.2
  left_inv sigma := by
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp
    · simp
  right_inv z := by
    apply Prod.ext
    · funext j
      simp
    · simp

/-- Appending one state exposes the final transition factor in a fixed-prefix likelihood. [the stated conclusion](goal). -/
lemma finiteFixedPrefixWeight_snoc {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin (k + 1) → Bool × Fin nR)
    (sigma : Fin (k + 1) → JointState nX nH) (s' : JointState nX nH) :
    finiteFixedPrefixWeight kernel p b o (Fin.snoc sigma s') =
      finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma *
        (b (sigma (Fin.last k)).1 (o (Fin.last k)).1).toReal *
          (kernel (sigma (Fin.last k)) (o (Fin.last k)).1
            ((o (Fin.last k)).2, s')).toReal := by
  have hsnoc (j : Fin k) :
      (Fin.snoc sigma s' : Fin (k + 2) → JointState nX nH) j.castSucc.succ =
        sigma j.succ := by
    rw [show j.castSucc.succ = j.succ.castSucc by rfl, Fin.snoc_castSucc]
  simp [finiteFixedPrefixWeight, Fin.prod_univ_castSucc]
  simp_rw [hsnoc]
  ring

/-- Marginalizing the suffix after one additional reward carries a reward-symbol payoff to the
one-step kernel at the cut state. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_prefix_nextPayoff
    {nX nH nR : Nat} [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (U k : Nat) (o : Fin k → Bool × Fin nR) (phi : Fin nR → ℝ) :
    (∑ tau : FiniteTrajectory (U + (k + 1)) nX nH nR,
      if (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o then
        finitePathWeightFrom kernel p b tau *
          phi (finiteObservedPrefixExtra U (k + 1) tau (Fin.last k)).2 else 0) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma *
          ∑ a : Bool, (b (sigma (Fin.last k)).1 a).toReal *
            ∑ r : Fin nR, phi r *
              ∑ s' : JointState nX nH,
                (kernel (sigma (Fin.last k)) a (r, s')).toReal := by
  classical
  rw [sum_finitePathWeightFrom_prefix_nextPayoff_as_extensions]
  simp_rw [sum_finitePathWeightFrom_fixedPrefix kernel b (k + 1) U p]
  have hstate (ar : Bool × Fin nR) :
      (∑ rho : Fin (k + 2) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) rho) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        ∑ s' : JointState nX nH,
          finiteFixedPrefixWeight kernel p b o sigma *
            (b (sigma (Fin.last k)).1 ar.1).toReal *
              (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal := by
    rw [Fintype.sum_equiv (finiteStatePrefixLastEquiv k nX nH)
      (fun rho ↦ finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) rho)
      (fun z ↦ finiteFixedPrefixWeight kernel p b (Fin.snoc o ar) (Fin.snoc z.1 z.2))]
    · rw [Fintype.sum_prod_type]
      simp_rw [finiteFixedPrefixWeight_snoc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    · intro rho
      rw [show Fin.snoc
          ((finiteStatePrefixLastEquiv k nX nH rho).1)
          ((finiteStatePrefixLastEquiv k nX nH rho).2) = rho from
        (finiteStatePrefixLastEquiv k nX nH).symm_apply_apply rho]
  simp_rw [hstate]
  symm
  calc
    (∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma *
          ∑ a : Bool, (b (sigma (Fin.last k)).1 a).toReal *
            ∑ r : Fin nR, phi r *
              ∑ s' : JointState nX nH,
                (kernel (sigma (Fin.last k)) a (r, s')).toReal) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        ∑ a : Bool, ∑ r : Fin nR, ∑ s' : JointState nX nH,
          phi r * (finiteFixedPrefixWeight kernel p b o sigma *
            (b (sigma (Fin.last k)).1 a).toReal *
              (kernel (sigma (Fin.last k)) a (r, s')).toReal) := by
        apply Finset.sum_congr rfl
        intro sigma _
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro r _
        apply Finset.sum_congr rfl
        intro s' _
        ring
    _ = ∑ a : Bool, ∑ sigma : Fin (k + 1) → JointState nX nH,
        ∑ r : Fin nR, ∑ s' : JointState nX nH,
          phi r * (finiteFixedPrefixWeight kernel p b o sigma *
            (b (sigma (Fin.last k)).1 a).toReal *
              (kernel (sigma (Fin.last k)) a (r, s')).toReal) := by
        rw [Finset.sum_comm]
    _ = ∑ a : Bool, ∑ r : Fin nR,
        ∑ sigma : Fin (k + 1) → JointState nX nH,
          ∑ s' : JointState nX nH,
            phi r * (finiteFixedPrefixWeight kernel p b o sigma *
              (b (sigma (Fin.last k)).1 a).toReal *
                (kernel (sigma (Fin.last k)) a (r, s')).toReal) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
    _ = ∑ ar : Bool × Fin nR,
        phi ar.2 *
          ∑ sigma : Fin (k + 1) → JointState nX nH,
            ∑ s' : JointState nX nH,
              finiteFixedPrefixWeight kernel p b o sigma *
                (b (sigma (Fin.last k)).1 ar.1).toReal *
                  (kernel (sigma (Fin.last k)) ar.1 (ar.2, s')).toReal := by
        rw [Fintype.sum_prod_type]
        simp_rw [Finset.mul_sum]

/-- Unnormalized finite-state filter mass after a fixed observed prefix. -/
noncomputable def finiteTerminalStatePrefixMass {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) (s : JointState nX nH) : ℝ :=
  ∑ sigma : Fin (k + 1) → JointState nX nH,
    if sigma (Fin.last k) = s then finiteFixedPrefixWeight kernel p b o sigma else 0

/-- With no observations, the unnormalized state filter is its initial state weight. [the stated conclusion](goal). -/
lemma finiteTerminalStatePrefixMass_zero {nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin 0 → Bool × Fin nR) (s : JointState nX nH) :
    finiteTerminalStatePrefixMass kernel p b o s = p s := by
  classical
  unfold finiteTerminalStatePrefixMass
  rw [Fintype.sum_equiv (finiteStatePrefixZeroEquiv nX nH)
    (fun sigma ↦ if sigma (Fin.last 0) = s then
      finiteFixedPrefixWeight kernel p b o sigma else 0)
    (fun s' ↦ if s' = s then p s' else 0)]
  · simp
  · intro sigma
    simp [finiteStatePrefixZeroEquiv, finiteFixedPrefixWeight]

/-- Summing terminal-state filter masses recovers the unrestricted fixed-prefix likelihood. [the stated conclusion](goal). -/
lemma sum_finiteTerminalStatePrefixMass {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) :
    ∑ s : JointState nX nH, finiteTerminalStatePrefixMass kernel p b o s =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma := by
  classical
  unfold finiteTerminalStatePrefixMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  simp

/-- Restricting the terminal-state sum by a predicate is the corresponding restriction of the
fixed state-prefix likelihood. [the stated conclusion](goal). -/
lemma sum_finiteTerminalStatePrefixMass_indicator {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) (P : JointState nX nH → Prop) [DecidablePred P] :
    (∑ s : JointState nX nH,
        if P s then finiteTerminalStatePrefixMass kernel p b o s else 0) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        if P (sigma (Fin.last k)) then finiteFixedPrefixWeight kernel p b o sigma else 0 := by
  classical
  unfold finiteTerminalStatePrefixMass
  have hdist (s : JointState nX nH) :
      (if P s then
          ∑ sigma : Fin (k + 1) → JointState nX nH,
            if sigma (Fin.last k) = s then finiteFixedPrefixWeight kernel p b o sigma else 0
        else 0) =
        ∑ sigma : Fin (k + 1) → JointState nX nH,
          if P s then
            (if sigma (Fin.last k) = s then finiteFixedPrefixWeight kernel p b o sigma else 0)
          else 0 := by
    by_cases hPs : P s <;> simp [hPs]
  simp_rw [hdist]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  calc
    (∑ s : JointState nX nH,
        if P s then
          (if sigma (Fin.last k) = s then finiteFixedPrefixWeight kernel p b o sigma else 0)
        else 0) =
      ∑ s : JointState nX nH,
        if sigma (Fin.last k) = s then
          (if P s then finiteFixedPrefixWeight kernel p b o sigma else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro s _
        by_cases hP : P s <;> by_cases hs : sigma (Fin.last k) = s <;> simp [hP, hs]
    _ = if P (sigma (Fin.last k)) then finiteFixedPrefixWeight kernel p b o sigma else 0 := by
      simp

/-- A terminal-state payoff can be evaluated either after grouping the fixed-prefix likelihood by
its terminal state or directly on each chronological state prefix. [the stated conclusion](goal). -/
lemma sum_mul_finiteTerminalStatePrefixMass {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) (g : JointState nX nH → ℝ) :
    (∑ s : JointState nX nH, g s * finiteTerminalStatePrefixMass kernel p b o s) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        g (sigma (Fin.last k)) * finiteFixedPrefixWeight kernel p b o sigma := by
  classical
  unfold finiteTerminalStatePrefixMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  simp

/-- The exact one-step unnormalized filter recursion before grouping by the previous state. [the stated conclusion](goal). -/
lemma finiteTerminalStatePrefixMass_succ {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin (k + 1) → Bool × Fin nR) (s' : JointState nX nH) :
    finiteTerminalStatePrefixMass kernel p b o s' =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma *
          (b (sigma (Fin.last k)).1 (o (Fin.last k)).1).toReal *
            (kernel (sigma (Fin.last k)) (o (Fin.last k)).1
              ((o (Fin.last k)).2, s')).toReal := by
  classical
  unfold finiteTerminalStatePrefixMass
  let e := finiteStatePrefixLastEquiv k nX nH
  rw [Fintype.sum_equiv e
    (fun sigma ↦ if sigma (Fin.last (k + 1)) = s' then
      finiteFixedPrefixWeight kernel p b o sigma else 0)
    (fun z ↦ (if (e.symm z) (Fin.last (k + 1)) = s' then
      finiteFixedPrefixWeight kernel p b o (e.symm z) else 0))
    (fun sigma ↦ by rw [e.symm_apply_apply])]
  have he (z : (Fin (k + 1) → JointState nX nH) × JointState nX nH) :
      e.symm z = Fin.snoc z.1 z.2 := by rfl
  simp_rw [he, Fin.snoc_last]
  rw [Fintype.sum_prod_type]
  · simp_rw [finiteFixedPrefixWeight_snoc]
    rw [Finset.sum_comm]
    have hinner (y : JointState nX nH) :
        (∑ sigma : Fin (k + 1) → JointState nX nH,
          if y = s' then
            finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma *
              (b (sigma (Fin.last k)).1 (o (Fin.last k)).1).toReal *
                (kernel (sigma (Fin.last k)) (o (Fin.last k)).1
                  ((o (Fin.last k)).2, y)).toReal else 0) =
          if y = s' then
            ∑ sigma : Fin (k + 1) → JointState nX nH,
              finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma *
                (b (sigma (Fin.last k)).1 (o (Fin.last k)).1).toReal *
                  (kernel (sigma (Fin.last k)) (o (Fin.last k)).1
                    ((o (Fin.last k)).2, y)).toReal else 0 := by
      by_cases hy : y = s' <;> simp [hy]
    simp_rw [hinner]
    simp

/-- Grouping the chronological update by its previous terminal state gives the usual
unnormalized finite-state filter recursion. [the stated conclusion](goal). -/
lemma finiteTerminalStatePrefixMass_succ_grouped {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin (k + 1) → Bool × Fin nR) (s' : JointState nX nH) :
    finiteTerminalStatePrefixMass kernel p b o s' =
      ∑ s : JointState nX nH,
        finiteTerminalStatePrefixMass kernel p b (fun j ↦ o j.castSucc) s *
          (b s.1 (o (Fin.last k)).1).toReal *
            (kernel s (o (Fin.last k)).1 ((o (Fin.last k)).2, s')).toReal := by
  classical
  rw [finiteTerminalStatePrefixMass_succ]
  unfold finiteTerminalStatePrefixMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  let G : JointState nX nH → ℝ := fun s ↦
    (b s.1 (o (Fin.last k)).1).toReal *
      (kernel s (o (Fin.last k)).1 ((o (Fin.last k)).2, s')).toReal
  have hcollapse :
      (∑ s : JointState nX nH,
        (if sigma (Fin.last k) = s then
          finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma else 0) * G s) =
        finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma *
          G (sigma (Fin.last k)) := by
    simp
  rw [show
    (∑ s : JointState nX nH,
      (if sigma (Fin.last k) = s then
        finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma else 0) *
          (b s.1 (o (Fin.last k)).1).toReal *
            (kernel s (o (Fin.last k)).1 ((o (Fin.last k)).2, s')).toReal) =
      ∑ s : JointState nX nH,
        (if sigma (Fin.last k) = s then
          finiteFixedPrefixWeight kernel p b (fun j ↦ o j.castSucc) sigma else 0) * G s by
    apply Finset.sum_congr rfl
    intro s _
    simp [G]
    ring]
  rw [hcollapse]
  simp only [G]
  ring

/-- The signed-depth instance of the unnormalized state filter. -/
noncomputable def signedDepthFilterMass (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) (h : Fin (2 * (Q + 1))) : ℝ :=
  finiteTerminalStatePrefixMass
    (signedDepthFinite N t0 zeta C Q v).kernel
    (fun s ↦ ((signedDepthFinite N t0 zeta C Q v).init s).toReal)
    (signedDepthFinite N t0 zeta C Q v).b o (0, h)

/-- The empty-history signed-depth filter is the raw stationary initial weight. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepthFilterMass_zero {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : Fin 0 → Bool × Fin 2) (h : Fin (2 * (Q + 1))) :
    signedDepthFilterMass N t0 zeta C Q v o h = signedDepthInitWeight t0 zeta C Q h := by
  rw [signedDepthFilterMass, finiteTerminalStatePrefixMass_zero]
  exact signedDepthFinite_init_toReal ht0 hzeta hC.le v h

/-- Grouped one-step depth/sign recursion for the signed-depth kernel. [the h' condition](hyp:h'). [the stated conclusion](goal). -/
lemma signedDepthFilterMass_succ_grouped (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) (h' : Fin (2 * (Q + 1))) :
    signedDepthFilterMass N t0 zeta C Q v o h' =
      ∑ h : Fin (2 * (Q + 1)),
        signedDepthFilterMass N t0 zeta C Q v (fun j ↦ o j.castSucc) h *
          ((signedDepthFinite N t0 zeta C Q v).b 0 (o (Fin.last k)).1).toReal *
            ((signedDepthFinite N t0 zeta C Q v).kernel (0, h)
              (o (Fin.last k)).1 ((o (Fin.last k)).2, (0, h'))).toReal := by
  rw [signedDepthFilterMass, finiteTerminalStatePrefixMass_succ_grouped]
  simp only [Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  simp [signedDepthFilterMass]

/-- Under the signed-depth positivity hypotheses, one filter update is exactly multiplication by
the raw behavior, reward-emission, and reset/advance transition factors. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC); and [the h' condition](hyp:h'). [the stated conclusion](goal). -/
lemma signedDepthFilterMass_succ_raw {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    {k : Nat} (o : Fin (k + 1) → Bool × Fin 2) (h' : Fin (2 * (Q + 1))) :
    signedDepthFilterMass N t0 zeta C Q v o h' =
      signedDepthBehaviourWeight zeta (o (Fin.last k)).1 *
        ∑ h : Fin (2 * (Q + 1)),
          signedDepthFilterMass N t0 zeta C Q v (fun j ↦ o j.castSucc) h *
            signedDepthRewardWeight t0 Q v h (o (Fin.last k)).2 *
              signedDepthStateWeight t0 C Q h (o (Fin.last k)).1 h' := by
  rw [signedDepthFilterMass_succ_grouped]
  simp_rw [signedDepthFinite_b_toReal (T := N) (Q := Q) hzeta v,
    signedDepthFinite_kernel_toReal (T := N) ht0 hC.le v]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h _
  ring

/-- The raw Rademacher reward emission has its declared signed terminal mean. [the stated conclusion](goal). -/
lemma sum_rewardValue_mul_signedDepthRewardWeight (t0 : ℝ) (Q : Nat) (v : Bool)
    (h : Fin (2 * (Q + 1))) :
    ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
      signedDepthRewardWeight t0 Q v h r =
        signedValue v * c0 t0 * signedValue (latentSign Q h) *
          (if latentDepth Q h = Q then 1 else 0) := by
  rw [Fin.sum_univ_two]
  cases v <;> cases hs : latentSign Q h <;>
    by_cases hQ : latentDepth Q h = Q <;>
    simp [signedDepthRewardWeight, signedValue, hs, hQ] <;> ring

/-- The one-additional-epoch payoff appearing in the generic marginal is the signed terminal
reward mean at the cut hidden state. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_oneStepRewardPayoff {N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (h : Fin (2 * (Q + 1))) :
    (∑ a : Bool, ((signedDepthFinite N t0 zeta C Q v).b 0 a).toReal *
      ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
        ∑ s' : JointState 1 (2 * (Q + 1)),
          ((signedDepthFinite N t0 zeta C Q v).kernel (0, h) a (r, s')).toReal) =
      signedValue v * c0 t0 * signedValue (latentSign Q h) *
        (if latentDepth Q h = Q then 1 else 0) := by
  simp_rw [signedDepthFinite_b_toReal (T := N) (Q := Q) hzeta v]
  calc
    (∑ a : Bool, signedDepthBehaviourWeight zeta a *
      ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
        ∑ s' : JointState 1 (2 * (Q + 1)),
          ((signedDepthFinite N t0 zeta C Q v).kernel (0, h) a (r, s')).toReal) =
      ∑ a : Bool, signedDepthBehaviourWeight zeta a *
        ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
          signedDepthRewardWeight t0 Q v h r := by
        apply Finset.sum_congr rfl
        intro a _
        apply congrArg
        apply Finset.sum_congr rfl
        intro r _
        congr 1
        rw [Fintype.sum_prod_type]
        simp_rw [signedDepthFinite_kernel_toReal (T := N) ht0 hC.le v]
        rw [← Finset.mul_sum, sum_signedDepthStateWeight, mul_one]
        simp
    _ = (∑ a : Bool, signedDepthBehaviourWeight zeta a) *
        ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
          signedDepthRewardWeight t0 Q v h r := by rw [Finset.sum_mul]
    _ = ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
          signedDepthRewardWeight t0 Q v h r := by
      rw [sum_signedDepthBehaviourWeight, one_mul]
    _ = _ := sum_rewardValue_mul_signedDepthRewardWeight t0 Q v h

/-- The signed terminal-depth filter moment is the same moment evaluated on chronological fixed
state prefixes. [the stated conclusion](goal). -/
lemma sum_terminalSignedFilterMass_eq_sum_fixedPrefix
    (N : Nat) (t0 zeta C : ℝ) (Q : Nat) (v : Bool)
    {k : Nat} (o : Fin k → Bool × Fin 2) :
    (∑ h : Fin (2 * (Q + 1)),
      if latentDepth Q h = Q then
        signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h else 0) =
      ∑ sigma : Fin (k + 1) → JointState 1 (2 * (Q + 1)),
        if latentDepth Q (sigma (Fin.last k)).2 = Q then
          signedValue (latentSign Q (sigma (Fin.last k)).2) *
            finiteFixedPrefixWeight
              (signedDepthFinite N t0 zeta C Q v).kernel
              (fun s ↦ ((signedDepthFinite N t0 zeta C Q v).init s).toReal)
              (signedDepthFinite N t0 zeta C Q v).b o sigma
        else 0 := by
  classical
  let g : JointState 1 (2 * (Q + 1)) → ℝ := fun s ↦
    if latentDepth Q s.2 = Q then signedValue (latentSign Q s.2) else 0
  have hw := sum_mul_finiteTerminalStatePrefixMass
    (signedDepthFinite N t0 zeta C Q v).kernel
    (fun s ↦ ((signedDepthFinite N t0 zeta C Q v).init s).toReal)
    (signedDepthFinite N t0 zeta C Q v).b o g
  rw [Fintype.sum_prod_type] at hw
  simp only [Fin.sum_univ_one] at hw
  simpa [g, signedDepthFilterMass] using hw

/-- For a fixed observed prefix, marginalizing the next signed-depth reward over the remaining
trajectory gives `signedValue v * c0` times the signed terminal-depth filter moment. [the ht0 condition](hyp:ht0); and [the hzeta condition](hyp:hzeta); and [the h C condition](hyp:hC). [the stated conclusion](goal). -/
lemma signedDepth_prefix_nextRewardNumerator {U k N Q : Nat} {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (v : Bool)
    (o : Fin k → Bool × Fin 2) :
    (∑ tau : FiniteTrajectory (U + (k + 1)) 1 (2 * (Q + 1)) 2,
      if (fun j : Fin k ↦ finiteObservedPrefixExtra U (k + 1) tau j.castSucc) = o then
        finitePathWeightFrom
          (signedDepthFinite N t0 zeta C Q v).kernel
          (fun s ↦ ((signedDepthFinite N t0 zeta C Q v).init s).toReal)
          (signedDepthFinite N t0 zeta C Q v).b tau *
            (if (finiteObservedPrefixExtra U (k + 1) tau (Fin.last k)).2 = 0 then
              (-1 : ℝ) else 1)
      else 0) =
      signedValue v * c0 t0 *
        ∑ h : Fin (2 * (Q + 1)),
          if latentDepth Q h = Q then
            signedValue (latentSign Q h) * signedDepthFilterMass N t0 zeta C Q v o h else 0 := by
  refine (sum_finitePathWeightFrom_prefix_nextPayoff
    (signedDepthFinite N t0 zeta C Q v).kernel
    (fun s ↦ ((signedDepthFinite N t0 zeta C Q v).init s).toReal)
    (signedDepthFinite N t0 zeta C Q v).b U k o
    (fun r : Fin 2 ↦ if r = 0 then (-1 : ℝ) else 1)).trans ?_
  have hpay (s : JointState 1 (2 * (Q + 1))) :
      (∑ a : Bool, ((signedDepthFinite N t0 zeta C Q v).b s.1 a).toReal *
        ∑ r : Fin 2, (if r = 0 then (-1 : ℝ) else 1) *
          ∑ s' : JointState 1 (2 * (Q + 1)),
            ((signedDepthFinite N t0 zeta C Q v).kernel s a (r, s')).toReal) =
        signedValue v * c0 t0 * signedValue (latentSign Q s.2) *
          (if latentDepth Q s.2 = Q then 1 else 0) := by
    obtain ⟨x, h⟩ := s
    have hx : x = 0 := Subsingleton.elim _ _
    subst x
    exact signedDepth_oneStepRewardPayoff ht0 hzeta hC v h
  simp_rw [hpay]
  rw [sum_terminalSignedFilterMass_eq_sum_fixedPrefix]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sigma _
  by_cases hQ : latentDepth Q (sigma (Fin.last k)).2 = Q <;> simp [hQ]
  ring

/-- Signed target-sign aggregate of the reset/advance transition at a fixed target depth. [the stated conclusion](goal). -/
lemma sum_signedValue_mul_signedDepthStateWeight_at_depth (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) (j' : Fin (Q + 1)) :
    (∑ u' : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (j', u'))) *
      signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (j', u'))) =
      if latentDepth Q h = Q then
        if j'.val = 0 then epsC C else 0
      else
        (if j'.val = 0 then (1 - mixingAlpha t0) * epsC C else 0) +
          (if j'.val = latentDepth Q h + 1 then
            mixingAlpha t0 * (if a then signedValue (latentSign Q h) else 0) else 0) := by
  rw [Fin.sum_univ_two]
  by_cases hterm : latentDepth Q h = Q <;>
    by_cases hj0 : j'.val = 0 <;>
    by_cases hjnext : j'.val = latentDepth Q h + 1 <;>
    cases a <;> cases hs : latentSign Q h <;>
    simp [signedDepthStateWeight, latentDepth_depthSignEquiv,
      latentSign_depthSignEquiv_zero, latentSign_depthSignEquiv_one,
      resetSignWeight, signedValue, hs, hterm, hj0, hjnext] <;> ring

/-- The unsigned mass sent to reset depth zero is one after a terminal state and `1 - alpha`
otherwise. [the stated conclusion](goal). -/
lemma sum_signedDepthStateWeight_reset (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) :
    (∑ u' : Fin 2,
      signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (0, u'))) =
      if latentDepth Q h = Q then 1 else 1 - mixingAlpha t0 := by
  rw [sum_signedDepthStateWeight_at_depth]
  simp

/-- The signed mass sent to reset depth zero is the reset bias `epsC`, multiplied by the reset
probability away from a terminal state. [the stated conclusion](goal). -/
lemma sum_signedValue_mul_signedDepthStateWeight_reset (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) :
    (∑ u' : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (0, u'))) *
      signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (0, u'))) =
      if latentDepth Q h = Q then epsC C else (1 - mixingAlpha t0) * epsC C := by
  rw [sum_signedValue_mul_signedDepthStateWeight_at_depth]
  simp

/-- At a positive target depth, unsigned transition mass is zero after a terminal state and is
exactly `alpha` only at the unique advance depth otherwise. [the hj' condition](hyp:hj'). [the stated conclusion](goal). -/
lemma sum_signedDepthStateWeight_pos (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) (j' : Fin (Q + 1)) (hj' : 0 < j'.val) :
    (∑ u' : Fin 2,
      signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (j', u'))) =
      if latentDepth Q h = Q then 0
      else if j'.val = latentDepth Q h + 1 then mixingAlpha t0 else 0 := by
  rw [sum_signedDepthStateWeight_at_depth]
  simp [Nat.ne_of_gt hj']

/-- At a positive target depth, signed advance mass preserves the old sign only under action one;
all other positive-depth signed aggregates vanish. [the hj' condition](hyp:hj'). [the stated conclusion](goal). -/
lemma sum_signedValue_mul_signedDepthStateWeight_pos (t0 C : ℝ) (Q : Nat)
    (h : Fin (2 * (Q + 1))) (a : Bool) (j' : Fin (Q + 1)) (hj' : 0 < j'.val) :
    (∑ u' : Fin 2, signedValue (latentSign Q (depthSignEquiv Q (j', u'))) *
      signedDepthStateWeight t0 C Q h a (depthSignEquiv Q (j', u'))) =
      if latentDepth Q h = Q then 0
      else if j'.val = latentDepth Q h + 1 then
        mixingAlpha t0 * (if a then signedValue (latentSign Q h) else 0) else 0 := by
  rw [sum_signedValue_mul_signedDepthStateWeight_at_depth]
  simp [Nat.ne_of_gt hj']

end CausalSmith.Stat.PomdpLatentOverlapMinimax
