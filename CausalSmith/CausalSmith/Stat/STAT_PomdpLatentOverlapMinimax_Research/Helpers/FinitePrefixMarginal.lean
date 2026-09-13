import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePathMarginal

set_option linter.style.longLine false

/-! # Fixed-prefix marginalization for chronological finite paths -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators ENNReal

/-- Embed a prefix coordinate into a horizon with `U` additional epochs. -/
def prefixExtraIndex (U : Nat) {k : Nat} (j : Fin k) : Fin (U + k) :=
  ⟨j.val, lt_of_lt_of_le j.isLt (Nat.le_add_left k U)⟩

/-- The first `k` action/reward coordinates of a path with `U` further epochs. -/
def finiteObservedPrefixExtra {nX nH nR : Nat} (U k : Nat)
    (tau : FiniteTrajectory (U + k) nX nH nR) : Fin k → Bool × Fin nR :=
  fun j ↦ tau.2 (prefixExtraIndex U j)

/-- The state coordinate at the end of a `k`-epoch prefix. -/
def cutStateExtraIndex (U k : Nat) : Fin (U + k + 1) := ⟨k, by omega⟩

/-- The chronological weight of a state prefix under fixed observed action/reward coordinates. -/
noncomputable def finiteFixedPrefixWeight {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin k → Bool × Fin nR) (sigma : Fin (k + 1) → JointState nX nH) : ℝ :=
  p (sigma 0) *
    ∏ j : Fin k,
      (b (sigma j.castSucc).1 (o j).1).toReal *
        (kernel (sigma j.castSucc) (o j).1 ((o j).2, sigma j.succ)).toReal

/-- A zero-length state prefix is equivalent to its unique state. -/
def finiteStatePrefixZeroEquiv (nX nH : Nat) :
    (Fin 1 → JointState nX nH) ≃ JointState nX nH :=
  Equiv.funUnique (Fin 1) (JointState nX nH)

/-- Split a nonempty state prefix into its initial state and remaining state prefix. -/
def finiteStatePrefixSuccEquiv (k nX nH : Nat) :
    (Fin (k + 2) → JointState nX nH) ≃
      JointState nX nH × (Fin (k + 1) → JointState nX nH) where
  toFun sigma := (sigma 0, fun i ↦ sigma i.succ)
  invFun z := Fin.cases z.1 z.2
  left_inv sigma := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv z := by
    apply Prod.ext
    · rfl
    · funext i
      rfl

/-- Peeling a trajectory exposes the first observed coordinate of its fixed prefix. [the stated conclusion](goal). -/
lemma finiteObservedPrefixExtra_succEquiv_zero {k U nX nH nR : Nat}
    (z : (JointState nX nH × (Bool × Fin nR)) ×
      FiniteTrajectory (U + k) nX nH nR) :
    finiteObservedPrefixExtra U (k + 1)
      ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z) 0 = z.1.2 := by
  rfl

/-- After peeling, the remaining fixed observed prefix is the prefix of the tail trajectory. [the stated conclusion](goal). -/
lemma finiteObservedPrefixExtra_succEquiv_succ {k U nX nH nR : Nat}
    (z : (JointState nX nH × (Bool × Fin nR)) ×
      FiniteTrajectory (U + k) nX nH nR) (j : Fin k) :
    finiteObservedPrefixExtra U (k + 1)
      ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z) j.succ =
        finiteObservedPrefixExtra U k z.2 j := by
  rfl

/-- The cut state of a peeled positive prefix is the cut state of its tail prefix. [the stated conclusion](goal). -/
lemma cutStateExtraIndex_succEquiv {k U nX nH nR : Nat}
    (z : (JointState nX nH × (Bool × Fin nR)) ×
      FiniteTrajectory (U + k) nX nH nR) :
    ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z).1
        (cutStateExtraIndex U (k + 1)) =
      z.2.1 (cutStateExtraIndex U k) := by
  rfl

/-- Peeling the first state from a positive-length state prefix preserves its terminal state. [the stated conclusion](goal). -/
lemma finiteStatePrefixSuccEquiv_last {k nX nH : Nat}
    (z : JointState nX nH × (Fin (k + 1) → JointState nX nH)) :
    ((finiteStatePrefixSuccEquiv k nX nH).symm z) (Fin.last (k + 1)) =
      z.2 (Fin.last k) := by
  rfl

/-- Peeling the first state from a fixed-prefix likelihood leaves the fixed-prefix likelihood of
the tail, apart from the first transition factor. [the stated conclusion](goal). -/
lemma finiteFixedPrefixWeight_succEquiv_symm {k nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (o : Fin (k + 1) → Bool × Fin nR)
    (z : JointState nX nH × (Fin (k + 1) → JointState nX nH)) :
    finiteFixedPrefixWeight kernel p b o
        ((finiteStatePrefixSuccEquiv k nX nH).symm z) =
      p z.1 * (b z.1.1 (o 0).1).toReal *
        (kernel z.1 (o 0).1 ((o 0).2, z.2 0)).toReal *
          (∏ j : Fin k,
            (b (z.2 j.castSucc).1 (o j.succ).1).toReal *
              (kernel (z.2 j.castSucc) (o j.succ).1
                ((o j.succ).2, z.2 j.succ)).toReal) := by
  rcases z with ⟨s, sigma⟩
  simp [finiteFixedPrefixWeight, finiteStatePrefixSuccEquiv, Fin.prod_univ_succ]
  ring

/-- Summing a full chronological path over a fixed observed prefix eliminates every suffix
coordinate.  An arbitrary test function at the cut state is carried to the terminal state of the
remaining state-prefix likelihood. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_fixedPrefix_cutWeight {nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) : ∀ (k U : Nat) (p : JointState nX nH → ℝ)
      (o : Fin k → Bool × Fin nR) (g : JointState nX nH → ℝ),
      (∑ tau : FiniteTrajectory (U + k) nX nH nR,
        if finiteObservedPrefixExtra U k tau = o then
          finitePathWeightFrom kernel p b tau *
            g (tau.1 (cutStateExtraIndex U k)) else 0) =
      ∑ sigma : Fin (k + 1) → JointState nX nH,
        finiteFixedPrefixWeight kernel p b o sigma * g (sigma (Fin.last k)) := by
  intro k
  induction k with
  | zero =>
      intro U p o g
      have ho : o = fun i ↦ Fin.elim0 i := Subsingleton.elim _ _
      subst o
      simp only [Subsingleton.elim (fun _ ↦ _) (fun i ↦ Fin.elim0 i), if_true]
      let pg : JointState nX nH → ℝ := fun s ↦ p s * g s
      calc
        (∑ tau : FiniteTrajectory (U + 0) nX nH nR,
            finitePathWeightFrom kernel p b tau *
              g (tau.1 (cutStateExtraIndex U 0))) =
            ∑ tau : FiniteTrajectory U nX nH nR,
              finitePathWeightFrom kernel pg b tau := by
          apply Finset.sum_congr rfl
          intro tau _
          simp [finitePathWeightFrom, pg, cutStateExtraIndex]
          ring
        _ = ∑ s : JointState nX nH, pg s := sum_finitePathWeightFrom kernel b U pg
        _ = ∑ sigma : Fin 1 → JointState nX nH,
              finiteFixedPrefixWeight kernel p b (fun i ↦ Fin.elim0 i) sigma *
                g (sigma (Fin.last 0)) := by
          symm
          apply Fintype.sum_equiv (finiteStatePrefixZeroEquiv nX nH)
          intro sigma
          simp [finiteFixedPrefixWeight, finiteStatePrefixZeroEquiv, pg]
  | succ k ih =>
      intro U p o g
      let oTail : Fin k → Bool × Fin nR := fun j ↦ o j.succ
      let pNext : JointState nX nH → ℝ := fun s' ↦
        ∑ s : JointState nX nH,
          p s * (b s.1 (o 0).1).toReal *
            (kernel s (o 0).1 ((o 0).2, s')).toReal
      have hprefix (z : (JointState nX nH × (Bool × Fin nR)) ×
          FiniteTrajectory (U + k) nX nH nR) :
          finiteObservedPrefixExtra U (k + 1)
              ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z) = o ↔
            z.1.2 = o 0 ∧ finiteObservedPrefixExtra U k z.2 = oTail := by
        constructor
        · intro h
          constructor
          · simpa [finiteObservedPrefixExtra_succEquiv_zero] using congrFun h 0
          · funext j
            simpa [oTail, finiteObservedPrefixExtra_succEquiv_succ] using congrFun h j.succ
        · rintro ⟨hzero, htail⟩
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simpa [finiteObservedPrefixExtra_succEquiv_zero] using hzero
          · simpa [oTail, finiteObservedPrefixExtra_succEquiv_succ] using congrFun htail j
      calc
        (∑ tau : FiniteTrajectory (U + (k + 1)) nX nH nR,
            if finiteObservedPrefixExtra U (k + 1) tau = o then
              finitePathWeightFrom kernel p b tau *
                g (tau.1 (cutStateExtraIndex U (k + 1))) else 0) =
            ∑ z : (JointState nX nH × (Bool × Fin nR)) ×
                FiniteTrajectory (U + k) nX nH nR,
              if finiteObservedPrefixExtra U (k + 1)
                  ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z) = o then
                finitePathWeightFrom kernel p b
                  ((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z) *
                    g (((finiteTrajectorySuccEquiv (U + k) nX nH nR).symm z).1
                      (cutStateExtraIndex U (k + 1))) else 0 := by
          apply Fintype.sum_equiv (finiteTrajectorySuccEquiv (U + k) nX nH nR)
          intro tau
          rw [Equiv.symm_apply_apply]
        _ = ∑ sigma : Fin (k + 2) → JointState nX nH,
              finiteFixedPrefixWeight kernel p b o sigma *
                g (sigma (Fin.last (k + 1))) := by
          rw [Fintype.sum_prod_type]
          simp_rw [hprefix, finitePathWeightFrom_succEquiv_symm,
            cutStateExtraIndex_succEquiv]
          rw [Finset.sum_comm]
          calc
            (∑ tau : FiniteTrajectory (U + k) nX nH nR,
                ∑ x : JointState nX nH × (Bool × Fin nR),
                  if x.2 = o 0 ∧ finiteObservedPrefixExtra U k tau = oTail then
                    p x.1 * (b x.1.1 x.2.1).toReal *
                      (kernel x.1 x.2.1 (x.2.2, tau.1 0)).toReal *
                        (∏ j : Fin (U + k),
                          (b (tau.1 j.castSucc).1 (tau.2 j).1).toReal *
                            (kernel (tau.1 j.castSucc) (tau.2 j).1
                              ((tau.2 j).2, tau.1 j.succ)).toReal)
                      * g (tau.1 (cutStateExtraIndex U k))
                  else 0) =
                ∑ tau : FiniteTrajectory (U + k) nX nH nR,
                  if finiteObservedPrefixExtra U k tau = oTail then
                    finitePathWeightFrom kernel pNext b tau *
                      g (tau.1 (cutStateExtraIndex U k)) else 0 := by
              apply Finset.sum_congr rfl
              intro tau _
              rw [Fintype.sum_prod_type]
              by_cases ht : finiteObservedPrefixExtra U k tau = oTail
              · simp only [ht, and_true, if_true]
                simp [pNext, finitePathWeightFrom, Fintype.sum_prod_type]
                simp_rw [← Finset.sum_mul]
              · simp [ht]
            _ = ∑ sigma : Fin (k + 1) → JointState nX nH,
                  finiteFixedPrefixWeight kernel pNext b oTail sigma *
                    g (sigma (Fin.last k)) := ih U pNext oTail g
            _ = ∑ sigma : Fin (k + 2) → JointState nX nH,
                  finiteFixedPrefixWeight kernel p b o sigma *
                    g (sigma (Fin.last (k + 1))) := by
              symm
              apply Eq.trans (Fintype.sum_equiv (finiteStatePrefixSuccEquiv k nX nH)
                (fun sigma ↦ finiteFixedPrefixWeight kernel p b o sigma *
                  g (sigma (Fin.last (k + 1))))
                (fun z ↦ finiteFixedPrefixWeight kernel p b o
                  ((finiteStatePrefixSuccEquiv k nX nH).symm z) *
                    g (((finiteStatePrefixSuccEquiv k nX nH).symm z) (Fin.last (k + 1))))
                (fun sigma ↦ by rw [Equiv.symm_apply_apply]))
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro sigma _
              simp_rw [finiteFixedPrefixWeight_succEquiv_symm,
                finiteStatePrefixSuccEquiv_last]
              simp only [pNext, oTail, finiteFixedPrefixWeight]
              simp_rw [← Finset.sum_mul]

/-- The unweighted fixed-prefix marginal is the constant-test-function instance of cut-weighted
marginalization. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_fixedPrefix {nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) (k U : Nat) (p : JointState nX nH → ℝ)
    (o : Fin k → Bool × Fin nR) :
    (∑ tau : FiniteTrajectory (U + k) nX nH nR,
      if finiteObservedPrefixExtra U k tau = o then
        finitePathWeightFrom kernel p b tau else 0) =
    ∑ sigma : Fin (k + 1) → JointState nX nH,
      finiteFixedPrefixWeight kernel p b o sigma := by
  simpa using sum_finitePathWeightFrom_fixedPrefix_cutWeight kernel b k U p o (fun _ ↦ 1)

/-- Indicator specialization of cut-weighted marginalization.  This gives the joint mass of a
fixed observed prefix and an arbitrary decidable event at its terminal hidden state. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_fixedPrefix_indicator {nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) (k U : Nat) (p : JointState nX nH → ℝ)
    (o : Fin k → Bool × Fin nR) (P : JointState nX nH → Prop)
    [DecidablePred P] :
    (∑ tau : FiniteTrajectory (U + k) nX nH nR,
      if finiteObservedPrefixExtra U k tau = o ∧
          P (tau.1 (cutStateExtraIndex U k)) then
        finitePathWeightFrom kernel p b tau else 0) =
    ∑ sigma : Fin (k + 1) → JointState nX nH,
      if P (sigma (Fin.last k)) then finiteFixedPrefixWeight kernel p b o sigma else 0 := by
  calc
    (∑ tau : FiniteTrajectory (U + k) nX nH nR,
        if finiteObservedPrefixExtra U k tau = o ∧
            P (tau.1 (cutStateExtraIndex U k)) then
          finitePathWeightFrom kernel p b tau else 0) =
        ∑ tau : FiniteTrajectory (U + k) nX nH nR,
          if finiteObservedPrefixExtra U k tau = o then
            finitePathWeightFrom kernel p b tau *
              (if P (tau.1 (cutStateExtraIndex U k)) then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro tau _
      by_cases ho : finiteObservedPrefixExtra U k tau = o <;>
        by_cases hP : P (tau.1 (cutStateExtraIndex U k)) <;> simp [ho, hP]
    _ = ∑ sigma : Fin (k + 1) → JointState nX nH,
          finiteFixedPrefixWeight kernel p b o sigma *
            (if P (sigma (Fin.last k)) then 1 else 0) :=
      sum_finitePathWeightFrom_fixedPrefix_cutWeight kernel b k U p o
        (fun s ↦ if P s then 1 else 0)
    _ = ∑ sigma : Fin (k + 1) → JointState nX nH,
          if P (sigma (Fin.last k)) then finiteFixedPrefixWeight kernel p b o sigma else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _
      by_cases hP : P (sigma (Fin.last k)) <;> simp [hP]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
