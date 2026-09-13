import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FinitePrefixMarginal

set_option linter.style.longLine false

/-! # Finite chronological history factorization -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

/-- Remove the final epoch of a finite trajectory, retaining its final action, reward, and state. -/
def finiteTrajectorySnocEquiv (T nX nH nR : Nat) :
    FiniteTrajectory (T + 1) nX nH nR ≃
      FiniteTrajectory T nX nH nR × ((Bool × Fin nR) × JointState nX nH) where
  toFun tau :=
    ((fun i ↦ tau.1 i.castSucc, fun i ↦ tau.2 i.castSucc),
      (tau.2 (Fin.last T), tau.1 (Fin.last (T + 1))))
  invFun z :=
    (Fin.lastCases z.2.2 z.1.1, Fin.lastCases z.2.1 z.1.2)
  left_inv tau := by
    apply Prod.ext
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
    · funext i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i <;> simp
  right_inv z := by
    rcases z with ⟨tau, ar, s⟩
    apply Prod.ext
    · apply Prod.ext <;> funext i <;> simp
    · apply Prod.ext <;> simp

/-- A chronological real path weight splits into its preceding path and final epoch. [the stated conclusion](goal). -/
lemma finitePathWeightFrom_snocEquiv_symm {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (z : FiniteTrajectory T nX nH nR × ((Bool × Fin nR) × JointState nX nH)) :
    finitePathWeightFrom kernel p b ((finiteTrajectorySnocEquiv T nX nH nR).symm z) =
      finitePathWeightFrom kernel p b z.1 *
        (b (z.1.1 (Fin.last T)).1 z.2.1.1).toReal *
          (kernel (z.1.1 (Fin.last T)) z.2.1.1 (z.2.1.2, z.2.2)).toReal := by
  rcases z with ⟨tau, ar, s⟩
  have hzero : Fin.lastCases s tau.1 (0 : Fin (T + 2)) = tau.1 0 := by
    cases T
    · rw [show (0 : Fin 2) = (0 : Fin 1).castSucc by rfl, Fin.lastCases_castSucc]
    · rw [show (0 : Fin (_ + 2)) = (0 : Fin (_ + 1)).castSucc by rfl,
        Fin.lastCases_castSucc]
  have hnext (x : Fin T) :
      Fin.lastCases s tau.1 x.castSucc.succ = tau.1 x.succ := by
    have hi : x.castSucc.succ = x.succ.castSucc := Fin.ext rfl
    rw [hi, Fin.lastCases_castSucc]
  simp [finitePathWeightFrom, finiteTrajectorySnocEquiv, Fin.prod_univ_castSucc,
    hzero, hnext]
  ring

/-- The first `k` observations of a trajectory with `U` trailing epochs. -/
def finiteObservedPrefixTrailing {nX nH nR : Nat} (k U : Nat)
    (tau : FiniteTrajectory (k + U) nX nH nR) : Fin k → Bool × Fin nR :=
  fun j ↦ tau.2 (Fin.castAdd U j)

/-- The first `k+1` states of a trajectory with `U` trailing epochs. -/
def finiteStatePrefixTrailing {nX nH nR : Nat} (k U : Nat)
    (tau : FiniteTrajectory (k + U) nX nH nR) : Fin (k + 1) → JointState nX nH :=
  fun j ↦ tau.1 ⟨j.val, by omega⟩

/-- Summing a chronological law over all suffixes leaves the exact state/observation-prefix
likelihood. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom_exactPrefix {nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) (k : Nat) (p : JointState nX nH → ℝ)
    (o : Fin k → Bool × Fin nR) (sigma : Fin (k + 1) → JointState nX nH) :
    ∀ U : Nat,
      (∑ tau : FiniteTrajectory (k + U) nX nH nR,
        if finiteObservedPrefixTrailing k U tau = o ∧
            finiteStatePrefixTrailing k U tau = sigma then
          finitePathWeightFrom kernel p b tau else 0) =
        finiteFixedPrefixWeight kernel p b o sigma := by
  intro U
  induction U with
  | zero =>
      classical
      change (∑ tau ∈ Finset.univ,
        if finiteObservedPrefixTrailing k 0 tau = o ∧
            finiteStatePrefixTrailing k 0 tau = sigma then
          finitePathWeightFrom kernel p b tau else 0) = _
      calc
        _ = if finiteObservedPrefixTrailing k 0 (sigma, o) = o ∧
              finiteStatePrefixTrailing k 0 (sigma, o) = sigma then
            finitePathWeightFrom kernel p b (sigma, o) else 0 := by
          apply Finset.sum_eq_single (sigma, o)
          · intro tau _ hne
            by_cases h : finiteObservedPrefixTrailing k 0 tau = o ∧
                finiteStatePrefixTrailing k 0 tau = sigma
            · exfalso
              apply hne
              apply Prod.ext
              · funext j
                simpa [finiteStatePrefixTrailing] using congrFun h.2 j
              · funext j
                simpa [finiteObservedPrefixTrailing] using congrFun h.1 j
            · simp [h]
          · simp
        _ = _ := by
          have ho : finiteObservedPrefixTrailing k 0 (sigma, o) = o := by
            funext j; rfl
          have hs : finiteStatePrefixTrailing k 0 (sigma, o) = sigma := by
            funext j; rfl
          rw [if_pos ⟨ho, hs⟩]
          rfl
  | succ U ih =>
      have hprefix (z : FiniteTrajectory (k + U) nX nH nR ×
          ((Bool × Fin nR) × JointState nX nH)) :
          (finiteObservedPrefixTrailing k (U + 1)
              ((finiteTrajectorySnocEquiv (k + U) nX nH nR).symm z) = o ∧
            finiteStatePrefixTrailing k (U + 1)
              ((finiteTrajectorySnocEquiv (k + U) nX nH nR).symm z) = sigma) ↔
          (finiteObservedPrefixTrailing k U z.1 = o ∧
            finiteStatePrefixTrailing k U z.1 = sigma) := by
        have ho : finiteObservedPrefixTrailing k (U + 1)
              ((finiteTrajectorySnocEquiv (k + U) nX nH nR).symm z) =
            finiteObservedPrefixTrailing k U z.1 := by
          funext j
          change Fin.lastCases z.2.1 z.1.2 _ = z.1.2 _
          rw [show Fin.castAdd (U + 1) j = (Fin.castAdd U j).castSucc by rfl,
            Fin.lastCases_castSucc]
        have hs : finiteStatePrefixTrailing k (U + 1)
              ((finiteTrajectorySnocEquiv (k + U) nX nH nR).symm z) =
            finiteStatePrefixTrailing k U z.1 := by
          funext j
          change Fin.lastCases z.2.2 z.1.1 _ = z.1.1 _
          rw [show (⟨j.val, by omega⟩ : Fin (k + (U + 1) + 1)) =
              (⟨j.val, by omega⟩ : Fin (k + U + 1)).castSucc by rfl,
            Fin.lastCases_castSucc]
        rw [ho, hs]
      calc
        (∑ tau : FiniteTrajectory (k + (U + 1)) nX nH nR,
            if finiteObservedPrefixTrailing k (U + 1) tau = o ∧
                finiteStatePrefixTrailing k (U + 1) tau = sigma then
              finitePathWeightFrom kernel p b tau else 0) =
            ∑ z : FiniteTrajectory (k + U) nX nH nR ×
                ((Bool × Fin nR) × JointState nX nH),
              if finiteObservedPrefixTrailing k U z.1 = o ∧
                  finiteStatePrefixTrailing k U z.1 = sigma then
                finitePathWeightFrom kernel p b
                  ((finiteTrajectorySnocEquiv (k + U) nX nH nR).symm z) else 0 := by
              apply Fintype.sum_equiv (finiteTrajectorySnocEquiv (k + U) nX nH nR)
              intro tau
              let z := finiteTrajectorySnocEquiv (k + U) nX nH nR tau
              have hp := hprefix z
              simp only [z, Equiv.symm_apply_apply] at hp
              simp only [hp, Equiv.symm_apply_apply]
        _ = ∑ tau : FiniteTrajectory (k + U) nX nH nR,
              if finiteObservedPrefixTrailing k U tau = o ∧
                  finiteStatePrefixTrailing k U tau = sigma then
                finitePathWeightFrom kernel p b tau else 0 := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro tau _
              by_cases hpref : finiteObservedPrefixTrailing k U tau = o ∧
                  finiteStatePrefixTrailing k U tau = sigma
              · simp only [hpref, if_true]
                simp_rw [finitePathWeightFrom_snocEquiv_symm]
                simp only [Fintype.sum_prod_type]
                simp only [true_and, if_true]
                have hk (a : Bool) :
                    (∑ r : Fin nR, ∑ x : Fin nX, ∑ h : Fin nH,
                      (kernel (tau.1 (Fin.last (k + U))) a (r, x, h)).toReal) = 1 := by
                  simpa only [Fintype.sum_prod_type] using
                    sum_pmf_toReal_eq_one (kernel (tau.1 (Fin.last (k + U))) a)
                simp_rw [← Finset.mul_sum, hk, mul_one]
                simp_rw [← Finset.mul_sum, sum_pmf_toReal_eq_one, mul_one]
              · simp [hpref]
        _ = finiteFixedPrefixWeight kernel p b o sigma := ih

/-- Finite-symbol state history through the current state. -/
def finiteHistStateView {T nX nH nR : Nat} (t : Fin T)
    (tau : FiniteTrajectory T nX nH nR) :=
  (((fun j ↦ tau.1 (prefixIndex t j).castSucc),
    (fun j ↦ tau.2 (prefixIndex t j))), tau.1 t.castSucc)

/-- Finite-symbol state history with the current action adjoined. -/
def finiteHistActionPair {T nX nH nR : Nat} (t : Fin T)
    (tau : FiniteTrajectory T nX nH nR) :=
  (finiteHistStateView t tau, (tau.2 t).1)

/-- Finite-symbol kernel history with the current reward and successor state adjoined. -/
def finiteHistNextPair {T nX nH nR : Nat} (t : Fin T)
    (tau : FiniteTrajectory T nX nH nR) :=
  (finiteHistActionPair t tau, ((tau.2 t).2, tau.1 t.succ))

/-- Reassemble the state prefix represented by a finite state-history view. -/
def finiteHistoryStates {k nX nH nR : Nat}
    (h : ((Fin k → JointState nX nH) × (Fin k → Bool × Fin nR)) ×
      JointState nX nH) : Fin (k + 1) → JointState nX nH :=
  Fin.lastCases h.2 h.1.1

/-- The mass of an exact finite state history is its chronological prefix likelihood. [the stated conclusion](goal). -/
lemma finiteHistStateView_mass_toReal {T nX nH nR : Nat}
    (F : FiniteRewardModel T nX nH nR) (t : Fin T)
    (h : ((Fin t.val → JointState nX nH) ×
      (Fin t.val → Bool × Fin nR)) × JointState nX nH) :
    ((F.law.map (finiteHistStateView t)) h).toReal =
      finiteFixedPrefixWeight F.kernel (fun s ↦ (F.init s).toReal) F.b
        h.1.2 (finiteHistoryStates h) := by
  classical
  rcases t with ⟨k, hk⟩
  obtain ⟨U, hTU⟩ : ∃ U, T = k + U := ⟨T - k, by omega⟩
  subst T
  obtain ⟨s, -⟩ := F.init.support_nonempty
  letI : NeZero nX := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt s.1.isLt)⟩
  letI : NeZero nH := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt s.2.isLt)⟩
  obtain ⟨q, -⟩ := (F.kernel s false).support_nonempty
  letI : NeZero nR := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt q.1.isLt)⟩
  have hlaw (tau : FiniteTrajectory (k + U) nX nH nR) :
      (F.law tau).toReal =
        finitePathWeightFrom F.kernel (fun s ↦ (F.init s).toReal) F.b tau := by
    rw [F.law_generated tau, ENNReal.toReal_mul, ENNReal.toReal_prod]
    unfold finitePathWeightFrom
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    rw [ENNReal.toReal_mul]
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_zero, hlaw]
    have hm := sum_finitePathWeightFrom_exactPrefix F.kernel F.b k
      (fun s ↦ (F.init s).toReal) h.1.2 (finiteHistoryStates h) U
    rw [← hm]
    apply Finset.sum_congr rfl
    intro tau _
    have heq : h = finiteHistStateView (⟨k, hk⟩ : Fin (k + U)) tau ↔
        finiteObservedPrefixTrailing k U tau = h.1.2 ∧
          finiteStatePrefixTrailing k U tau = finiteHistoryStates h := by
      constructor
      · intro hh
        subst h
        constructor <;> funext j
        · rfl
        · refine Fin.lastCases ?_ (fun i ↦ ?_) j
          · simp only [finiteStatePrefixTrailing, finiteHistoryStates,
              Fin.lastCases_last, finiteHistStateView]
            congr
          · simp only [finiteStatePrefixTrailing, finiteHistoryStates,
              Fin.lastCases_castSucc, finiteHistStateView]
            congr
      · rintro ⟨ho, hs⟩
        apply Prod.ext
        · apply Prod.ext
          · funext j
            calc
              h.1.1 j = finiteHistoryStates h j.castSucc := by
                simp [finiteHistoryStates]
              _ = finiteStatePrefixTrailing k U tau j.castSucc :=
                (congrFun hs j.castSucc).symm
              _ = _ := by congr
          · exact ho.symm
        ·
          calc
            h.2 = finiteHistoryStates h (Fin.last k) := by simp [finiteHistoryStates]
            _ = finiteStatePrefixTrailing k U tau (Fin.last k) :=
              (congrFun hs (Fin.last k)).symm
            _ = _ := by congr
    by_cases hx : h = finiteHistStateView (⟨k, hk⟩ : Fin (k + U)) tau
    · simp [hx, heq.mp hx]
    · rw [if_neg hx, if_neg (fun hp ↦ hx (heq.mpr hp))]
  · intro tau _
    by_cases hh : h = finiteHistStateView (⟨k, hk⟩ : Fin (k + U)) tau
    · simpa [hh] using F.law.apply_ne_top tau
    · simp [hh]

end CausalSmith.Stat.PomdpLatentOverlapMinimax
