import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.FiniteEncodingCore

set_option linter.style.longLine false

/-! # Chronological marginalization for finite path weights -/

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators ENNReal

/-- The real-valued masses of a finite PMF sum to one. [the stated conclusion](goal). -/
lemma sum_pmf_toReal_eq_one {A : Type*} [Fintype A] (p : PMF A) :
    ∑ a, (p a).toReal = 1 := by
  calc
    ∑ a, (p a).toReal = ∑' a, (p a).toReal := (tsum_fintype _).symm
    _ = (∑' a, p a).toReal :=
      (ENNReal.tsum_toReal_eq (f := fun a : A ↦ p a)
        (fun a ↦ PMF.apply_ne_top p a)).symm
    _ = 1 := by rw [p.tsum_coe, ENNReal.toReal_one]

/-- Chronological path weight with an arbitrary real initial-state weight. -/
noncomputable def finitePathWeightFrom {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (tau : FiniteTrajectory T nX nH nR) : ℝ :=
  p (tau.1 0) *
    ∏ t : Fin T,
      (b (tau.1 t.castSucc).1 (tau.2 t).1).toReal *
        (kernel (tau.1 t.castSucc) (tau.2 t).1
          ((tau.2 t).2, tau.1 t.succ)).toReal

/-- The public finite path weight is the arbitrary-initial-weight form specialized to the
real masses of the supplied initial PMF. [the stated conclusion](goal). -/
lemma finitePathWeight_eq_finitePathWeightFrom {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool)
    (tau : FiniteTrajectory T nX nH nR) :
    finitePathWeight kernel init b tau =
      finitePathWeightFrom kernel (fun s ↦ (init s).toReal) b tau := rfl

/-- A positive-length trajectory is its initial state and first observation followed by a tail
trajectory.  This is the carrier-level decomposition used by chronological peeling proofs. -/
def finiteTrajectorySuccEquiv (T nX nH nR : Nat) :
    FiniteTrajectory (T + 1) nX nH nR ≃
      (JointState nX nH × (Bool × Fin nR)) × FiniteTrajectory T nX nH nR where
  toFun tau := ((tau.1 0, tau.2 0), (fun i ↦ tau.1 i.succ, fun i ↦ tau.2 i.succ))
  invFun z :=
    (Fin.cases z.1.1 z.2.1, Fin.cases z.1.2 z.2.2)
  left_inv tau := by
    apply Prod.ext
    · funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
    · funext i
      refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  right_inv z := by
    rcases z with ⟨⟨s, ar⟩, tau⟩
    apply Prod.ext
    · apply Prod.ext <;> rfl
    · apply Prod.ext
      · funext i
        rfl
      · funext i
        rfl

/-- Peeling the first epoch leaves the same chronological product on the tail. [the stated conclusion](goal). -/
lemma finitePathWeightFrom_succEquiv_symm {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (p : JointState nX nH → ℝ) (b : Fin nX → PMF Bool)
    (z : (JointState nX nH × (Bool × Fin nR)) × FiniteTrajectory T nX nH nR) :
    finitePathWeightFrom kernel p b ((finiteTrajectorySuccEquiv T nX nH nR).symm z) =
      p z.1.1 * (b z.1.1.1 z.1.2.1).toReal *
        (kernel z.1.1 z.1.2.1 (z.1.2.2, z.2.1 0)).toReal *
          (∏ t : Fin T,
            (b (z.2.1 t.castSucc).1 (z.2.2 t).1).toReal *
              (kernel (z.2.1 t.castSucc) (z.2.2 t).1
                ((z.2.2 t).2, z.2.1 t.succ)).toReal) := by
  rcases z with ⟨⟨s, ar⟩, tau⟩
  simp [finitePathWeightFrom, finiteTrajectorySuccEquiv, Fin.prod_univ_succ]
  ring

/-- A zero-length trajectory carries only its initial state. -/
def finiteTrajectoryZeroEquiv (nX nH nR : Nat) :
    FiniteTrajectory 0 nX nH nR ≃ JointState nX nH where
  toFun tau := tau.1 0
  invFun s := (fun _ ↦ s, fun i ↦ Fin.elim0 i)
  left_inv tau := by
    apply Prod.ext
    · funext i
      exact Fin.eq_zero i ▸ rfl
    · funext i
      exact Fin.elim0 i
  right_inv s := rfl

/-- Summing chronological path weights eliminates every generated epoch and leaves the total
initial-state weight. [the stated conclusion](goal). -/
lemma sum_finitePathWeightFrom {nX nH nR : Nat} [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (b : Fin nX → PMF Bool) : ∀ (T : Nat) (p : JointState nX nH → ℝ),
    (∑ tau : FiniteTrajectory T nX nH nR, finitePathWeightFrom kernel p b tau) =
      ∑ s, p s := by
  intro T
  induction T with
  | zero =>
      intro p
      rw [Fintype.sum_equiv (finiteTrajectoryZeroEquiv nX nH nR)
        (fun tau ↦ finitePathWeightFrom kernel p b tau) p]
      intro tau
      simp [finitePathWeightFrom, finiteTrajectoryZeroEquiv]
  | succ T ih =>
      intro p
      let pNext : JointState nX nH → ℝ := fun s' ↦
        ∑ z : JointState nX nH × Bool,
          p z.1 * (b z.1.1 z.2).toReal *
            ∑ r : Fin nR, (kernel z.1 z.2 (r, s')).toReal
      calc
        (∑ tau : FiniteTrajectory (T + 1) nX nH nR,
            finitePathWeightFrom kernel p b tau) =
            ∑ z : (JointState nX nH × (Bool × Fin nR)) ×
                FiniteTrajectory T nX nH nR,
              finitePathWeightFrom kernel p b
                ((finiteTrajectorySuccEquiv T nX nH nR).symm z) := by
          apply Fintype.sum_equiv (finiteTrajectorySuccEquiv T nX nH nR)
          intro tau
          rw [Equiv.symm_apply_apply]
        _ = ∑ tau : FiniteTrajectory T nX nH nR,
              finitePathWeightFrom kernel pNext b tau := by
          rw [Fintype.sum_prod_type]
          simp_rw [finitePathWeightFrom_succEquiv_symm]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro tau _
          simp only [pNext, Fintype.sum_prod_type]
          rw [finitePathWeightFrom]
          simp_rw [← Finset.sum_mul]
          have hhead :
              (∑ x : Fin nX, ∑ h : Fin nH, ∑ a : Bool, ∑ r : Fin nR,
                p (x, h) * (b x a).toReal *
                  (kernel (x, h) a (r, tau.1 0)).toReal) =
              ∑ x : Fin nX, ∑ h : Fin nH, ∑ a : Bool,
                p (x, h) * (b x a).toReal *
                  ∑ r : Fin nR, (kernel (x, h) a (r, tau.1 0)).toReal := by
            apply Finset.sum_congr rfl
            intro x _
            apply Finset.sum_congr rfl
            intro h _
            apply Finset.sum_congr rfl
            intro a _
            rw [Finset.mul_sum]
          rw [hhead]
        _ = ∑ s, pNext s := ih pNext
        _ = ∑ s, p s := by
          simp only [pNext]
          rw [Finset.sum_comm]
          calc
            (∑ z : JointState nX nH × Bool,
                ∑ s' : JointState nX nH,
                  p z.1 * (b z.1.1 z.2).toReal *
                    ∑ r : Fin nR, (kernel z.1 z.2 (r, s')).toReal) =
                ∑ z : JointState nX nH × Bool,
                  p z.1 * (b z.1.1 z.2).toReal := by
              apply Finset.sum_congr rfl
              intro z _
              simp_rw [← Finset.mul_sum]
              have hk : ∑ s' : JointState nX nH,
                  ∑ r : Fin nR, (kernel z.1 z.2 (r, s')).toReal = 1 := by
                rw [Finset.sum_comm]
                simpa only [Fintype.sum_prod_type] using
                  sum_pmf_toReal_eq_one (kernel z.1 z.2)
              rw [hk, mul_one]
            _ = ∑ s, p s := by
              simp only [Fintype.sum_prod_type]
              simp_rw [← Finset.mul_sum, sum_pmf_toReal_eq_one, mul_one]

/-- Chronological finite path weights are nonnegative. [the stated conclusion](goal). -/
lemma finitePathWeight_nonneg {T nX nH nR : Nat}
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool)
    (tau : FiniteTrajectory T nX nH nR) :
    0 ≤ finitePathWeight kernel init b tau := by
  unfold finitePathWeight
  positivity

/-- Chronological finite path weights have total mass one. [the stated conclusion](goal). -/
lemma sum_finitePathWeight_eq_one {T nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool) :
    ∑ tau : FiniteTrajectory T nX nH nR, finitePathWeight kernel init b tau = 1 := by
  simp_rw [finitePathWeight_eq_finitePathWeightFrom]
  rw [sum_finitePathWeightFrom, sum_pmf_toReal_eq_one]

/-- Normalizing already normalized nonnegative finite real weights preserves every weight. [the hw condition](hyp:hw); and [the hsum condition](hyp:hsum). [the stated conclusion](goal). -/
lemma pmfOfRealWeight_apply_of_nonneg_sum_one {A : Type*} [Fintype A] [Nonempty A]
    (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (hsum : ∑ a, w a = 1) (a : A) :
    pmfOfRealWeight w a = ENNReal.ofReal (w a) := by
  have hmass : ∑' a, ENNReal.ofReal (w a) = 1 := by
    rw [tsum_fintype]
    calc
      ∑ a, ENNReal.ofReal (w a) = ENNReal.ofReal (∑ a, w a) := by
        symm
        exact ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hw i)
      _ = 1 := by rw [hsum]; norm_num
  rw [pmfOfRealWeight, dif_neg (by rw [hmass]; norm_num), PMF.normalize_apply,
    hmass, inv_one, mul_one]

/-- The normalized finite path PMF agrees pointwise with its chronological product. [the stated conclusion](goal). -/
lemma finitePathPMF_apply {T nX nH nR : Nat} [NeZero nX] [NeZero nH] [NeZero nR]
    (kernel : JointState nX nH → Bool → PMF (Fin nR × JointState nX nH))
    (init : PMF (JointState nX nH)) (b : Fin nX → PMF Bool)
    (tau : FiniteTrajectory T nX nH nR) :
    finitePathPMF kernel init b tau =
      init (tau.1 0) *
        ∏ t : Fin T,
          b (tau.1 t.castSucc).1 (tau.2 t).1 *
            kernel (tau.1 t.castSucc) (tau.2 t).1 ((tau.2 t).2, tau.1 t.succ) := by
  rw [finitePathPMF,
    pmfOfRealWeight_apply_of_nonneg_sum_one (finitePathWeight kernel init b)
      (finitePathWeight_nonneg kernel init b) (sum_finitePathWeight_eq_one kernel init b)]
  rw [← ENNReal.toReal_eq_toReal_iff' ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
      (ENNReal.prod_ne_top fun t _ ↦
        ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)))]
  rw [ENNReal.toReal_ofReal (finitePathWeight_nonneg kernel init b tau),
    ENNReal.toReal_mul]
  unfold finitePathWeight
  congr 1
  rw [ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro t _
  rw [ENNReal.toReal_mul]

-- @node: embed_initial_marginal
/-- The embedded chronological finite path law has the supplied initial marginal. [the stated conclusion](goal). -/
lemma embed_initial_marginal {T nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (F : FiniteRewardModel T nX nH nR) (s : JointState nX nH) :
    ((embed F).law.map (stateAt (T := T) (nX := nX) (nH := nH) 0)) {s} =
      ENNReal.ofReal ((embed F).init s) := by
  classical
  change MeasureTheory.Measure.map (stateAt 0)
      (F.law.map (decodeTraj F.rew)).toMeasure {s} = ENNReal.ofReal (F.init s).toReal
  rw [PMF.toMeasure_map]
  rw [PMF.map_comp]
  have hcomp : (@stateAt T nX nH 0) ∘ (@decodeTraj T nX nH nR F.rew) =
      fun tau : FiniteTrajectory T nX nH nR ↦ tau.1 0 := by rfl
  rw [hcomp]
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_singleton_iff]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [PMF.map_apply]
  rw [tsum_fintype, ENNReal.ofReal_toReal (F.init.apply_ne_top s)]
  rw [← ENNReal.toReal_eq_toReal_iff'
    ((ENNReal.sum_ne_top).2 fun tau _ ↦ by
      by_cases h : s = tau.1 0
      · simpa [h] using F.law.apply_ne_top tau
      · simp [h])
    (F.init.apply_ne_top s), ENNReal.toReal_sum]
  have hreal : (∑ tau, (if tau.1 0 = s then F.law tau else 0).toReal) =
      (F.init s).toReal := by
    calc
      (∑ tau, (if tau.1 0 = s then F.law tau else 0).toReal) =
          ∑ tau, finitePathWeightFrom F.kernel
            (fun s' ↦ if s' = s then (F.init s').toReal else 0) F.b tau := by
        apply Finset.sum_congr rfl
        intro tau _
        by_cases hs : tau.1 0 = s
        · simp only [hs, ↓reduceIte]
          rw [F.law_generated tau, ENNReal.toReal_mul, ENNReal.toReal_prod]
          simp only [ENNReal.toReal_mul]
          unfold finitePathWeightFrom
          simp [hs]
        · simp only [hs, ↓reduceIte, ENNReal.toReal_zero]
          unfold finitePathWeightFrom
          simp [hs]
      _ = ∑ s', if s' = s then (F.init s').toReal else 0 :=
        sum_finitePathWeightFrom F.kernel F.b T _
      _ = (F.init s).toReal := by simp
  calc
    _ = ∑ tau, (if tau.1 0 = s then F.law tau else 0).toReal := by
      apply Finset.sum_congr rfl
      intro tau _
      by_cases h : tau.1 0 = s
      · simp [h]
      · have hn : ¬s = tau.1 0 := fun hs ↦ h hs.symm
        simp [h, hn]
    _ = _ := hreal
  all_goals
    first
    | exact (measurable_pi_apply 0).comp measurable_fst
    | (intro tau _
       by_cases h : s = tau.1 0
       · simpa [h] using F.law.apply_ne_top tau
       · simp [h])

/-- A stationary finite initial vector remains stationary after reward decoding. [the hstat condition](hyp:hstat); and [the hsel condition](hyp:hsel). [the stated conclusion](goal). -/
lemma embed_stationaryStart {T nX nH nR : Nat}
    [NeZero nX] [NeZero nH] [NeZero nR]
    (F : FiniteRewardModel T nX nH nR)
    (hstat : IsStationary (policyKernel (embed F) (embed F).b) (embed F).init)
    (hsel : stationaryLaw (policyKernel (embed F) (embed F).b) = (embed F).init) :
    StationaryStart (embed F) := by
  constructor
  · simpa [hsel] using hstat
  · intro s
    simpa [hsel] using embed_initial_marginal F s

end CausalSmith.Stat.PomdpLatentOverlapMinimax
