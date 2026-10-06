module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwScoreMoments

/-! # Weighted future-state peeling under the behavior policy. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

/-- A real-valued history multiplier followed by target-policy likelihood
ratios up to (but excluding) the current epoch. -/
noncomputable def weightedRatioCarrier {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (h : PreHistory T nX nH k r) : ℝ :=
  G (restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr h) *
    ∏ q : Fin r.val, if j.val ≤ q.val then
      ratio M.b M.e (h.1 q).1 (h.2.1 q).1 else 1

lemma weightedRatioCarrier_measurable {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (hG : Measurable G) :
    Measurable (weightedRatioCarrier M j r hjr G) := by
  unfold weightedRatioCarrier
  apply Measurable.mul (hG.comp (restrictPreHist_measurable j r hjr))
  apply Finset.measurable_prod
  intro q _
  by_cases hq : j.val ≤ q.val
  · simp only [if_pos hq]
    exact (measurable_of_countable fun xa : Fin nX × Fin k =>
      ratio M.b M.e xa.1 xa.2).comp
        (((by fun_prop : Measurable fun h : PreHistory T nX nH k r => (h.1 q).1)).prodMk
          (by fun_prop : Measurable fun h : PreHistory T nX nH k r => (h.2.1 q).1))
  · simp only [if_neg hq]
    fun_prop

lemma weightedRatioCarrier_preHist {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (w : FullPath T nX nH k) :
    weightedRatioCarrier M j r hjr G (preHist r w) =
      G (preHist j w) * ∏ q : Fin r.val, if j.val ≤ q.val then
        ratio M.b M.e (currentState w (pastIndex r q)).1
          (actionAt w (pastIndex r q)) else 1 := by
  unfold weightedRatioCarrier
  rw [restrictPreHist_preHist]
  rfl

lemma weightedRatioCarrier_self {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j : Fin T)
    (G : PreHistory T nX nH k j → ℝ) (h : PreHistory T nX nH k j) :
    weightedRatioCarrier M j j le_rfl G h = G h := by
  unfold weightedRatioCarrier restrictPreHist
  have hq : ∀ q : Fin j.val, ¬j.val ≤ q.val := by intro q; omega
  simp [hq]

lemma weightedRatioCarrier_next {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (j r : Fin T) (hjr : j.val ≤ r.val)
    (hr : r.val + 1 < T) (G : PreHistory T nX nH k j → ℝ)
    (q : PostHistory T nX nH k r × (ℝ × JointState nX nH)) :
    weightedRatioCarrier M j ⟨r.val + 1, hr⟩ (Nat.le_succ_of_le hjr) G
        (nextPreHistory r hr q) =
      weightedRatioCarrier M j r hjr G q.1.1 *
        ratio M.b M.e q.1.1.2.2.1 q.1.2 := by
  unfold weightedRatioCarrier
  rw [restrictPreHist_nextPreHistory j r hjr hr q]
  rw [Fin.prod_univ_castSucc]
  simp only [nextPreHistory, Fin.snoc_castSucc, Fin.snoc_last]
  have hprod : (∏ x : Fin r.val, if j.val ≤ x.castSucc.val then
      ratio M.b M.e (q.1.1.1 x).1 (q.1.1.2.1 x).1 else 1) =
      ∏ x : Fin r.val, if j.val ≤ x.val then
        ratio M.b M.e (q.1.1.1 x).1 (q.1.1.2.1 x).1 else 1 := by
    apply Finset.prod_congr rfl
    intro x _
    rfl
  rw [hprod, if_pos (by simpa using hjr)]
  ring

lemma weightedRatioCarrier_norm_bound {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (h : PreHistory T nX nH k r) :
    ‖weightedRatioCarrier M j r hjr G h‖ ≤
      ‖G (restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr h)‖ *
        max 1 (policyFactor zeta) ^ r.val := by
  unfold weightedRatioCarrier
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun q _ => by
    split_ifs
    · exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
    · exact zero_le_one)]
  calc
    (∏ q : Fin r.val, if j.val ≤ q.val then
        ratio M.b M.e (h.1 q).1 (h.2.1 q).1 else 1) ≤
        ∏ _q : Fin r.val, max 1 (policyFactor zeta) := by
      apply Finset.prod_le_prod
      · intro q _
        split_ifs
        · exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
        · exact zero_le_one
      · intro q _
        split_ifs
        · exact (policy_ratio_bounds M hOverlap hA.1 _ _).2.trans (le_max_right _ _)
        · exact le_max_left _ _
    _ = _ := by simp

/-- A measurable integrable multiplier from the pre-action history may be
carried through one behavior-policy transition. -/
lemma integral_preHist_mul_nextState_eq_behaviorStep {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (r : Fin T)
    (G : PreHistory T nX nH k r → ℝ) (hGm : Measurable G)
    (hGi : Integrable (fun w => G (preHist r w)) M.law)
    (F : JointState nX nH → ℝ) :
    ∫ w, G (preHist r w) * F (nextState w r) ∂M.law =
      ∫ w, G (preHist r w) * behaviorStep M F (currentState w r) ∂M.law := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  letI : IsMarkovKernel (actionKernel M) := by
    refine ⟨fun x => ⟨?_⟩⟩
    change (∑ a : Fin k, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp only [Measure.finsetSum_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (by intro a _; exact (hA.1 x).1 a)]
    simp [(hA.1 x).2]
  let C := ∑ s : JointState nX nH, ‖F s‖
  have hC (s : JointState nX nH) : ‖F s‖ ≤ C :=
    Finset.single_le_sum (fun x _ => norm_nonneg (F x)) (Finset.mem_univ s)
  have hpre : Measurable (preHist r : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  have hcur : Measurable (fun w : FullPath T nX nH k => currentState w r) := by
    unfold currentState
    fun_prop
  have hact : Measurable (fun w : FullPath T nX nH k => actionAt w r) := by
    unfold actionAt
    fun_prop
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hmjoint : Measurable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        G z.1.1 * F z.2.2) :=
    (hGm.comp (by fun_prop)).mul ((measurable_of_finite F).comp (by fun_prop))
  have hjoint : Integrable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        G z.1.1 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
    rw [integrable_map_measure hmjoint.aestronglyMeasurable henc.aemeasurable]
    apply hGi.mul_bdd
      (((measurable_of_finite F).comp (by
        unfold nextState
        fun_prop)).aestronglyMeasurable)
    filter_upwards with w
    exact hC (nextState w r)
  have hpost : Measurable (postHist r : FullPath T nX nH k → _) := by
    unfold postHist preHist currentState pastIndex actionAt
    fun_prop
  have hinner : Integrable
      (fun h : PostHistory T nX nH k r =>
        G h.1 * ∫ y, F y.2 ∂M.K h.1.2.2 h.2)
      (M.law.map (postHist r)) := by
    have hm : Measurable (fun h : PostHistory T nX nH k r =>
        G h.1 * ∫ y, F y.2 ∂M.K h.1.2.2 h.2) :=
      (hGm.comp measurable_fst).mul
        ((measurable_of_countable fun sa : JointState nX nH × Fin k =>
          ∫ y, F y.2 ∂M.K sa.1 sa.2).comp
            ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
              measurable_snd))
    rw [integrable_map_measure hm.aestronglyMeasurable hpost.aemeasurable]
    change Integrable (fun w => G (preHist r w) *
      ∫ y, F y.2 ∂M.K (currentState w r) (actionAt w r)) M.law
    apply hGi.mul_bdd
      (((measurable_of_countable fun sa : JointState nX nH × Fin k =>
        ∫ y, F y.2 ∂M.K sa.1 sa.2).comp
          (hcur.prodMk hact)).aestronglyMeasurable)
    filter_upwards with w
    letI : IsProbabilityMeasure (M.K (currentState w r) (actionAt w r)) := hK.1 _ _
    calc
      ‖∫ y, F y.2 ∂M.K (currentState w r) (actionAt w r)‖ ≤
          C * (M.K (currentState w r) (actionAt w r)).real Set.univ :=
        norm_integral_le_of_norm_le_const
          (by filter_upwards with y; exact hC y.2)
      _ = C := by simp
  calc
    (∫ w, G (preHist r w) * F (nextState w r) ∂M.law) =
        ∫ z, G z.1.1 * F z.2.2
          ∂(M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      rfl
    _ = ∫ h, ∫ y, G h.1 * F y.2 ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist r)) :=
      full_history_integral_kernel_step M hK r _ hjoint
    _ = ∫ h, G h.1 * (∫ y, F y.2 ∂M.K h.1.2.2 h.2)
          ∂(M.law.map (postHist r)) := by
      apply integral_congr_ae
      filter_upwards with h
      rw [integral_const_mul]
    _ = ∫ h, ∑ a : Fin k, M.b h.2.2.1 a *
          (G h * ∫ y, F y.2 ∂M.K h.2.2 a)
          ∂(M.law.map (preHist r)) := by
      change (∫ h, G h.1 * (∫ y, F y.2 ∂M.K h.1.2.2 h.2)
        ∂(M.law.map (fun w => (preHist r w, actionAt w r)))) = _
      change Integrable (fun h : PreHistory T nX nH k r × Fin k =>
        G h.1 * ∫ y, F y.2 ∂M.K h.1.2.2 h.2)
        (M.law.map (fun w => (preHist r w, actionAt w r))) at hinner
      rw [hA.2 r] at hinner ⊢
      rw [Measure.integral_compProd hinner]
      apply integral_congr_ae
      filter_upwards with h
      change (∫ a, G h * (∫ y, F y.2 ∂M.K h.2.2 a) ∂
        ∑ a : Fin k, ENNReal.ofReal (M.b h.2.2.1 a) • Measure.dirac a) = _
      rw [integral_finsetSum_measure (fun a _ =>
        (integrable_dirac (f := fun a : Fin k => G h * ∫ y, F y.2 ∂M.K h.2.2 a)
          enorm_lt_top).smul_measure ENNReal.ofReal_ne_top)]
      simp_rw [integral_smul_measure, integral_dirac,
        ENNReal.toReal_ofReal ((hA.1 _).1 _), smul_eq_mul]
    _ = ∫ h, G h * behaviorStep M F h.2.2 ∂(M.law.map (preHist r)) := by
      apply integral_congr_ae
      filter_upwards with h
      rw [← behaviorStep_eq_action_integral M hK]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact (hGm.mul ((measurable_of_finite (behaviorStep M F)).comp
          (by fun_prop))).aestronglyMeasurable

/-- Iterating weighted behavior peeling propagates a future state function
back to the history where the multiplier is measurable. -/
lemma integral_preHist_mul_behaviorIter {T nX nH k n : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (j : Fin T) (hn : j.val + n < T)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hGi : Integrable (fun w => G (preHist j w)) M.law)
    (F : JointState nX nH → ℝ) :
    ∫ w, G (preHist j w) * F (currentState w ⟨j.val + n, hn⟩) ∂M.law =
      ∫ w, G (preHist j w) * ((behaviorStep M)^[n] F) (currentState w j) ∂M.law := by
  induction n generalizing F with
  | zero =>
      have he : (⟨j.val + 0, hn⟩ : Fin T) = j := Fin.ext (by simp)
      simp [he]
  | succ n ih =>
      let r : Fin T := ⟨j.val + n, by omega⟩
      have hjr : j.val ≤ r.val := by dsimp [r]; omega
      let Gr : PreHistory T nX nH k r → ℝ := fun h =>
        G (restrictPreHist (nX := nX) (nH := nH) (k := k) j r hjr h)
      have hGrm : Measurable Gr := by
        apply hGm.comp
        unfold restrictPreHist
        by_cases heq : j.val = r.val <;> simp [heq] <;> fun_prop
      have hGre : (fun w : FullPath T nX nH k => Gr (preHist r w)) =
          fun w => G (preHist j w) := by
        funext w
        unfold Gr
        rw [restrictPreHist_preHist]
      have hGri : Integrable (fun w : FullPath T nX nH k => Gr (preHist r w)) M.law := by
        rw [hGre]
        exact hGi
      have hstep := integral_preHist_mul_nextState_eq_behaviorStep
        M hK hA r Gr hGrm hGri F
      have hnext : (fun w : FullPath T nX nH k => F (nextState w r)) =
          fun w => F (currentState w ⟨j.val + (n + 1), hn⟩) := by
        funext w
        unfold nextState currentState
        congr 2
      have hstep' :
          (∫ w, G (preHist j w) * F (currentState w ⟨j.val + (n + 1), hn⟩) ∂M.law) =
          ∫ w, G (preHist j w) * behaviorStep M F (currentState w r) ∂M.law := by
        calc
          _ = ∫ w, Gr (preHist r w) * F (nextState w r) ∂M.law := by
            apply integral_congr_ae
            filter_upwards with w
            rw [congrFun hGre w, congrFun hnext w]
          _ = _ := hstep
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with w
            rw [congrFun hGre w]
      rw [hstep']
      change (∫ w, G (preHist j w) *
        behaviorStep M F (currentState w ⟨j.val + n, by omega⟩) ∂M.law) = _
      rw [ih (by omega) (behaviorStep M F)]
      have hc : ((behaviorStep M)^[n] (behaviorStep M F)) =
          behaviorStep M ((behaviorStep M)^[n] F) :=
        (Function.iterate_succ_apply (behaviorStep M) n F).symm.trans
          (Function.iterate_succ_apply' (behaviorStep M) n F)
      rw [hc, Function.iterate_succ_apply']

/-- One target-policy likelihood-ratio step for a real-valued history carrier.
The two integrability premises are exactly the kernel and action expressions
used by Fubini and policy change. -/
lemma weightedRatioCarrier_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val) (hr : r.val + 1 < T)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (F : JointState nX nH → ℝ)
    (hjoint : Integrable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j r hjr G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))))
    (haction : Integrable
      (fun z : PreHistory T nX nH k r × Fin k =>
        weightedRatioCarrier M j r hjr G z.1 *
          ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist r w, actionAt w r)))) :
    ∫ w, weightedRatioCarrier M j ⟨r.val + 1, hr⟩
          (Nat.le_succ_of_le hjr) G (preHist ⟨r.val + 1, hr⟩ w) *
          F (currentState w ⟨r.val + 1, hr⟩) ∂M.law =
      ∫ w, weightedRatioCarrier M j r hjr G (preHist r w) *
          targetStep M F (currentState w r) ∂M.law := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist r : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ z, weightedRatioCarrier M j r hjr G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2
          ∂(M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      apply integral_congr_ae
      filter_upwards with w
      rw [← nextPreHistory_path r hr w,
        weightedRatioCarrier_next M j r hjr hr G]
      rfl
    _ = ∫ h, ∫ y, weightedRatioCarrier M j r hjr G h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * F y.2 ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist r)) :=
      full_history_integral_kernel_step M hK r _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (weightedRatioCarrier M j r hjr G z.1 *
            ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
          ∂(M.law.map (fun w => (preHist r w, actionAt w r))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (weightedRatioCarrier M j r hjr G h *
            ∫ y, F y.2 ∂M.K h.2.2 a) ∂(M.law.map (preHist r)) :=
      full_history_integral_ratio_step M hA hOverlap r _ haction
    _ = ∫ h, weightedRatioCarrier M j r hjr G h * targetStep M F h.2.2
          ∂(M.law.map (preHist r)) := by
      apply integral_congr_ae
      filter_upwards with h
      rw [← targetStep_eq_action_integral M hK, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((weightedRatioCarrier_measurable M j r hjr G hGm).mul
          ((measurable_of_finite (targetStep M F)).comp (by fun_prop))).aestronglyMeasurable

/-- The kernel-side integrability premise of weighted target peeling follows
from integrability of the starting multiplier, since all later factors are
uniformly bounded on finite carriers. -/
lemma weightedRatioCarrier_kernel_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M) (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hGi : Integrable (fun w => G (preHist j w)) M.law)
    (F : JointState nX nH → ℝ) :
    Integrable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j r hjr G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2)
      (M.law.map (fun w => (postHist r w, (rewardAt w r, nextState w r)))) := by
  obtain ⟨C, hC⟩ := Finite.exists_le (fun s : JointState nX nH => ‖F s‖)
  let D := max 1 (policyFactor zeta) ^ r.val * policyFactor zeta * C
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist r w, (rewardAt w r, nextState w r))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hm : Measurable
      (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j r hjr G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * F z.2.2) :=
    (((weightedRatioCarrier_measurable M j r hjr G hGm).comp
      (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
        z.1.1) by fun_prop)).mul
      ((measurable_of_countable fun xa : Fin nX × Fin k => ratio M.b M.e xa.1 xa.2).comp
        (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
          (z.1.1.2.2.1, z.1.2)) by fun_prop))).mul
      ((measurable_of_finite F).comp
        (show Measurable (fun z : PostHistory T nX nH k r × (ℝ × JointState nX nH) =>
          z.2.2) by fun_prop))
  rw [integrable_map_measure hm.aestronglyMeasurable henc.aemeasurable]
  apply (hGi.abs.const_mul D).mono' ((hm.comp henc).aestronglyMeasurable)
  filter_upwards with w
  dsimp only [Function.comp_apply]
  change ‖weightedRatioCarrier M j r hjr G (preHist r w) *
    ratio M.b M.e (currentState w r).1 (actionAt w r) * F (nextState w r)‖ ≤
      D * |G (preHist j w)|
  rw [norm_mul, norm_mul]
  have hc := weightedRatioCarrier_norm_bound M hA hOverlap j r hjr G (preHist r w)
  rw [restrictPreHist_preHist] at hc
  have hr : ‖ratio M.b M.e (currentState w r).1 (actionAt w r)‖ ≤
      policyFactor zeta := by
    rw [Real.norm_eq_abs, abs_of_nonneg (policy_ratio_bounds M hOverlap hA.1 _ _).1]
    exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
  calc
    _ ≤ (‖G (preHist j w)‖ * max 1 (policyFactor zeta) ^ r.val) *
          policyFactor zeta * C := by
      exact mul_le_mul (mul_le_mul hc hr (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))) (hC (nextState w r))
        (norm_nonneg _) (mul_nonneg
          (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
          (Real.exp_nonneg _))
    _ = D * |G (preHist j w)| := by dsimp [D]; ring

/-- The action-side integrability premise of weighted target peeling. -/
lemma weightedRatioCarrier_action_integrable {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j r : Fin T) (hjr : j.val ≤ r.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hGi : Integrable (fun w => G (preHist j w)) M.law)
    (F : JointState nX nH → ℝ) :
    Integrable
      (fun z : PreHistory T nX nH k r × Fin k =>
        weightedRatioCarrier M j r hjr G z.1 *
          ∫ y, F y.2 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist r w, actionAt w r))) := by
  let C := ∑ sa : JointState nX nH × Fin k,
    ‖∫ y, F y.2 ∂M.K sa.1 sa.2‖
  have hC (sa : JointState nX nH × Fin k) :
      ‖∫ y, F y.2 ∂M.K sa.1 sa.2‖ ≤ C :=
    Finset.single_le_sum (fun x _ => norm_nonneg
      (∫ y, F y.2 ∂M.K x.1 x.2)) (Finset.mem_univ sa)
  let D := max 1 (policyFactor zeta) ^ r.val * C
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (preHist r w, actionAt w r)) := by
    unfold preHist currentState pastIndex actionAt
    fun_prop
  have hm : Measurable
      (fun z : PreHistory T nX nH k r × Fin k =>
        weightedRatioCarrier M j r hjr G z.1 *
          ∫ y, F y.2 ∂M.K z.1.2.2 z.2) :=
    ((weightedRatioCarrier_measurable M j r hjr G hGm).comp measurable_fst).mul
      ((measurable_of_countable fun sa : JointState nX nH × Fin k =>
        ∫ y, F y.2 ∂M.K sa.1 sa.2).comp
          (show Measurable (fun z : PreHistory T nX nH k r × Fin k =>
            (z.1.2.2, z.2)) by fun_prop))
  rw [integrable_map_measure hm.aestronglyMeasurable henc.aemeasurable]
  apply (hGi.abs.const_mul D).mono' ((hm.comp henc).aestronglyMeasurable)
  filter_upwards with w
  dsimp only [Function.comp_apply]
  change ‖weightedRatioCarrier M j r hjr G (preHist r w) *
    ∫ y, F y.2 ∂M.K (currentState w r) (actionAt w r)‖ ≤
      D * |G (preHist j w)|
  rw [norm_mul]
  have hc := weightedRatioCarrier_norm_bound M hA hOverlap j r hjr G (preHist r w)
  rw [restrictPreHist_preHist] at hc
  calc
    _ ≤ (‖G (preHist j w)‖ * max 1 (policyFactor zeta) ^ r.val) * C :=
      mul_le_mul hc (hC (currentState w r, actionAt w r)) (norm_nonneg _)
        (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _))
    _ = D * |G (preHist j w)| := by dsimp [D]; ring

/-- Iteration of weighted target-policy peeling. -/
lemma weightedRatioCarrier_iteration {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hOverlap : PolicyOverlap zeta M)
    (j : Fin T) (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hGi : Integrable (fun w => G (preHist j w)) M.law)
    (n : Nat) (hjn : j.val ≤ n) (hnT : n < T)
    (F : JointState nX nH → ℝ) :
    ∫ w, weightedRatioCarrier M j ⟨n, hnT⟩ hjn G (preHist ⟨n, hnT⟩ w) *
        F (currentState w ⟨n, hnT⟩) ∂M.law =
      ∫ w, G (preHist j w) *
        ((targetStep M)^[n - j.val] F) (currentState w j) ∂M.law := by
  induction n, hjn using Nat.le_induction generalizing F with
  | base =>
      have he : (⟨j.val, hnT⟩ : Fin T) = j := Fin.ext rfl
      cases he
      simp [weightedRatioCarrier_self]
  | succ n hjn ih =>
      have hnT' : n < T := lt_trans (Nat.lt_succ_self n) hnT
      have hjoint := weightedRatioCarrier_kernel_integrable M hA hOverlap j
        ⟨n, hnT'⟩ hjn G hGm hGi F
      have haction := weightedRatioCarrier_action_integrable M hK hA hOverlap j
        ⟨n, hnT'⟩ hjn G hGm hGi F
      calc
        _ = ∫ w, weightedRatioCarrier M j ⟨n, hnT'⟩ hjn G
              (preHist ⟨n, hnT'⟩ w) *
              targetStep M F (currentState w ⟨n, hnT'⟩) ∂M.law :=
          weightedRatioCarrier_peeling M hK hA hOverlap j ⟨n, hnT'⟩ hjn hnT
            G hGm F hjoint haction
        _ = ∫ w, G (preHist j w) *
              ((targetStep M)^[n - j.val] (targetStep M F))
                (currentState w j) ∂M.law := ih hnT' (targetStep M F)
        _ = _ := by
          have hd : n + 1 - j.val = (n - j.val) + 1 := by omega
          have hc : ((targetStep M)^[n - j.val] (targetStep M F)) =
              targetStep M ((targetStep M)^[n - j.val] F) :=
            (Function.iterate_succ_apply (targetStep M) (n - j.val) F).symm.trans
              (Function.iterate_succ_apply' (targetStep M) (n - j.val) F)
          rw [hd, Function.iterate_succ_apply', hc]

/-- Terminal reward peeling for a weighted target-ratio carrier. -/
lemma weightedRatioCarrier_terminal_peeling {T nX nH k : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (j t : Fin T) (hjt : j.val ≤ t.val)
    (G : PreHistory T nX nH k j → ℝ) (hGm : Measurable G)
    (hjoint : Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) =>
        weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))))
    (haction : Integrable
      (fun z : PreHistory T nX nH k t × Fin k =>
        weightedRatioCarrier M j t hjt G z.1 *
          ∫ y, y.1 ∂M.K z.1.2.2 z.2)
      (M.law.map (fun w => (preHist t w, actionAt w t)))) :
    ∫ w, G (preHist j w) * windowScore M j t w ∂M.law =
      ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
        rewardRegression M (currentState w t) ∂M.law := by
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hpre : Measurable (preHist t : FullPath T nX nH k → _) := by
    unfold preHist currentState pastIndex
    fun_prop
  calc
    _ = ∫ w, weightedRatioCarrier M j t hjt G (preHist t w) *
          ratio M.b M.e (currentState w t).1 (actionAt w t) * rewardAt w t ∂M.law := by
      apply integral_congr_ae
      filter_upwards with w
      unfold windowScore
      rw [weightedRatioCarrier_preHist]
      have hp : (∏ q : Fin t.val, if j.val ≤ q.val then
          ratio M.b M.e (currentState w (pastIndex t q)).1
            (actionAt w (pastIndex t q)) else 1) =
          ∏ q ∈ Finset.univ.filter
            (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val),
            ratio M.b M.e (currentState w q).1 (actionAt w q) := by
        rw [← Finset.prod_filter]
        apply Finset.prod_bij (fun q _ =>
          (⟨q.val, lt_trans q.isLt t.isLt⟩ : Fin T))
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
          exact ⟨hq, q.isLt⟩
        · intro q _ q' _ he
          apply Fin.ext
          simpa using congrArg Fin.val he
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
          exact ⟨⟨q.val, hq.2⟩, by simpa using hq.1, Fin.ext rfl⟩
        · intro q _
          rfl
      rw [hp]
      have hsets : insert t (Finset.univ.filter
          (fun q : Fin T => j.val ≤ q.val ∧ q.val < t.val)) =
          Finset.univ.filter (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val) := by
        ext q
        simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro (rfl | h)
          · exact ⟨hjt, le_rfl⟩
          · exact ⟨h.1, Nat.le_of_lt h.2⟩
        · intro h
          by_cases hqt : q = t
          · exact Or.inl hqt
          · exact Or.inr ⟨h.1, lt_of_le_of_ne h.2 (fun hv => hqt (Fin.ext hv))⟩
      rw [← hsets, Finset.prod_insert (by simp)]
      ring
    _ = ∫ z, weightedRatioCarrier M j t hjt G z.1.1 *
          ratio M.b M.e z.1.1.2.2.1 z.1.2 * z.2.1
          ∂(M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
      rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
      rfl
    _ = ∫ h, ∫ y, weightedRatioCarrier M j t hjt G h.1 *
          ratio M.b M.e h.1.2.2.1 h.2 * y.1 ∂M.K h.1.2.2 h.2
          ∂(M.law.map (postHist t)) :=
      full_history_integral_kernel_step M hK t _ hjoint
    _ = ∫ z, ratio M.b M.e z.1.2.2.1 z.2 *
          (weightedRatioCarrier M j t hjt G z.1 *
            ∫ y, y.1 ∂M.K z.1.2.2 z.2)
          ∂(M.law.map (fun w => (preHist t w, actionAt w t))) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Fin k, M.e h.2.2.1 a *
          (weightedRatioCarrier M j t hjt G h *
            ∫ y, y.1 ∂M.K h.2.2 a) ∂(M.law.map (preHist t)) :=
      full_history_integral_ratio_step M hA hOverlap t _ haction
    _ = ∫ h, weightedRatioCarrier M j t hjt G h *
          rewardRegression M h.2.2 ∂(M.law.map (preHist t)) := by
      apply integral_congr_ae
      filter_upwards with h
      unfold rewardRegression
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = _ := by
      rw [integral_map hpre.aemeasurable]
      · rfl
      · exact ((weightedRatioCarrier_measurable M j t hjt G hGm).mul
          ((measurable_of_finite (rewardRegression M)).comp (by fun_prop))).aestronglyMeasurable

end CausalSmith.Stat.PomdpStateauditMinimax
