module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwBias

/-! # Reward and PHIW score moment bounds. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

/-- The unconditional reward at every epoch inherits the conditional second-moment bound. -/
lemma reward_sq_integrable_and_integral_le_one {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hY : RewardMomentEnvelope M) (t : Fin T) :
    Integrable (fun w : FullPath T nX nH k => rewardAt w t ^ 2) M.law ∧
      ∫ w, rewardAt w t ^ 2 ∂M.law ≤ 1 := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa => hK.1 sa.1 sa.2⟩
  have henc : Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
    unfold postHist preHist currentState pastIndex actionAt rewardAt nextState
    fun_prop
  have hm : Measurable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) => z.2.1 ^ 2) := by
    fun_prop
  have hjoint : Integrable
      (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) => z.2.1 ^ 2)
      (M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
    rw [hK.2 t]
    let κ := Kernel.comap (kernelOfK M)
      (fun h : PostHistory T nX nH k t => (h.1.2.2, h.2)) (by fun_prop)
    rw [Measure.integrable_compProd_iff hm.aestronglyMeasurable]
    constructor
    · filter_upwards with h
      exact (hY h.1.2.2 h.2).2.1
    · have hout : StronglyMeasurable (fun h : PostHistory T nX nH k t =>
          ∫ y, ‖y.1 ^ 2‖ ∂κ h) :=
        hm.norm.stronglyMeasurable.integral_kernel_prod_right'
      apply Integrable.of_bound hout.aestronglyMeasurable 1
      filter_upwards with h
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      change (∫ y, ‖y.1 ^ 2‖ ∂M.K h.1.2.2 h.2) ≤ 1
      have heq : (∫ y, ‖y.1 ^ 2‖ ∂M.K h.1.2.2 h.2) =
          ∫ y, y.1 ^ 2 ∂M.K h.1.2.2 h.2 := by
        apply integral_congr_ae
        filter_upwards with y
        rw [Real.norm_of_nonneg (sq_nonneg _)]
      rw [heq]
      exact (hY h.1.2.2 h.2).2.2.2
  have hpath : Integrable (fun w : FullPath T nX nH k => rewardAt w t ^ 2) M.law := by
    simpa [Function.comp_def] using hjoint.comp_measurable henc
  refine ⟨hpath, ?_⟩
  have hfull := full_history_integral_kernel_step M hK t
    (fun z : PostHistory T nX nH k t × (ℝ × JointState nX nH) => z.2.1 ^ 2) hjoint
  have hmap : ∫ w, rewardAt w t ^ 2 ∂M.law =
      ∫ z, z.2.1 ^ 2
        ∂(M.law.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))) := by
    rw [integral_map henc.aemeasurable hjoint.aestronglyMeasurable]
  rw [hmap, hfull]
  have hpost : Measurable (postHist t : FullPath T nX nH k → _) := by
    unfold postHist preHist currentState pastIndex actionAt
    fun_prop
  letI : IsProbabilityMeasure (M.law.map (postHist t)) :=
    Measure.isProbabilityMeasure_map hpost.aemeasurable
  have hinter : Integrable
      (fun h : PostHistory T nX nH k t => ∫ y, y.1 ^ 2 ∂M.K h.1.2.2 h.2)
      (M.law.map (postHist t)) := by
    refine Integrable.of_bound
      ((measurable_of_countable fun sa : JointState nX nH × Fin k =>
        ∫ y, y.1 ^ 2 ∂M.K sa.1 sa.2).comp
          ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk
            measurable_snd) |>.aestronglyMeasurable) 1 ?_
    filter_upwards with h
    change |∫ y, y.1 ^ 2 ∂M.K h.1.2.2 h.2| ≤ 1
    rw [abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
    exact (hY h.1.2.2 h.2).2.2.2
  change (∫ h, ∫ y, y.1 ^ 2 ∂M.K h.1.2.2 h.2
    ∂M.law.map (postHist t)) ≤ 1
  calc
    (∫ h, ∫ y, y.1 ^ 2 ∂M.K h.1.2.2 h.2 ∂M.law.map (postHist t)) ≤
        ∫ _h, (1 : ℝ) ∂M.law.map (postHist t) := by
      apply integral_mono hinter (integrable_const 1)
      intro h
      exact (hY h.1.2.2 h.2).2.2.2
    _ = 1 := by simp

/-- A mature PHIW summand is bounded by the likelihood-ratio envelope times
the terminal reward. -/
lemma abs_observed_phiwScore_le {T nX nH k depth : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hA : FullFiltrationRandomization M)
    (hOverlap : PolicyOverlap zeta M)
    (t : Fin T) (hdepth : depth ≤ t.val) (w : FullPath T nX nH k) :
    |phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t| ≤
      policyFactor zeta ^ (depth + 1) * |rewardAt w t| := by
  rw [phiwScore_observedRecord_eq_windowScore M t hdepth w]
  unfold windowScore
  rw [abs_mul]
  let j : Fin T := ⟨t.val - depth, by omega⟩
  let I := Finset.univ.filter
    (fun q : Fin T => j.val ≤ q.val ∧ q.val ≤ t.val)
  have hI : I = Finset.Icc j t := by
    ext q
    simp [I]
  have hcard : I.card = depth + 1 := by
    rw [hI, Fin.card_Icc]
    dsimp [j]
    omega
  have hprod0 : 0 ≤ ∏ q ∈ I,
      ratio M.b M.e (currentState w q).1 (actionAt w q) :=
    Finset.prod_nonneg fun q _ => (policy_ratio_bounds M hOverlap hA.1 _ _).1
  have hprod : (∏ q ∈ I,
      ratio M.b M.e (currentState w q).1 (actionAt w q)) ≤
      policyFactor zeta ^ (depth + 1) := by
    calc
      (∏ q ∈ I, ratio M.b M.e (currentState w q).1 (actionAt w q)) ≤
          ∏ _q ∈ I, policyFactor zeta := by
        apply Finset.prod_le_prod
        · intro q _
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).1
        · intro q _
          exact (policy_ratio_bounds M hOverlap hA.1 _ _).2
      _ = _ := by simp [hcard]
  change |rewardAt w t| * |∏ q ∈ I,
    ratio M.b M.e (currentState w q).1 (actionAt w q)| ≤ _
  rw [abs_of_nonneg hprod0]
  nlinarith [abs_nonneg (rewardAt w t)]

/-- A pointwise likelihood envelope gives a coarse diagonal second-moment
bound.  This suffices for square integrability; the rate-sharp variance bound
must additionally exploit behavior-policy normalization of squared ratios. -/
lemma observed_phiwScore_sq_integrable_and_le {T nX nH k depth : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (t : Fin T) (hdepth : depth ≤ t.val) :
    let X := fun w : FullPath T nX nH k =>
      phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t
    Integrable (fun w => X w ^ 2) M.law ∧
      ∫ w, X w ^ 2 ∂M.law ≤ policyFactor zeta ^ (2 * (depth + 1)) := by
  dsimp only
  let X := fun w : FullPath T nX nH k =>
    phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t
  have hreward := reward_sq_integrable_and_integral_le_one M hK hY t
  have hcoef : 0 ≤ policyFactor zeta ^ (depth + 1) :=
    pow_nonneg (Real.exp_nonneg _) _
  have hsq (w : FullPath T nX nH k) : X w ^ 2 ≤
      policyFactor zeta ^ (2 * (depth + 1)) * rewardAt w t ^ 2 := by
    have habs := abs_observed_phiwScore_le M hA hOverlap t hdepth w
    have hmul : 0 ≤
        (policyFactor zeta ^ (depth + 1) * |rewardAt w t| - |X w|) *
        (policyFactor zeta ^ (depth + 1) * |rewardAt w t| + |X w|) :=
      mul_nonneg (sub_nonneg.mpr habs)
        (add_nonneg (mul_nonneg hcoef (abs_nonneg _)) (abs_nonneg _))
    rw [show X w ^ 2 = |X w| ^ 2 by rw [sq_abs]]
    have hp : (policyFactor zeta ^ (depth + 1) * |rewardAt w t|) ^ 2 =
        policyFactor zeta ^ (2 * (depth + 1)) * rewardAt w t ^ 2 := by
      rw [mul_pow, sq_abs, ← pow_mul]
      congr 2
      omega
    rw [← hp]
    nlinarith
  have hmeas : Measurable (fun w : FullPath T nX nH k => X w ^ 2) := by
    dsimp [X]
    unfold phiwScore observedRecord obsProj currentState actionAt rewardAt
    fun_prop
  have hsqi : Integrable (fun w : FullPath T nX nH k => X w ^ 2) M.law := by
    apply (hreward.1.const_mul (policyFactor zeta ^ (2 * (depth + 1)))).mono'
      hmeas.aestronglyMeasurable
    filter_upwards with w
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hsq w
  refine ⟨hsqi, ?_⟩
  calc
    (∫ w, X w ^ 2 ∂M.law) ≤
        ∫ w, policyFactor zeta ^ (2 * (depth + 1)) * rewardAt w t ^ 2 ∂M.law := by
      exact integral_mono hsqi
        (hreward.1.const_mul (policyFactor zeta ^ (2 * (depth + 1)))) hsq
    _ = policyFactor zeta ^ (2 * (depth + 1)) *
        ∫ w, rewardAt w t ^ 2 ∂M.law := by rw [integral_const_mul]
    _ ≤ policyFactor zeta ^ (2 * (depth + 1)) * 1 := by
      exact mul_le_mul_of_nonneg_left hreward.2
        (pow_nonneg (Real.exp_nonneg _) _)
    _ = _ := mul_one _

/-- Every mature PHIW summand is square integrable under the full path law. -/
lemma observed_phiwScore_memLp_two {T nX nH k depth : Nat} {zeta : ℝ}
    (M : PomdpModel T nX nH k) (hK : FullFiltrationPomdp M)
    (hA : FullFiltrationRandomization M) (hY : RewardMomentEnvelope M)
    (hOverlap : PolicyOverlap zeta M) (t : Fin T) (hdepth : depth ≤ t.val) :
    MemLp (fun w : FullPath T nX nH k =>
      phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t) 2 M.law := by
  let X := fun w : FullPath T nX nH k =>
    phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t
  have hmeas : Measurable X := by
    dsimp [X]
    unfold phiwScore observedRecord obsProj currentState actionAt rewardAt
    fun_prop
  rw [memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable]
  exact (observed_phiwScore_sq_integrable_and_le M hK hA hY hOverlap t hdepth).1

/-- The unclipped PHIW average pulled back to the complete path. -/
noncomputable def fullPathPhiwRaw {T nX nH k : Nat} (depth : Nat)
    (M : PomdpModel T nX nH k) (w : FullPath T nX nH k) : ℝ :=
  (((T - depth : Nat) : ℝ)⁻¹) *
    ∑ t ∈ Finset.univ.filter (fun t : Fin T => depth ≤ t.val),
      phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t

/-- The unclipped finite-window average has geometric bias. -/
lemma fullPathPhiwRaw_bias_le {T nX nH k depth : Nat} {t0 zeta : ℝ}
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (hT : 1 ≤ T) (hdepth : depth ≤ T / 2) :
    |∫ w, fullPathPhiwRaw depth M w ∂M.law - targetValue M| ≤
      2 * mixingAlpha t0 ^ depth := by
  let F := (targetStep M)^[depth] (rewardRegression M)
  let I : Finset (Fin T) := Finset.univ.filter (fun t => depth ≤ t.val)
  have hdT : depth < T := by omega
  have hI : I = Finset.Ici (⟨depth, hdT⟩ : Fin T) := by
    ext t
    simp only [I, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
    change depth ≤ t.val ↔ depth ≤ t.val
    rfl
  have hIcard : I.card = T - depth := by rw [hI, Fin.card_Ici]
  have hNpos : 0 < T - depth := by omega
  have hmean : ∫ w, fullPathPhiwRaw depth M w ∂M.law =
      ∑ s, stationaryLaw (policyKernel M M.b) s * F s := by
    unfold fullPathPhiwRaw
    rw [integral_const_mul, integral_finset_sum]
    · rw [show (∑ t ∈ I, ∫ w,
          phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t ∂M.law) =
          ∑ _t ∈ I, ∑ s, stationaryLaw (policyKernel M M.b) s * F s by
        apply Finset.sum_congr rfl
        intro t ht
        have hdt : depth ≤ t.val := (Finset.mem_filter.mp ht).2
        have heq : (fun w : FullPath T nX nH k =>
            phiwScore depth M.b M.e (observedRecord (nH := nH) (obsProj w)) t) =
            fun w => windowScore M ⟨t.val - depth, by omega⟩ t w := by
          funext w
          exact phiwScore_observedRecord_eq_windowScore M t hdt w
        rw [heq]
        rw [integral_windowScore_eq_stationary_targetIter M hM.pomdp hM.randomization
          hM.moment hM.overlap hM.start _ _ (by dsimp; omega)]
        rw [Nat.sub_sub_self hdt]]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [hIcard]
      have hcast : ((T - depth : Nat) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hNpos)
      rw [← mul_assoc, inv_mul_cancel₀ hcast, one_mul]
    · intro t ht
      exact (observed_phiwScore_memLp_two M hM.pomdp hM.randomization hM.moment
        hM.overlap t (Finset.mem_filter.mp ht).2).integrable one_le_two
  rw [hmean]
  exact stationary_targetIter_bias_le M hM hnX hnH

end CausalSmith.Stat.PomdpStateauditMinimax
