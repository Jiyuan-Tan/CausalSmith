module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.PhiwVariance

/-! # Sharp depth-zero variance for the immediate IW estimator. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

lemma phiwScore_zero_eq_immediate {T nX nH k : Nat}
    (b e : Policy nX k) (w : AuditedRecord T nX nH k) (t : Fin T) :
    phiwScore 0 b e w t = (w t).2.2.1 * ratio b e (w t).1 (w t).2.1 := by
  unfold phiwScore
  have hf : Finset.univ.filter
      (fun j : Fin T => j.val ≤ t.val ∧ t.val - j.val ≤ 0) = {t} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hj
      apply Fin.ext
      omega
    · intro hj
      subst j
      omega
  rw [hf]
  simp

lemma fullPathPhiwRaw_zero_mean_eq_target
    {T nX nH k : Nat} {t0 zeta : ℝ} (hT : 1 ≤ T)
    (M : PomdpModel T nX nH k) (hM : InvarianceClass t0 zeta M) :
    ∫ w, fullPathPhiwRaw 0 M w ∂M.law = targetValue M := by
  have hsum : ∀ t : Fin T,
      ∫ w, phiwScore 0 M.b M.e
          (observedRecord (nH := nH) (obsProj w)) t ∂M.law =
        ∑ s, stationaryLaw (policyKernel M M.b) s * rewardRegression M s := by
    intro t
    have heq : (fun w : FullPath T nX nH k =>
        phiwScore 0 M.b M.e (observedRecord (nH := nH) (obsProj w)) t) =
        fun w => windowScore M t t w := by
      funext w
      have hh := phiwScore_observedRecord_eq_windowScore (depth := 0) M t (by omega) w
      have hi : (⟨t.val - 0, (show t.val - 0 < T by simpa using t.isLt)⟩ : Fin T) = t :=
        Fin.ext (by simp)
      rw [hi] at hh
      exact hh
    rw [heq, integral_windowScore_eq_stationary_targetIter M hM.1.pomdp
      hM.1.randomization hM.1.moment hM.1.overlap hM.1.start t t (by omega)]
    simp
  unfold fullPathPhiwRaw
  simp only [Nat.sub_zero, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
  rw [integral_const_mul, integral_finset_sum]
  · simp_rw [hsum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hTr : (T : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < T))
    rw [← mul_assoc, inv_mul_cancel₀ hTr, one_mul]
    unfold targetValue
    rw [hM.2]
  · intro t _
    exact (observed_phiwScore_memLp_two M hM.1.pomdp hM.1.randomization
      hM.1.moment hM.1.overlap t (by omega)).integrable one_le_two

lemma variance_fullPathPhiwRaw_zero_le
    {T nX nH k : Nat} {t0 zeta : ℝ} (hT : 1 ≤ T)
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) :
    variance (fullPathPhiwRaw 0 M) M.law ≤
      (policyFactor zeta + 4 / (1 - mixingAlpha t0)) / (T : ℝ) := by
  let L := policyFactor zeta
  let a := mixingAlpha t0
  let S : Fin T → FullPath T nX nH k → ℝ := fun t w => windowScore M t t w
  have hL0 : 0 ≤ L := by dsimp [L, policyFactor]; positivity
  have ha0 : 0 ≤ a := by dsimp [a, mixingAlpha]; positivity
  have ha1 : a < 1 := by
    dsimp [a, mixingAlpha]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hM.t0_pos)
  have hSmem (t : Fin T) : MemLp (S t) 2 M.law := by
    have hh := observed_phiwScore_memLp_two (depth := 0) M hM.pomdp hM.randomization
      hM.moment hM.overlap t (by omega : 0 ≤ t.val)
    apply (memLp_congr_ae ?_).2 hh
    filter_upwards with w
    have he := phiwScore_observedRecord_eq_windowScore (depth := 0) M t (by omega) w
    have hi : (⟨t.val - 0, (show t.val - 0 < T by simpa using t.isLt)⟩ : Fin T) = t :=
      Fin.ext (by simp)
    rw [hi] at he
    exact he.symm
  have hfuture (t : Fin T) :
      ∑ u ∈ Finset.univ.filter (fun u : Fin T => t < u),
        |covariance (S t) (S u) M.law| ≤ 2 / (1 - a) := by
    calc
      _ ≤ ∑ u ∈ Finset.univ.filter (fun u : Fin T => t < u),
          2 * a ^ (u.val - t.val - 1) := by
        apply Finset.sum_le_sum
        intro u hu
        have htu : t < u := (Finset.mem_filter.mp hu).2
        have hh := abs_covariance_windowScore_le_disjoint_one M hM hnX hnH t u
          (depth := 0) (lag := u.val - t.val) (by omega) (by omega) (by omega)
        simpa [S, a, mul_comm] using hh
      _ = 2 * ∑ u ∈ Finset.univ.filter (fun u : Fin T => t < u),
          a ^ (u.val - t.val - 1) := by rw [Finset.mul_sum]
      _ ≤ 2 * ∑ j ∈ Finset.range T, a ^ j := by
        gcongr
        apply sum_pow_image_le_range
          (Finset.univ.filter (fun u : Fin T => t < u))
          (fun u => u.val - t.val - 1) T a ha0
        · intro u hu; omega
        · intro u hu v hv huv
          apply Fin.ext
          have hu' := (Finset.mem_filter.mp hu).2
          have hv' := (Finset.mem_filter.mp hv).2
          simp only at huv
          omega
      _ ≤ 2 * (1 / (1 - a)) := by gcongr; exact geom_partial_le_inv ha0 ha1 T
      _ = _ := by ring
  have hsumVar : variance (fun w => ∑ t : Fin T, S t w) M.law ≤
      (T : ℝ) * (L + 4 / (1 - a)) := by
    rw [variance_fun_sum']
    · calc
        _ ≤ ∑ t, ∑ u, |covariance (S t) (S u) M.law| := by
          gcongr with t u
          exact le_abs_self _
        _ = ∑ t, |covariance (S t) (S t) M.law| +
            2 * ∑ t, ∑ u ∈ Finset.univ.filter (fun u => t < u),
              |covariance (S t) (S u) M.law| := by
          apply sum_abs_symmetric_eq_diag_add_two_upper
          intro t u
          rw [covariance_comm]
        _ ≤ ∑ _t : Fin T, L + 2 * ∑ _t : Fin T, (2 / (1 - a)) := by
          gcongr with t
          · have hsquare := integral_windowScore_sq_le M hM.pomdp hM.randomization
              hM.moment hM.overlap hM.start t t (by omega)
            have hm := hSmem t
            rw [covariance_self hm.1.aemeasurable,
              abs_of_nonneg (variance_nonneg _ _), variance_eq_sub hm]
            exact (sub_le_self _ (sq_nonneg _)).trans (by simpa [S, L] using hsquare)
          · exact hfuture t
        _ = (T : ℝ) * (L + 4 / (1 - a)) := by simp; ring
    · exact fun t _ => hSmem t
  have hraw : fullPathPhiwRaw 0 M = fun w => (T : ℝ)⁻¹ * ∑ t, S t w := by
    funext w
    unfold fullPathPhiwRaw
    simp only [Nat.sub_zero, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    have he := phiwScore_observedRecord_eq_windowScore (depth := 0) M t (by omega) w
    have hi : (⟨t.val - 0, (show t.val - 0 < T by simpa using t.isLt)⟩ : Fin T) = t :=
      Fin.ext (by simp)
    rw [hi] at he
    simpa [S] using he
  rw [hraw, variance_const_mul]
  have hTr : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  calc
    (T : ℝ)⁻¹ ^ 2 * variance (fun w => ∑ t, S t w) M.law ≤
        (T : ℝ)⁻¹ ^ 2 * ((T : ℝ) * (L + 4 / (1 - a))) := by gcongr
    _ = (L + 4 / (1 - a)) / (T : ℝ) := by field_simp
    _ = _ := rfl

noncomputable def observedIwEstimator {T nX nH k : Nat}
    (b e : Policy nX k) (w : ObsPath T nX k) : ℝ :=
  iwEstimator b e (observedRecord (nH := nH) w)

lemma measurable_observedIwEstimator {T nX nH k : Nat} (b e : Policy nX k) :
    Measurable (observedIwEstimator (T := T) (nH := nH) b e) := by
  have hr (t : Fin T) : Measurable (fun w : ObsPath T nX k =>
      ratio b e (w t).1 (w t).2.1) := by
    exact (measurable_of_finite (fun xa : Fin nX × Fin k =>
      ratio b e xa.1 xa.2)).comp
        ((measurable_pi_apply t).fst.prodMk (measurable_pi_apply t).snd.fst)
  unfold observedIwEstimator iwEstimator observedRecord clipUnit
  fun_prop (disch := assumption)

lemma iwEstimator_eq_observedProjection {T nX nH k : Nat}
    (b e : Policy nX k) (w : AuditedRecord T nX nH k) :
    iwEstimator b e w =
      observedIwEstimator (nH := nH) b e (auditedProjection w) := by
  unfold observedIwEstimator iwEstimator observedRecord auditedProjection
  rfl

lemma sqRisk_audited_iw_eq_fullPath {T nX nH k : Nat}
    (M : PomdpModel T nX nH k) (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1)
    (theta : ℝ) :
    Causalean.Stat.sqRisk (auditedLaw eta M) (iwEstimator M.b M.e) theta =
      Causalean.Stat.sqRisk M.law
        (fun w => clipUnit (fullPathPhiwRaw 0 M w)) theta := by
  have hproj : Measurable (auditedProjection (T := T) (nX := nX)
      (nH := nH) (k := k)) := by unfold auditedProjection; fun_prop
  have haud := Causalean.Stat.sqRisk_map_affinePullback
    (law := auditedLaw eta M) (phi := auditedProjection)
    (a := (1 : ℝ)) (b := 0) (theta := theta)
    (targetEst := observedIwEstimator (nH := nH) M.b M.e)
    one_ne_zero hproj (measurable_observedIwEstimator M.b M.e)
  have hobs : Measurable (obsProj : FullPath T nX nH k → ObsPath T nX k) := by
    unfold obsProj currentState actionAt rewardAt; fun_prop
  have hfull := Causalean.Stat.sqRisk_map_affinePullback
    (law := M.law) (phi := obsProj) (a := (1 : ℝ)) (b := 0) (theta := theta)
    (targetEst := observedIwEstimator (nH := nH) M.b M.e)
    one_ne_zero hobs (measurable_observedIwEstimator M.b M.e)
  simp only [one_pow, one_mul, add_zero] at haud hfull
  rw [auditedLaw_projection M eta heta] at haud
  have hpaud : Causalean.Stat.affinePullbackEstimator
      (auditedProjection (T := T) (nX := nX) (nH := nH) (k := k)) 1 0
      (observedIwEstimator (T := T) (nH := nH) M.b M.e) = iwEstimator M.b M.e := by
    funext w
    unfold Causalean.Stat.affinePullbackEstimator observedIwEstimator iwEstimator
      observedRecord auditedProjection
    ring
  have hpfull : Causalean.Stat.affinePullbackEstimator
      (obsProj : FullPath T nX nH k → ObsPath T nX k) 1 0
      (observedIwEstimator (T := T) (nH := nH) M.b M.e) =
        fun w => clipUnit (fullPathPhiwRaw 0 M w) := by
    funext w
    unfold Causalean.Stat.affinePullbackEstimator observedIwEstimator iwEstimator
      observedRecord fullPathPhiwRaw obsProj currentState actionAt rewardAt
    simp only [Nat.sub_zero, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _),
      sub_zero, div_one]
    congr 1
    apply congrArg
    apply Finset.sum_congr rfl
    intro t _
    change ((observedRecord (nH := nH) (obsProj w)) t).2.2.1 *
        ratio M.b M.e ((observedRecord (nH := nH) (obsProj w)) t).1
          ((observedRecord (nH := nH) (obsProj w)) t).2.1 =
      phiwScore 0 M.b M.e (observedRecord (nH := nH) (obsProj w)) t
    exact (phiwScore_zero_eq_immediate M.b M.e
      (observedRecord (nH := nH) (obsProj w)) t).symm
  rw [hpaud] at haud
  rw [hpfull] at hfull
  exact haud.trans hfull.symm

lemma audited_iw_invariance_risk_le
    {T nX nH k : Nat} {t0 zeta : ℝ} (hT : 1 ≤ T)
    (M : PomdpModel T nX nH k) (hM : InvarianceClass t0 zeta M)
    (hnX : 1 ≤ nX) (hnH : 1 ≤ nH) (eta : ℝ)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.sqRisk (auditedLaw eta M) (iwEstimator M.b M.e)
        (targetValue M) ≤
      (policyFactor zeta + 4 / (1 - mixingAlpha t0)) / (T : ℝ) := by
  rw [sqRisk_audited_iw_eq_fullPath M eta heta]
  have hrawMeas : Measurable (fullPathPhiwRaw 0 M) := by
    unfold fullPathPhiwRaw phiwScore observedRecord obsProj currentState actionAt rewardAt
    fun_prop
  have hrawLp : MemLp (fullPathPhiwRaw 0 M) 2 M.law := by
    unfold fullPathPhiwRaw
    apply MemLp.const_mul
    apply memLp_finsetSum
    intro t ht
    exact observed_phiwScore_memLp_two M hM.1.pomdp hM.1.randomization hM.1.moment
      hM.1.overlap t (Finset.mem_filter.mp ht).2
  have hrisk := sqRisk_clipUnit_le_variance_add_bias_sq M.law hrawMeas hrawLp
    (targetValue_mem_unit_hw hM.1)
  rw [fullPathPhiwRaw_zero_mean_eq_target hT M hM, sub_self, zero_pow (by norm_num)] at hrisk
  exact hrisk.trans (by simpa using variance_fullPathPhiwRaw_zero_le hT M hM.1 hnX hnH)

noncomputable def iwAuditedEstimator (T : Nat) : AuditedEstimator T :=
  ⟨fun nX nH k b e => iwEstimator (nH := nH) b e, by
    constructor
    · intro nX nH k b e
      have hp : Measurable (auditedProjection (T := T) (nX := nX)
          (nH := nH) (k := k)) := by unfold auditedProjection; fun_prop
      have hm := (measurable_observedIwEstimator (T := T) (nH := nH) b e).comp hp
      have heq : iwEstimator (T := T) (nH := nH) b e =
          (observedIwEstimator (T := T) (nH := nH) b e) ∘ auditedProjection := by
        funext w
        exact iwEstimator_eq_observedProjection b e w
      change Measurable (iwEstimator (T := T) (nH := nH) b e)
      rw [heq]
      exact hm
    · intro nX nH k b e w
      unfold iwEstimator clipUnit
      constructor
      · exact le_max_left _ _
      · apply max_le (by norm_num)
        exact min_le_left _ _⟩


end CausalSmith.Stat.PomdpStateauditMinimax
