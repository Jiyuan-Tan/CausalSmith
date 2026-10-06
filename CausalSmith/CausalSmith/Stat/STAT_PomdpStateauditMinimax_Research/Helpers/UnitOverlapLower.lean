module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.UnitOverlapVariance
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.MinimaxMonotonicity
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.SignedDepth
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.TwoPoint

/-! # The singleton-state parametric pair for the audited invariance lower bound. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

noncomputable def parametricStateModel (T : Nat) (v : Bool) : PomdpModel T 1 1 2 :=
  embedBinary (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPairFinite T v))

lemma parametricStateModel_invariance {T : Nat} {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (v : Bool) :
    InvarianceClass t0 zeta (parametricStateModel T v) := by
  let F := CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPairFinite T v
  let R := CausalSmith.Stat.PomdpLatentOverlapMinimax.embed F
  have hbase := CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_mem
    T t0 zeta 1 v ht0 hzeta le_rfl
  have hK : FullFiltrationPomdp (embedBinary R) :=
    embedBinary_fullFiltrationPomdp R
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_pomdpKernelLaw F)
  have hA : FullFiltrationRandomization (embedBinary R) :=
    embedBinary_fullFiltrationRandomization R
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_sequentialIgnorability F)
  have hY : RewardMomentEnvelope (embedBinary R) := by
    apply rewardMomentEnvelope_of_ae_bound
    · exact hK.1
    · intro s a
      exact finiteReward_kernel_ae_bound F s a
  have hpol : PolicyOverlap zeta (embedBinary R) :=
    embedBinary_policyOverlap R hbase.policy_overlap
  have hcon : UniformContraction t0 (embedBinary R) :=
    embedBinary_uniformContraction R hbase.uniform_contraction
  have hstart : StationaryStart (embedBinary R) :=
    embedBinary_stationaryStart R hbase.stationary_start
  have hhw : HuWagerClass t0 zeta (embedBinary R) :=
    ⟨ht0, hzeta, hK, hA, hY, hpol, hcon, hstart⟩
  refine ⟨by simpa [parametricStateModel, F, R] using hhw, ?_⟩
  change stationaryLaw (policyKernel (embedBinary R) (embedBinary R).e) =
    stationaryLaw (policyKernel (embedBinary R) (embedBinary R).b)
  have hbe : (embedBinary R).b = (embedBinary R).e := by
    rfl
  rw [hbe]

lemma parametricStateModel_targetValue {T : Nat} {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (v : Bool) :
    targetValue (parametricStateModel T v) =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.signedValue v *
        CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T := by
  rw [parametricStateModel, embedBinary_targetValue]
  exact CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_targetValue
    ht0 hzeta le_rfl v

lemma parametricStateModel_obsLaw {T : Nat} (v : Bool) :
    obsLaw (parametricStateModel T v) =
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed
          (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPairFinite T v))).map
        (fun w t => ((w t).1, boolActionFin (w t).2.1, (w t).2.2)) := by
  unfold obsLaw parametricStateModel embedBinary
    CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
  rw [Measure.map_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
    (by fun_prop)]
  rw [Measure.map_map (by fun_prop)
    CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj]
  congr 1

lemma parametricStateModel_observed_klDiv_le (T : Nat) (hT : 1 ≤ T) :
    InformationTheory.klDiv (obsLaw (parametricStateModel T false))
        (obsLaw (parametricStateModel T true)) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let P := CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPairFinite T false))
  let Q := CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPairFinite T true))
  letI : IsProbabilityMeasure P := by
    unfold P CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
    exact Measure.isProbabilityMeasure_map
      CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
  letI : IsProbabilityMeasure Q := by
    unfold Q CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
    exact Measure.isProbabilityMeasure_map
      CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
  rw [parametricStateModel_obsLaw, parametricStateModel_obsLaw]
  exact (InformationTheory.klDiv_map_le _ _ (by fun_prop)).trans
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricPair_observed_klDiv_le T hT)

/-- With singleton hidden and observed state spaces, forgetting the next state is an equivalence. -/
noncomputable def singletonPathObsEquiv (T : Nat) :
    FullPath T 1 1 2 ≃ᵐ ObsPath T 1 2 where
  toFun := obsProj
  invFun := fun w =>
    (fun _ => (0, 0), fun t => ((w t).2.1, (w t).2.2))
  left_inv w := by
    ext t <;> simp [obsProj, currentState, actionAt, rewardAt] <;> apply Subsingleton.elim
  right_inv w := by
    ext t <;> simp [obsProj, currentState, actionAt, rewardAt]
  measurable_toFun := by
    have h : Measurable (obsProj : FullPath T 1 1 2 → ObsPath T 1 2) := by
      unfold obsProj currentState actionAt rewardAt
      fun_prop
    exact h
  measurable_invFun := by
    apply Measurable.prodMk
    · exact measurable_const
    · apply measurable_pi_lambda
      intro t
      apply Measurable.prodMk <;> fun_prop

lemma singleton_law_klDiv_eq_obsLaw {T : Nat} (M0 M1 : PomdpModel T 1 1 2) :
    InformationTheory.klDiv M0.law M1.law =
      InformationTheory.klDiv (obsLaw M0) (obsLaw M1) := by
  change InformationTheory.klDiv M0.law M1.law =
    InformationTheory.klDiv
      (Measure.map (singletonPathObsEquiv T) M0.law)
      (Measure.map (singletonPathObsEquiv T) M1.law)
  exact (Causalean.Mathlib.Probability.klDiv_map_measurableEquiv
    (singletonPathObsEquiv T) M0.law M1.law).symm

lemma parametricStateModel_audited_klDiv_le (T : Nat) (hT : 1 ≤ T)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    InformationTheory.klDiv (auditedLaw eta (parametricStateModel T false))
        (auditedLaw eta (parametricStateModel T true)) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
  let M0 := parametricStateModel T false
  let M1 := parametricStateModel T true
  let R := auditMaskLaw T eta
  letI : IsProbabilityMeasure R := auditMaskLaw_prob T eta heta
  have hprod : InformationTheory.klDiv (M0.law.prod R) (M1.law.prod R) =
      InformationTheory.klDiv M0.law M1.law := by
    rw [← Measure.compProd_const, ← Measure.compProd_const]
    exact Causalean.Mathlib.InformationTheory.Measure.klDiv_compProd_left
      M0.law M1.law (Kernel.const (FullPath T 1 1 2) R)
  unfold auditedLaw auditJointLaw
  calc
    InformationTheory.klDiv
        (Measure.map (fun q => auditRecord q.1 q.2) (M0.law.prod R))
        (Measure.map (fun q => auditRecord q.1 q.2) (M1.law.prod R)) ≤
        InformationTheory.klDiv (M0.law.prod R) (M1.law.prod R) :=
      InformationTheory.klDiv_map_le _ _ (by
        unfold auditRecord currentState actionAt rewardAt
        apply measurable_pi_lambda
        intro t
        apply Measurable.prodMk
        · fun_prop
        apply Measurable.prodMk
        · fun_prop
        apply Measurable.prodMk
        · fun_prop
        apply Measurable.prodMk
        · fun_prop
        apply Measurable.ite
        · exact (((measurable_pi_apply t).comp measurable_snd)
            (measurableSet_singleton true) :
              MeasurableSet ((fun q : FullPath T 1 1 2 × AuditMask T => q.2 t) ⁻¹' {true}))
        · fun_prop
        · fun_prop)
    _ = InformationTheory.klDiv M0.law M1.law := hprod
    _ = InformationTheory.klDiv (obsLaw M0) (obsLaw M1) :=
      singleton_law_klDiv_eq_obsLaw M0 M1
    _ ≤ ENNReal.ofReal (1 / 4 : ℝ) := parametricStateModel_observed_klDiv_le T hT

lemma parametricStateModel_audited_tv_le_half (T : Nat) (hT : 1 ≤ T)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.tvDist (auditedLaw eta (parametricStateModel T true))
      (auditedLaw eta (parametricStateModel T false)) ≤ 1 / 2 := by
  let P := auditedLaw eta (parametricStateModel T true)
  let Q := auditedLaw eta (parametricStateModel T false)
  letI : IsProbabilityMeasure P := auditedLaw_prob _ eta heta
  letI : IsProbabilityMeasure Q := auditedLaw_prob _ eta heta
  have hKL : InformationTheory.klDiv Q P ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
    parametricStateModel_audited_klDiv_le T hT eta heta
  have hfin : InformationTheory.klDiv Q P ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hKL
  have hac : Q ≪ P := (InformationTheory.klDiv_ne_top_iff.mp hfin).1
  have hKLreal : (InformationTheory.klDiv Q P).toReal ≤ 1 / 4 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL
    simpa using h
  rw [Causalean.Stat.tvDist_symm]
  have hp := Causalean.Stat.pinskerBound_of_ac_of_ne_top Q P hac hfin
  unfold Causalean.Stat.PinskerBound at hp
  apply hp.trans
  have hn : 0 ≤ (InformationTheory.klDiv Q P).toReal / 2 := by positivity
  nlinarith [Real.sq_sqrt hn,
    Real.sqrt_nonneg ((InformationTheory.klDiv Q P).toReal / 2)]

lemma auditedEstimator_sq_integrable {T nX nH k : Nat} {t0 zeta eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T)
    (M : PomdpModel T nX nH k) (hM : HuWagerClass t0 zeta M) :
    Integrable (fun w =>
      (est.1 nX nH k M.b M.e w - targetValue M) ^ 2) (auditedLaw eta M) := by
  letI : IsProbabilityMeasure (auditedLaw eta M) := auditedLaw_prob M eta heta
  apply Integrable.of_bound
    (((est.2.1 nX nH k M.b M.e).sub measurable_const).pow_const 2).aestronglyMeasurable 4
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  rcases est.2.2 nX nH k M.b M.e w with ⟨hew0, hew1⟩
  rcases targetValue_mem_unit_hw hM with ⟨ht0, ht1⟩
  have habs : |est.1 nX nH k M.b M.e w - targetValue M| ≤ 2 := by
    rw [abs_le]; constructor <;> linarith
  change |est.1 nX nH k M.b M.e w - targetValue M| ^ 2 ≤ 4
  calc
    _ ≤ (2 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
    _ = 4 := by norm_num

lemma parametric_twoPoint_lintegral_floor {Ω : Type*} [MeasurableSpace Ω]
    {T : Nat} (hT : 1 ≤ T) (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (htv : Causalean.Stat.tvDist P Q ≤ 1 / 2) (f : Ω → ℝ) (hf : Measurable f) :
    ENNReal.ofReal (3 / (512 * (T : ℝ))) ≤
      max (Causalean.Stat.sqRiskLIntegral P f
          (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T))
        (Causalean.Stat.sqRiskLIntegral Q f
          (-CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T)) := by
  let a := CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T
  have htwo := twoPoint_sqRiskLIntegral_tv P Q a
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude_mem T).1 f hf
  have hapos : 0 < Real.sqrt T := Real.sqrt_pos.2 (by exact_mod_cast hT)
  have hasq : a ^ 2 = 1 / (16 * (T : ℝ)) := by
    dsimp [a, CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude]
    field_simp [ne_of_gt hapos]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ T by positivity)]
  apply (ENNReal.ofReal_le_ofReal ?_).trans htwo
  rw [hasq]
  have hTp : (0 : ℝ) < T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hT)
  field_simp
  nlinarith

lemma twoModel_estimator_lintegral_floor {T : Nat} (hT : 1 ≤ T) {eta : ℝ}
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T)
    (M0 M1 : PomdpModel T 1 1 2) (hb : M0.b = M1.b) (he : M0.e = M1.e)
    (ht0v : targetValue M0 =
      -CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T)
    (ht1v : targetValue M1 =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T)
    (htv : Causalean.Stat.tvDist (auditedLaw eta M1) (auditedLaw eta M0) ≤ 1 / 2) :
    ENNReal.ofReal (3 / (512 * (T : ℝ))) ≤
      max (Causalean.Stat.sqRiskLIntegral (auditedLaw eta M1)
          (est.1 1 1 2 M1.b M1.e) (targetValue M1))
        (Causalean.Stat.sqRiskLIntegral (auditedLaw eta M0)
          (est.1 1 1 2 M0.b M0.e) (targetValue M0)) := by
  letI : IsProbabilityMeasure (auditedLaw eta M1) := auditedLaw_prob M1 eta heta
  letI : IsProbabilityMeasure (auditedLaw eta M0) := auditedLaw_prob M0 eta heta
  have h := parametric_twoPoint_lintegral_floor hT (auditedLaw eta M1)
    (auditedLaw eta M0) htv (est.1 1 1 2 M1.b M1.e) (est.2.1 _ _ _ _ _)
  have hf : est.1 1 1 2 M1.b M1.e = est.1 1 1 2 M0.b M0.e := by rw [hb, he]
  have ht01 : -targetValue M1 = targetValue M0 := by rw [ht1v, ht0v]
  rw [← ht1v, ht01] at h
  have hr : Causalean.Stat.sqRiskLIntegral (auditedLaw eta M0)
      (est.1 1 1 2 M1.b M1.e) (targetValue M0) =
      Causalean.Stat.sqRiskLIntegral (auditedLaw eta M0)
        (est.1 1 1 2 M0.b M0.e) (targetValue M0) := congrArg (fun g =>
          Causalean.Stat.sqRiskLIntegral (auditedLaw eta M0) g (targetValue M0)) hf
  rw [hr] at h
  exact h

lemma parametricStateModel_behavior_eq (T : Nat) (hT : 1 ≤ T) {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    (parametricStateModel T false).b = (parametricStateModel T true).b := by
  rcases CausalSmith.Stat.PomdpLatentOverlapMinimax.uniform_parametric_floor
      ht0 hzeta T hT 1 le_rfl with ⟨_, _, _, _, _, hb, _, _⟩
  simpa [parametricStateModel, embedBinary] using congrArg (fun p => fun s a =>
    p s (finActionBool a)) hb

lemma parametricStateModel_policy_eq (T : Nat) (hT : 1 ≤ T) {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    (parametricStateModel T false).e = (parametricStateModel T true).e := by
  rcases CausalSmith.Stat.PomdpLatentOverlapMinimax.uniform_parametric_floor
      ht0 hzeta T hT 1 le_rfl with ⟨_, _, _, _, _, _, he, _⟩
  simpa [parametricStateModel, embedBinary] using congrArg (fun p => fun s a =>
    p s (finActionBool a)) he

lemma parametricStateModel_target_eq_false {T : Nat} {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    targetValue (parametricStateModel T false) =
      -CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T := by
  simpa [CausalSmith.Stat.PomdpLatentOverlapMinimax.signedValue] using
    (parametricStateModel_targetValue ht0 hzeta false)

lemma parametricStateModel_target_eq_true {T : Nat} {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    targetValue (parametricStateModel T true) =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.parametricAmplitude T := by
  simpa [CausalSmith.Stat.PomdpLatentOverlapMinimax.signedValue] using
    (parametricStateModel_targetValue ht0 hzeta true)

/-- The extended risks of the parametric pair obey the testing floor. -/
lemma parametricStateModel_estimator_lintegral_floor {T : Nat} (hT : 1 ≤ T)
    {t0 zeta eta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T) :
    ENNReal.ofReal (3 / (512 * (T : ℝ))) ≤
      max (Causalean.Stat.sqRiskLIntegral (auditedLaw eta (parametricStateModel T true))
          (est.1 1 1 2 (parametricStateModel T true).b (parametricStateModel T true).e)
          (targetValue (parametricStateModel T true)))
        (Causalean.Stat.sqRiskLIntegral (auditedLaw eta (parametricStateModel T false))
          (est.1 1 1 2 (parametricStateModel T false).b (parametricStateModel T false).e)
          (targetValue (parametricStateModel T false))) := by
  exact twoModel_estimator_lintegral_floor hT heta est
    (parametricStateModel T false) (parametricStateModel T true)
    (parametricStateModel_behavior_eq T hT ht0 hzeta)
    (parametricStateModel_policy_eq T hT ht0 hzeta)
    (parametricStateModel_target_eq_false ht0 hzeta)
    (parametricStateModel_target_eq_true ht0 hzeta)
    (parametricStateModel_audited_tv_le_half T hT eta heta)

/-- Every audited estimator incurs the parametric floor on one member of the pair. -/
lemma parametricStateModel_estimator_floor {T : Nat} (hT : 1 ≤ T)
    {t0 zeta eta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) (est : AuditedEstimator T) :
    3 / (512 * (T : ℝ)) ≤
      max (Causalean.Stat.sqRisk (auditedLaw eta (parametricStateModel T true))
          (est.1 1 1 2 (parametricStateModel T true).b (parametricStateModel T true).e)
          (targetValue (parametricStateModel T true)))
        (Causalean.Stat.sqRisk (auditedLaw eta (parametricStateModel T false))
          (est.1 1 1 2 (parametricStateModel T false).b (parametricStateModel T false).e)
          (targetValue (parametricStateModel T false))) := by
  have h := parametricStateModel_estimator_lintegral_floor hT ht0 hzeta heta est
  rw [sqRiskLIntegral_eq_ofReal_sqRisk _ _ _
      (auditedEstimator_sq_integrable heta est _
        (parametricStateModel_invariance ht0 hzeta true).1),
    sqRiskLIntegral_eq_ofReal_sqRisk _ _ _
      (auditedEstimator_sq_integrable heta est _
        (parametricStateModel_invariance ht0 hzeta false).1),
    ← ENNReal.ofReal_max] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    ((integral_nonneg fun _ => sq_nonneg _).trans (le_max_left _ _))).mp h

/-- The singleton-state reward pair supplies the parametric invariance lower bound. -/
lemma invarianceMinimaxRisk_lower_parametric {T : Nat} (hT : 1 ≤ T)
    {t0 zeta eta : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    3 / (512 * (T : ℝ)) ≤ invarianceMinimaxRisk T t0 zeta eta := by
  let M0 := parametricStateModel T false
  let M1 := parametricStateModel T true
  have hM0 : InvarianceClass t0 zeta M0 := parametricStateModel_invariance ht0 hzeta false
  have hM1 : InvarianceClass t0 zeta M1 := parametricStateModel_invariance ht0 hzeta true
  let i0 : HWIndex T t0 zeta :=
    ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, M0, hM0.1⟩
  let i1 : HWIndex T t0 zeta :=
    ⟨1, 1, 2, by norm_num, by norm_num, by norm_num, M1, hM1.1⟩
  let j0 : {i : HWIndex T t0 zeta // InvarianceClass t0 zeta i.raw} := ⟨i0, hM0⟩
  let j1 : {i : HWIndex T t0 zeta // InvarianceClass t0 zeta i.raw} := ⟨i1, hM1⟩
  unfold invarianceMinimaxRisk
  let zeroEst : AuditedEstimator T := ⟨fun _ _ _ _ _ _ => 0, by
    constructor
    · intros; fun_prop
    · intros; norm_num⟩
  letI : Nonempty (AuditedEstimator T) := ⟨zeroEst⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  have hlowerReal : 3 / (512 * (T : ℝ)) ≤
      max (auditedRisk eta est i1) (auditedRisk eta est i0) := by
    simpa [auditedRisk, i0, i1, M0, M1] using
      parametricStateModel_estimator_floor hT ht0 hzeta heta est
  let InvIndex := {i : HWIndex T t0 zeta // InvarianceClass t0 zeta i.raw}
  let risk : AuditedEstimator T → InvIndex → ℝ := fun est i => auditedRisk eta est i.1
  have hbdd : BddAbove (Set.range (risk est)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact auditedRisk_le_four heta est i.1
  have hw1 : auditedRisk eta est i1 ≤ Causalean.Stat.worstCaseRiskReal risk est := by
    simpa [risk, InvIndex, j1] using
      (Causalean.Stat.le_worstCaseRisk (risk := risk) (e := est) hbdd j1)
  have hw0 : auditedRisk eta est i0 ≤ Causalean.Stat.worstCaseRiskReal risk est := by
    simpa [risk, InvIndex, j0] using
      (Causalean.Stat.le_worstCaseRisk (risk := risk) (e := est) hbdd j0)
  exact hlowerReal.trans (max_le hw1 hw0)

end CausalSmith.Stat.PomdpStateauditMinimax
