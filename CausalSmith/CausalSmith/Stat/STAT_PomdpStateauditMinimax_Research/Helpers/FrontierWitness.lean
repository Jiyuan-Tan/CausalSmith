module
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FrontierTheorems

/-! # A recurrent constant-path witness for the exact birthday distance. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory Filter

-- @node: probe_fullFiltrationPomdp
lemma probe_fullFiltrationPomdp (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    FullFiltrationPomdp (probeConstantModel T n k hn hk) := by
  constructor
  · intro s a
    change IsProbabilityMeasure (Measure.dirac _)
    infer_instance
  · intro t
    letI : IsMarkovKernel (kernelOfK (probeConstantModel T n k hn hk)) :=
      ⟨fun _ => by change IsProbabilityMeasure (Measure.dirac _); infer_instance⟩
    have hjoint : Measurable (fun w : FullPath T 1 n k =>
        (postHist t w, (rewardAt w t, nextState w t))) := by
      unfold postHist preHist pastIndex currentState actionAt rewardAt nextState
      fun_prop
    have hpost : Measurable (postHist t : FullPath T 1 n k → _) := by
      unfold postHist preHist pastIndex currentState actionAt
      fun_prop
    ext A hA
    change (Measure.map (fun w : FullPath T 1 n k =>
      (postHist t w, (rewardAt w t, nextState w t)))
        (Measure.dirac (probeConstantPath T n k hn hk))) A =
      ((Measure.map (postHist t) (Measure.dirac (probeConstantPath T n k hn hk))).compProd
        (Kernel.comap (kernelOfK (probeConstantModel T n k hn hk))
          (fun h => (h.1.2.2, h.2)) (by fun_prop))) A
    rw [Measure.map_dirac (probeConstantPath T n k hn hk),
      Measure.map_dirac (probeConstantPath T n k hn hk),
      Measure.dirac_compProd_apply hA]
    simp [probeConstantModel, probeConstantPath, postHist, preHist, currentState,
      actionAt, rewardAt, nextState, kernelOfK, Kernel.comap_apply,
      Kernel.ofFunOfCountable]
    rfl

-- @node: probe_fullFiltrationRandomization
lemma probe_fullFiltrationRandomization (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    FullFiltrationRandomization (probeConstantModel T n k hn hk) := by
  constructor
  · intro x
    constructor
    · intro a
      simp only [probeConstantModel]
      split_ifs <;> positivity
    · simp [probeConstantModel]
  · intro t
    letI : IsMarkovKernel (actionKernel (probeConstantModel T n k hn hk)) := by
      refine ⟨fun x => ⟨?_⟩⟩
      change (∑ a : Fin k, ENNReal.ofReal
        (if a = (⟨0, by omega⟩ : Fin k) then 1 else 0) • Measure.dirac a) Set.univ = 1
      simp only [Measure.finsetSum_apply, Measure.smul_apply,
        Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
      rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin k)]
      · simp
      · intro b _ hb
        simp [hb]
      · simp
    have hjoint : Measurable (fun w : FullPath T 1 n k =>
        (preHist t w, actionAt w t)) := by
      unfold preHist pastIndex currentState actionAt
      fun_prop
    have hpre : Measurable (preHist t : FullPath T 1 n k → _) := by
      unfold preHist pastIndex currentState
      fun_prop
    ext A hA
    change (Measure.map (fun w : FullPath T 1 n k => (preHist t w, actionAt w t))
      (Measure.dirac (probeConstantPath T n k hn hk))) A =
      ((Measure.map (preHist t) (Measure.dirac (probeConstantPath T n k hn hk))).compProd
        (Kernel.comap (actionKernel (probeConstantModel T n k hn hk))
          (fun h => h.2.2.1) (by fun_prop))) A
    rw [Measure.map_dirac (probeConstantPath T n k hn hk),
      Measure.map_dirac (probeConstantPath T n k hn hk),
      Measure.dirac_compProd_apply hA]
    simp [probeConstantModel, probeConstantPath, preHist, currentState,
      actionAt, actionKernel, Kernel.comap_apply, Kernel.ofFunOfCountable]
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin k)]
    · simp
      rfl
    · intro b _ hb
      simp [hb]
    · simp

-- @node: probe_policyKernel
lemma probe_policyKernel (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (s s' : JointState 1 n) :
    policyKernel (probeConstantModel T n k hn hk)
      (probeConstantModel T n k hn hk).b s s' =
      if s' = ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n)) then 1 else 0 := by
  unfold policyKernel
  simp only [probeConstantModel]
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin k)]
  · simp only [if_pos, one_mul]
    have hset : MeasurableSet {q : ℝ × JointState 1 n | q.2 = s'} := by
      exact measurableSet_singleton s' |>.preimage measurable_snd
    rw [Measure.dirac_apply' _ hset]
    by_cases hs : s' = ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n))
    · subst s'
      simp
    · rw [Set.indicator_of_notMem]
      · rw [if_neg hs]
        simp
      · intro hmem
        apply hs
        exact hmem.symm
  · intro a _ ha
    simp [ha]
  · simp

-- @node: probe_stationaryStart
lemma probe_stationaryStart (T n k : Nat) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    StationaryStart (probeConstantModel T n k hn hk) := by
  let s0 : JointState 1 n :=
    ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n))
  have hs0 : ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n)) = s0 := by
    apply Prod.ext
    · apply Subsingleton.elim
    · apply Fin.ext
      rfl
  let p0 : JointState 1 n → ℝ := fun s => if s = s0 then 1 else 0
  have hp0 : IsStationary
      (policyKernel (probeConstantModel T n k hn hk)
        (probeConstantModel T n k hn hk).b) p0 := by
    constructor
    · constructor
      · intro s
        dsimp [p0]
        split_ifs <;> positivity
      · rw [Finset.sum_eq_single s0]
        · simp [p0]
        · intro s _ hs
          simp [p0, hs]
        · simp
    · intro s'
      rw [Finset.sum_eq_single s0]
      · rw [probe_policyKernel]
        rw [hs0]
        simp [p0]
      · intro s _ hs
        simp [p0, hs]
      · simp
  have hselected : IsStationary
      (policyKernel (probeConstantModel T n k hn hk)
        (probeConstantModel T n k hn hk).b)
      (stationaryLaw (policyKernel (probeConstantModel T n k hn hk)
        (probeConstantModel T n k hn hk).b)) :=
    Classical.epsilon_spec ⟨p0, hp0⟩
  have heq : stationaryLaw (policyKernel (probeConstantModel T n k hn hk)
      (probeConstantModel T n k hn hk).b) = p0 := by
    funext s'
    have hs := hselected.2 s'
    simp_rw [probe_policyKernel] at hs
    rw [hs0] at hs
    by_cases h : s' = s0
    · subst s'
      simpa [p0, hselected.1.2] using hs.symm
    · simpa [p0, h] using hs.symm
  constructor
  · rw [heq]
    exact hp0
  · intro s
    rw [heq]
    have hstate : Measurable (fun w : FullPath T 1 n k => stateAt w 0) := by
      unfold stateAt
      fun_prop
    simp only [probeConstantModel, Measure.map_dirac]
    rw [Measure.dirac_apply' _ (measurableSet_singleton s)]
    change {q : JointState 1 n | q = s}.indicator
      (1 : JointState 1 n → ENNReal) (stateAt (probeConstantPath T n k hn hk) 0) =
        ENNReal.ofReal (p0 s)
    have hpath : stateAt (probeConstantPath T n k hn hk) 0 = s0 := by
      apply Prod.ext
      · apply Subsingleton.elim
      · apply Fin.ext
        rfl
    rw [hpath]
    by_cases h : s = s0
    · subst s
      simp [p0]
    · rw [Set.indicator_of_notMem]
      · simp [p0, h]
      · simpa [Set.mem_setOf_eq] using Ne.symm h

-- @node: probe_auditRank_strictMono_on_true
lemma probe_auditRank_strictMono_on_true {T : Nat} (mask : AuditMask T)
    {t u : Fin T} (htu : t < u) (ht : mask t = true) :
    auditRank mask t < auditRank mask u := by
  unfold auditRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact ⟨lt_trans hj.1 htu, hj.2⟩
  · intro heq
    have hmemu : t ∈ Finset.univ.filter (fun j : Fin T => j.val < u.val ∧ mask j) := by
      simp [htu, ht]
    have hmemt : t ∈ Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j) :=
      heq.symm ▸ hmemu
    simp at hmemt

-- @node: probe_auditRank_injective_on_true
lemma probe_auditRank_injective_on_true {T : Nat} (mask : AuditMask T) :
    Function.Injective (fun t : {t : Fin T // mask t = true} => auditRank mask t) := by
  intro t u h
  apply Subtype.ext
  rcases lt_trichotomy t.1 u.1 with hlt | heq | hgt
  · exact False.elim (Nat.ne_of_lt (probe_auditRank_strictMono_on_true mask hlt t.2) h)
  · exact heq
  · exact False.elim (Nat.ne_of_gt (probe_auditRank_strictMono_on_true mask hgt u.2) h)

-- @node: probe_auditRank_lt_T
lemma probe_auditRank_lt_T {T : Nat} (mask : AuditMask T)
    (t : Fin T) (ht : mask t = true) : auditRank mask t < T := by
  unfold auditRank
  have hlt :
      (Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j)).card <
        (Finset.univ.filter fun j : Fin T => mask j).card := by
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact hj.2
    · intro heq
      have hmem : t ∈ Finset.univ.filter (fun j : Fin T => mask j) := by simp [ht]
      have : t ∈ Finset.univ.filter (fun j : Fin T => j.val < t.val ∧ mask j) :=
        heq ▸ hmem
      simp at this
  exact lt_of_lt_of_le hlt (by
    simpa using Finset.card_le_card
      (Finset.filter_subset (fun j : Fin T => mask j) Finset.univ))

-- @node: probe_freshRecord_no_repeated
lemma probe_freshRecord_no_repeated {T n k m : Nat}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hcard : T ≤ n * m)
    (w : ObsPath T 1 k) (mask : AuditMask T) (σ : Equiv.Perm (Fin (n * m))) :
    ¬ RepeatedAuditLabel (freshRecord hn hm w mask σ) := by
  rintro ⟨t, u, htu, ht, hu, hlabels, hsome⟩
  have htmask : mask t = true := by simpa [freshRecord] using ht
  have humask : mask u = true := by simpa [freshRecord] using hu
  have hrt : auditRank mask t < n * m :=
    lt_of_lt_of_le (probe_auditRank_lt_T mask t htmask) hcard
  have hru : auditRank mask u < n * m :=
    lt_of_lt_of_le (probe_auditRank_lt_T mask u humask) hcard
  have hrank : auditRank mask t = auditRank mask u := by
    simp only [freshRecord] at hlabels
    rw [if_pos htmask, if_pos humask, dif_pos hrt, dif_pos hru] at hlabels
    injection hlabels with hpair
    exact Fin.ext_iff.mp (σ.injective (congrArg Prod.snd hpair))
  have htu' : (⟨t, htmask⟩ : {j : Fin T // mask j = true}) = ⟨u, humask⟩ :=
    probe_auditRank_injective_on_true mask hrank
  exact htu (congrArg Subtype.val htu')

example {T n k : Nat} :
    MeasurableSet {w : AuditedRecord T 1 n k | RepeatedAuditLabel w} := by
  unfold RepeatedAuditLabel
  measurability

-- @node: probe_freshLabelLaw_repeated_zero
lemma probe_freshLabelLaw_repeated_zero {T n k m : Nat} (M : PomdpModel T 1 n k)
    (hn : 1 ≤ n) (hm : 1 ≤ m) (eta : ℝ) (hcard : T ≤ n * m) :
    (freshLabelLaw M hn hm eta) {w | RepeatedAuditLabel w} = 0 := by
  have hE : MeasurableSet
      {w : AuditedRecord T 1 (n * m) k | RepeatedAuditLabel w} := by
    unfold RepeatedAuditLabel
    measurability
  rw [freshLabelLaw, Measure.bind_apply hE (Kernel.aemeasurable _)]
  have hz (w : ObsPath T 1 k) :
      (freshKernel hn hm eta w) {z | RepeatedAuditLabel z} = 0 := by
    change (((auditMaskLaw T eta).prod (uniformPermutation (n * m))).map
      (fun q => freshRecord hn hm w q.1 q.2)) {z | RepeatedAuditLabel z} = 0
    rw [Measure.map_apply (by fun_prop) hE]
    rw [show (fun q : AuditMask T × Equiv.Perm (Fin (n * m)) =>
        freshRecord hn hm w q.1 q.2) ⁻¹' {z | RepeatedAuditLabel z} = ∅ by
      ext q
      constructor
      · intro h
        exact (probe_freshRecord_no_repeated hn hm hcard w q.1 q.2 h).elim
      · intro h
        exact h.elim]
    simp
  simp_rw [hz]
  exact lintegral_zero

-- @node: probe_fixedPermutationRecord_measurable
lemma probe_fixedPermutationRecord_measurable {T n k m : Nat} :
    Measurable (fixedPermutationRecord :
      ((FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
        ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) →
          AuditedRecord T 1 (n * m) k) := by
  unfold fixedPermutationRecord auditRecord clonePath currentState actionAt rewardAt
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
  · exact (((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
      (measurableSet_singleton true) : MeasurableSet
        ((fun q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
          ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T) => q.2.2 t) ⁻¹' {true}))
  · fun_prop
  · fun_prop

-- @node: probe_repeated_fixed_iff_collision
lemma probe_repeated_fixed_iff_collision {T n k m : Nat}
    (q : (FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :
    RepeatedAuditLabel (fixedPermutationRecord q) ↔
      CloneCollision q.2.2 (clonePath q.2.1 q.1.1 q.1.2) := by
  constructor
  · rintro ⟨t, u, htu, ht, hu, heq, hsome⟩
    have ht' : q.2.2 t = true := by
      simpa [fixedPermutationRecord, auditRecord] using ht
    have hu' : q.2.2 u = true := by
      simpa [fixedPermutationRecord, auditRecord] using hu
    refine ⟨t, u, htu, ht', hu', ?_⟩
    simpa [fixedPermutationRecord, auditRecord, ht', hu'] using heq
  · rintro ⟨t, u, htu, ht, hu, heq⟩
    refine ⟨t, u, htu, ?_, ?_, ?_, ?_⟩
    · simpa [fixedPermutationRecord, auditRecord] using ht
    · simpa [fixedPermutationRecord, auditRecord] using hu
    · simpa [fixedPermutationRecord, auditRecord, ht, hu] using heq
    · simp [fixedPermutationRecord, auditRecord, ht]

-- @node: probe_fixedCoupling_constantPath
lemma probe_fixedCoupling_constantPath {T n k m : Nat}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (eta : ℝ) :
    ∀ᵐ q ∂(fixedPermutationCoupling (m := m) (probeConstantModel T n k hn hk) eta),
      q.1.1 = probeConstantPath T n k hn hk := by
  have hbase : ∀ᵐ w ∂(Measure.dirac (probeConstantPath T n k hn hk)),
      w = probeConstantPath T n k hn hk := by simp
  have hfirst : ∀ᵐ q ∂((Measure.dirac (probeConstantPath T n k hn hk)).prod
      (Measure.pi fun _ : Fin (T + 1) => uniformFin m)),
      q.1 = probeConstantPath T n k hn hk :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae hbase
  have hsecond : ∀ᵐ q ∂(((Measure.dirac (probeConstantPath T n k hn hk)).prod
      (Measure.pi fun _ : Fin (T + 1) => uniformFin m)).prod
        ((uniformRelabeling n m).prod (auditMaskLaw T eta))),
      q.1.1 = probeConstantPath T n k hn hk :=
    Measure.quasiMeasurePreserving_fst.tendsto_ae hfirst
  simpa [fixedPermutationCoupling, probeConstantModel] using hsecond

-- @node: probe_coordinateCollision_iff_not_injective
lemma probe_coordinateCollision_iff_not_injective {T m : Nat}
    (coords : Fin (T + 1) → Fin m) (mask : AuditMask T) :
    (∃ t u : Fin T, t ≠ u ∧ mask t = true ∧ mask u = true ∧
      coords t.castSucc = coords u.castSucc) ↔
    ¬ Function.Injective
      (fun t : auditedIndex mask => coords t.1.castSucc) := by
  classical
  constructor
  · rintro ⟨t, u, htu, ht, hu, hcoord⟩ hinj
    have heq : (⟨t, ht⟩ : auditedIndex mask) = ⟨u, hu⟩ := hinj hcoord
    exact htu (congrArg Subtype.val heq)
  · intro h
    simp only [Function.Injective] at h
    push_neg at h
    rcases h with ⟨t, u, hcoord, htu⟩
    exact ⟨t.1, u.1, fun hval => htu (Subtype.ext hval), t.2, u.2, hcoord⟩

-- @node: probe_permutationMixture_repeated_real
lemma probe_permutationMixture_repeated_real {T n k m : Nat}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) :
    (permutationMixture (probeConstantModel T n k hn hk) hm eta).real
      {w | RepeatedAuditLabel w} = collisionEnvelope T eta m := by
  let M := probeConstantModel T n k hn hk
  have hres := overflow_safe_fixed_permutation_tv M hn hm
    (probe_fullFiltrationPomdp T n k hn hk)
    (probe_fullFiltrationRandomization T n k hn hk)
    (probe_stationaryStart T n k hn hk) eta ⟨heta, rfl⟩
    auditRecord_atomic_labels
  have hmix := hres.2.1
  have hE : MeasurableSet
      {w : AuditedRecord T 1 (n * m) k | RepeatedAuditLabel w} := by
    unfold RepeatedAuditLabel
    measurability
  rw [← hmix, Measure.real, Measure.map_apply probe_fixedPermutationRecord_measurable hE]
  let γ := fixedPermutationCoupling (m := m) M eta
  let C : Set ((FullPath T 1 n k × (Fin (T + 1) → Fin m)) ×
      ((Fin n × Fin m ≃ Fin (n * m)) × AuditMask T)) :=
    {q | ¬ Function.Injective
      (fun t : auditedIndex q.2.2 => q.1.2 t.1.castSucc)}
  have hpath : ∀ᵐ q ∂γ, q.1.1 = probeConstantPath T n k hn hk := by
    exact probe_fixedCoupling_constantPath hn hk eta
  have haeeq : fixedPermutationRecord ⁻¹' {w | RepeatedAuditLabel w} =ᵐ[γ] C := by
    filter_upwards [hpath] with q hq
    apply propext
    change RepeatedAuditLabel (fixedPermutationRecord q) ↔
      ¬ Function.Injective (fun t : auditedIndex q.2.2 => q.1.2 t.1.castSucc)
    rw [probe_repeated_fixed_iff_collision,
      constantPath_cloneCollision_iff_coordinateCollision q.2.1 q.1.1 q.1.2 q.2.2
        (((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n)) : JointState 1 n)]
    · exact probe_coordinateCollision_iff_not_injective q.1.2 q.2.2
    · intro t
      rw [hq]
      rfl
  change (γ (fixedPermutationRecord ⁻¹' {w | RepeatedAuditLabel w})).toReal = _
  rw [measure_congr haeeq]
  exact frontier_coordinateCollision_mass M hm eta heta

-- @node: probe_constantModel_exact_tv
lemma probe_constantModel_exact_tv {T n k m : Nat}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hcard : T ≤ n * m) :
    Causalean.Stat.tvDist
      (permutationMixture (probeConstantModel T n k hn hk) hm eta)
      (freshLabelLaw (probeConstantModel T n k hn hk) hn hm eta) =
        collisionEnvelope T eta m := by
  let M := probeConstantModel T n k hn hk
  letI : IsProbabilityMeasure (permutationMixture M hm eta) :=
    permutationMixture_prob M hm eta heta
  letI : IsProbabilityMeasure (obsLaw M) :=
    Measure.isProbabilityMeasure_map (by
      unfold obsProj currentState actionAt rewardAt
      fun_prop)
  letI : IsMarkovKernel (freshKernel (T := T) (k := k) hn hm eta) :=
    freshKernel_markov hn hm eta heta
  letI : IsProbabilityMeasure (freshLabelLaw M hn hm eta) := by
    unfold freshLabelLaw
    infer_instance
  have hE : MeasurableSet
      {w : AuditedRecord T 1 (n * m) k | RepeatedAuditLabel w} := by
    unfold RepeatedAuditLabel
    measurability
  have hlower := Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := permutationMixture M hm eta) (ν := freshLabelLaw M hn hm eta) hE
  rw [probe_permutationMixture_repeated_real hn hk hm eta heta] at hlower
  have hfresh := probe_freshLabelLaw_repeated_zero M hn hm eta hcard
  rw [Measure.real, hfresh, ENNReal.toReal_zero, sub_zero,
    abs_of_nonneg (collisionEnvelope_nonneg T m eta hm heta)] at hlower
  apply le_antisymm
  · exact frontier_fixed_permutation_tv_upper M hn hm
      (probe_fullFiltrationPomdp T n k hn hk)
      (probe_fullFiltrationRandomization T n k hn hk)
      (probe_stationaryStart T n k hn hk) eta heta
  · exact hlower

-- @node: probe_exact_witness
lemma probe_exact_witness {T n k m : Nat}
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m)
    (eta : ℝ) (heta : eta ∈ Set.Icc (0 : ℝ) 1) (hcard : T ≤ n * m) :
    ∃ M : PomdpModel T 1 n k,
      FullFiltrationPomdp M ∧ FullFiltrationRandomization M ∧ StationaryStart M ∧
      (∃ s0 : JointState 1 n, M.law {w | ∀ t : Fin T, currentState w t = s0} = 1) ∧
      Causalean.Stat.tvDist (permutationMixture M hm eta)
        (freshLabelLaw M hn hm eta) = collisionEnvelope T eta m := by
  let M := probeConstantModel T n k hn hk
  refine ⟨M, probe_fullFiltrationPomdp T n k hn hk,
    probe_fullFiltrationRandomization T n k hn hk,
    probe_stationaryStart T n k hn hk, ?_,
    probe_constantModel_exact_tv hn hk hm eta heta hcard⟩
  let s0 : JointState 1 n :=
    ((⟨0, by omega⟩ : Fin 1), (⟨0, by omega⟩ : Fin n))
  refine ⟨s0, ?_⟩
  have hset : MeasurableSet
      {w : FullPath T 1 n k | ∀ t : Fin T, currentState w t = s0} := by
    rw [show {w : FullPath T 1 n k | ∀ t : Fin T, currentState w t = s0} =
        ⋂ t : Fin T, {w | currentState w t = s0} by
      ext w
      simp]
    exact MeasurableSet.iInter fun t =>
      (measurableSet_singleton s0).preimage (show Measurable
        (fun w : FullPath T 1 n k => currentState w t) by
        unfold currentState
        fun_prop)
  change (Measure.dirac (probeConstantPath T n k hn hk))
    {w | ∀ t : Fin T, currentState w t = s0} = 1
  rw [Measure.dirac_apply' _ hset]
  simp only [Set.indicator, Pi.one_apply]
  split_ifs with h
  · rfl
  · exfalso
    apply h
    intro t
    apply Prod.ext
    · apply Subsingleton.elim
    · apply Fin.ext
      rfl
end CausalSmith.Stat.PomdpStateauditMinimax
