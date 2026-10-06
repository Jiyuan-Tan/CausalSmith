module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.ObservedKL
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwHistory
public import CausalSmith.Stat.STAT_PomdpStateauditMinimax_Research.Helpers.FullHistory
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Signed-depth binary-action witnesses and their observed-path KL bound. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpStateauditMinimax

open MeasureTheory ProbabilityTheory

@[no_expose]
private def encodeBinaryPath {T nX nH : Nat}
    (w : CausalSmith.Stat.PomdpLatentOverlapMinimax.FullTrajectory T nX nH) :
    FullPath T nX nH 2 :=
  (w.1, fun t => (boolActionFin (w.2 t).1, (w.2 t).2))

@[no_expose]
private def encodeBinaryPreHistory {T nX nH : Nat} (t : Fin T)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.StateHistoryView T nX nH t) :
    PreHistory T nX nH 2 t :=
  (h.1.1, fun j => (boolActionFin (h.1.2 j).1, (h.1.2 j).2), h.2)

@[no_expose]
private def encodeBinaryPostHistory {T nX nH : Nat} (t : Fin T)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.ActionHistoryView T nX nH t) :
    PostHistory T nX nH 2 t :=
  (encodeBinaryPreHistory t h.1, boolActionFin h.2)

-- @node: measurable_boolActionFin
/-- The binary-action encoding is measurable. -/
@[fun_prop]
lemma measurable_boolActionFin : Measurable boolActionFin := measurable_of_finite _

@[fun_prop]
private lemma measurable_encodeBinaryPath {T nX nH : Nat} :
    Measurable (@encodeBinaryPath T nX nH) := by
  unfold encodeBinaryPath
  fun_prop

@[fun_prop]
private lemma measurable_encodeBinaryPreHistory {T nX nH : Nat} (t : Fin T) :
    Measurable (@encodeBinaryPreHistory T nX nH t) := by
  unfold encodeBinaryPreHistory
  fun_prop

@[fun_prop]
private lemma measurable_encodeBinaryPostHistory {T nX nH : Nat} (t : Fin T) :
    Measurable (@encodeBinaryPostHistory T nX nH t) := by
  unfold encodeBinaryPostHistory
  fun_prop

private lemma measurable_preHist' {T nX nH k : Nat} (t : Fin T) :
    Measurable (@preHist T nX nH k t) := by
  unfold preHist currentState pastIndex
  fun_prop

private lemma measurable_postHist' {T nX nH k : Nat} (t : Fin T) :
    Measurable (@postHist T nX nH k t) := by
  unfold postHist
  exact (measurable_preHist' t).prodMk (by unfold actionAt; fun_prop)

private lemma measurable_actionHistory' {T nX nH k : Nat} (t : Fin T) :
    Measurable (fun w : FullPath T nX nH k => (preHist t w, actionAt w t)) := by
  exact (measurable_preHist' t).prodMk (by unfold actionAt; fun_prop)

private lemma measurable_nextHistory' {T nX nH k : Nat} (t : Fin T) :
    Measurable (fun w : FullPath T nX nH k =>
      (postHist t w, (rewardAt w t, nextState w t))) := by
  have hr : Measurable (fun w : FullPath T nX nH k => rewardAt w t) := by
    unfold rewardAt
    fun_prop
  have hn : Measurable (fun w : FullPath T nX nH k => nextState w t) := by
    unfold nextState
    fun_prop
  exact (measurable_postHist' t).prodMk (hr.prodMk hn)

private lemma measurable_raw_stateHistory {T nX nH : Nat} (t : Fin T) :
    Measurable (@CausalSmith.Stat.PomdpLatentOverlapMinimax.histStateView T nX nH t) := by
  unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.histStateView
    CausalSmith.Stat.PomdpLatentOverlapMinimax.curState
    CausalSmith.Stat.PomdpLatentOverlapMinimax.prefixIndex
  fun_prop

private lemma measurable_raw_actionHistory {T nX nH : Nat} (t : Fin T) :
    Measurable (@CausalSmith.Stat.PomdpLatentOverlapMinimax.histActionPair T nX nH t) := by
  unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.histActionPair
    CausalSmith.Stat.PomdpLatentOverlapMinimax.actionAt
  exact (measurable_raw_stateHistory t).prodMk (by fun_prop)

private lemma measurable_raw_nextHistory {T nX nH : Nat} (t : Fin T) :
    Measurable (@CausalSmith.Stat.PomdpLatentOverlapMinimax.histNextPair T nX nH t) := by
  unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.histNextPair
    CausalSmith.Stat.PomdpLatentOverlapMinimax.histView
    CausalSmith.Stat.PomdpLatentOverlapMinimax.rewardAt
    CausalSmith.Stat.PomdpLatentOverlapMinimax.nextState
  have hr : Measurable (fun w :
      CausalSmith.Stat.PomdpLatentOverlapMinimax.FullTrajectory T nX nH => w.2 t |>.2) := by
    fun_prop
  have hn : Measurable (fun w :
      CausalSmith.Stat.PomdpLatentOverlapMinimax.FullTrajectory T nX nH => w.1 t.succ) := by
    fun_prop
  exact (measurable_raw_actionHistory t).prodMk (hr.prodMk hn)

private lemma finActionBool_boolActionFin (a : Bool) :
    finActionBool (boolActionFin a) = a := by
  cases a <;> rfl

-- @node: embedBinary_actionKernel_apply
/-- Recoding Boolean actions as `Fin 2` maps the predecessor behavior kernel
fiberwise. -/
lemma embedBinary_actionKernel_apply {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (x : Fin nX) :
    actionKernel (embedBinary M) x = Measure.map boolActionFin
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.behaviourKernel M x) := by
  apply Measure.ext_of_singleton
  intro a
  change (∑ z : Fin 2, ENNReal.ofReal (M.b x (finActionBool z)) • Measure.dirac z) {a} =
    Measure.map boolActionFin
      (∑ z : Bool, ENNReal.ofReal (M.b x z) • Measure.dirac z) {a}
  rw [Measure.map_apply measurable_boolActionFin (measurableSet_singleton a)]
  fin_cases a <;> simp [boolActionFin, finActionBool]

private lemma embedBinary_law_map_preHistory {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (t : Fin T) :
    (embedBinary M).law.map (preHist t) =
      Measure.map (encodeBinaryPreHistory t)
        (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histStateView t)) := by
  unfold embedBinary
  change Measure.map (preHist t) (Measure.map encodeBinaryPath M.law) = _
  rw [Measure.map_map (measurable_preHist' t) measurable_encodeBinaryPath,
    Measure.map_map (measurable_encodeBinaryPreHistory t) (measurable_raw_stateHistory t)]
  congr 1

private lemma embedBinary_law_map_actionHistory {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (t : Fin T) :
    (embedBinary M).law.map (fun w => (preHist t w, actionAt w t)) =
      Measure.map (Prod.map (encodeBinaryPreHistory t) boolActionFin)
        (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histActionPair t)) := by
  unfold embedBinary
  change Measure.map (fun w => (preHist t w, actionAt w t))
    (Measure.map encodeBinaryPath M.law) = _
  rw [Measure.map_map (measurable_actionHistory' t) measurable_encodeBinaryPath,
    Measure.map_map ((measurable_encodeBinaryPreHistory t).prodMap measurable_boolActionFin)
      (measurable_raw_actionHistory t)]
  congr 1

private lemma embedBinary_law_map_postHistory {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (t : Fin T) :
    (embedBinary M).law.map (postHist t) =
      Measure.map (encodeBinaryPostHistory t)
        (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histView t)) := by
  unfold embedBinary
  change Measure.map (postHist t) (Measure.map encodeBinaryPath M.law) = _
  rw [Measure.map_map (measurable_postHist' t) measurable_encodeBinaryPath,
    Measure.map_map (measurable_encodeBinaryPostHistory t) (measurable_raw_actionHistory t)]
  congr 1

private lemma embedBinary_law_map_nextHistory {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (t : Fin T) :
    (embedBinary M).law.map
        (fun w => (postHist t w, (rewardAt w t, nextState w t))) =
      Measure.map (Prod.map (encodeBinaryPostHistory t) id)
        (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histNextPair t)) := by
  unfold embedBinary
  change Measure.map (fun w => (postHist t w, (rewardAt w t, nextState w t)))
    (Measure.map encodeBinaryPath M.law) = _
  rw [Measure.map_map (measurable_nextHistory' t) measurable_encodeBinaryPath,
    Measure.map_map ((measurable_encodeBinaryPostHistory t).prodMap measurable_id)
      (measurable_raw_nextHistory t)]
  congr 1

-- @node: embedBinary_fullFiltrationRandomization
set_option maxHeartbeats 800000 in
-- Elaborating the dependent compProd transport requires a larger unification budget.
/-- Boolean-to-`Fin 2` recoding transports the full-history action compProd
identity. -/
lemma embedBinary_fullFiltrationRandomization {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (hA : CausalSmith.Stat.PomdpLatentOverlapMinimax.SequentialIgnorability M) :
    FullFiltrationRandomization (embedBinary M) := by
  constructor
  · intro x
    constructor
    · intro a
      exact (hA.1 x).1 (finActionBool a)
    · simpa [embedBinary, finActionBool, Fin.sum_univ_two, add_comm]
        using (hA.1 x).2
  · intro t
    letI : IsMarkovKernel
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.behaviourKernel M) :=
      ⟨fun x => ⟨by
        change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
        simp only [Measure.finsetSum_apply, Measure.smul_apply,
          Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
        rw [← ENNReal.ofReal_sum_of_nonneg (by
          intro a _
          exact (hA.1 x).1 a)]
        have hs := (hA.1 x).2
        simpa [add_comm] using congrArg ENNReal.ofReal hs⟩⟩
    letI : IsMarkovKernel (actionKernel (embedBinary M)) :=
      ⟨fun x => by
        rw [embedBinary_actionKernel_apply]
        exact Measure.isProbabilityMeasure_map measurable_boolActionFin.aemeasurable⟩
    rw [embedBinary_law_map_actionHistory, embedBinary_law_map_preHistory, hA.2 t]
    symm
    refine CausalSmith.Stat.PomdpLatentOverlapMinimax.map_compProd_of_fiber
      (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histStateView t))
      (Kernel.comap
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.behaviourKernel M)
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.currentObsState t)
          (CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_currentObsState t))
      (Kernel.comap (actionKernel (embedBinary M)) (fun h => h.2.2.1) (by fun_prop))
      (encodeBinaryPreHistory t) (measurable_encodeBinaryPreHistory t)
      boolActionFin measurable_boolActionFin ?_
    intro h
    rw [Kernel.comap_apply, Kernel.comap_apply, embedBinary_actionKernel_apply]
    rfl

-- @node: embedBinary_fullFiltrationPomdp
/-- Boolean-to-`Fin 2` recoding transports the full-history reward-transition
compProd identity. -/
lemma embedBinary_fullFiltrationPomdp {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (hK : CausalSmith.Stat.PomdpLatentOverlapMinimax.PomdpKernelLaw M) :
    FullFiltrationPomdp (embedBinary M) := by
  constructor
  · intro s a
    change IsProbabilityMeasure (M.K s (finActionBool a))
    exact hK.1 s (finActionBool a)
  · intro t
    letI : IsMarkovKernel (CausalSmith.Stat.PomdpLatentOverlapMinimax.kernelOfK M) :=
      ⟨fun sa => hK.1 sa.1 sa.2⟩
    letI : IsMarkovKernel (kernelOfK (embedBinary M)) :=
      ⟨fun sa => hK.1 sa.1 (finActionBool sa.2)⟩
    rw [embedBinary_law_map_nextHistory, embedBinary_law_map_postHistory, hK.2 t]
    symm
    refine CausalSmith.Stat.PomdpLatentOverlapMinimax.map_compProd_of_fiber
      (M.law.map (CausalSmith.Stat.PomdpLatentOverlapMinimax.histView t))
      (Kernel.comap (CausalSmith.Stat.PomdpLatentOverlapMinimax.kernelOfK M)
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.currentStateAction t)
          (CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_currentStateAction t))
      (Kernel.comap (kernelOfK (embedBinary M)) (fun h => (h.1.2.2, h.2)) (by fun_prop))
      (encodeBinaryPostHistory t) (measurable_encodeBinaryPostHistory t)
      id measurable_id ?_
    intro h
    rw [Kernel.comap_apply, Kernel.comap_apply]
    simp only [encodeBinaryPostHistory, encodeBinaryPreHistory,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.currentStateAction]
    change M.K h.1.2 (finActionBool (boolActionFin h.2)) = Measure.map id (M.K h.1.2 h.2)
    rw [finActionBool_boolActionFin, Measure.map_id]

-- @node: embedBinary_policyKernel
lemma embedBinary_policyKernel {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (p : CausalSmith.Stat.PomdpLatentOverlapMinimax.Policy nX)
    (s s' : JointState nX nH) :
    policyKernel (embedBinary M) (fun x a => p x (finActionBool a)) s s' =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M p s s' := by
  simp [policyKernel, CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel,
    embedBinary, finActionBool, Fin.sum_univ_two]
  ring

-- @node: embedBinary_stationaryLaw
lemma embedBinary_stationaryLaw {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (p : CausalSmith.Stat.PomdpLatentOverlapMinimax.Policy nX) :
    stationaryLaw (policyKernel (embedBinary M) (fun x a => p x (finActionBool a))) =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.stationaryLaw
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M p) := by
  have hP : policyKernel (embedBinary M) (fun x a => p x (finActionBool a)) =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M p := by
    funext s s'
    exact embedBinary_policyKernel M p s s'
  rw [hP]
  rfl

-- @node: embedBinary_stationaryOverlap
lemma embedBinary_stationaryOverlap {T nX nH : Nat} {C : ℝ}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.LatentStationaryOverlap C M) :
    StationaryOverlap C (embedBinary M) := by
  refine ⟨h.1, ?_⟩
  intro s
  change stationaryLaw (policyKernel (embedBinary M)
      (fun x a => M.e x (finActionBool a))) s ≤
    C * stationaryLaw (policyKernel (embedBinary M)
      (fun x a => M.b x (finActionBool a))) s
  rw [embedBinary_stationaryLaw M M.e, embedBinary_stationaryLaw M M.b]
  exact h.2 s

-- @node: embedBinary_uniformContraction
lemma embedBinary_uniformContraction {T nX nH : Nat} {t0 : ℝ}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.UniformContraction
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.mixingAlpha t0) M) :
    UniformContraction t0 (embedBinary M) := by
  intro p hp d d' hd hd'
  rcases hp with hp | hp
  · subst p
    rw [show (embedBinary M).b = (fun x a => M.b x (finActionBool a)) from rfl]
    have hP : policyKernel (embedBinary M) (fun x a => M.b x (finActionBool a)) =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M M.b := by
      funext s s'
      exact embedBinary_policyKernel M M.b s s'
    rw [hP]
    exact h M.b (Or.inl rfl) d d' hd hd'
  · subst p
    rw [show (embedBinary M).e = (fun x a => M.e x (finActionBool a)) from rfl]
    have hP : policyKernel (embedBinary M) (fun x a => M.e x (finActionBool a)) =
        CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M M.e := by
      funext s s'
      exact embedBinary_policyKernel M M.e s s'
    rw [hP]
    exact h M.e (Or.inr rfl) d d' hd hd'

-- @node: signedDepthModel_stationaryOverlap
lemma signedDepthModel_stationaryOverlap {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    StationaryOverlap C (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_stationaryOverlap _ hBase.1.latent_stationary_overlap

-- @node: embedBinary_policyOverlap
/-- Binary action recoding preserves the pointwise policy overlap condition. -/
lemma embedBinary_policyOverlap {T nX nH : Nat} {zeta : ℝ}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.PolicyOverlap
      (policyFactor zeta) M) :
    PolicyOverlap zeta (embedBinary M) := by
  constructor
  · intro x
    constructor
    · intro a
      exact (h.1 x).1 (finActionBool a)
    · simpa [embedBinary, finActionBool, Fin.sum_univ_two, add_comm]
        using (h.1 x).2
  · intro x a
    exact h.2 x (finActionBool a)

-- @node: embedBinary_stationaryStart
/-- Binary action recoding leaves the initial state marginal and the behavior
stationary vector unchanged. -/
lemma embedBinary_stationaryStart {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH)
    (h : CausalSmith.Stat.PomdpLatentOverlapMinimax.StationaryStart M) :
    StationaryStart (embedBinary M) := by
  have hP : policyKernel (embedBinary M) (embedBinary M).b =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M M.b := by
    funext s s'
    exact embedBinary_policyKernel M M.b s s'
  constructor
  · rw [hP]
    exact h.1
  · intro s
    rw [hP]
    change (M.law.map
      (fun w => (w.1, fun t => (boolActionFin (w.2 t).1, (w.2 t).2)))).map
      (fun w => stateAt w 0) {s} = _
    rw [Measure.map_map (by unfold stateAt; fun_prop) (by fun_prop)]
    exact h.2 s

-- @node: signedDepthModel_policyOverlap
/-- The signed-depth witness inherits policy overlap after binary recoding. -/
lemma signedDepthModel_policyOverlap {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    PolicyOverlap zeta (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_policyOverlap _ hBase.1.policy_overlap

-- @node: signedDepthModel_stationaryStart
/-- The signed-depth witness starts from its behavior stationary law. -/
lemma signedDepthModel_stationaryStart {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    StationaryStart (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_stationaryStart _ hBase.1.stationary_start

-- @node: signedDepthModel_uniformContraction
lemma signedDepthModel_uniformContraction {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    UniformContraction t0 (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_uniformContraction _ hBase.1.uniform_contraction

-- @node: signedDepthModel_fullFiltrationPomdp
/-- The decoded signed-depth witness obeys the full-history reward-transition
factorization after binary action recoding. -/
lemma signedDepthModel_fullFiltrationPomdp {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    FullFiltrationPomdp
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_fullFiltrationPomdp _ hBase.1.pomdp_kernel

-- @node: signedDepthModel_fullFiltrationRandomization
/-- The decoded signed-depth witness obeys full-history behavior
randomization after binary action recoding. -/
lemma signedDepthModel_fullFiltrationRandomization {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    FullFiltrationRandomization
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  have hBase := CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_membership
    (T := T) (Q := Q) (v := v) ht0 hzeta hC hQ
  exact embedBinary_fullFiltrationRandomization _ hBase.1.sequential_ignorability

-- @node: signedDepthModel_fixedOverlap_of_history_moment
/-- The remaining signed-depth class obligations are precisely the full-history
laws and the pointwise kernel moment envelope. -/
lemma signedDepthModel_fixedOverlap_of_history_moment {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q)
    (hK : FullFiltrationPomdp
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ))
    (hA : FullFiltrationRandomization
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ))
    (hY : RewardMomentEnvelope
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ)) :
    FixedOverlapClass t0 zeta C
      (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  refine ⟨⟨ht0, hzeta, hK, hA, hY,
    signedDepthModel_policyOverlap v ht0 hzeta hC hQ,
    signedDepthModel_uniformContraction v ht0 hzeta hC hQ,
    signedDepthModel_stationaryStart v ht0 hzeta hC hQ⟩,
    signedDepthModel_stationaryOverlap v ht0 hzeta hC hQ⟩

-- @node: embedBinary_targetValue
lemma embedBinary_targetValue {T nX nH : Nat}
    (M : CausalSmith.Stat.PomdpLatentOverlapMinimax.RawPomdpExperiment T nX nH) :
    targetValue (embedBinary M) =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.targetValue M := by
  unfold targetValue CausalSmith.Stat.PomdpLatentOverlapMinimax.targetValue
  apply Finset.sum_congr rfl
  intro s _
  rw [show stationaryLaw (policyKernel (embedBinary M) (embedBinary M).e) s =
      CausalSmith.Stat.PomdpLatentOverlapMinimax.stationaryLaw
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.policyKernel M M.e) s from by
        congr 1
        funext u v
        exact embedBinary_policyKernel M M.e u v]
  congr 1
  simp [rewardRegression, CausalSmith.Stat.PomdpLatentOverlapMinimax.rewardRegression,
    embedBinary, finActionBool, Fin.sum_univ_two]
  ring

-- @node: signedDepthModel_obsLaw
/-- Encoding Boolean actions as `Fin 2` pushes forward the earlier signed-depth
observed law. -/
lemma signedDepthModel_obsLaw {T Q : Nat} {t0 zeta C : ℝ} (v : Bool)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) (hQ : 1 ≤ Q) :
    obsLaw (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) =
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
        T t0 zeta C Q v).map
        (fun w t => ((w t).1, boolActionFin (w t).2.1, (w t).2.2)) := by
  unfold obsLaw signedDepthModel embedBinary
    CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
    CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
    CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
  rw [Measure.map_map (by unfold obsProj currentState actionAt rewardAt; fun_prop)
    (by fun_prop)]
  rw [Measure.map_map (by fun_prop)
    CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj]
  congr 1

-- @node: signedDepthModel_observedKL
/-- The observed KL certificate survives the binary-action encoding. -/
lemma signedDepthModel_observedKL {t0 zeta C : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 < C) :
    ∃ B0 : ℝ, 1 ≤ B0 ∧ ∀ (T Q : Nat) (hQ : 1 ≤ Q),
      InformationTheory.klDiv
        (obsLaw (signedDepthModel T Q t0 zeta C true ht0 hzeta hC hQ))
        (obsLaw (signedDepthModel T Q t0 zeta C false ht0 hzeta hC hQ)) ≤
      ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ))) := by
  obtain ⟨K0, hK0, hpath⟩ :=
    CausalSmith.Stat.PomdpLatentOverlapMinimax.observed_path_kl ht0
  have hseq : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      CausalSmith.Stat.PomdpLatentOverlapMinimax.SequentialIgnorability
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
          T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T' Q' hQ' v
    exact CausalSmith.Stat.PomdpLatentOverlapMinimax.embed_sequentialIgnorability _
  have hstat : ∀ (T' Q' : Nat) (hQ' : 1 ≤ Q') (v : Bool),
      CausalSmith.Stat.PomdpLatentOverlapMinimax.StationaryStart
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamily
          T' t0 zeta C Q' v ht0 hzeta hC hQ') := by
    intro T' Q' hQ' v
    exact CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_stationaryStart
      ht0 hzeta hC.le hQ'
  obtain ⟨B, hB, hall⟩ := hpath zeta C hzeta hC hseq hstat
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro T Q hQ
  rw [signedDepthModel_obsLaw true ht0 hzeta hC hQ,
    signedDepthModel_obsLaw false ht0 hzeta hC hQ]
  have hmap : InformationTheory.klDiv
      ((CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
        T t0 zeta C Q true).map
        (fun w t => ((w t).1, boolActionFin (w t).2.1, (w t).2.2)))
      ((CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
        T t0 zeta C Q false).map
        (fun w t => ((w t).1, boolActionFin (w t).2.1, (w t).2.2))) ≤
      InformationTheory.klDiv
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
          T t0 zeta C Q true)
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
          T t0 zeta C Q false) := by
    letI : IsProbabilityMeasure
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
          T t0 zeta C Q true) := by
      unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
        CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
      exact Measure.isProbabilityMeasure_map
        CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
    letI : IsProbabilityMeasure
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
          T t0 zeta C Q false) := by
      unfold CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthObsLaw
        CausalSmith.Stat.PomdpLatentOverlapMinimax.obsLaw
      exact Measure.isProbabilityMeasure_map
        CausalSmith.Stat.PomdpLatentOverlapMinimax.measurable_obsProj.aemeasurable
    exact InformationTheory.klDiv_map_le _ _ (by fun_prop)
  have hscale : B * (T : ℝ) * mixingAlpha t0 ^ (2 * Q) *
      policyFactor zeta ^ (-(Q : ℤ)) ≤
      max 1 B * (T : ℝ) * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)) := by
    unfold policyFactor mixingAlpha
    gcongr
    exact le_max_right _ _
  exact hmap.trans ((hall T Q hQ).1.trans (ENNReal.ofReal_le_ofReal hscale))

/-- The witness at radius two supplied by `signed_depth_kl`. -/
@[no_expose]
def SignedDepthConstantAtTwo (t0 zeta B0 : ℝ) : Prop :=
  1 ≤ B0 ∧ ∀ (T Q : Nat) (hQ : 1 ≤ Q) (ht0 : 0 < t0) (hzeta : 0 < zeta),
    let Mp := signedDepthModel T Q t0 zeta 2 true ht0 hzeta (by norm_num) hQ
    let Mm := signedDepthModel T Q t0 zeta 2 false ht0 hzeta (by norm_num) hQ
    FixedOverlapClass t0 zeta 2 Mp ∧
    FixedOverlapClass t0 zeta 2 Mm ∧
    targetValue Mp = separationRadius t0 2 Q ht0 (by norm_num) hQ ∧
    targetValue Mm = -separationRadius t0 2 Q ht0 (by norm_num) hQ ∧
    Mp.law = generatedPathLaw Mp ∧ Mm.law = generatedPathLaw Mm ∧
    InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
      ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)))

-- @node: signedDepthConstantAtTwo_spec
/-- The radius-two witness predicate exposes its bound and model certificates. -/
lemma signedDepthConstantAtTwo_spec {t0 zeta B0 : ℝ}
    (h : SignedDepthConstantAtTwo t0 zeta B0) :
    1 ≤ B0 ∧ ∀ (T Q : Nat) (hQ : 1 ≤ Q) (ht0 : 0 < t0) (hzeta : 0 < zeta),
      let Mp := signedDepthModel T Q t0 zeta 2 true ht0 hzeta (by norm_num) hQ
      let Mm := signedDepthModel T Q t0 zeta 2 false ht0 hzeta (by norm_num) hQ
      FixedOverlapClass t0 zeta 2 Mp ∧
      FixedOverlapClass t0 zeta 2 Mm ∧
      targetValue Mp = separationRadius t0 2 Q ht0 (by norm_num) hQ ∧
      targetValue Mm = -separationRadius t0 2 Q ht0 (by norm_num) hQ ∧
      Mp.law = generatedPathLaw Mp ∧ Mm.law = generatedPathLaw Mm ∧
      InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
        ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ))) := h

-- @node: rewardMomentEnvelope_of_ae_bound
/-- An almost-sure unit reward bound on every probability kernel row gives both
required moment bounds. -/
lemma rewardMomentEnvelope_of_ae_bound {T nX nH k : Nat}
    (M : PomdpModel T nX nH k)
    (hprob : ∀ s a, IsProbabilityMeasure (M.K s a))
    (hbound : ∀ s a, ∀ᵐ q ∂(M.K s a), |q.1| ≤ (1 : ℝ)) :
    RewardMomentEnvelope M := by
  intro s a
  letI : IsProbabilityMeasure (M.K s a) := hprob s a
  have hmeas : Measurable (fun q : ℝ × JointState nX nH => q.1) := by fun_prop
  have hi : Integrable (fun q : ℝ × JointState nX nH => q.1) (M.K s a) :=
    Integrable.of_bound hmeas.aestronglyMeasurable 1 (by
      filter_upwards [hbound s a] with q hq
      simpa using hq)
  have hi2 : Integrable (fun q : ℝ × JointState nX nH => q.1 ^ 2) (M.K s a) :=
    Integrable.of_bound (by fun_prop : AEStronglyMeasurable
      (fun q : ℝ × JointState nX nH => q.1 ^ 2) (M.K s a)) 1 (by
      filter_upwards [hbound s a] with q hq
      have hsq : q.1 ^ 2 ≤ (1 : ℝ) := by
        rcases abs_le.mp hq with ⟨hl, hu⟩
        nlinarith
      simpa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q.1)] using hsq)
  refine ⟨hi, hi2, ?_, ?_⟩
  · have hlow : ∀ᵐ q ∂(M.K s a), (-1 : ℝ) ≤ q.1 := by
      filter_upwards [hbound s a] with q hq
      exact (abs_le.mp hq).1
    have hupp : ∀ᵐ q ∂(M.K s a), q.1 ≤ (1 : ℝ) := by
      filter_upwards [hbound s a] with q hq
      exact (abs_le.mp hq).2
    exact abs_le.mpr ⟨by simpa using integral_mono_ae (integrable_const _) hi hlow,
      by simpa using integral_mono_ae hi (integrable_const _) hupp⟩
  · have hupp : ∀ᵐ q ∂(M.K s a), q.1 ^ 2 ≤ (1 : ℝ) := by
      filter_upwards [hbound s a] with q hq
      rcases abs_le.mp hq with ⟨hl, hu⟩
      nlinarith
    simpa using integral_mono_ae hi2 (integrable_const _) hupp

-- @node: finiteReward_kernel_ae_bound
/-- A finite reward model whose decoded symbols lie in the unit interval has
unit-bounded rewards in every decoded kernel row. -/
lemma finiteReward_kernel_ae_bound {T nX nH nR : Nat}
    (F : CausalSmith.Stat.PomdpLatentOverlapMinimax.FiniteRewardModel T nX nH nR)
    (s : JointState nX nH) (a : Fin 2) :
    ∀ᵐ q ∂(embedBinary (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed F)).K s a,
      |q.1| ≤ (1 : ℝ) := by
  letI : IsProbabilityMeasure
      ((embedBinary (CausalSmith.Stat.PomdpLatentOverlapMinimax.embed F)).K s a) := by
    change IsProbabilityMeasure
      ((F.kernel s (finActionBool a)).map
        (CausalSmith.Stat.PomdpLatentOverlapMinimax.decodeFiniteStep F.rew)).toMeasure
    infer_instance
  let S : Set (ℝ × JointState nX nH) := {q | |q.1| ≤ (1 : ℝ)}
  have hS : MeasurableSet S := by
    exact measurableSet_le (by fun_prop) measurable_const
  apply (mem_ae_iff_prob_eq_one hS).2
  change ((F.kernel s (finActionBool a)).map
    (CausalSmith.Stat.PomdpLatentOverlapMinimax.decodeFiniteStep F.rew)).toMeasure S = 1
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rw [Measure.map_apply (measurable_of_finite _) hS]
  have hpre :
      CausalSmith.Stat.PomdpLatentOverlapMinimax.decodeFiniteStep F.rew ⁻¹' S =
        Set.univ := by
    ext q
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact abs_le.mpr (F.rew_mem q.1)
  rw [hpre, measure_univ]

-- @node: signedDepthModel_rewardMomentEnvelope
/-- The finite signed-depth rewards are decoded from values in `[-1,1]`. -/
lemma signedDepthModel_rewardMomentEnvelope {T Q : Nat} {t0 zeta C : ℝ}
    (v : Bool) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) (hQ : 1 ≤ Q) :
    RewardMomentEnvelope (signedDepthModel T Q t0 zeta C v ht0 hzeta hC hQ) := by
  apply rewardMomentEnvelope_of_ae_bound
  · intro s a
    change IsProbabilityMeasure
      ((CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFinite
        T t0 zeta C Q v).kernel s (finActionBool a) |>.map
          (CausalSmith.Stat.PomdpLatentOverlapMinimax.decodeFiniteStep
            (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFinite
              T t0 zeta C Q v).rew)).toMeasure
    infer_instance
  · intro s a
    exact finiteReward_kernel_ae_bound
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFinite T t0 zeta C Q v) s a

-- @node: lem:signed-depth-kl
/-- One constant independent of depth and horizon controls the observed KL divergence;
constructed signed-depth alternatives satisfy the fixed-overlap subclass, the path
factorization, and have opposite target values. -/
lemma signed_depth_kl {t0 zeta C : ℝ} (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 < C) :
    ∃ B0 : ℝ, 1 ≤ B0 ∧
      ∀ (T Q : Nat) (hQ : 1 ≤ Q),
      let Mp := signedDepthModel T Q t0 zeta C true ht0 hzeta hC hQ
      let Mm := signedDepthModel T Q t0 zeta C false ht0 hzeta hC hQ
      FixedOverlapClass t0 zeta C Mp ∧
      FixedOverlapClass t0 zeta C Mm ∧
      targetValue Mp = separationRadius t0 C Q ht0 hC hQ ∧
      targetValue Mm = -separationRadius t0 C Q ht0 hC hQ ∧
      Mp.law = generatedPathLaw Mp ∧ Mm.law = generatedPathLaw Mm ∧
      InformationTheory.klDiv (obsLaw Mp) (obsLaw Mm) ≤
      ENNReal.ofReal (B0 * T * mixingAlpha t0 ^ (2 * Q) *
          policyFactor zeta ^ (-(Q : ℤ))) := by
  obtain ⟨B0, hB0, hKL⟩ := signedDepthModel_observedKL ht0 hzeta hC
  refine ⟨B0, hB0, ?_⟩
  intro T Q hQ
  dsimp
  have hMp : FixedOverlapClass t0 zeta C
      (signedDepthModel T Q t0 zeta C true ht0 hzeta hC hQ) := by
    apply signedDepthModel_fixedOverlap_of_history_moment true ht0 hzeta hC hQ
    · exact signedDepthModel_fullFiltrationPomdp true ht0 hzeta hC hQ
    · exact signedDepthModel_fullFiltrationRandomization true ht0 hzeta hC hQ
    · exact signedDepthModel_rewardMomentEnvelope true ht0 hzeta hC hQ
  have hMm : FixedOverlapClass t0 zeta C
      (signedDepthModel T Q t0 zeta C false ht0 hzeta hC hQ) := by
    apply signedDepthModel_fixedOverlap_of_history_moment false ht0 hzeta hC hQ
    · exact signedDepthModel_fullFiltrationPomdp false ht0 hzeta hC hQ
    · exact signedDepthModel_fullFiltrationRandomization false ht0 hzeta hC hQ
    · exact signedDepthModel_rewardMomentEnvelope false ht0 hzeta hC hQ
  refine ⟨hMp, hMm, ?_, ?_, ?_, ?_, hKL T Q hQ⟩
  · rw [signedDepthModel, embedBinary_targetValue]
    change CausalSmith.Stat.PomdpLatentOverlapMinimax.targetValue
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamilyAtLeastOne
        T t0 zeta C Q true ht0 hzeta hC.le hQ) = _
    rw [CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_targetValue
      ht0 hzeta hC.le hQ]
    simp [separationRadius, rewardAmplitude, signBias, terminalMass,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.signedValue,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.c0,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.epsC,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.depthMass,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.mixingAlpha, mixingAlpha]
  · rw [signedDepthModel, embedBinary_targetValue]
    change CausalSmith.Stat.PomdpLatentOverlapMinimax.targetValue
      (CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepthFamilyAtLeastOne
        T t0 zeta C Q false ht0 hzeta hC.le hQ) = _
    rw [CausalSmith.Stat.PomdpLatentOverlapMinimax.signedDepth_targetValue
      ht0 hzeta hC.le hQ]
    simp [separationRadius, rewardAmplitude, signBias, terminalMass,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.signedValue,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.c0,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.epsC,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.depthMass,
      CausalSmith.Stat.PomdpLatentOverlapMinimax.mixingAlpha, mixingAlpha]
  · exact (full_history_factorization _ hMp.1.pomdp hMp.1.randomization
      hMp.1.moment hMp.1.overlap hMp.1.start).1
  · exact (full_history_factorization _ hMm.1.pomdp hMm.1.randomization
      hMm.1.moment hMm.1.overlap hMm.1.start).1

-- @node: signedDepthConstantAtTwo_exists
/-- The signed-depth KL lemma supplies one radius-two witness for every positive
mixing time and overlap exponent. -/
lemma signedDepthConstantAtTwo_exists {t0 zeta : ℝ}
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ B0 : ℝ, SignedDepthConstantAtTwo t0 zeta B0 := by
  obtain ⟨B0, hB0, h⟩ := signed_depth_kl ht0 hzeta (C := 2) (by norm_num)
  refine ⟨B0, hB0, ?_⟩
  intro T Q hQ ht0' hzeta'
  simpa only using h T Q hQ

end CausalSmith.Stat.PomdpStateauditMinimax
