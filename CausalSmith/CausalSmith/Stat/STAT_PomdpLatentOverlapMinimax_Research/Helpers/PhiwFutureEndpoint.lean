module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwFutureIteration
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.StationaryRewardSupport

set_option linter.style.longLine false

/-! # Terminal endpoint of future PHIW peeling -/

public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- The trajectory reward bound transported to the kernel-output history marginal. [the h Y condition](hyp:hY). [the stated conclusion](goal). -/
lemma boundedReward_histNextPair_ae {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hY : BoundedReward M) (t : Fin T) :
    ∀ᵐ z ∂(M.law.map (histNextPair t)), |z.2.1| ≤ 1 := by
  have hs : MeasurableSet
      {z : ActionHistoryView T nX nH t × Step nX nH | |z.2.1| ≤ 1} :=
    measurableSet_le (continuous_abs.measurable.comp
      (measurable_fst.comp measurable_snd)) measurable_const
  apply (MeasureTheory.ae_map_iff (measurable_histNextPair t).aemeasurable hs).2
  simpa [histNextPair] using boundedReward_law_ae hY t

/-- The terminal reward and terminal conditional-reward integrands are integrable whenever
the past carrier is integrable. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the h Gm condition](hyp:hGm); and [the h Gi condition](hyp:hGi). [the stated conclusion](goal). -/
lemma integrable_terminalPeel_obligations
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (lo : Nat) (t : Fin T) (G : StateHistoryView T nX nH t → ℝ)
    (hGm : Measurable G) (hGi : Integrable G (M.law.map (histStateView t))) :
    Integrable (fun z : ActionHistoryView T nX nH t × Step nX nH ↦
      (G z.1.1 * stateHistoryRatioBlock M lo t z.1.1) *
        ratio M.b M.e (currentObsState t z.1.1) z.1.2 * z.2.1)
      (M.law.map (histNextPair t)) ∧
    Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
      (G z.1 * stateHistoryRatioBlock M lo t z.1) *
        ∫ y, y.1 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair t)) := by
  have hone : ∀ s : JointState nX nH, |(1 : ℝ)| ≤ 1 := fun _ ↦ by norm_num
  have hbase := integrable_targetPeel_obligations hign hoverlap hL hK lo t
    G hGm hGi (fun _ ↦ (1 : ℝ)) hone
  constructor
  · have hr := hbase.1.bdd_mul
      (continuous_fst.measurable.comp measurable_snd
        |>.aestronglyMeasurable)
      (by
        filter_upwards [boundedReward_histNextPair_ae hY t] with z hz
        change |z.2.1| ≤ 1
        exact hz)
    convert hr using 1
    funext z
    simp only [Function.comp_apply, mul_one]
    ring
  · let J : StateHistoryView T nX nH t × Bool → ℝ :=
      fun z ↦ ∫ y, y.1 ∂(M.K z.1.2 z.2)
    have hJm : Measurable J := by
      let J0 : JointState nX nH × Bool → ℝ := fun z ↦ ∫ y, y.1 ∂(M.K z.1 z.2)
      exact (measurable_of_finite J0).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hJb : ∀ᵐ z ∂(M.law.map (histActionPair t)), |J z| ≤ 1 := by
      letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa ↦ hK.1 sa.1 sa.2⟩
      have hpair := boundedReward_histNextPair_ae hY t
      rw [hK.2 t] at hpair
      have hsections := MeasureTheory.Measure.ae_ae_of_ae_compProd hpair
      filter_upwards [hsections] with z hz
      letI : IsProbabilityMeasure (M.K z.1.2 z.2) := hK.1 z.1.2 z.2
      change ∀ᵐ y ∂(M.K z.1.2 z.2), |y.1| ≤ 1 at hz
      have hz' : ∀ᵐ y ∂(M.K z.1.2 z.2), ‖y.1‖ ≤ (1 : ℝ) := by
        simpa only [Real.norm_eq_abs] using hz
      simpa only [J, Real.norm_eq_abs, mul_one, probReal_univ] using
        (norm_integral_le_of_norm_le_const (μ := M.K z.1.2 z.2)
          (f := fun y : Step nX nH ↦ y.1) (C := (1 : ℝ)) hz')
    have hcarrier : Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
        G z.1 * stateHistoryRatioBlock M lo t z.1)
        (M.law.map (histActionPair t)) := by
      have heq : (fun z : StateHistoryView T nX nH t × Bool ↦
          G z.1 * stateHistoryRatioBlock M lo t z.1 *
            ∫ _y, (1 : ℝ) ∂(M.K z.1.2 z.2)) =
          fun z ↦ G z.1 * stateHistoryRatioBlock M lo t z.1 := by
        funext z
        letI : IsProbabilityMeasure (M.K z.1.2 z.2) := hK.1 z.1.2 z.2
        simp
      rw [heq] at hbase
      exact hbase.2
    have hb := hcarrier.bdd_mul hJm.aestronglyMeasurable (by
      filter_upwards [hJb] with z hz
      simpa only [Real.norm_eq_abs] using hz)
    simpa [J, mul_assoc, mul_comm] using hb

/-- A future mature PHIW score peels to the contracted future function when multiplied by
an earlier mature score.  The lag is represented as `gap + k + 1`. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk); and [the hhorizon condition](hyp:hhorizon). [the stated conclusion](goal). -/
lemma integral_phiwScore_mul_eq_futureFunction_full
    {T nX nH k gap : Nat} {L : ℝ} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (t : Fin T) (htk : k ≤ t.val) (hhorizon : t.val + 1 + gap + k < T) :
    let r := nextEpoch t (by omega)
    let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
    let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    ∫ tau, phiwScore k M.b M.e (obsProj tau) t *
        phiwScore k M.b M.e (obsProj tau) u ∂M.law =
      ∫ tau, phiwScore k M.b M.e (obsProj tau) t *
        phiwFutureFunction M gap k (nextState t tau) ∂M.law := by
  dsimp only
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  let G := phiwPastCarrier (k := k) M t (by omega)
  let Gq := iterLiftStateHistoryFunction r G gap
    (by dsimp [r, nextEpoch]; omega)
  let Gu := iterLiftStateHistoryFunction q Gq k
    (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have hGi : Integrable G (M.law.map (histStateView r)) :=
    integrable_phiwPastCarrier hign hoverlap hL hY t (by omega) htk
  have hGqi : Integrable Gq (M.law.map (histStateView q)) :=
    integrable_iterLiftStateHistoryFunction hign hK r G
      (measurable_phiwPastCarrier M t (by omega)) hGi gap
      (by dsimp [r, nextEpoch]; omega)
  have hGui : Integrable Gu (M.law.map (histStateView u)) :=
    integrable_iterLiftStateHistoryFunction hign hK q Gq
      (measurable_iterLiftStateHistoryFunction r G
        (measurable_phiwPastCarrier M t (by omega)) gap
          (by dsimp [r, nextEpoch]; omega)) hGqi k
      (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have hterminal := integrable_terminalPeel_obligations hign hoverlap hL hK hY
    q.val u Gu
    (measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G
        (measurable_phiwPastCarrier M t (by omega)) gap
          (by dsimp [r, nextEpoch]; omega)) k
      (by dsimp [q, r, nextEpoch, epochAdd]; omega)) hGui
  have hp := integral_futureScore_peeling_of_integrable hign hoverlap hL hK hY
    r G (measurable_phiwPastCarrier M t (by omega)) hGi gap k
    (by dsimp [r, nextEpoch]; omega) hterminal.1 hterminal.2
  have huK : k ≤ u.val := by dsimp [u, q, r, epochAdd, nextEpoch]; omega
  have hqval : u.val - k = q.val := by dsimp [u, epochAdd]; omega
  have hleftMeas : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
      (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
        ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1) := by
    have hGuM := measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G
        (measurable_phiwPastCarrier M t (by omega)) gap
          (by dsimp [r, nextEpoch]; omega)) k
        (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    have hfstfst : Measurable
        (fun z : ActionHistoryView T nX nH u × Step nX nH ↦ z.1.1) :=
      measurable_fst.comp measurable_fst
    have hratio : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
        ratio M.b M.e (currentObsState u z.1.1) z.1.2) :=
      (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
        (((measurable_currentObsState u).comp hfstfst).prodMk
          (measurable_snd.comp measurable_fst))
    exact (((hGuM.comp hfstfst).mul
      ((measurable_stateHistoryRatioBlock M q.val u).comp hfstfst)).mul hratio).mul
      (measurable_fst.comp measurable_snd)
  have hrightMeas : Measurable (fun h : StateHistoryView T nX nH r ↦
      G h * phiwFutureFunction M gap k h.2) := by
    exact (measurable_phiwPastCarrier M t (by omega)).mul
      ((measurable_of_finite (phiwFutureFunction M gap k)).comp measurable_snd)
  calc
    (∫ tau, phiwScore k M.b M.e (obsProj tau) t *
        phiwScore k M.b M.e (obsProj tau) u ∂M.law) =
      ∫ tau, (Gu (histStateView u tau) *
          stateHistoryRatioBlock M q.val u (histStateView u tau)) *
          ratio M.b M.e (currentObsState u (histStateView u tau)) (actionAt u tau) *
          rewardAt u tau ∂M.law := by
        apply integral_congr_ae
        filter_upwards with tau
        have hGt : G (histStateView r tau) =
            phiwScore k M.b M.e (obsProj tau) t :=
          phiwPastCarrier_histStateView M t (by omega) htk tau
        have hGu : Gu (histStateView u tau) = G (histStateView r tau) := by
          dsimp [Gu, Gq]
          rw [iterLiftStateHistoryFunction_histStateView]
          rw [iterLiftStateHistoryFunction_histStateView]
        rw [hGu, hGt]
        have hblock : actionHistoryRatioBlock M q.val u (histActionPair u tau) =
            ∏ j ∈ phiwWindow k u,
              ratio M.b M.e (curState j tau).1 (actionAt j tau) := by
          rw [actionHistoryRatioBlock_histActionPair M q.val u (by
            dsimp [u, q, epochAdd]
            omega) tau]
          rw [phiwWindow_eq_interval u huK]
          rw [hqval]
        have hscoreU : phiwScore k M.b M.e (obsProj tau) u =
            rewardAt u tau * actionHistoryRatioBlock M q.val u
              (histActionPair u tau) := by
          rw [phiwScore_obsProj, hblock]
        rw [hscoreU]
        unfold actionHistoryRatioBlock
        simp only [currentObsState, histActionPair, histStateView, actionAt]
        ring
    _ = ∫ z, (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
          ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1
          ∂(M.law.map (histNextPair u)) := by
      rw [integral_map (measurable_histNextPair u).aemeasurable
        hleftMeas.aestronglyMeasurable]
      rfl
    _ = ∫ h, G h * phiwFutureFunction M gap k h.2
          ∂(M.law.map (histStateView r)) := hp
    _ = ∫ tau, G (histStateView r tau) *
          phiwFutureFunction M gap k (histStateView r tau).2 ∂M.law := by
      rw [integral_map (measurable_histStateView r).aemeasurable
        hrightMeas.aestronglyMeasurable]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with tau
      dsimp [G, r]
      rw [phiwPastCarrier_histStateView M t (by omega) htk tau]
      rfl

/-- Observed-law form of the mature-score cross-moment peeling identity. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the htk condition](hyp:htk); and [the hhorizon condition](hyp:hhorizon). [the stated conclusion](goal). -/
lemma integral_phiwScore_mul_eq_futureFunction
    {T nX nH k gap : Nat} {L : ℝ} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (t : Fin T) (htk : k ≤ t.val) (hhorizon : t.val + 1 + gap + k < T) :
    let r := nextEpoch t (by omega)
    let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
    let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    ∫ w, phiwScore k M.b M.e w t * phiwScore k M.b M.e w u ∂obsLaw M =
      ∫ tau, phiwScore k M.b M.e (obsProj tau) t *
        phiwFutureFunction M gap k (nextState t tau) ∂M.law := by
  dsimp only
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have hm : Measurable (fun w : ObsView T nX ↦
      phiwScore k M.b M.e w t * phiwScore k M.b M.e w u) :=
    (phiwScore_measurable M.b M.e t).mul (phiwScore_measurable M.b M.e u)
  unfold obsLaw
  rw [integral_map (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
    hm.aestronglyMeasurable]
  exact integral_phiwScore_mul_eq_futureFunction_full
    hign hoverlap hL hK hY t htk hhorizon

/-- The unweighted companion to the cross-moment identity: a future mature score has the
same mean as its behavior-gap/target-window conditional reward function at the next state. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the hhorizon condition](hyp:hhorizon). [the stated conclusion](goal). -/
lemma integral_phiwScore_eq_futureFunction_full
    {T nX nH k gap : Nat} {L : ℝ} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (t : Fin T) (hhorizon : t.val + 1 + gap + k < T) :
    let r := nextEpoch t (by omega)
    let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
    let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    ∫ tau, phiwScore k M.b M.e (obsProj tau) u ∂M.law =
      ∫ tau, phiwFutureFunction M gap k (nextState t tau) ∂M.law := by
  dsimp only
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  let G : StateHistoryView T nX nH r → ℝ := fun _ ↦ 1
  let Gq := iterLiftStateHistoryFunction r G gap
    (by dsimp [r, nextEpoch]; omega)
  let Gu := iterLiftStateHistoryFunction q Gq k
    (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have hGi : Integrable G (M.law.map (histStateView r)) := integrable_const 1
  have hGqi : Integrable Gq (M.law.map (histStateView q)) :=
    integrable_iterLiftStateHistoryFunction hign hK r G measurable_const hGi gap
      (by dsimp [r, nextEpoch]; omega)
  have hGui : Integrable Gu (M.law.map (histStateView u)) :=
    integrable_iterLiftStateHistoryFunction hign hK q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap
        (by dsimp [r, nextEpoch]; omega)) hGqi k
      (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have hterminal := integrable_terminalPeel_obligations hign hoverlap hL hK hY
    q.val u Gu
    (measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap
        (by dsimp [r, nextEpoch]; omega)) k
      (by dsimp [q, r, nextEpoch, epochAdd]; omega)) hGui
  have hp := integral_futureScore_peeling_of_integrable hign hoverlap hL hK hY
    r G measurable_const hGi gap k (by dsimp [r, nextEpoch]; omega)
    hterminal.1 hterminal.2
  have huK : k ≤ u.val := by dsimp [u, q, r, epochAdd, nextEpoch]; omega
  have hqval : u.val - k = q.val := by dsimp [u, epochAdd]; omega
  have hleftMeas : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
      (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
        ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1) := by
    have hGuM := measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap
        (by dsimp [r, nextEpoch]; omega)) k
      (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    have hfstfst : Measurable
        (fun z : ActionHistoryView T nX nH u × Step nX nH ↦ z.1.1) :=
      measurable_fst.comp measurable_fst
    have hratio : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
        ratio M.b M.e (currentObsState u z.1.1) z.1.2) :=
      (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
        (((measurable_currentObsState u).comp hfstfst).prodMk
          (measurable_snd.comp measurable_fst))
    exact (((hGuM.comp hfstfst).mul
      ((measurable_stateHistoryRatioBlock M q.val u).comp hfstfst)).mul hratio).mul
      (measurable_fst.comp measurable_snd)
  have hrightMeas : Measurable (fun h : StateHistoryView T nX nH r ↦
      G h * phiwFutureFunction M gap k h.2) := by
    exact measurable_const.mul
      ((measurable_of_finite (phiwFutureFunction M gap k)).comp measurable_snd)
  calc
    (∫ tau, phiwScore k M.b M.e (obsProj tau) u ∂M.law) =
      ∫ tau, (Gu (histStateView u tau) *
          stateHistoryRatioBlock M q.val u (histStateView u tau)) *
          ratio M.b M.e (currentObsState u (histStateView u tau)) (actionAt u tau) *
          rewardAt u tau ∂M.law := by
        apply integral_congr_ae
        filter_upwards with tau
        have hGu : Gu (histStateView u tau) = 1 := by
          dsimp [Gu, Gq]
          rw [iterLiftStateHistoryFunction_histStateView]
          rw [iterLiftStateHistoryFunction_histStateView]
        have hblock : actionHistoryRatioBlock M q.val u (histActionPair u tau) =
            ∏ j ∈ phiwWindow k u,
              ratio M.b M.e (curState j tau).1 (actionAt j tau) := by
          rw [actionHistoryRatioBlock_histActionPair M q.val u (by
            dsimp [u, q, epochAdd]
            omega) tau]
          rw [phiwWindow_eq_interval u huK]
          rw [hqval]
        have hscoreU : phiwScore k M.b M.e (obsProj tau) u =
            rewardAt u tau * actionHistoryRatioBlock M q.val u
              (histActionPair u tau) := by
          rw [phiwScore_obsProj, hblock]
        rw [hscoreU, hGu]
        unfold actionHistoryRatioBlock
        simp only [currentObsState, histActionPair, histStateView, actionAt, one_mul]
        ring
    _ = ∫ z, (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
          ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1
          ∂(M.law.map (histNextPair u)) := by
      rw [integral_map (measurable_histNextPair u).aemeasurable
        hleftMeas.aestronglyMeasurable]
      rfl
    _ = ∫ h, G h * phiwFutureFunction M gap k h.2
          ∂(M.law.map (histStateView r)) := hp
    _ = ∫ tau, G (histStateView r tau) *
          phiwFutureFunction M gap k (histStateView r tau).2 ∂M.law := by
      rw [integral_map (measurable_histStateView r).aemeasurable
        hrightMeas.aestronglyMeasurable]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with tau
      dsimp [G, r]
      simp only [one_mul]
      simp only [histStateView, nextEpoch, curState, nextState]
      congr 2

/-- Observed-law version of the unweighted future-score identity. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the hhorizon condition](hyp:hhorizon). [the stated conclusion](goal). -/
lemma integral_phiwScore_eq_futureFunction
    {T nX nH k gap : Nat} {L : ℝ} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (t : Fin T) (hhorizon : t.val + 1 + gap + k < T) :
    let r := nextEpoch t (by omega)
    let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
    let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
    ∫ w, phiwScore k M.b M.e w u ∂obsLaw M =
      ∫ tau, phiwFutureFunction M gap k (nextState t tau) ∂M.law := by
  dsimp only
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let u := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  unfold obsLaw
  rw [integral_map (measurable_obsProj (T := T) (nX := nX) (nH := nH)).aemeasurable
    (phiwScore_measurable M.b M.e u).aestronglyMeasurable]
  exact integral_phiwScore_eq_futureFunction_full hign hoverlap hL hK hY t hhorizon

/-- A mature score peels from the state at the beginning of its ratio window. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the hhorizon condition](hyp:hhorizon). [the stated conclusion](goal). -/
lemma integral_phiwScore_eq_futureFunction_from_state
    {T nX nH k gap : Nat} {L : ℝ} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (r : Fin T) (hhorizon : r.val + gap + k < T) :
    let q := epochAdd r gap (by omega)
    let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
    ∫ w, phiwScore k M.b M.e w u ∂obsLaw M =
      ∫ tau, phiwFutureFunction M gap k (curState r tau) ∂M.law := by
  dsimp only
  let q := epochAdd r gap (by omega)
  let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
  let G : StateHistoryView T nX nH r → ℝ := fun _ ↦ 1
  let Gq := iterLiftStateHistoryFunction r G gap (by omega)
  let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
  have hGi : Integrable G (M.law.map (histStateView r)) := integrable_const 1
  have hGqi : Integrable Gq (M.law.map (histStateView q)) :=
    integrable_iterLiftStateHistoryFunction hign hK r G measurable_const hGi gap (by omega)
  have hGui : Integrable Gu (M.law.map (histStateView u)) :=
    integrable_iterLiftStateHistoryFunction hign hK q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap (by omega)) hGqi k
      (by dsimp [q, epochAdd]; omega)
  have hterminal := integrable_terminalPeel_obligations hign hoverlap hL hK hY q.val u Gu
    (measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap (by omega)) k
      (by dsimp [q, epochAdd]; omega)) hGui
  have hp := integral_futureScore_peeling_of_integrable hign hoverlap hL hK hY
    r G measurable_const hGi gap k (by omega) hterminal.1 hterminal.2
  have huK : k ≤ u.val := by dsimp [u, q, epochAdd]; omega
  have hqval : u.val - k = q.val := by dsimp [u, epochAdd]; omega
  have hleftMeas : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
      (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
        ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1) := by
    have hGuM := measurable_iterLiftStateHistoryFunction q Gq
      (measurable_iterLiftStateHistoryFunction r G measurable_const gap (by omega)) k
      (by dsimp [q, epochAdd]; omega)
    have hfstfst : Measurable
        (fun z : ActionHistoryView T nX nH u × Step nX nH ↦ z.1.1) :=
      measurable_fst.comp measurable_fst
    have hratio : Measurable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
        ratio M.b M.e (currentObsState u z.1.1) z.1.2) :=
      (measurable_of_finite (fun xa : Fin nX × Bool ↦ ratio M.b M.e xa.1 xa.2)).comp
        (((measurable_currentObsState u).comp hfstfst).prodMk
          (measurable_snd.comp measurable_fst))
    exact (((hGuM.comp hfstfst).mul
      ((measurable_stateHistoryRatioBlock M q.val u).comp hfstfst)).mul hratio).mul
      (measurable_fst.comp measurable_snd)
  have hrightMeas : Measurable (fun h : StateHistoryView T nX nH r ↦
      G h * phiwFutureFunction M gap k h.2) := measurable_const.mul
    ((measurable_of_finite (phiwFutureFunction M gap k)).comp measurable_snd)
  have hfull : (∫ tau, phiwScore k M.b M.e (obsProj tau) u ∂M.law) =
      ∫ tau, phiwFutureFunction M gap k (curState r tau) ∂M.law := by
    calc
      (∫ tau, phiwScore k M.b M.e (obsProj tau) u ∂M.law) =
          ∫ tau, (Gu (histStateView u tau) *
            stateHistoryRatioBlock M q.val u (histStateView u tau)) *
            ratio M.b M.e (currentObsState u (histStateView u tau)) (actionAt u tau) *
            rewardAt u tau ∂M.law := by
        apply integral_congr_ae
        filter_upwards with tau
        have hGu : Gu (histStateView u tau) = 1 := by
          dsimp [Gu, Gq]
          rw [iterLiftStateHistoryFunction_histStateView,
            iterLiftStateHistoryFunction_histStateView]
        have hblock : actionHistoryRatioBlock M q.val u (histActionPair u tau) =
            ∏ j ∈ phiwWindow k u,
              ratio M.b M.e (curState j tau).1 (actionAt j tau) := by
          rw [actionHistoryRatioBlock_histActionPair M q.val u (by
            dsimp [u, q, epochAdd]
            omega) tau, phiwWindow_eq_interval u huK, hqval]
        have hscoreU : phiwScore k M.b M.e (obsProj tau) u =
            rewardAt u tau * actionHistoryRatioBlock M q.val u (histActionPair u tau) := by
          rw [phiwScore_obsProj, hblock]
        rw [hscoreU, hGu]
        unfold actionHistoryRatioBlock
        simp only [currentObsState, histActionPair, histStateView, actionAt, one_mul]
        ring
      _ = ∫ z, (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
            ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1
            ∂(M.law.map (histNextPair u)) := by
        rw [integral_map (measurable_histNextPair u).aemeasurable
          hleftMeas.aestronglyMeasurable]
        rfl
      _ = ∫ h, G h * phiwFutureFunction M gap k h.2
            ∂(M.law.map (histStateView r)) := hp
      _ = ∫ tau, G (histStateView r tau) *
            phiwFutureFunction M gap k (histStateView r tau).2 ∂M.law := by
        rw [integral_map (measurable_histStateView r).aemeasurable
          hrightMeas.aestronglyMeasurable]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with tau
        simp only [G, one_mul, histStateView]
  unfold obsLaw
  rw [integral_map measurable_obsProj.aemeasurable
    (phiwScore_measurable M.b M.e u).aestronglyMeasurable]
  exact hfull

/-- Centering an oscillation-bounded future function controls its covariance with an
integrable unit-`L¹` carrier.  The sharper constant `B` is kept as a local summation tool. [the h X condition](hyp:hX); and [the h FV condition](hyp:hFV); and [the h Xone condition](hyp:hXone); and [the h Fosc condition](hyp:hFosc). [the stated conclusion](goal). -/
lemma abs_integral_mul_sub_mul_integral_le_oscillation
    {Omega S : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {F : S → ℝ} {V : Omega → S} {B : ℝ}
    (hX : Integrable X mu) (hFV : Integrable (F ∘ V) mu)
    (hXone : ∫ w, |X w| ∂mu ≤ 1) (hFosc : OscillationBound B F) :
    |∫ w, X w * F (V w) ∂mu - (∫ w, X w ∂mu) * ∫ w, F (V w) ∂mu| ≤ B := by
  letI : Nonempty Omega := nonempty_of_isProbabilityMeasure mu
  have hFV' : Integrable (fun z ↦ F (V z)) mu := by
    simpa only [Function.comp_def] using hFV
  have hB0 : 0 ≤ B := by
    let w : Omega := Classical.choice inferInstance
    simpa using hFosc (V w) (V w)
  have hcenter : ∀ w, |F (V w) - ∫ z, F (V z) ∂mu| ≤ B := by
    intro w
    have heq : F (V w) - ∫ z, F (V z) ∂mu =
        ∫ z, (F (V w) - F (V z)) ∂mu := by
      symm
      calc
        (∫ z, (F (V w) - F (V z)) ∂mu) =
            (∫ _z : Omega, F (V w) ∂mu) - ∫ z, F (V z) ∂mu := by
          rw [integral_sub (integrable_const _) hFV']
        _ = _ := by simp
    rw [heq]
    calc
      |∫ z, (F (V w) - F (V z)) ∂mu| ≤
          ∫ z, |F (V w) - F (V z)| ∂mu := abs_integral_le_integral_abs
      _ ≤ ∫ _z : Omega, B ∂mu := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun _ ↦ abs_nonneg _
        · exact integrable_const B
        · exact Filter.Eventually.of_forall fun z ↦ hFosc (V w) (V z)
      _ = B := by simp
  have hcenterInt : Integrable (fun w ↦ F (V w) - ∫ z, F (V z) ∂mu) mu :=
    hFV'.sub (integrable_const _)
  have hprod : Integrable (fun w ↦ X w * (F (V w) - ∫ z, F (V z) ∂mu)) mu := by
    simpa only [mul_comm] using
      (hX.bdd_mul hcenterInt.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w ↦ by
          simpa only [Real.norm_eq_abs] using hcenter w))
  have hXF : Integrable (fun w ↦ X w * F (V w)) mu := by
    have hadd := hprod.add (hX.const_mul (∫ z, F (V z) ∂mu))
    apply hadd.congr
    filter_upwards with w
    simp only [Pi.add_apply]
    ring
  calc
    |∫ w, X w * F (V w) ∂mu - (∫ w, X w ∂mu) * ∫ w, F (V w) ∂mu| =
        |∫ w, X w * (F (V w) - ∫ z, F (V z) ∂mu) ∂mu| := by
      congr 1
      rw [show (∫ w, X w * (F (V w) - ∫ z, F (V z) ∂mu) ∂mu) =
          (∫ w, X w * F (V w) ∂mu) -
            (∫ w, X w ∂mu) * ∫ z, F (V z) ∂mu by
        simp_rw [mul_sub]
        rw [integral_sub hXF (hX.mul_const _), integral_mul_const]]
    _ ≤ ∫ w, |X w * (F (V w) - ∫ z, F (V z) ∂mu)| ∂mu :=
      abs_integral_le_integral_abs
    _ ≤ ∫ w, B * |X w| ∂mu := by
      apply integral_mono hprod.abs (hX.abs.const_mul B)
      intro w
      change |X w * (F (V w) - ∫ z, F (V z) ∂mu)| ≤ B * |X w|
      rw [abs_mul]
      nlinarith [abs_nonneg (X w), hcenter w]
    _ = B * ∫ w, |X w| ∂mu := by rw [integral_const_mul]
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left hXone hB0
    _ = B := mul_one B

/-- Sharp form of the disjoint-window covariance estimate used in the variance sum. [the h M condition](hyp:hM); and [the htk condition](hyp:htk); and [the hu condition](hyp:hu); and [the hdisjoint condition](hyp:hdisjoint). [the stated conclusion](goal). -/
lemma abs_covariance_phiwScore_le_disjoint_sharp {T nX nH k h : Nat} {t0 zeta C : ℝ}
    {M : RawPomdpExperiment T nX nH} (hM : LatentOverlapClass t0 zeta C M)
    (t u : Fin T) (htk : k ≤ t.val) (hu : u.val = t.val + h)
    (hdisjoint : k + 1 ≤ h) :
    |covariance (phiwScore k M.b M.e · t) (phiwScore k M.b M.e · u) (obsLaw M)| ≤
      2 * mixingAlpha t0 ^ (h - k - 1) := by
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  let gap := h - k - 1
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  have hgap : t.val + 1 + gap + k < T := by dsimp [gap]; omega
  have hXt : MemLp (phiwScore k M.b M.e · t) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 t
  have hXu : MemLp (phiwScore k M.b M.e · u) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 u
  have hXfull : Integrable (fun tau ↦ phiwScore k M.b M.e (obsProj tau) t) M.law := by
    apply (integrable_map_measure (phiwScore_measurable M.b M.e t).aestronglyMeasurable
      measurable_obsProj.aemeasurable).mp
    simpa only [obsLaw] using hXt.integrable one_le_two
  have hXone : ∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law ≤ 1 := by
    have hh := integral_abs_phiwScore_le_one hM.sequential_ignorability hM.policy_overlap
      hL hM.pomdp_kernel hM.bounded_reward t htk
    unfold obsLaw at hh
    calc
      (∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law) =
          ∫ w, |phiwScore k M.b M.e w t| ∂(M.law.map obsProj) := by
        symm
        exact integral_map (f := fun w : ObsView T nX ↦ |phiwScore k M.b M.e w t|)
          measurable_obsProj.aemeasurable
          ((continuous_abs.measurable.comp
            (phiwScore_measurable M.b M.e t)).aestronglyMeasurable)
      _ ≤ 1 := hh
  have hc :
      |(∫ tau, phiwScore k M.b M.e (obsProj tau) t *
          phiwFutureFunction M gap k (nextState t tau) ∂M.law) -
        (∫ tau, phiwScore k M.b M.e (obsProj tau) t ∂M.law) *
          ∫ tau, phiwFutureFunction M gap k (nextState t tau) ∂M.law| ≤
        2 * mixingAlpha t0 ^ gap := by
    /- Only states reached from the behavior-stationary trajectory contribute.
    Derive the centered contraction bound on that support; no claim is made
    about reward laws in unreachable kernel rows. -/
    let dB := stationaryLaw (policyKernel M M.b)
    let g : JointState nX nH → ℝ := fun s ↦
      if 0 < dB s then rewardRegression M s else 0
    let Fe := markovOperatorIter (policyKernel M M.e) k g
    let Fc := markovOperatorIter (policyKernel M M.b) gap Fe
    letI : Nonempty (JointState nX nH) :=
      nonemptyOfProbabilityVector dB hM.behavior_stationary_law.1
    have hg (s : JointState nX nH) : |g s| ≤ 1 := by
      dsimp [g]
      split_ifs with hs
      · exact rewardRegression_abs_le_one_of_behaviorSupport (by omega) hM s hs
      · simp
    have hgosc : OscillationBound 2 g := by
      intro x y
      calc
        |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
        _ ≤ 2 := by linarith [hg x, hg y]
    have ha0 : 0 ≤ mixingAlpha t0 := Real.exp_nonneg _
    have ha1 : mixingAlpha t0 ≤ 1 := by
      unfold mixingAlpha
      exact Real.exp_le_one_iff.mpr
        (neg_nonpos.mpr (one_div_nonneg.mpr hM.t0_pos.le))
    have heosc0 := oscillationBound_markovOperatorIter
      (policyKernel M M.e)
      (policyKernel_probabilityVector M hM.pomdp_kernel M.e hM.policy_overlap.1)
      ha0 (hM.uniform_contraction M.e (Or.inr rfl)) hgosc k
    have heosc : OscillationBound 2 Fe := by
      apply heosc0.mono
      have hpow : mixingAlpha t0 ^ k ≤ 1 := pow_le_one₀ ha0 ha1
      nlinarith
    have hfcosc : OscillationBound (2 * mixingAlpha t0 ^ gap) Fc := by
      have hh := oscillationBound_markovOperatorIter
        (policyKernel M M.b)
        (policyKernel_probabilityVector M hM.pomdp_kernel M.b
          hM.sequential_ignorability.1)
        ha0 (hM.uniform_contraction M.b (Or.inl rfl)) heosc gap
      simpa only [Fc, mul_comm] using hh
    have hfuture_eq (s : JointState nX nH) (hs : 0 < dB s) :
        phiwFutureFunction M gap k s = Fc s := by
      have heq_e (x : JointState nX nH) (hx : 0 < dB x) :
          markovOperatorIter (policyKernel M M.e) k (rewardRegression M) x = Fe x := by
        exact markovOperatorIter_congr_on_behaviorSupport hM M.e (Or.inr rfl)
          (rewardRegression M) g (fun y hy ↦ by simp [g, dB, hy]) k x hx
      simpa only [phiwFutureFunction, Fc, Fe] using
        markovOperatorIter_congr_on_behaviorSupport hM M.b (Or.inl rfl)
          (markovOperatorIter (policyKernel M M.e) k (rewardRegression M)) Fe
          heq_e gap s hs
    let r := nextEpoch t (by omega)
    let I : JointState nX nH → ℝ := fun s ↦ if dB s = 0 then 1 else 0
    have hIint : ∫ tau, I (curState r tau) ∂M.law = 0 := by
      rw [integral_curState_eq_behaviorStationary hM r I]
      apply Finset.sum_eq_zero
      intro s _
      change dB s * I s = 0
      by_cases hs : dB s = 0 <;> simp [I, hs]
    have hIi : Integrable (fun tau ↦ I (curState r tau)) M.law := by
      apply Integrable.of_bound (C := 1)
      · apply Measurable.aestronglyMeasurable
        apply (measurable_of_finite I).comp
        change Measurable (fun tau : FullTrajectory T nX nH ↦ tau.1 r.castSucc)
        fun_prop
      · filter_upwards with tau
        dsimp [I]
        split_ifs <;> norm_num
    have hInonneg : ∀ tau, 0 ≤ I (curState r tau) := by
      intro tau
      dsimp [I]
      split_ifs <;> norm_num
    have hIzero : (fun tau ↦ I (curState r tau)) =ᵐ[M.law] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg hInonneg hIi).mp hIint
    have hsupp : ∀ᵐ tau ∂M.law, 0 < dB (nextState t tau) := by
      filter_upwards [hIzero] with tau htau
      have hnext : nextState t tau = curState r tau := by
        rfl
      rw [hnext]
      by_contra hn
      have hz : dB (curState r tau) = 0 :=
        le_antisymm (le_of_not_gt hn) (hM.behavior_stationary_law.1.1 _)
      have : I (curState r tau) = 1 := by simp [I, hz]
      rw [this] at htau
      norm_num at htau
    have hFeq : (fun tau ↦ phiwFutureFunction M gap k (nextState t tau)) =ᵐ[M.law]
        fun tau ↦ Fc (nextState t tau) := by
      filter_upwards [hsupp] with tau htau
      exact hfuture_eq _ htau
    have hFci : Integrable (fun tau ↦ Fc (nextState t tau)) M.law := by
      apply Integrable.of_bound (C := ∑ s, |Fc s|)
      · apply Measurable.aestronglyMeasurable
        apply (measurable_of_finite Fc).comp
        change Measurable (fun tau : FullTrajectory T nX nH ↦ tau.1 t.succ)
        fun_prop
      · filter_upwards with tau
        exact Finset.single_le_sum (fun s _ ↦ abs_nonneg (Fc s))
          (Finset.mem_univ (nextState t tau))
    have hc' := abs_integral_mul_sub_mul_integral_le_oscillation M.law hXfull hFci
      hXone hfcosc
    have hprodEq : (fun tau ↦ phiwScore k M.b M.e (obsProj tau) t *
        phiwFutureFunction M gap k (nextState t tau)) =ᵐ[M.law]
        fun tau ↦ phiwScore k M.b M.e (obsProj tau) t * Fc (nextState t tau) := by
      filter_upwards [hFeq] with tau htau
      rw [htau]
    rw [integral_congr_ae hprodEq, integral_congr_ae hFeq]
    exact hc'
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let uu := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have huu : uu = u := by
    apply Fin.ext
    dsimp [uu, q, r, epochAdd, nextEpoch, gap]
    omega
  have hcross := integral_phiwScore_mul_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t htk hgap
  have hmean := integral_phiwScore_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t hgap
  change (∫ w, phiwScore k M.b M.e w t * phiwScore k M.b M.e w uu ∂obsLaw M) = _
    at hcross
  change (∫ w, phiwScore k M.b M.e w uu ∂obsLaw M) = _ at hmean
  rw [huu] at hcross hmean
  have hmeanT : (∫ w, phiwScore k M.b M.e w t ∂obsLaw M) =
      ∫ tau, phiwScore k M.b M.e (obsProj tau) t ∂M.law := by
    unfold obsLaw
    rw [integral_map measurable_obsProj.aemeasurable
      (phiwScore_measurable M.b M.e t).aestronglyMeasurable]
  rw [covariance_eq_sub hXt hXu]
  simp only [Pi.mul_apply]
  rw [hcross, hmean, hmeanT]
  simpa only [gap] using (hc.trans_eq (by ring))
/-! PRIOR PROOF (carry-over; the global kernel-row reward bound used below is no longer
available from the trajectory-level `BoundedReward` assumption). -/
/-
  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  let gap := h - k - 1
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  have hgap : t.val + 1 + gap + k < T := by dsimp [gap]; omega
  have hXt : MemLp (phiwScore k M.b M.e · t) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 t
  have hXu : MemLp (phiwScore k M.b M.e · u) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 u
  have hXfull : Integrable (fun tau ↦ phiwScore k M.b M.e (obsProj tau) t) M.law := by
    apply (integrable_map_measure (phiwScore_measurable M.b M.e t).aestronglyMeasurable
      measurable_obsProj.aemeasurable).mp
    simpa only [obsLaw] using hXt.integrable one_le_two
  have hXone : ∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law ≤ 1 := by
    have hh := integral_abs_phiwScore_le_one hM.sequential_ignorability hM.policy_overlap
      hL hM.pomdp_kernel hM.bounded_reward t htk
    unfold obsLaw at hh
    calc
      (∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law) =
          ∫ w, |phiwScore k M.b M.e w t| ∂(M.law.map obsProj) := by
        symm
        exact integral_map (f := fun w : ObsView T nX ↦ |phiwScore k M.b M.e w t|)
          measurable_obsProj.aemeasurable
          ((continuous_abs.measurable.comp
            (phiwScore_measurable M.b M.e t)).aestronglyMeasurable)
      _ ≤ 1 := hh
  have hfutureBound (s : JointState nX nH) : |phiwFutureFunction M gap k s| ≤ 1 := by
    apply abs_markovOperatorIter_le (policyKernel M M.b)
      (policyKernel_probabilityVector M hM.pomdp_kernel M.b hM.sequential_ignorability.1)
      zero_le_one
    intro x
    apply abs_markovOperatorIter_le (policyKernel M M.e)
      (policyKernel_probabilityVector M hM.pomdp_kernel M.e hM.policy_overlap.1) zero_le_one
    exact abs_rewardRegression_le_one hM.pomdp_kernel hM.bounded_reward hM.policy_overlap.1
  have hFV : Integrable (phiwFutureFunction M gap k ∘ nextState t) M.law := by
    apply Integrable.of_bound
    · exact ((measurable_of_finite (phiwFutureFunction M gap k)).comp (by
          unfold nextState
          fun_prop)).aestronglyMeasurable
    · filter_upwards with tau
      simpa only [Function.comp_apply, Real.norm_eq_abs] using hfutureBound (nextState t tau)
  have hc := abs_integral_mul_sub_mul_integral_le_oscillation M.law hXfull hFV hXone
    (phiwFutureFunction_oscillationBound hM gap k)
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let uu := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have huu : uu = u := by
    apply Fin.ext
    dsimp [uu, q, r, epochAdd, nextEpoch, gap]
    omega
  have hcross := integral_phiwScore_mul_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t htk hgap
  have hmean := integral_phiwScore_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t hgap
  change (∫ w, phiwScore k M.b M.e w t * phiwScore k M.b M.e w uu ∂obsLaw M) = _
    at hcross
  change (∫ w, phiwScore k M.b M.e w uu ∂obsLaw M) = _ at hmean
  rw [huu] at hcross hmean
  have hmeanT : (∫ w, phiwScore k M.b M.e w t ∂obsLaw M) =
      ∫ tau, phiwScore k M.b M.e (obsProj tau) t ∂M.law := by
    unfold obsLaw
    rw [integral_map measurable_obsProj.aemeasurable
      (phiwScore_measurable M.b M.e t).aestronglyMeasurable]
  rw [covariance_eq_sub hXt hXu]
  simp only [Pi.mul_apply]
  rw [hcross, hmean, hmeanT]
  simpa only [gap] using (hc.trans_eq (by ring))
-/

/-! PRIOR PROOF (carry-over: auto; signature-unchanged `abs_covariance_phiwScore_le_disjoint_sharp`). Stage 3: replace the
   placeholder above with this body, run `lean_diagnostic_messages`, patch failures only.
   := by  letI : IsProbabilityMeasure (obsLaw M) := by
    unfold obsLaw
    exact Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  let gap := h - k - 1
  have hL : 1 ≤ policyFactor zeta := by
    rw [policyFactor, ← Real.exp_zero]
    exact Real.exp_le_exp.mpr hM.zeta_pos.le
  have hgap : t.val + 1 + gap + k < T := by dsimp [gap]; omega
  have hXt : MemLp (phiwScore k M.b M.e · t) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 t
  have hXu : MemLp (phiwScore k M.b M.e · u) 2 (obsLaw M) :=
    phiwScore_memLp hM.sequential_ignorability hM.policy_overlap hL hM.bounded_reward 2 u
  have hXfull : Integrable (fun tau ↦ phiwScore k M.b M.e (obsProj tau) t) M.law := by
    apply (integrable_map_measure (phiwScore_measurable M.b M.e t).aestronglyMeasurable
      measurable_obsProj.aemeasurable).mp
    simpa only [obsLaw] using hXt.integrable one_le_two
  have hXone : ∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law ≤ 1 := by
    have hh := integral_abs_phiwScore_le_one hM.sequential_ignorability hM.policy_overlap
      hL hM.pomdp_kernel hM.bounded_reward t htk
    unfold obsLaw at hh
    calc
      (∫ tau, |phiwScore k M.b M.e (obsProj tau) t| ∂M.law) =
          ∫ w, |phiwScore k M.b M.e w t| ∂(M.law.map obsProj) := by
        symm
        exact integral_map (f := fun w : ObsView T nX ↦ |phiwScore k M.b M.e w t|)
          measurable_obsProj.aemeasurable
          ((continuous_abs.measurable.comp
            (phiwScore_measurable M.b M.e t)).aestronglyMeasurable)
      _ ≤ 1 := hh
  have hfutureBound (s : JointState nX nH) : |phiwFutureFunction M gap k s| ≤ 1 := by
    apply abs_markovOperatorIter_le (policyKernel M M.b)
      (policyKernel_probabilityVector M hM.pomdp_kernel M.b hM.sequential_ignorability.1)
      zero_le_one
    intro x
    apply abs_markovOperatorIter_le (policyKernel M M.e)
      (policyKernel_probabilityVector M hM.pomdp_kernel M.e hM.policy_overlap.1) zero_le_one
    exact abs_rewardRegression_le_one hM.pomdp_kernel hM.bounded_reward hM.policy_overlap.1
  have hFV : Integrable (phiwFutureFunction M gap k ∘ nextState t) M.law := by
    apply Integrable.of_bound
    · exact ((measurable_of_finite (phiwFutureFunction M gap k)).comp (by
          unfold nextState
          fun_prop)).aestronglyMeasurable
    · filter_upwards with tau
      simpa only [Function.comp_apply, Real.norm_eq_abs] using hfutureBound (nextState t tau)
  have hc := abs_integral_mul_sub_mul_integral_le_oscillation M.law hXfull hFV hXone
    (phiwFutureFunction_oscillationBound hM gap k)
  let r := nextEpoch t (by omega)
  let q := epochAdd r gap (by dsimp [r, nextEpoch]; omega)
  let uu := epochAdd q k (by dsimp [q, r, nextEpoch, epochAdd]; omega)
  have huu : uu = u := by
    apply Fin.ext
    dsimp [uu, q, r, epochAdd, nextEpoch, gap]
    omega
  have hcross := integral_phiwScore_mul_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t htk hgap
  have hmean := integral_phiwScore_eq_futureFunction hM.sequential_ignorability
    hM.policy_overlap hL hM.pomdp_kernel hM.bounded_reward t hgap
  change (∫ w, phiwScore k M.b M.e w t * phiwScore k M.b M.e w uu ∂obsLaw M) = _
    at hcross
  change (∫ w, phiwScore k M.b M.e w uu ∂obsLaw M) = _ at hmean
  rw [huu] at hcross hmean
  have hmeanT : (∫ w, phiwScore k M.b M.e w t ∂obsLaw M) =
      ∫ tau, phiwScore k M.b M.e (obsProj tau) t ∂M.law := by
    unfold obsLaw
    rw [integral_map measurable_obsProj.aemeasurable
      (phiwScore_measurable M.b M.e t).aestronglyMeasurable]
  rw [covariance_eq_sub hXt hXu]
  simp only [Pi.mul_apply]
  rw [hcross, hmean, hmeanT]
  simpa only [gap] using (hc.trans_eq (by ring))

-/
end CausalSmith.Stat.PomdpLatentOverlapMinimax
