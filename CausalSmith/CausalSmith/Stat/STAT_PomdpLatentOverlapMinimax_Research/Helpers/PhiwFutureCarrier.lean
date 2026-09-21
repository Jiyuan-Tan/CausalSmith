module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwMoments
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PolicyKernelContraction

set_option linter.style.longLine false

/-! # Peeling future PHIW scores through the trajectory law

This file supplies the one-epoch integral identities used to condition a future PHIW window
on an earlier state.  They are stated separately from the covariance algebra so that all
dependent-history transport remains localized here.

For disjoint windows, conditioning after the earlier reward leaves
`P_b^(h-k-1) P_e^k g_e`.  Thus state-marginal contraction supplies the exponent
`h-k-1`; it cannot supply one additional contraction across the reward/next-state pair.
For example, iid hidden signs with reward `(H_t + H_{t+1}) / 2` have a zero-contraction
state kernel but nonzero adjacent reward covariance.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- Adjoining a probability-kernel coordinate preserves integrability of a function of the
base coordinate alone. [the h Gm condition](hyp:hGm); and [the h G condition](hyp:hG). [the stated conclusion](goal). -/
lemma integrable_fst_compProd {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {mu : Measure A} {K : Kernel A B} [SFinite mu] [IsMarkovKernel K]
    {G : A → ℝ} (hGm : Measurable G) (hG : Integrable G mu) :
    Integrable (fun z : A × B ↦ G z.1) (mu.compProd K) := by
  have hmeas : AEStronglyMeasurable (fun z : A × B ↦ G z.1) (mu.compProd K) :=
    (hGm.comp measurable_fst).aestronglyMeasurable
  rw [Measure.integrable_compProd_iff hmeas]
  constructor
  · filter_upwards with a
    exact integrable_const (G a)
  · simpa using hG.norm

/-- Restrict a later state-history carrier to a strictly earlier epoch. -/
def restrictStateHistory {T nX nH : Nat} (t r : Fin T) (htr : t.val < r.val)
    (h : StateHistoryView T nX nH r) : StateHistoryView T nX nH t :=
  (((fun j ↦ h.1.1 ⟨j.val, lt_trans j.isLt htr⟩),
    (fun j ↦ h.1.2 ⟨j.val, lt_trans j.isLt htr⟩)),
    h.1.1 ⟨t.val, htr⟩)

/-- The restriction map is measurable. [the htr condition](hyp:htr). [the stated conclusion](goal). -/
lemma measurable_restrictStateHistory {T nX nH : Nat} (t r : Fin T)
    (htr : t.val < r.val) :
    Measurable (restrictStateHistory (nX := nX) (nH := nH) t r htr) := by
  unfold restrictStateHistory
  fun_prop

/-- Lift a function on the current state-history carrier to the successor carrier by forgetting
the appended action, reward, and next state. -/
def liftStateHistoryFunction {T nX nH : Nat} (r : Fin T) (hr : r.val + 1 < T)
    (G : StateHistoryView T nX nH r → ℝ) :
    StateHistoryView T nX nH (nextEpoch r hr) → ℝ :=
  fun h ↦ G (restrictStateHistory r (nextEpoch r hr) (by dsimp [nextEpoch]; omega) h)

/-- Assuming [the hr condition](hyp:hr), [the lift State History Function succ State History Equiv assertion holds](goal). -/
lemma liftStateHistoryFunction_succStateHistoryEquiv {T nX nH : Nat}
    (r : Fin T) (hr : r.val + 1 < T) (G : StateHistoryView T nX nH r → ℝ)
    (z : ActionHistoryView T nX nH r × Step nX nH) :
    liftStateHistoryFunction r hr G (succStateHistoryEquiv r hr z) = G z.1.1 := by
  unfold liftStateHistoryFunction restrictStateHistory
  apply congrArg G
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change (@Fin.snoc r.val (fun _ ↦ JointState nX nH) z.1.1.1.1 z.1.1.2)
          (Fin.castSucc j) = z.1.1.1.1 j
      rw [Fin.snoc_castSucc]
    · funext j
      change (@Fin.snoc r.val (fun _ ↦ Bool × ℝ) z.1.1.1.2 (z.1.2, z.2.1))
          (Fin.castSucc j) = z.1.1.1.2 j
      rw [Fin.snoc_castSucc]
  · change (@Fin.snoc r.val (fun _ ↦ JointState nX nH) z.1.1.1.1 z.1.1.2)
        (Fin.last r.val) = z.1.1.2
    rw [Fin.snoc_last]

/-- Assuming [the hr condition](hyp:hr), [the h G condition](hyp:hG), [the measurable lift State History Function assertion holds](goal). -/
lemma measurable_liftStateHistoryFunction {T nX nH : Nat}
    (r : Fin T) (hr : r.val + 1 < T) (G : StateHistoryView T nX nH r → ℝ)
    (hG : Measurable G) : Measurable (liftStateHistoryFunction r hr G) := by
  exact hG.comp (measurable_restrictStateHistory r (nextEpoch r hr)
    (by dsimp [nextEpoch]; omega))

/-- Add a natural offset to an epoch while retaining the explicit horizon proof. -/
def epochAdd {T : Nat} (r : Fin T) (m : Nat) (hm : r.val + m < T) : Fin T :=
  ⟨r.val + m, hm⟩

/-- Repeatedly lift a past-history carrier along successive state-history views. -/
def iterLiftStateHistoryFunction {T nX nH : Nat} (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) :
    (m : Nat) → (hm : r.val + m < T) →
      StateHistoryView T nX nH (epochAdd r m hm) → ℝ
  | 0, _ => G
  | m + 1, hm =>
      liftStateHistoryFunction
        (epochAdd r m (by omega)) (by dsimp [epochAdd]; omega)
        (iterLiftStateHistoryFunction r G m (by omega))

/-- Assuming [the h G condition](hyp:hG), [the hm condition](hyp:hm), [the measurable iter Lift State History Function assertion holds](goal). -/
lemma measurable_iterLiftStateHistoryFunction {T nX nH : Nat} (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) (hG : Measurable G)
    (m : Nat) (hm : r.val + m < T) :
    Measurable (iterLiftStateHistoryFunction r G m hm) := by
  induction m with
  | zero => simpa [iterLiftStateHistoryFunction]
  | succ m ih =>
      exact measurable_liftStateHistoryFunction _ _ _ (ih (by omega))

/-- A mature PHIW score represented on the state-history carrier immediately after its
reward epoch. -/
noncomputable def phiwPastCarrier {T nX nH k : Nat}
    (M : RawPomdpExperiment T nX nH) (t : Fin T) (ht : t.val + 1 < T)
    (h : StateHistoryView T nX nH (nextEpoch t ht)) : ℝ :=
  (h.1.2 (Fin.last t.val)).2 *
    actionHistoryRatioBlock M (t.val - k) t ((succStateHistoryEquiv t ht).symm h).1

/-- Assuming [the ht condition](hyp:ht), [the measurable phiw Past Carrier assertion holds](goal). -/
lemma measurable_phiwPastCarrier {T nX nH k : Nat}
    (M : RawPomdpExperiment T nX nH) (t : Fin T) (ht : t.val + 1 < T) :
    Measurable (phiwPastCarrier (k := k) M t ht) := by
  unfold phiwPastCarrier
  apply Measurable.mul
  · exact measurable_snd.comp ((measurable_pi_apply (Fin.last t.val)).comp
      (measurable_snd.comp measurable_fst))
  · exact (measurable_actionHistoryRatioBlock M (t.val - k) t).comp
      (measurable_fst.comp (measurable_succStateHistoryEquiv_symm t ht))

/-- The successor-history carrier is exactly the observable PHIW score on full paths. [the ht condition](hyp:ht); and [the htk condition](hyp:htk). [the stated conclusion](goal). -/
lemma phiwPastCarrier_histStateView {T nX nH k : Nat}
    (M : RawPomdpExperiment T nX nH) (t : Fin T) (ht : t.val + 1 < T)
    (htk : k ≤ t.val) (tau : FullTrajectory T nX nH) :
    phiwPastCarrier (k := k) M t ht (histStateView (nextEpoch t ht) tau) =
      phiwScore k M.b M.e (obsProj tau) t := by
  rw [← succStateHistoryEquiv_histNextPair t ht tau]
  unfold phiwPastCarrier
  simp only [Equiv.symm_apply_apply]
  have hre : (((succStateHistoryEquiv t ht) (histNextPair t tau)).1.2
      (Fin.last t.val)).2 = rewardAt t tau := by
    change ((@Fin.snoc t.val (fun _ ↦ Bool × ℝ)
      (histNextPair t tau).1.1.1.2
      ((histNextPair t tau).1.2, (histNextPair t tau).2.1)) (Fin.last t.val)).2 = _
    rw [Fin.snoc_last]
    rfl
  rw [hre]
  change rewardAt t tau * actionHistoryRatioBlock M (t.val - k) t
      (histActionPair t tau) = _
  rw [actionHistoryRatioBlock_histActionPair M (t.val - k) t (Nat.sub_le _ _)]
  rw [phiwScore_obsProj, phiwWindow_eq_interval t htk]

/-- Assuming [the hign condition](hyp:hign), [the hoverlap condition](hyp:hoverlap), [the h L condition](hyp:hL), [the h Y condition](hyp:hY), [the ht condition](hyp:ht), [the htk condition](hyp:htk), [the integrable phiw Past Carrier assertion holds](goal). -/
lemma integrable_phiwPastCarrier {T nX nH k : Nat} {L : ℝ}
    {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hY : BoundedReward M) (t : Fin T) (ht : t.val + 1 < T)
    (htk : k ≤ t.val) :
    Integrable (phiwPastCarrier (k := k) M t ht)
      (M.law.map (histStateView (nextEpoch t ht))) := by
  letI : IsProbabilityMeasure (obsLaw M) :=
    Measure.isProbabilityMeasure_map measurable_obsProj.aemeasurable
  have hs : Integrable (phiwScore k M.b M.e · t) (obsLaw M) :=
    (phiwScore_memLp (k := k) hign hoverlap hL hY 2 t).integrable one_le_two
  rw [obsLaw] at hs
  have hsfull : Integrable (fun tau ↦ phiwScore k M.b M.e (obsProj tau) t) M.law :=
    (integrable_map_measure (phiwScore_measurable M.b M.e t).aestronglyMeasurable
      measurable_obsProj.aemeasurable).mp hs
  apply (integrable_map_measure
    (measurable_phiwPastCarrier (k := k) M t ht).aestronglyMeasurable
    (measurable_histStateView (nextEpoch t ht)).aemeasurable).mpr
  exact Integrable.congr hsfull (Filter.Eventually.of_forall fun tau ↦
    (phiwPastCarrier_histStateView M t ht htk tau).symm)

/-- Integrating a function of the successor state under a reward-transition law is the
corresponding finite transition-marginal sum. [the h K condition](hyp:hK). [the stated conclusion](goal). -/
lemma integral_nextState_eq_sum {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hK : PomdpKernelLaw M) (s : JointState nX nH) (a : Bool)
    (F : JointState nX nH → ℝ) :
    ∫ y, F y.2 ∂(M.K s a) =
      ∑ s', (M.K s a {y | y.2 = s'}).toReal * F s' := by
  letI : IsProbabilityMeasure (M.K s a) := hK.1 s a
  have hmeas : Measurable (fun y : Step nX nH ↦ y.2) := measurable_snd
  haveI : IsProbabilityMeasure ((M.K s a).map (fun y ↦ y.2)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hF : Integrable F ((M.K s a).map (fun y ↦ y.2)) := by
    exact Integrable.of_finite
  rw [← integral_map hmeas.aemeasurable
    hF.aestronglyMeasurable]
  rw [MeasureTheory.integral_fintype hF]
  apply Finset.sum_congr rfl
  intro s' _
  change ((M.K s a).map (fun y ↦ y.2) {s'}).toReal * F s' = _
  rw [Measure.map_apply hmeas (measurableSet_singleton s')]
  rfl

/-- Averaging a successor-state function over the target action and transition is exactly
the target-policy Markov operator. [the h K condition](hyp:hK). [the stated conclusion](goal). -/
lemma sum_target_integral_nextState_eq_markovOperator
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hK : PomdpKernelLaw M) (s : JointState nX nH)
    (F : JointState nX nH → ℝ) :
    ∑ a : Bool, M.e s.1 a * ∫ y, F y.2 ∂(M.K s a) =
      markovOperator (policyKernel M M.e) F s := by
  simp_rw [integral_nextState_eq_sum hK]
  unfold markovOperator policyKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s' _
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The analogous behavior-policy identity. [the h K condition](hyp:hK). [the stated conclusion](goal). -/
lemma sum_behavior_integral_nextState_eq_markovOperator
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hK : PomdpKernelLaw M) (s : JointState nX nH)
    (F : JointState nX nH → ℝ) :
    ∑ a : Bool, M.b s.1 a * ∫ y, F y.2 ∂(M.K s a) =
      markovOperator (policyKernel M M.b) F s := by
  simp_rw [integral_nextState_eq_sum hK]
  unfold markovOperator policyKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s' _
  conv_rhs => rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Integrating the current action under its behavior conditional law. [the hign condition](hyp:hign); and [the hf condition](hyp:hf). [the stated conclusion](goal). -/
lemma integral_behavior_action_step
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (t : Fin T)
    (f : StateHistoryView T nX nH t × Bool → ℝ)
    (hf : Integrable f (M.law.map (histActionPair t))) :
    ∫ z, f z ∂(M.law.map (histActionPair t)) =
      ∫ h, ∑ a : Bool, M.b (currentObsState t h) a * f (h, a)
        ∂(M.law.map (histStateView t)) := by
  letI : IsMarkovKernel (behaviourKernel M) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hign.1 x).1 true) ((hign.1 x).1 false)]
    rw [show M.b x true + M.b x false = 1 by simpa using (hign.1 x).2]
    norm_num
  rw [hign.2 t] at hf ⊢
  rw [Measure.integral_compProd hf]
  apply integral_congr_ae
  filter_upwards with h
  change (∫ b, f (h, b) ∂
      ∑ a : Bool, ENNReal.ofReal (M.b (currentObsState t h) a) • Measure.dirac a) = _
  rw [integral_finsetSum_measure (fun a _ ↦
    (integrable_dirac (f := fun b : Bool ↦ f (h, b)) enorm_lt_top).smul_measure
      ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro a _
  rw [integral_smul_measure, integral_dirac,
    ENNReal.toReal_ofReal ((hign.1 _).1 a)]
  rfl

/-- A measurable integrable past carrier remains integrable after one successor-history lift. [the hign condition](hyp:hign); and [the h K condition](hyp:hK); and [the hr condition](hyp:hr); and [the h Gm condition](hyp:hGm); and [the h Gi condition](hyp:hGi). [the stated conclusion](goal). -/
lemma integrable_liftStateHistoryFunction
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M)
    (r : Fin T) (hr : r.val + 1 < T) (G : StateHistoryView T nX nH r → ℝ)
    (hGm : Measurable G) (hGi : Integrable G (M.law.map (histStateView r))) :
    Integrable (liftStateHistoryFunction r hr G)
      (M.law.map (histStateView (nextEpoch r hr))) := by
  letI : IsMarkovKernel (behaviourKernel M) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hign.1 x).1 true) ((hign.1 x).1 false)]
    rw [show M.b x true + M.b x false = 1 by simpa using (hign.1 x).2]
    norm_num
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa ↦ hK.1 sa.1 sa.2⟩
  have hGa : Integrable (fun z : StateHistoryView T nX nH r × Bool ↦ G z.1)
      (M.law.map (histActionPair r)) := by
    rw [hign.2 r]
    exact integrable_fst_compProd hGm hGi
  have hGn : Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦ G z.1.1)
      (M.law.map (histNextPair r)) := by
    rw [hK.2 r]
    exact integrable_fst_compProd (hGm.comp measurable_fst) hGa
  rw [map_histStateView_next M r hr]
  apply (integrable_map_measure
    (measurable_liftStateHistoryFunction r hr G hGm).aestronglyMeasurable
    (measurable_succStateHistoryEquiv r hr).aemeasurable).mpr
  have heq : liftStateHistoryFunction r hr G ∘ (succStateHistoryEquiv r hr) =
      fun z ↦ G z.1.1 := by
    funext z
    exact liftStateHistoryFunction_succStateHistoryEquiv r hr G z
  rw [heq]
  exact hGn

/-- Assuming [the hign condition](hyp:hign), [the h Gm condition](hyp:hGm), [the h Gi condition](hyp:hGi), [the integrable history Carrier action assertion holds](goal). -/
lemma integrable_historyCarrier_action
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) (hGm : Measurable G)
    (hGi : Integrable G (M.law.map (histStateView r))) :
    Integrable (fun z : StateHistoryView T nX nH r × Bool ↦ G z.1)
      (M.law.map (histActionPair r)) := by
  letI : IsMarkovKernel (behaviourKernel M) := by
    constructor
    intro x
    constructor
    change (∑ a : Bool, ENNReal.ofReal (M.b x a) • Measure.dirac a) Set.univ = 1
    simp
    rw [← ENNReal.ofReal_add ((hign.1 x).1 true) ((hign.1 x).1 false)]
    rw [show M.b x true + M.b x false = 1 by simpa using (hign.1 x).2]
    norm_num
  rw [hign.2 r]
  exact integrable_fst_compProd hGm hGi

/-- Assuming [the hign condition](hyp:hign), [the h K condition](hyp:hK), [the h Gm condition](hyp:hGm), [the h Gi condition](hyp:hGi), [the integrable history Carrier next assertion holds](goal). -/
lemma integrable_historyCarrier_next
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M) (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) (hGm : Measurable G)
    (hGi : Integrable G (M.law.map (histStateView r))) :
    Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦ G z.1.1)
      (M.law.map (histNextPair r)) := by
  letI : IsMarkovKernel (kernelOfK M) := ⟨fun sa ↦ hK.1 sa.1 sa.2⟩
  have hGa := integrable_historyCarrier_action hign r G hGm hGi
  rw [hK.2 r]
  exact integrable_fst_compProd (hGm.comp measurable_fst) hGa

/-- The two explicit integrability obligations for a behavior peeling step follow from an
integrable past carrier and a bounded finite-state future function. [the hign condition](hyp:hign); and [the h K condition](hyp:hK); and [the h Gm condition](hyp:hGm); and [the h Gi condition](hyp:hGi); and [the h F condition](hyp:hF). [the stated conclusion](goal). -/
lemma integrable_behaviorPeel_obligations
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M) (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) (hGm : Measurable G)
    (hGi : Integrable G (M.law.map (histStateView r)))
    (F : JointState nX nH → ℝ) {B : ℝ} (hF : ∀ s, |F s| ≤ B) :
    Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦
      G z.1.1 * F z.2.2) (M.law.map (histNextPair r)) ∧
    Integrable (fun z : StateHistoryView T nX nH r × Bool ↦
      G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair r)) := by
  have hGn := integrable_historyCarrier_next hign hK r G hGm hGi
  have hGa := integrable_historyCarrier_action hign r G hGm hGi
  constructor
  · have hb := hGn.bdd_mul
      ((measurable_of_finite F).comp (measurable_snd.comp measurable_snd)
        |>.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z ↦ by
        change |F z.2.2| ≤ B
        exact hF z.2.2)
    simpa [mul_comm] using hb
  · let J : StateHistoryView T nX nH r × Bool → ℝ :=
      fun z ↦ ∫ y, F y.2 ∂(M.K z.1.2 z.2)
    let J0 : JointState nX nH × Bool → ℝ :=
      fun z ↦ ∫ y, F y.2 ∂(M.K z.1 z.2)
    have hJm : Measurable J := by
      exact (measurable_of_finite J0).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hJb : ∀ z, |J z| ≤ B := by
      intro z
      letI : IsProbabilityMeasure (M.K z.1.2 z.2) := hK.1 z.1.2 z.2
      have hn : ‖∫ y, F y.2 ∂(M.K z.1.2 z.2)‖ ≤
          B * (M.K z.1.2 z.2).real Set.univ :=
        norm_integral_le_of_norm_le_const
          (Filter.Eventually.of_forall fun y : Step nX nH ↦ by
            simpa only [Real.norm_eq_abs] using hF y.2)
      simpa only [J, Real.norm_eq_abs, mul_one, probReal_univ] using hn
    have hb := hGa.bdd_mul hJm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by
        simpa only [Real.norm_eq_abs] using hJb z)
    simpa [J, mul_comm] using hb

/-- The analogous obligations for an epoch inside the target ratio block. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Gm condition](hyp:hGm); and [the h Gi condition](hyp:hGi); and [the h F condition](hyp:hF). [the stated conclusion](goal). -/
lemma integrable_targetPeel_obligations
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat) (r : Fin T)
    (G : StateHistoryView T nX nH r → ℝ) (hGm : Measurable G)
    (hGi : Integrable G (M.law.map (histStateView r)))
    (F : JointState nX nH → ℝ) {B : ℝ} (hF : ∀ s, |F s| ≤ B) :
    Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦
      (G z.1.1 * stateHistoryRatioBlock M lo r z.1.1) *
        ratio M.b M.e (currentObsState r z.1.1) z.1.2 * F z.2.2)
      (M.law.map (histNextPair r)) ∧
    Integrable (fun z : StateHistoryView T nX nH r × Bool ↦
      (G z.1 * stateHistoryRatioBlock M lo r z.1) *
        ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair r)) := by
  let Cfun : StateHistoryView T nX nH r → ℝ :=
    fun h ↦ G h * stateHistoryRatioBlock M lo r h
  have hCm : Measurable Cfun := hGm.mul (measurable_stateHistoryRatioBlock M lo r)
  have hCi : Integrable Cfun (M.law.map (histStateView r)) := by
    have hb := hGi.bdd_mul
      (measurable_stateHistoryRatioBlock M lo r).aestronglyMeasurable
      (Filter.Eventually.of_forall fun h ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo r h).1]
        exact (stateHistoryRatioBlock_mem_Icc hign hoverlap hL lo r h).2)
    simpa [Cfun, mul_comm] using hb
  have hb := integrable_behaviorPeel_obligations hign hK r Cfun hCm hCi F hF
  constructor
  · have hrm : Measurable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦
        ratio M.b M.e (currentObsState r z.1.1) z.1.2) := by
      exact (measurable_of_finite (fun xa : Fin nX × Bool ↦
        ratio M.b M.e xa.1 xa.2)).comp
        (((measurable_currentObsState r).comp (measurable_fst.comp measurable_fst)).prodMk
          (measurable_snd.comp measurable_fst))
    have hx := hb.1.bdd_mul hrm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg
          (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).1]
        exact (ratio_mem hign.1 hoverlap.1 hoverlap.2 (zero_le_one.trans hL) _ _).2)
    simpa [Cfun, mul_assoc, mul_left_comm, mul_comm] using hx
  · simpa [Cfun] using hb.2

/-- Assuming [the hign condition](hyp:hign), [the h K condition](hyp:hK), [the h Gm condition](hyp:hGm), [the h Gi condition](hyp:hGi), [the hm condition](hyp:hm), [the integrable iter Lift State History Function assertion holds](goal). -/
lemma integrable_iterLiftStateHistoryFunction
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M)
    (r : Fin T) (G : StateHistoryView T nX nH r → ℝ)
    (hGm : Measurable G) (hGi : Integrable G (M.law.map (histStateView r)))
    (m : Nat) (hm : r.val + m < T) :
    Integrable (iterLiftStateHistoryFunction r G m hm)
      (M.law.map (histStateView (epochAdd r m hm))) := by
  induction m with
  | zero => exact hGi
  | succ m ih =>
      let rm : Fin T := epochAdd r m (by omega)
      have hrm : rm.val + 1 < T := by dsimp [rm, epochAdd]; omega
      have hs := integrable_liftStateHistoryFunction hign hK rm hrm
        (iterLiftStateHistoryFunction r G m (by omega))
        (measurable_iterLiftStateHistoryFunction r G hGm m (by omega)) (ih (by omega))
      have hepoch : nextEpoch rm hrm = epochAdd r (m + 1) hm := by
        apply Fin.ext
        dsimp [nextEpoch, rm, epochAdd]
        omega
      cases hepoch
      change Integrable (liftStateHistoryFunction rm hrm
        (iterLiftStateHistoryFunction r G m (by omega)))
        (M.law.map (histStateView (nextEpoch rm hrm)))
      exact hs

/-- Assuming [the hm condition](hyp:hm), [the iter Lift State History Function hist State View assertion holds](goal). -/
lemma iterLiftStateHistoryFunction_histStateView
    {T nX nH : Nat} (r : Fin T) (G : StateHistoryView T nX nH r → ℝ)
    (m : Nat) (hm : r.val + m < T) (tau : FullTrajectory T nX nH) :
    iterLiftStateHistoryFunction r G m hm (histStateView (epochAdd r m hm) tau) =
      G (histStateView r tau) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      let rm : Fin T := epochAdd r m (by omega)
      have hrm : rm.val + 1 < T := by dsimp [rm, epochAdd]; omega
      have hepoch : nextEpoch rm hrm = epochAdd r (m + 1) hm := by
        apply Fin.ext
        dsimp [nextEpoch, rm, epochAdd]
        omega
      cases hepoch
      change liftStateHistoryFunction rm hrm
        (iterLiftStateHistoryFunction r G m (by omega))
        (histStateView (nextEpoch rm hrm) tau) = _
      rw [← succStateHistoryEquiv_histNextPair rm hrm tau]
      rw [liftStateHistoryFunction_succStateHistoryEquiv]
      exact ih (by omega)

end CausalSmith.Stat.PomdpLatentOverlapMinimax
