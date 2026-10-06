module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.PhiwFutureCarrier

set_option linter.style.longLine false

/-! # Iterated peeling of future PHIW scores -/

public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open Causalean.Mathlib.Probability.FiniteMarkovOscillation
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- An unweighted behavior epoch advances a history carrier by one behavior-policy Markov
operator. [the hign condition](hyp:hign); and [the h K condition](hyp:hK); and [the hfull condition](hyp:hfull); and [the haction condition](hyp:haction). [the stated conclusion](goal). -/
lemma integral_history_mul_behavior_nextState
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M) (t : Fin T)
    (G : StateHistoryView T nX nH t → ℝ) (F : JointState nX nH → ℝ)
    (hfull : Integrable (fun z : ActionHistoryView T nX nH t × Step nX nH ↦
      G z.1.1 * F z.2.2) (M.law.map (histNextPair t)))
    (haction : Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
      G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair t))) :
    ∫ z, G z.1.1 * F z.2.2 ∂(M.law.map (histNextPair t)) =
      ∫ h, G h * markovOperator (policyKernel M M.b) F h.2
        ∂(M.law.map (histStateView t)) := by
  rw [integral_kernel_step hK t _ hfull]
  have hactionStep := integral_behavior_action_step hign t
    (fun z ↦ G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2)) haction
  calc
    (∫ h, ∫ y, G h.1 * F y.2 ∂(M.K h.1.2 h.2)
        ∂(M.law.map (histView t))) =
        ∫ z, G z.1 * (∫ y, F y.2 ∂(M.K z.1.2 z.2))
          ∂(M.law.map (histActionPair t)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [MeasureTheory.integral_const_mul]
    _ = ∫ h, ∑ a : Bool, M.b (currentObsState t h) a *
          (G h * ∫ y, F y.2 ∂(M.K h.2 a))
          ∂(M.law.map (histStateView t)) := hactionStep
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with h
      rw [← sum_behavior_integral_nextState_eq_markovOperator hK h.2 F]
      simp only [currentObsState]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- A history-measurable carrier can be kept fixed while the current target-policy ratio and
the reward-transition output are integrated.  The resulting state function is one target
Markov step. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the hfull condition](hyp:hfull); and [the haction condition](hyp:haction). [the stated conclusion](goal). -/
lemma integral_history_mul_ratio_nextState
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 0 ≤ L) (hK : PomdpKernelLaw M) (t : Fin T)
    (G : StateHistoryView T nX nH t → ℝ) (F : JointState nX nH → ℝ)
    (hfull : Integrable (fun z : ActionHistoryView T nX nH t × Step nX nH ↦
      G z.1.1 * ratio M.b M.e (currentObsState t z.1.1) z.1.2 * F z.2.2)
      (M.law.map (histNextPair t)))
    (haction : Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
      G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair t))) :
    ∫ z, G z.1.1 * ratio M.b M.e (currentObsState t z.1.1) z.1.2 * F z.2.2
        ∂(M.law.map (histNextPair t)) =
      ∫ h, G h * markovOperator (policyKernel M M.e) F h.2
        ∂(M.law.map (histStateView t)) := by
  rw [integral_kernel_step hK t _ hfull]
  have hratio := integral_ratio_step hign hoverlap hL t
    (fun z ↦ G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2)) haction
  calc
    (∫ h, ∫ y, G h.1 * ratio M.b M.e (currentObsState t h.1) h.2 * F y.2
        ∂(M.K h.1.2 h.2) ∂(M.law.map (histView t))) =
        ∫ z, ratio M.b M.e (currentObsState t z.1) z.2 *
          (G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2))
          ∂(M.law.map (histActionPair t)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [MeasureTheory.integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Bool, M.e (currentObsState t h) a *
          (G h * ∫ y, F y.2 ∂(M.K h.2 a))
          ∂(M.law.map (histStateView t)) := hratio
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with h
      rw [← sum_target_integral_nextState_eq_markovOperator hK h.2 F]
      simp only [currentObsState]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- The terminal version of the peeling identity replaces the weighted current reward by the
target-policy reward regression while preserving every past-history carrier. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the hfull condition](hyp:hfull); and [the haction condition](hyp:haction). [the stated conclusion](goal). -/
lemma integral_history_mul_ratio_reward
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 0 ≤ L) (hK : PomdpKernelLaw M) (t : Fin T)
    (G : StateHistoryView T nX nH t → ℝ)
    (hfull : Integrable (fun z : ActionHistoryView T nX nH t × Step nX nH ↦
      G z.1.1 * ratio M.b M.e (currentObsState t z.1.1) z.1.2 * z.2.1)
      (M.law.map (histNextPair t)))
    (haction : Integrable (fun z : StateHistoryView T nX nH t × Bool ↦
      G z.1 * ∫ y, y.1 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair t))) :
    ∫ z, G z.1.1 * ratio M.b M.e (currentObsState t z.1.1) z.1.2 * z.2.1
        ∂(M.law.map (histNextPair t)) =
      ∫ h, G h * rewardRegression M h.2 ∂(M.law.map (histStateView t)) := by
  rw [integral_kernel_step hK t _ hfull]
  have hratio := integral_ratio_step hign hoverlap hL t
    (fun z ↦ G z.1 * ∫ y, y.1 ∂(M.K z.1.2 z.2)) haction
  calc
    (∫ h, ∫ y, G h.1 * ratio M.b M.e (currentObsState t h.1) h.2 * y.1
        ∂(M.K h.1.2 h.2) ∂(M.law.map (histView t))) =
        ∫ z, ratio M.b M.e (currentObsState t z.1) z.2 *
          (G z.1 * ∫ y, y.1 ∂(M.K z.1.2 z.2))
          ∂(M.law.map (histActionPair t)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [MeasureTheory.integral_const_mul]
      ring
    _ = ∫ h, ∑ a : Bool, M.e (currentObsState t h) a *
          (G h * ∫ y, y.1 ∂(M.K h.2 a))
          ∂(M.law.map (histStateView t)) := hratio
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with h
      unfold rewardRegression
      simp only [currentObsState]
      conv_rhs => rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Backward-induction step through an epoch belonging to the target-policy ratio block. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the hr condition](hyp:hr); and [the hlo condition](hyp:hlo); and [the h G condition](hyp:hG); and [the hfull condition](hyp:hfull); and [the haction condition](hyp:haction). [the stated conclusion](goal). -/
lemma integral_lift_mul_stateHistoryRatioBlock_target_succ
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 0 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat) (r : Fin T)
    (hr : r.val + 1 < T) (hlo : lo ≤ r.val)
    (G : StateHistoryView T nX nH r → ℝ) (hG : Measurable G)
    (F : JointState nX nH → ℝ)
    (hfull : Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦
      (G z.1.1 * stateHistoryRatioBlock M lo r z.1.1) *
        ratio M.b M.e (currentObsState r z.1.1) z.1.2 * F z.2.2)
      (M.law.map (histNextPair r)))
    (haction : Integrable (fun z : StateHistoryView T nX nH r × Bool ↦
      (G z.1 * stateHistoryRatioBlock M lo r z.1) *
        ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair r))) :
    ∫ h, liftStateHistoryFunction r hr G h *
          stateHistoryRatioBlock M lo (nextEpoch r hr) h * F h.2
        ∂(M.law.map (histStateView (nextEpoch r hr))) =
      ∫ h, G h * stateHistoryRatioBlock M lo r h *
          markovOperator (policyKernel M M.e) F h.2
        ∂(M.law.map (histStateView r)) := by
  rw [map_histStateView_next M r hr]
  have hmeas : Measurable (fun h : StateHistoryView T nX nH (nextEpoch r hr) ↦
      liftStateHistoryFunction r hr G h *
        stateHistoryRatioBlock M lo (nextEpoch r hr) h * F h.2) := by
    exact ((measurable_liftStateHistoryFunction r hr G hG).mul
      (measurable_stateHistoryRatioBlock M lo (nextEpoch r hr))).mul
      ((measurable_of_finite F).comp measurable_snd)
  rw [integral_map (measurable_succStateHistoryEquiv r hr).aemeasurable
    hmeas.aestronglyMeasurable]
  have hp := integral_history_mul_ratio_nextState hign hoverlap hL hK r
    (fun h ↦ G h * stateHistoryRatioBlock M lo r h) F hfull haction
  calc
    (∫ z, liftStateHistoryFunction r hr G (succStateHistoryEquiv r hr z) *
        stateHistoryRatioBlock M lo (nextEpoch r hr) (succStateHistoryEquiv r hr z) *
          F (succStateHistoryEquiv r hr z).2 ∂(M.law.map (histNextPair r))) =
      ∫ z, (G z.1.1 * stateHistoryRatioBlock M lo r z.1.1) *
          ratio M.b M.e (currentObsState r z.1.1) z.1.2 * F z.2.2
        ∂(M.law.map (histNextPair r)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [liftStateHistoryFunction_succStateHistoryEquiv]
      rw [stateHistoryRatioBlock_succEquiv M lo r hr hlo]
      unfold actionHistoryRatioBlock
      change G z.1.1 * (stateHistoryRatioBlock M lo r z.1.1 *
          ratio M.b M.e (currentObsState r z.1.1) z.1.2) * F z.2.2 = _
      ring
    _ = _ := by
      simpa [mul_assoc] using hp

/-- Backward-induction step through an epoch in the unweighted behavior-policy gap. [the hign condition](hyp:hign); and [the h K condition](hyp:hK); and [the hr condition](hyp:hr); and [the h G condition](hyp:hG); and [the hfull condition](hyp:hfull); and [the haction condition](hyp:haction). [the stated conclusion](goal). -/
lemma integral_lift_mul_behavior_succ
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M) (r : Fin T)
    (hr : r.val + 1 < T) (G : StateHistoryView T nX nH r → ℝ)
    (hG : Measurable G) (F : JointState nX nH → ℝ)
    (hfull : Integrable (fun z : ActionHistoryView T nX nH r × Step nX nH ↦
      G z.1.1 * F z.2.2) (M.law.map (histNextPair r)))
    (haction : Integrable (fun z : StateHistoryView T nX nH r × Bool ↦
      G z.1 * ∫ y, F y.2 ∂(M.K z.1.2 z.2))
      (M.law.map (histActionPair r))) :
    ∫ h, liftStateHistoryFunction r hr G h * F h.2
        ∂(M.law.map (histStateView (nextEpoch r hr))) =
      ∫ h, G h * markovOperator (policyKernel M M.b) F h.2
        ∂(M.law.map (histStateView r)) := by
  rw [map_histStateView_next M r hr]
  have hmeas : Measurable (fun h : StateHistoryView T nX nH (nextEpoch r hr) ↦
      liftStateHistoryFunction r hr G h * F h.2) :=
    (measurable_liftStateHistoryFunction r hr G hG).mul
      ((measurable_of_finite F).comp measurable_snd)
  rw [integral_map (measurable_succStateHistoryEquiv r hr).aemeasurable
    hmeas.aestronglyMeasurable]
  have hp := integral_history_mul_behavior_nextState hign hK r G F hfull haction
  calc
    (∫ z, liftStateHistoryFunction r hr G (succStateHistoryEquiv r hr z) *
        F (succStateHistoryEquiv r hr z).2 ∂(M.law.map (histNextPair r))) =
      ∫ z, G z.1.1 * F z.2.2 ∂(M.law.map (histNextPair r)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [liftStateHistoryFunction_succStateHistoryEquiv]
      rfl
    _ = _ := hp

/-- [the markov Operator Iter one right assertion holds](goal). -/
lemma markovOperatorIter_one_right {S : Type*} [Fintype S]
    (P : S → S → ℝ) (n : Nat) (F : S → ℝ) :
    markovOperatorIter P n (markovOperator P F) =
      markovOperatorIter P (n + 1) F := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [markovOperatorIter_succ]
      rw [ih]
      rfl

/-- Iteration of the behavior-gap peeling step.  The hypotheses expose exactly the two
integrability obligations at every backward epoch. [the hign condition](hyp:hign); and [the h K condition](hyp:hK); and [the h G condition](hyp:hG); and [the hm condition](hyp:hm); and [the hint condition](hyp:hint). [the stated conclusion](goal). -/
lemma integral_iterLift_mul_behavior
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH}
    (hign : SequentialIgnorability M) (hK : PomdpKernelLaw M)
    (r : Fin T) (G : StateHistoryView T nX nH r → ℝ) (hG : Measurable G)
    (F : JointState nX nH → ℝ) (m : Nat) (hm : r.val + m < T)
    (hint : ∀ i (hi : i < m),
      let ri := epochAdd r i (by omega)
      let Gi := iterLiftStateHistoryFunction r G i (by omega)
      let Fi := markovOperatorIter (policyKernel M M.b) (m - i - 1) F
      Integrable (fun z : ActionHistoryView T nX nH ri × Step nX nH ↦
        Gi z.1.1 * Fi z.2.2) (M.law.map (histNextPair ri)) ∧
      Integrable (fun z : StateHistoryView T nX nH ri × Bool ↦
        Gi z.1 * ∫ y, Fi y.2 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair ri))) :
    ∫ h, iterLiftStateHistoryFunction r G m hm h * F h.2
        ∂(M.law.map (histStateView (epochAdd r m hm))) =
      ∫ h, G h * markovOperatorIter (policyKernel M M.b) m F h.2
        ∂(M.law.map (histStateView r)) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
      let rm : Fin T := epochAdd r m (by omega)
      have hrm : rm.val + 1 < T := by dsimp [rm, epochAdd]; omega
      have hepoch : nextEpoch rm hrm = epochAdd r (m + 1) hm := by
        apply Fin.ext
        dsimp [nextEpoch, rm, epochAdd]
        omega
      have hend : m + 1 - m - 1 = 0 := by omega
      have hs := integral_lift_mul_behavior_succ hign hK rm hrm
        (iterLiftStateHistoryFunction r G m (by omega))
        (measurable_iterLiftStateHistoryFunction r G hG m (by omega)) F
        (by simpa [hend, markovOperatorIter] using (hint m (by omega)).1)
        (by simpa [hend, markovOperatorIter] using (hint m (by omega)).2)
      have hrec := ih (markovOperator (policyKernel M M.b) F) (by omega)
        (fun i hi ↦ by
          have hx := hint i (by omega)
          have he : m + 1 - i - 1 = (m - i - 1) + 1 := by omega
          rw [he, ← markovOperatorIter_one_right] at hx
          exact hx)
      calc
        (∫ h, iterLiftStateHistoryFunction r G (m + 1) hm h * F h.2
            ∂(M.law.map (histStateView (epochAdd r (m + 1) hm)))) =
          (∫ h, iterLiftStateHistoryFunction r G m (by omega) h *
              markovOperator (policyKernel M M.b) F h.2
            ∂(M.law.map (histStateView rm))) := by
              cases hepoch
              change (∫ h, liftStateHistoryFunction rm hrm
                  (iterLiftStateHistoryFunction r G m (by omega)) h * F h.2
                    ∂(M.law.map (histStateView (nextEpoch rm hrm)))) = _
              exact hs
        _ = (∫ h, G h * markovOperatorIter (policyKernel M M.b) m
              (markovOperator (policyKernel M M.b) F) h.2
            ∂(M.law.map (histStateView r))) := hrec
        _ = _ := by rw [markovOperatorIter_one_right]

/-- Iteration of the target-policy part of a PHIW window, with all intermediate
integrability obligations made explicit. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the hlo condition](hyp:hlo); and [the h G condition](hyp:hG); and [the hm condition](hyp:hm); and [the hint condition](hyp:hint). [the stated conclusion](goal). -/
lemma integral_iterLift_mul_targetRatioBlock
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 0 ≤ L) (hK : PomdpKernelLaw M) (lo : Nat)
    (r : Fin T) (hlo : lo ≤ r.val)
    (G : StateHistoryView T nX nH r → ℝ) (hG : Measurable G)
    (F : JointState nX nH → ℝ) (m : Nat) (hm : r.val + m < T)
    (hint : ∀ i (hi : i < m),
      let ri := epochAdd r i (by omega)
      let Gi := iterLiftStateHistoryFunction r G i (by omega)
      let Fi := markovOperatorIter (policyKernel M M.e) (m - i - 1) F
      Integrable (fun z : ActionHistoryView T nX nH ri × Step nX nH ↦
        (Gi z.1.1 * stateHistoryRatioBlock M lo ri z.1.1) *
          ratio M.b M.e (currentObsState ri z.1.1) z.1.2 * Fi z.2.2)
        (M.law.map (histNextPair ri)) ∧
      Integrable (fun z : StateHistoryView T nX nH ri × Bool ↦
        (Gi z.1 * stateHistoryRatioBlock M lo ri z.1) *
          ∫ y, Fi y.2 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair ri))) :
    ∫ h, iterLiftStateHistoryFunction r G m hm h *
          stateHistoryRatioBlock M lo (epochAdd r m hm) h * F h.2
        ∂(M.law.map (histStateView (epochAdd r m hm))) =
      ∫ h, G h * stateHistoryRatioBlock M lo r h *
          markovOperatorIter (policyKernel M M.e) m F h.2
        ∂(M.law.map (histStateView r)) := by
  induction m generalizing F with
  | zero => rfl
  | succ m ih =>
      let rm : Fin T := epochAdd r m (by omega)
      have hrm : rm.val + 1 < T := by dsimp [rm, epochAdd]; omega
      have hlom : lo ≤ rm.val := by dsimp [rm, epochAdd]; omega
      have hepoch : nextEpoch rm hrm = epochAdd r (m + 1) hm := by
        apply Fin.ext
        dsimp [nextEpoch, rm, epochAdd]
        omega
      have hend : m + 1 - m - 1 = 0 := by omega
      have hs := integral_lift_mul_stateHistoryRatioBlock_target_succ
        hign hoverlap hL hK lo rm hrm hlom
        (iterLiftStateHistoryFunction r G m (by omega))
        (measurable_iterLiftStateHistoryFunction r G hG m (by omega)) F
        (by simpa [hend, markovOperatorIter] using (hint m (by omega)).1)
        (by simpa [hend, markovOperatorIter] using (hint m (by omega)).2)
      have hrec := ih (markovOperator (policyKernel M M.e) F) (by omega)
        (fun i hi ↦ by
          have hx := hint i (by omega)
          have he : m + 1 - i - 1 = (m - i - 1) + 1 := by omega
          rw [he, ← markovOperatorIter_one_right] at hx
          exact hx)
      calc
        (∫ h, iterLiftStateHistoryFunction r G (m + 1) hm h *
              stateHistoryRatioBlock M lo (epochAdd r (m + 1) hm) h * F h.2
            ∂(M.law.map (histStateView (epochAdd r (m + 1) hm)))) =
          (∫ h, iterLiftStateHistoryFunction r G m (by omega) h *
              stateHistoryRatioBlock M lo rm h *
                markovOperator (policyKernel M M.e) F h.2
            ∂(M.law.map (histStateView rm))) := by
              cases hepoch
              change (∫ h, liftStateHistoryFunction rm hrm
                    (iterLiftStateHistoryFunction r G m (by omega)) h *
                    stateHistoryRatioBlock M lo (nextEpoch rm hrm) h * F h.2
                    ∂(M.law.map (histStateView (nextEpoch rm hrm)))) = _
              exact hs
        _ = (∫ h, G h * stateHistoryRatioBlock M lo r h *
              markovOperatorIter (policyKernel M M.e) m
                (markovOperator (policyKernel M M.e) F) h.2
            ∂(M.law.map (histStateView r))) := hrec
        _ = _ := by rw [markovOperatorIter_one_right]

/-- Complete backward peeling: terminal reward, target-policy ratio block, then behavior gap.
All analytic obligations are explicit and no conditional-expectation primitive is required. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h G condition](hyp:hG); and [the horizon condition](hyp:horizon); and [the hbehavior condition](hyp:hbehavior); and [the htarget condition](hyp:htarget); and [the hterminal Full condition](hyp:hterminalFull); and [the hterminal Action condition](hyp:hterminalAction). [the stated conclusion](goal). -/
lemma integral_futureScore_peeling
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M)
    (r : Fin T) (G : StateHistoryView T nX nH r → ℝ) (hG : Measurable G)
    (gap k : Nat) (horizon : r.val + gap + k < T)
    (hbehavior : ∀ i (hi : i < gap),
      let ri := epochAdd r i (by omega)
      let Gi := iterLiftStateHistoryFunction r G i (by omega)
      let Fi := markovOperatorIter (policyKernel M M.b) (gap - i - 1)
        (markovOperatorIter (policyKernel M M.e) k (rewardRegression M))
      Integrable (fun z : ActionHistoryView T nX nH ri × Step nX nH ↦
        Gi z.1.1 * Fi z.2.2) (M.law.map (histNextPair ri)) ∧
      Integrable (fun z : StateHistoryView T nX nH ri × Bool ↦
        Gi z.1 * ∫ y, Fi y.2 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair ri)))
    (htarget : ∀ i (hi : i < k),
      let q := epochAdd r gap (by omega)
      let qi := epochAdd q i (by dsimp [q, epochAdd]; omega)
      let Gq := iterLiftStateHistoryFunction r G gap (by omega)
      let Gi := iterLiftStateHistoryFunction q Gq i (by dsimp [q, epochAdd]; omega)
      let Fi := markovOperatorIter (policyKernel M M.e) (k - i - 1)
        (rewardRegression M)
      Integrable (fun z : ActionHistoryView T nX nH qi × Step nX nH ↦
        (Gi z.1.1 * stateHistoryRatioBlock M q.val qi z.1.1) *
          ratio M.b M.e (currentObsState qi z.1.1) z.1.2 * Fi z.2.2)
        (M.law.map (histNextPair qi)) ∧
      Integrable (fun z : StateHistoryView T nX nH qi × Bool ↦
        (Gi z.1 * stateHistoryRatioBlock M q.val qi z.1) *
          ∫ y, Fi y.2 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair qi)))
    (hterminalFull :
      let q := epochAdd r gap (by omega)
      let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
      let Gq := iterLiftStateHistoryFunction r G gap (by omega)
      let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
      Integrable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
        (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
          ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1)
        (M.law.map (histNextPair u)))
    (hterminalAction :
      let q := epochAdd r gap (by omega)
      let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
      let Gq := iterLiftStateHistoryFunction r G gap (by omega)
      let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
      Integrable (fun z : StateHistoryView T nX nH u × Bool ↦
        (Gu z.1 * stateHistoryRatioBlock M q.val u z.1) *
          ∫ y, y.1 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair u))) :
    let q := epochAdd r gap (by omega)
    let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
    let Gq := iterLiftStateHistoryFunction r G gap (by omega)
    let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
    ∫ z, (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
        ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1
        ∂(M.law.map (histNextPair u)) =
      ∫ h, G h * phiwFutureFunction M gap k h.2
        ∂(M.law.map (histStateView r)) := by
  dsimp only
  let q := epochAdd r gap (by omega)
  let Gq := iterLiftStateHistoryFunction r G gap (by omega)
  let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
  let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
  have hterm := integral_history_mul_ratio_reward hign hoverlap (zero_le_one.trans hL) hK u
    (fun h ↦ Gu h * stateHistoryRatioBlock M q.val u h)
    hterminalFull hterminalAction
  have ht := integral_iterLift_mul_targetRatioBlock hign hoverlap (zero_le_one.trans hL) hK q.val q
    (le_refl q.val) Gq
    (measurable_iterLiftStateHistoryFunction r G hG gap (by omega))
    (rewardRegression M) k (by dsimp [q, epochAdd]; omega) htarget
  have hb := integral_iterLift_mul_behavior hign hK r G hG
    (markovOperatorIter (policyKernel M M.e) k (rewardRegression M))
    gap (by omega) hbehavior
  calc
    _ = ∫ h, Gu h * stateHistoryRatioBlock M q.val u h * rewardRegression M h.2
          ∂(M.law.map (histStateView u)) := by simpa [mul_assoc] using hterm
    _ = ∫ h, Gq h * stateHistoryRatioBlock M q.val q h *
          markovOperatorIter (policyKernel M M.e) k (rewardRegression M) h.2
          ∂(M.law.map (histStateView q)) := ht
    _ = ∫ h, Gq h *
          markovOperatorIter (policyKernel M M.e) k (rewardRegression M) h.2
          ∂(M.law.map (histStateView q)) := by
      apply integral_congr_ae
      filter_upwards with h
      rw [stateHistoryRatioBlock_eq_one_of_le M q.val q (le_refl q.val) h]
      ring
    _ = _ := by simpa [phiwFutureFunction] using hb

/-- The complete peeling identity with all intermediate obligations discharged from
integrability of the initial past carrier and the unit reward bound. [the hign condition](hyp:hign); and [the hoverlap condition](hyp:hoverlap); and [the h L condition](hyp:hL); and [the h K condition](hyp:hK); and [the h Y condition](hyp:hY); and [the h Gm condition](hyp:hGm); and [the h Gi condition](hyp:hGi); and [the horizon condition](hyp:horizon); and [the hterminal Full condition](hyp:hterminalFull); and [the hterminal Action condition](hyp:hterminalAction). [the stated conclusion](goal). -/
lemma integral_futureScore_peeling_of_integrable
    {T nX nH : Nat} {M : RawPomdpExperiment T nX nH} {L : ℝ}
    (hign : SequentialIgnorability M) (hoverlap : PolicyOverlap L M)
    (hL : 1 ≤ L) (hK : PomdpKernelLaw M) (hY : BoundedReward M)
    (r : Fin T) (G : StateHistoryView T nX nH r → ℝ) (hGm : Measurable G)
    (hGi : Integrable G (M.law.map (histStateView r)))
    (gap k : Nat) (horizon : r.val + gap + k < T)
    (hterminalFull :
      let q := epochAdd r gap (by omega)
      let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
      let Gq := iterLiftStateHistoryFunction r G gap (by omega)
      let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
      Integrable (fun z : ActionHistoryView T nX nH u × Step nX nH ↦
        (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
          ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1)
        (M.law.map (histNextPair u)))
    (hterminalAction :
      let q := epochAdd r gap (by omega)
      let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
      let Gq := iterLiftStateHistoryFunction r G gap (by omega)
      let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
      Integrable (fun z : StateHistoryView T nX nH u × Bool ↦
        (Gu z.1 * stateHistoryRatioBlock M q.val u z.1) *
          ∫ y, y.1 ∂(M.K z.1.2 z.2))
        (M.law.map (histActionPair u))) :
    let q := epochAdd r gap (by omega)
    let u := epochAdd q k (by dsimp [q, epochAdd]; omega)
    let Gq := iterLiftStateHistoryFunction r G gap (by omega)
    let Gu := iterLiftStateHistoryFunction q Gq k (by dsimp [q, epochAdd]; omega)
    ∫ z, (Gu z.1.1 * stateHistoryRatioBlock M q.val u z.1.1) *
        ratio M.b M.e (currentObsState u z.1.1) z.1.2 * z.2.1
        ∂(M.law.map (histNextPair u)) =
      ∫ h, G h * phiwFutureFunction M gap k h.2
        ∂(M.law.map (histStateView r)) := by
  apply integral_futureScore_peeling hign hoverlap hL hK r G hGm gap k horizon
  · intro i hi
    let ri := epochAdd r i (by omega)
    let Gi := iterLiftStateHistoryFunction r G i (by omega)
    let Fi := markovOperatorIter (policyKernel M M.b) (gap - i - 1)
      (markovOperatorIter (policyKernel M M.e) k (rewardRegression M))
    have hGii : Integrable Gi (M.law.map (histStateView ri)) :=
      integrable_iterLiftStateHistoryFunction hign hK r G hGm hGi i (by omega)
    apply integrable_behaviorPeel_obligations hign hK ri Gi
      (measurable_iterLiftStateHistoryFunction r G hGm i (by omega)) hGii Fi
    intro s
    exact Finset.single_le_sum (fun x _ ↦ abs_nonneg (Fi x)) (Finset.mem_univ s)
  · intro i hi
    let q := epochAdd r gap (by omega)
    let qi := epochAdd q i (by dsimp [q, epochAdd]; omega)
    let Gq := iterLiftStateHistoryFunction r G gap (by omega)
    let Gi := iterLiftStateHistoryFunction q Gq i (by dsimp [q, epochAdd]; omega)
    let Fi := markovOperatorIter (policyKernel M M.e) (k - i - 1)
      (rewardRegression M)
    have hGqi : Integrable Gq (M.law.map (histStateView q)) :=
      integrable_iterLiftStateHistoryFunction hign hK r G hGm hGi gap (by omega)
    have hGii : Integrable Gi (M.law.map (histStateView qi)) :=
      integrable_iterLiftStateHistoryFunction hign hK q Gq
        (measurable_iterLiftStateHistoryFunction r G hGm gap (by omega)) hGqi i
        (by dsimp [q, epochAdd]; omega)
    apply integrable_targetPeel_obligations hign hoverlap hL hK q.val qi Gi
      (measurable_iterLiftStateHistoryFunction q Gq
        (measurable_iterLiftStateHistoryFunction r G hGm gap (by omega)) i
        (by dsimp [q, epochAdd]; omega)) hGii Fi
    intro s
    exact Finset.single_le_sum (fun x _ ↦ abs_nonneg (Fi x)) (Finset.mem_univ s)
  · exact hterminalFull
  · exact hterminalAction

end CausalSmith.Stat.PomdpLatentOverlapMinimax
