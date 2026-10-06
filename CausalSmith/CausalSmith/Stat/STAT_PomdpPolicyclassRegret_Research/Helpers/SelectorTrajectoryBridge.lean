module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorBlockTails
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Structural trajectory bridge for selector blocks

This file packages an arbitrary-start observed segment as a Markov kernel and
proves the past-event inequality needed to use the one-block Chebyshev bound
chronologically.  The statement uses a composition product, so it avoids
choosing a regular conditional distribution.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
open scoped ENNReal

/-- The point mass at a finite state is a probability vector. For [the index subset](hyp:S) and
[the state](hyp:s), this establishes [the selector point probability vector result](goal). -/
-- @node: selector_point_probabilityVector
lemma selector_point_probabilityVector {S : Type*} [Fintype S] [DecidableEq S]
    (s : S) : ProbabilityVector (fun s' : S ↦ if s' = s then 1 else 0) := by
  constructor
  · intro s'
    by_cases hs : s' = s <;> simp [hs]
  · simp

/-- The observable structural segment begun at a specified finite state. -/
-- @node: selectorObservedSegmentStateKernel
@[no_expose]
noncomputable def selectorObservedSegmentStateKernel {T M n : Nat}
    (m : ModelIndex T M) (hFinite : FiniteState m) :
    Kernel (JointState m.nX m.nH) (ObsView n m.nX) :=
  Kernel.ofFunOfCountable fun s ↦ (segmentLaw m hFinite
    (fun s' ↦ if s' = s then 1 else 0) n).map obsProj

/-- Pull the structural segment kernel back along a measurable current-state
map on an arbitrary history carrier. -/
-- @node: selectorObservedSegmentKernel
@[no_expose]
noncomputable def selectorObservedSegmentKernel {T M n : Nat}
    (m : ModelIndex T M) (hFinite : FiniteState m) {H : Type*}
    [MeasurableSpace H] (start : H → JointState m.nX m.nH)
    (hstart : Measurable start) : Kernel H (ObsView n m.nX) :=
  Kernel.comap (selectorObservedSegmentStateKernel m hFinite (n := n)) start hstart

/-- Every history-indexed structural observed segment is probabilistic. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the sample size](hyp:n),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the model](hyp:m), and [the class assumption](hyp:hClass),
this establishes [the selector observed segment state kernel is markov result](goal). -/
-- @node: selectorObservedSegmentKernel_isMarkov
lemma selectorObservedSegmentStateKernel_isMarkov {T M n : Nat}
    (t0 zeta C : ℝ) (m : ModelIndex T M)
    (hClass : PolicyListClass t0 zeta C m)
    : IsMarkovKernel (selectorObservedSegmentStateKernel m hClass.finite_state
      (n := n)) := by
  constructor
  intro s
  exact observedSegmentLaw_isProbability m hClass.sequential_ignorability.1
    hClass.finite_state _ (selector_point_probabilityVector s) n

/-- A uniform future-event bound under a history-indexed Markov kernel multiplies the
probability of every measurable past event. For [the h](hyp:H), [the w](hyp:W),
[the mu](hyp:mu), [the kernel](hyp:κ), [the past](hyp:past), [the bad](hyp:bad),
[the past assumption](hyp:hpast), [the bad assumption](hyp:hbad), [the q](hyp:q), and
[the q assumption](hyp:hq), this establishes
[the selector comp prod past event bound result](goal). -/
-- @node: selector_compProd_past_event_le
lemma selector_compProd_past_event_le {H W : Type*}
    [MeasurableSpace H] [MeasurableSpace W]
    (mu : Measure H) [SFinite mu] (κ : Kernel H W) [IsMarkovKernel κ]
    (past : Set H) (bad : Set W) (hpast : MeasurableSet past)
    (hbad : MeasurableSet bad) (q : ℝ≥0∞) (hq : ∀ h, κ h bad ≤ q) :
    (mu ⊗ₘ κ) (past ×ˢ bad) ≤ q * mu past := by
  rw [Measure.compProd_apply_prod hpast hbad]
  calc
    (∫⁻ h in past, κ h bad ∂mu) ≤ ∫⁻ _h in past, q ∂mu := by
      exact lintegral_mono fun h ↦ hq h
    _ = q * mu past := by simp

/-- The model's one-epoch factorization gives a direct past-event inequality under the actual
full trajectory law. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the reward symbol](hyp:r), [the past](hyp:past), [the bad](hyp:bad),
[the past assumption](hyp:hpast), [the bad assumption](hyp:hbad), [the q](hyp:q), and
[the q assumption](hyp:hq), this establishes
[the selector actual step past event bound result](goal). -/
-- @node: selector_actual_step_past_event_le
lemma selector_actual_step_past_event_le {T M : Nat}
    (m : ModelIndex T M) (r : Fin T)
    (past : Set (ActionHistoryView T m.nX m.nH r))
    (bad : Set (Step m.nX m.nH))
    (hpast : MeasurableSet past) (hbad : MeasurableSet bad)
    (q : ℝ≥0∞)
    (hq : ∀ h : ActionHistoryView T m.nX m.nH r,
      m.Mx.K h.1.2 h.2 bad ≤ q) :
    (m.Mx.law.map (histNextPair r)) (past ×ˢ bad) ≤
      q * (m.Mx.law.map (histView r)) past := by
  change (m.Mx.toRawB.law.map (histNextPair r)) (past ×ˢ bad) ≤
    q * (m.Mx.toRawB.law.map (histView r)) past
  rw [m.kernel_law.2 r]
  letI : IsMarkovKernel (kernelOfK m.Mx.toRawB) :=
    ⟨fun sa ↦ m.kernel_law.1 sa.1 sa.2⟩
  letI : IsProbabilityMeasure m.Mx.law := m.Mx.law_isProbability
  have hhist : Measurable (@histView T m.nX m.nH r) := by
    unfold histView histActionPair histStateView curState actionAt prefixIndex
    fun_prop
  letI : IsProbabilityMeasure
      (m.Mx.law.map (@histView T m.nX m.nH r)) :=
    Measure.isProbabilityMeasure_map hhist.aemeasurable
  apply selector_compProd_past_event_le
    (m.Mx.law.map (histView r))
    (Kernel.comap (kernelOfK m.Mx.toRawB)
      (currentStateAction r) (measurable_currentStateAction r))
    past bad hpast hbad q
  intro h
  change m.Mx.K h.1.2 h.2 bad ≤ q
  exact hq h

/-- The arbitrary-start Chebyshev estimate remains valid after weighting by any measurable past
event in the structural trajectory composition product. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the sample size](hyp:n), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), [the model](hyp:m),
[the class assumption](hyp:hClass), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the candidate index](hyp:j),
[the history length](hyp:k), [the history length assumption](hyp:hk),
[the sample size assumption](hyp:hn), [the h](hyp:H), [the mu](hyp:mu), [the start](hyp:start),
[the past](hyp:past), [the start assumption](hyp:hstart), [the past assumption](hyp:hpast),
[the observed state](hyp:x), and [the observed state assumption](hyp:hx), this establishes
[the selector block chebyshev past event result](goal). -/
-- @node: selector_block_chebyshev_past_event
lemma selector_block_chebyshev_past_event {T M n : Nat} (t0 zeta C : ℝ)
    (m : ModelIndex T M) (hClass : PolicyListClass t0 zeta C m)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (j : Fin M)
    (k : Nat) (hk : 2 * k ≤ n) (hn : 4 ≤ n)
    {H : Type*} [MeasurableSpace H]
    (mu : Measure H) [SFinite mu]
    (start : H → JointState m.nX m.nH) (past : Set H)
    (hstart : Measurable start) (hpast : MeasurableSet past) (x : ℝ) (hx : 0 < x) :
    (mu ⊗ₘ selectorObservedSegmentKernel m hClass.finite_state
      (n := n) start hstart)
      (past ×ˢ {w | mixingAlpha t0 ^ k *
        (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
          |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|}) ≤
      ENNReal.ofReal (((1 + 2 / (policyFactor zeta - 1) +
        4 / (1 - mixingAlpha t0)) * policyFactor zeta ^ (k + 1) /
          (n - k : Nat)) / x ^ 2) * mu past := by
  let bad : Set (ObsView n m.nX) := {w | mixingAlpha t0 ^ k *
    (overlapRadius C + 1 / ((n - k : Nat) * (1 - mixingAlpha t0))) + x <
      |phiwRaw k m.Mx.b (m.Mx.E j) w - policyValue m j|}
  have hbad : MeasurableSet bad := by
    dsimp only [bad]
    apply measurableSet_lt measurable_const
    exact continuous_abs.measurable.comp
      ((show Measurable (phiwRaw k m.Mx.b (m.Mx.E j)) by
      unfold phiwRaw
      apply Measurable.const_mul
      apply Finset.measurable_sum
      intro t ht
      exact phiwScore_measurable (k := k) m.Mx.b (m.Mx.E j) t).sub_const _)
  letI : IsMarkovKernel (selectorObservedSegmentStateKernel m hClass.finite_state
      (n := n)) := selectorObservedSegmentStateKernel_isMarkov t0 zeta C m hClass
  letI : IsMarkovKernel (selectorObservedSegmentKernel m hClass.finite_state
      (n := n) start hstart) := by
    unfold selectorObservedSegmentKernel
    infer_instance
  apply selector_compProd_past_event_le mu
    (selectorObservedSegmentKernel m hClass.finite_state (n := n) start hstart)
    past bad hpast hbad _
  intro h
  rw [selectorObservedSegmentKernel, Kernel.comap_apply]
  exact selector_block_chebyshev t0 zeta C m hClass ht0 hzeta j k hk hn
    (fun s ↦ if s = start h then 1 else 0)
    (selector_point_probabilityVector (start h)) x hx

end CausalSmith.Stat.PomdpPolicyclassRegret
