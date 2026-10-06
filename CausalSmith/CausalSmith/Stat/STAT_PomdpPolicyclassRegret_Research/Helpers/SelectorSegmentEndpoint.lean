module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorSegmentSplit
public import Mathlib.Data.List.GetD

/-!
# Endpoint extension of structural selector segments

Fixed-length normalization gives a measurable snoc operation for the
coordinate-generated list sigma algebra.  It is used to expose the final
transition of the head-recursive structural path law.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Append one value after the first `n` padded coordinates of a list. -/
def segmentSnocFixed {A : Type*} : Nat → A → List A → A → List A
  | 0, _, _, a => [a]
  | n + 1, fallback, xs, a =>
      xs.getD 0 fallback ::
        segmentSnocFixed n fallback (xs.drop 1) a

/-- Fixed-length snoc is measurable in the prefix and appended value. For
[the first event](hyp:A), [the sample size](hyp:n), and [the fallback state](hyp:fallback), this
establishes [the segment snoc fixed measurability result](goal). -/
@[fun_prop]
-- @node: segmentSnocFixed_measurable
lemma segmentSnocFixed_measurable {A : Type*} [MeasurableSpace A]
    (n : Nat) (fallback : A) :
    Measurable (fun p : List A × A ↦ segmentSnocFixed n fallback p.1 p.2) := by
  induction n with
  | zero =>
      change Measurable (fun p : List A × A ↦ p.2 :: [])
      exact segment_list_cons_measurable.comp
        (measurable_snd.prodMk (measurable_const : Measurable fun _ : List A × A ↦ ([] : List A)))
  | succ n ih =>
      change Measurable (fun p : List A × A ↦
        p.1.getD 0 fallback :: segmentSnocFixed n fallback (p.1.drop 1) p.2)
      exact segment_list_cons_measurable.comp
        (((segment_list_getD_measurable 0 fallback).comp measurable_fst).prodMk
          (ih.comp (((segment_list_drop_measurable 1).comp measurable_fst).prodMk
            measurable_snd)))

/-- On an exact-length prefix, fixed-length snoc is ordinary append. For
[the first event](hyp:A), [the sample size](hyp:n), [the fallback state](hyp:fallback),
[the xs](hyp:xs), [the action](hyp:a), and [the len assumption](hyp:hlen), this establishes
[the segment snoc fixed equality append result](goal). -/
-- @node: segmentSnocFixed_eq_append
lemma segmentSnocFixed_eq_append {A : Type*} (n : Nat) (fallback : A)
    (xs : List A) (a : A) (hlen : xs.length = n) :
    segmentSnocFixed n fallback xs a = xs ++ [a] := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => rfl
      | cons b tail => simp at hlen
  | succ n ih =>
      cases xs with
      | nil => simp at hlen
      | cons b tail =>
          simp only [segmentSnocFixed, List.getD_cons_zero, List.drop_succ_cons,
            List.drop_zero, List.cons_append, List.cons.injEq]
          constructor
          · trivial
          · apply ih tail
            simpa using hlen

/-- State reached after the first `n` padded steps of a path. -/
def segmentPathEnd {S : Type*} :
    Nat → (Bool × ℝ × S) → S → List (Bool × ℝ × S) → S
  | 0, _, s, _ => s
  | n + 1, fallback, s, path =>
      segmentPathEnd n fallback
        (path.getD 0 fallback).2.2 (path.drop 1)

/-- The fixed-horizon endpoint is jointly measurable in the initial state and path when the
state alphabet is countable. For [the index subset](hyp:S), [the sample size](hyp:n), and
[the fallback state](hyp:fallback), this establishes
[the segment path end measurability result](goal). -/
@[fun_prop]
-- @node: segmentPathEnd_measurable
lemma segmentPathEnd_measurable {S : Type*} [MeasurableSpace S] [Countable S]
    (n : Nat) (fallback : Bool × ℝ × S) :
    Measurable (fun p : S × List (Bool × ℝ × S) ↦
      segmentPathEnd n fallback p.1 p.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
      exact ih.comp
        ((((segment_list_getD_measurable 0 fallback).comp measurable_snd).snd.snd).prodMk
          ((segment_list_drop_measurable 1).comp measurable_snd))

/-- Endpoint recursion agrees with removing a present first step. For [the index subset](hyp:S),
[the sample size](hyp:n), [the fallback state](hyp:fallback), [the state](hyp:s),
[the step](hyp:step), and [the tail](hyp:tail), this establishes
[the segment path end cons result](goal). -/
-- @node: segmentPathEnd_cons
lemma segmentPathEnd_cons {S : Type*} (n : Nat) (fallback : Bool × ℝ × S)
    (s : S) (step : Bool × ℝ × S) (tail : List (Bool × ℝ × S)) :
    segmentPathEnd (n + 1) fallback s (step :: tail) =
      segmentPathEnd n fallback step.2.2 tail := by
  rfl

/-- The recursively read path endpoint is the current state at the final epoch of the decoded
trajectory. For [the observed-state count](hyp:nX), [the hidden-state count](hyp:nH),
[the sample size](hyp:n), [the fallback state](hyp:fallback), [the state](hyp:s), and
[the xs](hyp:xs), this establishes
[the segment path end equality decode cur state result](goal). -/
-- @node: segmentPathEnd_eq_decode_curState
lemma segmentPathEnd_eq_decode_curState {nX nH : Nat} (n : Nat)
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH)) :
    segmentPathEnd n fallback s xs =
      curState (Fin.last n)
        (decodeSegment (n := n + 1) fallback.2.2 (s, xs)) := by
  induction n generalizing s xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil =>
          simp only [segmentPathEnd, List.getD_nil, List.drop_nil]
          rw [ih fallback.2.2 []]
          simp [curState, decodeSegment]
      | cons step tail =>
          simp only [segmentPathEnd, List.getD_cons_zero, List.drop_succ_cons,
            List.drop_zero]
          rw [ih step.2.2 tail]
          simp [curState, decodeSegment]
          cases n <;> simp

/-- The structural one-step measures form a Markov kernel on the finite full
state alphabet. -/
-- @node: segmentStepKernel
noncomputable def segmentStepKernel {T M : Nat} (m : ModelIndex T M) :
    Kernel (JointState m.nX m.nH)
      (Bool × ℝ × JointState m.nX m.nH) :=
  ⟨segmentStepLaw m, measurable_of_countable (segmentStepLaw m)⟩

-- @node: segmentStepKernel_isMarkov
/-- For [the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the model](hyp:m), and
[the behavior policy assumption](hyp:hb), this establishes
[the segment step kernel is markov result](goal). -/
lemma segmentStepKernel_isMarkov {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) : IsMarkovKernel (segmentStepKernel m) :=
  ⟨segmentStepLaw_isProbability m hb⟩

/-- Appending the final structural step after a normalized prefix is a measurable family of
measures. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the model](hyp:m), [the behavior policy assumption](hyp:hb), [the sample size](hyp:n),
[the fallback state](hyp:fallback), and [the state](hyp:s), this establishes
[the segment endpoint family measurability result](goal). -/
@[fun_prop]
-- @node: segmentEndpoint_family_measurable
lemma segmentEndpoint_family_measurable {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH) :
    Measurable (fun xs : List (Bool × ℝ × JointState m.nX m.nH) ↦
      (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
        (fun step ↦ segmentSnocFixed n fallback xs step)) := by
  letI : IsMarkovKernel (segmentStepKernel m) :=
    segmentStepKernel_isMarkov m hb
  let κ : Kernel (List (Bool × ℝ × JointState m.nX m.nH))
      (Bool × ℝ × JointState m.nX m.nH) :=
    (segmentStepKernel m).comap
      (fun xs ↦ segmentPathEnd n fallback s xs)
      ((segmentPathEnd_measurable n fallback).comp
        (measurable_const.prodMk measurable_id))
  letI : IsMarkovKernel κ := Kernel.IsMarkovKernel.comap _ _
  apply Measure.measurable_of_measurable_coe
  intro B hB
  have hsnoc : MeasurableSet
      ((fun p : List (Bool × ℝ × JointState m.nX m.nH) ×
        (Bool × ℝ × JointState m.nX m.nH) ↦
          segmentSnocFixed n fallback p.1 p.2) ⁻¹' B) :=
    segmentSnocFixed_measurable n fallback hB
  convert Kernel.measurable_kernel_prodMk_left (κ := κ) hsnoc using 1
  funext xs
  exact Measure.map_apply
    ((segmentSnocFixed_measurable n fallback).comp
      (measurable_prodMk_left (x := xs))) hB

private lemma map_dirac_of_measurable {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (f : A → B) (hf : Measurable f)
    (a : A) : (Measure.dirac a).map f = Measure.dirac (f a) := by
  rw [← Measure.bind_dirac_eq_map _ hf,
    Measure.dirac_bind (show Measurable (fun x ↦ Measure.dirac (f x)) by fun_prop)]

private lemma map_bind_eq_bind_map {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (κ : A → Measure B) (f : B → C)
    (hκ : AEMeasurable κ μ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun a ↦ (κ a).map f) := by
  have hdirac : Measurable (fun b ↦ Measure.dirac (f b)) := by fun_prop
  rw [← Measure.bind_dirac_eq_map _ hf, Measure.bind_bind hκ hdirac.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with a
  exact Measure.bind_dirac_eq_map (κ a) hf

private lemma bind_map_eq_bind_comp {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (f : A → B) (κ : B → Measure C)
    (hf : Measurable f) (hκ : Measurable κ) :
    (μ.map f).bind κ = μ.bind (κ ∘ f) := by
  have hdirac : Measurable (fun a ↦ Measure.dirac (f a)) := by fun_prop
  rw [← Measure.bind_dirac_eq_map _ hf,
    Measure.bind_bind hdirac.aemeasurable hκ.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with a
  rw [Measure.dirac_bind hκ]
  rfl

/-- A positive-length structural path law is obtained by drawing its exact prefix and then
appending one final structural step from the prefix endpoint. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n),
[the fallback state](hyp:fallback), and [the state](hyp:s), this establishes
[the segment from endpoint extension result](goal). -/
-- @node: segmentFrom_endpoint_extension
lemma segmentFrom_endpoint_extension {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat)
    (fallback : Bool × ℝ × JointState m.nX m.nH)
    (s : JointState m.nX m.nH) :
    segmentFrom m (n + 1) s =
      (segmentFrom m n s).bind (fun xs ↦
        (segmentStepLaw m (segmentPathEnd n fallback s xs)).map
          (fun step ↦ segmentSnocFixed n fallback xs step)) := by
  induction n generalizing s with
  | zero =>
      rw [segmentFrom, segmentFrom]
      rw [Measure.dirac_bind
        (segmentEndpoint_family_measurable m hb 0 fallback s)]
      have hsingle : Measurable
        (fun step : Bool × ℝ × JointState m.nX m.nH ↦
            segmentSnocFixed 0 fallback [] step) :=
        (segmentSnocFixed_measurable 0 fallback).comp
          ((show Measurable (fun _ : Bool × ℝ × JointState m.nX m.nH ↦
              ([] : List (Bool × ℝ × JointState m.nX m.nH))) from
            measurable_const).prodMk measurable_id)
      rw [← Measure.bind_dirac_eq_map _ hsingle]
      apply Measure.bind_congr_right
      filter_upwards [] with step
      have hcons : Measurable
          (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦ step :: tail) :=
        segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))
      change (Measure.dirac
          ([] : List (Bool × ℝ × JointState m.nX m.nH))).map
          (fun tail ↦ step :: tail) = Measure.dirac [step]
      rw [map_dirac_of_measurable _ hcons]
  | succ n ih =>
      rw [segmentFrom, segmentFrom]
      rw [Measure.bind_bind
        (segmentFrom_cons_family_measurable m hb n).aemeasurable
        (segmentEndpoint_family_measurable m hb (n + 1) fallback s).aemeasurable]
      apply Measure.bind_congr_right
      filter_upwards [] with first
      have hcons : Measurable
          (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦ first :: tail) :=
        segment_list_cons_measurable.comp (measurable_prodMk_left (x := first))
      rw [ih first.2.2]
      rw [map_bind_eq_bind_map _ _ _
        (segmentEndpoint_family_measurable m hb n fallback first.2.2).aemeasurable
        hcons]
      rw [bind_map_eq_bind_comp _ _ _ hcons
        (segmentEndpoint_family_measurable m hb (n + 1) fallback s)]
      apply Measure.bind_congr_right
      filter_upwards [] with tail
      have hsnoc : Measurable
          (fun final : Bool × ℝ × JointState m.nX m.nH ↦
            segmentSnocFixed n fallback tail final) :=
        (segmentSnocFixed_measurable n fallback).comp
          (measurable_prodMk_left (x := tail))
      change Measure.map (fun rest ↦ first :: rest)
          (Measure.map (fun final ↦ segmentSnocFixed n fallback tail final)
            (segmentStepLaw m (segmentPathEnd n fallback first.2.2 tail))) =
        Measure.map (fun final ↦ segmentSnocFixed (n + 1) fallback
            (first :: tail) final)
          (segmentStepLaw m
            (segmentPathEnd (n + 1) fallback s (first :: tail)))
      rw [Measure.map_map hcons hsnoc]
      apply Measure.map_congr
      filter_upwards [] with final
      rfl

/-- Appending the terminal step does not change the history available before that terminal
action. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the xs](hyp:xs), [the step](hyp:step), and [the len assumption](hyp:hlen), this establishes
[the segment snoc fixed hist state view result](goal). -/
-- @node: segmentSnocFixed_histStateView
lemma segmentSnocFixed_histStateView {n nX nH : Nat}
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH))
    (step : Bool × ℝ × JointState nX nH) (hlen : xs.length = n) :
    histStateView (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step)) =
      histStateView (Fin.last n) (decodeSegment fallback.2.2 (s, xs)) := by
  rw [segmentSnocFixed_eq_append n fallback xs step hlen]
  unfold histStateView
  apply Prod.ext
  · apply Prod.ext
    · funext j
      change curState (prefixIndex (Fin.last n) j)
          (decodeSegment fallback.2.2 (s, xs ++ [step])) =
        curState (prefixIndex (Fin.last n) j)
          (decodeSegment fallback.2.2 (s, xs))
      unfold curState decodeSegment prefixIndex
      simp only [Fin.val_castSucc]
      by_cases hj : j.val = 0
      · simp [hj]
      · simp only [hj, if_false]
        rw [List.getD_append xs [step] (false, 0, fallback.2.2)
          (j.val - 1) (by omega)]
    · funext j
      apply Prod.ext
      · change actionAt (prefixIndex (Fin.last n) j)
            (decodeSegment fallback.2.2 (s, xs ++ [step])) =
          actionAt (prefixIndex (Fin.last n) j)
            (decodeSegment fallback.2.2 (s, xs))
        unfold actionAt decodeSegment prefixIndex
        change ((xs ++ [step]).getD j.val (false, 0, fallback.2.2)).1 =
          (xs.getD j.val (false, 0, fallback.2.2)).1
        rw [List.getD_append xs [step] (false, 0, fallback.2.2)
          j.val (by omega)]
      · change rewardAt (prefixIndex (Fin.last n) j)
            (decodeSegment fallback.2.2 (s, xs ++ [step])) =
          rewardAt (prefixIndex (Fin.last n) j)
            (decodeSegment fallback.2.2 (s, xs))
        unfold rewardAt decodeSegment prefixIndex
        change ((xs ++ [step]).getD j.val (false, 0, fallback.2.2)).2.1 =
          (xs.getD j.val (false, 0, fallback.2.2)).2.1
        rw [List.getD_append xs [step] (false, 0, fallback.2.2)
          j.val (by omega)]
  · change curState (Fin.last n)
        (decodeSegment fallback.2.2 (s, xs ++ [step])) =
      curState (Fin.last n) (decodeSegment fallback.2.2 (s, xs))
    unfold curState decodeSegment
    simp only [Fin.val_castSucc, Fin.val_last]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [Fin.val_last, hn, if_false]
      rw [List.getD_append xs [step] (false, 0, fallback.2.2)
        (n - 1) (by omega)]

/-- Under fixed-length snoc, the terminal decoded action is the appended step's action
coordinate. For [the sample size](hyp:n), [the observed-state count](hyp:nX),
[the hidden-state count](hyp:nH), [the fallback state](hyp:fallback), [the state](hyp:s),
[the xs](hyp:xs), and [the step](hyp:step), this establishes
[the segment snoc fixed action at result](goal). -/
-- @node: segmentSnocFixed_actionAt
lemma segmentSnocFixed_actionAt {n nX nH : Nat}
    (fallback : Bool × ℝ × JointState nX nH) (s : JointState nX nH)
    (xs : List (Bool × ℝ × JointState nX nH))
    (step : Bool × ℝ × JointState nX nH) :
    actionAt (Fin.last n)
        (decodeSegment fallback.2.2
          (s, segmentSnocFixed n fallback xs step)) = step.1 := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
      cases xs with
      | nil => exact ih []
      | cons b tail => exact ih tail

end CausalSmith.Stat.PomdpPolicyclassRegret
