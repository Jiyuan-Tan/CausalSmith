module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.BlockPathWeights

/-!
# Head-tail decomposition of structural selector segments

The structural path recursion can be pushed forward to expose its first step
and the remaining generated suffix.  This is the local decomposition needed
to transport complete-history coordinates through `decodeSegment`.
-/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory ProbabilityTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- Splitting a generated list into its padded head and tail is measurable. For
[the first event](hyp:A) and [the fallback state](hyp:fallback), this establishes
[the segment list head tail measurability result](goal). -/
@[fun_prop]
-- @node: segment_list_headTail_measurable
lemma segment_list_headTail_measurable {A : Type*} [MeasurableSpace A]
    (fallback : A) :
    Measurable (fun path : List A ↦ (path.getD 0 fallback, path.drop 1)) := by
  exact (segment_list_getD_measurable 0 fallback).prodMk
    (segment_list_drop_measurable 1)

/-- Taking a finite prefix preserves the coordinate-generated list sigma algebra. For
[the first event](hyp:A) and [the history length](hyp:k), this establishes
[the segment list take measurability result](goal). -/
@[fun_prop]
-- @node: segment_list_take_measurable
lemma segment_list_take_measurable {A : Type*} [MeasurableSpace A] (k : Nat) :
    Measurable (fun path : List A ↦ path.take k) := by
  apply measurable_generateFrom
  rintro _ ⟨j, B, hB, rfl⟩
  by_cases hj : j < k
  · have hcoord : MeasurableSet {l : List A | ∃ a ∈ B, l[j]? = some a} :=
      MeasurableSpace.measurableSet_generateFrom ⟨j, B, hB, rfl⟩
    convert hcoord using 1
    ext l
    simp [hj]
  · convert MeasurableSet.empty using 1
    ext l
    simp [hj]

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

/-- A positive-length fixed-start structural segment splits into its first joint step and the
suffix generated from that step's successor state. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n), and [the state](hyp:s), this
establishes [the segment from map head tail result](goal). -/
-- @node: segmentFrom_map_headTail
lemma segmentFrom_map_headTail {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n : Nat) (s : JointState m.nX m.nH) :
    (segmentFrom m (n + 1) s).map
        (fun path ↦ (path.getD 0 (false, 0, s), path.drop 1)) =
      (segmentStepLaw m s).bind (fun step ↦
        (segmentFrom m n step.2.2).map (fun tail ↦ (step, tail))) := by
  let split := fun path : List (Bool × ℝ × JointState m.nX m.nH) ↦
    (path.getD 0 (false, 0, s), path.drop 1)
  have hsplit : Measurable split := segment_list_headTail_measurable _
  have hdirac : Measurable (fun path : List (Bool × ℝ × JointState m.nX m.nH) ↦
      Measure.dirac (split path)) := by fun_prop
  rw [← Measure.bind_dirac_eq_map _ hsplit, segmentFrom,
    Measure.bind_bind (segmentFrom_cons_family_measurable m hb n).aemeasurable
      hdirac.aemeasurable]
  apply Measure.bind_congr_right
  filter_upwards [] with step
  have hcons : Measurable
      (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦ step :: tail) :=
    segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))
  rw [Measure.bind_dirac_eq_map _ hsplit, Measure.map_map hsplit hcons]
  apply Measure.map_congr
  filter_upwards [] with tail
  simp [split]

/-- Truncating a fixed-start generated path to its first `k` steps recovers the structural
`k`-step law, independently of the discarded future. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the model](hyp:m),
[the behavior policy assumption](hyp:hb), [the sample size](hyp:n), [the history length](hyp:k),
[the history length assumption](hyp:hk), and [the state](hyp:s), this establishes
[the segment from map take result](goal). -/
-- @node: segmentFrom_map_take
lemma segmentFrom_map_take {T M : Nat} (m : ModelIndex T M)
    (hb : PolicyVector m.Mx.b) (n k : Nat) (hk : k ≤ n)
    (s : JointState m.nX m.nH) :
    (segmentFrom m n s).map (fun path ↦ path.take k) = segmentFrom m k s := by
  induction n generalizing k s with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp only [segmentFrom]
      change Measure.map
        (fun _ : List (Bool × ℝ × JointState m.nX m.nH) ↦
          ([] : List (Bool × ℝ × JointState m.nX m.nH)))
        (Measure.dirac []) = Measure.dirac []
      rw [Measure.map_const]
      simp
  | succ n ih =>
      cases k with
      | zero =>
          change (segmentFrom m (n + 1) s).map (fun _ ↦ []) = Measure.dirac []
          rw [Measure.map_const]
          have : IsProbabilityMeasure (segmentFrom m (n + 1) s) :=
            segmentFrom_isProbability m hb (n + 1) s
          simp
      | succ k =>
          rw [segmentFrom, segmentFrom]
          rw [map_bind_eq_bind_map _ _ _
            (segmentFrom_cons_family_measurable m hb n).aemeasurable
            (segment_list_take_measurable (k + 1))]
          apply Measure.bind_congr_right
          filter_upwards [] with step
          have hcons : Measurable
              (fun tail : List (Bool × ℝ × JointState m.nX m.nH) ↦ step :: tail) :=
            segment_list_cons_measurable.comp (measurable_prodMk_left (x := step))
          rw [Measure.map_map (segment_list_take_measurable (k + 1)) hcons]
          have htake : ((fun path : List (Bool × ℝ × JointState m.nX m.nH) ↦
              path.take (k + 1)) ∘ fun tail ↦ step :: tail) =
              (fun tail ↦ step :: tail.take k) := by
            funext tail
            simp
          rw [htake]
          change Measure.map
              ((fun tail ↦ step :: tail) ∘ (fun path ↦ path.take k))
              (segmentFrom m n step.2.2) =
            Measure.map (fun tail ↦ step :: tail) (segmentFrom m k step.2.2)
          rw [← Measure.map_map hcons (segment_list_take_measurable k),
            ih k (by omega) step.2.2]

end CausalSmith.Stat.PomdpPolicyclassRegret
