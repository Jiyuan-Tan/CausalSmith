module
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinGridCore
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCertifiedInitial
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.False10
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinChunkData.True10

set_option linter.style.longLine false

/-! Proof-producing bounded recurrence certificates for the insulin-grid trace. -/

@[expose] public section

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators
open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- For [the target input](hyp:target), [this defines the insulin Generated Initial object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3). -/
def insulinGeneratedInitial (target : Bool) :
    RationalProbabilityVector (JointState 90 4) where
  value := fun s => (insulinCertifiedInitial target).value (insulinJointEquiv s)
  nonneg := fun s => (insulinCertifiedInitial target).nonneg (insulinJointEquiv s)
  sum_eq_one := by
    rw [← (insulinCertifiedInitial target).sum_eq_one]
    exact Fintype.sum_equiv insulinJointEquiv _ _ (fun _ => rfl)

/-- For [the target input](hyp:target), [the k input](hyp:k), [this defines the insulin Generated Trace object](goal). -/
def insulinGeneratedTrace (target : Bool) (k : Fin 2) :
    IntervalVector (JointState 90 4) :=
  fun s => insulinTraceInterval target k (insulinJointEquiv s)

/-- [the insulin Generated Initial checked assertion holds](goal). -/
theorem insulinGeneratedInitial_checked (target : Bool) : ∀ s,
    (RatInterval.point ((insulinGeneratedInitial target).value s)).Subinterval
      (insulinGeneratedTrace target 0 s) := by
  intro s
  exact insulinCertifiedInitial_checked target (insulinJointEquiv s)

/-- For [the target input](hyp:target), [the j input](hyp:j), [the c input](hyp:c), [this defines the insulin Generated Chunk Sum object](goal). -/
def insulinGeneratedChunkSum (target : Bool) (j : Fin 360) (c : Fin 9) :
    RatInterval :=
  intervalSum fun x : Fin 40 =>
    let i : Fin 360 := ⟨c.val * 40 + x.val, by omega⟩
    (insulinTraceInterval target 0 i).mul
      (insulinPolicyIntervalMatrix target
        (insulinJointEquiv.symm i) (insulinJointEquiv.symm j))

/-- For [the target input](hyp:target), [the j input](hyp:j), [the c input](hyp:c), [this defines the insulin Chunk Bound10 object](goal). -/
def insulinChunkBound10 (target : Bool) (j : Fin 360) (c : Fin 9) : RatInterval :=
  if target then (insulinTrueChunkStep10 j).get c
  else (insulinFalseChunkStep10 j).get c

/-- For [the target input](hyp:target), [the j input](hyp:j), [this defines the Insulin Coordinate Checked object](goal). [defining clause 1](step:1); and [defining clause 2](step:2). -/
def InsulinCoordinateChecked (target : Bool) (j : Fin 360) : Prop :=
  (∀ c : Fin 9,
    (insulinChunkBound10 target j c).lo ≤
        (insulinGeneratedChunkSum target j c).lo ∧
      (insulinGeneratedChunkSum target j c).hi ≤
        (insulinChunkBound10 target j c).hi) ∧
  ((insulinTraceInterval target 1 j).lo ≤
      (List.ofFn fun c : Fin 9 => insulinChunkBound10 target j c).sum.lo ∧
    (List.ofFn fun c : Fin 9 => insulinChunkBound10 target j c).sum.hi ≤
      (insulinTraceInterval target 1 j).hi)

/-- For [the c input](hyp:c), [this defines the insulin Chunk Embedding object](goal). [defining clause 1](step:1); and [defining clause 2](step:2). -/
def insulinChunkEmbedding (c : Fin 9) : Fin 40 ↪ JointState 90 4 where
  toFun x := insulinJointEquiv.symm ⟨c.val * 40 + x.val, by omega⟩
  inj' := by
    intro x y h
    apply Fin.ext
    have h' := insulinJointEquiv.symm.injective h
    have hval := congrArg Fin.val h'
    exact Nat.add_left_cancel hval

/-- For [the c input](hyp:c), [this defines the insulin Chunk Indices object](goal). -/
def insulinChunkIndices (c : Fin 9) : Finset (JointState 90 4) :=
  Finset.univ.map (insulinChunkEmbedding c)

/-- [the insulin Chunk Indices card assertion holds](goal). -/
theorem insulinChunkIndices_card (c : Fin 9) :
    (insulinChunkIndices c).card ≤ 40 := by
  simp [insulinChunkIndices]

/-- [the insulin Chunk Sum eq assertion holds](goal). -/
theorem insulinChunkSum_eq (target : Bool) (j : Fin 360) (c : Fin 9) :
    (∑ s ∈ insulinChunkIndices c,
      (insulinGeneratedTrace target 0 s).mul
        (insulinPolicyIntervalMatrix target s (insulinJointEquiv.symm j))) =
      insulinGeneratedChunkSum target j c := by
  unfold insulinChunkIndices insulinGeneratedChunkSum intervalSum
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro x _
  change
    (insulinGeneratedTrace target 0
      (insulinJointEquiv.symm ⟨c.val * 40 + x.val, by omega⟩)).mul
        (insulinPolicyIntervalMatrix target
          (insulinJointEquiv.symm ⟨c.val * 40 + x.val, by omega⟩)
          (insulinJointEquiv.symm j)) = _
  simp only [insulinGeneratedTrace, Equiv.apply_symm_apply]

/-- For [the xs input](hyp:xs), [the output input](hyp:output), [the h input](hyp:h), [this defines the interval Fold Certificate Of Subinterval object](goal). -/
def intervalFoldCertificateOfSubinterval (xs : List RatInterval)
    (output : RatInterval) (h : xs.sum.Subinterval output) :
    IntervalFoldCertificate xs output := by
  cases xs with
  | nil => exact .nil h
  | cons head tail =>
      exact .cons (intervalFoldCertificateOfSubinterval tail tail.sum
        (RatInterval.subinterval_refl _)) h
termination_by xs.length

end CausalSmith.Stat.PomdpLatentOverlapMinimax
