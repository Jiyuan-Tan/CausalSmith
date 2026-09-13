import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinCoordinateEvidence
import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinPrimitiveCertificates

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open scoped BigOperators
open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

set_option maxRecDepth 1000000 in
/-- [the insulin Chunk Indices pairwise assertion holds](goal). -/
theorem insulinChunkIndices_pairwise :
    (List.ofFn insulinChunkIndices).Pairwise (fun s t => Disjoint s t) := by
  unfold insulinChunkIndices insulinChunkEmbedding insulinJointEquiv
  decide +kernel

set_option maxRecDepth 1000000 in
/-- [the insulin Chunk Indices cover assertion holds](goal). -/
theorem insulinChunkIndices_cover :
    (List.ofFn insulinChunkIndices).foldr (fun s acc => s ∪ acc) ∅ =
      (Finset.univ : Finset (JointState 90 4)) := by
  unfold insulinChunkIndices insulinChunkEmbedding insulinJointEquiv
  decide +kernel

/-- For [the target input](hyp:target), [the j input](hyp:j), [the checked input](hyp:checked), [the c input](hyp:c), [this defines the insulin Certified Chunk object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3); and [defining clause 4](step:4). -/
def insulinCertifiedChunk (target : Bool) (j : Fin 360)
    (checked : InsulinCoordinateChecked target j) (c : Fin 9) :
    CertifiedChunk
      (fun s => (insulinGeneratedTrace target 0 s).mul
        (insulinPolicyIntervalMatrix target s (insulinJointEquiv.symm j))) 40 where
  indices := insulinChunkIndices c
  bound := insulinChunkBound10 target j c
  size_le := insulinChunkIndices_card c
  checked := by
    rw [insulinChunkSum_eq]
    exact checked.1 c

/-- For [the target input](hyp:target), [the j input](hyp:j), [the checked input](hyp:checked), [this defines the insulin Coordinate Dot Certificate object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3); and [defining clause 4](step:4). -/
def insulinCoordinateDotCertificate (target : Bool) (j : Fin 360)
    (checked : InsulinCoordinateChecked target j) :
    ChunkedDotCertificate (insulinGeneratedTrace target 0)
      (fun s => insulinPolicyIntervalMatrix target s (insulinJointEquiv.symm j))
      40 (insulinTraceInterval target 1 j) where
  chunks := List.ofFn (insulinCertifiedChunk target j checked)
  pairwise_disjoint := by
    change (List.ofFn insulinChunkIndices).Pairwise (fun s t => Disjoint s t)
    exact insulinChunkIndices_pairwise
  covers := by
    change (List.ofFn insulinChunkIndices).foldr (fun s acc => s ∪ acc) ∅ = Finset.univ
    exact insulinChunkIndices_cover
  assembly := by
    apply intervalFoldCertificateOfSubinterval
    exact checked.2

/-- For [the target input](hyp:target), [this defines the insulin Recurrence Certificate object](goal). -/
def insulinRecurrenceCertificate (target : Bool) :
    CoordinateRecurrenceCertificate (insulinPolicyIntervalMatrix target)
      (insulinGeneratedTrace target 0) (insulinGeneratedTrace target 1) 40 where
  coordinate := by
    intro s
    change ChunkedDotCertificate (insulinGeneratedTrace target 0)
      (fun i => insulinPolicyIntervalMatrix target i s) 40
      (insulinTraceInterval target 1 (insulinJointEquiv s))
    simpa only [Equiv.symm_apply_apply] using
      insulinCoordinateDotCertificate target (insulinJointEquiv s)
        (insulinCoordinateChecked target (insulinJointEquiv s))

/-- For [the target input](hyp:target), [this defines the insulin Chunked Iterate Certificate object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3); and [defining clause 4](step:4); and [defining clause 5](step:5); and [defining clause 6](step:6). -/
def insulinChunkedIterateCertificate (target : Bool) :
    ChunkedFiniteIterateCertificate (insulinPolicyIntervalMatrix target)
      (insulinGeneratedInitial target) where
  steps := 0
  chunkSize := 40
  chunkSize_pos := by norm_num
  table := insulinGeneratedTrace target
  initial_checked := insulinGeneratedInitial_checked target
  recurrence := by
    intro k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    simpa using insulinRecurrenceCertificate target

/-- For [the target input](hyp:target), [this defines the insulin Generated Residual object](goal). -/
def insulinGeneratedResidual (target : Bool) : ℚ :=
  ∑ s : JointState 90 4,
    ((insulinGeneratedTrace target 0 s).sub
      (insulinGeneratedTrace target 1 s)).maxAbs

/-- [the insulin Generated Residual nonneg assertion holds](goal). -/
theorem insulinGeneratedResidual_nonneg (target : Bool) :
    0 ≤ insulinGeneratedResidual target := by
  exact Finset.sum_nonneg fun s _ =>
    le_max_of_le_left (abs_nonneg ((insulinGeneratedTrace target 0 s).sub
      (insulinGeneratedTrace target 1 s)).lo)

/-- For [the target input](hyp:target), [this defines the insulin Chunked Stationary Reward Interval object](goal). -/
def insulinChunkedStationaryRewardInterval (target : Bool) : RatInterval :=
  let radius := insulinGeneratedResidual target / (1 - 1 / 2)
  (intervalExpectation (insulinGeneratedTrace target 0) insulinRewardIntervals).expand
    radius (div_nonneg (insulinGeneratedResidual_nonneg target) (by norm_num))

set_option maxRecDepth 1000000 in
/-- [the insulin Chunked Stationary Reward Interval eq assertion holds](goal). -/
theorem insulinChunkedStationaryRewardInterval_eq (target : Bool) :
    stationaryRewardInterval
      (insulinChunkedIterateCertificate target).toFiniteIterateCertificate
      insulinRewardCertificate (1 / 2) insulinRho_nonneg insulinRho_lt_one =
        insulinChunkedStationaryRewardInterval target := by
  unfold stationaryRewardInterval stationaryErrorRadius finiteIterateResidualBound
    insulinChunkedStationaryRewardInterval insulinGeneratedResidual
    insulinChunkedIterateCertificate
    ChunkedFiniteIterateCertificate.toFiniteIterateCertificate
    FiniteIterateCertificate.terminal FiniteIterateCertificate.next
  simp only [insulinRewardCertificate, one_mul]
  rfl

/-- [this defines the insulin Bias Interval object](goal). -/
def insulinBiasInterval : RatInterval :=
  (insulinChunkedStationaryRewardInterval false).sub
    (insulinChunkedStationaryRewardInterval true)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- [the insulin Bias Interval bounds assertion holds](goal). -/
theorem insulinBiasInterval_bounds :
    -(6 / 1000 : ℚ) < insulinBiasInterval.lo ∧
      insulinBiasInterval.hi < -(58 / 10000 : ℚ) := by
  unfold insulinBiasInterval insulinChunkedStationaryRewardInterval
    insulinGeneratedResidual insulinGeneratedTrace insulinRewardIntervals
  decide +kernel

end CausalSmith.Stat.PomdpLatentOverlapMinimax
