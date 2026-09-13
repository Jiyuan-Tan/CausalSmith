import Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic.Complex.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Finite rational interval linear algebra

This module lifts Causalean's exact rational scalar intervals to finite sums,
vectors, matrices, matrix products, and row-vector actions.  All computations
are performed on rational endpoints, while the soundness theorems relate the
computed intervals to real linear algebra.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- Rational intervals form an additive commutative monoid under outward
interval addition, with the point interval at zero as identity. -/
instance : AddCommMonoid RatInterval where
  zero := RatInterval.point 0
  add := RatInterval.add
  add_assoc := by
    intro I J K
    apply RatInterval.ext
    · change (I.lo + J.lo) + K.lo = I.lo + (J.lo + K.lo)
      exact add_assoc _ _ _
    · change (I.hi + J.hi) + K.hi = I.hi + (J.hi + K.hi)
      exact add_assoc _ _ _
  zero_add := by
    intro I
    apply RatInterval.ext
    · change 0 + I.lo = I.lo
      exact zero_add _
    · change 0 + I.hi = I.hi
      exact zero_add _
  add_zero := by
    intro I
    apply RatInterval.ext
    · change I.lo + 0 = I.lo
      exact add_zero _
    · change I.hi + 0 = I.hi
      exact add_zero _
  add_comm := by
    intro I J
    apply RatInterval.ext
    · change I.lo + J.lo = J.lo + I.lo
      exact add_comm _ _
    · change I.hi + J.hi = J.hi + I.hi
      exact add_comm _ _
  nsmul := fun n I => Nat.rec (RatInterval.point 0)
    (fun _ acc => RatInterval.add acc I) n
  nsmul_zero := by
    intro I
    rfl
  nsmul_succ := by
    intro n I
    rfl

/-- An interval vector assigns one exact rational interval to each coordinate. -/
abbrev IntervalVector (ι : Type*) := ι → RatInterval

/-- An interval matrix assigns one exact rational interval to each row and column. -/
abbrev IntervalMatrix (ι κ : Type*) := ι → κ → RatInterval

/-- An interval vector contains a real vector when it contains every coordinate. -/
def ContainsVector {ι : Type*} (I : IntervalVector ι) (x : ι → ℝ) : Prop :=
  ∀ i, (I i).Contains (x i)

/-- An interval matrix contains a real matrix when it contains every entry. -/
def ContainsMatrix {ι κ : Type*} (I : IntervalMatrix ι κ) (A : Matrix ι κ ℝ) : Prop :=
  ∀ i j, (I i j).Contains (A i j)

/-- Coordinatewise rational interval refinement for vectors. -/
def VectorSubinterval {ι : Type*} (I J : IntervalVector ι) : Prop :=
  ∀ i, (I i).Subinterval (J i)

/-- Coordinatewise rational interval refinement for matrices. -/
def MatrixSubinterval {ι κ : Type*} (I J : IntervalMatrix ι κ) : Prop :=
  ∀ i j, (I i j).Subinterval (J i j)

/-- The finite interval sum is the ordinary finite sum using outward interval addition. -/
def intervalSum {ι : Type*} [Fintype ι] (I : ι → RatInterval) : RatInterval :=
  ∑ i, I i

/-- The interval dot product sums outward products of corresponding coordinates. -/
def intervalDot {ι : Type*} [Fintype ι]
    (I J : IntervalVector ι) : RatInterval :=
  intervalSum fun i => (I i).mul (J i)

/-- Applying an interval matrix to an interval column vector uses interval dot products rowwise. -/
def intervalMulVec {ι κ : Type*} [Fintype κ]
    (A : IntervalMatrix ι κ) (x : IntervalVector κ) : IntervalVector ι :=
  fun i => intervalDot (A i) x

/-- Applying an interval row vector to an interval matrix uses interval dot products columnwise. -/
def intervalVecMul {ι κ : Type*} [Fintype ι]
    (x : IntervalVector ι) (A : IntervalMatrix ι κ) : IntervalVector κ :=
  fun j => intervalDot x (fun i => A i j)

/-- Interval matrix multiplication computes every entry by an interval dot product. -/
def intervalMatrixMul {ι κ υ : Type*} [Fintype κ]
    (A : IntervalMatrix ι κ) (B : IntervalMatrix κ υ) : IntervalMatrix ι υ :=
  fun i j => intervalDot (A i) (fun k => B k j)

/-- The interval reward expectation is the interval dot product of mass and reward vectors. -/
def intervalExpectation {ι : Type*} [Fintype ι]
    (mass reward : IntervalVector ι) : RatInterval :=
  intervalDot mass reward

/-- Finite outward interval addition contains the sum of any coordinatewise enclosed real family. -/
theorem intervalSum_sound {ι : Type*} [Fintype ι]
    {I : ι → RatInterval} {x : ι → ℝ}
    (hx : ∀ i, (I i).Contains (x i)) :
    (intervalSum I).Contains (∑ i, x i) := by
  classical
  unfold intervalSum
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · change (RatInterval.point 0).Contains (0 : ℝ)
    simpa only [Rat.cast_zero] using RatInterval.point_sound (0 : ℚ)
  · intro i s hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact RatInterval.add_sound (hx i) ih

/-- An interval dot product contains the real dot product of any two enclosed vectors. -/
theorem intervalDot_sound {ι : Type*} [Fintype ι]
    {I J : IntervalVector ι} {x y : ι → ℝ}
    (hx : ContainsVector I x) (hy : ContainsVector J y) :
    (intervalDot I J).Contains (∑ i, x i * y i) := by
  apply intervalSum_sound
  intro i
  exact RatInterval.mul_sound (hx i) (hy i)

/-- Interval matrix-vector multiplication contains the corresponding real matrix-vector product. -/
theorem intervalMulVec_sound {ι κ : Type*} [Fintype κ]
    {A : IntervalMatrix ι κ} {x : IntervalVector κ}
    {M : Matrix ι κ ℝ} {v : κ → ℝ}
    (hA : ContainsMatrix A M) (hx : ContainsVector x v) :
    ContainsVector (intervalMulVec A x) (Matrix.mulVec M v) := by
  intro i
  exact intervalDot_sound (hA i) hx

/-- Interval row-vector multiplication contains the corresponding real row-vector action. -/
theorem intervalVecMul_sound {ι κ : Type*} [Fintype ι]
    {x : IntervalVector ι} {A : IntervalMatrix ι κ}
    {v : ι → ℝ} {M : Matrix ι κ ℝ}
    (hx : ContainsVector x v) (hA : ContainsMatrix A M) :
    ContainsVector (intervalVecMul x A) (Matrix.vecMul v M) := by
  intro j
  exact intervalDot_sound hx (fun i => hA i j)

/-- When [the first rational interval matrix encloses a real matrix](hyp:hA) and [the second rational interval matrix encloses a real matrix](hyp:hB), [their interval matrix product encloses the corresponding real matrix product](goal). -/
theorem intervalMatrixMul_sound {ι κ υ : Type*} [Fintype κ]
    {A : IntervalMatrix ι κ} {B : IntervalMatrix κ υ}
    {M : Matrix ι κ ℝ} {N : Matrix κ υ ℝ}
    (hA : ContainsMatrix A M) (hB : ContainsMatrix B N) :
    ContainsMatrix (intervalMatrixMul A B) (M * N) := by
  intro i j
  exact intervalDot_sound (hA i) (fun k => hB k j)

/-- Coordinatewise refinement preserves containment of a real vector. -/
theorem ContainsVector.mono {ι : Type*} {I J : IntervalVector ι} {x : ι → ℝ}
    (hIJ : VectorSubinterval I J) (hx : ContainsVector I x) :
    ContainsVector J x := by
  intro i
  exact RatInterval.Contains.mono (hIJ i) (hx i)

/-- Coordinatewise refinement preserves containment of a real matrix. -/
theorem ContainsMatrix.mono {ι κ : Type*}
    {I J : IntervalMatrix ι κ} {A : Matrix ι κ ℝ}
    (hIJ : MatrixSubinterval I J) (hA : ContainsMatrix I A) :
    ContainsMatrix J A := by
  intro i j
  exact RatInterval.Contains.mono (hIJ i j) (hA i j)

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- Given [an inner rational interval](hyp:inner) and [an outer rational interval](hyp:outer), [the scalar subinterval check](goal) is [the exact endpoint comparison that accepts exactly when the inner interval lies inside the outer interval](step:1). -/
def scalarSubintervalCheck (inner outer : RatInterval) : Bool :=
  decide (outer.lo ≤ inner.lo ∧ inner.hi ≤ outer.hi)

/-- When [the scalar subinterval check accepts](hyp:h), [the inner interval is contained in the outer interval](goal). -/
theorem scalarSubintervalCheck_sound {inner outer : RatInterval}
    (h : scalarSubintervalCheck inner outer = true) :
    inner.Subinterval outer := by
  simpa [scalarSubintervalCheck, RatInterval.Subinterval] using (of_decide_eq_true h)

/-- A scalar interval certificate records that [an exact rational value](hyp:q) lies in [a reported rational interval](hyp:I), through [a checked point-interval refinement](hyp:checked). -/
structure ScalarIntervalCertificate (q : ℚ) (I : RatInterval) : Prop where
  /-- The point interval at the exact value refines the reported interval. -/
  checked : (RatInterval.point q).Subinterval I

/-- When [a scalar interval certificate is supplied](hyp:c), [its reported interval contains the certificate's rational value as a real number](goal). -/
theorem ScalarIntervalCertificate.sound {q : ℚ} {I : RatInterval}
    (c : ScalarIntervalCertificate q I) : I.Contains (q : ℝ) := by
  exact RatInterval.Contains.mono c.checked (RatInterval.point_sound q)

/-- A finite-vector certificate records independently checked scalar enclosures for [each coordinate of an exact rational vector](hyp:q) in [a rational interval vector](hyp:I), through [one certificate per coordinate](hyp:coordinate). -/
structure FiniteVectorCertificate {ι : Type*} [Fintype ι]
    (q : ι → ℚ) (I : IntervalVector ι) : Prop where
  /-- Independently checked certificate for each vector coordinate. -/
  coordinate : ∀ i, ScalarIntervalCertificate (q i) (I i)

/-- When [a finite-vector certificate is supplied](hyp:c), [the reported interval vector contains the real vector obtained from its rational coordinates](goal). -/
theorem FiniteVectorCertificate.sound {ι : Type*} [Fintype ι]
    {q : ι → ℚ} {I : IntervalVector ι} (c : FiniteVectorCertificate q I) :
    ContainsVector I (fun i => (q i : ℝ)) := by
  intro i
  exact (c.coordinate i).sound

/-- A finite-matrix certificate records independently checked scalar enclosures for [each entry of an exact rational matrix](hyp:q) in [a rational interval matrix](hyp:I), through [one certificate per entry](hyp:entry). -/
structure FiniteMatrixCertificate {ι κ : Type*} [Fintype ι] [Fintype κ]
    (q : Matrix ι κ ℚ) (I : IntervalMatrix ι κ) : Prop where
  /-- Independently checked certificate for each matrix entry. -/
  entry : ∀ i j, ScalarIntervalCertificate (q i j) (I i j)

/-- When [a finite-matrix certificate is supplied](hyp:c), [the reported interval matrix contains the real matrix obtained from its rational entries](goal). -/
theorem FiniteMatrixCertificate.sound {ι κ : Type*} [Fintype ι] [Fintype κ]
    {q : Matrix ι κ ℚ} {I : IntervalMatrix ι κ}
    (c : FiniteMatrixCertificate q I) :
    ContainsMatrix I (fun i j => (q i j : ℝ)) := by
  intro i j
  exact (c.entry i j).sound

/-- [An interval-fold certificate](goal) records a proof-producing binary assembly of a list of intervals into one output interval, with [the empty-list case](step:1) and [the one-more-interval case](step:2) checked separately. -/
inductive IntervalFoldCertificate : List RatInterval → RatInterval → Prop
  /-- The empty list is enclosed by any interval containing the point zero. -/
  | nil {output : RatInterval}
      (checked : (RatInterval.point 0).Subinterval output) :
      IntervalFoldCertificate [] output
  /-- A certified tail and one checked addition certify the interval-list sum. -/
  | cons {head tailBound output : RatInterval} {tail : List RatInterval}
      (tailCertificate : IntervalFoldCertificate tail tailBound)
      (checked : (head.add tailBound).Subinterval output) :
      IntervalFoldCertificate (head :: tail) output

/-- When [an interval-fold certificate is supplied](hyp:c), [the ordinary interval sum of its input list refines its reported output interval](goal). -/
theorem IntervalFoldCertificate.refines_sum {xs : List RatInterval}
    {output : RatInterval} (c : IntervalFoldCertificate xs output) :
    xs.sum.Subinterval output := by
  induction c with
  | nil checked =>
      change (RatInterval.point 0).Subinterval _
      exact checked
  | cons tailCertificate checked ih =>
      exact RatInterval.subinterval_trans
        (RatInterval.add_mono (RatInterval.subinterval_refl _) ih) checked

/-- Given [an interval-fold certificate](hyp:c) and [coordinatewise evidence that each input interval contains its corresponding real value](hyp:h), [the reported interval contains the sum of those real values](goal). -/
theorem IntervalFoldCertificate.contains_sum {xs : List RatInterval}
    {values : List ℝ} {output : RatInterval}
    (c : IntervalFoldCertificate xs output)
    (h : List.Forall₂ (fun I x => I.Contains x) xs values) :
    output.Contains values.sum := by
  induction c generalizing values with
  | nil checked =>
      cases h
      rw [List.sum_nil]
      simpa only [Rat.cast_zero] using
        RatInterval.Contains.mono checked (RatInterval.point_sound 0)
  | cons tailCertificate checked ih =>
      cases h with
      | cons hhead htail =>
          exact RatInterval.Contains.mono checked
            (RatInterval.add_sound hhead (ih htail))

/-- When [each interval in one list refines the corresponding interval in another list](hyp:h), [the sum of the first list refines the sum of the second](goal). -/
theorem listSum_subinterval {xs ys : List RatInterval}
    (h : List.Forall₂ RatInterval.Subinterval xs ys) :
    xs.sum.Subinterval ys.sum := by
  induction h with
  | nil => exact RatInterval.subinterval_refl _
  | cons hhead htail ih => exact RatInterval.add_mono hhead ih

/-- A certified chunk records a bounded partial interval sum of [a finite interval family](hyp:terms), with [the selected maximum chunk size](hyp:chunkSize), [its indices](hyp:indices), [its reported bound](hyp:bound), [a size proof](hyp:size_le), and [a local exact-sum refinement proof](hyp:checked). -/
structure CertifiedChunk {ι : Type*} [DecidableEq ι]
    (terms : ι → RatInterval) (chunkSize : ℕ) where
  /-- Indices assigned to this chunk. -/
  indices : Finset ι
  /-- Caller-supplied interval bound for this chunk. -/
  bound : RatInterval
  /-- The chunk contains no more than the selected number of terms. -/
  size_le : indices.card ≤ chunkSize
  /-- The exact interval sum for this chunk refines its reported bound. -/
  checked : (∑ i ∈ indices, terms i).Subinterval bound

/-- A chunked-sum certificate assembles [a finite interval family](hyp:terms) using [a selected chunk-size bound](hyp:chunkSize) into [a reported output interval](hyp:output), through [bounded chunk certificates](hyp:chunks), [their pairwise disjointness](hyp:pairwise_disjoint), [their exhaustive coverage](hyp:covers), and [a checked binary assembly](hyp:assembly). -/
structure ChunkedSumCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (terms : ι → RatInterval) (chunkSize : ℕ) (output : RatInterval) where
  /-- Independently checked bounded chunks. -/
  chunks : List (CertifiedChunk terms chunkSize)
  /-- No index is counted by two different chunks. -/
  pairwise_disjoint :
    (chunks.map (fun c => c.indices)).Pairwise (fun s t => Disjoint s t)
  /-- Every index occurs in some chunk. -/
  covers :
    (chunks.map (fun c => c.indices)).foldr (fun s acc => s ∪ acc) ∅ = Finset.univ
  /-- Chunk bounds are combined only through checked binary additions. -/
  assembly : IntervalFoldCertificate (chunks.map (fun c => c.bound)) output

/-- Given [a finite additive family](hyp:f), [a list of index chunks](hyp:chunks), [pairwise disjoint chunks](hyp:hdisjoint), and [chunks covering every index](hyp:hcovers), [the full finite sum equals the list sum of the chunk sums](goal). -/
theorem sum_eq_sum_chunks {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (f : ι → M) (chunks : List (Finset ι))
    (hdisjoint : chunks.Pairwise (fun s t => Disjoint s t))
    (hcovers : chunks.foldr (fun s acc => s ∪ acc) ∅ = Finset.univ) :
    ∑ i, f i = (chunks.map (fun s => ∑ i ∈ s, f i)).sum := by
  have disjoint_foldr (s : Finset ι) (cs : List (Finset ι))
      (h : ∀ t ∈ cs, Disjoint s t) :
      Disjoint s (cs.foldr (fun t acc => t ∪ acc) ∅) := by
    induction cs with
    | nil => simp
    | cons t ts ih =>
        rw [List.foldr_cons]
        exact Finset.disjoint_union_right.mpr
          ⟨h t (by simp), ih (fun u hu => h u (by simp [hu]))⟩
  have partition_sum (cs : List (Finset ι))
      (h : cs.Pairwise (fun s t => Disjoint s t)) :
      ∑ i ∈ cs.foldr (fun s acc => s ∪ acc) ∅, f i =
        (cs.map (fun s => ∑ i ∈ s, f i)).sum := by
    induction cs with
    | nil => simp
    | cons s cs ih =>
        obtain ⟨hs, hcs⟩ := List.pairwise_cons.mp h
        rw [List.foldr_cons, Finset.sum_union (disjoint_foldr s cs hs),
          List.map_cons, List.sum_cons, ih hcs]
  calc
    ∑ i, f i = ∑ i ∈ chunks.foldr (fun s acc => s ∪ acc) ∅, f i := by rw [hcovers]
    _ = (chunks.map (fun s => ∑ i ∈ s, f i)).sum := partition_sum chunks hdisjoint

/-- When [a chunked-sum certificate is supplied](hyp:c), [the complete interval sum refines its reported output interval](goal). -/
theorem ChunkedSumCertificate.sound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {terms : ι → RatInterval} {chunkSize : ℕ} {output : RatInterval}
    (c : ChunkedSumCertificate terms chunkSize output) :
    (intervalSum terms).Subinterval output := by
  have chunk_refinements (cs : List (CertifiedChunk terms chunkSize)) :
      List.Forall₂ RatInterval.Subinterval
        (cs.map (fun d => ∑ i ∈ d.indices, terms i))
        (cs.map (fun d => d.bound)) := by
    induction cs with
    | nil => exact .nil
    | cons d ds ih => exact .cons d.checked ih
  apply RatInterval.subinterval_trans ?_ c.assembly.refines_sum
  have hfull : intervalSum terms =
      (c.chunks.map (fun d => ∑ i ∈ d.indices, terms i)).sum := by
    simpa only [intervalSum, List.map_map, Function.comp_def] using
      sum_eq_sum_chunks terms (c.chunks.map (fun d => d.indices))
        c.pairwise_disjoint c.covers
  rw [hfull]
  exact listSum_subinterval (chunk_refinements c.chunks)

/-- Given [a chunked-sum certificate](hyp:c) and [coordinatewise interval containment of real summands](hyp:hvalues), [the reported interval contains their full real sum](goal). -/
theorem ChunkedSumCertificate.contains {ι : Type*} [Fintype ι] [DecidableEq ι]
    {terms : ι → RatInterval} {chunkSize : ℕ} {output : RatInterval}
    (c : ChunkedSumCertificate terms chunkSize output) {values : ι → ℝ}
    (hvalues : ∀ i, (terms i).Contains (values i)) :
    output.Contains (∑ i, values i) := by
  exact RatInterval.Contains.mono c.sound (intervalSum_sound hvalues)

/-- Given [left interval-vector factors](hyp:left), [right interval-vector factors](hyp:right), [a chunk-size bound](hyp:chunkSize), and [an output interval](hyp:output), [a chunked dot-product certificate](goal) is [the corresponding chunked certificate for outward interval products](step:1). -/
abbrev ChunkedDotCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (left right : IntervalVector ι) (chunkSize : ℕ) (output : RatInterval) :=
  ChunkedSumCertificate (fun i => (left i).mul (right i)) chunkSize output

/-- When [a chunked dot-product certificate is supplied](hyp:c), [the library interval dot product refines its reported coordinate interval](goal). -/
theorem ChunkedDotCertificate.sound {ι : Type*} [Fintype ι] [DecidableEq ι]
    {left right : IntervalVector ι} {chunkSize : ℕ} {output : RatInterval}
    (c : ChunkedDotCertificate left right chunkSize output) :
    (intervalDot left right).Subinterval output := by
  simpa only [intervalDot] using ChunkedSumCertificate.sound c

/-- Given [a chunked dot-product certificate](hyp:c), [left-vector containment](hyp:hx), and [right-vector containment](hyp:hy), [the reported interval contains the corresponding real dot product](goal). -/
theorem ChunkedDotCertificate.contains {ι : Type*} [Fintype ι] [DecidableEq ι]
    {left right : IntervalVector ι} {chunkSize : ℕ} {output : RatInterval}
    (c : ChunkedDotCertificate left right chunkSize output)
    {x y : ι → ℝ} (hx : ContainsVector left x) (hy : ContainsVector right y) :
    output.Contains (∑ i, x i * y i) := by
  exact ChunkedSumCertificate.contains c fun i => RatInterval.mul_sound (hx i) (hy i)
end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
