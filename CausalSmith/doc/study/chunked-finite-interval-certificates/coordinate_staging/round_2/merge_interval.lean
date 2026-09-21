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

/-- [A scalar interval certificate](goal) records that [an exact rational value](hyp:q) lies in [a reported rational interval](hyp:I), through [a checked point-interval refinement](hyp:checked). -/
structure ScalarIntervalCertificate (q : ℚ) (I : RatInterval) : Prop where
  /-- The point interval at the exact value refines the reported interval. -/
  checked : (RatInterval.point q).Subinterval I

/-- When [a scalar interval certificate is supplied](hyp:c), [its reported interval contains the certificate's rational value as a real number](goal). -/
theorem ScalarIntervalCertificate.sound {q : ℚ} {I : RatInterval}
    (c : ScalarIntervalCertificate q I) : I.Contains (q : ℝ) := by
  exact RatInterval.Contains.mono c.checked (RatInterval.point_sound q)

/-- [A finite-vector certificate](goal) records independently checked scalar enclosures for [each coordinate of an exact rational vector](hyp:q) in [a rational interval vector](hyp:I), through [one certificate per coordinate](hyp:coordinate). -/
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

/-- [A finite-matrix certificate](goal) records independently checked scalar enclosures for [each entry of an exact rational matrix](hyp:q) in [a rational interval matrix](hyp:I), through [one certificate per entry](hyp:entry). -/
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

/-- [A certified chunk](goal) records a bounded partial interval sum of [a finite interval family](hyp:terms), with [the selected maximum chunk size](hyp:chunkSize), [its indices](hyp:indices), [its reported bound](hyp:bound), [a size proof](hyp:size_le), and [a local exact-sum refinement proof](hyp:checked). -/
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

/-- [A chunked-sum certificate](goal) assembles [a finite interval family](hyp:terms) using [a selected chunk-size bound](hyp:chunkSize) into [a reported output interval](hyp:output), through [bounded chunk certificates](hyp:chunks), [their pairwise disjointness](hyp:pairwise_disjoint), [their exhaustive coverage](hyp:covers), and [a checked binary assembly](hyp:assembly). -/
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
