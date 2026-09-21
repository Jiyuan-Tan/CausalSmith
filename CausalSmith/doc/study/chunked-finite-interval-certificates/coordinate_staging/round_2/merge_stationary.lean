namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- [A coordinate recurrence certificate](goal) records, for [an interval transition matrix](hyp:K), [a current interval vector](hyp:current), [a next interval vector](hyp:next), and [a chunk-size bound](hyp:chunkSize), [one chunked dot-product certificate for each output coordinate](hyp:coordinate). -/
structure CoordinateRecurrenceCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : IntervalMatrix ι ι) (current next : IntervalVector ι)
    (chunkSize : ℕ) where
  /-- Chunked certificate for the dot product producing each next coordinate. -/
  coordinate : ∀ j,
    ChunkedDotCertificate current (fun i => K i j) chunkSize (next j)

/-- When [a coordinate recurrence certificate is supplied](hyp:c), [the interval row-vector recurrence refines the reported next interval vector](goal). -/
theorem CoordinateRecurrenceCertificate.sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : IntervalMatrix ι ι} {current next : IntervalVector ι}
    {chunkSize : ℕ} (c : CoordinateRecurrenceCertificate K current next chunkSize) :
    VectorSubinterval (intervalVecMul current K) next := by
  intro j
  exact (c.coordinate j).sound

/-- [A chunked finite-iterate certificate](goal) stores a recurrence trace for [an interval transition matrix](hyp:K) from [an exact rational initial distribution](hyp:p0), using [a number of approximation steps](hyp:steps), [a positive chunk-size bound](hyp:chunkSize) and [its positivity proof](hyp:chunkSize_pos), [the interval rows](hyp:table), [initial coordinate checks](hyp:initial_checked), and [bounded coordinate recurrence checks](hyp:recurrence). -/
structure ChunkedFiniteIterateCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : IntervalMatrix ι ι) (p0 : RationalProbabilityVector ι) where
  /-- Number of the penultimate iterate used by stationary enclosures. -/
  steps : ℕ
  /-- Maximum number of scalar products checked by any chunk leaf. -/
  chunkSize : ℕ
  /-- A chunk must contain at least one permitted slot. -/
  chunkSize_pos : 0 < chunkSize
  /-- Interval vectors for iterates zero through `steps + 1`. -/
  table : Fin (steps + 2) → IntervalVector ι
  /-- Independently checked initial coordinate inclusions. -/
  initial_checked : ∀ i, (RatInterval.point (p0.value i)).Subinterval (table 0 i)
  /-- Every recurrence step is certified coordinatewise with bounded chunks. -/
  recurrence : ∀ k : Fin (steps + 1),
    CoordinateRecurrenceCertificate K (table k.castSucc) (table k.succ) chunkSize

/-- Given [a chunked finite-iterate certificate](hyp:c), [the corresponding established finite-iterate certificate](goal) is [the same trace with each opaque coordinate proof composed into its recurrence field](step:1). -/
def ChunkedFiniteIterateCertificate.toFiniteIterateCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : ChunkedFiniteIterateCertificate K p0) :
    FiniteIterateCertificate K p0 where
  steps := c.steps
  table := c.table
  initial_checked := c.initial_checked
  recurrence_checked := by
    intro k
    exact (c.recurrence k).sound

/-- Given [a chunked finite-iterate certificate](hyp:c), [a real transition matrix enclosed by its interval matrix](hyp:hK), and [a selected trace row](hyp:k), [that row contains the corresponding exact Markov iterate](goal). -/
theorem ChunkedFiniteIterateCertificate.table_sound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    {p0 : RationalProbabilityVector ι}
    (c : ChunkedFiniteIterateCertificate K p0)
    (hK : ContainsMatrix K P) (k : Fin (c.steps + 2)) :
    ContainsVector (c.table k) (markovIterate P p0.toReal k) := by
  exact c.toFiniteIterateCertificate.table_sound hK k

/-- When [a chunked finite-iterate certificate is supplied](hyp:c), [its adapter has exactly the same table, terminal row, and successor row](goal). -/
theorem ChunkedFiniteIterateCertificate.adapter_rows
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : ChunkedFiniteIterateCertificate K p0) :
    c.toFiniteIterateCertificate.table = c.table ∧
      c.toFiniteIterateCertificate.terminal = c.table (Fin.castSucc (Fin.last c.steps)) ∧
      c.toFiniteIterateCertificate.next = c.table (Fin.last (c.steps + 1)) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Given [a certified real kernel](hyp:kernel), [a chunked finite-iterate certificate](hyp:c), [a bounded reward certificate](hyp:r), [a rational contraction coefficient](hyp:rho) that is [nonnegative](hyp:hrho0) and [strictly below one](hyp:hrho1), [the contraction property](hyp:hcontract), and [a stationary distribution](hyp:hπ), [the stationary-reward interval obtained through the adapter contains the stationary reward expectation](goal). -/
theorem stationaryRewardInterval_sound_of_chunked
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (kernel : CertifiedKernel P)
    (c : ChunkedFiniteIterateCertificate kernel.intervals p0)
    (r : BoundedRewardCertificate reward)
    (rho : ℚ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P (rho : ℝ))
    {π : ι → ℝ} (hπ : IsStationary P π) :
    (stationaryRewardInterval c.toFiniteIterateCertificate r rho hrho0 hrho1).Contains
      (rewardExpectation π reward) := by
  exact stationaryRewardInterval_sound kernel c.toFiniteIterateCertificate r
    rho hrho0 hrho1 hcontract hπ

/-- Given [a certified real kernel](hyp:kernel), [a rational minorization certificate](hyp:minor), [a chunked finite-iterate certificate](hyp:c), [a bounded reward certificate](hyp:r), [positive minorization mass](hyp:hepsilon_pos), and [a stationary distribution](hyp:hπ), [the stationary-reward interval at coefficient one minus the minorization mass contains the stationary reward expectation](goal). -/
theorem stationaryRewardInterval_sound_of_minorization_chunked
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (kernel : CertifiedKernel P)
    (minor : RationalMinorizationCertificate kernel.intervals)
    (c : ChunkedFiniteIterateCertificate kernel.intervals p0)
    (r : BoundedRewardCertificate reward)
    (hepsilon_pos : 0 < minor.epsilon)
    {π : ι → ℝ} (hπ : IsStationary P π) :
    (stationaryRewardInterval c.toFiniteIterateCertificate r (1 - minor.epsilon)
      (sub_nonneg.mpr minor.epsilon_le_one) (by linarith)).Contains
      (rewardExpectation π reward) := by
  exact stationaryRewardInterval_sound_of_minorization kernel minor
    c.toFiniteIterateCertificate r hepsilon_pos hπ

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
