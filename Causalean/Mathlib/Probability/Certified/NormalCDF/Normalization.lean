module
public import Causalean.Mathlib.Probability.Certified.NormalCDFInterval

/-!
# Certified normalization intervals for the standard normal density

This module isolates the reusable exact-rational certificate for
`1 / sqrt (2 * π)`.  It reuses Causalean's Machin enclosure for `π`, rational
square-root enclosure, and interval reciprocal, without invoking its uniform
normal-CDF quadrature.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

/-- A normalization schedule is the finite precision datum used for the
Machin-π and Newton square-root computations. -/
structure NormalizationSchedule where
  /-- Precision used by the certified `π` and square-root evaluators. -/
  fuel : ℕ

/-- The raw normalization interval is the reciprocal square-root enclosure
when its exact rational guards succeed, and a harmless fallback otherwise. -/
def normalizationInterval (s : NormalizationSchedule) : RatInterval :=
  if htwoPi : 0 ≤ (twoPiInterval s.fuel).lo then
    let root := RatInterval.sqrtInterval (twoPiInterval s.fuel) htwoPi s.fuel
    if hroot : root.hi < 0 ∨ 0 < root.lo then root.inv hroot else RatInterval.point 0
  else RatInterval.point 0

/-- The executable schedule checker validates that the computed `2π` interval
is nonnegative and that its square-root enclosure excludes zero. -/
def normalizationScheduleCheck (s : NormalizationSchedule) : Bool :=
  if htwoPi : 0 ≤ (twoPiInterval s.fuel).lo then
    let root := RatInterval.sqrtInterval (twoPiInterval s.fuel) htwoPi s.fuel
    decide (root.hi < 0 ∨ 0 < root.lo)
  else false

/-- A normalization certificate is raw finite schedule and caller-enclosure
data; `normalizationCheck` validates all side conditions. -/
structure NormalizationCertificate where
  /-- Finite exact-arithmetic schedule for the normalization constant. -/
  schedule : NormalizationSchedule
  /-- Caller-facing enclosure of `1 / sqrt (2π)`. -/
  enclosure : RatInterval

/-- The executable normalization checker validates every guarded interval
operation and the exact rational refinement into the caller's enclosure. -/
def normalizationCheck (c : NormalizationCertificate) : Bool :=
  normalizationScheduleCheck c.schedule &&
    decide (c.enclosure.lo ≤ (normalizationInterval c.schedule).lo ∧
      (normalizationInterval c.schedule).hi ≤ c.enclosure.hi)

/-- For [a normalization schedule](hyp:s) with
[a successful executable guard](hyp:hcheck),
[the raw interval contains `1 / sqrt (2π)`](goal). -/
theorem normalizationInterval_sound (s : NormalizationSchedule)
    (hcheck : normalizationScheduleCheck s = true) :
    (normalizationInterval s).Contains (1 / Real.sqrt (2 * Real.pi)) := by
  -- Unfold the executable guard twice.  The successful `decide` supplies the
  -- `AwayFromZero` proof (proof irrelevance identifies it with the proof used
  -- by `normalizationInterval`).  Then reuse `piInterval_sound`,
  -- `sqrtInterval_sound`, and `RatInterval.inv_sound`, as in Causalean's
  -- `normalDensityScaleInterval_sound`.
  unfold normalizationScheduleCheck at hcheck
  split at hcheck
  next htwoPi =>
    dsimp only at hcheck
    have hroot := of_decide_eq_true hcheck
    rw [normalizationInterval, dif_pos htwoPi, dif_pos hroot]
    rw [one_div]
    apply RatInterval.inv_sound hroot
    apply RatInterval.sqrtInterval_sound htwoPi
    simpa [twoPiInterval] using RatInterval.mul_sound (RatInterval.point_sound 2)
      (Transcendental.piInterval_sound s.fuel)
  next =>
    contradiction

/-- A [normalization certificate](hyp:c) whose [executable check succeeds](hyp:hcheck) [contains the standard-normal density scale](goal). -/
theorem NormalizationCertificate.sound (c : NormalizationCertificate)
    (hcheck : normalizationCheck c = true) :
    c.enclosure.Contains (1 / Real.sqrt (2 * Real.pi)) := by
  -- Split the Boolean conjunction, decode the exact `Subinterval` decision,
  -- and apply `RatInterval.Contains.mono` to `normalizationInterval_sound`.
  unfold normalizationCheck at hcheck
  rw [Bool.and_eq_true] at hcheck
  rcases hcheck with ⟨hschedule, hrefinement⟩
  have hrefinement' :
      c.enclosure.lo ≤ (normalizationInterval c.schedule).lo ∧
        (normalizationInterval c.schedule).hi ≤ c.enclosure.hi :=
    of_decide_eq_true hrefinement
  exact (normalizationInterval_sound c.schedule hschedule).mono hrefinement'

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
