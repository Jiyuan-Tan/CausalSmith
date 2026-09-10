import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Stationary

/-!
# Strict comparison of certified stationary expectations

This module provides the final order-theoretic comparison step.  Disjoint
rational enclosures for two stationary expectations certify a strict ordering,
and subtracting a common benchmark turns the same ordering into a strict bias
comparison between two policies.
-/

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The stationary bias of a reward process relative to a benchmark is its
stationary reward expectation minus that benchmark. -/
def stationaryBias {ι : Type*} [Fintype ι]
    (π reward : ι → ℝ) (benchmark : ℝ) : ℝ :=
  rewardExpectation π reward - benchmark

/-- If two rational intervals contain two real values and the first upper
endpoint is below the second lower endpoint, then the first value is strictly smaller. -/
theorem lt_of_disjoint_enclosures {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (hsep : I.hi < J.lo) :
    x < y := by
  -- Cast the exact rational endpoint separation to `ℝ`, then chain the upper
  -- containment inequality for `x` with the lower containment inequality for `y`.
  have hsep_real : (I.hi : ℝ) < (J.lo : ℝ) := by
    exact_mod_cast hsep
  exact hx.2.trans_lt (hsep_real.trans_le hy.1)

/-- Strict ordering of two stationary reward expectations is preserved after
subtracting the same real benchmark, yielding a strict stationary-bias comparison. -/
theorem stationaryBias_lt_of_expectation_lt {ι : Type*} [Fintype ι]
    {πP πQ reward : ι → ℝ} {benchmark : ℝ}
    (h : rewardExpectation πP reward < rewardExpectation πQ reward) :
    stationaryBias πP reward benchmark < stationaryBias πQ reward benchmark := by
  -- Unfold the common-benchmark subtraction and use strict-order compatibility.
  simpa only [stationaryBias] using sub_lt_sub_right h benchmark

/-- Given [the first certified policy kernel](hyp:kernelP), [the second certified policy kernel](hyp:kernelQ), [their checked finite interval recurrences](hyp:iterateP,iterateQ), [a certified bounded reward vector](hyp:rewardCert), [their rational contraction coefficients](hyp:rhoP,rhoQ), [the first coefficient's nonnegativity and strict upper bound](hyp:hrhoP0,hrhoP1), [the second coefficient's nonnegativity and strict upper bound](hyp:hrhoQ0,hrhoQ1), [the two contraction guarantees](hyp:hcontractP,hcontractQ), [their stationary distributions](hyp:hπP,hπQ), and [strictly separated computed reward intervals](hyp:hsep), [the first stationary reward expectation is strictly smaller than the second](goal). -/
theorem stationaryExpectation_lt_of_certified_intervals
    {ι : Type*} [Fintype ι]
    {P Q : Matrix ι ι ℝ}
    {p0P p0Q : RationalProbabilityVector ι}
    {reward : ι → ℝ}
    (kernelP : CertifiedKernel P) (kernelQ : CertifiedKernel Q)
    (iterateP : FiniteIterateCertificate kernelP.intervals p0P)
    (iterateQ : FiniteIterateCertificate kernelQ.intervals p0Q)
    (rewardCert : BoundedRewardCertificate reward)
    (rhoP rhoQ : ℚ)
    (hrhoP0 : 0 ≤ rhoP) (hrhoP1 : rhoP < 1)
    (hrhoQ0 : 0 ≤ rhoQ) (hrhoQ1 : rhoQ < 1)
    (hcontractP : ContractsL1 P (rhoP : ℝ))
    (hcontractQ : ContractsL1 Q (rhoQ : ℝ))
    {πP πQ : ι → ℝ} (hπP : IsStationary P πP) (hπQ : IsStationary Q πQ)
    (hsep :
      (stationaryRewardInterval iterateP rewardCert rhoP hrhoP0 hrhoP1).hi <
      (stationaryRewardInterval iterateQ rewardCert rhoQ hrhoQ0 hrhoQ1).lo) :
    rewardExpectation πP reward < rewardExpectation πQ reward := by
  -- Obtain both semantic containment facts from `stationaryRewardInterval_sound`,
  -- then apply `lt_of_disjoint_enclosures` to the checked endpoint separation.
  apply lt_of_disjoint_enclosures
  · exact stationaryRewardInterval_sound kernelP iterateP rewardCert rhoP
      hrhoP0 hrhoP1 hcontractP hπP
  · exact stationaryRewardInterval_sound kernelQ iterateQ rewardCert rhoQ
      hrhoQ0 hrhoQ1 hcontractQ hπQ
  · exact hsep

/-- For two certified policy kernels, disjoint stationary-expectation intervals
imply a strict comparison of their stationary biases relative to any common benchmark. -/
theorem stationaryBias_lt_of_certified_intervals
    {ι : Type*} [Fintype ι]
    {P Q : Matrix ι ι ℝ}
    {p0P p0Q : RationalProbabilityVector ι}
    {reward : ι → ℝ}
    (kernelP : CertifiedKernel P) (kernelQ : CertifiedKernel Q)
    (iterateP : FiniteIterateCertificate kernelP.intervals p0P)
    (iterateQ : FiniteIterateCertificate kernelQ.intervals p0Q)
    (rewardCert : BoundedRewardCertificate reward)
    (rhoP rhoQ : ℚ)
    (hrhoP0 : 0 ≤ rhoP) (hrhoP1 : rhoP < 1)
    (hrhoQ0 : 0 ≤ rhoQ) (hrhoQ1 : rhoQ < 1)
    (hcontractP : ContractsL1 P (rhoP : ℝ))
    (hcontractQ : ContractsL1 Q (rhoQ : ℝ))
    {πP πQ : ι → ℝ} (hπP : IsStationary P πP) (hπQ : IsStationary Q πQ)
    {benchmark : ℝ}
    (hsep :
      (stationaryRewardInterval iterateP rewardCert rhoP hrhoP0 hrhoP1).hi <
      (stationaryRewardInterval iterateQ rewardCert rhoQ hrhoQ0 hrhoQ1).lo) :
    stationaryBias πP reward benchmark < stationaryBias πQ reward benchmark := by
  -- First invoke the assembled expectation comparison above, then translate it
  -- through `stationaryBias_lt_of_expectation_lt`.
  apply stationaryBias_lt_of_expectation_lt
  exact stationaryExpectation_lt_of_certified_intervals kernelP kernelQ iterateP iterateQ
    rewardCert rhoP rhoQ hrhoP0 hrhoP1 hrhoQ0 hrhoQ1 hcontractP hcontractQ hπP hπQ hsep

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
