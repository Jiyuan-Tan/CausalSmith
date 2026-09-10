import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Existence

/-!
# Finite-iterate enclosures of stationary distributions and rewards

This module turns a checked interval recurrence into an a posteriori fixed-point
certificate.  An `ℓ¹` contraction coefficient converts the last one-step
residual into a stationary-distribution radius; a certified reward bound then
converts that radius into a stationary-expectation interval.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- The expectation of a finite reward vector under a real mass vector. -/
def rewardExpectation {ι : Type*} [Fintype ι]
    (p reward : ι → ℝ) : ℝ :=
  ∑ i, p i * reward i

/-- A bounded reward certificate gives entrywise rational enclosures and an
exact rational uniform absolute bound on all their endpoints. -/
structure BoundedRewardCertificate {ι : Type*} [Fintype ι] (reward : ι → ℝ) where
  /-- Rational interval enclosure for each reward coordinate. -/
  intervals : IntervalVector ι
  /-- Each real reward is contained in its coordinate interval. -/
  contains : ContainsVector intervals reward
  /-- Exact rational uniform absolute reward bound. -/
  bound : ℚ
  /-- The uniform bound is nonnegative. -/
  bound_nonneg : 0 ≤ bound
  /-- Every interval endpoint has absolute value at most the uniform bound. -/
  endpoints_bounded : ∀ i, (intervals i).maxAbs ≤ bound

/-- The rational residual bound sums the maximum absolute endpoint of the
difference between the terminal interval row and its certified successor. -/
def finiteIterateResidualBound {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) : ℚ :=
  ∑ i, ((c.terminal i).sub (c.next i)).maxAbs

/-- The a posteriori stationary radius is the residual bound divided by one
minus the supplied exact rational contraction coefficient. -/
def stationaryErrorRadius {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) (rho : ℚ) : ℚ :=
  finiteIterateResidualBound c / (1 - rho)

private theorem RatInterval.abs_le_maxAbs_of_contains
    (I : RatInterval) {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.maxAbs : ℝ) := by
  apply abs_le.mpr
  constructor
  · exact (neg_le_of_abs_le (by
      exact_mod_cast (le_max_left |I.lo| |I.hi|))).trans hx.1
  · exact hx.2.trans (le_trans (le_abs_self (I.hi : ℝ)) (by
      exact_mod_cast (le_max_right |I.lo| |I.hi|)))

/-- The exact rational finite-iterate residual bound is nonnegative. -/
theorem finiteIterateResidualBound_nonneg {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) :
    0 ≤ finiteIterateResidualBound c := by
  exact Finset.sum_nonneg fun i _ =>
    le_max_of_le_left (abs_nonneg ((c.terminal i).sub (c.next i)).lo)

/-- A nonnegative contraction coefficient strictly below one gives a
nonnegative a posteriori stationary error radius. -/
theorem stationaryErrorRadius_nonneg {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) (rho : ℚ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) :
    0 ≤ stationaryErrorRadius c rho := by
  exact div_nonneg (finiteIterateResidualBound_nonneg c) (sub_nonneg.mpr hrho1.le)

/-- The certified stationary-distribution enclosure expands each terminal
coordinate interval by the common a posteriori `ℓ¹` radius. -/
def stationaryDistributionInterval {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) (rho : ℚ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) : IntervalVector ι :=
  fun i => (c.terminal i).expand (stationaryErrorRadius c rho)
    (stationaryErrorRadius_nonneg c rho hrho0 hrho1)

/-- The stationary reward interval is the terminal interval expectation widened
by the reward bound times the a posteriori stationary radius. -/
def stationaryRewardInterval {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (c : FiniteIterateCertificate K p0)
    (r : BoundedRewardCertificate reward) (rho : ℚ)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1) : RatInterval :=
  (intervalExpectation c.terminal r.intervals).expand
    (r.bound * stationaryErrorRadius c rho)
    (mul_nonneg r.bound_nonneg (stationaryErrorRadius_nonneg c rho hrho0 hrho1))

/-- Two real vectors enclosed by the terminal and successor rows have `ℓ¹`
distance at most the exact rational residual bound. -/
theorem l1Distance_le_finiteIterateResidualBound {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) {x y : ι → ℝ}
    (hx : ContainsVector c.terminal x) (hy : ContainsVector c.next y) :
    l1Distance x y ≤ (finiteIterateResidualBound c : ℝ) := by
  unfold l1Distance finiteIterateResidualBound
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum fun i _ =>
    RatInterval.abs_le_maxAbs_of_contains _ (RatInterval.sub_sound (hx i) (hy i))

/-- An a posteriori contraction estimate bounds the distance from an
approximate probability vector to any stationary distribution by its one-step
residual divided by `1 - rho`. -/
theorem l1Distance_stationary_le_residual {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {p π : ι → ℝ} {rho residual : ℝ}
    (hp : IsProbabilityVector p) (hπ : IsStationary P π)
    (hcontract : ContractsL1 P rho)
    (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hresidual0 : 0 ≤ residual)
    (hresidual : l1Distance p (markovStep p P) ≤ residual) :
    l1Distance p π ≤ residual / (1 - rho) := by
  have htriangle : l1Distance p π ≤
      l1Distance p (markovStep p P) +
        l1Distance (markovStep p P) (markovStep π P) := by
    unfold l1Distance
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => by
      calc
        |p i - π i| = |(p i - markovStep p P i) +
            (markovStep p P i - markovStep π P i)| := by rw [hπ.2]; ring
        _ ≤ |p i - markovStep p P i| +
            |markovStep p P i - markovStep π P i| := abs_add_le _ _
  have hstep := hcontract p π hp hπ.1
  have hmain : l1Distance p π ≤ residual + rho * l1Distance p π :=
    htriangle.trans (add_le_add hresidual hstep)
  apply (le_div_iff₀ (sub_pos.mpr hrho1)).2
  nlinarith

/-- A bounded reward changes by at most its uniform absolute bound times the
`ℓ¹` distance between two mass vectors. -/
theorem abs_rewardExpectation_sub_le {ι : Type*} [Fintype ι]
    {p q reward : ι → ℝ} {B : ℝ}
    (hB0 : 0 ≤ B) (hreward : ∀ i, |reward i| ≤ B) :
    |rewardExpectation p reward - rewardExpectation q reward| ≤
      B * l1Distance p q := by
  unfold rewardExpectation l1Distance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (p i * reward i - q i * reward i)| =
        |∑ i, (p i - q i) * reward i| := by
          congr 2
          funext i
          ring
    _ ≤ ∑ i, |(p i - q i) * reward i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |p i - q i| * B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hreward i) (abs_nonneg _)
    _ = B * ∑ i, |p i - q i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- The endpoint check in a bounded reward certificate implies the semantic
absolute bound for every true reward coordinate. -/
theorem BoundedRewardCertificate.bound_sound {ι : Type*} [Fintype ι]
    {reward : ι → ℝ} (r : BoundedRewardCertificate reward) (i : ι) :
    |reward i| ≤ (r.bound : ℝ) := by
  exact (RatInterval.abs_le_maxAbs_of_contains _ (r.contains i)).trans (by
    exact_mod_cast r.endpoints_bounded i)

private theorem finiteIterate_stationary_l1_le {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    (kernel : CertifiedKernel P)
    (c : FiniteIterateCertificate kernel.intervals p0)
    (rho : ℚ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P (rho : ℝ))
    {π : ι → ℝ} (hπ : IsStationary P π) :
    l1Distance (markovIterate P p0.toReal c.steps) π ≤
      (stationaryErrorRadius c rho : ℝ) := by
  let p := markovIterate P p0.toReal c.steps
  have hp : IsProbabilityVector p :=
    kernel.stochastic.iterate_probability p0.isProbability c.steps
  have hterminal : ContainsVector c.terminal p := c.terminal_sound kernel.contains
  have hnext : ContainsVector c.next (markovStep p P) := by
    simpa only [p, markovIterate] using c.next_sound kernel.contains
  have hresidual : l1Distance p (markovStep p P) ≤
      (finiteIterateResidualBound c : ℝ) :=
    l1Distance_le_finiteIterateResidualBound c hterminal hnext
  simpa only [stationaryErrorRadius, Rat.cast_div, Rat.cast_sub, Rat.cast_one] using
    l1Distance_stationary_le_residual hp hπ hcontract
      (by exact_mod_cast hrho0) (by exact_mod_cast hrho1)
      (by exact_mod_cast finiteIterateResidualBound_nonneg c) hresidual

/-- A checked finite recurrence and a strict `ℓ¹` contraction enclose every
stationary distribution coordinate in the computed rational expansion of the
terminal interval row. -/
theorem stationaryDistributionInterval_sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    (kernel : CertifiedKernel P)
    (c : FiniteIterateCertificate kernel.intervals p0)
    (rho : ℚ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P (rho : ℝ))
    {π : ι → ℝ} (hπ : IsStationary P π) :
    ContainsVector (stationaryDistributionInterval c rho hrho0 hrho1) π := by
  let p := markovIterate P p0.toReal c.steps
  have hterminal : ContainsVector c.terminal p := c.terminal_sound kernel.contains
  have hl1 : l1Distance p π ≤ (stationaryErrorRadius c rho : ℝ) :=
    finiteIterate_stationary_l1_le kernel c rho hrho0 hrho1 hcontract hπ
  intro i
  have hcoord : |p i - π i| ≤ (stationaryErrorRadius c rho : ℝ) :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (p j - π j))
      (Finset.mem_univ i)).trans hl1
  change
    ((((c.terminal i).lo - stationaryErrorRadius c rho : ℚ) : ℝ) ≤ π i ∧
      π i ≤ (((c.terminal i).hi + stationaryErrorRadius c rho : ℚ) : ℝ))
  norm_num only [Rat.cast_sub, Rat.cast_add]
  rcases hterminal i with ⟨hlo, hhi⟩
  rcases abs_le.mp hcoord with ⟨hcoord_lo, hcoord_hi⟩
  constructor <;> linarith

/-- Given [a certified finite transition kernel](hyp:kernel), [a checked finite interval recurrence](hyp:c), [a certified bounded reward vector](hyp:r), [a rational contraction coefficient](hyp:rho), [its nonnegativity](hyp:hrho0), [its strict upper bound by one](hyp:hrho1), [the corresponding contraction guarantee](hyp:hcontract), and [a stationary distribution](hyp:hπ), [the computed rational interval contains that distribution's stationary reward expectation](goal). -/
theorem stationaryRewardInterval_sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (kernel : CertifiedKernel P)
    (c : FiniteIterateCertificate kernel.intervals p0)
    (r : BoundedRewardCertificate reward)
    (rho : ℚ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P (rho : ℝ))
    {π : ι → ℝ} (hπ : IsStationary P π) :
    (stationaryRewardInterval c r rho hrho0 hrho1).Contains
      (rewardExpectation π reward) := by
  let p := markovIterate P p0.toReal c.steps
  have hterminal : ContainsVector c.terminal p := c.terminal_sound kernel.contains
  have hbase : (intervalExpectation c.terminal r.intervals).Contains
      (rewardExpectation p reward) := intervalDot_sound hterminal r.contains
  have hl1 : l1Distance p π ≤ (stationaryErrorRadius c rho : ℝ) :=
    finiteIterate_stationary_l1_le kernel c rho hrho0 hrho1 hcontract hπ
  have hperturb : |rewardExpectation π reward - rewardExpectation p reward| ≤
      (r.bound : ℝ) * (stationaryErrorRadius c rho : ℝ) :=
    (by
      rw [abs_sub_comm]
      exact (abs_rewardExpectation_sub_le (by exact_mod_cast r.bound_nonneg)
        r.bound_sound).trans
        (mul_le_mul_of_nonneg_left hl1 (by exact_mod_cast r.bound_nonneg)))
  change
    ((((intervalExpectation c.terminal r.intervals).lo -
        r.bound * stationaryErrorRadius c rho : ℚ) : ℝ) ≤
      rewardExpectation π reward ∧
      rewardExpectation π reward ≤
        (((intervalExpectation c.terminal r.intervals).hi +
          r.bound * stationaryErrorRadius c rho : ℚ) : ℝ))
  norm_num only [Rat.cast_sub, Rat.cast_add, Rat.cast_mul]
  rcases hbase with ⟨hbase_lo, hbase_hi⟩
  rcases abs_le.mp hperturb with ⟨hperturb_lo, hperturb_hi⟩
  constructor <;> linarith

/-- An exact rational minorization certificate supplies the contraction needed
to certify the stationary reward interval with coefficient `1 - epsilon`. -/
theorem stationaryRewardInterval_sound_of_minorization
    {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (kernel : CertifiedKernel P)
    (minor : RationalMinorizationCertificate kernel.intervals)
    (c : FiniteIterateCertificate kernel.intervals p0)
    (r : BoundedRewardCertificate reward)
    (hepsilon_pos : 0 < minor.epsilon)
    {π : ι → ℝ} (hπ : IsStationary P π) :
    (stationaryRewardInterval c r (1 - minor.epsilon)
      (sub_nonneg.mpr minor.epsilon_le_one) (by linarith)).Contains
      (rewardExpectation π reward) := by
  apply stationaryRewardInterval_sound kernel c r (1 - minor.epsilon)
    (sub_nonneg.mpr minor.epsilon_le_one) (by linarith) _ hπ
  simpa only [Rat.cast_sub, Rat.cast_one] using
    contractsL1_of_rationalMinorization kernel.stochastic kernel.contains minor

/-- For a nonempty state space, the checked recurrence and contraction both
produce a unique stationary distribution and certify its reward expectation. -/
theorem existsUnique_stationary_and_reward_enclosed
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {P : Matrix ι ι ℝ} {p0 : RationalProbabilityVector ι}
    {reward : ι → ℝ} (kernel : CertifiedKernel P)
    (c : FiniteIterateCertificate kernel.intervals p0)
    (r : BoundedRewardCertificate reward)
    (rho : ℚ) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hcontract : ContractsL1 P (rho : ℝ)) :
    ∃! π : ι → ℝ,
      IsStationary P π ∧
      (stationaryRewardInterval c r rho hrho0 hrho1).Contains
        (rewardExpectation π reward) := by
  obtain ⟨π, hπ, hunique⟩ := existsUnique_stationary_of_contractsL1
    kernel.stochastic (by exact_mod_cast hrho0) (by exact_mod_cast hrho1) hcontract
  refine ⟨π, ⟨hπ, stationaryRewardInterval_sound kernel c r rho hrho0 hrho1
    hcontract hπ⟩, ?_⟩
  intro π' hπ'
  exact hunique π' hπ'.1

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
