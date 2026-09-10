import Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.Interval

/-!
# Finite stochastic kernels, contraction, and checked interval recurrences

This module defines row-stochastic finite kernels and their action on
probability row vectors.  It also provides exact-rational certificates for
kernel minorization and for a finite interval recurrence enclosing successive
iterates of a real Markov chain.
-/

open scoped BigOperators

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic

/-- A real vector is a probability vector when its entries are nonnegative and sum to one. -/
def IsProbabilityVector {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- A real square matrix is row-stochastic when every entry is nonnegative and every row sums to one. -/
def IsStochasticMatrix {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- One Markov step applies a row probability vector to a row-stochastic matrix. -/
def markovStep {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (P : Matrix ι ι ℝ) : ι → ℝ :=
  Matrix.vecMul p P

/-- The successive distributions from an initial row vector under a fixed finite kernel. -/
def markovIterate {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (p0 : ι → ℝ) : ℕ → (ι → ℝ)
  | 0 => p0
  | n + 1 => markovStep (markovIterate P p0 n) P

/-- A stationary distribution is a probability vector fixed by one Markov step. -/
def IsStationary {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (π : ι → ℝ) : Prop :=
  IsProbabilityVector π ∧ markovStep π P = π

/-- The finite `ℓ¹` distance is the sum of absolute coordinate differences. -/
def l1Distance {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  ∑ i, |p i - q i|

/-- A kernel contracts probability vectors in `ℓ¹` by a supplied coefficient. -/
def ContractsL1 {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (ρ : ℝ) : Prop :=
  ∀ p q, IsProbabilityVector p → IsProbabilityVector q →
    l1Distance (markovStep p P) (markovStep q P) ≤ ρ * l1Distance p q

/-- A Doeblin minorization says every row of a kernel dominates the same
probability vector with a common mass `ε` between zero and one. -/
def Minorizes {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (ε : ℝ) (ν : ι → ℝ) : Prop :=
  IsProbabilityVector ν ∧ 0 ≤ ε ∧ ε ≤ 1 ∧ ∀ i j, ε * ν j ≤ P i j

/-- A certified real kernel packages a stochastic matrix together with an
entrywise rational interval table that contains it. -/
structure CertifiedKernel {ι : Type*} [Fintype ι] (P : Matrix ι ι ℝ) where
  /-- Exact rational interval table for the transition entries. -/
  intervals : IntervalMatrix ι ι
  /-- Every real transition entry lies in its reported rational interval. -/
  contains : ContainsMatrix intervals P
  /-- The underlying real transition matrix is row-stochastic. -/
  stochastic : IsStochasticMatrix P

/-- A rational probability-vector certificate contains exact nonnegativity and sum checks. -/
structure RationalProbabilityVector (ι : Type*) [Fintype ι] where
  /-- Exact rational mass at each state. -/
  value : ι → ℚ
  /-- Every rational mass is nonnegative. -/
  nonneg : ∀ i, 0 ≤ value i
  /-- The exact rational masses sum to one. -/
  sum_eq_one : ∑ i, value i = 1

/-- The real probability vector denoted by an exact rational certificate. -/
def RationalProbabilityVector.toReal {ι : Type*} [Fintype ι]
    (p : RationalProbabilityVector ι) : ι → ℝ :=
  fun i => (p.value i : ℝ)

/-- A rational minorization certificate is checked solely by exact rational
nonnegativity, normalization, and entrywise lower-endpoint comparisons. -/
structure RationalMinorizationCertificate {ι : Type*} [Fintype ι]
    (K : IntervalMatrix ι ι) where
  /-- Common minorization mass. -/
  epsilon : ℚ
  /-- Exact rational minorizing probability vector. -/
  nu : RationalProbabilityVector ι
  /-- The common mass is nonnegative. -/
  epsilon_nonneg : 0 ≤ epsilon
  /-- The common mass is at most one. -/
  epsilon_le_one : epsilon ≤ 1
  /-- Each interval lower endpoint dominates the minorizing mass at that column. -/
  lower_checked : ∀ i j, epsilon * nu.value j ≤ (K i j).lo

/-- A finite iterate certificate stores `steps + 2` interval vectors and checks
each recurrence inclusion using exact rational interval arithmetic. -/
structure FiniteIterateCertificate {ι : Type*} [Fintype ι]
    (K : IntervalMatrix ι ι) (p0 : RationalProbabilityVector ι) where
  /-- Number of the penultimate iterate used as the approximation. -/
  steps : ℕ
  /-- Interval table for iterates zero through `steps + 1`. -/
  table : Fin (steps + 2) → IntervalVector ι
  /-- The first interval row contains the exact rational initial distribution. -/
  initial_checked : ∀ i,
    (RatInterval.point (p0.value i)).Subinterval (table 0 i)
  /-- Every next row contains the interval row-vector recurrence from its predecessor. -/
  recurrence_checked : ∀ k : Fin (steps + 1),
    VectorSubinterval
      (intervalVecMul (table k.castSucc) K)
      (table k.succ)

/-- The penultimate stored interval vector is the finite-iterate approximation
used for the stationary enclosure. -/
def FiniteIterateCertificate.terminal {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) : IntervalVector ι :=
  c.table (Fin.castSucc (Fin.last c.steps))

/-- The final stored interval vector encloses one further Markov step and is
used to certify the finite-iterate residual. -/
def FiniteIterateCertificate.next {ι : Type*} [Fintype ι]
    {K : IntervalMatrix ι ι} {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) : IntervalVector ι :=
  c.table (Fin.last (c.steps + 1))

/-- An exact rational probability-vector certificate denotes a real probability vector. -/
theorem RationalProbabilityVector.isProbability {ι : Type*} [Fintype ι]
    (p : RationalProbabilityVector ι) : IsProbabilityVector p.toReal := by
  unfold IsProbabilityVector RationalProbabilityVector.toReal
  constructor
  · intro i
    exact_mod_cast p.nonneg i
  · exact_mod_cast p.sum_eq_one

/-- A stochastic matrix sends every probability row vector to a probability row vector. -/
theorem IsStochasticMatrix.step_probability {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} (hP : IsStochasticMatrix P)
    {p : ι → ℝ} (hp : IsProbabilityVector p) :
    IsProbabilityVector (markovStep p P) := by
  classical
  rcases hP with ⟨hP_nonneg, hP_sum⟩
  rcases hp with ⟨hp_nonneg, hp_sum⟩
  constructor
  · intro j
    unfold markovStep Matrix.vecMul dotProduct
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hp_nonneg i) (hP_nonneg i j)
  · unfold markovStep Matrix.vecMul dotProduct
    rw [Finset.sum_comm]
    calc
      ∑ i, ∑ j, p i * P i j = ∑ i, p i * ∑ j, P i j := by
        congr 1
        funext i
        rw [Finset.mul_sum]
      _ = ∑ i, p i := by simp only [hP_sum, mul_one]
      _ = 1 := hp_sum

/-- Every finite iterate of a probability vector under a stochastic matrix is a probability vector. -/
theorem IsStochasticMatrix.iterate_probability {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} (hP : IsStochasticMatrix P)
    {p0 : ι → ℝ} (hp0 : IsProbabilityVector p0) (n : ℕ) :
    IsProbabilityVector (markovIterate P p0 n) := by
  induction n with
  | zero => exact hp0
  | succ n ih =>
      exact hP.step_probability ih

/-- An exact rational minorization certificate soundly minorizes every real
kernel contained in its interval table. -/
theorem RationalMinorizationCertificate.sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    (c : RationalMinorizationCertificate K)
    (hK : ContainsMatrix K P) :
    Minorizes P (c.epsilon : ℝ) c.nu.toReal := by
  refine ⟨c.nu.isProbability, ?_, ?_, ?_⟩
  · exact_mod_cast c.epsilon_nonneg
  · exact_mod_cast c.epsilon_le_one
  · intro i j
    calc
      (c.epsilon : ℝ) * c.nu.toReal j = ((c.epsilon * c.nu.value j : ℚ) : ℝ) := by
        simp only [RationalProbabilityVector.toReal, Rat.cast_mul]
      _ ≤ ((K i j).lo : ℝ) := by exact_mod_cast c.lower_checked i j
      _ ≤ P i j := (hK i j).1

/-- Doeblin minorization by mass `ε` yields `ℓ¹` contraction coefficient `1 - ε`. -/
theorem contractsL1_of_minorization {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {ε : ℝ} {ν : ι → ℝ}
    (hP : IsStochasticMatrix P) (hminor : Minorizes P ε ν) :
    ContractsL1 P (1 - ε) := by
  classical
  rcases hP with ⟨hP_nonneg, hP_sum⟩
  rcases hminor with ⟨hν, hε_nonneg, hε_le_one, hminor⟩
  rcases hν with ⟨hν_nonneg, hν_sum⟩
  intro p q hp hq
  rcases hp with ⟨hp_nonneg, hp_sum⟩
  rcases hq with ⟨hq_nonneg, hq_sum⟩
  let Q : Matrix ι ι ℝ := fun i j => P i j - ε * ν j
  have hQ_nonneg (i j : ι) : 0 ≤ Q i j := by
    dsimp [Q]
    linarith [hminor i j]
  have hQ_sum (i : ι) : ∑ j, Q i j = 1 - ε := by
    simp only [Q, Finset.sum_sub_distrib]
    rw [hP_sum]
    calc
      1 - ∑ j, ε * ν j = 1 - ε * ∑ j, ν j := by rw [Finset.mul_sum]
      _ = 1 - ε := by rw [hν_sum, mul_one]
  have hcoord (j : ι) :
      markovStep p P j - markovStep q P j =
        ∑ i, (p i - q i) * Q i j := by
    unfold markovStep Matrix.vecMul dotProduct
    simp_rw [show ∀ i, P i j = Q i j + ε * ν j by
      intro i
      simp only [Q]
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hp_common : ∑ i, p i * (ε * ν j) = ε * ν j := by
      rw [← Finset.sum_mul, hp_sum, one_mul]
    have hq_common : ∑ i, q i * (ε * ν j) = ε * ν j := by
      rw [← Finset.sum_mul, hq_sum, one_mul]
    rw [hp_common, hq_common]
    simp only [add_sub_add_right_eq_sub]
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext i
    ring
  unfold l1Distance
  simp_rw [hcoord]
  calc
    ∑ j, |∑ i, (p i - q i) * Q i j| ≤
        ∑ j, ∑ i, |(p i - q i) * Q i j| := by
      exact Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, ∑ i, |p i - q i| * Q i j := by
      congr 1
      funext j
      congr 1
      funext i
      rw [abs_mul, abs_of_nonneg (hQ_nonneg i j)]
    _ = ∑ i, ∑ j, |p i - q i| * Q i j := Finset.sum_comm
    _ = ∑ i, |p i - q i| * (1 - ε) := by
      congr 1
      funext i
      rw [← Finset.mul_sum, hQ_sum]
    _ = (1 - ε) * ∑ i, |p i - q i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Given [a row-stochastic real transition matrix](hyp:hP), [its containment in an exact rational interval table](hyp:hK), and [a checked rational minorization certificate for that table](hyp:c), [the kernel contracts finite probability vectors in total variation with coefficient one minus the certified minorization mass](goal). -/
theorem contractsL1_of_rationalMinorization {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    (hP : IsStochasticMatrix P) (hK : ContainsMatrix K P)
    (c : RationalMinorizationCertificate K) :
    ContractsL1 P (1 - (c.epsilon : ℝ)) := by
  exact contractsL1_of_minorization hP (c.sound hK)

/-- Every row of a checked finite interval recurrence contains the corresponding
true Markov iterate for any real kernel enclosed by the certified table. -/
theorem FiniteIterateCertificate.table_sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0)
    (hK : ContainsMatrix K P) (k : Fin (c.steps + 2)) :
    ContainsVector (c.table k) (markovIterate P p0.toReal k) := by
  refine Fin.induction ?_ (fun k ih => ?_) k
  · intro i
    exact RatInterval.Contains.mono (c.initial_checked i)
      (RatInterval.point_sound (p0.value i))
  · apply ContainsVector.mono (c.recurrence_checked k)
    exact intervalVecMul_sound ih hK

/-- The terminal stored row contains the true iterate at the certificate's selected step. -/
theorem FiniteIterateCertificate.terminal_sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) (hK : ContainsMatrix K P) :
    ContainsVector c.terminal (markovIterate P p0.toReal c.steps) := by
  exact c.table_sound hK (Fin.castSucc (Fin.last c.steps))

/-- The last stored row contains the true iterate one step after the selected terminal row. -/
theorem FiniteIterateCertificate.next_sound {ι : Type*} [Fintype ι]
    {P : Matrix ι ι ℝ} {K : IntervalMatrix ι ι}
    {p0 : RationalProbabilityVector ι}
    (c : FiniteIterateCertificate K p0) (hK : ContainsMatrix K P) :
    ContainsVector c.next (markovIterate P p0.toReal (c.steps + 1)) := by
  exact c.table_sound hK (Fin.last (c.steps + 1))

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
