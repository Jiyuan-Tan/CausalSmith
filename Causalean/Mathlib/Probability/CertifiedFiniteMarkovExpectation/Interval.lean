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
