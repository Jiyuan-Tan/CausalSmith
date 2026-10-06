module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Engine

/-! # The paper's explicit finite rational arithmetic routines

The specified truncation counts, remainder brackets, binary integer-square-root
recurrence and Machin formula define the witness; its contracts remain proof obligations.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- Exact dyadic rational error. -/
def rationalError (q : ℕ) : ℚ := 1 / 2 ^ q
/-- Bound for the exponential and cosine routines. -/
def seriesBound (z : ℚ) : ℕ := max 1 (⌈|z|⌉ : ℤ).toNat
/-- The specified polynomial length. -/
def seriesCount (q : ℕ) (z : ℚ) : ℕ := max (2 * seriesBound z ^ 2) (q + 6)
/-- Exact exponential polynomial. -/
def expPolynomial (q : ℕ) (z : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (2 * seriesCount q z), z ^ j / (Nat.factorial j : ℚ)
/-- Scalar exponential enclosure with the prescribed positive floor. -/
def paperExpScalar (q : ℕ) (z : ℚ) : RatInterval :=
  rationalBox (max (1 / (3 : ℚ) ^ seriesBound z)
    (expPolynomial q z - rationalError (q + 3)))
    (expPolynomial q z + rationalError (q + 3))
/-- Exact cosine polynomial. -/
def cosPolynomial (q : ℕ) (z : ℚ) : ℚ :=
  ∑ j ∈ Finset.range (seriesCount q z), (-1 : ℚ) ^ j * z ^ (2 * j) /
    (Nat.factorial (2 * j) : ℚ)
/-- Scalar cosine bracket, clipped to its range. -/
def paperCosScalar (q : ℕ) (z : ℚ) : RatInterval :=
  rationalBox (max (-1) (cosPolynomial q z - rationalError (q + 3)))
    (min 1 (cosPolynomial q z + rationalError (q + 3)))
/-- Rational range bound for the logarithm. -/
def logRangeBound (z : ℚ) : ℕ :=
  max 2 (max (⌈z⌉ : ℤ).toNat (⌈1 / z⌉ : ℤ).toNat)
/-- Exact atanh logarithm polynomial, with the specified count. -/
def logPolynomial (q : ℕ) (z : ℚ) : ℚ :=
  let B := logRangeBound z
  let v := (z - 1) / (z + 1)
  2 * ∑ j ∈ Finset.range (B * (q + 3 + Nat.clog 2 (8 * B) + 2)),
    v ^ (2 * j + 1) / (2 * j + 1 : ℕ)
/-- Positive-domain logarithm enclosure, totalized by a point outside the domain. -/
def paperLogScalar (q : ℕ) (z : ℚ) : RatInterval :=
  if 0 < z then rationalBox (logPolynomial q z - rationalError (q + 3))
    (logPolynomial q z + rationalError (q + 3)) else RatInterval.point 0
/-- One binary integer-square-root step. -/
def integerSqrtStep (N : ℕ) (lu : ℕ × ℕ) : ℕ × ℕ :=
  if lu.2 - lu.1 = 1 then lu else
    let a := (lu.1 + lu.2) / 2
    if a ^ 2 ≤ N then (a, lu.2) else (lu.1, a)
/-- Exactly the public number of binary steps, by structural recursion. -/
def integerSqrtLoop (N : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ
  | 0, lu => lu
  | q + 1, lu => integerSqrtLoop N q (integerSqrtStep N lu)
/-- The literal prescribed fixed-count integer-square-root algorithm. -/
def paperIntegerSqrt (N : ℕ) : ℕ :=
  (integerSqrtLoop N (Nat.clog 2 (N + 1) + 1) (0, N + 1)).1
/-- Scalar dyadic square-root bracket. -/
def paperSqrtScalar (q : ℕ) (z : ℚ) : RatInterval :=
  let p := q + 3
  let N := (⌊(2 : ℚ) ^ (2 * p) * z⌋ : ℤ).toNat
  let a := paperIntegerSqrt N
  rationalBox ((a : ℚ) / 2 ^ p) (((a : ℚ) + 1) / 2 ^ p)
/-- The alternating arctangent polynomial. -/
def arctanPolynomial (N : ℕ) (v : ℚ) : ℚ :=
  ∑ j ∈ Finset.range N, (-1 : ℚ) ^ j * v ^ (2 * j + 1) / (2 * j + 1 : ℕ)
/-- Machin's fixed-count rational pi enclosure. -/
def paperPi (q : ℕ) : RatInterval :=
  let p := q + 3
  let S := 16 * arctanPolynomial (p + 4) (1 / 5) -
    4 * arctanPolynomial (p + 4) (1 / 239)
  rationalBox (max 3 (S - rationalError p)) (min 4 (S + rationalError p))
/-- Monotone endpoint extension of a scalar routine. -/
def endpointExtension (F : ℕ → ℚ → RatInterval) (q : ℕ) (I : RatInterval) : RatInterval :=
  rationalBox (F q I.lo).lo (F q I.hi).hi
/-- Midpoint cosine, enlarged by half the argument width then intersected with [-1,1]. -/
def paperCos (q : ℕ) (I : RatInterval) : RatInterval :=
  let J := paperCosScalar q ((I.lo + I.hi) / 2)
  rationalBox (max (-1) (J.lo - I.width / 2)) (min 1 (J.hi + I.width / 2))
/-- Scalar positive-integer-base power with the paper's internal precision. -/
def paperPowerScalar (q b : ℕ) (v : ℚ) : RatInterval :=
  if b = 1 then RatInterval.point 1 else
    let B := max 2 b
    let p := q + 12 + 3 * Nat.clog 2 B
    let L := paperLogScalar p b
    let J := paperExpScalar p (v * ((L.lo + L.hi) / 2))
    let e := 96 * (B : ℚ) ^ 3 * rationalError p
    rationalBox (max (1 / (b : ℚ) ^ 3) (J.lo - e)) (min ((b : ℚ) ^ 3) (J.hi + e))
/-- The concrete independently fixed rational engine. -/
def concreteEngine : ArithmeticEngine where -- @realizes \mathsf E_0(series and integer routines)
  piBox := paperPi
  expBox := endpointExtension paperExpScalar
  cosBox := paperCos
  logBox := endpointExtension paperLogScalar
  sqrtBox := endpointExtension paperSqrtScalar
  powBox := fun q b => endpointExtension (fun q v => paperPowerScalar q b v) q
end CausalSmith.Stat.LogoddsLowsmoothFrontier
