module
public import Causalean.Mathlib.Probability.Certified.NormalCDF.Basic
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Exponential

/-!
# Finite rational exponential certificates with explicit range reduction

A caller supplies a natural split `m`, a Taylor degree, and an enclosure; the
Boolean checker verifies `0 < m`, `|q/m| ≤ 1`, and exact interval refinement.
Raising the checked Taylor interval to `m` encloses
`exp q`.  For normal tails the exponent has magnitude below 745, so a split of
at most 745 suffices independently of the denominator of the rational endpoint.
-/

@[expose] public section

namespace Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
/-- The finite Taylor interval for `exp z`, using Causalean's exact rational
partial sum and explicit remainder radius. -/
def expTaylorInterval (z : ℚ) (degree : ℕ) : RatInterval :=
  Transcendental.expReducedRaw
    z degree

/-- On the unit interval, the finite rational Taylor interval encloses the real
exponential. -/
theorem expTaylorInterval_sound (z : ℚ) (hz : |z| ≤ 1) (degree : ℕ) :
    (expTaylorInterval z degree).Contains (Real.exp (z : ℝ)) := by
  -- Follow the reduced-input part of Causalean's `expRaw_sound`: apply
  -- `Real.exp_bound`, then identify its partial sum and remainder with
  -- `Transcendental.expPartial` and `expRemainder` by exact casts.
  have hzR : |(z : ℝ)| ≤ 1 := by exact_mod_cast hz
  have hb := Real.exp_bound hzR (n := degree + 1) (Nat.succ_pos degree)
  have hp :
      ((Transcendental.expPartial z degree : ℚ) : ℝ) =
        ∑ k ∈ Finset.range (degree + 1),
          (z : ℝ) ^ k / (k.factorial : ℝ) := by
    simp [Transcendental.expPartial]
  have hr :
      ((Transcendental.expRemainder z degree : ℚ) : ℝ) =
        |(z : ℝ)| ^ (degree + 1) * ((degree + 2 : ℕ) : ℝ) /
          (((degree + 1).factorial : ℝ) * (degree + 1 : ℕ)) := by
    simp [Transcendental.expRemainder]
  rw [← hp] at hb
  have hb' :
      |Real.exp (z : ℝ) - (Transcendental.expPartial z degree : ℝ)| ≤
        (Transcendental.expRemainder z degree : ℝ) := by
    rw [hr]
    convert hb using 1 <;> norm_num [Nat.cast_succ] <;> ring
  rw [abs_le] at hb'
  simp only [expTaylorInterval, Transcendental.expReducedRaw,
    RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
  constructor <;> linarith [hb'.1, hb'.2]

/-- The width of the raw reduced exponential interval is exactly twice its
explicit rational Taylor remainder radius. -/
theorem expTaylorInterval_width (z : ℚ) (degree : ℕ) :
    (expTaylorInterval z degree).width =
      2 * Transcendental.expRemainder z degree := by
  -- Unfold the interval endpoints and its width, then use ring arithmetic.
  simp only [expTaylorInterval, Transcendental.expReducedRaw,
    RatInterval.width]
  ring

/-- The factorial `(n+1)!` dominates `2^n`; this is the discrete estimate used
to turn Taylor factorial decay into a geometric precision bound. -/
theorem two_pow_le_factorial_succ (n : ℕ) :
    2 ^ n ≤ (n + 1).factorial := by
  -- Induct on `n`; rewrite both recurrences and use `2 ≤ n+2`.
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ, Nat.factorial_succ]
      calc
        2 ^ n * 2 ≤ (n + 1).factorial * 2 := Nat.mul_le_mul_right 2 ih
        _ ≤ (n + 1).factorial * (n + 1 + 1) := by gcongr <;> omega
        _ = (n + 1 + 1) * (n + 1).factorial := Nat.mul_comm _ _

/-- From degree one onward, the unit-range exponential interval has width at
most `3 / 2^degree`, explicitly witnessing logarithmic degree in inverse target
width. -/
theorem expTaylorInterval_width_le_geometric (z : ℚ) (hz : |z| ≤ 1)
    (degree : ℕ) (hdegree : 1 ≤ degree) :
    (expTaylorInterval z degree).width ≤ 3 / (2 : ℚ) ^ degree := by
  -- Rewrite the width with `expTaylorInterval_width`. Bound `|z|^(n+1)` by
  -- one, `(n+2)/(n+1)` by `3/2`, and use
  -- `two_pow_le_factorial_succ`; clear only manifestly positive denominators.
  have habsPow : |z| ^ (degree + 1) ≤ (1 : ℚ) :=
    pow_le_one₀ (abs_nonneg z) hz
  have hratioNat : 2 * (degree + 2) ≤ 3 * (degree + 1) := by omega
  have hratio :
      (2 : ℚ) * |z| ^ (degree + 1) * (degree + 2 : ℕ) ≤
        3 * (degree + 1 : ℕ) := by
    calc
      (2 : ℚ) * |z| ^ (degree + 1) * (degree + 2 : ℕ) ≤
          2 * 1 * (degree + 2 : ℕ) := by gcongr
      _ ≤ 3 * (degree + 1 : ℕ) := by exact_mod_cast hratioNat
  have hfactorialQ :
      (2 : ℚ) ^ degree ≤ ((degree + 1).factorial : ℚ) := by
    exact_mod_cast two_pow_le_factorial_succ degree
  have hcross :
      ((2 : ℚ) * |z| ^ (degree + 1) * (degree + 2 : ℕ)) * 2 ^ degree ≤
        3 * (((degree + 1).factorial : ℚ) * (degree + 1 : ℕ)) := by
    calc
      ((2 : ℚ) * |z| ^ (degree + 1) * (degree + 2 : ℕ)) * 2 ^ degree ≤
          (3 * (degree + 1 : ℕ)) * 2 ^ degree := by gcongr
      _ ≤ (3 * (degree + 1 : ℕ)) * ((degree + 1).factorial : ℚ) := by
        gcongr
      _ = 3 * (((degree + 1).factorial : ℚ) * (degree + 1 : ℕ)) := by ring
  rw [expTaylorInterval_width, Transcendental.expRemainder]
  rw [show
    (2 : ℚ) *
        (|z| ^ (degree + 1) * (degree + 2 : ℕ) /
          (((degree + 1).factorial : ℚ) * (degree + 1 : ℕ))) =
      ((2 : ℚ) * |z| ^ (degree + 1) * (degree + 2 : ℕ)) /
        (((degree + 1).factorial : ℚ) * (degree + 1 : ℕ)) by ring]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  exact hcross

/-- A finite exponential certificate is raw caller-supplied range-reduction,
Taylor-degree, and rational-enclosure data; `expCheck` validates it. -/
structure ExpCertificate (q : ℚ) where
  /-- Number of equal exponent pieces. -/
  split : ℕ
  /-- Taylor truncation index for the reduced exponent. -/
  degree : ℕ
  /-- Rational interval exposed to the tail checker. -/
  enclosure : RatInterval

/-- The exact interval computed from the caller's split and Taylor degree. -/
def expCertificateInterval {q : ℚ} (c : ExpCertificate q) : RatInterval :=
  (expTaylorInterval (q / (c.split : ℚ)) c.degree).npow c.split

/-- The executable exponential checker validates positive range reduction, a
unit reduced argument, and exact refinement into the reported interval. -/
def expCheck (q : ℚ) (c : ExpCertificate q) : Bool :=
  decide (0 < c.split ∧ |q / (c.split : ℚ)| ≤ 1 ∧
    c.enclosure.lo ≤ (expCertificateInterval c).lo ∧
    (expCertificateInterval c).hi ≤ c.enclosure.hi)

/-- A [finite rational exponential certificate](hyp:c) whose [executable check succeeds](hyp:hcheck) [contains the real exponential at its certified argument](goal). -/
theorem ExpCertificate.sound {q : ℚ} (c : ExpCertificate q)
    (hcheck : expCheck q c = true) :
    c.enclosure.Contains (Real.exp (q : ℝ)) := by
  -- Decode the three rational checks.  Enclose the reduced exponential with
  -- `expTaylorInterval_sound`, raise it using `RatInterval.npow_sound`, and
  -- identify the enclosed power with `exp q` via `Real.exp_nat_mul` and the
  -- nonzero real cast of the checked positive split.  Finish by monotonicity
  -- along the checked `Subinterval` relation.
  have hchecked :
      0 < c.split ∧ |q / (c.split : ℚ)| ≤ 1 ∧
        c.enclosure.lo ≤ (expCertificateInterval c).lo ∧
        (expCertificateInterval c).hi ≤ c.enclosure.hi :=
    of_decide_eq_true (by simpa [expCheck] using hcheck)
  rcases hchecked with ⟨hsplit, hreduced, hlo, hhi⟩
  have hbase := expTaylorInterval_sound (q / (c.split : ℚ)) hreduced c.degree
  have hpow := RatInterval.npow_sound hbase c.split
  have hsplitR : (c.split : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hsplit)
  have hmul :
      (c.split : ℝ) * ((q / (c.split : ℚ) : ℚ) : ℝ) = (q : ℝ) := by
    rw [Rat.cast_div]
    exact mul_div_cancel₀ _ hsplitR
  have hexp :
      Real.exp ((q / (c.split : ℚ) : ℚ) : ℝ) ^ c.split =
        Real.exp (q : ℝ) := by
    rw [← Real.exp_nat_mul, hmul]
  have hsub : (expCertificateInterval c).Subinterval c.enclosure := ⟨hlo, hhi⟩
  apply RatInterval.Contains.mono hsub
  rw [← hexp]
  exact hpow

end Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure
