module
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Data.Rat.Floor

/-! # Rational arithmetic for compact Prawitz certificates

Finite Taylor polynomials, outward rounding, and existing bounds for pi
turn the analytic cell enclosures into exact rational checks. No floating
point evaluation is used by these definitions or their comparison lemmas.
The Taylor degree and rounding scale are fixed for the compact certificates.
-/

@[expose] public section

namespace Causalean.Stat.CLT.BerryEsseen

open Finset

/-- The [sixteen-term Taylor polynomial](goal) at [a rational argument](hyp:x)
is an exactly computable rational approximation to the exponential. -/
def prawitzTaylor16 (x : ℚ) : ℚ :=
  ∑ m ∈ range 16, x ^ m / (m.factorial : ℚ)

/-- The [rational upper enclosure of the exponential](goal) at
[an argument](hyp:x) uses a Taylor remainder at one eighth of the argument,
followed by an eighth power. Its analytic comparison requires 0 ≤ x ≤ 8. -/
def prawitzExpUpper8 (x : ℚ) : ℚ :=
  (prawitzTaylor16 (x / 8) +
    (x / 8) ^ 16 * 17 / ((Nat.factorial 16 : ℚ) * 16)) ^ 8

/-- [Outward rounding](goal) of [a rational value](hyp:x) to the next
multiple of one hundred millionth preserves an upper bound. -/
def prawitzRoundUp (x : ℚ) : ℚ :=
  (⌈100000000 * x⌉ : ℤ) / (100000000 : ℚ)

/-- [A rational input](hyp:x) is [no larger than its outward rounding](goal). -/
theorem prawitz_le_roundUp (x : ℚ) : x ≤ prawitzRoundUp x := by
  have h := Int.le_ceil (100000000 * x)
  unfold prawitzRoundUp
  exact (le_div_iff₀ (by norm_num : (0 : ℚ) < 100000000)).2 (by
    simpa only [mul_comm] using h)

/-- [Casting the rational Taylor polynomial](hyp:x) gives
[the real Taylor polynomial with exactly the same terms](goal). -/
theorem prawitzTaylor16_cast (x : ℚ) :
    (prawitzTaylor16 x : ℝ) =
      ∑ m ∈ range 16, (x : ℝ) ^ m / (m.factorial : ℝ) := by
  simp [prawitzTaylor16]

/-- At [a nonnegative real argument](hyp:x,hx),
[the sixteen-term Taylor polynomial is positive and no larger than
the exponential](goal). -/
theorem prawitz_taylor16_pos_le_exp (x : ℝ) (hx : 0 ≤ x) :
    0 < (∑ m ∈ range 16, x ^ m / (m.factorial : ℝ)) ∧
      (∑ m ∈ range 16, x ^ m / (m.factorial : ℝ)) ≤ Real.exp x := by
  have hone : (1 : ℝ) ≤ ∑ m ∈ range 16, x ^ m / (m.factorial : ℝ) := by
    simpa using (single_le_sum
      (f := fun m : ℕ => x ^ m / (m.factorial : ℝ))
      (fun m _ => by positivity) (show 0 ∈ range 16 by decide))
  exact ⟨lt_of_lt_of_le (by norm_num) hone, Real.sum_le_exp_of_nonneg hx 16⟩

/-- At [a nonnegative rational argument](hyp:x,hx),
[the reciprocal Taylor polynomial encloses the negative exponential](goal). -/
theorem prawitz_exp_neg_le_reciprocal_taylor16 (x : ℚ) (hx : 0 ≤ x) :
    Real.exp (-(x : ℝ)) ≤ (1 / prawitzTaylor16 x : ℚ) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have h := prawitz_taylor16_pos_le_exp (x : ℝ) hx'
  rw [Real.exp_neg]
  push_cast
  rw [prawitzTaylor16_cast]
  simpa only [one_div] using one_div_le_one_div_of_le h.1 h.2

/-- On [the nonnegative interval through eight](hyp:x,hx,hx8),
[the rational eighth-power Taylor remainder encloses the exponential](goal). -/
theorem prawitz_exp_le_upper8 (x : ℚ) (hx : 0 ≤ x) (hx8 : x ≤ 8) :
    Real.exp (x : ℝ) ≤ (prawitzExpUpper8 x : ℝ) := by
  have hx' : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hx8' : (x : ℝ) ≤ 8 := by exact_mod_cast hx8
  have h := Real.exp_bound' (x := (x : ℝ) / 8)
    (by positivity) (by linarith) (n := 16) (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg _) h 8
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have heq : 8 * ((x : ℝ) / 8) = x := by ring
  rw [heq] at hp
  norm_num [prawitzExpUpper8, prawitzTaylor16_cast] at hp ⊢
  exact hp

/-- [The rational endpoints 314159/100000 and 314160/100000 used by the compact
certificates enclose π](goal). Both inequalities follow from Mathlib's proved
decimal bounds. -/
theorem prawitz_rational_pi_bounds :
    (314159 / 100000 : ℝ) ≤ Real.pi ∧ Real.pi ≤ 314160 / 100000 := by
  constructor
  · linarith [Real.pi_gt_d6]
  · linarith [Real.pi_lt_d4]

end Causalean.Stat.CLT.BerryEsseen
