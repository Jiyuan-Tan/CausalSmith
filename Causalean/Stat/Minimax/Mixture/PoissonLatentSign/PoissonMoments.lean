module
public import Causalean.Mathlib.Probability.Poisson.Moments
public import Causalean.Stat.Concentration.Poisson.RawMoments
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Poisson receipts for latent-sign coefficients

These scalar integrability and tilted moment identities support averaging
pointwise posterior bounds. They reuse the existing Poisson law, exponential
integrability, and descending-factorial infrastructure.
-/

public section

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.Poisson
open Causalean.Stat.Concentration.Poisson
namespace Causalean.Stat.Minimax.Mixture.PoissonLatentSign

/-- Every binomial coefficient in a Poisson count is integrable. -/
theorem integrable_poisson_choose (ξ : NNReal) (d : ℕ) :
    Integrable (fun m : ℕ => (m.choose d : ℝ)) (poissonMeasure ξ) := by
  have h := (poisson_descFactorial_integrable ξ d).div_const (d.factorial : ℝ)
  convert h using 1
  funext m
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
  simp [Nat.factorial_ne_zero]

/-- The expected order-d binomial coefficient of a Poisson count is the mean to d divided by d
  factorial. -/
theorem integral_poisson_choose (ξ : NNReal) (d : ℕ) :
    (∫ m : ℕ, (m.choose d : ℝ) ∂poissonMeasure ξ) =
      (ξ : ℝ) ^ d / (d.factorial : ℝ) := by
  calc
    (∫ m : ℕ, (m.choose d : ℝ) ∂poissonMeasure ξ) =
        ∫ m : ℕ, (m.descFactorial d : ℝ) / (d.factorial : ℝ) ∂poissonMeasure ξ := by
      congr 1
      funext m
      rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul]
      simp [Nat.factorial_ne_zero]
    _ = _ := by rw [integral_div, poisson_descFactorial_moment]

/-- Tilting a Poisson weight rescales it to the Poisson weight at the tilted rate. -/
private lemma poisson_weight_tilt (ξ b : NNReal) (m : ℕ) :
    Real.exp (-(ξ : ℝ)) * (ξ : ℝ) ^ m / (m.factorial : ℝ) * (b : ℝ) ^ m =
      Real.exp ((ξ : ℝ) * ((b : ℝ) - 1)) *
        (Real.exp (-((ξ * b : NNReal) : ℝ)) *
          ((ξ * b : NNReal) : ℝ) ^ m / (m.factorial : ℝ)) := by
  have he : Real.exp ((ξ : ℝ) * ((b : ℝ) - 1)) *
      Real.exp (-((ξ * b : NNReal) : ℝ)) = Real.exp (-(ξ : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [NNReal.coe_mul]
    ring
  simp only [NNReal.coe_mul, mul_pow]
  calc
    _ = Real.exp (-(ξ : ℝ)) * ((ξ : ℝ) ^ m * (b : ℝ) ^ m) /
        (m.factorial : ℝ) := by ring
    _ = _ := by rw [← he]; simp only [NNReal.coe_mul]; ring

/-- A descending factorial times a nonnegative exponential tilt is Poisson-integrable. -/
theorem integrable_poisson_tilted_factorial (ξ : NNReal) {a : ℝ}
    (ha : 0 ≤ a) (d : ℕ) :
    Integrable (fun m : ℕ => (m.descFactorial d : ℝ) * a ^ m)
      (poissonMeasure ξ) := by
  let b : NNReal := ⟨a, ha⟩
  have hs := integrable_poissonMeasure_iff.mp (poisson_descFactorial_integrable (ξ * b) d)
  rw [integrable_poissonMeasure_iff]
  apply (hs.mul_left (Real.exp ((ξ : ℝ) * (a - 1)))).congr
  intro m
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity : 0 ≤
    (m.descFactorial d : ℝ) * a ^ m), abs_of_nonneg (Nat.cast_nonneg _)]
  have hw := poisson_weight_tilt ξ b m
  change _ * a ^ m = Real.exp ((ξ : ℝ) * (a - 1)) *
    (Real.exp (-((ξ * b : NNReal) : ℝ)) *
      ((ξ * b : NNReal) : ℝ) ^ m / (m.factorial : ℝ)) at hw
  calc
    _ = (Real.exp ((ξ : ℝ) * (a - 1)) *
        (Real.exp (-((ξ * b : NNReal) : ℝ)) *
          ((ξ * b : NNReal) : ℝ) ^ m / (m.factorial : ℝ))) *
        (m.descFactorial d : ℝ) := by ring
    _ = _ := by rw [← hw]; ring

/-- The tilted factorial moment equals the tilted mean to its order times the Poisson exponential
  factor. -/
theorem integral_poisson_tilted_factorial (ξ : NNReal) {a : ℝ}
    (ha : 0 ≤ a) (d : ℕ) :
    (∫ m : ℕ, (m.descFactorial d : ℝ) * a ^ m ∂poissonMeasure ξ) =
      ((ξ : ℝ) * a) ^ d * Real.exp ((ξ : ℝ) * (a - 1)) := by
  let b : NNReal := ⟨a, ha⟩
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  calc
    _ = Real.exp ((ξ : ℝ) * (a - 1)) *
        ∑' m : ℕ, Real.exp (-((ξ * b : NNReal) : ℝ)) *
          ((ξ * b : NNReal) : ℝ) ^ m / (m.factorial : ℝ) *
            (m.descFactorial d : ℝ) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      have hw := poisson_weight_tilt ξ b m
      change _ * a ^ m = Real.exp ((ξ : ℝ) * (a - 1)) *
        (Real.exp (-((ξ * b : NNReal) : ℝ)) *
          ((ξ * b : NNReal) : ℝ) ^ m / (m.factorial : ℝ)) at hw
      calc
        _ = (Real.exp (-(ξ : ℝ)) * (ξ : ℝ) ^ m /
            (m.factorial : ℝ) * a ^ m) * (m.descFactorial d : ℝ) := by ring
        _ = _ := by rw [hw]; ring
    _ = _ := by
      have hm := poisson_descFactorial_moment (ξ * b) d
      rw [integral_poissonMeasure] at hm
      simp only [smul_eq_mul] at hm
      rw [hm]
      simp only [NNReal.coe_mul]
      change Real.exp ((ξ : ℝ) * (a - 1)) * ((ξ : ℝ) * a) ^ d = _
      ring

/-- The collision polynomial is the sum of the third and second descending factorials. -/
private lemma collision_factorial_identity (m : ℕ) :
    (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 =
      (m.descFactorial 3 : ℝ) + (m.descFactorial 2 : ℝ) := by
  rcases m with _ | (_ | m)
  · norm_num [Nat.descFactorial_succ]
  · norm_num [Nat.descFactorial_succ]
  · simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero,
      Nat.mul_one, Nat.cast_mul]
    have h1 : m + 1 + 1 - 1 = m + 1 := by omega
    have h2 : m + 1 + 1 - 2 = m := by omega
    simp only [h1, h2, Nat.cast_add, Nat.cast_one]
    ring

/-- The singleton collision polynomial times a nonnegative exponential tilt is integrable. -/
theorem integrable_poisson_collision_tilt (ξ : NNReal) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun m : ℕ => (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 * a ^ m)
      (poissonMeasure ξ) := by
  simp_rw [collision_factorial_identity, add_mul]
  exact (integrable_poisson_tilted_factorial ξ ha 3).add
    (integrable_poisson_tilted_factorial ξ ha 2)

/-- The tilted singleton collision moment is the sum of its second and third factorial moments. -/
theorem integral_poisson_collision_tilt (ξ : NNReal) {a : ℝ} (ha : 0 ≤ a) :
    (∫ m : ℕ, (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 * a ^ m ∂poissonMeasure ξ) =
      (((ξ : ℝ) * a) ^ 3 + ((ξ : ℝ) * a) ^ 2) *
        Real.exp ((ξ : ℝ) * (a - 1)) := by
  simp_rw [collision_factorial_identity, add_mul]
  rw [integral_add (integrable_poisson_tilted_factorial ξ ha 3)
    (integrable_poisson_tilted_factorial ξ ha 2),
    integral_poisson_tilted_factorial ξ ha 3,
    integral_poisson_tilted_factorial ξ ha 2]

/-- When [the Poisson mean ξ is at most one](hyp:hξ), [the mean of m(m − 1)²(25/9)ᵐ over
a Poisson count m is at most e^((5/3)² − 1) · ((5/3)⁶ + (5/3)⁴) · ξ²](goal). -/
theorem integral_poisson_collision_le {ξ : NNReal} (hξ : (ξ : ℝ) ≤ 1) :
    (∫ m : ℕ, (m : ℝ) * ((m - 1 : ℕ) : ℝ) ^ 2 *
      ((5 / 3 : ℝ) ^ 2) ^ m ∂poissonMeasure ξ) ≤
    Real.exp ((5 / 3 : ℝ) ^ 2 - 1) *
      ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4) * (ξ : ℝ) ^ 2 := by
  rw [integral_poisson_collision_tilt ξ (by positivity)]
  have hx : 0 ≤ (ξ : ℝ) := ξ.coe_nonneg
  have hc : (ξ : ℝ) ^ 3 ≤ (ξ : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (ξ : ℝ)]
  have he : Real.exp ((ξ : ℝ) * ((5 / 3 : ℝ) ^ 2 - 1)) ≤
      Real.exp ((5 / 3 : ℝ) ^ 2 - 1) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ (((ξ : ℝ) * ((5 / 3 : ℝ) ^ 2)) ^ 3 +
        ((ξ : ℝ) * ((5 / 3 : ℝ) ^ 2)) ^ 2) *
          Real.exp ((5 / 3 : ℝ) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ ≤ _ := by
      have hp : (((ξ : ℝ) * ((5 / 3 : ℝ) ^ 2)) ^ 3 +
          ((ξ : ℝ) * ((5 / 3 : ℝ) ^ 2)) ^ 2) ≤
          ((5 / 3 : ℝ) ^ 6 + (5 / 3 : ℝ) ^ 4) * (ξ : ℝ) ^ 2 := by
        nlinarith
      have hh := mul_le_mul_of_nonneg_right hp
        (Real.exp_pos ((5 / 3 : ℝ) ^ 2 - 1)).le
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hh

end Causalean.Stat.Minimax.Mixture.PoissonLatentSign
