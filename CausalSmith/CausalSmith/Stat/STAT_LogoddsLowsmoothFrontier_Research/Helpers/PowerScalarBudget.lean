module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerScalarFusion

/-! # Public fuel for the full scalar power register program

A conservative rational count bounds the literal logarithm and exponential loops
on all rational inputs, including inputs outside the primitive's analytic domain.
The scalar code and its argument-specific truncation counts are unchanged.
-/
@[expose] public section
set_option maxRecDepth 8192
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The number of odd terms evaluated in the power logarithm. -/
-- @node: powerLogTermCount
def powerLogTermCount (q b : ℕ) : ℕ :=
  logRangeBound b*(powerRegisterPrecision q b+3+Nat.clog 2 (8*logRangeBound b)+2)

/-- Each atanh term has magnitude at most one for a nonnegative integer base. [the stated conclusion](goal) holds. -/
-- @node: powerLogPolynomial_abs_le
lemma powerLogPolynomial_abs_le (q b : ℕ) :
    |logPolynomial (powerRegisterPrecision q b) b| ≤ 2*(powerLogTermCount q b : ℚ) := by
  have hb : (0 : ℚ) ≤ b := by positivity
  have hr : |((b : ℚ)-1)/((b : ℚ)+1)| ≤ 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℚ) < b+1)]
    apply (div_le_one (by positivity)).mpr
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have ht (j : ℕ) : |(((b : ℚ)-1)/((b : ℚ)+1))^(2*j+1)/(2*j+1 : ℕ)| ≤ 1 := by
    rw [abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℚ) < (2*j+1 : ℕ))]
    apply (div_le_one (by positivity)).mpr
    have hp : |((b : ℚ)-1)/((b : ℚ)+1)|^(2*j+1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hr
    exact hp.trans (by norm_cast; omega)
  unfold logPolynomial
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℚ) < 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    |∑ j ∈ Finset.range (powerLogTermCount q b),
      (((b : ℚ)-1)/((b : ℚ)+1))^(2*j+1)/(2*j+1 : ℕ)|
        ≤ ∑ j ∈ Finset.range (powerLogTermCount q b),
          |(((b : ℚ)-1)/((b : ℚ)+1))^(2*j+1)/(2*j+1 : ℕ)| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range (powerLogTermCount q b), (1 : ℚ) :=
      Finset.sum_le_sum (fun j _ => ht j)
    _ = (powerLogTermCount q b : ℚ) := by simp

/-- Original-input bound for the exponential argument's integer range. -/
-- @node: powerScalarSeriesBound
def powerScalarSeriesBound (q b : ℕ) (v : ℚ) : ℕ :=
  max 1 (⌈2*(powerLogTermCount q b : ℚ)*|v|⌉ : ℤ).toNat

/-- The bound depends only on the original precision, base, and rational exponent. -/
-- @node: powerScalarPublicFuel
def powerScalarPublicFuel (xs : List ℚ) : ℕ :=
  let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
  let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
  let p := powerRegisterPrecision q b
  let B := powerScalarSeriesBound q b (xs[2]?.getD 0)
  161+7*powerLogTermCount q b+28*max (2*B^2) (p+6)

/-- The logarithm midpoint gives no larger range bound than the original-input count. [the stated conclusion](goal) holds. -/
-- @node: powerScalarSeriesBound_le
lemma powerScalarSeriesBound_le (q b : ℕ) (v : ℚ) :
    seriesBound (v*((paperLogScalar (powerRegisterPrecision q b) b).lo+
      (paperLogScalar (powerRegisterPrecision q b) b).hi)/2) ≤
      powerScalarSeriesBound q b v := by
  rw [show v*((paperLogScalar (powerRegisterPrecision q b) b).lo+
    (paperLogScalar (powerRegisterPrecision q b) b).hi)/2 =
    v*(((paperLogScalar (powerRegisterPrecision q b) b).lo+
    (paperLogScalar (powerRegisterPrecision q b) b).hi)/2) by ring,
    paperLogScalar_midpoint]
  have h : |v*(if 0 < (b : ℚ) then logPolynomial (powerRegisterPrecision q b) b else 0)| ≤
      2*(powerLogTermCount q b : ℚ)*|v| := by
    rw [abs_mul]
    split
    · nlinarith [powerLogPolynomial_abs_le q b, abs_nonneg v]
    · simp only [abs_zero, mul_zero]; positivity
  exact max_le_max_left 1 (Int.toNat_le_toNat (Int.ceil_mono h))

/-- The fixed original-input fuel covers the exact fused scalar run. [the stated conclusion](goal) holds. -/
-- @node: powerScalarFuel_le_public
lemma powerScalarFuel_le_public (xs : List ℚ) :
    powerScalarFuel xs ≤ powerScalarPublicFuel xs := by
  have h := powerLogCode_before_halt xs
  dsimp only at h
  rw [← powerLogActiveFuel] at h
  obtain ⟨_, _, hp, hm, _, hv, _⟩ := h
  have hB := powerScalarSeriesBound_le (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    (⌊xs[1]?.getD 0⌋ : ℤ).toNat (xs[2]?.getD 0)
  have hM : seriesCount (powerRegisterPrecision (⌊xs[0]?.getD 0⌋ : ℤ).toNat
      (⌊xs[1]?.getD 0⌋ : ℤ).toNat)
      (xs[2]?.getD 0 * (((paperLogScalar
        (powerRegisterPrecision (⌊xs[0]?.getD 0⌋ : ℤ).toNat
          (⌊xs[1]?.getD 0⌋ : ℤ).toNat) (⌊xs[1]?.getD 0⌋ : ℤ).toNat).lo+
        (paperLogScalar (powerRegisterPrecision (⌊xs[0]?.getD 0⌋ : ℤ).toNat
          (⌊xs[1]?.getD 0⌋ : ℤ).toNat) (⌊xs[1]?.getD 0⌋ : ℤ).toNat).hi)/2)) ≤
      max (2*powerScalarSeriesBound (⌊xs[0]?.getD 0⌋ : ℤ).toNat
        (⌊xs[1]?.getD 0⌋ : ℤ).toNat (xs[2]?.getD 0)^2)
        (powerRegisterPrecision (⌊xs[0]?.getD 0⌋ : ℤ).toNat
          (⌊xs[1]?.getD 0⌋ : ℤ).toNat+6) := by
    unfold seriesCount
    apply max_le_max_right
    gcongr
    simpa only [mul_div_assoc] using hB
  simp only [powerScalarFuel, powerExpClipFuel, powerExpFrameFuel, expRegisterFuel,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    hp, hm, hv, Int.floor_natCast, Int.toNat_natCast]
  dsimp only [powerScalarPublicFuel, powerLogActiveFuel, powerLogFuel, powerLogTermCount] at *
  omega

/-- A literal straight-line program computes the conservative scalar fuel. -/
-- @node: powerScalarPublicFuelCode
def powerScalarPublicFuelCode : RationalProgram :=
  powerLogFuelCode.take 36 ++
  [.mul 5 2 9, .constant 10 (-1), .mul 10 18 10, .max 6 18 10,
   .mul 5 5 6, .ceil 5 5, .max 5 5 8, .mul 5 5 5, .mul 5 5 9,
   .constant 6 6, .add 6 14 6, .max 5 5 6,
   .constant 6 28, .mul 5 5 6, .constant 6 7, .mul 0 2 6,
   .add 0 0 5, .constant 6 161, .add 0 0 6, .halt]

set_option maxHeartbeats 1500000 in
-- Enumerating the 36 literal instruction positions needs extra simplifier resources.
/-- The fuel program uses the same logarithm initialization instructions. Under the stated assumptions. [The stated hypotheses](hyp:hs,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerScalarPublicFuelCode_prefix_step
lemma powerScalarPublicFuelCode_prefix_step (s : RationalState) (hs : s.1 < 36)
    (ha : s.2.2 = false) :
    powerScalarPublicFuelCode.step s = powerLogCode.step s := by
  generalize hp : s.1 = pc at hs
  interval_cases pc <;>
    simp [powerScalarPublicFuelCode, powerLogFuelCode, powerLogCode,
      RationalProgram.step, hp, ha]

/-- [Every initialization step is identical in the fuel and scalar programs.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: powerScalarPublicFuelCode_prefix
lemma powerScalarPublicFuelCode_prefix (xs : List ℚ) (n : ℕ) (hn : n ≤ 36) :
    powerScalarPublicFuelCode.run n (RationalProgram.initial xs) =
      powerLogCode.run n (RationalProgram.initial xs) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨_, hp, ha⟩ := powerLogFuelCode_prefix_run xs n (by omega)
    rw [rationalProgram_run_add _ n 1, rationalProgram_run_add _ n 1, ih (by omega)]
    exact powerScalarPublicFuelCode_prefix_step _ (by rw [hp]; omega) ha

set_option maxHeartbeats 1500000 in
-- Expanding the 20 arithmetic instructions after initialization needs extra resources.
/-- The complete original-input bound is computed by finite rational instructions. [the stated conclusion](goal) holds. -/
-- @node: powerScalarPublicFuel_public
lemma powerScalarPublicFuel_public : PublicIterationBound powerScalarPublicFuel := by
  refine ⟨powerScalarPublicFuelCode, ?_⟩
  intro xs
  have h := powerLogCode_initial xs
  have habs (z : ℚ) : max z (-z) = |z| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz, max_eq_left (by linarith)]
    · rw [abs_of_neg (lt_of_not_ge hz), max_eq_right (by linarith)]
  have hceil (x : ℚ) (hx : 0 ≤ x) :
      max (↑(⌈x⌉ : ℤ) : ℚ) 1 = (max 1 (⌈x⌉ : ℤ).toNat : ℕ) := by
    have hc : ((⌈x⌉ : ℤ).toNat : ℚ) = (⌈x⌉ : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.ceil_nonneg hx)
    simp only [Nat.cast_max, Nat.cast_one, hc, max_comm]
  refine ⟨56, ?_, ?_⟩
  all_goals
    rw [show 56 = 36+20 by rfl, rationalProgram_run_add,
      powerScalarPublicFuelCode_prefix xs 36 (by omega)]
    generalize he : powerLogCode.run 36 (RationalProgram.initial xs) = t at h ⊢
    rcases h with ⟨hp, ha, hc, _, _, _, _, _, h1, h2, _, _, hq, hl, _, _⟩
    norm_num [powerScalarPublicFuelCode, powerLogFuelCode, RationalProgram.run,
      RationalProgram.step, Function.update_apply, hp, ha, hc, h1, h2, hq, hl,
      powerScalarPublicFuel, powerScalarSeriesBound, powerLogTermCount,
      Nat.cast_add, Nat.cast_mul, Nat.cast_max, Nat.cast_pow, habs]
  rw [show ∀ N : ℚ, N*2*|xs[2]?.getD 0| =
    2*N*|xs[2]?.getD 0| by intro N; ring]
  rw [hceil _ (by positivity)]
  push_cast
  ring

/-- Sufficient extra steps leave the already halted scalar output unchanged. [the stated conclusion](goal) holds. -/
-- @node: powerScalarCode_public_result
lemma powerScalarCode_public_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let t := powerScalarCode.run (powerScalarPublicFuel xs) (RationalProgram.initial xs)
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) =
      paperPowerScalar q b (xs[2]?.getD 0) := by
  have h := powerScalarCode_result xs
  dsimp only at h
  have hf := powerScalarFuel_le_public xs
  rw [show powerScalarPublicFuel xs = powerScalarFuel xs+
    (powerScalarPublicFuel xs-powerScalarFuel xs) by omega,
    rationalProgram_run_add, rationalProgram_run_halted _ _ _ h.1]
  exact h

/-- A certified single register program implements the entire scalar power routine. -/
-- @node: powerScalarProgram
def powerScalarProgram : BoundedRationalProgram where
  code := powerScalarCode
  iterationBound := powerScalarPublicFuel
  public_bound := powerScalarPublicFuel_public
  halts := fun xs => (powerScalarCode_public_result xs).1

/-- The bounded scalar register evaluation returns the prescribed paper bracket. [the stated conclusion](goal) holds. -/
-- @node: powerScalarProgram_eval
lemma powerScalarProgram_eval (q b : ℕ) (v w : ℚ) :
    let endpoints := powerScalarProgram.eval [q,b,v,w]
    rationalBox endpoints.1 endpoints.2 = paperPowerScalar q b v := by
  have h := powerScalarCode_public_result [(q : ℚ),b,v,w]
  simpa only [BoundedRationalProgram.eval, powerScalarProgram,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] using h.2

end CausalSmith.Stat.LogoddsLowsmoothFrontier
