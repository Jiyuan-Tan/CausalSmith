module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LogProgram

/-! # The logarithm stage of the integer-base power register computation

This stage computes the prescribed internal precision and the midpoint of its
logarithm bracket. Its output retains the integer base and both exponent endpoints
for the exponential continuation. The complete power certificate remains separate.
-/
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Internal precision used by the literal power algorithm. -/
-- @node: powerRegisterPrecision
def powerRegisterPrecision (q b : ℕ) : ℕ := q+12+3*Nat.clog 2 (max 2 b)

/-- The sorted logarithm bracket has the same midpoint as its unsorted endpoints. [the stated conclusion](goal) holds. -/
-- @node: paperLogScalar_midpoint
lemma paperLogScalar_midpoint (p : ℕ) (z : ℚ) :
    ((paperLogScalar p z).lo+(paperLogScalar p z).hi)/2 =
      if 0 < z then logPolynomial p z else 0 := by
  by_cases hz : 0 < z
  · simp only [paperLogScalar, if_pos hz, rationalBox]
    rw [min_add_max]
    ring
  · simp [paperLogScalar, hz, RatInterval.point]

/-- Single logarithm loop, retaining the original base and exponent endpoints.
Register zero returns the internal precision and register one the logarithm midpoint. -/
-- @node: powerLogCode
def powerLogCode : RationalProgram :=
  [.copy 18 2, .copy 20 3, .constant 12 0,
   .floor 14 0, .max 14 14 12, .floor 21 1, .max 21 21 12,
   .constant 9 2, .max 22 9 21, .clogTwo 13 22,
   .constant 10 3, .mul 13 13 10, .add 14 14 13,
   .constant 10 12, .add 14 14 10,
   .copy 7 21, .constant 8 1,
   .ceil 11 7, .div 13 8 7, .ceil 13 13,
   .max 11 11 13, .max 11 11 9,
   .constant 10 8, .mul 13 11 10, .clogTwo 13 13,
   .constant 10 5, .add 10 14 10, .add 10 10 13, .mul 2 11 10,
   .sub 4 7 8, .add 13 7 8, .div 4 4 13,
   .mul 10 4 4, .copy 5 4, .constant 6 0, .constant 3 1,
   .branchLe 2 12 43 37,
   .div 13 5 3, .add 6 6 13, .mul 5 5 10,
   .add 3 3 9, .sub 2 2 8, .jump 36,
   .branchLe 7 12 46 44,
   .mul 1 6 9, .jump 47,
   .constant 1 0,
   .copy 0 14, .copy 2 21, .copy 3 18, .copy 4 20, .halt]

/-- The loop frame keeps the power data while generating the odd logarithm terms. -/
-- @node: PowerLogInvariant
structure PowerLogInvariant (p b j remaining : ℕ) (lo hi : ℚ)
    (s : RationalState) : Prop where
  pc : s.1 = 36
  active : s.2.2 = false
  count : s.2.1 2 = remaining
  odd : s.2.1 3 = (2*j+1 : ℕ)
  coordinate : s.2.1 4 = ((b : ℚ)-1)/((b : ℚ)+1)
  term : s.2.1 5 = (((b : ℚ)-1)/((b : ℚ)+1))^(2*j+1)
  sum : s.2.1 6 = ∑ i ∈ Finset.range j,
    (((b : ℚ)-1)/((b : ℚ)+1))^(2*i+1)/(2*i+1 : ℕ)
  scalar : s.2.1 7 = b
  one : s.2.1 8 = 1
  two : s.2.1 9 = 2
  ratio : s.2.1 10 = (((b : ℚ)-1)/((b : ℚ)+1))^2
  zero : s.2.1 12 = 0
  precision : s.2.1 14 = p
  left : s.2.1 18 = lo
  right : s.2.1 20 = hi
  base : s.2.1 21 = b

/-- Signed rational inputs are clamped to their prescribed natural-number interpretations. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerRegister_clamp_cast
lemma powerRegister_clamp_cast (x : ℚ) :
    max (↑(⌊x⌋ : ℤ) : ℚ) 0 = ((⌊x⌋ : ℤ).toNat : ℚ) := by
  exact_mod_cast (show max (⌊x⌋ : ℤ) 0 =
    (((⌊x⌋ : ℤ).toNat : ℕ) : ℤ) by omega)

/-- [The short preparation block clamps the two integers and computes internal precision. [the stated conclusion](goal) holds. -/
-- @node: powerLogCode_prepare
lemma powerLogCode_prepare (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let t := powerLogCode.run 15 (RationalProgram.initial xs)
    t.1 = 15 ∧ t.2.2 = false ∧ t.2.1 14 = powerRegisterPrecision q b ∧
      t.2.1 21 = b ∧ t.2.1 18 = xs[2]?.getD 0 ∧
      t.2.1 20 = xs[3]?.getD 0 ∧ t.2.1 9 = 2 ∧ t.2.1 12 = 0 := by
  have hB (b : ℕ) : max (2 : ℚ) b = (max 2 b : ℕ) := by push_cast; rfl
  have hclog (b : ℕ) : (⌊max (2 : ℚ) b⌋ : ℤ).toNat = max 2 b := by
    rw [hB]; simp only [Int.floor_natCast, Int.toNat_natCast]
  rw [show 15 = 7+8 by rfl, rationalProgram_run_add]
  have hf :
      let t := powerLogCode.run 7 (RationalProgram.initial xs)
      t.1 = 7 ∧ t.2.2 = false ∧
        t.2.1 14 = ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) ∧
        t.2.1 21 = ((⌊xs[1]?.getD 0⌋ : ℤ).toNat : ℚ) ∧
        t.2.1 18 = xs[2]?.getD 0 ∧ t.2.1 20 = xs[3]?.getD 0 ∧
        t.2.1 12 = 0 := by
    generalize he : powerLogCode.run 7 (RationalProgram.initial xs) = t
    norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply, powerRegister_clamp_cast] at he
    subst t
    norm_num [Function.update_apply]
  generalize he : powerLogCode.run 7 (RationalProgram.initial xs) = t at hf ⊢
  obtain ⟨hp, ha, hq, hb, hl, hu, h0⟩ := hf
  generalize he' : powerLogCode.run 8 t = u
  norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha, hq, hb, hclog] at he'
  subst u
  norm_num [Function.update_apply, hq, hb, hl, hu, h0, hclog,
    powerRegisterPrecision, Nat.cast_mul, Nat.cast_add]
  ring

/-- The initialization suffix prepares the literal logarithm loop. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha,hq,hb',hl,hu,h2,h0) hold, and [the stated conclusion follows](goal). -/
-- @node: powerLogCode_initialize_loop
lemma powerLogCode_initialize_loop (p b : ℕ) (lo hi : ℚ) (s : RationalState)
    (hp : s.1 = 15) (ha : s.2.2 = false) (hq : s.2.1 14 = p)
    (hb' : s.2.1 21 = b) (hl : s.2.1 18 = lo) (hu : s.2.1 20 = hi)
    (h2 : s.2.1 9 = 2) (h0 : s.2.1 12 = 0) :
    PowerLogInvariant p b 0
      (logRangeBound b*(p+3+Nat.clog 2 (8*logRangeBound b)+2)) lo hi
      (powerLogCode.run 21 s) := by
  have hb (z : ℚ) : max (max (↑(⌈z⌉ : ℤ) : ℚ) (↑(⌈z⁻¹⌉ : ℤ) : ℚ)) 2 =
      (logRangeBound z : ℚ) := by simpa only [one_div] using logRegister_bound_cast z
  have hc (z : ℚ) : (⌊(logRangeBound z : ℚ)*8⌋ : ℤ).toNat =
      8*logRangeBound z := by
    rw [show (logRangeBound z : ℚ)*8 = (8*logRangeBound z : ℕ) by push_cast; ring]
    norm_cast
  have hbNat : max (max (b : ℚ) (↑(⌈(b : ℚ)⁻¹⌉ : ℤ) : ℚ)) 2 =
      (logRangeBound b : ℚ) := by simpa using hb (b : ℚ)
  generalize he : powerLogCode.run 21 s = t
  norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha, hq, hb', hl, hu, h2, h0, hb, hbNat, hc] at he
  subst t
  constructor <;> norm_num [Function.update_apply, hq, hb', hl, hu, h2, h0, hbNat, hc, Nat.cast_mul, Nat.cast_add]
  all_goals (ring <;> try simp)

/-- [Initialization computes exactly the internal precision and the logarithm count. [the stated conclusion](goal) holds. -/
-- @node: powerLogCode_initial
lemma powerLogCode_initial (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let p := powerRegisterPrecision q b
    PowerLogInvariant p b 0
      (logRangeBound b*(p+3+Nat.clog 2 (8*logRangeBound b)+2))
      (xs[2]?.getD 0) (xs[3]?.getD 0)
      (powerLogCode.run 36 (RationalProgram.initial xs)) := by
  rw [show 36 = 15+21 by rfl, rationalProgram_run_add]
  obtain ⟨hp, ha, hq, hb, hl, hu, h2, h0⟩ := powerLogCode_prepare xs
  exact powerLogCode_initialize_loop _ _ _ _ _ hp ha hq hb hl hu h2 h0

/-- A seven-instruction block adds precisely one logarithm term. Under the stated assumptions. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerLogCode_round
lemma powerLogCode_round (p b j N : ℕ) (lo hi : ℚ) (s : RationalState)
    (h : PowerLogInvariant p b j (N+1) lo hi s) :
    PowerLogInvariant p b (j+1) N lo hi (powerLogCode.run 7 s) := by
  rcases h with ⟨hp, ha, hc, hi', hz, ht, hs, hb, h1, h2, hr, h0, hq, hl, hu, hb'⟩
  have hpos : ¬ s.2.1 2 ≤ s.2.1 12 := by
    rw [hc, h0]; exact not_le.mpr (by positivity)
  generalize he : powerLogCode.run 7 s = t
  norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha, hpos] at he
  subst t
  constructor <;> norm_num [Function.update_apply, hc, hi', hz, ht, hs, hb,
    h1, h2, hr, h0, hq, hl, hu, hb', Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul]
  · ring
  · rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add]
    ring

/-- [Both domain branches return the midpoint and retain the continuation inputs.](goal) Under [the stated assumptions](hyp:hi,h). -/
-- @node: powerLogCode_exit
lemma powerLogCode_exit (p b j : ℕ) (lo hi : ℚ) (s : RationalState)
    (h : PowerLogInvariant p b j 0 lo hi s) :
    let S := 2*∑ i ∈ Finset.range j,
      (((b : ℚ)-1)/((b : ℚ)+1))^(2*i+1)/(2*i+1 : ℕ)
    let t := powerLogCode.run 9 s
    t.2.2 = true ∧ t.2.1 0 = p ∧ t.2.1 1 = (if 0 < b then S else 0) ∧
      t.2.1 2 = b ∧ t.2.1 3 = lo ∧ t.2.1 4 = hi := by
  rcases h with ⟨hp, ha, hc, hi', hz, ht, hs, hb, h1, h2, hr, h0, hq, hl, hu, hb'⟩
  by_cases hpos : 0 < b
  · have hn : ¬ s.2.1 7 ≤ s.2.1 12 := by
      rw [hb, h0]; exact not_le.mpr (by exact_mod_cast hpos)
    rw [h0] at hn
    generalize he : powerLogCode.run 9 s = t
    norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, h0, hn] at he
    subst t
    norm_num [Function.update_apply, hs, h2, hq, hl, hu, hb', hpos]
    ring
  · have hn : s.2.1 7 ≤ s.2.1 12 := by
      rw [hb, h0]; exact_mod_cast (le_of_not_gt hpos)
    rw [h0] at hn
    generalize he : powerLogCode.run 9 s = t
    norm_num [powerLogCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, h0, hn] at he
    subst t
    norm_num [Function.update_apply, hs, h2, hq, hl, hu, hb', hpos]

/-- [Exhaustion of the exact term count proves termination and the completed sum.](goal) Under [the stated assumptions](hyp:hi,h). -/
-- @node: powerLogCode_loop
lemma powerLogCode_loop (p b j N : ℕ) (lo hi : ℚ) (s : RationalState)
    (h : PowerLogInvariant p b j N lo hi s) :
    let S := 2*∑ i ∈ Finset.range (j+N),
      (((b : ℚ)-1)/((b : ℚ)+1))^(2*i+1)/(2*i+1 : ℕ)
    let t := powerLogCode.run (7*N+9) s
    t.2.2 = true ∧ t.2.1 0 = p ∧ t.2.1 1 = (if 0 < b then S else 0) ∧
      t.2.1 2 = b ∧ t.2.1 3 = lo ∧ t.2.1 4 = hi := by
  induction N generalizing j s with
  | zero => simpa using powerLogCode_exit p b j lo hi s h
  | succ N ih =>
    rw [show 7*(N+1)+9 = 7+(7*N+9) by omega, rationalProgram_run_add]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (j+1) _ (powerLogCode_round p b j N lo hi s h)

/-- [Public fuel of the logarithm preparation stage. -/
-- @node: powerLogFuel
def powerLogFuel (xs : List ℚ) : ℕ :=
  let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
  let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
  let p := powerRegisterPrecision q b
  45+7*(logRangeBound b*(p+3+Nat.clog 2 (8*logRangeBound b)+2))

/-- The stage computes the literal logarithm midpoint, including the totalized zero base. [the stated conclusion](goal) holds. -/
-- @node: powerLogCode_result
lemma powerLogCode_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let p := powerRegisterPrecision q b
    let L := paperLogScalar p b
    let t := powerLogCode.run (powerLogFuel xs) (RationalProgram.initial xs)
    t.2.2 = true ∧ t.2.1 0 = p ∧ t.2.1 1 = (L.lo+L.hi)/2 ∧
      t.2.1 2 = b ∧ t.2.1 3 = xs[2]?.getD 0 ∧ t.2.1 4 = xs[3]?.getD 0 := by
  have h := powerLogCode_loop _ _ 0 _ _ _ _ (powerLogCode_initial xs)
  dsimp only [powerLogFuel]
  rw [show ∀ N : ℕ, 45+7*N = 36+(7*N+9) by omega, rationalProgram_run_add]
  simpa only [zero_add, paperLogScalar_midpoint, logPolynomial,
    Nat.cast_pos] using h

/-- Straight-line computation of the public stage bound. -/
-- @node: powerLogFuelCode
def powerLogFuelCode : RationalProgram :=
  [.copy 18 2, .copy 20 3, .constant 12 0,
   .floor 14 0, .max 14 14 12, .floor 21 1, .max 21 21 12,
   .constant 9 2, .max 22 9 21, .clogTwo 13 22,
   .constant 10 3, .mul 13 13 10, .add 14 14 13,
   .constant 10 12, .add 14 14 10,
   .copy 7 21, .constant 8 1,
   .ceil 11 7, .div 13 8 7, .ceil 13 13,
   .max 11 11 13, .max 11 11 9,
   .constant 10 8, .mul 13 11 10, .clogTwo 13 13,
   .constant 10 5, .add 10 14 10, .add 10 10 13, .mul 2 11 10,
   .sub 4 7 8, .add 13 7 8, .div 4 4 13,
   .mul 10 4 4, .copy 5 4, .constant 6 0, .constant 3 1,
   .constant 3 7, .mul 0 2 3, .constant 3 45, .add 0 0 3, .halt]

/-- The two codes have identical straight-line instructions before the loop head. Under the stated assumptions. [The stated hypotheses](hyp:hs,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerLogFuelCode_prefix_step
lemma powerLogFuelCode_prefix_step (s : RationalState) (hs : s.1 < 36)
    (ha : s.2.2 = false) :
    powerLogFuelCode.step s = powerLogCode.step s ∧
      (powerLogCode.step s).1 = s.1+1 ∧ (powerLogCode.step s).2.2 = false := by
  generalize hp : s.1 = pc at hs
  interval_cases pc <;>
    simp [powerLogFuelCode, powerLogCode, RationalProgram.step, hp, ha]

/-- [The straight-line prefixes agree at each of their bounded instruction positions.](goal) Under [the stated assumptions](hyp:hn). -/
-- @node: powerLogFuelCode_prefix_run
lemma powerLogFuelCode_prefix_run (xs : List ℚ) (n : ℕ) (hn : n ≤ 36) :
    powerLogFuelCode.run n (RationalProgram.initial xs) =
      powerLogCode.run n (RationalProgram.initial xs) ∧
    (powerLogCode.run n (RationalProgram.initial xs)).1 = n ∧
    (powerLogCode.run n (RationalProgram.initial xs)).2.2 = false := by
  induction n with
  | zero => simp [RationalProgram.run, RationalProgram.initial]
  | succ n ih =>
    obtain ⟨he, hp, ha⟩ := ih (by omega)
    have hs := powerLogFuelCode_prefix_step
      (powerLogCode.run n (RationalProgram.initial xs)) (by rw [hp]; omega) ha
    rw [show n+1 = n+1 by rfl, rationalProgram_run_add, rationalProgram_run_add,
      he]
    simpa only [RationalProgram.run] using ⟨hs.1, by simpa [hp] using hs.2.1, hs.2.2⟩

/-- [The shared initialization prefix is the same computation. [the stated conclusion](goal) holds. -/
-- @node: powerLogFuelCode_prefix
lemma powerLogFuelCode_prefix (xs : List ℚ) :
    powerLogFuelCode.run 36 (RationalProgram.initial xs) =
      powerLogCode.run 36 (RationalProgram.initial xs) := by
  exact (powerLogFuelCode_prefix_run xs 36 (by omega)).1

/-- The prescribed fuel itself is a finite rational register computation. [the stated conclusion](goal) holds. -/
-- @node: powerLogFuel_public
lemma powerLogFuel_public : PublicIterationBound powerLogFuel := by
  refine ⟨powerLogFuelCode, ?_⟩
  intro xs
  have h := powerLogCode_initial xs
  refine ⟨41, ?_, ?_⟩
  all_goals
    rw [show 41 = 36+5 by rfl, rationalProgram_run_add, powerLogFuelCode_prefix]
    generalize he : powerLogCode.run 36 (RationalProgram.initial xs) = t at h ⊢
    rcases h with ⟨hp, ha, hc, _⟩
    norm_num [powerLogFuelCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, powerLogFuel, Nat.cast_add, Nat.cast_mul]
  ring

/-- The preparation stage halts at the proved public count on every rational input. -/
-- @node: powerLogProgram
def powerLogProgram : BoundedRationalProgram where
  code := powerLogCode
  iterationBound := powerLogFuel
  public_bound := powerLogFuel_public
  halts := fun xs => (powerLogCode_result xs).1

/-- The certified program supplies the literal midpoint needed by both scalar exponentials. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerLogProgram_eval
lemma powerLogProgram_eval (q b : ℕ) (lo hi : ℚ) :
    powerLogProgram.eval [q,b,lo,hi] =
      ((powerRegisterPrecision q b : ℚ),
        ((paperLogScalar (powerRegisterPrecision q b) b).lo+
         (paperLogScalar (powerRegisterPrecision q b) b).hi)/2) := by
  have h := powerLogCode_result [(q : ℚ), b, lo, hi]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] at h
  exact Prod.ext h.2.1 h.2.2.1

end CausalSmith.Stat.LogoddsLowsmoothFrontier
