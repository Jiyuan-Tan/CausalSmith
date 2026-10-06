module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PiProgram

/-! # Register certificate for the prescribed logarithm recurrence

Two endpoint loops compute the odd-power sum using the exact public count.
Nonpositive scalar arguments return the prescribed zero point.
-/
@[expose] public section
set_option maxRecDepth 2048
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The integer range bound is computed by clamping the two signed ceilings. [the stated conclusion](goal) holds. -/
-- @node: logRegister_bound_cast
lemma logRegister_bound_cast (z : ℚ) :
    max (max (↑(⌈z⌉ : ℤ) : ℚ) (↑(⌈1/z⌉ : ℤ) : ℚ)) 2 =
      (logRangeBound z : ℚ) := by
  have h (a b : ℤ) : max (max a b) 2 =
      ((max 2 (max a.toNat b.toNat) : ℕ) : ℤ) := by omega
  exact_mod_cast h (⌈z⌉ : ℤ) (⌈1/z⌉ : ℤ)

/-- The two-endpoint logarithm register code. -/
-- @node: logRegisterCode
def logRegisterCode : RationalProgram :=
  [.copy 16 0,
   .copy 20 2,
   .constant 18 0,
   .constant 12 0,
   .floor 14 0,
   .max 14 14 12,
   .constant 8 1,
   .constant 9 2,
   .copy 7 1,
   .ceil 11 1,
   .div 13 8 1,
   .ceil 13 13,
   .max 11 11 13,
   .max 11 11 9,
   .constant 10 8,
   .mul 13 11 10,
   .clogTwo 13 13,
   .constant 10 5,
   .add 10 14 10,
   .add 10 10 13,
   .mul 2 11 10,
   .sub 4 1 8,
   .add 13 1 8,
   .div 4 4 13,
   .mul 10 4 4,
   .copy 5 4,
   .constant 6 0,
   .constant 3 1,
   .branchLe 2 12 35 29,
   .div 13 5 3,
   .add 6 6 13,
   .mul 5 5 10,
   .add 3 3 9,
   .sub 2 2 8,
   .jump 28,
   .branchLe 7 12 45 36,
   .mul 6 6 9,
   .constant 13 3,
   .add 13 14 13,
   .natPow 9 9 13,
   .div 8 8 9,
   .sub 0 6 8,
   .add 1 6 8,
   .copy 13 13,
   .jump 54,
   .constant 0 0,
   .constant 1 0,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .jump 54,
   .min 17 0 1,
   .max 1 0 1,
   .copy 0 17,
   .copy 18 0,
   .copy 0 16,
   .copy 1 20,
   .constant 12 0,
   .floor 14 0,
   .max 14 14 12,
   .constant 8 1,
   .constant 9 2,
   .copy 7 1,
   .ceil 11 1,
   .div 13 8 1,
   .ceil 13 13,
   .max 11 11 13,
   .max 11 11 9,
   .constant 10 8,
   .mul 13 11 10,
   .clogTwo 13 13,
   .constant 10 5,
   .add 10 14 10,
   .add 10 10 13,
   .mul 2 11 10,
   .sub 4 1 8,
   .add 13 1 8,
   .div 4 4 13,
   .mul 10 4 4,
   .copy 5 4,
   .constant 6 0,
   .constant 3 1,
   .branchLe 2 12 92 86,
   .div 13 5 3,
   .add 6 6 13,
   .mul 5 5 10,
   .add 3 3 9,
   .sub 2 2 8,
   .jump 85,
   .branchLe 7 12 102 93,
   .mul 6 6 9,
   .constant 13 3,
   .add 13 14 13,
   .natPow 9 9 13,
   .div 8 8 9,
   .sub 0 6 8,
   .add 1 6 8,
   .copy 13 13,
   .jump 111,
   .constant 0 0,
   .constant 1 0,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .copy 13 13,
   .jump 111,
   .min 17 0 1,
   .max 1 0 1,
   .copy 0 17,
   .copy 0 18,
   .halt]

/-- The loop head records the odd index, power, partial sum and untouched frame. -/
-- @node: LogRegisterInvariant
structure LogRegisterInvariant (right : Bool) (q j remaining : ℕ) (z : ℚ)
    (original left endpoint : ℚ) (s : RationalState) : Prop where
  pc : s.1 = (if right then 85 else 28)
  active : s.2.2 = false
  count : s.2.1 2 = remaining
  index : s.2.1 3 = (2*j+1 : ℕ)
  argument : s.2.1 4 = (z-1)/(z+1)
  term : s.2.1 5 = ((z-1)/(z+1))^(2*j+1)
  sum : s.2.1 6 = ∑ i ∈ Finset.range j,
    ((z-1)/(z+1))^(2*i+1)/(2*i+1 : ℕ)
  scalar : s.2.1 7 = z
  one : s.2.1 8 = 1
  two : s.2.1 9 = 2
  ratio : s.2.1 10 = ((z-1)/(z+1))^2
  zero : s.2.1 12 = 0
  precision : s.2.1 14 = q
  original : s.2.1 16 = original
  left : s.2.1 18 = left
  endpoint : s.2.1 20 = endpoint

set_option maxHeartbeats 1000000 in
-- Expanding the fixed register block needs extra simplifier resources.
/-- Initialization computes the literal logarithm truncation count. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: logRegisterCode_initial
lemma logRegisterCode_initial (right : Bool) (s : RationalState)
    (hp : s.1 = (if right then 60 else 3)) (ha : s.2.2 = false) :
    let q := (⌊s.2.1 0⌋ : ℤ).toNat
    let z := s.2.1 1
    LogRegisterInvariant right q 0
      (logRangeBound z * (q+3+Nat.clog 2 (8*logRangeBound z)+2)) z
      (s.2.1 16) (s.2.1 18) (s.2.1 20) (logRegisterCode.run 25 s) := by
  have hq : max (↑(⌊s.2.1 0⌋ : ℤ) : ℚ) 0 =
      ((⌊s.2.1 0⌋ : ℤ).toNat : ℚ) := by
    exact_mod_cast (show max (⌊s.2.1 0⌋ : ℤ) 0 =
      (((⌊s.2.1 0⌋ : ℤ).toNat : ℕ) : ℤ) by omega)
  have hb (z : ℚ) : max (max (↑(⌈z⌉ : ℤ) : ℚ) (↑(⌈z⁻¹⌉ : ℤ) : ℚ)) 2 =
      (logRangeBound z : ℚ) := by simpa only [one_div] using logRegister_bound_cast z
  have hc (z : ℚ) : (⌊(logRangeBound z : ℚ)*8⌋ : ℤ).toNat =
      8*logRangeBound z := by
    rw [show (logRangeBound z : ℚ)*8 = (8*logRangeBound z : ℕ) by push_cast; ring]
    norm_cast
  cases right <;> generalize he : logRegisterCode.run 25 s = t
  all_goals
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hq, hb, hc] at he
    subst t
    constructor <;> norm_num [Function.update_apply, Nat.cast_mul, Nat.cast_add, hb, hc]
    all_goals (ring <;> simp)

/-- [One seven-instruction block adds the next odd-power term.](goal) Under [the stated assumptions](hyp:l). Under [the stated assumptions](hyp:h). -/
-- @node: logRegisterCode_round
lemma logRegisterCode_round (right : Bool) (q j N : ℕ) (z a l e : ℚ)
    (s : RationalState) (h : LogRegisterInvariant right q j (N + 1) z a l e s) :
    LogRegisterInvariant right q (j+1) N z a l e (logRegisterCode.run 7 s) := by
  rcases h with ⟨hp, ha, hc, hi, hz, ht, hs, hscalar, h1, h2, hr, h0, hq, ho, hl, he⟩
  have hcpos : ¬ (s.2.1 2 ≤ s.2.1 12) := by
    rw [hc, h0]
    exact not_le.mpr (by positivity)
  cases right <;> generalize hh : logRegisterCode.run 7 s = t
  all_goals
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hcpos] at hh
    subst t
    constructor <;> norm_num [Function.update_apply, hc, hi, hz, ht, hs,
      hscalar, h1, h2, hr, h0, hq, ho, hl, he,
      Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul]
    · ring
    · rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add]
      ring

/-- [At zero count both branches return the prescribed sorted scalar endpoints.](goal) Under [the stated assumptions](hyp:l,h). -/
-- @node: logRegisterCode_exit
lemma logRegisterCode_exit (right : Bool) (q j : ℕ) (z a l e : ℚ)
    (s : RationalState) (h : LogRegisterInvariant right q j 0 z a l e s) :
    let S := 2*∑ i ∈ Finset.range j, ((z-1)/(z+1))^(2*i+1)/(2*i+1 : ℕ)
    let A := if 0 < z then S-rationalError (q+3) else 0
    let B := if 0 < z then S+rationalError (q+3) else 0
    let t := logRegisterCode.run 14 s
    t.1 = (if right then 114 else 57) ∧ t.2.2 = false ∧
    t.2.1 0 = min A B ∧ t.2.1 1 = max A B ∧
    t.2.1 16 = a ∧ t.2.1 18 = l ∧ t.2.1 20 = e := by
  rcases h with ⟨hp, ha, hc, hi, hz, ht, hs, hscalar, h1, h2, hr, h0, hq, ho, hl, he⟩
  have hnat : ((q : ℤ)+3).toNat = q+3 := by omega
  by_cases hzpos : 0 < z
  · have hzle : ¬ z ≤ 0 := not_le.mpr hzpos
    have hn : ¬ s.2.1 7 ≤ s.2.1 12 := by rw [hscalar, h0]; exact not_le.mpr hzpos
    cases right <;>
      norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
        Function.update_apply, hp, ha, hc, hs, hscalar, h1, h2, h0, hq, ho, hl, he,
        rationalError, ← Nat.cast_add, hnat, hn, hzpos, hzle] <;> ring <;> simp
  · have hzle : z ≤ 0 := le_of_not_gt hzpos
    have hn : s.2.1 7 ≤ s.2.1 12 := by rw [hscalar, h0]; exact le_of_not_gt hzpos
    cases right <;>
      norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
        Function.update_apply, hp, ha, hc, hs, hscalar, h1, h2, h0, hq, ho, hl, he,
        hn, hzpos, hzle]

/-- [The fixed term loop exhausts its counter before the scalar exit.](goal) Under [the stated assumptions](hyp:l,h). -/
-- @node: logRegisterCode_loop
lemma logRegisterCode_loop (right : Bool) (q j N : ℕ) (z a l e : ℚ)
    (s : RationalState) (h : LogRegisterInvariant right q j N z a l e s) :
    let S := 2*∑ i ∈ Finset.range (j+N), ((z-1)/(z+1))^(2*i+1)/(2*i+1 : ℕ)
    let A := if 0 < z then S-rationalError (q+3) else 0
    let B := if 0 < z then S+rationalError (q+3) else 0
    let t := logRegisterCode.run (7*N+14) s
    t.1 = (if right then 114 else 57) ∧ t.2.2 = false ∧
    t.2.1 0 = min A B ∧ t.2.1 1 = max A B ∧
    t.2.1 16 = a ∧ t.2.1 18 = l ∧ t.2.1 20 = e := by
  induction N generalizing j s with
  | zero => simpa using logRegisterCode_exit right q j z a l e s h
  | succ N ih =>
      rw [show 7*(N+1)+14 = 7+(7*N+14) by omega, rationalProgram_run_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (j+1) _ (logRegisterCode_round right q j N z a l e s h)

/-- The initial frame saves the right endpoint before the left scalar loop. [the stated conclusion](goal) holds. -/
-- @node: logRegisterCode_start
lemma logRegisterCode_start (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let z := xs[1]?.getD 0
    LogRegisterInvariant false q 0
      (logRangeBound z*(q+3+Nat.clog 2 (8*logRangeBound z)+2)) z
      (xs[0]?.getD 0) 0 (xs[2]?.getD 0)
      (logRegisterCode.run 28 (RationalProgram.initial xs)) := by
  rw [show 28 = 3+25 by rfl, rationalProgram_run_add]
  have hp : (logRegisterCode.run 3 (RationalProgram.initial xs)).1 = 3 := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step, RationalProgram.initial]
  have ha : (logRegisterCode.run 3 (RationalProgram.initial xs)).2.2 = false := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step, RationalProgram.initial]
  have h := logRegisterCode_initial false _ hp ha
  convert h using 1 <;>
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]

/-- The instruction bound includes two endpoint initializations, loops and exits. -/
-- @node: logRegisterFuel
def logRegisterFuel (xs : List ℚ) : ℕ :=
  let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
  let count := fun z => logRangeBound z*(q+3+Nat.clog 2 (8*logRangeBound z)+2)
  86+7*(count (xs[1]?.getD 0)+count (xs[2]?.getD 0))

/-- Both endpoint loops return the literal endpoint extension on every rational list. [the stated conclusion](goal) holds. -/
-- @node: logRegisterCode_result
lemma logRegisterCode_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let lo := (paperLogScalar q (xs[1]?.getD 0)).lo
    let hi := (paperLogScalar q (xs[2]?.getD 0)).hi
    let t := logRegisterCode.run (logRegisterFuel xs) (RationalProgram.initial xs)
    t.2.2 = true ∧ t.2.1 0 = lo ∧ t.2.1 1 = hi := by
  let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
  let z := xs[1]?.getD 0
  let w := xs[2]?.getD 0
  let N := logRangeBound z*(q+3+Nat.clog 2 (8*logRangeBound z)+2)
  let M := logRangeBound w*(q+3+Nat.clog 2 (8*logRangeBound w)+2)
  have h := logRegisterCode_loop false q 0 N z _ 0 w _ (logRegisterCode_start xs)
  dsimp only [logRegisterFuel]
  have hf : 86+7*(N+M) = 28+(7*N+14)+(3+25)+(7*M+14)+2 := by omega
  rw [hf, rationalProgram_run_add _ (28+(7*N+14)+(3+25)+(7*M+14)) 2,
    rationalProgram_run_add _ (28+(7*N+14)+(3+25)) (7*M+14),
    rationalProgram_run_add _ (28+(7*N+14)) (3+25),
    rationalProgram_run_add _ 28 (7*N+14)]
  generalize hs : logRegisterCode.run (7*N+14)
    (logRegisterCode.run 28 (RationalProgram.initial xs)) = s at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
  rcases h with ⟨hp, ha, hlo, hhi, hq, hl, hw⟩
  have hp' : (logRegisterCode.run 3 s).1 = 60 := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have ha' : (logRegisterCode.run 3 s).2.2 = false := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have hinit := logRegisterCode_initial true (logRegisterCode.run 3 s) hp' ha'
  have h0 : (logRegisterCode.run 3 s).2.1 0 = xs[0]?.getD 0 := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hq]
  have h1 : (logRegisterCode.run 3 s).2.1 1 = w := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hw]
  have h18 : (logRegisterCode.run 3 s).2.1 18 = (paperLogScalar q z).lo := by
    norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hlo, paperLogScalar, rationalBox, logPolynomial, N]
    split <;> simp_all [RatInterval.point]
  simp only [h0, h1] at hinit
  have hright := logRegisterCode_loop true q 0 M w _ _ _ _ hinit
  rw [rationalProgram_run_add _ 3 25]
  generalize ht : logRegisterCode.run (7*M+14)
    (logRegisterCode.run 25 (logRegisterCode.run 3 s)) = t at hright ⊢
  simp only [↓reduceIte, zero_add] at hright
  rcases hright with ⟨htp, hta, _, hthi, _, htl, _⟩
  rw [h18] at htl
  norm_num [logRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, htp, hta, hthi, htl, paperLogScalar, rationalBox,
    logPolynomial, M, q, z, w]
  split <;> simp_all [RatInterval.point]

/-- A straight-line program computes the public count of both endpoint loops. -/
-- @node: logRegisterFuelCode
def logRegisterFuelCode : RationalProgram :=
  [.copy 20 2,
   .constant 12 0,
   .floor 14 0,
   .max 14 14 12,
   .constant 8 1,
   .constant 9 2,
   .copy 7 1,
   .ceil 11 1,
   .div 13 8 1,
   .ceil 13 13,
   .max 11 11 13,
   .max 11 11 9,
   .constant 10 8,
   .mul 13 11 10,
   .clogTwo 13 13,
   .constant 10 5,
   .add 10 14 10,
   .add 10 10 13,
   .mul 2 11 10,
   .sub 4 1 8,
   .add 13 1 8,
   .div 4 4 13,
   .mul 10 4 4,
   .copy 5 4,
   .constant 6 0,
   .constant 3 1,
   .copy 21 2,
   .copy 1 20,
   .constant 12 0,
   .floor 14 0,
   .max 14 14 12,
   .constant 8 1,
   .constant 9 2,
   .copy 7 1,
   .ceil 11 1,
   .div 13 8 1,
   .ceil 13 13,
   .max 11 11 13,
   .max 11 11 9,
   .constant 10 8,
   .mul 13 11 10,
   .clogTwo 13 13,
   .constant 10 5,
   .add 10 14 10,
   .add 10 10 13,
   .mul 2 11 10,
   .sub 4 1 8,
   .add 13 1 8,
   .div 4 4 13,
   .mul 10 4 4,
   .copy 5 4,
   .constant 6 0,
   .constant 3 1,
   .add 2 2 21,
   .constant 13 7,
   .mul 0 2 13,
   .constant 13 86,
   .add 0 0 13,
   .halt]

set_option maxHeartbeats 1000000 in
-- Expanding the fixed register block needs extra simplifier resources.
/-- The instruction count is itself a finite rational register computation. [the stated conclusion](goal) holds. -/
-- @node: logRegisterFuel_public
lemma logRegisterFuel_public : PublicIterationBound logRegisterFuel := by
  refine ⟨logRegisterFuelCode, ?_⟩
  intro xs
  have hq : max (↑(⌊xs[0]?.getD 0⌋ : ℤ) : ℚ) 0 =
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) := by
    exact_mod_cast (show max (⌊xs[0]?.getD 0⌋ : ℤ) 0 =
      (((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℕ) : ℤ) by omega)
  have hb (z : ℚ) : max (max (↑(⌈z⌉ : ℤ) : ℚ) (↑(⌈z⁻¹⌉ : ℤ) : ℚ)) 2 =
      (logRangeBound z : ℚ) := by simpa only [one_div] using logRegister_bound_cast z
  have hc (z : ℚ) : (⌊(logRangeBound z : ℚ)*8⌋ : ℤ).toNat =
      8*logRangeBound z := by
    rw [show (logRangeBound z : ℚ)*8 = (8*logRangeBound z : ℕ) by push_cast; ring]
    norm_cast
  refine ⟨59, ?_, ?_⟩
  · norm_num [logRegisterFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]
  · norm_num [logRegisterFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply, logRegisterFuel,
      Nat.cast_add, Nat.cast_mul, hq, hb, hc]
    ring

/-- The fixed public count halts the logarithm computation on every rational list. [the stated conclusion](goal) holds. -/
-- @node: logRegisterCode_halts
lemma logRegisterCode_halts (xs : List ℚ) :
    (logRegisterCode.run (logRegisterFuel xs) (RationalProgram.initial xs)).2.2 = true := by
  exact (logRegisterCode_result xs).1

/-- Certified finite rational register implementation of both logarithm endpoints. -/
-- @node: logRegisterProgram
def logRegisterProgram : BoundedRationalProgram where
  code := logRegisterCode
  iterationBound := logRegisterFuel
  public_bound := logRegisterFuel_public
  halts := logRegisterCode_halts

/-- The finite register result equals the prescribed logarithm endpoint extension. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_log_register_certificate
lemma concreteEngine_log_register_certificate (q : ℕ) (I : RatInterval) :
    concreteEngine.logBox q I =
      let v := logRegisterProgram.eval [q, I.lo, I.hi]; rationalBox v.1 v.2 := by
  have h := logRegisterCode_result [(q : ℚ), I.lo, I.hi]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] at h
  dsimp only [concreteEngine, endpointExtension, BoundedRationalProgram.eval,
    logRegisterProgram]
  rw [h.2.1, h.2.2]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
