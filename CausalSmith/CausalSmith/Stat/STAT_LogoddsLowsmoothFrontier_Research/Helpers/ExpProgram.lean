module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PiProgram

/-! # Register certificate for the prescribed exponential recurrence

Two copies of the successive-term loop evaluate the scalar endpoint brackets.
The instruction count is a fixed rational computation of the public truncation counts.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Successive terms multiply by the argument and divide by the next index. [the stated conclusion](goal) holds. -/
-- @node: expRegister_term_succ
lemma expRegister_term_succ (j : ℕ) (z : ℚ) :
    (z^j / (Nat.factorial j : ℚ) * z) / (j+1 : ℕ) =
      z^(j+1) / (Nat.factorial (j+1) : ℚ) := by
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  rw [mul_comm (↑j + 1 : ℚ), ← div_div]
  ring

/-- The two scalar loops retain the original precision and right endpoint in spare registers. -/
-- @node: expRegisterCode
def expRegisterCode : RationalProgram :=
  [.copy 16 0, .copy 20 2, .constant 18 0, .constant 12 0,
   .floor 14 0, .max 14 14 12, .constant 8 1, .constant 9 2,
   .copy 4 1, .constant 13 (-1), .mul 13 4 13, .max 11 4 13,
   .ceil 11 11, .max 11 11 8, .mul 2 11 11, .mul 2 2 9,
   .constant 13 6, .add 13 14 13, .max 2 2 13, .mul 2 2 9,
   .constant 5 1, .constant 6 0, .constant 3 1, .branchLe 2 12 30 24,
   .add 6 6 5, .mul 5 5 4, .div 5 5 3, .add 3 3 8,
   .sub 2 2 8, .jump 23, .constant 13 3, .add 13 14 13,
   .natPow 9 9 13, .div 8 8 9, .sub 0 6 8, .add 1 6 8,
   .constant 13 3, .natPow 13 13 11, .constant 8 1, .div 13 8 13,
   .max 0 13 0, .min 17 0 1, .max 1 0 1, .copy 0 17,
   .copy 18 0, .copy 0 16, .copy 1 20, .constant 12 0,
   .floor 14 0, .max 14 14 12, .constant 8 1, .constant 9 2,
   .copy 4 1, .constant 13 (-1), .mul 13 4 13, .max 11 4 13,
   .ceil 11 11, .max 11 11 8, .mul 2 11 11, .mul 2 2 9,
   .constant 13 6, .add 13 14 13, .max 2 2 13, .mul 2 2 9,
   .constant 5 1, .constant 6 0, .constant 3 1, .branchLe 2 12 74 68,
   .add 6 6 5, .mul 5 5 4, .div 5 5 3, .add 3 3 8,
   .sub 2 2 8, .jump 67, .constant 13 3, .add 13 14 13,
   .natPow 9 9 13, .div 8 8 9, .sub 0 6 8, .add 1 6 8,
   .constant 13 3, .natPow 13 13 11, .constant 8 1, .div 13 8 13,
   .max 0 13 0, .min 17 0 1, .max 1 0 1, .copy 0 17,
   .copy 0 18, .halt]

/-- The loop head records the partial sum, current term, counter, and untouched frame. -/
-- @node: ExpRegisterInvariant
structure ExpRegisterInvariant (right : Bool) (q j remaining : ℕ) (z : ℚ)
    (original left endpoint : ℚ) (s : RationalState) : Prop where
  pc : s.1 = (if right then 67 else 23)
  active : s.2.2 = false
  count : s.2.1 2 = remaining
  index : s.2.1 3 = (j+1 : ℕ)
  argument : s.2.1 4 = z
  term : s.2.1 5 = z^j/(Nat.factorial j : ℚ)
  sum : s.2.1 6 = ∑ i ∈ Finset.range j, z^i/(Nat.factorial i : ℚ)
  one : s.2.1 8 = 1
  two : s.2.1 9 = 2
  bound : s.2.1 11 = seriesBound z
  zero : s.2.1 12 = 0
  precision : s.2.1 14 = q
  original : s.2.1 16 = original
  left : s.2.1 18 = left
  endpoint : s.2.1 20 = endpoint

/-- Initialization computes the prescribed count from any rational argument and precision. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: expRegisterCode_initial
lemma expRegisterCode_initial (right : Bool) (s : RationalState)
    (hp : s.1 = (if right then 47 else 3)) (ha : s.2.2 = false) :
    let q := (⌊s.2.1 0⌋ : ℤ).toNat
    let z := s.2.1 1
    ExpRegisterInvariant right q 0 (2*seriesCount q z) z
      (s.2.1 16) (s.2.1 18) (s.2.1 20) (expRegisterCode.run 20 s) := by
  have hq : max (↑(⌊s.2.1 0⌋ : ℤ) : ℚ) 0 =
      ((⌊s.2.1 0⌋ : ℤ).toNat : ℚ) := by
    exact_mod_cast (show max (⌊s.2.1 0⌋ : ℤ) 0 =
      (((⌊s.2.1 0⌋ : ℤ).toNat : ℕ) : ℤ) by omega)
  have habs (z : ℚ) : max z (-z) = |z| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz, max_eq_left (by linarith)]
    · rw [abs_of_neg (lt_of_not_ge hz), max_eq_right (by linarith)]
  have hB (z : ℚ) : max (↑(⌈|z|⌉ : ℤ) : ℚ) 1 = (seriesBound z : ℚ) := by
    have hn := Int.ceil_nonneg (abs_nonneg z)
    have hc : ((⌈|z|⌉ : ℤ).toNat : ℚ) = (⌈|z|⌉ : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simp only [seriesBound, Nat.cast_max, Nat.cast_one, hc]
    exact max_comm _ _
  cases right <;>
    generalize he : expRegisterCode.run 20 s = t
  all_goals
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hq, habs, hB] at he
    subst t
    constructor <;> norm_num [Function.update_apply, seriesCount,
      Nat.cast_max, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] <;> ring

/-- [Seven instructions add a term and advance the exponential recurrence.](goal) Under [the stated assumptions](hyp:l). Under [the stated assumptions](hyp:h). -/
-- @node: expRegisterCode_round
lemma expRegisterCode_round (right : Bool) (q j N : ℕ) (z a l e : ℚ) (s : RationalState)
    (h : ExpRegisterInvariant right q j (N + 1) z a l e s) :
    ExpRegisterInvariant right q (j+1) N z a l e (expRegisterCode.run 7 s) := by
  rcases h with ⟨hp, ha, hc, hi, hz, ht, hs, h1, h2, hB, h0, hq, ho, hl, he⟩
  have hcpos : ¬ (s.2.1 2 ≤ s.2.1 12) := by
    rw [hc, h0]
    exact not_le.mpr (by positivity)
  cases right <;> generalize hh : expRegisterCode.run 7 s = t
  all_goals
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hcpos] at hh
    subst t
    constructor <;> norm_num [Function.update_apply, hc, hi, hz, ht, hs,
      h1, h2, hB, h0, hq, ho, hl, he, Finset.sum_range_succ, Nat.cast_add]
    · convert expRegister_term_succ j z using 1 <;> push_cast <;> ring

/-- [At zero count the scalar exit sorts its prescribed positive-floor bracket.](goal) Under [the stated assumptions](hyp:l,h). -/
-- @node: expRegisterCode_exit
lemma expRegisterCode_exit (right : Bool) (q j : ℕ) (z a l e : ℚ) (s : RationalState)
    (h : ExpRegisterInvariant right q j 0 z a l e s) :
    let S := ∑ i ∈ Finset.range j, z^i/(Nat.factorial i : ℚ)
    let A := max (1/(3 : ℚ)^seriesBound z) (S-rationalError (q+3))
    let B := S+rationalError (q+3)
    let t := expRegisterCode.run 15 s
    t.1 = (if right then 88 else 44) ∧ t.2.2 = false ∧
    t.2.1 0 = min A B ∧ t.2.1 1 = max A B ∧
    t.2.1 16 = a ∧ t.2.1 18 = l ∧ t.2.1 20 = e := by
  rcases h with ⟨hp, ha, hc, hi, hz, ht, hs, h1, h2, hB, h0, hq, ho, hl, he⟩
  have hnat : ((q : ℤ)+3).toNat = q+3 := by omega
  have hbound : (⌊(seriesBound z : ℚ)⌋ : ℤ).toNat = seriesBound z := by simp
  cases right <;>
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, hs, h1, h2, hB, h0, hq, ho, hl, he,
      rationalError, ← Nat.cast_add, hnat, hbound]

/-- [The fixed loop count exhausts all terms before the scalar exit.](goal) Under [the stated assumptions](hyp:l,h). -/
-- @node: expRegisterCode_loop
lemma expRegisterCode_loop (right : Bool) (q j N : ℕ) (z a l e : ℚ) (s : RationalState)
    (h : ExpRegisterInvariant right q j N z a l e s) :
    let S := ∑ i ∈ Finset.range (j+N), z^i/(Nat.factorial i : ℚ)
    let A := max (1/(3 : ℚ)^seriesBound z) (S-rationalError (q+3))
    let B := S+rationalError (q+3)
    let t := expRegisterCode.run (7*N+15) s
    t.1 = (if right then 88 else 44) ∧ t.2.2 = false ∧
    t.2.1 0 = min A B ∧ t.2.1 1 = max A B ∧
    t.2.1 16 = a ∧ t.2.1 18 = l ∧ t.2.1 20 = e := by
  induction N generalizing j s with
  | zero => simpa using expRegisterCode_exit right q j z a l e s h
  | succ N ih =>
      rw [show 7*(N+1)+15 = 7+(7*N+15) by omega, rationalProgram_run_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (j+1) _ (expRegisterCode_round right q j N z a l e s h)

/-- The initial frame saves the right endpoint before the left scalar loop. [the stated conclusion](goal) holds. -/
-- @node: expRegisterCode_start
lemma expRegisterCode_start (xs : List ℚ) :
    ExpRegisterInvariant false (⌊xs[0]?.getD 0⌋ : ℤ).toNat 0
      (2*seriesCount (⌊xs[0]?.getD 0⌋ : ℤ).toNat (xs[1]?.getD 0))
      (xs[1]?.getD 0) (xs[0]?.getD 0) 0 (xs[2]?.getD 0)
      (expRegisterCode.run 23 (RationalProgram.initial xs)) := by
  rw [show 23 = 3+20 by rfl, rationalProgram_run_add]
  have hp : (expRegisterCode.run 3 (RationalProgram.initial xs)).1 = 3 := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, RationalProgram.initial]
  have ha : (expRegisterCode.run 3 (RationalProgram.initial xs)).2.2 = false := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, RationalProgram.initial]
  have h := expRegisterCode_initial false _ hp ha
  convert h using 1 <;>
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]

/-- The two scalar loops have a public count determined by the input precision and endpoints. -/
-- @node: expRegisterFuel
def expRegisterFuel (xs : List ℚ) : ℕ :=
  78 + 7*(2*seriesCount (⌊xs[0]?.getD 0⌋ : ℤ).toNat (xs[1]?.getD 0) +
    2*seriesCount (⌊xs[0]?.getD 0⌋ : ℤ).toNat (xs[2]?.getD 0))

/-- Both endpoint loops return the literal endpoint extension, on every rational input list. [the stated conclusion](goal) holds. -/
-- @node: expRegisterCode_result
lemma expRegisterCode_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let lo := (paperExpScalar q (xs[1]?.getD 0)).lo
    let hi := (paperExpScalar q (xs[2]?.getD 0)).hi
    let t := expRegisterCode.run (expRegisterFuel xs) (RationalProgram.initial xs)
    t.2.2 = true ∧ t.2.1 0 = lo ∧ t.2.1 1 = hi := by
  let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
  let z := xs[1]?.getD 0
  let w := xs[2]?.getD 0
  let N := 2*seriesCount q z
  let M := 2*seriesCount q w
  have h := expRegisterCode_loop false q 0 N z _ 0 w _ (expRegisterCode_start xs)
  dsimp only [expRegisterFuel]
  have hf : 78+7*(N+M) = 23+(7*N+15)+(3+20)+(7*M+15)+2 := by omega
  rw [hf, rationalProgram_run_add _ (23+(7*N+15)+(3+20)+(7*M+15)) 2,
    rationalProgram_run_add _ (23+(7*N+15)+(3+20)) (7*M+15),
    rationalProgram_run_add _ (23+(7*N+15)) (3+20),
    rationalProgram_run_add _ 23 (7*N+15)]
  generalize hs : expRegisterCode.run (7*N+15)
    (expRegisterCode.run 23 (RationalProgram.initial xs)) = s at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
  rcases h with ⟨hp, ha, hlo, hhi, hq, hl, hw⟩
  have hp' : (expRegisterCode.run 3 s).1 = 47 := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have ha' : (expRegisterCode.run 3 s).2.2 = false := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have hinit := expRegisterCode_initial true (expRegisterCode.run 3 s) hp' ha'
  have h0 : (expRegisterCode.run 3 s).2.1 0 = xs[0]?.getD 0 := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hq]
  have h1 : (expRegisterCode.run 3 s).2.1 1 = w := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hw]
  have h18 : (expRegisterCode.run 3 s).2.1 18 = (paperExpScalar q z).lo := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hlo, paperExpScalar, rationalBox, expPolynomial, N]
  simp only [h0, h1] at hinit
  have hright := expRegisterCode_loop true q 0 M w _ _ _ _ hinit
  rw [rationalProgram_run_add _ 3 20]
  generalize ht : expRegisterCode.run (7*M+15)
    (expRegisterCode.run 20 (expRegisterCode.run 3 s)) = t at hright ⊢
  simp only [↓reduceIte, zero_add] at hright
  rcases hright with ⟨htp, hta, _, hthi, _, htl, _⟩
  rw [h18] at htl
  norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, htp, hta, hthi, htl, paperExpScalar, rationalBox,
    expPolynomial, M, q, z, w]

/-- A straight-line register program computes the complete two-endpoint instruction count. -/
-- @node: expRegisterFuelCode
def expRegisterFuelCode : RationalProgram :=
  [.copy 20 2] ++
  [.constant 12 0, .floor 14 0, .max 14 14 12, .constant 8 1,
   .constant 9 2, .copy 4 1, .constant 13 (-1), .mul 13 4 13,
   .max 11 4 13, .ceil 11 11, .max 11 11 8, .mul 2 11 11,
   .mul 2 2 9, .constant 13 6, .add 13 14 13, .max 2 2 13,
   .mul 2 2 9, .constant 5 1, .constant 6 0, .constant 3 1] ++
  [.copy 21 2, .copy 1 20] ++
  [.constant 12 0, .floor 14 0, .max 14 14 12, .constant 8 1,
   .constant 9 2, .copy 4 1, .constant 13 (-1), .mul 13 4 13,
   .max 11 4 13, .ceil 11 11, .max 11 11 8, .mul 2 11 11,
   .mul 2 2 9, .constant 13 6, .add 13 14 13, .max 2 2 13,
   .mul 2 2 9, .constant 5 1, .constant 6 0, .constant 3 1] ++
  [.add 2 2 21, .constant 13 7, .mul 0 2 13,
   .constant 13 78, .add 0 0 13, .halt]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
-- Expanding the 49-instruction bound computation needs extra simplifier resources.
/-- The step bound is itself computed by a total finite rational program. [the stated conclusion](goal) holds. -/
-- @node: expRegisterFuel_public
lemma expRegisterFuel_public : PublicIterationBound expRegisterFuel := by
  refine ⟨expRegisterFuelCode, ?_⟩
  intro xs
  have hq : max (↑(⌊xs[0]?.getD 0⌋ : ℤ) : ℚ) 0 =
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) := by
    exact_mod_cast (show max (⌊xs[0]?.getD 0⌋ : ℤ) 0 =
      (((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℕ) : ℤ) by omega)
  have habs (z : ℚ) : max z (-z) = |z| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz, max_eq_left (by linarith)]
    · rw [abs_of_neg (lt_of_not_ge hz), max_eq_right (by linarith)]
  have hB (z : ℚ) : max (↑(⌈|z|⌉ : ℤ) : ℚ) 1 = (seriesBound z : ℚ) := by
    have hn := Int.ceil_nonneg (abs_nonneg z)
    have hc : ((⌈|z|⌉ : ℤ).toNat : ℚ) = (⌈|z|⌉ : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simp only [seriesBound, Nat.cast_max, Nat.cast_one, hc]
    exact max_comm _ _
  refine ⟨49, ?_, ?_⟩
  · norm_num [expRegisterFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]
  · norm_num [expRegisterFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply, expRegisterFuel, seriesCount,
      Nat.cast_add, Nat.cast_mul, Nat.cast_max, Nat.cast_pow, hq, habs, hB]
    ring

/-- The publicly bounded two-endpoint exponential program halts on every rational list. [the stated conclusion](goal) holds. -/
-- @node: expRegisterCode_halts
lemma expRegisterCode_halts (xs : List ℚ) :
    (expRegisterCode.run (expRegisterFuel xs) (RationalProgram.initial xs)).2.2 = true := by
  exact (expRegisterCode_result xs).1

/-- Certified finite register implementation of exponential endpoint extension. -/
-- @node: expRegisterProgram
def expRegisterProgram : BoundedRationalProgram where
  code := expRegisterCode
  iterationBound := expRegisterFuel
  public_bound := expRegisterFuel_public
  halts := expRegisterCode_halts

/-- The register output agrees with the prescribed concrete exponential interval. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_exp_register_certificate
lemma concreteEngine_exp_register_certificate (q : ℕ) (I : RatInterval) :
    concreteEngine.expBox q I =
      let v := expRegisterProgram.eval [q, I.lo, I.hi]; rationalBox v.1 v.2 := by
  have h := expRegisterCode_result [(q : ℚ), I.lo, I.hi]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] at h
  dsimp only [concreteEngine, endpointExtension, BoundedRationalProgram.eval,
    expRegisterProgram]
  rw [h.2.1, h.2.2]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
