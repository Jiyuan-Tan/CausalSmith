module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PiProgram

/-! # Finite register certificate for the prescribed cosine routine

The fixed program computes the midpoint polynomial by the successive-term
recurrence, sorts its scalar endpoints, and enlarges by the input half width.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The next cosine term is obtained by the prescribed rational multiplier. [the stated conclusion](goal) holds. -/
-- @node: cosRegister_term_succ
lemma cosRegister_term_succ (j : ℕ) (z : ℚ) :
    (((-1 : ℚ)^j*z^(2*j)/(Nat.factorial (2*j) : ℚ)) * (-z^2)) /
      ((2*j+1 : ℕ)*(2*j+2 : ℕ) : ℚ) =
      (-1 : ℚ)^(j+1)*z^(2*(j+1))/(Nat.factorial (2*(j+1)) : ℚ) := by
  rw [show 2*(j+1) = (2*j+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  rw [show 2*j+1+1 = 2*j+2 by omega, pow_add, pow_succ]
  have hf : (Nat.factorial (2*j) : ℚ) ≠ 0 := by positivity
  have h1 : (2*(j : ℚ)+1) ≠ 0 := by positivity
  have h2 : (2*(j : ℚ)+2) ≠ 0 := by positivity
  field_simp
  ring

/-- The finite midpoint cosine program, including the exact prescribed truncation count. -/
-- @node: cosRegisterCode
def cosRegisterCode : RationalProgram :=
  [.constant 12 0, .floor 14 0, .max 14 14 12,
   .constant 8 1, .constant 9 2,
   .add 4 1 2, .div 4 4 9, .sub 15 2 1, .div 15 15 9,
   .mul 10 4 4, .constant 13 (-1), .mul 10 10 13,
   .copy 11 4, .constant 13 (-1), .mul 13 4 13, .max 11 11 13,
   .ceil 11 11, .max 11 11 8, .mul 2 11 11, .mul 2 2 9,
   .constant 13 6, .add 13 14 13, .max 2 2 13,
   .constant 5 1, .constant 6 0, .constant 3 1,
   .branchLe 2 12 35 27,
   .add 6 6 5, .add 13 3 8, .mul 13 3 13, .mul 5 5 10,
   .div 5 5 13, .add 3 3 9, .sub 2 2 8, .jump 26,
   .constant 13 3, .add 13 14 13, .natPow 9 9 13, .div 8 8 9,
   .sub 0 6 8, .add 1 6 8, .constant 13 (-1), .max 0 13 0,
   .constant 16 1, .min 1 16 1,
   .min 17 0 1, .max 1 0 1, .copy 0 17,
   .sub 0 0 15, .add 1 1 15, .max 0 13 0, .min 1 16 1, .halt]

/-- Registers at the head of the cosine term loop. -/
-- @node: CosRegisterInvariant
structure CosRegisterInvariant (q j remaining : ℕ) (z w : ℚ) (s : RationalState) : Prop where
  pc : s.1 = 26
  active : s.2.2 = false
  count : s.2.1 2 = remaining
  odd : s.2.1 3 = (2*j+1 : ℕ)
  argument : s.2.1 4 = z
  term : s.2.1 5 = (-1 : ℚ)^j*z^(2*j)/(Nat.factorial (2*j) : ℚ)
  sum : s.2.1 6 = ∑ i ∈ Finset.range j, (-1 : ℚ)^i*z^(2*i)/(Nat.factorial (2*i) : ℚ)
  one : s.2.1 8 = 1
  two : s.2.1 9 = 2
  ratio : s.2.1 10 = -z^2
  zero : s.2.1 12 = 0
  precision : s.2.1 14 = q
  halfWidth : s.2.1 15 = w

/-- Initialization on arbitrary rational inputs clamps the precision to a natural number. [the stated conclusion](goal) holds. -/
-- @node: cosRegisterCode_initial
lemma cosRegisterCode_initial (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let z := (xs[1]?.getD 0 + xs[2]?.getD 0)/2
    let w := (xs[2]?.getD 0 - xs[1]?.getD 0)/2
    CosRegisterInvariant q 0 (seriesCount q z) z w
      (cosRegisterCode.run 26 (RationalProgram.initial xs)) := by
  have hq : max (↑(⌊xs[0]?.getD 0⌋ : ℤ) : ℚ) 0 =
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) := by
    exact_mod_cast (show max (⌊xs[0]?.getD 0⌋ : ℤ) 0 =
      (((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℕ) : ℤ) by omega)
  have habs (z : ℚ) : max z (-z) = |z| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz, max_eq_left (by linarith)]
    · rw [abs_of_neg (lt_of_not_ge hz), max_eq_right (by linarith)]
  have hB (z : ℚ) : max (↑(⌈|z|⌉ : ℤ) : ℚ) 1 = (seriesBound z : ℚ) := by
    have hn : 0 ≤ (⌈|z|⌉ : ℤ) := Int.ceil_nonneg (abs_nonneg z)
    have hc : ((⌈|z|⌉ : ℤ).toNat : ℚ) = (⌈|z|⌉ : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg hn
    simp only [seriesBound, Nat.cast_max, Nat.cast_one, hc]
    exact max_comm _ _
  generalize he : cosRegisterCode.run 26 (RationalProgram.initial xs) = t
  norm_num [cosRegisterCode, RationalProgram.run, RationalProgram.step,
    RationalProgram.initial, Function.update_apply, hq, habs, hB] at he
  subst t
  constructor <;> norm_num [Function.update_apply, seriesCount,
    Nat.cast_max, Nat.cast_mul, Nat.cast_pow, Nat.cast_add] <;> ring

/-- Each nine-instruction loop block adds one term and advances its multiplier. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:h). -/
-- @node: cosRegisterCode_round
lemma cosRegisterCode_round (q j N : ℕ) (z w : ℚ) (s : RationalState)
    (h : CosRegisterInvariant q j (N+1) z w s) :
    CosRegisterInvariant q (j+1) N z w (cosRegisterCode.run 9 s) := by
  rcases h with ⟨hp, ha, hc, ho, hz, ht, hs, h1, h2, hr, h0, hq, hw⟩
  have hcpos : ¬ (s.2.1 2 ≤ s.2.1 12) := by
    rw [hc, h0]
    exact not_le.mpr (by positivity)
  generalize he : cosRegisterCode.run 9 s = t
  norm_num [cosRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha, hcpos] at he
  subst t
  constructor <;> norm_num [Function.update_apply, hc, ho, hz, ht, hs,
    h1, h2, hr, h0, hq, hw, Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul]
  · ring
  · convert cosRegister_term_succ j z using 1 <;> push_cast <;> ring

/-- At zero count the exit block returns the literal scalar sorting and width enlargement. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: cosRegisterCode_exit
lemma cosRegisterCode_exit (q j : ℕ) (z w : ℚ) (s : RationalState)
    (h : CosRegisterInvariant q j 0 z w s) :
    let S := ∑ i ∈ Finset.range j, (-1 : ℚ)^i*z^(2*i)/(Nat.factorial (2*i) : ℚ)
    let a := max (-1) (S - rationalError (q+3))
    let b := min 1 (S + rationalError (q+3))
    let t := cosRegisterCode.run 20 s
    t.2.2 = true ∧ t.2.1 0 = max (-1) (min a b - w) ∧
      t.2.1 1 = min 1 (max a b + w) := by
  rcases h with ⟨hp, ha, hc, ho, hz, ht, hs, h1, h2, hr, h0, hq, hw⟩
  have hnat : ((q : ℤ)+3).toNat = q+3 := by omega
  norm_num [cosRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha, hc, hs, h1, h2, h0, hq, hw,
    rationalError, ← Nat.cast_add, hnat]

/-- [Iteration exhausts the prescribed term counter before executing the exit block.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: cosRegisterCode_loop
lemma cosRegisterCode_loop (q j N : ℕ) (z w : ℚ) (s : RationalState)
    (h : CosRegisterInvariant q j N z w s) :
    let S := ∑ i ∈ Finset.range (j+N), (-1 : ℚ)^i*z^(2*i)/(Nat.factorial (2*i) : ℚ)
    let a := max (-1) (S - rationalError (q+3))
    let b := min 1 (S + rationalError (q+3))
    let t := cosRegisterCode.run (9*N+20) s
    t.2.2 = true ∧ t.2.1 0 = max (-1) (min a b - w) ∧
      t.2.1 1 = min 1 (max a b + w) := by
  induction N generalizing j s with
  | zero => simpa using cosRegisterCode_exit q j z w s h
  | succ N ih =>
      rw [show 9*(N+1)+20 = 9+(9*N+20) by omega, rationalProgram_run_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (j+1) _ (cosRegisterCode_round q j N z w s h)

/-- The total public step count includes initialization, each term, and clipping. -/
-- @node: cosRegisterFuel
def cosRegisterFuel (xs : List ℚ) : ℕ :=
  26 + (9*seriesCount (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    ((xs[1]?.getD 0 + xs[2]?.getD 0)/2) + 20)

/-- A fixed straight-line program computes the public fuel from the same input bounds. -/
-- @node: cosRegisterFuelCode
def cosRegisterFuelCode : RationalProgram :=
  cosRegisterCode.take 26 ++
    [.constant 13 9, .mul 0 2 13, .constant 13 46, .add 0 0 13, .halt]

/-- The cosine fuel is itself a total finite rational register computation. [the stated conclusion](goal) holds. -/
-- @node: cosRegisterFuel_public
lemma cosRegisterFuel_public : PublicIterationBound cosRegisterFuel := by
  refine ⟨cosRegisterFuelCode, ?_⟩
  intro xs
  have hp : cosRegisterFuelCode.run 26 (RationalProgram.initial xs) =
      cosRegisterCode.run 26 (RationalProgram.initial xs) := by
    norm_num [cosRegisterFuelCode, cosRegisterCode, RationalProgram.run,
      RationalProgram.step, RationalProgram.initial, Function.update_apply]
  have h := cosRegisterCode_initial xs
  refine ⟨31, ?_, ?_⟩
  all_goals
    rw [show 31 = 26+5 by rfl, rationalProgram_run_add, hp]
    generalize he : cosRegisterCode.run 26 (RationalProgram.initial xs) = s at h ⊢
    norm_num [cosRegisterFuelCode, cosRegisterCode, RationalProgram.run,
      RationalProgram.step, Function.update_apply, h.pc, h.active, h.count,
      cosRegisterFuel, Nat.cast_add, Nat.cast_mul]
  ring

/-- The publicly bounded cosine computation halts on every rational input list. [the stated conclusion](goal) holds. -/
-- @node: cosRegisterCode_halts
lemma cosRegisterCode_halts (xs : List ℚ) :
    (cosRegisterCode.run (cosRegisterFuel xs) (RationalProgram.initial xs)).2.2 = true := by
  unfold cosRegisterFuel
  rw [rationalProgram_run_add]
  exact (cosRegisterCode_loop _ _ _ _ _ _ (cosRegisterCode_initial xs)).1

/-- Certified register implementation of the midpoint cosine routine. -/
-- @node: cosRegisterProgram
def cosRegisterProgram : BoundedRationalProgram where
  code := cosRegisterCode
  iterationBound := cosRegisterFuel
  public_bound := cosRegisterFuel_public
  halts := cosRegisterCode_halts

/-- The finite recurrence returns exactly the concrete engine's cosine interval. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_cos_register_certificate
lemma concreteEngine_cos_register_certificate (q : ℕ) (I : RatInterval) :
    concreteEngine.cosBox q I =
      let v := cosRegisterProgram.eval [q, I.lo, I.hi]; rationalBox v.1 v.2 := by
  have h := cosRegisterCode_loop _ _ _ _ _ _
    (cosRegisterCode_initial [(q : ℚ), I.lo, I.hi])
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast, zero_add] at h
  change paperCos q I = rationalBox
    ((cosRegisterCode.run (cosRegisterFuel [q, I.lo, I.hi])
      (RationalProgram.initial [q, I.lo, I.hi])).2.1 0)
    ((cosRegisterCode.run (cosRegisterFuel [q, I.lo, I.hi])
      (RationalProgram.initial [q, I.lo, I.hi])).2.1 1)
  unfold cosRegisterFuel
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast]
  rw [rationalProgram_run_add, h.2.1, h.2.2]
  rfl

end CausalSmith.Stat.LogoddsLowsmoothFrontier
