module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines

/-! # Finite register certificate for the prescribed Machin enclosure

A fixed loop advances the two alternating arctangent sums together. Its public
fuel is linear in the prescribed term count, including initialization and clipping.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Iteration can be divided into consecutive blocks of instructions. [the stated conclusion](goal) holds. -/
-- @node: rationalProgram_run_add
lemma rationalProgram_run_add (code : RationalProgram) (a b : ℕ) (s : RationalState) :
    code.run (a + b) s = code.run b (code.run a s) := by
  induction a generalizing s with
  | zero => simp [RationalProgram.run]
  | succ a ih => simpa [Nat.succ_add, RationalProgram.run] using ih (code.step s)

/-- The fixed Machin program uses the two term recurrences and clips its final endpoints. -/
-- @node: piRegisterCode
def piRegisterCode : RationalProgram :=
  [.constant 12 0, .floor 14 0, .max 14 14 12,
   .constant 8 1, .constant 9 2, .constant 10 (-1/25), .constant 11 (-1/57121),
   .constant 3 1, .constant 4 (1/5), .constant 5 (1/239),
   .constant 6 0, .constant 7 0, .constant 2 7, .add 2 14 2,
   .branchLe 2 12 24 15,
   .div 13 4 3, .add 6 6 13, .div 13 5 3, .add 7 7 13,
   .mul 4 4 10, .mul 5 5 11, .add 3 3 9, .sub 2 2 8, .jump 14,
   .constant 13 16, .mul 6 6 13, .constant 13 4, .mul 7 7 13, .sub 6 6 7,
   .constant 13 3, .add 14 14 13, .natPow 9 9 14, .div 8 8 9,
   .sub 0 6 8, .add 1 6 8, .constant 13 3, .max 0 13 0,
   .constant 13 4, .min 1 13 1, .halt]

/-- Loop-head register meanings after a specified number of arctangent terms. -/
-- @node: PiRegisterInvariant
structure PiRegisterInvariant (q j remaining : ℕ) (s : RationalState) : Prop where
  pc : s.1 = 14
  active : s.2.2 = false
  count : s.2.1 2 = remaining
  odd : s.2.1 3 = (2*j+1 : ℕ)
  term5 : s.2.1 4 = (-1 : ℚ)^j * (1/5 : ℚ)^(2*j+1)
  term239 : s.2.1 5 = (-1 : ℚ)^j * (1/239 : ℚ)^(2*j+1)
  sum5 : s.2.1 6 = arctanPolynomial j (1/5)
  sum239 : s.2.1 7 = arctanPolynomial j (1/239)
  one : s.2.1 8 = 1
  two : s.2.1 9 = 2
  ratio5 : s.2.1 10 = -1/25
  ratio239 : s.2.1 11 = -1/57121
  zero : s.2.1 12 = 0
  precision : s.2.1 14 = q

/-- Initialization clamps arbitrary rational precisions and prepares the prescribed count. [the stated conclusion](goal) holds. -/
-- @node: piRegisterCode_initial
lemma piRegisterCode_initial (xs : List ℚ) :
    PiRegisterInvariant (⌊xs[0]?.getD 0⌋ : ℤ).toNat 0
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat + 7)
      (piRegisterCode.run 14 (RationalProgram.initial xs)) := by
  have hmax : max (⌊xs[0]?.getD 0⌋ : ℤ) 0 =
      (((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℕ) : ℤ) := by omega
  have hq : max (↑(⌊xs[0]?.getD 0⌋ : ℤ) : ℚ) 0 =
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) := by exact_mod_cast hmax
  constructor <;> norm_num [piRegisterCode, RationalProgram.run, RationalProgram.step,
    RationalProgram.initial, Function.update_apply, arctanPolynomial, hq]

/-- One loop block adds precisely the next term of both finite sums. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:h). -/
-- @node: piRegisterCode_round
lemma piRegisterCode_round (q j N : ℕ) (s : RationalState)
    (h : PiRegisterInvariant q j (N + 1) s) :
    PiRegisterInvariant q (j+1) N (piRegisterCode.run 10 s) := by
  rcases h with ⟨hpc, ha, hc, ho, ht5, ht239, hs5, hs239,
    h1, h2, hr5, hr239, hz, hq⟩
  have hcpos : ¬ (s.2.1 2 ≤ s.2.1 12) := by
    rw [hc, hz]
    exact not_le.mpr (by positivity)
  have term (v : ℚ) :
      ((-1 : ℚ)^j*v^(2*j+1)) * (-v^2) = (-1 : ℚ)^(j+1)*v^(2*(j+1)+1) := by
    rw [show 2*(j+1)+1 = (2*j+1)+2 by omega, pow_add, pow_succ]
    ring
  generalize he : piRegisterCode.run 10 s = t
  norm_num [piRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hpc, ha, hcpos] at he
  subst t
  constructor <;>
    norm_num [Function.update_apply, hc, ho, ht5, ht239,
      hs5, hs239, h1, h2, hr5, hr239, hz, hq, arctanPolynomial,
      Finset.sum_range_succ, Nat.cast_add, Nat.cast_mul]
  · ring
  · convert term (1/5) using 1; norm_num
  · convert term (1/239) using 1; norm_num

/-- The exit block returns the literal clipped Machin endpoints and halts. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: piRegisterCode_exit
lemma piRegisterCode_exit (q j : ℕ) (s : RationalState)
    (h : PiRegisterInvariant q j 0 s) :
    let t := piRegisterCode.run 17 s
    t.2.2 = true ∧
    t.2.1 0 = max 3 (16*arctanPolynomial j (1/5) -
      4*arctanPolynomial j (1/239) - rationalError (q+3)) ∧
    t.2.1 1 = min 4 (16*arctanPolynomial j (1/5) -
      4*arctanPolynomial j (1/239) + rationalError (q+3)) := by
  rcases h with ⟨hpc, ha, hc, ho, ht5, ht239, hs5, hs239,
    h1, h2, hr5, hr239, hz, hq⟩
  have hnat : (3+(q : ℤ)).toNat = q+3 := by omega
  norm_num [piRegisterCode, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hpc, ha, hc, hs5, hs239, h1, h2, hz, hq,
    rationalError, ← Nat.cast_add, hnat]
  have hnat' : ((q : ℤ)+3).toNat = q+3 := by omega
  constructor <;> simp only [hnat'] <;> congr 1 <;> ring

/-- [Iterating the loop exhausts its counter and returns both completed sums.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: piRegisterCode_loop
lemma piRegisterCode_loop (q j N : ℕ) (s : RationalState)
    (h : PiRegisterInvariant q j N s) :
    let t := piRegisterCode.run (10*N+17) s
    t.2.2 = true ∧
    t.2.1 0 = max 3 (16*arctanPolynomial (j+N) (1/5) -
      4*arctanPolynomial (j+N) (1/239) - rationalError (q+3)) ∧
    t.2.1 1 = min 4 (16*arctanPolynomial (j+N) (1/5) -
      4*arctanPolynomial (j+N) (1/239) + rationalError (q+3)) := by
  induction N generalizing j s with
  | zero => simpa using piRegisterCode_exit q j s h
  | succ N ih =>
      rw [show 10*(N+1)+17 = 10+(10*N+17) by omega, rationalProgram_run_add]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (j+1) _ (piRegisterCode_round q j N s h)

/-- Public fuel for the fixed Machin program, on every rational input list. -/
-- @node: piRegisterFuel
def piRegisterFuel (xs : List ℚ) : ℕ :=
  14 + (10*((⌊xs[0]?.getD 0⌋ : ℤ).toNat+7)+17)

/-- The public fuel is computed by a fixed straight-line register program. [the stated conclusion](goal) holds. -/
-- @node: piRegisterFuel_public
lemma piRegisterFuel_public : PublicIterationBound piRegisterFuel := by
  refine ⟨[.constant 1 0, .floor 0 0, .max 0 0 1, .constant 1 7,
    .add 0 0 1, .constant 1 10, .mul 0 0 1, .constant 1 31, .add 0 0 1, .halt], ?_⟩
  intro xs
  have hmax : max (⌊xs[0]?.getD 0⌋ : ℤ) 0 =
      (((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℕ) : ℤ) := by omega
  have hq : max (↑(⌊xs[0]?.getD 0⌋ : ℤ) : ℚ) 0 =
      ((⌊xs[0]?.getD 0⌋ : ℤ).toNat : ℚ) := by exact_mod_cast hmax
  refine ⟨10, ?_, ?_⟩ <;>
    norm_num [RationalProgram.run, RationalProgram.step, RationalProgram.initial,
      Function.update_apply, piRegisterFuel, hq, Nat.cast_add, Nat.cast_mul]
  ring

/-- The fixed public fuel halts the Machin computation for every input list. [the stated conclusion](goal) holds. -/
-- @node: piRegisterCode_halts
lemma piRegisterCode_halts (xs : List ℚ) :
    (piRegisterCode.run (piRegisterFuel xs) (RationalProgram.initial xs)).2.2 = true := by
  unfold piRegisterFuel
  rw [rationalProgram_run_add]
  exact (piRegisterCode_loop _ _ _ _ (piRegisterCode_initial xs)).1

/-- Certified finite rational program for the Machin primitive. -/
-- @node: piRegisterProgram
def piRegisterProgram : BoundedRationalProgram where
  code := piRegisterCode
  iterationBound := piRegisterFuel
  public_bound := piRegisterFuel_public
  halts := piRegisterCode_halts

/-- The Machin primitive is exactly the interval returned by its finite register program. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_pi_register_certificate
lemma concreteEngine_pi_register_certificate (q : ℕ) :
    concreteEngine.piBox q =
      let v := piRegisterProgram.eval [q]; rationalBox v.1 v.2 := by
  have h := piRegisterCode_loop _ _ _ _ (piRegisterCode_initial [(q : ℚ)])
  simp only [List.getElem?_cons_zero, Option.getD_some, Int.floor_natCast,
    Int.toNat_natCast, zero_add] at h
  change paperPi q = rationalBox
    ((piRegisterCode.run (piRegisterFuel [q]) (RationalProgram.initial [q])).2.1 0)
    ((piRegisterCode.run (piRegisterFuel [q]) (RationalProgram.initial [q])).2.1 1)
  unfold piRegisterFuel
  simp only [List.getElem?_cons_zero, Option.getD_some, Int.floor_natCast, Int.toNat_natCast]
  rw [rationalProgram_run_add, h.2.1, h.2.2]
  rfl

end CausalSmith.Stat.LogoddsLowsmoothFrontier
