module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines

/-! # Finite register certificate for the prescribed square-root routine

The binary-loop invariant identifies its result with the integer-square-root
instruction. A fixed straight-line program computes both dyadic endpoints,
with a constant, independently certified public fuel bound.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A binary step preserves the integer square-root bracket.](goal) Under [the stated assumptions](hyp:l,hl,hu,hlu). -/
-- @node: integerSqrtStep_bracket
lemma integerSqrtStep_bracket (N l u : ℕ)
    (hl : l ^ 2 ≤ N) (hu : N < u ^ 2) (hlu : l < u) :
    let v := integerSqrtStep N (l,u)
    v.1 ^ 2 ≤ N ∧ N < v.2 ^ 2 ∧ v.1 < v.2 := by
  unfold integerSqrtStep
  split
  · exact ⟨hl, hu, hlu⟩
  · rename_i hwidth
    have hmid : l < (l + u) / 2 ∧ (l + u) / 2 < u := by omega
    dsimp only
    split
    · rename_i hsq
      exact ⟨hsq, hu, hmid.2⟩
    · rename_i hsq
      exact ⟨hl, Nat.lt_of_not_ge hsq, hmid.1⟩

/-- [A nonterminal binary step halves a power-of-two width budget.](goal) Under [the stated assumptions](hyp:l,hlu). Under [the stated assumptions](hyp:hw). -/
-- @node: integerSqrtStep_width
lemma integerSqrtStep_width (N l u q : ℕ) (hlu : l < u)
    (hw : u - l ≤ 2 ^ (q + 1)) :
    (integerSqrtStep N (l,u)).2 - (integerSqrtStep N (l,u)).1 ≤ 2 ^ q := by
  have hp : 0 < 2 ^ q := by positivity
  rw [pow_succ] at hw
  unfold integerSqrtStep
  split
  · rename_i h
    simp only [h]
    omega
  · dsimp only
    split <;> dsimp <;> omega

/-- [The structurally recursive fixed-count loop preserves the bracket and exhausts its width.](goal) Under [the stated assumptions](hyp:l,hl,hu,hlu,hw). -/
-- @node: integerSqrtLoop_spec
lemma integerSqrtLoop_spec (N q l u : ℕ)
    (hl : l ^ 2 ≤ N) (hu : N < u ^ 2) (hlu : l < u)
    (hw : u - l ≤ 2 ^ q) :
    let v := integerSqrtLoop N q (l,u)
    v.1 ^ 2 ≤ N ∧ N < v.2 ^ 2 ∧ v.2 = v.1 + 1 := by
  induction q generalizing l u with
  | zero =>
      simp only [integerSqrtLoop, pow_zero] at *
      exact ⟨hl, hu, by omega⟩
  | succ q ih =>
      obtain ⟨hl', hu', hlu'⟩ := integerSqrtStep_bracket N l u hl hu hlu
      exact ih _ _ hl' hu' hlu' (integerSqrtStep_width N l u q hlu hw)

/-- [The prescribed number of binary steps returns the unique integer square-root bracket. [the stated conclusion](goal) holds. -/
-- @node: paperIntegerSqrt_spec
lemma paperIntegerSqrt_spec (N : ℕ) :
    paperIntegerSqrt N ^ 2 ≤ N ∧ N < (paperIntegerSqrt N + 1) ^ 2 := by
  have hw : (N + 1) - 0 ≤ 2 ^ (Nat.clog 2 (N + 1) + 1) := by
    have h := Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (N + 1)
    rw [pow_succ]
    omega
  obtain ⟨hl, hu, heq⟩ := integerSqrtLoop_spec N (Nat.clog 2 (N + 1) + 1) 0 (N + 1)
    (by simp) (by nlinarith) (by omega) hw
  refine ⟨hl, ?_⟩
  simpa only [paperIntegerSqrt, heq] using hu

/-- The paper's binary recurrence agrees with the integer-square-root instruction. [the stated conclusion](goal) holds. -/
-- @node: paperIntegerSqrt_eq_sqrt
lemma paperIntegerSqrt_eq_sqrt (N : ℕ) : paperIntegerSqrt N = Nat.sqrt N := by
  exact Nat.eq_sqrt'.mpr (paperIntegerSqrt_spec N)

/-- Straight-line dyadic square-root endpoint program; inputs are precision, lower, upper. -/
-- @node: sqrtRegisterCode
def sqrtRegisterCode : RationalProgram :=
  [.constant 3 3, .add 3 0 3, .constant 4 2, .natPow 4 4 3,
   .mul 5 4 4, .mul 6 5 1, .integerSqrt 6 6, .div 0 6 4,
   .mul 7 5 2, .integerSqrt 7 7, .constant 8 1, .add 7 7 8,
   .div 1 7 4, .halt]

/-- Every rational input halts after the fixed instruction count. [the stated conclusion](goal) holds. -/
-- @node: sqrtRegisterCode_halts
lemma sqrtRegisterCode_halts (xs : List ℚ) :
    (sqrtRegisterCode.run 14 (RationalProgram.initial xs)).2.2 = true := by
  norm_num [sqrtRegisterCode, RationalProgram.run, RationalProgram.step,
    RationalProgram.initial, Function.update_apply]

/-- The public fuel bound is itself computed by a two-step rational program. [the stated conclusion](goal) holds. -/
-- @node: sqrtRegisterBound_public
lemma sqrtRegisterBound_public : PublicIterationBound (fun _ => 14) := by
  refine ⟨[.constant 0 14, .halt], ?_⟩
  intro xs
  refine ⟨2, ?_, ?_⟩ <;>
    norm_num [RationalProgram.run, RationalProgram.step, RationalProgram.initial,
      Function.update_apply]

/-- The certified square-root register program. -/
-- @node: sqrtRegisterProgram
def sqrtRegisterProgram : BoundedRationalProgram where
  code := sqrtRegisterCode
  iterationBound := fun _ => 14
  public_bound := sqrtRegisterBound_public
  halts := sqrtRegisterCode_halts

/-- Executing the program on valid precision inputs returns the two raw dyadic endpoints. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: sqrtRegisterProgram_eval
lemma sqrtRegisterProgram_eval (q : ℕ) (l u : ℚ) :
    sqrtRegisterProgram.eval [q, l, u] =
      (((Nat.sqrt (⌊(2 : ℚ) ^ (2 * (q + 3)) * l⌋ : ℤ).toNat : ℚ) / 2 ^ (q + 3)),
       (((Nat.sqrt (⌊(2 : ℚ) ^ (2 * (q + 3)) * u⌋ : ℤ).toNat : ℚ) + 1) / 2 ^ (q + 3))) := by
  norm_num [BoundedRationalProgram.eval, sqrtRegisterProgram, sqrtRegisterCode,
    RationalProgram.run, RationalProgram.step, RationalProgram.initial,
    Function.update_apply, ← Nat.cast_add, pow_mul, mul_comm 2]
  have hp : ((q : ℤ) + 3).toNat = q + 3 := by omega
  simp [hp, pow_two]

/-- The scalar dyadic bracket endpoints are in their literal monotone order for all inputs. [the stated conclusion](goal) holds. -/
-- @node: paperSqrtScalar_endpoints
lemma paperSqrtScalar_endpoints (q : ℕ) (z : ℚ) :
    (paperSqrtScalar q z).lo =
      (Nat.sqrt (⌊(2 : ℚ) ^ (2 * (q + 3)) * z⌋ : ℤ).toNat : ℚ) / 2 ^ (q + 3) ∧
    (paperSqrtScalar q z).hi =
      ((Nat.sqrt (⌊(2 : ℚ) ^ (2 * (q + 3)) * z⌋ : ℤ).toNat : ℚ) + 1) / 2 ^ (q + 3) := by
  have horder (a : ℕ) : (a : ℚ) / 2 ^ (q + 3) ≤ ((a : ℚ) + 1) / 2 ^ (q + 3) := by
    apply div_le_div_of_nonneg_right <;> first | positivity | linarith
  simp [paperSqrtScalar, paperIntegerSqrt_eq_sqrt, rationalBox,
    min_eq_left (horder _), max_eq_right (horder _)]

/-- The concrete square-root map has a bounded finite rational register implementation. [the stated conclusion](goal) holds. -/
-- @node: concreteEngine_sqrt_register_certificate
lemma concreteEngine_sqrt_register_certificate (q : ℕ) (I : RatInterval) :
    concreteEngine.sqrtBox q I =
      let v := sqrtRegisterProgram.eval [q, I.lo, I.hi]
      rationalBox v.1 v.2 := by
  rw [sqrtRegisterProgram_eval]
  change rationalBox (paperSqrtScalar q I.lo).lo (paperSqrtScalar q I.hi).hi = _
  rw [(paperSqrtScalar_endpoints q I.lo).1, (paperSqrtScalar_endpoints q I.hi).2]

/-- Assemble the remaining five certificates with the independently proved square-root program. the stated conclusion holds. Under the stated assumptions. [The stated hypotheses](hyp:hpi,hexp,hcos,hlog,hpower) hold, and [the stated conclusion follows](goal). -/
-- @node: concreteEngine_registers_of_other_primitives
lemma concreteEngine_registers_of_other_primitives
    (pi exp cos log power : BoundedRationalProgram)
    (hpi : ∀ q, concreteEngine.piBox q =
      let v := pi.eval [q]; rationalBox v.1 v.2)
    (hexp : ∀ q I, concreteEngine.expBox q I =
      let v := exp.eval [q, I.lo, I.hi]; rationalBox v.1 v.2)
    (hcos : ∀ q I, concreteEngine.cosBox q I =
      let v := cos.eval [q, I.lo, I.hi]; rationalBox v.1 v.2)
    (hlog : ∀ q I, concreteEngine.logBox q I =
      let v := log.eval [q, I.lo, I.hi]; rationalBox v.1 v.2)
    (hpower : ∀ q b I, concreteEngine.powBox q b I =
      let v := power.eval [q, b, I.lo, I.hi]; rationalBox v.1 v.2) :
    RationalRecurrences concreteEngine := by
  refine ⟨(fun kind => match kind with
    | .pi => pi | .exp => exp | .cos => cos | .log => log
    | .sqrt => sqrtRegisterProgram | .power => power),
    hpi, hexp, hcos, hlog, concreteEngine_sqrt_register_certificate, hpower⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
