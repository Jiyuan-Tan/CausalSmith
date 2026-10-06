module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ExpProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerLogProgram

/-! # Register certificate for the final power bracket

The last stage takes the internal precision, integer base, and exponential
endpoints. It widens by the prescribed rational error, clips to the exact cubic
range, and implements the base-one exception. Its fixed bound is itself a
finite rational program. The staged scalar computation uses the certified
logarithm and exponential programs. Fusing these stages into a single bounded
register program remains a separate obligation.
-/
@[expose] public section
set_option maxRecDepth 4096
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The final power bracket, applied to already computed exponential endpoints. -/
-- @node: powerClipBox
def powerClipBox (p b : ℕ) (lo hi : ℚ) : RatInterval :=
  if b = 1 then RatInterval.point 1 else
    let e := 96 * (max 2 b : ℚ)^3 * rationalError p
    rationalBox (max (1/(b : ℚ)^3) (lo-e)) (min ((b : ℚ)^3) (hi+e))

/-- The literal scalar power is its exponential bracket followed by final clipping. [the stated conclusion](goal) holds. -/
-- @node: paperPowerScalar_eq_powerClipBox
lemma paperPowerScalar_eq_powerClipBox (q b : ℕ) (v : ℚ) :
    let p := powerRegisterPrecision q b
    let L := paperLogScalar p b
    let J := paperExpScalar p (v*((L.lo+L.hi)/2))
    paperPowerScalar q b v = powerClipBox p b J.lo J.hi := by
  dsimp only
  by_cases hb : b = 1
  · simp [paperPowerScalar, powerClipBox, hb]
  · simp [paperPowerScalar, powerClipBox, hb, powerRegisterPrecision, Nat.cast_max]

/-- Registers zero and one initially hold precision and base; two and three
hold the exponential bracket. The output is sorted by the external rational box. -/
-- @node: powerClipCode
def powerClipCode : RationalProgram :=
  [.constant 12 0, .floor 14 0, .max 14 14 12,
   .floor 21 1, .max 21 21 12, .constant 8 1,
   .branchLe 21 8 7 11, .branchLe 8 21 8 11,
   .constant 0 1, .constant 1 1, .halt,
   .constant 9 2, .max 22 9 21, .constant 13 3,
   .natPow 22 22 13, .constant 13 96, .mul 22 22 13,
   .natPow 9 9 14, .div 22 22 9, .constant 13 3,
   .natPow 23 21 13, .div 24 8 23,
   .sub 2 2 22, .add 3 3 22, .max 0 24 2, .min 1 23 3, .halt]

set_option maxHeartbeats 1000000 in
-- Expanding both finite branches requires additional simplifier resources.
/-- On any active starting frame, the clipping stage computes precisely the
paper's rational formula; natural-number inputs are interpreted by floor-clamping. [the documented result](goal) Under [the stated assumptions](hyp:ha). Under [the stated assumptions](hyp:hp). -/
-- @node: powerClipCode_result
lemma powerClipCode_result (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let b := (⌊s.2.1 1⌋ : ℤ).toNat
    let e := 96 * (max 2 b : ℚ)^3 * rationalError p
    let t := powerClipCode.run 27 s
    t.2.2 = true ∧
      t.2.1 0 = (if b = 1 then 1 else max (1/(b : ℚ)^3) (s.2.1 2-e)) ∧
      t.2.1 1 = (if b = 1 then 1 else min ((b : ℚ)^3) (s.2.1 3+e)) := by
  dsimp only
  let b := (⌊s.2.1 1⌋ : ℤ).toNat
  let p := (⌊s.2.1 0⌋ : ℤ).toNat
  change let t := powerClipCode.run 27 s
         t.2.2 = true ∧
           t.2.1 0 = (if b = 1 then 1 else max (1/(b : ℚ)^3)
             (s.2.1 2-96*(max 2 b : ℚ)^3*rationalError p)) ∧
           t.2.1 1 = (if b = 1 then 1 else min ((b : ℚ)^3)
             (s.2.1 3+96*(max 2 b : ℚ)^3*rationalError p))
  have hpre :
      let t := powerClipCode.run 6 s
      t.1 = 6 ∧ t.2.2 = false ∧ t.2.1 14 = p ∧ t.2.1 21 = b ∧
      t.2.1 8 = 1 ∧ t.2.1 2 = s.2.1 2 ∧ t.2.1 3 = s.2.1 3 := by
    norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, powerRegister_clamp_cast, p, b]
  rw [show 27 = 6+21 by rfl, rationalProgram_run_add]
  generalize he : powerClipCode.run 6 s = t at hpre ⊢
  dsimp only at hpre
  obtain ⟨htp, hta, hprecision, hbase, hone, hlo, hhi⟩ := hpre
  by_cases hb : b = 1
  · norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, htp, hta, hbase, hone, hb]
  · by_cases hz : b = 0
    · generalize hu : powerClipCode.run 21 t = u
      norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
        Function.update_apply, htp, hta, hbase, hone, hprecision, hz] at hu
      subst u
      norm_num [Function.update_apply, hlo, hhi, rationalError, hz, p,
        (show (3 : ℤ).toNat = 3 by rfl), div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    · have hgt : ¬ (b : ℚ) ≤ 1 := by exact_mod_cast (show ¬ b ≤ 1 by omega)
      generalize hu : powerClipCode.run 21 t = u
      norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
        Function.update_apply, htp, hta, hbase, hone, hprecision, hgt] at hu
      subst u
      norm_num [Function.update_apply, hlo, hhi, rationalError, hb, p,
        (show (3 : ℤ).toNat = 3 by rfl), div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

/-- [The fixed instruction bound is computed without inspecting any input. [the stated conclusion](goal) holds. -/
-- @node: powerClipFuel_public
lemma powerClipFuel_public : PublicIterationBound (fun _ => 27) := by
  refine ⟨[.constant 0 27, .halt], ?_⟩
  intro xs
  refine ⟨2, ?_, ?_⟩ <;>
    norm_num [RationalProgram.run, RationalProgram.step, RationalProgram.initial,
      Function.update_apply]

/-- Certified total finite register program for the final power bracket. -/
-- @node: powerClipProgram
def powerClipProgram : BoundedRationalProgram where
  code := powerClipCode
  iterationBound := fun _ => 27
  public_bound := powerClipFuel_public
  halts := fun xs => (powerClipCode_result (RationalProgram.initial xs) rfl rfl).1

/-- The certified program returns the exact clipped scalar formula. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerClipProgram_eval
lemma powerClipProgram_eval (p b : ℕ) (lo hi : ℚ) :
    let v := powerClipProgram.eval [p,b,lo,hi]
    rationalBox v.1 v.2 = powerClipBox p b lo hi := by
  have h := powerClipCode_result (RationalProgram.initial [(p : ℚ),b,lo,hi]) rfl rfl
  simp only [RationalProgram.initial, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Int.floor_natCast, Int.toNat_natCast] at h
  dsimp only [BoundedRationalProgram.eval, powerClipProgram, RationalProgram.initial]
  rw [h.2.1, h.2.2]
  by_cases hb : b = 1
  · simp [powerClipBox, hb, rationalBox, RatInterval.point]
  · simp [powerClipBox, hb]

/-- Given the two exponential endpoints, the register stage returns the literal
power scalar, including its exceptional constant base. [the documented result](goal) -/
-- @node: paperPowerScalar_clip_register_certificate
lemma paperPowerScalar_clip_register_certificate (q b : ℕ) (v : ℚ) :
    let p := powerRegisterPrecision q b
    let L := paperLogScalar p b
    let J := paperExpScalar p (v*((L.lo+L.hi)/2))
    let endpoints := powerClipProgram.eval [p,b,J.lo,J.hi]
    paperPowerScalar q b v = rationalBox endpoints.1 endpoints.2 := by
  dsimp only
  rw [powerClipProgram_eval]
  exact paperPowerScalar_eq_powerClipBox q b v

/-- A point-input exponential call returns both endpoints of the scalar bracket. [the stated conclusion](goal) holds. -/
-- @node: expRegisterProgram_point_eval
lemma expRegisterProgram_point_eval (p : ℕ) (z : ℚ) :
    expRegisterProgram.eval [p,z,z] = ((paperExpScalar p z).lo, (paperExpScalar p z).hi) := by
  have h := expRegisterCode_result [(p : ℚ),z,z]
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] at h
  dsimp only [BoundedRationalProgram.eval, expRegisterProgram]
  rw [h.2.1, h.2.2]

/-- Execute the three certified register stages for one rational exponent.
The logarithm stage supplies both the precision and its midpoint; the exponential
stage is called on their product with the exponent, then the final stage clips. -/
-- @node: powerScalarRegisterEval
def powerScalarRegisterEval (q b : ℕ) (v : ℚ) : RatInterval :=
  let prepared := powerLogProgram.eval [q,b,v,v]
  let exponential := expRegisterProgram.eval [prepared.1,v*prepared.2,v*prepared.2]
  let clipped := powerClipProgram.eval [prepared.1,b,exponential.1,exponential.2]
  rationalBox clipped.1 clipped.2

/-- The staged finite register evaluation agrees with the full scalar power
formula, on all natural precisions and bases and all rational exponents. [the documented result](goal) -/
-- @node: powerScalarRegisterEval_spec
lemma powerScalarRegisterEval_spec (q b : ℕ) (v : ℚ) :
    powerScalarRegisterEval q b v = paperPowerScalar q b v := by
  simp only [powerScalarRegisterEval, powerLogProgram_eval]
  rw [expRegisterProgram_point_eval, powerClipProgram_eval]
  exact (paperPowerScalar_eq_powerClipBox q b v).symm

/-- Two staged scalar calls supply the monotone endpoint extension. This is
a composition of bounded programs, rather than a certificate for a fused code list. -/
-- @node: powerEndpointRegisterEval
def powerEndpointRegisterEval (q b : ℕ) (I : RatInterval) : RatInterval :=
  rationalBox (powerScalarRegisterEval q b I.lo).lo (powerScalarRegisterEval q b I.hi).hi

/-- Every endpoint of the concrete power engine is computed by the certified
stages. The remaining recurrence obligation is to fuse these calls and their fuel. [the documented result](goal) -/
-- @node: concreteEngine_power_staged_certificate
lemma concreteEngine_power_staged_certificate (q b : ℕ) (I : RatInterval) :
    concreteEngine.powBox q b I = powerEndpointRegisterEval q b I := by
  simp only [concreteEngine, endpointExtension, powerEndpointRegisterEval,
    powerScalarRegisterEval_spec]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
