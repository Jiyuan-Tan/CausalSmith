module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerExpFrames

/-! # Control-flow certificates for fusion of the power recurrence

The exponential stage reaches an active final frame before its halt instruction.
Replacing that halt with a relocated jump joins the prescribed clipping recurrence
into one bounded register program. Its public fuel is computed by a separate finite
rational recurrence. The logarithm and two endpoint calls remain to be joined.
-/
@[expose] public section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [A halted frame is fixed by any number of further steps.](goal) Under [the stated assumptions](hyp:ha). -/
-- @node: rationalProgram_run_halted
lemma rationalProgram_run_halted (code : RationalProgram) (n : ℕ)
    (s : RationalState) (ha : s.2.2 = true) : code.run n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [RationalProgram.run, RationalProgram.step, ha] using ih

/-- [An active final frame certifies that the initial frame was active. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ha). -/
-- @node: rationalProgram_run_active
lemma rationalProgram_run_active (code : RationalProgram) (n : ℕ)
    (s : RationalState) (ha : (code.run n s).2.2 = false) : s.2.2 = false := by
  cases hs : s.2.2
  · rfl
  · rw [rationalProgram_run_halted code n s hs, hs] at ha
    contradiction

/-- Replace an explicit halt with a jump into an appended continuation. -/
-- @node: rationalInstruction_continue
def rationalInstruction_continue (target : ℕ) : RationalInstruction → RationalInstruction
  | .halt => .jump target
  | op => op

/-- Join two literal code lists, relocating all branches of the continuation. -/
-- @node: rationalProgram_continue
def rationalProgram_continue (code tail : RationalProgram) : RationalProgram :=
  code.map (rationalInstruction_continue code.length) ++
    tail.map (rationalInstruction_relocate code.length)

/-- Before the original computation halts, joining a continuation changes no step. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ha). -/
-- @node: rationalProgram_continue_step
lemma rationalProgram_continue_step (code tail : RationalProgram) (s : RationalState)
    (ha : (code.step s).2.2 = false) :
    (rationalProgram_continue code tail).step s = code.step s := by
  have hs : s.2.2 = false :=
    rationalProgram_run_active code 1 s (by simpa [RationalProgram.run] using ha)
  cases he : code[s.1]? with
  | none => simp [RationalProgram.step, hs, he] at ha
  | some op =>
    have hi : s.1 < code.length := List.getElem?_eq_some_iff.mp he |>.1
    have hlookup : (rationalProgram_continue code tail)[s.1]? =
        some (rationalInstruction_continue code.length op) := by
      simp only [rationalProgram_continue, List.getElem?_append, List.length_map,
        if_pos hi, List.getElem?_map, he, Option.map_some]
    cases op <;>
      simp_all [RationalProgram.step, rationalInstruction_continue]

/-- Any active finite prefix of the original run is identical in the joined program. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:ha). -/
-- @node: rationalProgram_continue_run
lemma rationalProgram_continue_run (code tail : RationalProgram) (n : ℕ)
    (s : RationalState) (ha : (code.run n s).2.2 = false) :
    (rationalProgram_continue code tail).run n s = code.run n s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    change (code.run n (code.step s)).2.2 = false at ha
    have hstep := rationalProgram_run_active code n (code.step s) ha
    rw [RationalProgram.run, rationalProgram_continue_step code tail s hstep,
      ih (code.step s) ha, RationalProgram.run]

/-- The appended block uses the same register frame as the unrelocated continuation. [the stated conclusion](goal) holds. -/
-- @node: rationalProgram_continue_tail
lemma rationalProgram_continue_tail (code tail : RationalProgram) (n : ℕ)
    (s : RationalState) :
    (rationalProgram_continue code tail).run n (rationalState_relocate code.length s) =
      rationalState_relocate code.length (tail.run n s) := by
  simpa [rationalProgram_continue] using
    rationalProgram_relocate_run (code.map (rationalInstruction_continue code.length)) tail n s

/-- Both endpoint loops reach their active final frame without zeroing spare registers. Under the stated assumptions. [The stated hypotheses](hyp:hp₀,ha₀) hold, and [the stated conclusion follows](goal). -/
-- @node: expRegisterCode_before_halt
lemma expRegisterCode_before_halt (s₀ : RationalState) (hp₀ : s₀.1 = 0)
    (ha₀ : s₀.2.2 = false) :
    let q := (⌊s₀.2.1 0⌋ : ℤ).toNat
    let lo := (paperExpScalar q (s₀.2.1 1)).lo
    let hi := (paperExpScalar q (s₀.2.1 2)).hi
    let t := expRegisterCode.run ((expRegisterFuel [s₀.2.1 0,s₀.2.1 1,s₀.2.1 2]-1)) (s₀)
    t.1 = 89 ∧ t.2.2 = false ∧ t.2.1 0 = lo ∧ t.2.1 1 = hi := by
  let q := (⌊s₀.2.1 0⌋ : ℤ).toNat
  let z := s₀.2.1 1
  let w := s₀.2.1 2
  let N := 2*seriesCount q z
  let M := 2*seriesCount q w
  have h := expRegisterCode_loop false q 0 N z _ 0 w _ (expRegisterCode_start_frame s₀ hp₀ ha₀)
  simp only [expRegisterFuel, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  have hf : 78+7*(N+M)-1 = 23+(7*N+15)+(3+20)+(7*M+15)+1 := by omega
  rw [hf, rationalProgram_run_add _ (23+(7*N+15)+(3+20)+(7*M+15)) 1,
    rationalProgram_run_add _ (23+(7*N+15)+(3+20)) (7*M+15),
    rationalProgram_run_add _ (23+(7*N+15)) (3+20),
    rationalProgram_run_add _ 23 (7*N+15)]
  generalize hs : expRegisterCode.run (7*N+15)
    (expRegisterCode.run 23 (s₀)) = s at h ⊢
  simp only [Bool.false_eq_true, ↓reduceIte, zero_add] at h
  rcases h with ⟨hp, ha, hlo, hhi, hq, hl, hw⟩
  have hp' : (expRegisterCode.run 3 s).1 = 47 := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have ha' : (expRegisterCode.run 3 s).2.2 = false := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp, ha]
  have hinit := expRegisterCode_initial true (expRegisterCode.run 3 s) hp' ha'
  have h0 : (expRegisterCode.run 3 s).2.1 0 = s₀.2.1 0 := by
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



set_option maxHeartbeats 1000000 in
/-- [The relocated exponential computation certifies the left power argument while
retaining the internal precision, base, right exponent, and logarithm midpoint. [the documented result](goal) Under [the stated assumptions](hyp:ha). Under [the stated assumptions](hyp:hp). -/
-- @node: powerExpCode_before_halt
lemma powerExpCode_before_halt (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let J := paperExpScalar p (s.2.1 3*s.2.1 1)
    let t := powerExpCode.run (powerExpFrameFuel s-1) s
    t.1 = 95 ∧ t.2.2 = false ∧ t.2.1 0 = J.lo ∧ t.2.1 1 = J.hi ∧
    t.2.1 24 = s.2.1 0 ∧ t.2.1 25 = s.2.1 2 ∧
    t.2.1 26 = s.2.1 4 ∧ t.2.1 27 = s.2.1 1 := by
  have hprep := powerExpCode_prepare s hp ha
  dsimp only [powerExpFrameFuel]
  rw [show 6 + expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1 =
      6+(expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) by
      simp only [expRegisterFuel]; omega, rationalProgram_run_add]
  generalize he : powerExpCode.run 6 s = t at hprep ⊢
  dsimp only at hprep
  obtain ⟨htp, hta, h0, h1, h2, h24, h25, h26, h27⟩ := hprep
  let u : RationalState := (0,t.2.1,false)
  have ht : t = rationalState_relocate powerExpPrelude.length u := by
    apply Prod.ext
    · simpa [rationalState_relocate, powerExpPrelude, u] using htp
    · apply Prod.ext
      · rfl
      · exact hta
  have hout := expRegisterCode_before_halt u rfl rfl
  have hs24 := expRegisterCode_spare_register 24 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) u
  have hs25 := expRegisterCode_spare_register 25 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) u
  have hs26 := expRegisterCode_spare_register 26 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) u
  have hs27 := expRegisterCode_spare_register 27 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) u
  dsimp only [u] at hout hs24 hs25 hs26 hs27
  simp only [h0,h1,h2] at hout
  have hrun := rationalProgram_relocate_run powerExpPrelude expRegisterCode
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]-1) u
  change powerExpCode.run _ (rationalState_relocate powerExpPrelude.length u) = _ at hrun
  rw [← ht] at hrun
  rw [hrun]
  dsimp only [rationalState_relocate]
  dsimp only [u]
  exact ⟨by simpa [powerExpPrelude, hout.1], hout.2.1,hout.2.2.1,hout.2.2.2,hs24.trans h24,hs25.trans h25,
    hs26.trans h26,hs27.trans h27⟩


/-- [Move the exponential bracket and saved power parameters into the clipping frame. -/
-- @node: powerClipPrelude
def powerClipPrelude : RationalProgram :=
  [.copy 2 0, .copy 3 1, .copy 0 24, .copy 1 25]

/-- The clipping continuation with all branch addresses relocated past the bridge. -/
-- @node: powerClipTail
def powerClipTail : RationalProgram :=
  powerClipPrelude ++ powerClipCode.map (rationalInstruction_relocate powerClipPrelude.length)

/-- The bridge preserves the two exponential endpoints while restoring precision and base. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerClipTail_prepare
lemma powerClipTail_prepare (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let t := powerClipTail.run 4 s
    t.1 = 4 ∧ t.2.2 = false ∧ t.2.1 0 = s.2.1 24 ∧
      t.2.1 1 = s.2.1 25 ∧ t.2.1 2 = s.2.1 0 ∧ t.2.1 3 = s.2.1 1 := by
  norm_num [powerClipTail, powerClipPrelude, RationalProgram.run, RationalProgram.step,
    hp, ha, Function.update_apply]

/-- [The appended clipping tail halts and returns the exact raw clipping endpoints.](goal) Under [the stated assumptions](hyp:hp,ha). -/
-- @node: powerClipTail_result
lemma powerClipTail_result (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let p := (⌊s.2.1 24⌋ : ℤ).toNat
    let b := (⌊s.2.1 25⌋ : ℤ).toNat
    let e := 96 * (max 2 b : ℚ)^3 * rationalError p
    let t := powerClipTail.run 31 s
    t.2.2 = true ∧
      t.2.1 0 = (if b = 1 then 1 else max (1/(b : ℚ)^3) (s.2.1 0-e)) ∧
      t.2.1 1 = (if b = 1 then 1 else min ((b : ℚ)^3) (s.2.1 1+e)) := by
  have hprep := powerClipTail_prepare s hp ha
  rw [show 31 = 4+27 by rfl, rationalProgram_run_add]
  generalize he : powerClipTail.run 4 s = t at hprep ⊢
  dsimp only at hprep
  obtain ⟨htp, hta, h0, h1, h2, h3⟩ := hprep
  let u : RationalState := (0,t.2.1,false)
  have ht : t = rationalState_relocate powerClipPrelude.length u := by
    apply Prod.ext
    · simpa [rationalState_relocate, powerClipPrelude, u] using htp
    · exact Prod.ext rfl hta
  have h := powerClipCode_result u rfl rfl
  dsimp only [u] at h
  simp only [h0,h1,h2,h3] at h
  rw [ht]
  rw [show powerClipTail = powerClipPrelude ++ powerClipCode.map
    (rationalInstruction_relocate powerClipPrelude.length) by rfl,
    rationalProgram_relocate_run]
  dsimp only [rationalState_relocate]
  generalize hv : powerClipCode.run 27 u = v at h ⊢
  exact h

/-- [A single literal register program performs the exponential and clipping stages. -/
-- @node: powerExpClipCode
def powerExpClipCode : RationalProgram := rationalProgram_continue powerExpCode powerClipTail

/-- Replace the last exponential halt by the actual jump into the clipping tail. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerExpClipCode_connect
lemma powerExpClipCode_connect (s : RationalState) (hp : s.1 = 95)
    (ha : s.2.2 = false) :
    powerExpClipCode.step s = rationalState_relocate powerExpCode.length (0,s.2.1,false) := by
  have hlen : powerExpCode.length = 96 := by rfl
  have hlookup : powerExpCode[95]? = some .halt := by rfl
  simp only [powerExpClipCode, rationalProgram_continue, RationalProgram.step,
    ha, Bool.false_eq_true, ↓reduceIte, hp, List.getElem?_append, List.length_map,
    hlen, show 95 < 96 by omega, ↓reduceIte, List.getElem?_map, hlookup,
    Option.map_some, rationalInstruction_continue, rationalState_relocate, Nat.add_zero]

/-- [Exact instruction bound for the joined continuation. -/
-- @node: powerExpClipFuel
def powerExpClipFuel (s : RationalState) : ℕ := powerExpFrameFuel s+31

/-- The fused code computes the prescribed power bracket from a logarithm frame. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerExpClipCode_result
lemma powerExpClipCode_result (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let b := (⌊s.2.1 2⌋ : ℤ).toNat
    let J := paperExpScalar p (s.2.1 3*s.2.1 1)
    let t := powerExpClipCode.run (powerExpClipFuel s) s
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) = powerClipBox p b J.lo J.hi := by
  have h := powerExpCode_before_halt s hp ha
  have hf : powerExpClipFuel s = (powerExpFrameFuel s-1)+1+31 := by
    simp only [powerExpClipFuel, powerExpFrameFuel, expRegisterFuel]; omega
  rw [hf, rationalProgram_run_add, rationalProgram_run_add]
  dsimp only at h
  have hrun := rationalProgram_continue_run powerExpCode powerClipTail
    (powerExpFrameFuel s-1) s h.2.1
  change powerExpClipCode.run _ s = _ at hrun
  rw [hrun]
  generalize he : powerExpCode.run (powerExpFrameFuel s-1) s = t at h ⊢
  obtain ⟨htp, hta, hlo, hhi, h24, h25, _⟩ := h
  rw [show powerExpClipCode.run 1 t = powerExpClipCode.step t by rfl,
    powerExpClipCode_connect t htp hta]
  rw [show powerExpClipCode = rationalProgram_continue powerExpCode powerClipTail by rfl,
    rationalProgram_continue_tail]
  have hout := powerClipTail_result (0,t.2.1,false) rfl rfl
  dsimp only at hout
  simp only [h24,h25,hlo,hhi] at hout
  dsimp only [rationalState_relocate]
  generalize hv : powerClipTail.run 31 (0,t.2.1,false) = v at hout ⊢
  refine ⟨hout.1, ?_⟩
  rw [hout.2.1,hout.2.2]
  by_cases hb : (⌊s.2.1 2⌋ : ℤ).toNat = 1
  · simp [powerClipBox, hb, rationalBox, RatInterval.point]
  · simp [powerClipBox, hb]


/-- [A straight-line recurrence computes the continuation's exact step bound. -/
-- @node: powerExpClipFuelCode
def powerExpClipFuelCode : RationalProgram :=
  [.mul 1 3 1, .copy 2 1] ++
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
   .constant 13 115, .add 0 0 13, .halt]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The continuation fuel is a total public rational computation on its input frame. [the stated conclusion](goal) holds. -/
-- @node: powerExpClipFuel_public
lemma powerExpClipFuel_public :
    PublicIterationBound (fun xs => powerExpClipFuel (RationalProgram.initial xs)) := by
  refine ⟨powerExpClipFuelCode, ?_⟩
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
  refine ⟨51, ?_, ?_⟩
  · norm_num [powerExpClipFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]
  · norm_num [powerExpClipFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply, powerExpClipFuel, powerExpFrameFuel, expRegisterFuel, seriesCount,
      Nat.cast_add, Nat.cast_mul, Nat.cast_max, Nat.cast_pow, hq, habs, hB]
    simp only [← abs_mul, hB]
    ring

/-- Certified single register program for the exponential-to-clipping continuation. -/
-- @node: powerExpClipProgram
def powerExpClipProgram : BoundedRationalProgram where
  code := powerExpClipCode
  iterationBound := fun xs => powerExpClipFuel (RationalProgram.initial xs)
  public_bound := powerExpClipFuel_public
  halts := fun xs => (powerExpClipCode_result (RationalProgram.initial xs) rfl rfl).1

/-- The fused continuation agrees with the literal scalar formula on prepared power data. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerExpClipProgram_eval
lemma powerExpClipProgram_eval (p b : ℕ) (mid lo hi : ℚ) :
    let v := powerExpClipProgram.eval [p,mid,b,lo,hi]
    rationalBox v.1 v.2 = powerClipBox p b
      (paperExpScalar p (lo*mid)).lo (paperExpScalar p (lo*mid)).hi := by
  have h := powerExpClipCode_result (RationalProgram.initial [(p : ℚ),mid,b,lo,hi]) rfl rfl
  dsimp only [BoundedRationalProgram.eval, powerExpClipProgram]
  generalize ht : powerExpClipCode.run
    (powerExpClipFuel (RationalProgram.initial [(p : ℚ),mid,b,lo,hi]))
    (RationalProgram.initial [(p : ℚ),mid,b,lo,hi]) = t at h ⊢
  simp only [RationalProgram.initial, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Int.floor_natCast, Int.toNat_natCast] at h
  exact h.2

/-- The two-stage logarithm/fused-continuation computation is the prescribed scalar power. [the stated conclusion](goal) holds. -/
-- @node: powerScalarFusedContinuation_certificate
lemma powerScalarFusedContinuation_certificate (q b : ℕ) (v : ℚ) :
    let prepared := powerLogProgram.eval [q,b,v,v]
    let endpoints := powerExpClipProgram.eval [prepared.1,prepared.2,b,v,v]
    paperPowerScalar q b v = rationalBox endpoints.1 endpoints.2 := by
  dsimp only
  rw [powerLogProgram_eval, powerExpClipProgram_eval]
  exact paperPowerScalar_eq_powerClipBox q b v


end CausalSmith.Stat.LogoddsLowsmoothFrontier
