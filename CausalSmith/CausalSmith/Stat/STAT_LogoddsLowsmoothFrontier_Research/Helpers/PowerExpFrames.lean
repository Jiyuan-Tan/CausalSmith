module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerClipProgram

/-! # Exponential register calls on active power frames

The existing exponential recurrence can start with arbitrary spare registers.
Its exact output certificate and untouched-register law allow the power computation
to retain its precision, base, and second exponent across an exponential call.
-/
@[expose] public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Initialization of the exponential loop from an arbitrary active frame.](goal) Under [the stated assumptions](hyp:hp₀,ha₀). -/
-- @node: expRegisterCode_start_frame
lemma expRegisterCode_start_frame (s : RationalState) (hp₀ : s.1 = 0)
    (ha₀ : s.2.2 = false) :
    ExpRegisterInvariant false (⌊s.2.1 0⌋ : ℤ).toNat 0
      (2*seriesCount (⌊s.2.1 0⌋ : ℤ).toNat (s.2.1 1))
      (s.2.1 1) (s.2.1 0) 0 (s.2.1 2)
      (expRegisterCode.run 23 (s)) := by
  rw [show 23 = 3+20 by rfl, rationalProgram_run_add]
  have hp : (expRegisterCode.run 3 (s)).1 = 3 := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp₀, ha₀]
  have ha : (expRegisterCode.run 3 (s)).2.2 = false := by
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step, hp₀, ha₀]
  have h := expRegisterCode_initial false _ hp ha
  convert h using 1 <;>
    norm_num [expRegisterCode, RationalProgram.run, RationalProgram.step,
      hp₀, ha₀, Function.update_apply]


/-- [Both endpoint loops are certified without zeroing the spare registers.](goal) Under [the stated assumptions](hyp:hp₀,ha₀). -/
-- @node: expRegisterCode_result_frame
lemma expRegisterCode_result_frame (s₀ : RationalState) (hp₀ : s₀.1 = 0)
    (ha₀ : s₀.2.2 = false) :
    let q := (⌊s₀.2.1 0⌋ : ℤ).toNat
    let lo := (paperExpScalar q (s₀.2.1 1)).lo
    let hi := (paperExpScalar q (s₀.2.1 2)).hi
    let t := expRegisterCode.run (expRegisterFuel [s₀.2.1 0,s₀.2.1 1,s₀.2.1 2]) (s₀)
    t.2.2 = true ∧ t.2.1 0 = lo ∧ t.2.1 1 = hi := by
  let q := (⌊s₀.2.1 0⌋ : ℤ).toNat
  let z := s₀.2.1 1
  let w := s₀.2.1 2
  let N := 2*seriesCount q z
  let M := 2*seriesCount q w
  have h := expRegisterCode_loop false q 0 N z _ 0 w _ (expRegisterCode_start_frame s₀ hp₀ ha₀)
  simp only [expRegisterFuel, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  have hf : 78+7*(N+M) = 23+(7*N+15)+(3+20)+(7*M+15)+2 := by omega
  rw [hf, rationalProgram_run_add _ (23+(7*N+15)+(3+20)+(7*M+15)) 2,
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


/-- [The destination register of a writing instruction, if any. -/
-- @node: rationalInstruction_destination
def rationalInstruction_destination : RationalInstruction → Option ℕ
  | .constant d _ | .copy d _ | .add d _ _ | .sub d _ _ | .mul d _ _
  | .div d _ _ | .min d _ _ | .max d _ _ | .floor d _ | .ceil d _
  | .factorial d _ | .integerSqrt d _ | .clogTwo d _ | .natPow d _ _ => some d
  | .branchLe _ _ _ _ | .jump _ | .halt => none

/-- A register not written by the code survives one step, including halting. Under the stated assumptions. [The stated hypotheses](hyp:h) hold, and [the stated conclusion follows](goal). -/
-- @node: rationalProgram_step_preserves
lemma rationalProgram_step_preserves (code : RationalProgram) (i : ℕ)
    (h : ∀ op ∈ code, rationalInstruction_destination op ≠ some i)
    (s : RationalState) : (code.step s).2.1 i = s.2.1 i := by
  unfold RationalProgram.step
  split
  · rfl
  · cases he : code[s.1]? with
    | none => simp [he]
    | some op =>
      have hm : op ∈ code := List.mem_of_getElem? he
      have hn := h op hm
      cases op <;> simp_all [rationalInstruction_destination, Function.update_apply] <;> aesop

/-- [An untouched register survives any finite recurrence.](goal) Under [the stated assumptions](hyp:h). -/
-- @node: rationalProgram_run_preserves
lemma rationalProgram_run_preserves (code : RationalProgram) (i : ℕ)
    (h : ∀ op ∈ code, rationalInstruction_destination op ≠ some i)
    (fuel : ℕ) (s : RationalState) : (code.run fuel s).2.1 i = s.2.1 i := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [RationalProgram.run, ih, rationalProgram_step_preserves code i h s]

/-- [The exponential routine never writes registers at or above twenty-one.](goal) Under [the stated assumptions](hyp:hi). -/
-- @node: expRegisterCode_spare_register
lemma expRegisterCode_spare_register (i : ℕ) (hi : 21 ≤ i) (fuel : ℕ)
    (s : RationalState) : (expRegisterCode.run fuel s).2.1 i = s.2.1 i := by
  apply rationalProgram_run_preserves
  intro op hop
  simp only [expRegisterCode, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst op <;> simp [rationalInstruction_destination] <;> omega

/-- [Relocate only control-flow targets; arithmetic registers retain their meaning. -/
-- @node: rationalInstruction_relocate
def rationalInstruction_relocate (offset : ℕ) : RationalInstruction → RationalInstruction
  | .branchLe a b yes no => .branchLe a b (offset+yes) (offset+no)
  | .jump target => .jump (offset+target)
  | op => op

/-- Shift a frame into a code block appended after a fixed prelude. -/
-- @node: rationalState_relocate
def rationalState_relocate (offset : ℕ) (s : RationalState) : RationalState :=
  (offset+s.1,s.2.1,s.2.2)

/-- Instruction lookup in a relocated appended block agrees with the original code. [the stated conclusion](goal) holds. -/
-- @node: rationalProgram_relocate_lookup
lemma rationalProgram_relocate_lookup (prelude code : RationalProgram) (pc : ℕ) :
    (prelude ++ code.map (rationalInstruction_relocate prelude.length))[prelude.length+pc]? =
      (code[pc]?).map (rationalInstruction_relocate prelude.length) := by
  simp [List.getElem?_append, List.getElem?_map]

/-- Relocation preserves one step for every frame, including arbitrary branches and halt. [the stated conclusion](goal) holds. -/
-- @node: rationalProgram_relocate_step
lemma rationalProgram_relocate_step (prelude code : RationalProgram) (s : RationalState) :
    (prelude ++ code.map (rationalInstruction_relocate prelude.length)).step
      (rationalState_relocate prelude.length s) =
    rationalState_relocate prelude.length (code.step s) := by
  by_cases ha : s.2.2 = true
  · simp [RationalProgram.step, rationalState_relocate, ha]
  · simp only [RationalProgram.step, rationalState_relocate, ha, ↓reduceIte]
    rw [rationalProgram_relocate_lookup]
    cases he : code[s.1]? with
    | none => simp [he, rationalState_relocate]
    | some op =>
      cases op <;> simp [he, rationalInstruction_relocate, rationalState_relocate,
        Nat.add_assoc] <;> split <;> rfl

/-- Every finite run of an appended relocated block is the relocated original run. [the stated conclusion](goal) holds. -/
-- @node: rationalProgram_relocate_run
lemma rationalProgram_relocate_run (prelude code : RationalProgram) (fuel : ℕ)
    (s : RationalState) :
    (prelude ++ code.map (rationalInstruction_relocate prelude.length)).run fuel
      (rationalState_relocate prelude.length s) =
    rationalState_relocate prelude.length (code.run fuel s) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [RationalProgram.run, rationalProgram_relocate_step, ih, RationalProgram.run]

/-- Save the power frame, then prepare a point-input exponential call for the left exponent. -/
-- @node: powerExpPrelude
def powerExpPrelude : RationalProgram :=
  [.copy 24 0, .copy 25 2, .copy 26 4, .copy 27 1, .mul 1 3 1, .copy 2 1]

/-- The continuation is one literal code list with every exponential branch relocated. -/
-- @node: powerExpCode
def powerExpCode : RationalProgram :=
  powerExpPrelude ++ expRegisterCode.map (rationalInstruction_relocate powerExpPrelude.length)

/-- Its exact finite instruction count includes preparation and both scalar loops. -/
-- @node: powerExpFrameFuel
def powerExpFrameFuel (s : RationalState) : ℕ :=
  6 + expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]

set_option maxHeartbeats 1000000 in
/-- The preparation block preserves all data needed for the later clipping and right call. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerExpCode_prepare
lemma powerExpCode_prepare (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let t := powerExpCode.run 6 s
    t.1 = 6 ∧ t.2.2 = false ∧ t.2.1 0 = s.2.1 0 ∧
    t.2.1 1 = s.2.1 3*s.2.1 1 ∧ t.2.1 2 = s.2.1 3*s.2.1 1 ∧
    t.2.1 24 = s.2.1 0 ∧ t.2.1 25 = s.2.1 2 ∧
    t.2.1 26 = s.2.1 4 ∧ t.2.1 27 = s.2.1 1 := by
  generalize he : powerExpCode.run 6 s = t
  norm_num [powerExpCode, powerExpPrelude, RationalProgram.run, RationalProgram.step,
    Function.update_apply, hp, ha] at he
  subst t
  norm_num [Function.update_apply]

set_option maxHeartbeats 1000000 in
/-- [The relocated exponential computation certifies the left power argument while
retaining the internal precision, base, right exponent, and logarithm midpoint. [the documented result](goal) Under [the stated assumptions](hyp:ha). Under [the stated assumptions](hyp:hp). -/
-- @node: powerExpCode_result
lemma powerExpCode_result (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let J := paperExpScalar p (s.2.1 3*s.2.1 1)
    let t := powerExpCode.run (powerExpFrameFuel s) s
    t.2.2 = true ∧ t.2.1 0 = J.lo ∧ t.2.1 1 = J.hi ∧
    t.2.1 24 = s.2.1 0 ∧ t.2.1 25 = s.2.1 2 ∧
    t.2.1 26 = s.2.1 4 ∧ t.2.1 27 = s.2.1 1 := by
  have hprep := powerExpCode_prepare s hp ha
  dsimp only [powerExpFrameFuel]
  rw [rationalProgram_run_add]
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
  have hout := expRegisterCode_result_frame u rfl rfl
  have hs24 := expRegisterCode_spare_register 24 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]) u
  have hs25 := expRegisterCode_spare_register 25 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]) u
  have hs26 := expRegisterCode_spare_register 26 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]) u
  have hs27 := expRegisterCode_spare_register 27 (by omega)
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]) u
  dsimp only [u] at hout hs24 hs25 hs26 hs27
  simp only [h0,h1,h2] at hout
  have hrun := rationalProgram_relocate_run powerExpPrelude expRegisterCode
    (expRegisterFuel [s.2.1 0,s.2.1 3*s.2.1 1,s.2.1 3*s.2.1 1]) u
  change powerExpCode.run _ (rationalState_relocate powerExpPrelude.length u) = _ at hrun
  rw [← ht] at hrun
  rw [hrun]
  dsimp only [rationalState_relocate]
  dsimp only [u]
  exact ⟨hout.1,hout.2.1,hout.2.2,hs24.trans h24,hs25.trans h25,
    hs26.trans h26,hs27.trans h27⟩

/-- [A straight-line recurrence computes the continuation's exact step bound. -/
-- @node: powerExpFuelCode
def powerExpFuelCode : RationalProgram :=
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
   .constant 13 84, .add 0 0 13, .halt]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- The continuation fuel is a total public rational computation on its input frame. [the stated conclusion](goal) holds. -/
-- @node: powerExpFrameFuel_public
lemma powerExpFrameFuel_public :
    PublicIterationBound (fun xs => powerExpFrameFuel (RationalProgram.initial xs)) := by
  refine ⟨powerExpFuelCode, ?_⟩
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
  · norm_num [powerExpFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply]
  · norm_num [powerExpFuelCode, RationalProgram.run, RationalProgram.step,
      RationalProgram.initial, Function.update_apply, powerExpFrameFuel, expRegisterFuel, seriesCount,
      Nat.cast_add, Nat.cast_mul, Nat.cast_max, Nat.cast_pow, hq, habs, hB]
    simp only [← abs_mul, hB]
    ring

/-- The exponential continuation is a certified bounded program on every input list. -/
-- @node: powerExpProgram
def powerExpProgram : BoundedRationalProgram where
  code := powerExpCode
  iterationBound := fun xs => powerExpFrameFuel (RationalProgram.initial xs)
  public_bound := powerExpFrameFuel_public
  halts := fun xs => (powerExpCode_result (RationalProgram.initial xs) rfl rfl).1

/-- The bounded continuation returns the exact point exponential bracket. Under the stated assumptions. [The stated conclusion follows](goal). -/
-- @node: powerExpProgram_eval
lemma powerExpProgram_eval (p b : ℕ) (mid lo hi : ℚ) :
    powerExpProgram.eval [p,mid,b,lo,hi] =
      ((paperExpScalar p (lo*mid)).lo,(paperExpScalar p (lo*mid)).hi) := by
  have h := powerExpCode_result (RationalProgram.initial [(p : ℚ),mid,b,lo,hi]) rfl rfl
  simp only [RationalProgram.initial, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Int.floor_natCast, Int.toNat_natCast] at h
  dsimp only [BoundedRationalProgram.eval, powerExpProgram, RationalProgram.initial]
  rw [h.2.1,h.2.2.1]

/-- The certified continuation replaces the standalone exponential call in the
power scalar assembly, returning exactly the prescribed clipped formula. [the documented result](goal) -/
-- @node: powerScalarContinuation_certificate
lemma powerScalarContinuation_certificate (q b : ℕ) (v : ℚ) :
    let prepared := powerLogProgram.eval [q,b,v,v]
    let exponential := powerExpProgram.eval [prepared.1,prepared.2,b,v,v]
    let clipped := powerClipProgram.eval [prepared.1,b,exponential.1,exponential.2]
    paperPowerScalar q b v = rationalBox clipped.1 clipped.2 := by
  dsimp only
  simp only [powerLogProgram_eval, powerExpProgram_eval, powerClipProgram_eval]
  exact paperPowerScalar_eq_powerClipBox q b v

end CausalSmith.Stat.LogoddsLowsmoothFrontier
