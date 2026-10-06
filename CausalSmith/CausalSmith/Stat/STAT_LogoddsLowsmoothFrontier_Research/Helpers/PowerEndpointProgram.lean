module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerScalarBudget

/-! # A fused two-endpoint power register program

This module joins two certified scalar power calls.  A small bridge retains the
lower endpoint of the left call in spare registers while the right call runs.
-/
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Away from the base-one shortcut, the clipping routine reaches its final halt
instruction after exactly twenty-six active steps. [the documented result](goal) Under [the stated assumptions](hyp:ha,hb). Under [the stated assumptions](hyp:hp). -/
lemma powerClipCode_before_halt_of_ne_one (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) (hb : (⌊s.2.1 1⌋ : ℤ).toNat ≠ 1) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let b := (⌊s.2.1 1⌋ : ℤ).toNat
    let e := 96 * (max 2 b : ℚ)^3 * rationalError p
    let t := powerClipCode.run (if b = 0 then 23 else 22) s
    t.1 = 26 ∧ t.2.2 = false ∧
      t.2.1 0 = max (1/(b : ℚ)^3) (s.2.1 2-e) ∧
      t.2.1 1 = min ((b : ℚ)^3) (s.2.1 3+e) := by
  dsimp only
  let b := (⌊s.2.1 1⌋ : ℤ).toNat
  let p := (⌊s.2.1 0⌋ : ℤ).toNat
  have hpre :
      let t := powerClipCode.run 6 s
      t.1 = 6 ∧ t.2.2 = false ∧ t.2.1 14 = p ∧ t.2.1 21 = b ∧
      t.2.1 8 = 1 ∧ t.2.1 2 = s.2.1 2 ∧ t.2.1 3 = s.2.1 3 := by
    norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, powerRegister_clamp_cast, p, b]
  rw [show (if b = 0 then 23 else 22) = 6 + (if b = 0 then 17 else 16) by
    split <;> rfl, rationalProgram_run_add]
  generalize he : powerClipCode.run 6 s = t at hpre ⊢
  dsimp only at hpre
  obtain ⟨htp, hta, hprecision, hbase, hone, hlo, hhi⟩ := hpre
  by_cases hz : b = 0
  · simp only [if_pos hz]
    norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, htp, hta, hbase, hone, hprecision, hz,
      hlo, hhi, rationalError, p, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      show (3 : ℤ).toNat = 3 by rfl]
    have hc : (max (⌊s.2.1 0⌋ : ℤ) 0).toNat = p := by dsimp [p]; omega
    rw [hc]
    rw [show (⌊s.2.1 0⌋ : ℤ).toNat = p by rfl,
      show (⌊s.2.1 1⌋ : ℤ).toNat = b by rfl]
    simp [hz, rationalError]
    constructor <;> congr 2 <;> ring
  · have hgt : ¬ (b : ℚ) ≤ 1 := by exact_mod_cast (show ¬ b ≤ 1 by omega)
    simp only [if_neg hz]
    norm_num [powerClipCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, htp, hta, hbase, hone, hprecision, hgt,
      hlo, hhi, rationalError, hb, hz, p, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      show (3 : ℤ).toNat = 3 by rfl]
    have hc : (max (⌊s.2.1 0⌋ : ℤ) 0).toNat = p := by dsimp [p]; omega
    rw [hc]
    rw [show (⌊s.2.1 0⌋ : ℤ).toNat = p by rfl,
      show (⌊s.2.1 1⌋ : ℤ).toNat = b by rfl]
    simp [rationalError]

/-- [Exact active fuel for the relocated clipping tail outside the base-one shortcut. -/
def powerClipTailActiveFuel (s : RationalState) : ℕ :=
  if (⌊s.2.1 25⌋ : ℤ).toNat = 0 then 27 else 26

/-- The clipping tail reaches its final active frame with the raw clipped endpoints. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha,hb) hold, and [the stated conclusion follows](goal). -/
lemma powerClipTail_before_halt_of_ne_one (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) (hb : (⌊s.2.1 25⌋ : ℤ).toNat ≠ 1) :
    let p := (⌊s.2.1 24⌋ : ℤ).toNat
    let b := (⌊s.2.1 25⌋ : ℤ).toNat
    let e := 96 * (max 2 b : ℚ)^3 * rationalError p
    let t := powerClipTail.run (powerClipTailActiveFuel s) s
    t.1 = 30 ∧ t.2.2 = false ∧
      t.2.1 0 = max (1/(b : ℚ)^3) (s.2.1 0-e) ∧
      t.2.1 1 = min ((b : ℚ)^3) (s.2.1 1+e) := by
  have hprep := powerClipTail_prepare s hp ha
  simp only [powerClipTailActiveFuel]
  rw [show (if (⌊s.2.1 25⌋ : ℤ).toNat = 0 then 27 else 26) =
      4 + (if (⌊s.2.1 25⌋ : ℤ).toNat = 0 then 23 else 22) by split <;> rfl,
    rationalProgram_run_add]
  generalize he : powerClipTail.run 4 s = t at hprep ⊢
  dsimp only at hprep
  obtain ⟨htp, hta, h0, h1, h2, h3⟩ := hprep
  let u : RationalState := (0,t.2.1,false)
  have ht : t = rationalState_relocate powerClipPrelude.length u := by
    apply Prod.ext
    · simpa [rationalState_relocate, powerClipPrelude, u] using htp
    · exact Prod.ext rfl hta
  have hout := powerClipCode_before_halt_of_ne_one u rfl rfl (by simpa [u, h1] using hb)
  dsimp only [u] at hout
  simp only [h0, h1, h2, h3] at hout
  rw [ht]
  rw [show powerClipTail = powerClipPrelude ++ powerClipCode.map
    (rationalInstruction_relocate powerClipPrelude.length) by rfl,
    rationalProgram_relocate_run]
  dsimp only [rationalState_relocate]
  rcases hout with ⟨hpc, hactive, hlo, hhi⟩
  simp only [Int.toNat_eq_zero] at hpc hactive hlo hhi
  refine ⟨by simp [powerClipPrelude, u, Int.toNat_eq_zero, hpc], ?_, ?_, ?_⟩
  · simpa [u, Int.toNat_eq_zero] using hactive
  · simpa [u, Int.toNat_eq_zero] using hlo
  · simpa [u, Int.toNat_eq_zero] using hhi

/-- [Exact active fuel of the exponential-and-clipping continuation. -/
def powerExpClipActiveFuel (s : RationalState) : ℕ :=
  powerExpFrameFuel s + if (⌊s.2.1 2⌋ : ℤ).toNat = 0 then 27 else 26

/-- Outside base one, the fused exponential/clipping code reaches its final
active halt frame and already contains the scalar power bracket. [the documented result](goal) Under [the stated assumptions](hyp:ha,hb). Under [the stated assumptions](hyp:hp). -/
lemma powerExpClipCode_before_halt_of_ne_one (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) (hb : (⌊s.2.1 2⌋ : ℤ).toNat ≠ 1) :
    let p := (⌊s.2.1 0⌋ : ℤ).toNat
    let b := (⌊s.2.1 2⌋ : ℤ).toNat
    let J := paperExpScalar p (s.2.1 3*s.2.1 1)
    let t := powerExpClipCode.run (powerExpClipActiveFuel s) s
    t.1 = 126 ∧ t.2.2 = false ∧
      rationalBox (t.2.1 0) (t.2.1 1) = powerClipBox p b J.lo J.hi := by
  have h := powerExpCode_before_halt s hp ha
  have hf : powerExpClipActiveFuel s = (powerExpFrameFuel s-1)+1+
      (if (⌊s.2.1 2⌋ : ℤ).toNat = 0 then 27 else 26) := by
    simp only [powerExpClipActiveFuel, powerExpFrameFuel, expRegisterFuel]
    omega
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
  have hout := powerClipTail_before_halt_of_ne_one (0,t.2.1,false) rfl rfl (by
    simpa [h25] using hb)
  dsimp only at hout
  simp only [h24, h25, hlo, hhi, Int.floor_natCast, Int.toNat_natCast] at hout
  dsimp only [rationalState_relocate]
  rcases hout with ⟨hpc, hactive, hrawlo, hrawhi⟩
  simp only [powerClipTailActiveFuel, h25] at hpc hactive hrawlo hrawhi
  refine ⟨?_, hactive, ?_⟩
  · have hlen : powerExpCode.length = 96 := by rfl
    rw [hlen, hpc]
  rw [hrawlo, hrawhi]
  simp [powerClipBox, hb]

/-- [Exact fuel to the scalar program's active final halt frame outside base one. -/
def powerScalarActiveFuel (xs : List ℚ) : ℕ :=
  let t := powerLogCode.run (powerLogActiveFuel xs) (RationalProgram.initial xs)
  powerLogActiveFuel xs + 1 + powerExpClipActiveFuel (0,t.2.1,false)

/-- Outside base one, the scalar code reaches its active final frame with the
prescribed rational bracket. [the documented result](goal) Under [the stated assumptions](hyp:hb). -/
lemma powerScalarCode_before_halt_of_ne_one (xs : List ℚ)
    (hb : (⌊xs[1]?.getD 0⌋ : ℤ).toNat ≠ 1) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let v := xs[2]?.getD 0
    let t := powerScalarCode.run (powerScalarActiveFuel xs) (RationalProgram.initial xs)
    t.1 = 178 ∧ t.2.2 = false ∧
      rationalBox (t.2.1 0) (t.2.1 1) = paperPowerScalar q b v := by
  have h := powerLogCode_before_halt xs
  dsimp only at h
  rw [← powerLogActiveFuel] at h
  dsimp only [powerScalarActiveFuel]
  rw [rationalProgram_run_add, rationalProgram_run_add]
  have hrun := rationalProgram_continue_run powerLogCode powerExpClipCode
    (powerLogActiveFuel xs) (RationalProgram.initial xs) h.2.1
  change powerScalarCode.run _ _ = _ at hrun
  rw [hrun]
  generalize he : powerLogCode.run (powerLogActiveFuel xs)
    (RationalProgram.initial xs) = t at h ⊢
  obtain ⟨htp, hta, hq, hmid, hbreg, hv, _⟩ := h
  rw [show powerScalarCode.run 1 t = powerScalarCode.step t by rfl,
    powerScalarCode_connect t htp hta]
  rw [show powerScalarCode = rationalProgram_continue powerLogCode powerExpClipCode by rfl,
    rationalProgram_continue_tail]
  have hout := powerExpClipCode_before_halt_of_ne_one (0,t.2.1,false) rfl rfl (by
    simpa only [hbreg, Int.floor_natCast, Int.toNat_natCast] using hb)
  dsimp only at hout
  simp only [hq, hmid, hbreg, hv, Int.floor_natCast, Int.toNat_natCast] at hout
  dsimp only [rationalState_relocate]
  rcases hout with ⟨hpc, hactive, hbox⟩
  refine ⟨?_, hactive, ?_⟩
  · have hlen : powerLogCode.length = 52 := by rfl
    rw [hlen, hpc]
  · rw [hbox]
    exact (paperPowerScalar_eq_powerClipBox _ _ _).symm

/-- The exact active scalar run plus its final halt fits inside the published fuel. [the stated conclusion](goal) holds. -/
lemma powerScalarActiveFuel_succ_le_public (xs : List ℚ) :
    powerScalarActiveFuel xs + 1 ≤ powerScalarPublicFuel xs := by
  apply le_trans _ (powerScalarFuel_le_public xs)
  simp only [powerScalarActiveFuel, powerScalarFuel, powerExpClipActiveFuel,
    powerExpClipFuel]
  split <;> omega

/-- The scalar routine leaves registers forty and above untouched. Under the stated assumptions. [The stated hypotheses](hyp:hi) hold, and [the stated conclusion follows](goal). -/
lemma powerScalarCode_spare_register (i : ℕ) (hi : 40 ≤ i) (fuel : ℕ)
    (s : RationalState) : (powerScalarCode.run fuel s).2.1 i = s.2.1 i := by
  apply rationalProgram_run_preserves
  intro op hop hd
  have hbound : ∀ op ∈ powerScalarCode, ∀ d,
      rationalInstruction_destination op = some d → d < 40 := by decide
  exact not_lt_of_ge hi (hbound op hop i hd)

/-- [Finalize the right scalar call while restoring the saved left lower endpoint. -/
def powerEndpointRestoreTail : RationalProgram :=
  [.max 1 0 1, .copy 0 43, .halt]

/-- A scalar call whose halt continues into endpoint restoration. -/
def powerEndpointSecondCode : RationalProgram :=
  rationalProgram_continue powerScalarCode powerEndpointRestoreTail

/-- Save the left lower endpoint and restore the original inputs for the right call. -/
def powerEndpointSecondPrelude : RationalProgram :=
  [.min 43 0 1, .copy 0 40, .copy 1 41, .copy 2 42, .copy 3 46,
   .constant 4 0, .constant 5 0, .constant 6 0, .constant 7 0, .constant 8 0, .constant 9 0, .constant 10 0, .constant 11 0, .constant 12 0, .constant 13 0, .constant 14 0, .constant 15 0, .constant 16 0, .constant 17 0, .constant 18 0, .constant 19 0, .constant 20 0, .constant 21 0, .constant 22 0, .constant 23 0, .constant 24 0, .constant 25 0, .constant 26 0, .constant 27 0, .constant 28 0, .constant 29 0, .constant 30 0, .constant 31 0, .constant 32 0, .constant 33 0, .constant 34 0, .constant 35 0, .constant 36 0, .constant 37 0, .constant 38 0, .constant 39 0]

/-- The bridge and relocated right scalar call. -/
def powerEndpointSecondTail : RationalProgram :=
  powerEndpointSecondPrelude ++ powerEndpointSecondCode.map
    (rationalInstruction_relocate powerEndpointSecondPrelude.length)

/-- Two scalar calls joined at their active final halt frames. -/
def powerEndpointCore : RationalProgram :=
  rationalProgram_continue powerScalarCode powerEndpointSecondTail

/-- Dispatch base one directly; otherwise save inputs before entering the fused calls. -/
def powerEndpointPrelude : RationalProgram :=
  [.floor 44 1, .constant 45 0, .max 44 44 45, .constant 45 1,
   .branchLe 44 45 5 9, .branchLe 45 44 6 9,
   .constant 0 1, .constant 1 1, .halt,
   .copy 40 0, .copy 41 1, .copy 42 3, .copy 46 2,
   .constant 4 0, .constant 5 0, .constant 6 0, .constant 7 0, .constant 8 0, .constant 9 0, .constant 10 0, .constant 11 0, .constant 12 0, .constant 13 0, .constant 14 0, .constant 15 0, .constant 16 0, .constant 17 0, .constant 18 0, .constant 19 0, .constant 20 0, .constant 21 0, .constant 22 0, .constant 23 0, .constant 24 0, .constant 25 0, .constant 26 0, .constant 27 0, .constant 28 0, .constant 29 0, .constant 30 0, .constant 31 0, .constant 32 0, .constant 33 0, .constant 34 0, .constant 35 0, .constant 36 0, .constant 37 0, .constant 38 0, .constant 39 0]

/-- The complete two-endpoint power program. -/
def powerEndpointCode : RationalProgram :=
  powerEndpointPrelude ++ powerEndpointCore.map
    (rationalInstruction_relocate powerEndpointPrelude.length)

/-- Active prelude length outside base one. -/
def powerEndpointPreludeFuel (xs : List ℚ) : ℕ :=
  if (⌊xs[1]?.getD 0⌋ : ℤ).toNat = 0 then 46 else 45

/-- The outer prelude saves the common inputs and right exponent. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hb). -/
lemma powerEndpointPrelude_prepare (xs : List ℚ)
    (hb : (⌊xs[1]?.getD 0⌋ : ℤ).toNat ≠ 1) :
    let t := powerEndpointCode.run (powerEndpointPreludeFuel xs)
      (RationalProgram.initial xs)
    t.1 = 49 ∧ t.2.2 = false ∧ t.2.1 40 = xs[0]?.getD 0 ∧
      t.2.1 41 = xs[1]?.getD 0 ∧ t.2.1 42 = xs[3]?.getD 0 ∧
      t.2.1 46 = xs[2]?.getD 0 := by
  dsimp only [powerEndpointPreludeFuel]
  let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
  have hbcast : ((b : ℕ) : ℚ) = max (⌊xs[1]?.getD 0⌋ : ℤ) 0 := by
    exact_mod_cast (show (b : ℤ) = max (⌊xs[1]?.getD 0⌋ : ℤ) 0 by
      dsimp [b]; omega)
  by_cases hz : b = 0
  · have hle : (b : ℚ) ≤ 1 := by simp [hz]
    have hnle : ¬(1 : ℚ) ≤ b := by simp [hz]
    have hle' : ((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) ≤ 1 := by
      rw [← hbcast]; exact hle
    have hnle' : ¬(1 : ℚ) ≤ ((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) := by
      rw [← hbcast]; exact hnle
    have hraw : ((⌊xs[1]?.getD 0⌋ : ℤ) : ℚ) ≤ 1 := by
      exact_mod_cast (show (⌊xs[1]?.getD 0⌋ : ℤ) ≤ 1 by dsimp [b] at hz; omega)
    have hnraw : ¬(1 : ℚ) ≤ (⌊xs[1]?.getD 0⌋ : ℤ) := by
      exact_mod_cast (show ¬(1 : ℤ) ≤ ⌊xs[1]?.getD 0⌋ by dsimp [b] at hz; omega)
    norm_num [powerEndpointCode, powerEndpointPrelude, RationalProgram.run,
      RationalProgram.step, RationalProgram.initial, Function.update_apply,
      b, hz, hle, hnle, hle', hnle', hraw, hnraw]
  · have hnle : ¬(b : ℚ) ≤ 1 := by exact_mod_cast (show ¬ b ≤ 1 by omega)
    have hnle' : ¬((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) ≤ 1 := by
      rw [← hbcast]; exact hnle
    have hraw : ¬((⌊xs[1]?.getD 0⌋ : ℤ) : ℚ) ≤ 1 := by
      exact_mod_cast (show ¬(⌊xs[1]?.getD 0⌋ : ℤ) ≤ 1 by dsimp [b] at hz; omega)
    norm_num [powerEndpointCode, powerEndpointPrelude, RationalProgram.run,
      RationalProgram.step, RationalProgram.initial, Function.update_apply,
      b, hz, hnle, hnle', hraw]

/-- The four-instruction bridge prepares the second scalar call. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
lemma powerEndpointSecondPrelude_prepare (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let t := powerEndpointSecondTail.run 41 s
    t.1 = 41 ∧ t.2.2 = false ∧ t.2.1 43 = min (s.2.1 0) (s.2.1 1) ∧
      t.2.1 0 = s.2.1 40 ∧ t.2.1 1 = s.2.1 41 ∧
      t.2.1 2 = s.2.1 42 ∧ t.2.1 3 = s.2.1 46 ∧
      (∀ i, 4 ≤ i → i < 40 → t.2.1 i = 0) := by
  norm_num [powerEndpointSecondTail, powerEndpointSecondPrelude,
    RationalProgram.run, RationalProgram.step, hp, ha, Function.update_apply]
  intro i hlo hi
  interval_cases i <;> norm_num

/-- [The restoration tail reaches its active halt frame with the requested pair.](goal) Under [the stated assumptions](hyp:hp,ha). Under [the stated assumptions](hyp:ha). -/
lemma powerEndpointRestore_before_halt (s : RationalState) (hp : s.1 = 0)
    (ha : s.2.2 = false) :
    let t := powerEndpointRestoreTail.run 2 s
    t.1 = 2 ∧ t.2.2 = false ∧ t.2.1 0 = s.2.1 43 ∧
      t.2.1 1 = max (s.2.1 0) (s.2.1 1) := by
  norm_num [powerEndpointRestoreTail, RationalProgram.run, RationalProgram.step,
    hp, ha, Function.update_apply]

/-- [Every register mentioned by an instruction lies below a fixed cutoff. -/
def rationalInstructionBelow (n : ℕ) : RationalInstruction → Prop
  | .constant d _ => d < n
  | .copy d a | .floor d a | .ceil d a | .factorial d a |
      .integerSqrt d a | .clogTwo d a => d < n ∧ a < n
  | .add d a b | .sub d a b | .mul d a b | .div d a b |
      .min d a b | .max d a b | .natPow d a b => d < n ∧ a < n ∧ b < n
  | .branchLe a b _ _ => a < n ∧ b < n
  | .jump _ | .halt => True
/-- The [anonymous instance result](goal) states the corresponding mathematical identity, bound, or structural property. -/

instance (n : ℕ) (op : RationalInstruction) : Decidable (rationalInstructionBelow n op) := by
  cases op <;> simp [rationalInstructionBelow] <;> infer_instance

/-- Agreement of the control frame and all registers below a cutoff. -/
def rationalStateAgreeBelow (n : ℕ) (s t : RationalState) : Prop :=
  s.1 = t.1 ∧ s.2.2 = t.2.2 ∧ ∀ i < n, s.2.1 i = t.2.1 i
/-- The [rational Program step agree below result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:hcode,hst). Under [the stated assumptions](hyp:hst). -/

lemma rationalProgram_step_agree_below (code : RationalProgram) (n : ℕ)
    (hcode : ∀ op ∈ code, rationalInstructionBelow n op)
    (s t : RationalState) (hst : rationalStateAgreeBelow n s t) :
    rationalStateAgreeBelow n (code.step s) (code.step t) := by
  rcases hst with ⟨hpc, hhalt, hreg⟩
  unfold RationalProgram.step
  rw [hhalt]
  split
  · exact ⟨hpc, hhalt, hreg⟩
  · simp only
    rw [hpc]
    cases he : code[t.1]? with
    | none => exact ⟨rfl, rfl, hreg⟩
    | some op =>
      have hop : op ∈ code := List.mem_of_getElem? he
      have hb := hcode op hop
      cases op <;>
        simp_all [rationalStateAgreeBelow, rationalInstructionBelow,
          Function.update_apply] <;> aesop
/-- [The rational Program run agree below result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:hcode,hst). Under [the stated assumptions](hyp:hst). -/

lemma rationalProgram_run_agree_below (code : RationalProgram) (n : ℕ)
    (hcode : ∀ op ∈ code, rationalInstructionBelow n op)
    (fuel : ℕ) (s t : RationalState) (hst : rationalStateAgreeBelow n s t) :
    rationalStateAgreeBelow n (code.run fuel s) (code.run fuel t) := by
  induction fuel generalizing s t with
  | zero => exact hst
  | succ fuel ih =>
      rw [RationalProgram.run, RationalProgram.run]
      exact ih _ _ (rationalProgram_step_agree_below code n hcode s t hst)

/-- [The scalar code depends only on registers below forty. [the stated conclusion](goal) holds. -/
lemma powerScalarCode_below : ∀ op ∈ powerScalarCode, rationalInstructionBelow 40 op := by
  decide

/-- The scalar active-frame certificate is stable under arbitrary spare-register data. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hs,hb). -/
lemma powerScalarCode_before_halt_frame (xs : List ℚ) (s : RationalState)
    (hs : rationalStateAgreeBelow 40 s (RationalProgram.initial xs))
    (hb : (⌊xs[1]?.getD 0⌋ : ℤ).toNat ≠ 1) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let v := xs[2]?.getD 0
    let t := powerScalarCode.run (powerScalarActiveFuel xs) s
    t.1 = 178 ∧ t.2.2 = false ∧
      rationalBox (t.2.1 0) (t.2.1 1) = paperPowerScalar q b v := by
  have href := powerScalarCode_before_halt_of_ne_one xs hb
  have hagree := rationalProgram_run_agree_below powerScalarCode 40
    powerScalarCode_below (powerScalarActiveFuel xs) s (RationalProgram.initial xs) hs
  dsimp only at href ⊢
  rcases hagree with ⟨hpc, hhalt, hreg⟩
  refine ⟨hpc.trans href.1, hhalt.trans href.2.1, ?_⟩
  rw [hreg 0 (by omega), hreg 1 (by omega)]
  exact href.2.2

/-- The initial endpoint prelude changes only spare registers before the first call. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hb). -/
lemma powerEndpointPrelude_frame (xs : List ℚ)
    (hb : (⌊xs[1]?.getD 0⌋ : ℤ).toNat ≠ 1) :
    let t := powerEndpointCode.run (powerEndpointPreludeFuel xs)
      (RationalProgram.initial xs)
    rationalStateAgreeBelow 40 (0,t.2.1,false)
        (RationalProgram.initial
          [xs[0]?.getD 0, xs[1]?.getD 0, xs[2]?.getD 0, xs[3]?.getD 0]) ∧
      t.2.1 40 = xs[0]?.getD 0 ∧ t.2.1 41 = xs[1]?.getD 0 ∧
      t.2.1 42 = xs[3]?.getD 0 ∧ t.2.1 46 = xs[2]?.getD 0 := by
  dsimp only [powerEndpointPreludeFuel]
  let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
  have hbcast : ((b : ℕ) : ℚ) = max (⌊xs[1]?.getD 0⌋ : ℤ) 0 := by
    exact_mod_cast (show (b : ℤ) = max (⌊xs[1]?.getD 0⌋ : ℤ) 0 by
      dsimp [b]; omega)
  by_cases hz : b = 0
  · have hle : (b : ℚ) ≤ 1 := by simp [hz]
    have hnle : ¬(1 : ℚ) ≤ b := by simp [hz]
    have hle' : ((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) ≤ 1 := by
      rw [← hbcast]; exact hle
    have hnle' : ¬(1 : ℚ) ≤ ((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) := by
      rw [← hbcast]; exact hnle
    have hraw : ((⌊xs[1]?.getD 0⌋ : ℤ) : ℚ) ≤ 1 := by
      exact_mod_cast (show (⌊xs[1]?.getD 0⌋ : ℤ) ≤ 1 by dsimp [b] at hz; omega)
    have hnraw : ¬(1 : ℚ) ≤ (⌊xs[1]?.getD 0⌋ : ℤ) := by
      exact_mod_cast (show ¬(1 : ℤ) ≤ ⌊xs[1]?.getD 0⌋ by dsimp [b] at hz; omega)
    norm_num [powerEndpointCode, powerEndpointPrelude, RationalProgram.run,
      RationalProgram.step, RationalProgram.initial, Function.update_apply,
      rationalStateAgreeBelow, b, hz, hle, hnle, hle', hnle', hraw, hnraw]
    intro i hi
    interval_cases i <;> simp [RationalProgram.initial]
  · have hnle : ¬(b : ℚ) ≤ 1 := by exact_mod_cast (show ¬ b ≤ 1 by omega)
    have hnle' : ¬((max (⌊xs[1]?.getD 0⌋ : ℤ) 0 : ℤ) : ℚ) ≤ 1 := by
      rw [← hbcast]; exact hnle
    have hraw : ¬((⌊xs[1]?.getD 0⌋ : ℤ) : ℚ) ≤ 1 := by
      exact_mod_cast (show ¬(⌊xs[1]?.getD 0⌋ : ℤ) ≤ 1 by dsimp [b] at hz; omega)
    norm_num [powerEndpointCode, powerEndpointPrelude, RationalProgram.run,
      RationalProgram.step, RationalProgram.initial, Function.update_apply,
      rationalStateAgreeBelow, b, hz, hnle, hnle', hraw]
    intro i hi
    interval_cases i <;> simp [RationalProgram.initial]

/-- The first scalar final halt jumps into the endpoint bridge. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
lemma powerEndpointCore_connect (s : RationalState) (hp : s.1 = 178)
    (ha : s.2.2 = false) :
    powerEndpointCore.step s =
      rationalState_relocate powerScalarCode.length (0,s.2.1,false) := by
  have hlen : powerScalarCode.length = 179 := by rfl
  have hlookup : powerScalarCode[178]? = some .halt := by rfl
  simp only [powerEndpointCore, rationalProgram_continue, RationalProgram.step,
    ha, Bool.false_eq_true, ↓reduceIte, hp, List.getElem?_append, List.length_map,
    hlen, show 178 < 179 by omega, ↓reduceIte, List.getElem?_map, hlookup,
    Option.map_some, rationalInstruction_continue, rationalState_relocate, Nat.add_zero]

/-- [The second scalar final halt jumps into endpoint restoration.](goal) Under [the stated assumptions](hyp:hp,ha). Under [the stated assumptions](hyp:ha). -/
lemma powerEndpointSecondCode_connect (s : RationalState) (hp : s.1 = 178)
    (ha : s.2.2 = false) :
    powerEndpointSecondCode.step s =
      rationalState_relocate powerScalarCode.length (0,s.2.1,false) := by
  have hlen : powerScalarCode.length = 179 := by rfl
  have hlookup : powerScalarCode[178]? = some .halt := by rfl
  simp only [powerEndpointSecondCode, rationalProgram_continue, RationalProgram.step,
    ha, Bool.false_eq_true, ↓reduceIte, hp, List.getElem?_append, List.length_map,
    hlen, show 178 < 179 by omega, ↓reduceIte, List.getElem?_map, hlookup,
    Option.map_some, rationalInstruction_continue, rationalState_relocate, Nat.add_zero]

/-- [Exact active fuel of the fused core for a pair of scalar inputs. -/
def powerEndpointCoreActiveFuel (leftArgs rightArgs : List ℚ) : ℕ :=
  powerScalarActiveFuel leftArgs + 1 + 41 +
    powerScalarActiveFuel rightArgs + 1 + 2

/-- The fused core returns the left lower and right upper scalar endpoints. Under the stated assumptions. Under the stated assumptions. [The stated hypotheses](hyp:hs,h40,h41,h42,h46,hrzero,hb,hrb) hold, and [the stated conclusion follows](goal). -/
lemma powerEndpointCore_before_halt (leftArgs rightArgs : List ℚ) (s : RationalState)
    (hs : rationalStateAgreeBelow 40 s (RationalProgram.initial leftArgs))
    (h40 : s.2.1 40 = rightArgs[0]?.getD 0)
    (h41 : s.2.1 41 = rightArgs[1]?.getD 0)
    (h42 : s.2.1 42 = rightArgs[2]?.getD 0)
    (h46 : s.2.1 46 = rightArgs[3]?.getD 0)
    (hrzero : ∀ i, 4 ≤ i → i < 40 → rightArgs[i]?.getD 0 = 0)
    (hb : (⌊leftArgs[1]?.getD 0⌋ : ℤ).toNat ≠ 1)
    (hrb : (⌊rightArgs[1]?.getD 0⌋ : ℤ).toNat ≠ 1) :
    let ql := (⌊leftArgs[0]?.getD 0⌋ : ℤ).toNat
    let bl := (⌊leftArgs[1]?.getD 0⌋ : ℤ).toNat
    let qr := (⌊rightArgs[0]?.getD 0⌋ : ℤ).toNat
    let br := (⌊rightArgs[1]?.getD 0⌋ : ℤ).toNat
    let t := powerEndpointCore.run (powerEndpointCoreActiveFuel leftArgs rightArgs) s
    t.1 = 401 ∧ t.2.2 = false ∧
      rationalBox (t.2.1 0) (t.2.1 1) =
        rationalBox (paperPowerScalar ql bl (leftArgs[2]?.getD 0)).lo
          (paperPowerScalar qr br (rightArgs[2]?.getD 0)).hi := by
  have hleft := powerScalarCode_before_halt_frame leftArgs s hs hb
  dsimp only [powerEndpointCoreActiveFuel]
  rw [show powerScalarActiveFuel leftArgs + 1 + 41 + powerScalarActiveFuel rightArgs + 1 + 2 =
    powerScalarActiveFuel leftArgs + (1 + 41 + powerScalarActiveFuel rightArgs + 1 + 2) by omega,
    rationalProgram_run_add]
  dsimp only at hleft
  have hrun := rationalProgram_continue_run powerScalarCode powerEndpointSecondTail
    (powerScalarActiveFuel leftArgs) s hleft.2.1
  change powerEndpointCore.run _ s = _ at hrun
  rw [hrun]
  generalize he : powerScalarCode.run (powerScalarActiveFuel leftArgs) s = t at hleft ⊢
  rcases hleft with ⟨htp, hta, hleftbox⟩
  have hs40 := powerScalarCode_spare_register 40 (by omega)
    (powerScalarActiveFuel leftArgs) s
  have hs41 := powerScalarCode_spare_register 41 (by omega)
    (powerScalarActiveFuel leftArgs) s
  have hs42 := powerScalarCode_spare_register 42 (by omega)
    (powerScalarActiveFuel leftArgs) s
  have hs46 := powerScalarCode_spare_register 46 (by omega)
    (powerScalarActiveFuel leftArgs) s
  rw [he] at hs40 hs41 hs42 hs46
  rw [show 1 + 41 + powerScalarActiveFuel rightArgs + 1 + 2 =
    1 + (41 + powerScalarActiveFuel rightArgs + 1 + 2) by omega,
    rationalProgram_run_add]
  rw [show powerEndpointCore.run 1 t = powerEndpointCore.step t by rfl,
    powerEndpointCore_connect t htp hta]
  rw [show powerEndpointCore = rationalProgram_continue powerScalarCode
    powerEndpointSecondTail by rfl, rationalProgram_continue_tail]
  rw [show 41 + powerScalarActiveFuel rightArgs + 1 + 2 =
    41 + (powerScalarActiveFuel rightArgs + 1 + 2) by omega,
    rationalProgram_run_add]
  have hprep := powerEndpointSecondPrelude_prepare (0,t.2.1,false) rfl rfl
  generalize hp : powerEndpointSecondTail.run 41 (0,t.2.1,false) = u at hprep ⊢
  dsimp only at hprep
  obtain ⟨hupc, hua, hu43, hu0, hu1, hu2, hu3, huzero⟩ := hprep
  have huagree : rationalStateAgreeBelow 40 (0,u.2.1,false)
      (RationalProgram.initial rightArgs) := by
    refine ⟨rfl, rfl, ?_⟩
    intro i hi
    interval_cases i <;> simp [RationalProgram.initial, hu0, hu1, hu2, hu3,
      hs40, hs41, hs42, hs46, h40, h41, h42, h46, hrzero, huzero]
  let v : RationalState := (0,u.2.1,false)
  have hu : u = rationalState_relocate powerEndpointSecondPrelude.length v := by
    apply Prod.ext
    · simpa [rationalState_relocate, powerEndpointSecondPrelude, v] using hupc
    · exact Prod.ext rfl hua
  rw [hu]
  rw [show powerEndpointSecondTail = powerEndpointSecondPrelude ++
    powerEndpointSecondCode.map (rationalInstruction_relocate
      powerEndpointSecondPrelude.length) by rfl, rationalProgram_relocate_run]
  dsimp only [rationalState_relocate]
  have hright := powerScalarCode_before_halt_frame rightArgs v huagree hrb
  dsimp only at hright
  rw [show powerScalarActiveFuel rightArgs + 1 + 2 =
    powerScalarActiveFuel rightArgs + (1 + 2) by omega,
    rationalProgram_run_add]
  have hrun2 := rationalProgram_continue_run powerScalarCode powerEndpointRestoreTail
    (powerScalarActiveFuel rightArgs) v hright.2.1
  change powerEndpointSecondCode.run _ v = _ at hrun2
  rw [hrun2]
  generalize hr : powerScalarCode.run (powerScalarActiveFuel rightArgs) v = w at hright ⊢
  rcases hright with ⟨hwpc, hwa, hrightbox⟩
  have hw43 := powerScalarCode_spare_register 43 (by omega)
    (powerScalarActiveFuel rightArgs) v
  rw [hr] at hw43
  rw [rationalProgram_run_add]
  rw [show powerEndpointSecondCode.run 1 w = powerEndpointSecondCode.step w by rfl,
    powerEndpointSecondCode_connect w hwpc hwa]
  rw [show powerEndpointSecondCode = rationalProgram_continue powerScalarCode
    powerEndpointRestoreTail by rfl, rationalProgram_continue_tail]
  have hrestore := powerEndpointRestore_before_halt (0,w.2.1,false) rfl rfl
  dsimp only at hrestore
  dsimp only [rationalState_relocate]
  rcases hrestore with ⟨hrpc, hra, hr0, hr1⟩
  refine ⟨?_, hra, ?_⟩
  · have hslen : powerScalarCode.length = 179 := by rfl
    have hplen : powerEndpointSecondPrelude.length = 41 := by rfl
    rw [hslen, hplen, hrpc]
  rw [hr0, hr1, hw43]
  have hv43 : v.2.1 43 = min (t.2.1 0) (t.2.1 1) := by
    simpa [v] using hu43
  rw [hv43]
  have hleftlo := congrArg RatInterval.lo hleftbox
  have hrighthi := congrArg RatInterval.hi hrightbox
  simp only [rationalBox] at hleftlo hrighthi
  rw [hleftlo, hrighthi]

/-- [Arguments for the left scalar endpoint. -/
def powerEndpointLeftArgs (xs : List ℚ) : List ℚ :=
  [xs[0]?.getD 0, xs[1]?.getD 0, xs[2]?.getD 0, xs[3]?.getD 0]

/-- Arguments for the right scalar endpoint. -/
def powerEndpointRightArgs (xs : List ℚ) : List ℚ :=
  [xs[0]?.getD 0, xs[1]?.getD 0, xs[3]?.getD 0, xs[2]?.getD 0]

/-- Exact fuel through the final halt of the two-endpoint program. -/
def powerEndpointExactFuel (xs : List ℚ) : ℕ :=
  if (⌊xs[1]?.getD 0⌋ : ℤ).toNat = 1 then 9 else
    powerEndpointPreludeFuel xs +
      powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs) (powerEndpointRightArgs xs) + 1

/-- The exact fused run halts and returns the desired endpoint extension. [the stated conclusion](goal) holds. -/
lemma powerEndpointCode_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let t := powerEndpointCode.run (powerEndpointExactFuel xs)
      (RationalProgram.initial xs)
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) =
      rationalBox (paperPowerScalar q b (xs[2]?.getD 0)).lo
        (paperPowerScalar q b (xs[3]?.getD 0)).hi := by
  let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
  by_cases hb : b = 1
  · have hbcast : max (⌊xs[1]?.getD 0⌋ : ℤ) 0 = (1 : ℚ) := by
      rw [← show (b : ℚ) = 1 by exact_mod_cast hb]
      exact_mod_cast (show max (⌊xs[1]?.getD 0⌋ : ℤ) 0 = (b : ℤ) by
        dsimp [b]; omega)
    have hfloor : ((⌊xs[1]?.getD 0⌋ : ℤ) : ℚ) = 1 := by
      exact_mod_cast (show (⌊xs[1]?.getD 0⌋ : ℤ) = 1 by dsimp [b] at hb; omega)
    norm_num [powerEndpointExactFuel, powerEndpointCode, powerEndpointPrelude,
      RationalProgram.run, RationalProgram.step, RationalProgram.initial,
      Function.update_apply, b, hb, hbcast, hfloor, paperPowerScalar,
      RatInterval.point, rationalBox]
  · have hprep := powerEndpointPrelude_prepare xs hb
    have hframe := powerEndpointPrelude_frame xs hb
    dsimp only [powerEndpointExactFuel]
    rw [if_neg hb, show powerEndpointPreludeFuel xs +
      powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs) (powerEndpointRightArgs xs) + 1 =
      powerEndpointPreludeFuel xs +
        (powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs)
          (powerEndpointRightArgs xs) + 1) by omega, rationalProgram_run_add]
    generalize hp : powerEndpointCode.run (powerEndpointPreludeFuel xs)
      (RationalProgram.initial xs) = t at hprep hframe ⊢
    dsimp only at hprep hframe
    rcases hprep with ⟨htp, hta, h40, h41, h42, h46⟩
    rcases hframe with ⟨hagree, _, _, _, _⟩
    let u : RationalState := (0,t.2.1,false)
    have ht : t = rationalState_relocate powerEndpointPrelude.length u := by
      apply Prod.ext
      · simpa [rationalState_relocate, powerEndpointPrelude, u] using htp
      · exact Prod.ext rfl hta
    rw [ht]
    rw [show powerEndpointCode = powerEndpointPrelude ++ powerEndpointCore.map
      (rationalInstruction_relocate powerEndpointPrelude.length) by rfl,
      rationalProgram_relocate_run]
    rw [show powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs)
      (powerEndpointRightArgs xs) + 1 =
      powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs)
        (powerEndpointRightArgs xs) + 1 by rfl, rationalProgram_run_add]
    have hcore := powerEndpointCore_before_halt
      (powerEndpointLeftArgs xs) (powerEndpointRightArgs xs) u hagree
      (by simpa [powerEndpointRightArgs] using h40)
      (by simpa [powerEndpointRightArgs] using h41)
      (by simpa [powerEndpointRightArgs] using h42)
      (by simpa [powerEndpointRightArgs] using h46)
      (by
        intro i hlo hi
        interval_cases i <;> simp [powerEndpointRightArgs])
      (by simpa [powerEndpointLeftArgs] using hb)
      (by simpa [powerEndpointRightArgs] using hb)
    dsimp only at hcore
    generalize hc : powerEndpointCore.run
      (powerEndpointCoreActiveFuel (powerEndpointLeftArgs xs) (powerEndpointRightArgs xs)) u = v
      at hcore ⊢
    rcases hcore with ⟨hvpc, hva, hvbox⟩
    have hlookup : powerEndpointCore[401]? = some .halt := by rfl
    have hstep : powerEndpointCore.run 1 v = (401,v.2.1,true) := by
      rw [show powerEndpointCore.run 1 v = powerEndpointCore.step v by rfl]
      simp [RationalProgram.step, hvpc, hva, hlookup]
    rw [hstep]
    simpa [rationalState_relocate, powerEndpointLeftArgs,
      powerEndpointRightArgs] using hvbox

set_option maxHeartbeats 1500000 in
/-- The scalar public-fuel program reaches its active final halt frame after 55 steps. [the stated conclusion](goal) holds. -/
lemma powerScalarPublicFuelCode_before_halt (xs : List ℚ) :
    let t := powerScalarPublicFuelCode.run 55 (RationalProgram.initial xs)
    t.1 = 55 ∧ t.2.2 = false ∧ t.2.1 0 = (powerScalarPublicFuel xs : ℚ) := by
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
  rw [show 55 = 36+19 by rfl, rationalProgram_run_add,
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

/-- The scalar fuel code also depends only on registers below forty. [the stated conclusion](goal) holds. -/
lemma powerScalarPublicFuelCode_below :
    ∀ op ∈ powerScalarPublicFuelCode, rationalInstructionBelow 40 op := by decide

/-- The active fuel certificate is stable under spare-register data. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hs). -/
lemma powerScalarPublicFuelCode_before_halt_frame (xs : List ℚ) (s : RationalState)
    (hs : rationalStateAgreeBelow 40 s (RationalProgram.initial xs)) :
    let t := powerScalarPublicFuelCode.run 55 s
    t.1 = 55 ∧ t.2.2 = false ∧ t.2.1 0 = (powerScalarPublicFuel xs : ℚ) := by
  have href := powerScalarPublicFuelCode_before_halt xs
  have hagree := rationalProgram_run_agree_below powerScalarPublicFuelCode 40
    powerScalarPublicFuelCode_below 55 s (RationalProgram.initial xs) hs
  dsimp only at href ⊢
  rcases hagree with ⟨hpc, hhalt, hreg⟩
  exact ⟨hpc.trans href.1, hhalt.trans href.2.1,
    (hreg 0 (by omega)).trans href.2.2⟩

/-- A common magnitude dominating both endpoint exponents. -/
def powerEndpointMagnitude (xs : List ℚ) : ℚ :=
  max |xs[2]?.getD 0| |xs[3]?.getD 0|

/-- One scalar-fuel query at the common endpoint magnitude. -/
def powerEndpointFuelArgs (xs : List ℚ) : List ℚ :=
  [xs[0]?.getD 0, xs[1]?.getD 0, powerEndpointMagnitude xs, 0]

/-- A forty-register initialization matching the transformed frame, including
irrelevant registers inherited from an arbitrary input list. -/
def powerEndpointFuelFrameArgs (xs : List ℚ) : List ℚ :=
  List.ofFn (fun i : Fin 40 =>
    if i = 2 then powerEndpointMagnitude xs else if i = 3 then 0 else xs[i]?.getD 0)
/-- [The power Endpoint Fuel Frame Args fuel result](goal) states the corresponding mathematical identity, bound, or structural property. -/

lemma powerEndpointFuelFrameArgs_fuel (xs : List ℚ) :
    powerScalarPublicFuel (powerEndpointFuelFrameArgs xs) =
      powerScalarPublicFuel (powerEndpointFuelArgs xs) := by
  simp [powerScalarPublicFuel, powerEndpointFuelFrameArgs, powerEndpointFuelArgs]

/-- Conservative public fuel for both scalar calls and their bridges. -/
def powerEndpointPublicFuel (xs : List ℚ) : ℕ :=
  90 + 2 * powerScalarPublicFuel (powerEndpointFuelArgs xs)
/-- The [power Scalar Series Bound mono abs result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:h). -/

lemma powerScalarSeriesBound_mono_abs (q b : ℕ) (v w : ℚ) (h : |v| ≤ |w|) :
    powerScalarSeriesBound q b v ≤ powerScalarSeriesBound q b w := by
  unfold powerScalarSeriesBound
  apply max_le_max_left
  apply Int.toNat_le_toNat
  apply Int.ceil_mono
  gcongr
/-- [The power Scalar Public Fuel mono abs raw result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:h). -/

lemma powerScalarPublicFuel_mono_abs_raw (q b v w : ℚ) (h : |v| ≤ |w|) :
    powerScalarPublicFuel [q,b,v,0] ≤ powerScalarPublicFuel [q,b,w,0] := by
  simp only [powerScalarPublicFuel, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]
  have hB := powerScalarSeriesBound_mono_abs
    (⌊q⌋ : ℤ).toNat (⌊b⌋ : ℤ).toNat v w h
  gcongr

/-- [Each endpoint's published scalar fuel is covered by the common-magnitude fuel. [the stated conclusion](goal) holds. -/
lemma powerScalarPublicFuel_endpoint_le (xs : List ℚ) (i : Fin 2) :
    powerScalarPublicFuel (if i = 0 then powerEndpointLeftArgs xs else powerEndpointRightArgs xs) ≤
      powerScalarPublicFuel (powerEndpointFuelArgs xs) := by
  have hm0 : |xs[2]?.getD 0| ≤ |powerEndpointMagnitude xs| := by
    have hmnonneg : 0 ≤ powerEndpointMagnitude xs :=
      (abs_nonneg _).trans (le_max_left _ _)
    rw [abs_of_nonneg hmnonneg]
    exact le_max_left _ _
  have hm1 : |xs[3]?.getD 0| ≤ |powerEndpointMagnitude xs| := by
    have hmnonneg : 0 ≤ powerEndpointMagnitude xs :=
      (abs_nonneg _).trans (le_max_left _ _)
    rw [abs_of_nonneg hmnonneg]
    exact le_max_right _ _
  fin_cases i
  · change powerScalarPublicFuel
      [xs[0]?.getD 0, xs[1]?.getD 0, xs[2]?.getD 0, 0] ≤
        powerScalarPublicFuel
          [xs[0]?.getD 0, xs[1]?.getD 0, powerEndpointMagnitude xs, 0]
    exact powerScalarPublicFuel_mono_abs_raw (xs[0]?.getD 0) (xs[1]?.getD 0)
      (xs[2]?.getD 0) (powerEndpointMagnitude xs) hm0
  · change powerScalarPublicFuel
      [xs[0]?.getD 0, xs[1]?.getD 0, xs[3]?.getD 0, 0] ≤
        powerScalarPublicFuel
          [xs[0]?.getD 0, xs[1]?.getD 0, powerEndpointMagnitude xs, 0]
    exact powerScalarPublicFuel_mono_abs_raw (xs[0]?.getD 0) (xs[1]?.getD 0)
      (xs[3]?.getD 0) (powerEndpointMagnitude xs) hm1

/-- Compute the common magnitude in register two without disturbing low inputs. -/
def powerEndpointFuelPrelude : RationalProgram :=
  [.constant 40 (-1), .mul 41 2 40, .max 2 2 41,
   .mul 41 3 40, .max 3 3 41, .max 2 2 3, .constant 3 0]

/-- Double the common scalar fuel and add all fixed bridge steps. -/
def powerEndpointFuelTail : RationalProgram :=
  [.constant 1 2, .mul 0 0 1, .constant 1 90, .add 0 0 1, .halt]

/-- Continue the scalar fuel computation into the fixed arithmetic tail. -/
def powerEndpointFuelCore : RationalProgram :=
  rationalProgram_continue powerScalarPublicFuelCode powerEndpointFuelTail

/-- A finite rational program computing the public two-endpoint fuel. -/
def powerEndpointFuelCode : RationalProgram :=
  powerEndpointFuelPrelude ++ powerEndpointFuelCore.map
    (rationalInstruction_relocate powerEndpointFuelPrelude.length)
/-- [The power Endpoint Fuel Prelude prepare result](goal) states the corresponding mathematical identity, bound, or structural property. -/

lemma powerEndpointFuelPrelude_prepare (xs : List ℚ) :
    let t := powerEndpointFuelCode.run 7 (RationalProgram.initial xs)
    t.1 = 7 ∧ t.2.2 = false ∧
      rationalStateAgreeBelow 40 (0,t.2.1,false)
        (RationalProgram.initial (powerEndpointFuelFrameArgs xs)) := by
  have habs (z : ℚ) : max z (-z) = |z| := by
    by_cases hz : 0 ≤ z
    · rw [abs_of_nonneg hz, max_eq_left (by linarith)]
    · rw [abs_of_neg (lt_of_not_ge hz), max_eq_right (by linarith)]
  norm_num [powerEndpointFuelCode, powerEndpointFuelPrelude, RationalProgram.run,
    RationalProgram.step, RationalProgram.initial, Function.update_apply,
    rationalStateAgreeBelow, powerEndpointFuelFrameArgs, powerEndpointMagnitude, habs]
  intro i hi
  interval_cases i <;> simp [RationalProgram.initial, powerEndpointFuelFrameArgs,
    Function.update_apply, habs]
/-- The [power Endpoint Fuel Core connect result states the corresponding mathematical identity, bound, or structural property](goal) Under [the stated assumptions](hyp:hp,ha). Under [the stated assumptions](hyp:ha). -/

lemma powerEndpointFuelCore_connect (s : RationalState) (hp : s.1 = 55)
    (ha : s.2.2 = false) :
    powerEndpointFuelCore.step s =
      rationalState_relocate powerScalarPublicFuelCode.length (0,s.2.1,false) := by
  have hlen : powerScalarPublicFuelCode.length = 56 := by rfl
  have hlookup : powerScalarPublicFuelCode[55]? = some .halt := by rfl
  simp only [powerEndpointFuelCore, rationalProgram_continue, RationalProgram.step,
    ha, Bool.false_eq_true, ↓reduceIte, hp, List.getElem?_append, List.length_map,
    hlen, show 55 < 56 by omega, ↓reduceIte, List.getElem?_map, hlookup,
    Option.map_some, rationalInstruction_continue, rationalState_relocate, Nat.add_zero]
/-- [The [power Endpoint Fuel Core before halt frame result](goal) states the corresponding mathematical identity, bound, or structural property. Under [the stated assumptions](hyp:hs). -/

lemma powerEndpointFuelCore_before_halt_frame (xs : List ℚ) (s : RationalState)
    (hs : rationalStateAgreeBelow 40 s
      (RationalProgram.initial (powerEndpointFuelFrameArgs xs))) :
    let t := powerEndpointFuelCore.run 55 s
    t.1 = 55 ∧ t.2.2 = false ∧
      t.2.1 0 = (powerScalarPublicFuel (powerEndpointFuelArgs xs) : ℚ) := by
  have h := powerScalarPublicFuelCode_before_halt_frame
    (powerEndpointFuelFrameArgs xs) s hs
  dsimp only at h ⊢
  have hrun := rationalProgram_continue_run powerScalarPublicFuelCode
    powerEndpointFuelTail 55 s h.2.1
  change powerEndpointFuelCore.run 55 s =
    powerScalarPublicFuelCode.run 55 s at hrun
  rw [hrun]
  simpa only [powerEndpointFuelFrameArgs_fuel] using h
/-- The [power Endpoint Fuel Core result result](goal) states the corresponding mathematical identity, bound, or structural property. Under [the stated assumptions](hyp:hs). -/

lemma powerEndpointFuelCore_result (xs : List ℚ) (s : RationalState)
    (hs : rationalStateAgreeBelow 40 s
      (RationalProgram.initial (powerEndpointFuelFrameArgs xs))) :
    let t := powerEndpointFuelCore.run 61 s
    t.2.2 = true ∧ t.2.1 0 = (powerEndpointPublicFuel xs : ℚ) := by
  rw [show 61 = 55 + 1 + 5 by rfl, rationalProgram_run_add,
    rationalProgram_run_add]
  have h := powerEndpointFuelCore_before_halt_frame xs s hs
  generalize he : powerEndpointFuelCore.run 55 s = t at h ⊢
  dsimp only at h
  rcases h with ⟨htp, hta, ht0⟩
  rw [show powerEndpointFuelCore.run 1 t = powerEndpointFuelCore.step t by rfl,
    powerEndpointFuelCore_connect t htp hta]
  rw [show powerEndpointFuelCore = rationalProgram_continue
    powerScalarPublicFuelCode powerEndpointFuelTail by rfl,
    rationalProgram_continue_tail]
  norm_num [powerEndpointFuelTail, RationalProgram.run, RationalProgram.step,
    Function.update_apply, ht0, powerEndpointPublicFuel]
  simp [rationalState_relocate, Function.update_apply]
  push_cast
  ring

set_option maxHeartbeats 2000000 in
/-- The [power Endpoint Fuel Code result result](goal) states the corresponding mathematical identity, bound, or structural property. -/
lemma powerEndpointFuelCode_result (xs : List ℚ) :
    let t := powerEndpointFuelCode.run 68 (RationalProgram.initial xs)
    t.2.2 = true ∧ t.2.1 0 = (powerEndpointPublicFuel xs : ℚ) := by
  rw [show 68 = 7 + 61 by rfl, rationalProgram_run_add]
  have hprep := powerEndpointFuelPrelude_prepare xs
  generalize hp : powerEndpointFuelCode.run 7 (RationalProgram.initial xs) = t at hprep ⊢
  dsimp only at hprep
  rcases hprep with ⟨htp, hta, hagree⟩
  let u : RationalState := (0,t.2.1,false)
  have ht : t = rationalState_relocate powerEndpointFuelPrelude.length u := by
    apply Prod.ext
    · simpa [rationalState_relocate, powerEndpointFuelPrelude, u] using htp
    · exact Prod.ext rfl hta
  rw [ht]
  rw [show powerEndpointFuelCode = powerEndpointFuelPrelude ++
    powerEndpointFuelCore.map (rationalInstruction_relocate
      powerEndpointFuelPrelude.length) by rfl, rationalProgram_relocate_run]
  dsimp only [rationalState_relocate]
  exact powerEndpointFuelCore_result xs u hagree

/-- The combined fuel is itself a public rational iteration bound. [the stated conclusion](goal) holds. -/
lemma powerEndpointPublicFuel_public : PublicIterationBound powerEndpointPublicFuel := by
  refine ⟨powerEndpointFuelCode, fun xs => ⟨68, ?_, ?_⟩⟩
  · exact (powerEndpointFuelCode_result xs).1
  · exact (powerEndpointFuelCode_result xs).2

/-- The conservative public fuel covers the exact fused run. [the stated conclusion](goal) holds. -/
lemma powerEndpointExactFuel_le_public (xs : List ℚ) :
    powerEndpointExactFuel xs ≤ powerEndpointPublicFuel xs := by
  by_cases hb : (⌊xs[1]?.getD 0⌋ : ℤ).toNat = 1
  · simp [powerEndpointExactFuel, powerEndpointPublicFuel, hb]
    omega
  · have hl := powerScalarActiveFuel_succ_le_public (powerEndpointLeftArgs xs)
    have hr := powerScalarActiveFuel_succ_le_public (powerEndpointRightArgs xs)
    have hl' := powerScalarPublicFuel_endpoint_le xs (0 : Fin 2)
    have hr' := powerScalarPublicFuel_endpoint_le xs (1 : Fin 2)
    norm_num at hl' hr'
    simp only [powerEndpointExactFuel, hb, ↓reduceIte, powerEndpointCoreActiveFuel,
      powerEndpointPublicFuel]
    simp only [powerEndpointPreludeFuel]
    split <;> omega

/-- Sufficient public fuel leaves the already halted endpoint output unchanged. [the stated conclusion](goal) holds. -/
lemma powerEndpointCode_public_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let t := powerEndpointCode.run (powerEndpointPublicFuel xs)
      (RationalProgram.initial xs)
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) =
      rationalBox (paperPowerScalar q b (xs[2]?.getD 0)).lo
        (paperPowerScalar q b (xs[3]?.getD 0)).hi := by
  have h := powerEndpointCode_result xs
  dsimp only at h
  have hf := powerEndpointExactFuel_le_public xs
  rw [show powerEndpointPublicFuel xs = powerEndpointExactFuel xs +
    (powerEndpointPublicFuel xs-powerEndpointExactFuel xs) by omega,
    rationalProgram_run_add, rationalProgram_run_halted _ _ _ h.1]
  exact h

/-- Certified bounded program for both power endpoints. -/
def powerEndpointProgram : BoundedRationalProgram where
  code := powerEndpointCode
  iterationBound := powerEndpointPublicFuel
  public_bound := powerEndpointPublicFuel_public
  halts := fun xs => (powerEndpointCode_public_result xs).1

/-- The endpoint program returns the left lower and right upper scalar endpoints. Under the stated assumptions. [The stated conclusion follows](goal). -/
lemma powerEndpointProgram_eval (q b : ℕ) (lo hi : ℚ) :
    let endpoints := powerEndpointProgram.eval [q,b,lo,hi]
    rationalBox endpoints.1 endpoints.2 =
      rationalBox (paperPowerScalar q b lo).lo (paperPowerScalar q b hi).hi := by
  have h := powerEndpointCode_public_result [(q : ℚ),b,lo,hi]
  simpa only [BoundedRationalProgram.eval, powerEndpointProgram,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Int.floor_natCast, Int.toNat_natCast] using h.2

/-- The fused endpoint program implements the concrete power engine. [the stated conclusion](goal) holds. -/
lemma concreteEngine_power_register_certificate (q b : ℕ) (I : RatInterval) :
    concreteEngine.powBox q b I =
      let endpoints := powerEndpointProgram.eval [q,b,I.lo,I.hi]
      rationalBox endpoints.1 endpoints.2 := by
  rw [powerEndpointProgram_eval]
  rfl

end CausalSmith.Stat.LogoddsLowsmoothFrontier
