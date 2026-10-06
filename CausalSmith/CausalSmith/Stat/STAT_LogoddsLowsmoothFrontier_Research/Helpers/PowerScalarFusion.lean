module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerFusion
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerLogProgram

/-! # Joining logarithm evaluation with the scalar power continuation

The logarithm reaches an active final frame with its midpoint and power inputs.
Replacing its halt by a jump executes the exponential and clipping instructions
in the same register machine and yields the prescribed scalar power bracket.
-/
@[expose] public section
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The logarithm exit reaches the active halt instruction with the complete power frame.](goal) Under [the stated assumptions](hyp:hi,h). -/
-- @node: powerLogCode_before_halt_exit
lemma powerLogCode_before_halt_exit (p b j : ℕ) (lo hi : ℚ) (s : RationalState)
    (h : PowerLogInvariant p b j 0 lo hi s) :
    let S := 2*∑ i ∈ Finset.range j,
      (((b : ℚ)-1)/((b : ℚ)+1))^(2*i+1)/(2*i+1 : ℕ)
    let t := powerLogCode.run (if 0 < b then 8 else 7) s
    t.1 = 51 ∧ t.2.2 = false ∧ t.2.1 0 = p ∧ t.2.1 1 = (if 0 < b then S else 0) ∧
      t.2.1 2 = b ∧ t.2.1 3 = lo ∧ t.2.1 4 = hi := by
  rcases h with ⟨hp, ha, hc, hi', hz, ht, hs, hb, h1, h2, hr, h0, hq, hl, hu, hb'⟩
  by_cases hpos : 0 < b
  · have hn : ¬ s.2.1 7 ≤ s.2.1 12 := by
      rw [hb, h0]; exact not_le.mpr (by exact_mod_cast hpos)
    rw [h0] at hn
    generalize he : powerLogCode.run (if 0 < b then 8 else 7) s = t
    norm_num [hpos, powerLogCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, h0, hn] at he
    subst t
    norm_num [Function.update_apply, hs, h2, hq, hl, hu, hb', hpos]
    ring
  · have hn : s.2.1 7 ≤ s.2.1 12 := by
      rw [hb, h0]; exact_mod_cast (le_of_not_gt hpos)
    rw [h0] at hn
    generalize he : powerLogCode.run (if 0 < b then 8 else 7) s = t
    norm_num [hpos, powerLogCode, RationalProgram.run, RationalProgram.step,
      Function.update_apply, hp, ha, hc, h0, hn] at he
    subst t
    norm_num [Function.update_apply, hs, h2, hq, hl, hu, hb', hpos]

/-- [Every logarithm term is evaluated before reaching the active final frame.](goal) Under [the stated assumptions](hyp:hi,h). -/
-- @node: powerLogCode_before_halt_loop
lemma powerLogCode_before_halt_loop (p b j N : ℕ) (lo hi : ℚ) (s : RationalState)
    (h : PowerLogInvariant p b j N lo hi s) :
    let S := 2*∑ i ∈ Finset.range (j+N),
      (((b : ℚ)-1)/((b : ℚ)+1))^(2*i+1)/(2*i+1 : ℕ)
    let t := powerLogCode.run (7*N+(if 0 < b then 8 else 7)) s
    t.1 = 51 ∧ t.2.2 = false ∧ t.2.1 0 = p ∧ t.2.1 1 = (if 0 < b then S else 0) ∧
      t.2.1 2 = b ∧ t.2.1 3 = lo ∧ t.2.1 4 = hi := by
  induction N generalizing j s with
  | zero => simpa using powerLogCode_before_halt_exit p b j lo hi s h
  | succ N ih =>
    rw [show 7*(N+1)+(if 0 < b then 8 else 7) = 7+(7*N+(if 0 < b then 8 else 7)) by omega, rationalProgram_run_add]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (j+1) _ (powerLogCode_round p b j N lo hi s h)

/-- [The logarithm midpoint and both exponents are ready before the final halt. [the stated conclusion](goal) holds. -/
-- @node: powerLogCode_before_halt
lemma powerLogCode_before_halt (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let p := powerRegisterPrecision q b
    let L := paperLogScalar p b
    let t := powerLogCode.run (powerLogFuel xs-(if 0 < b then 1 else 2)) (RationalProgram.initial xs)
    t.1 = 51 ∧ t.2.2 = false ∧ t.2.1 0 = p ∧ t.2.1 1 = (L.lo+L.hi)/2 ∧
      t.2.1 2 = b ∧ t.2.1 3 = xs[2]?.getD 0 ∧ t.2.1 4 = xs[3]?.getD 0 := by
  have h := powerLogCode_before_halt_loop _ _ 0 _ _ _ _ (powerLogCode_initial xs)
  dsimp only [powerLogFuel]
  rw [show ∀ N : ℕ, 45+7*N-(if 0 < (⌊xs[1]?.getD 0⌋ : ℤ).toNat then 1 else 2) =
    36+(7*N+(if 0 < (⌊xs[1]?.getD 0⌋ : ℤ).toNat then 8 else 7)) by intro N; split <;> omega, rationalProgram_run_add]
  simpa only [zero_add, paperLogScalar_midpoint, logPolynomial,
    Nat.cast_pos] using h


/-- Exact active-prefix length, including the shorter totalized zero-base branch. -/
-- @node: powerLogActiveFuel
def powerLogActiveFuel (xs : List ℚ) : ℕ :=
  powerLogFuel xs-(if 0 < (⌊xs[1]?.getD 0⌋ : ℤ).toNat then 1 else 2)

/-- The logarithm and exponential-to-clipping code form one literal instruction list. -/
-- @node: powerScalarCode
def powerScalarCode : RationalProgram :=
  rationalProgram_continue powerLogCode powerExpClipCode

/-- The active logarithm halt jumps directly to the relocated power continuation. Under the stated assumptions. [The stated hypotheses](hyp:hp,ha) hold, and [the stated conclusion follows](goal). -/
-- @node: powerScalarCode_connect
lemma powerScalarCode_connect (s : RationalState) (hp : s.1 = 51)
    (ha : s.2.2 = false) :
    powerScalarCode.step s = rationalState_relocate powerLogCode.length (0,s.2.1,false) := by
  have hlen : powerLogCode.length = 52 := by rfl
  have hlookup : powerLogCode[51]? = some .halt := by rfl
  simp only [powerScalarCode, rationalProgram_continue, RationalProgram.step,
    ha, Bool.false_eq_true, ↓reduceIte, hp, List.getElem?_append, List.length_map,
    hlen, show 51 < 52 by omega, ↓reduceIte, List.getElem?_map, hlookup,
    Option.map_some, rationalInstruction_continue, rationalState_relocate, Nat.add_zero]

/-- Exact step count of the joined scalar computation on arbitrary rational inputs. -/
-- @node: powerScalarFuel
def powerScalarFuel (xs : List ℚ) : ℕ :=
  let t := powerLogCode.run (powerLogActiveFuel xs) (RationalProgram.initial xs)
  powerLogActiveFuel xs+1+powerExpClipFuel (0,t.2.1,false)

/-- The fused literal program halts and returns the specified clipped scalar bracket.
The logarithm and exponential contracts here are evaluation identities, not assumptions. [the documented result](goal) -/
-- @node: powerScalarCode_result
lemma powerScalarCode_result (xs : List ℚ) :
    let q := (⌊xs[0]?.getD 0⌋ : ℤ).toNat
    let b := (⌊xs[1]?.getD 0⌋ : ℤ).toNat
    let v := xs[2]?.getD 0
    let t := powerScalarCode.run (powerScalarFuel xs) (RationalProgram.initial xs)
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) = paperPowerScalar q b v := by
  have h := powerLogCode_before_halt xs
  dsimp only at h
  rw [← powerLogActiveFuel] at h
  dsimp only [powerScalarFuel]
  rw [rationalProgram_run_add, rationalProgram_run_add]
  have hrun := rationalProgram_continue_run powerLogCode powerExpClipCode
    (powerLogActiveFuel xs) (RationalProgram.initial xs) h.2.1
  change powerScalarCode.run _ _ = _ at hrun
  rw [hrun]
  generalize he : powerLogCode.run (powerLogActiveFuel xs) (RationalProgram.initial xs) = t at h ⊢
  obtain ⟨htp, hta, hq, hmid, hb, hv, hright⟩ := h
  rw [show powerScalarCode.run 1 t = powerScalarCode.step t by rfl,
    powerScalarCode_connect t htp hta]
  rw [show powerScalarCode = rationalProgram_continue powerLogCode powerExpClipCode by rfl,
    rationalProgram_continue_tail]
  have hout := powerExpClipCode_result (0,t.2.1,false) rfl rfl
  dsimp only at hout
  simp only [hq, hmid, hb, hv, Int.floor_natCast, Int.toNat_natCast] at hout
  dsimp only [rationalState_relocate]
  generalize ht : powerExpClipCode.run (powerExpClipFuel (0,t.2.1,false))
    (0,t.2.1,false) = u at hout ⊢
  refine ⟨hout.1, ?_⟩
  rw [hout.2]
  exact (paperPowerScalar_eq_powerClipBox _ _ _).symm

/-- Natural precision and base inputs recover the exact paper scalar formula. [the stated conclusion](goal) holds. -/
-- @node: powerScalarCode_certificate
lemma powerScalarCode_certificate (q b : ℕ) (v w : ℚ) :
    let t := powerScalarCode.run (powerScalarFuel [q,b,v,w])
      (RationalProgram.initial [q,b,v,w])
    t.2.2 = true ∧ rationalBox (t.2.1 0) (t.2.1 1) = paperPowerScalar q b v := by
  simpa only [List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some, Int.floor_natCast, Int.toNat_natCast] using
    powerScalarCode_result [(q : ℚ),b,v,w]

end CausalSmith.Stat.LogoddsLowsmoothFrontier
