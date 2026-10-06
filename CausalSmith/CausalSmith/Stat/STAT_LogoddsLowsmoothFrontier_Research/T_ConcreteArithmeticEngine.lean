module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.CosProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.ExpProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LogEnclosure
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.LogProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.MachinEnclosure
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PiProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerEnclosure
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerEndpointProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerExpFrames
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerFusion
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerLogProgram
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.PowerScalarBudget
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SeriesEnclosures
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.SqrtProgram

/-! # T ConcreteArithmeticEngine

Paper-owned scaffold obligations; proofs are filled in Stage 3. -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The scalar square-root algorithm contains the true root and has the exact dyadic width.](goal) Under [the stated assumptions](hyp:hz). -/
-- @node: paperSqrtScalar_spec
lemma paperSqrtScalar_spec (q : ℕ) (z : ℚ) (hz : 0 ≤ z) :
    (paperSqrtScalar q z).Contains (Real.sqrt z) ∧
    0 ≤ (paperSqrtScalar q z).lo ∧
    (paperSqrtScalar q z).width = rationalError (q + 3) := by
  let p := q + 3
  let N := (⌊(2 : ℚ) ^ (2 * p) * z⌋ : ℤ).toNat
  let a := paperIntegerSqrt N
  have hpow : 0 < (2 : ℚ) ^ p := by positivity
  have hfloor : 0 ≤ (⌊(2 : ℚ) ^ (2 * p) * z⌋ : ℤ) :=
    Int.floor_nonneg.mpr (by positivity)
  have hcast : (N : ℚ) = (⌊(2 : ℚ) ^ (2 * p) * z⌋ : ℤ) := by
    dsimp only [N]
    exact_mod_cast Int.toNat_of_nonneg hfloor
  have hflo := Int.floor_le ((2 : ℚ) ^ (2 * p) * z)
  have hfhi := Int.lt_floor_add_one ((2 : ℚ) ^ (2 * p) * z)
  rw [← hcast] at hflo hfhi
  obtain ⟨ha, hb⟩ := paperIntegerSqrt_spec N
  have haQ : (a : ℚ) ^ 2 ≤ (N : ℚ) := by exact_mod_cast ha
  have hbQ : (N : ℚ) + 1 ≤ ((a : ℚ) + 1) ^ 2 := by exact_mod_cast hb
  have hloSq : ((a : ℚ) / 2 ^ p) ^ 2 ≤ z := by
    rw [div_pow]
    apply (div_le_iff₀ (sq_pos_of_pos hpow)).mpr
    rw [show 2 * p = p * 2 by omega, pow_mul] at hflo
    nlinarith
  have hhiSq : z ≤ (((a : ℚ) + 1) / 2 ^ p) ^ 2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hpow)).mpr
    rw [show 2 * p = p * 2 by omega, pow_mul] at hfhi
    nlinarith
  have hord : (a : ℚ) / 2 ^ p ≤ ((a : ℚ) + 1) / 2 ^ p := by
    apply div_le_div_of_nonneg_right <;> first | positivity | linarith
  change let J := rationalBox ((a : ℚ) / 2 ^ p) (((a : ℚ) + 1) / 2 ^ p)
         J.Contains (Real.sqrt z) ∧ 0 ≤ J.lo ∧ J.width = rationalError p
  simp only [rationalBox, min_eq_left hord, max_eq_right hord,
    Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval.Contains,
    Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval.width]
  refine ⟨⟨?_, ?_⟩, by positivity, ?_⟩
  · apply Real.le_sqrt_of_sq_le
    exact_mod_cast hloSq
  · apply (Real.sqrt_le_left (by positivity)).mpr
    exact_mod_cast hhiSq
  · change ((a : ℚ) + 1) / 2 ^ p - (a : ℚ) / 2 ^ p = 1 / 2 ^ p
    ring

/-- [The rational and real precision errors represent the same dyadic number. [the stated conclusion](goal) holds. -/
-- @node: rationalError_coe
lemma rationalError_coe (q : ℕ) : (rationalError q : ℝ) = precisionError q := by
  simp [rationalError, precisionError, zpow_neg, zpow_natCast]

/-- The scalar dyadic width is below the requested primitive tolerance. Under the stated assumptions. [The stated hypotheses](hyp:hz) hold, and [the stated conclusion follows](goal). -/
-- @node: paperSqrtScalar_width_le
lemma paperSqrtScalar_width_le (q : ℕ) (z : ℚ) (hz : 0 ≤ z) :
    ((paperSqrtScalar q z).width : ℝ) ≤ precisionError q := by
  rw [(paperSqrtScalar_spec q z hz).2.2, ← rationalError_coe]
  simp only [rationalError, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  apply one_div_le_one_div_of_le (by positivity)
  gcongr <;> norm_num

/-- [Monotone endpoint extension of the certified scalar brackets satisfies the square-root contract.](goal) Under [the stated assumptions](hyp:hI). -/
-- @node: concreteEngine_sqrt_contract
lemma concreteEngine_sqrt_contract (q : ℕ)
    (I : Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval) (hI : 0 ≤ I.lo) :
    MonotoneContract Real.sqrt q I (concreteEngine.sqrtBox q I) ∧
    0 ≤ (concreteEngine.sqrtBox q I).lo := by
  have hhi : 0 ≤ I.hi := hI.trans I.lo_le_hi
  obtain ⟨hl, hl0, _⟩ := paperSqrtScalar_spec q I.lo hI
  obtain ⟨hu, _, _⟩ := paperSqrtScalar_spec q I.hi hhi
  have hlohi : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.lo_le_hi
  have horderR : ((paperSqrtScalar q I.lo).lo : ℝ) ≤ (paperSqrtScalar q I.hi).hi :=
    hl.1.trans ((Real.sqrt_le_sqrt hlohi).trans hu.2)
  have horder : (paperSqrtScalar q I.lo).lo ≤ (paperSqrtScalar q I.hi).hi := by
    exact_mod_cast horderR
  have hwl := paperSqrtScalar_width_le q I.lo hI
  have hwu := paperSqrtScalar_width_le q I.hi hhi
  simp only [Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval.width,
    Rat.cast_sub] at hwl hwu
  simp only [concreteEngine, endpointExtension, rationalBox, min_eq_left horder,
    max_eq_right horder, MonotoneContract,
    Causalean.Mathlib.Analysis.IntervalArithmetic.RatInterval.Contains]
  refine ⟨⟨?_, sub_nonneg.mpr hl.1, ?_, sub_nonneg.mpr hu.2, ?_⟩, hl0⟩
  · intro x hx
    exact ⟨hl.1.trans (Real.sqrt_le_sqrt hx.1),
      (Real.sqrt_le_sqrt hx.2).trans hu.2⟩
  · linarith [hl.2]
  · linarith [hu.1]

-- @node: lem:concrete-arithmetic-engine
/-- The literal fixed-count rational routines satisfy every primitive engine contract. [the stated conclusion](goal) holds. -/
lemma concreteEngine_admissible : ArithmeticEngine.Admissible concreteEngine := by
  refine ⟨?_, ?_, ?_, ?_, concreteEngine_sqrt_contract, ?_, ?_⟩
  · obtain ⟨power, hpower⟩ :
        ∃ power : BoundedRationalProgram,
          ∀ q b I, concreteEngine.powBox q b I =
            let v := power.eval [q, b, I.lo, I.hi]; rationalBox v.1 v.2 := by
      exact ⟨powerEndpointProgram, concreteEngine_power_register_certificate⟩
    exact concreteEngine_registers_of_other_primitives
      piRegisterProgram expRegisterProgram cosRegisterProgram logRegisterProgram power
      concreteEngine_pi_register_certificate concreteEngine_exp_register_certificate
      concreteEngine_cos_register_certificate concreteEngine_log_register_certificate hpower
  · exact paperPi_contract
  · exact concreteEngine_exp_contract
  · exact concreteEngine_log_contract
  · exact concreteEngine_power_contract
  · exact concreteEngine_cos_contract
end CausalSmith.Stat.LogoddsLowsmoothFrontier
