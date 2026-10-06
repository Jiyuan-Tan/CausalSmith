module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.EngineRoutines
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Certificates for the prescribed logarithm truncation

The finite geometric remainder, public rational range bound and exponential
comparison certify the literal atanh sum at its fixed truncation count.
Monotonicity then gives the primitive interval contract.
-/
public section
noncomputable section
open Causalean.Mathlib.Analysis.IntervalArithmetic
open scoped BigOperators
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [The public logarithm range bounds both the argument and its reciprocal. [the stated conclusion](goal) holds. -/
-- @node: logRangeBound_spec
lemma logRangeBound_spec (z : ℚ) :
    2 ≤ logRangeBound z ∧ z ≤ (logRangeBound z : ℚ) ∧
    1/z ≤ (logRangeBound z : ℚ) := by
  have hc (x : ℚ) : x ≤ ((⌈x⌉ : ℤ).toNat : ℚ) := by
    exact (Int.le_ceil x).trans (by exact_mod_cast Int.self_le_toNat (⌈x⌉ : ℤ))
  refine ⟨le_max_left _ _, ?_, ?_⟩
  · exact (hc z).trans (by exact_mod_cast (le_max_left _ _).trans (le_max_right 2 _))
  · exact (hc (1/z)).trans (by exact_mod_cast (le_max_right _ _).trans (le_max_right 2 _))

/-- The atanh coordinate has the range and denominator bounds used by the roadmap. Under the stated assumptions. [The stated hypotheses](hyp:hz,hB,hzu,hzl) hold, and [the stated conclusion follows](goal). -/
-- @node: log_coordinate_bounds
lemma log_coordinate_bounds (z B : ℝ) (hz : 0 < z) (hB : 2 ≤ B)
    (hzu : z ≤ B) (hzl : 1 / z ≤ B) :
    |(z-1)/(z+1)| ≤ (B-1)/(B+1) ∧
    1/B ≤ 1-((z-1)/(z+1))^2 := by
  have hBp : 0 < B := by linarith
  have hden : 0 < z+1 := by linarith
  have hdenB : 0 < B+1 := by linarith
  have hlow : 1 ≤ B*z := (div_le_iff₀ hz).mp hzl
  have hab : |(z-1)/(z+1)| ≤ (B-1)/(B+1) := by
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ hden).mpr
      rw [← neg_div, div_mul_eq_mul_div]
      apply (div_le_iff₀ hdenB).mpr
      nlinarith
    · apply (div_le_iff₀ hden).mpr
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hdenB).mpr
      nlinarith
  refine ⟨hab, ?_⟩
  have hr0 : 0 ≤ (B-1)/(B+1) := div_nonneg (by linarith) hdenB.le
  have hs := pow_le_pow_left₀ (abs_nonneg ((z-1)/(z+1))) hab 2
  rw [sq_abs] at hs
  have hh : 1/B ≤ 1-((B-1)/(B+1))^2 := by
    apply (div_le_iff₀ hBp).mpr
    field_simp
    nlinarith
  linarith

/-- [The exponential comparison makes a full public block decay by a dyadic factor.](goal) Under [the stated assumptions](hyp:hB). Under [the stated assumptions](hyp:hv). -/
-- @node: log_coordinate_power_bound
lemma log_coordinate_power_bound (B L : ℕ) (hB : 2 ≤ B) (v : ℝ)
    (hv : |v| ≤ ((B : ℝ) - 1) / (B + 1)) :
    |v| ^ (2*(B*L)+1) ≤ (1/2 : ℝ)^L := by
  have hBp : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hB1 : (0 : ℝ) < (B : ℝ)+1 := by positivity
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have hv1 : |v| ≤ 1-1/(B : ℝ) := by
    have hh : ((B : ℝ) - 1) / (B + 1) ≤ 1-1/(B : ℝ) := by
      apply (div_le_iff₀ hB1).mpr
      field_simp
      nlinarith
    exact hv.trans hh
  have he : |v| ≤ Real.exp (-(1/(B : ℝ))) :=
    hv1.trans (Real.one_sub_le_exp_neg _)
  have hp := pow_le_pow_left₀ (abs_nonneg v) he (2*(B*L)+1)
  rw [← Real.exp_nat_mul] at hp
  have hexp : ((2*(B*L)+1 : ℕ) : ℝ) * (-(1/(B : ℝ))) ≤ -(L : ℝ) := by
    push_cast
    field_simp
    nlinarith
  have hhalf : Real.exp (-1 : ℝ) ≤ 1/2 := by
    rw [Real.exp_neg]
    rw [one_div]
    apply (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc
    |v| ^ (2*(B*L)+1) ≤ Real.exp (((2*(B*L)+1 : ℕ) : ℝ)*(-(1/(B : ℝ)))) := hp
    _ ≤ Real.exp (-(L : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = Real.exp (-1 : ℝ)^L := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ (1/2 : ℝ)^L := pow_le_pow_left₀ (Real.exp_pos _).le hhalf L

/-- [The prescribed integer count absorbs the range factor in the geometric tail. [the stated conclusion](goal) holds. -/
-- @node: log_tail_budget
lemma log_tail_budget (q B : ℕ) :
    2*(B : ℝ)*(1/2 : ℝ)^(q+3+Nat.clog 2 (8*B)+2) ≤
      (rationalError (q+3) : ℝ) := by
  have hclog : (8*B : ℝ) ≤ (2 : ℝ)^Nat.clog 2 (8*B) := by
    exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < (2 : ℕ)) (8*B)
  simp only [rationalError, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat]
  rw [one_div_pow, pow_add, pow_add]
  have hpow : 0 < (2 : ℝ)^Nat.clog 2 (8*B) := by positivity
  have hq : 0 < (2 : ℝ)^(q+3) := by positivity
  field_simp
  nlinarith

/-- The finite geometric remainder certifies the literal logarithm polynomial. Under the stated assumptions. [The stated hypotheses](hyp:hz) hold, and [the stated conclusion follows](goal). -/
-- @node: logPolynomial_error
lemma logPolynomial_error (q : ℕ) (z : ℚ) (hz : 0 < z) :
    |Real.log z - (logPolynomial q z : ℝ)| ≤ (rationalError (q+3) : ℝ) := by
  let B := logRangeBound z
  let L := q+3+Nat.clog 2 (8*B)+2
  let v : ℝ := ((z : ℝ)-1)/(z+1)
  obtain ⟨hB, hzu, hzl⟩ := logRangeBound_spec z
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  have hBr : (2 : ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hv, hd⟩ := log_coordinate_bounds (z : ℝ) B hzR hBr
    (by exact_mod_cast hzu) (by exact_mod_cast hzl)
  have hBp : (0 : ℝ) < B := by linarith
  have hvlt : |v| < 1 := by
    apply lt_of_le_of_lt hv
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < B+1)).mpr
    linarith
  have hdiv : (1+v)/(1-v) = (z : ℝ) := by
    dsimp [v]
    field_simp
    ring
  have hrem := Real.sum_range_sub_log_div_le hvlt (B*L)
  rw [hdiv] at hrem
  have hpoly : (logPolynomial q z : ℝ) =
      2*∑ j ∈ Finset.range (B*L), v^(2*j+1)/(2*(j : ℝ)+1) := by
    simp only [logPolynomial]
    push_cast
    rfl
  have heq : Real.log z - (logPolynomial q z : ℝ) =
      2*(1/2*Real.log z - ∑ j ∈ Finset.range (B*L), v^(2*j+1)/(2*(j : ℝ)+1)) := by
    rw [hpoly]
    ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hp := log_coordinate_power_bound B L hB v hv
  have hden : 0 < 1-v^2 := lt_of_lt_of_le (by positivity : (0 : ℝ) < 1/B) hd
  calc
    2*|1/2*Real.log z - ∑ j ∈ Finset.range (B*L), v^(2*j+1)/(2*(j : ℝ)+1)| ≤
        2*(|v|^(2*(B*L)+1)/(1-v^2)) := by
          exact mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ ≤ 2*((1/2 : ℝ)^L/(1/B)) := by gcongr
    _ = 2*(B : ℝ)*(1/2 : ℝ)^L := by field_simp
    _ ≤ (rationalError (q+3) : ℝ) := log_tail_budget q B

/-- [The symmetric scalar bracket contains the logarithm with the requested endpoint excess.](goal) Under [the stated assumptions](hyp:hz). -/
-- @node: paperLogScalar_spec
lemma paperLogScalar_spec (q : ℕ) (z : ℚ) (hz : 0 < z) :
    (paperLogScalar q z).Contains (Real.log z) ∧
    Real.log z - (paperLogScalar q z).lo ≤ precisionError q ∧
    (paperLogScalar q z).hi - Real.log z ≤ precisionError q := by
  obtain ⟨hl, hu⟩ := abs_le.mp (logPolynomial_error q z hz)
  have he0 : 0 ≤ rationalError (q+3) := by unfold rationalError; positivity
  have hord : logPolynomial q z-rationalError (q+3) ≤
      logPolynomial q z+rationalError (q+3) := by linarith
  have herr : 2*(rationalError (q+3) : ℝ) ≤ precisionError q := by
    simp only [rationalError, precisionError, Rat.cast_div, Rat.cast_one,
      Rat.cast_pow, Rat.cast_ofNat, zpow_neg, zpow_natCast]
    rw [pow_add]
    have hp : 0 < (2 : ℝ)^q := by positivity
    field_simp
    norm_num
  simp only [paperLogScalar, if_pos hz, rationalBox, min_eq_left hord,
    max_eq_right hord, RatInterval.Contains, Rat.cast_sub, Rat.cast_add]
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- [Monotonicity extends the certified logarithm brackets to positive rational intervals.](goal) Under [the stated assumptions](hyp:hI). -/
-- @node: concreteEngine_log_contract
lemma concreteEngine_log_contract (q : ℕ) (I : RatInterval) (hI : 0 < I.lo) :
    MonotoneContract Real.log q I (concreteEngine.logBox q I) := by
  have hhi : 0 < I.hi := hI.trans_le I.lo_le_hi
  obtain ⟨hl, hle, hlu⟩ := paperLogScalar_spec q I.lo hI
  obtain ⟨hu, hue, huu⟩ := paperLogScalar_spec q I.hi hhi
  have hIlo : (0 : ℝ) < I.lo := by exact_mod_cast hI
  have horderR : ((paperLogScalar q I.lo).lo : ℝ) ≤ (paperLogScalar q I.hi).hi :=
    hl.1.trans ((Real.log_le_log hIlo (by exact_mod_cast I.lo_le_hi)).trans hu.2)
  have horder : (paperLogScalar q I.lo).lo ≤ (paperLogScalar q I.hi).hi := by
    exact_mod_cast horderR
  simp only [concreteEngine, endpointExtension, rationalBox, min_eq_left horder,
    max_eq_right horder, MonotoneContract, RatInterval.Contains]
  refine ⟨?_, sub_nonneg.mpr hl.1, hle, sub_nonneg.mpr hu.2, huu⟩
  intro x hx
  exact ⟨hl.1.trans (Real.log_le_log hIlo hx.1),
    (Real.log_le_log (hIlo.trans_le hx.1) hx.2).trans hu.2⟩

end CausalSmith.Stat.LogoddsLowsmoothFrontier
