module
public import CausalSmith.Stat.STAT_AnnotationRarearmFrontier_Research.Helpers.Affine.NumericalSeparation
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Uniform numerical degree and rare-cell count estimates for concentration of the affine priors.
-/

public section

namespace CausalSmith.Stat.AnnotationRarearmFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

/-- [Under the stated inputs and conditions](hyp:y,hy), Half-scale exponential growth dominates the numerical linear budget above the threshold.  This gives [the stated result](goal).-/
-- @node: affine_exp_half_linear_budget
lemma affine_exp_half_linear_budget (y : Real) (hy : 4096 ≤ y) :
    180 * 2 ^ 30 * y ≤ Real.exp (y / 2) := by
  have hbase : (2 : Real) ^ 50 ≤ Real.exp (y / 4) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 2)
      Real.exp_one_gt_two.le 50
    rw [← Real.exp_nat_mul] at hp
    norm_num at hp ⊢
    exact hp.trans (Real.exp_le_exp.mpr (show (50 : Real) ≤ y / 4 by linarith))
  have hlin : y / 4 ≤ Real.exp (y / 4) := by
    linarith [Real.add_one_le_exp (y / 4)]
  have hprod := mul_le_mul hbase hlin (by linarith : 0 ≤ y / 4)
    (Real.exp_pos (y / 4)).le
  rw [← Real.exp_add] at hprod
  have hid : y / 4 + y / 4 = y / 2 := by ring
  rw [hid] at hprod
  norm_num at hprod ⊢
  nlinarith

/-- [Under the stated inputs and conditions](hyp:n,eps,hS), Above label scale two, the scheduled logarithm is within one of the ordinary logarithm.  This gives [the stated result](goal).-/
-- @node: affine_logScale_le_log_add_one
lemma affine_logScale_le_log_add_one (n : Nat) (eps : Real)
    (hS : 2 ≤ (n : Real) * eps) :
    logScale n eps ≤ Real.log ((n : Real) * eps) + 1 := by
  have hbound : Real.exp 1 + (n : Real) * eps ≤ Real.exp 1 * ((n : Real) * eps) := by
    nlinarith [Real.exp_one_gt_two]
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp 1 + (n : Real) * eps) hbound
  rw [Real.log_mul (Real.exp_pos 1).ne' (by linarith : (n : Real) * eps ≠ 0),
    Real.log_exp] at hlog
  simpa only [logScale, labelScale, add_comm] using hlog

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,m,d), Above the affine threshold the polynomial degree is bounded by ten times log S.  This gives [the stated result](goal).-/
-- @node: affine_tuning_degree_le_log
lemma affine_tuning_degree_le_log (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps) :
    4096 ≤ Real.log ((n : Real) * eps) ∧
      ((affineTuning n m d eps).L : Real) ≤ 10 * Real.log ((n : Real) * eps) := by
  have htwo : (2 : Real) ≤ (n : Real) * eps := by
    have h := Real.add_one_le_exp (4096 : Real)
    linarith
  have hy : 4096 ≤ Real.log ((n : Real) * eps) := by
    have h := Real.log_le_log (Real.exp_pos 4096) hS
    simpa only [Real.log_exp] using h
  have hell := affine_logScale_le_log_add_one n eps htwo
  have hL := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.1
  exact ⟨hy, by linarith⟩

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,m,d), The floor of the reciprocal mass budget retains at least 500 M ε L cells.  This gives [the stated result](goal).-/
-- @node: affine_tuning_floor_count_lower
lemma affine_tuning_floor_count_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps) :
    500 * (affineTuning n m d eps).M * eps * ((affineTuning n m d eps).L : Real) ≤
      (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) : Real) := by
  have hb := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.2.2.2.2.1
  have hmass := affine_tuning_floor_mass_lower n m d eps hn hd heps heps' hS
  have h := (div_le_iff₀ hb).mpr hmass
  have hid : (1 / 200 : Real) / (affineTuning n m d eps).b0 =
      500 * (affineTuning n m d eps).M * eps * ((affineTuning n m d eps).L : Real) := by
    rw [affine_tuning_b0_identity n m d eps hn hd heps heps']
    field_simp
    ring
  rw [hid] at h
  exact h

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,m), Both alphabet and floor budgets exceed the square-root-scale count in the affine regime.  This gives [the stated result](goal).-/
-- @node: affine_tuning_count_exp_lower
lemma affine_tuning_count_exp_lower (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : 1 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) :
    Real.exp (Real.log ((n : Real) * eps) / 2) *
      ((affineTuning n m d eps).L : Real) / 18 ≤
        ((affineTuning n m d eps).Kstar : Real) := by
  let S := (n : Real) * eps
  let r := Real.exp (Real.log S / 2)
  let ell := logScale n eps
  let D := ((n : Real) + m) * eps * ell
  have hSp : 0 < S := by dsimp [S]; linarith
  have hr : 0 < r := Real.exp_pos _
  have hrsq : r ^ 2 = S := by
    dsimp [r]
    rw [pow_two, ← Real.exp_add, show Real.log S / 2 + Real.log S / 2 = Real.log S by ring,
      Real.exp_log hSp]
  have hr1 : 1 ≤ r := by
    have hlog : 0 ≤ Real.log S := Real.log_nonneg hS
    exact Real.one_le_exp (by positivity)
  have hrS : r ≤ S := by nlinarith
  have hell : 1 ≤ ell := affine_logScale_one_le n eps heps.le
  have hN : S ≤ ((n : Real) + m) * eps := by
    dsimp [S]; nlinarith [Nat.cast_nonneg m (α := Real)]
  have hDp : 0 < D := by dsimp [D]; nlinarith
  have hdell : r * ell < (d : Real) := by
    by_contra h
    have hle : (d : Real) ≤ r * ell := le_of_not_gt h
    have hnum : (d : Real) * r ≤ D := by
      have ha := mul_le_mul_of_nonneg_right hle hr.le
      have hb := mul_le_mul_of_nonneg_right hN (by linarith : 0 ≤ ell)
      dsimp [D]
      nlinarith [hrsq]
    have hxle : (d : Real) / D ≤ 1 / r :=
      (div_le_div_iff₀ hDp hr).mpr (by simpa using hnum)
    have hs := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg d) hDp.le) hxle 2
    simp only [div_pow, one_pow, hrsq] at hs
    apply (not_le_of_gt hx)
    simpa only [div_pow] using hs
  have hdhalf : (d : Real) / 2 ≤ ((d - 1 : Nat) : Real) := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    have hdR : (2 : Real) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨hM, _, hLlo, hLhi, _, _, _, _⟩ :=
    affine_tuning_bounds n m d eps hn hd heps heps'
  have hL0 : 0 ≤ ((affineTuning n m d eps).L : Real) := Nat.cast_nonneg _
  have halphabet : r * ((affineTuning n m d eps).L : Real) / 18 ≤ ((d - 1 : Nat) : Real) := by
    have h := mul_le_mul_of_nonneg_left hLhi hr.le
    change _ ≤ 9 * ell at hLhi
    nlinarith
  have hMe : 128 * S ≤ (affineTuning n m d eps).M * eps := by
    have h := mul_le_mul_of_nonneg_right hM heps.le
    dsimp [S]
    nlinarith [mul_nonneg (Nat.cast_nonneg m) heps.le]
  have hcap : r * ((affineTuning n m d eps).L : Real) / 18 ≤
      (Nat.floor (1 / (100 * (affineTuning n m d eps).b0)) : Real) := by
    have hf := affine_tuning_floor_count_lower n m d eps hn hd heps heps' hS
    have ha := mul_le_mul_of_nonneg_right hMe hL0
    have hb := mul_le_mul_of_nonneg_right hrS hL0
    nlinarith
  change r * ((affineTuning n m d eps).L : Real) / 18 ≤
    ((min (d - 1) (Nat.floor (1 / (100 * (affineTuning n m d eps).b0))) : Nat) : Real)
  rw [Nat.cast_min]
  exact le_min halphabet hcap

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,m), The scheduled cell count dominates the entire degree-dependent concentration budget.  This gives [the stated result](goal).-/
-- @node: affine_tuning_count_concentration_budget
lemma affine_tuning_count_concentration_budget (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2) :
    2 ^ 30 * (1 + eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2) ≤
      ((affineTuning n m d eps).Kstar : Real) := by
  obtain ⟨hy, hLhi⟩ := affine_tuning_degree_le_log n m d eps hn hd heps heps' hS
  have hS1 : 1 ≤ (n : Real) * eps := by
    linarith [Real.add_one_le_exp (4096 : Real)]
  have hK := affine_tuning_count_exp_lower n m d eps hn hd heps heps' hS1 hx
  have hexp := affine_exp_half_linear_budget (Real.log ((n : Real) * eps)) hy
  have hLlo := (affine_tuning_bounds n m d eps hn hd heps heps').2.2.1
  have hell := affine_logScale_one_le n eps heps.le
  have hL : (8 : Real) ≤ (affineTuning n m d eps).L := by linarith
  have hprod := mul_le_mul_of_nonneg_right hexp
    (show 0 ≤ ((affineTuning n m d eps).L : Real) by positivity)
  have hKstrong : 10 * 2 ^ 30 * Real.log ((n : Real) * eps) *
      ((affineTuning n m d eps).L : Real) ≤ ((affineTuning n m d eps).Kstar : Real) := by
    nlinarith
  have hepssq : eps ^ 2 ≤ (1 / 16 : Real) := by
    have h := pow_le_pow_left₀ heps.le heps' 2
    norm_num at h
    exact h
  have hdegree := mul_le_mul_of_nonneg_right hLhi
    (show 0 ≤ ((affineTuning n m d eps).L : Real) by positivity)
  have hweight := mul_le_mul_of_nonneg_right hepssq
    (sq_nonneg ((affineTuning n m d eps).L : Real))
  have hunit : 1 ≤ Real.log ((n : Real) * eps) * ((affineTuning n m d eps).L : Real) := by
    nlinarith
  have hbudget : 1 + eps ^ 2 * ((affineTuning n m d eps).L : Real) ^ 2 ≤
      10 * Real.log ((n : Real) * eps) * ((affineTuning n m d eps).L : Real) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : Real) ≤ 2 ^ 30)
  nlinarith

/-- [Under the stated inputs and conditions](hyp:eps,hn,hd,heps,heps',hS,n,hx,d,sigma,hyp,m), Each normalized affine target has bad-event probability at most 1/128.  This gives [the stated result](goal).-/
-- @node: affine_normalized_target_tail_small
lemma affine_normalized_target_tail_small (n m d : Nat) (eps : Real)
    (hn : 1 ≤ n) (hd : 2 ≤ d) (heps : 0 < eps) (heps' : eps ≤ 1 / 4)
    (hS : Real.exp 4096 ≤ (n : Real) * eps)
    (hx : 1 / ((n : Real) * eps) <
      ((d : Real) / (((n : Real) + m) * eps * logScale n eps)) ^ 2)
    (sigma : ConeDual (affineTuning n m d eps).L (affineTuning n m d eps).B eps) (hyp : Bool) :
    let nu := Measure.pi (fun _ : Fin (affineTuning n m d eps).Kstar => (latentPMF sigma).toMeasure)
    let t := fun i => ∫ lat, affineRawTarget n m d eps sigma i lat ∂nu
    let gap := t true - t false
    nu.real {lat | gap / 8 ≤ |ateFunctional (normalizedLaw hyp n m d eps hd sigma lat) - t hyp|} ≤
      1 / 128 := by
  intro nu t gap
  have hS1 : 1 ≤ (n : Real) * eps := by
    linarith [Real.add_one_le_exp (4096 : Real)]
  have htail := affine_normalized_target_gap_tail n m d eps hn hd heps heps' hS1 sigma hyp
  change nu.real _ ≤ _ at htail
  refine htail.trans ?_
  have hK := affine_tuning_count_concentration_budget n m d eps hn hd heps heps' hS hx
  have hKp : (0 : Real) < (affineTuning n m d eps).Kstar := by
    exact_mod_cast affine_tuning_Kstar_pos n m d eps hn hd heps heps' hS1
  apply (div_le_iff₀ hKp).mpr
  norm_num at hK ⊢
  linarith

end CausalSmith.Stat.AnnotationRarearmFrontier
