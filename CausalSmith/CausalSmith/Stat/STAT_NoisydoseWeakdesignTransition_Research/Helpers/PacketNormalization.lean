module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.CitedGates

/-! Endpoint Gamma identities and uniform spectral power comparisons for (P2)--(P3). -/
public section
set_option linter.style.whitespace false
set_option linter.style.longLine false
noncomputable section
open Filter Set
open Causalean.Mathlib.Analysis.SpecialFunctions.Jacobi
open Polynomial
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Standard Jacobi endpoint evaluation inherited from the shifted Vandermonde identity. [Under the stated conditions](hyp:ha). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_neg_one
lemma stdJacobi_neg_one (a b : ℝ) (ha : -1/2 < a) (j : ℕ) :
    stdJacobi a b j (-1) = (-1 : ℝ)^j * rising (b+1) j / (j.factorial : ℝ) := by
  rw [stdJacobi]
  norm_num only
  rw [jacobiShifted_one j a b (by linarith)]
  have hr : rising (a+1) j ≠ 0 := ne_of_gt (rising_pos _ _ (by linarith))
  field_simp
/-- A Jacobi endpoint value is nonzero for the positive rising-factorial parameters. [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_neg_one_ne_zero
lemma stdJacobi_neg_one_ne_zero (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (j : ℕ) :
    stdJacobi a b j (-1) ≠ 0 := by
  rw [stdJacobi_neg_one a b ha j]
  exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
    (ne_of_gt (rising_pos _ _ (by linarith)))) (by positivity)
/-- The Gamma recurrence represents every positive-start rising factorial,
including the negative Jacobi shape parameters permitted in the endpoint construction. [Under the stated conditions](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: rising_eq_gamma_ratio_positive_start
lemma rising_eq_gamma_ratio_positive_start (x : ℝ) (hx : 0 < x) (j : ℕ) :
    rising x j = Real.Gamma (x+j) / Real.Gamma x := by
  have hg : Real.Gamma x ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hx)
  induction j with
  | zero => simp [rising, hg]
  | succ j ih =>
    rw [rising, ascPochhammer_succ_eval]
    change rising x j * (x+j) = _
    rw [ih]
    have hp : x+(j : ℝ) ≠ 0 := by positivity
    have he : x+((j+1 : ℕ) : ℝ) = (x+j)+1 := by push_cast; ring
    rw [he, Real.Gamma_add_one hp]
    ring

/-- The endpoint evaluation in (P2), with all Gamma denominators positive. [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). -/
-- @node: stdJacobi_neg_one_gamma
lemma stdJacobi_neg_one_gamma (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (j : ℕ) :
    stdJacobi a b j (-1) = (-1 : ℝ)^j *
      Real.Gamma (j+b+1) / (Real.Gamma (b+1) * Real.Gamma (j+1)) := by
  rw [stdJacobi_neg_one a b ha j,
    rising_eq_gamma_ratio_positive_start (b+1) (by linarith)]
  rw [show b+1+(j : ℝ) = j+b+1 by ring, ← Real.Gamma_nat_eq_factorial]
  ring

/-- Positive finite initial terms can be absorbed into uniform power-comparison constants. [Under the stated conditions](hyp:f,hf,htail). [This is the stated conclusion](goal). -/
-- @node: positive_sequence_extend_power_bounds
lemma positive_sequence_extend_power_bounds (f : ℕ → ℝ) (p : ℝ)
    (hf : ∀ j : ℕ, 1 ≤ j → 0 < f j) (N : ℕ)
    (htail : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ j : ℕ, N ≤ j → 1 ≤ j → c*(j : ℝ)^p ≤ f j ∧ f j ≤ C*(j : ℝ)^p) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ j : ℕ, 1 ≤ j → c*(j : ℝ)^p ≤ f j ∧ f j ≤ C*(j : ℝ)^p := by
  induction N with
  | zero =>
    obtain ⟨c, C, hc, hC, h⟩ := htail
    exact ⟨c, C, hc, hC, fun j hj => h j (Nat.zero_le j) hj⟩
  | succ N ih =>
    apply ih
    obtain ⟨c, C, hc, hC, h⟩ := htail
    by_cases hN : 1 ≤ N
    · have hp : 0 < (N : ℝ)^p := Real.rpow_pos_of_pos (by exact_mod_cast hN) p
      let r := f N / (N : ℝ)^p
      have hr : 0 < r := div_pos (hf N hN) hp
      refine ⟨min c r, max C r, lt_min hc hr, lt_of_lt_of_le hC (le_max_left _ _), ?_⟩
      intro j hj hj1
      by_cases he : j = N
      · subst j
        have heq : r*(N : ℝ)^p = f N := div_mul_cancel₀ _ hp.ne'
        constructor
        · calc
            min c r * (N : ℝ)^p ≤ r*(N : ℝ)^p :=
              mul_le_mul_of_nonneg_right (min_le_right _ _) hp.le
            _ = f N := heq
        · calc
            f N = r*(N : ℝ)^p := heq.symm
            _ ≤ max C r * (N : ℝ)^p :=
              mul_le_mul_of_nonneg_right (le_max_right _ _) hp.le
      · obtain ⟨hl, hu⟩ := h j (by omega) hj1
        exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.rpow_nonneg (by positivity) p)).trans hl,
          hu.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) p))⟩
    · refine ⟨c, C, hc, hC, ?_⟩
      intro j hj hj1
      exact h j (by omega) hj1

/-- The cited Gamma asymptotic gives two-sided power bounds at every positive integer,
with the finite initial segment included rather than discarded. [Under the stated conditions](hyp:hGamma,hs,ht). [This is the stated conclusion](goal). -/
-- @node: gamma_ratio_integer_power_bounds
lemma gamma_ratio_integer_power_bounds (hGamma : GammaRatioAsymptotic)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      c*(j : ℝ)^(s-t) ≤ Real.Gamma (j+s)/Real.Gamma (j+t) ∧
      Real.Gamma (j+s)/Real.Gamma (j+t) ≤ C*(j : ℝ)^(s-t) := by
  have hlim := (hGamma s t).comp tendsto_natCast_atTop_atTop
  have hlow := hlim.eventually (eventually_gt_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hupp := hlim.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))
  obtain ⟨N, hN⟩ := (hlow.and hupp).exists_forall_of_atTop
  refine positive_sequence_extend_power_bounds
    (fun j => Real.Gamma (j+s)/Real.Gamma (j+t)) (s-t) ?_ N ?_
  · intro j hj
    exact div_pos (Real.Gamma_pos_of_pos (by positivity))
      (Real.Gamma_pos_of_pos (by positivity))
  · refine ⟨1/2, 2, by norm_num, by norm_num, ?_⟩
    intro j hj hj1
    obtain ⟨hl, hu⟩ := hN j hj
    have hp : 0 < (j : ℝ)^(s-t) := Real.rpow_pos_of_pos (by exact_mod_cast hj1) _
    exact ⟨(le_div_iff₀ hp).mp hl.le, (div_le_iff₀ hp).mp hu.le⟩

/-- Dividing the squared endpoint value by its norm cancels two Gamma factors.
This is the spectral coefficient used in the normalization sum (P3). [Under the stated conditions](hyp:hNorm,ha,hb). [This is the stated conclusion](goal). -/
-- @node: jacobi_endpoint_spectral_gamma
lemma jacobi_endpoint_spectral_gamma (hNorm : JacobiNormOrthogonality)
    (a b : ℝ) (ha : -1/2 < a) (hb : -1/2 < b) (j : ℕ) :
    (stdJacobi a b j (-1))^2 / jacobiSqNorm a b j =
      (2*j+a+b+1) / ((2 : ℝ)^(a+b+1) * (Real.Gamma (b+1))^2) *
      (Real.Gamma (j+b+1) / Real.Gamma (j+1)) *
      (Real.Gamma (j+a+b+1) / Real.Gamma (j+a+1)) := by
  rw [stdJacobi_neg_one_gamma a b ha hb j, (hNorm a b ha hb j).2.2]
  have hg0 : Real.Gamma (b+1) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  have hg1 : Real.Gamma (j+1) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hg2 : Real.Gamma (j+a+1) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
  have hg3 : Real.Gamma (j+b+1) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
  have hg4 : Real.Gamma (j+a+b+1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by have := Nat.cast_nonneg (α := ℝ) j; linarith))
  have hd : (2 : ℝ)*j+a+b+1 ≠ 0 := by have := Nat.cast_nonneg (α := ℝ) j; linarith
  have hp : (2 : ℝ)^(a+b+1) ≠ 0 := by positivity
  have hsign : ((-1 : ℝ)^j)^2 = 1 := by rw [← pow_mul, mul_comm j 2, pow_mul]; simp
  field_simp [hg0, hg1, hg2, hg3, hg4, hd, hp]
  nlinarith [hsign]

/-- Each endpoint spectral coefficient has the exact power-law order needed in (P3),
uniformly over all positive degrees, including the finite initial segment. [Under the stated conditions](hyp:hNorm,hGamma,hb). [This is the stated conclusion](goal). -/
-- @node: jacobi_endpoint_spectral_power_bounds
lemma jacobi_endpoint_spectral_power_bounds (hNorm : JacobiNormOrthogonality)
    (hGamma : GammaRatioAsymptotic) (b : ℝ) (hb : -1/2 < b) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      c*(j : ℝ)^(2*b+1) ≤ (stdJacobi 4 b j (-1))^2 / jacobiSqNorm 4 b j ∧
      (stdJacobi 4 b j (-1))^2 / jacobiSqNorm 4 b j ≤ C*(j : ℝ)^(2*b+1) := by
  obtain ⟨c1, C1, hc1, hC1, h1⟩ :=
    gamma_ratio_integer_power_bounds hGamma (b+1) 1 (by linarith) (by norm_num)
  obtain ⟨c2, C2, hc2, hC2, h2⟩ :=
    gamma_ratio_integer_power_bounds hGamma (4+b+1) (4+1) (by linarith) (by norm_num)
  let D := (2 : ℝ)^(4+b+1) * (Real.Gamma (b+1))^2
  have hD : 0 < D := by
    dsimp [D]
    exact mul_pos (by positivity) (sq_pos_of_pos (Real.Gamma_pos_of_pos (by linarith)))
  have hb7 : 0 < b+7 := by linarith
  refine ⟨2*c1*c2/D, (b+7)*C1*C2/D, by positivity, by positivity, ?_⟩
  intro j hj
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  obtain ⟨hl1, hu1⟩ := h1 j hj
  obtain ⟨hl2, hu2⟩ := h2 j hj
  have he1 : b+1-1 = b := by ring
  have he2 : 4+b+1-(4+1) = b := by ring
  rw [he1] at hl1 hu1
  rw [he2] at hl2 hu2
  simp only [← add_assoc] at hl1 hu1 hl2 hu2
  have hp : 0 < (j : ℝ)^b := Real.rpow_pos_of_pos hjp _
  have hr1 : 0 < Real.Gamma (j+b+1)/Real.Gamma (j+1) :=
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by positivity))
  have hr2 : 0 < Real.Gamma (j+4+b+1)/Real.Gamma (j+4+1) :=
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by positivity))
  have hprod := mul_le_mul hl1 hl2 (mul_nonneg hc2.le hp.le) hr1.le
  have huprod := mul_le_mul hu1 hu2 hr2.le (mul_nonneg hC1.le hp.le)
  have hepow : (j : ℝ) * ((j : ℝ)^b * (j : ℝ)^b) = (j : ℝ)^(2*b+1) := by
    rw [← Real.rpow_add hjp]
    conv_lhs => lhs; rw [← Real.rpow_one (j : ℝ)]
    rw [← Real.rpow_add hjp]
    congr 1
    ring
  rw [jacobi_endpoint_spectral_gamma hNorm 4 b (by norm_num) hb j]
  change _ ≤ ((2*j+4+b+1)/D)*_ * _ ∧ ((2*j+4+b+1)/D)*_ * _ ≤ _
  have hlofactor : 2*(j : ℝ) ≤ 2*j+4+b+1 := by linarith
  have hufactor : 2*(j : ℝ)+4+b+1 ≤ (b+7)*j := by nlinarith
  have hlow : (2*j)*(c1*(j : ℝ)^b*(c2*(j : ℝ)^b)) ≤
      (2*j+4+b+1)*(Real.Gamma (j+b+1)/Real.Gamma (j+1)*
        (Real.Gamma (j+4+b+1)/Real.Gamma (j+4+1))) :=
    mul_le_mul hlofactor hprod (by positivity) (by linarith)
  have hupp : (2*j+4+b+1)*(Real.Gamma (j+b+1)/Real.Gamma (j+1)*
        (Real.Gamma (j+4+b+1)/Real.Gamma (j+4+1))) ≤
      ((b+7)*j)*(C1*(j : ℝ)^b*(C2*(j : ℝ)^b)) :=
    mul_le_mul hufactor huprod (mul_pos hr1 hr2).le (by linarith)
  have hel : (2*j)*(c1*(j : ℝ)^b*(c2*(j : ℝ)^b)) =
      (2*c1*c2)*(j : ℝ)^(2*b+1) := by rw [← hepow]; ring
  have heu : ((b+7)*j)*(C1*(j : ℝ)^b*(C2*(j : ℝ)^b)) =
      ((b+7)*C1*C2)*(j : ℝ)^(2*b+1) := by rw [← hepow]; ring
  rw [hel] at hlow
  rw [heu] at hupp
  constructor
  · convert (div_le_div_of_nonneg_right hlow hD.le) using 1 <;> first | rfl | ring
  · convert (div_le_div_of_nonneg_right hupp hD.le) using 1 <;> first | rfl | ring

end CausalSmith.Stat.NoisydoseWeakdesignTransition
