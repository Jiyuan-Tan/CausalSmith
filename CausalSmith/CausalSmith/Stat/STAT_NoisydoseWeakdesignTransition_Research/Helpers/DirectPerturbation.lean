module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ObservedMarkedChiSquare

/-! Direct-regime compact bump bounds for the observed lower-bound construction. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory Set
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The direct-regime compact bump of equation (14), including its zero extension. -/
-- @node: directPerturbation
def directPerturbation (beta epsilon h0 t : ℝ) : ℝ :=
  if |t| ≤ h0 then epsilon*h0^beta*(1-(t/h0)^2)^2 else 0

/-- Squaring on the unit interval has Lipschitz constant two. [This is the stated conclusion](goal). [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). [Under the stated conditions](hyp:ha,hb). [This is the stated conclusion](goal). -/
-- @node: unit_square_increment
lemma unit_square_increment (a b : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Icc (0 : ℝ) 1) : |a^2-b^2| ≤ 2*|a-b| := by
  have hs : |a+b| ≤ 2 := by rw [abs_of_nonneg (by linarith [ha.1, hb.1] : 0 ≤ a+b)]; linarith [ha.2, hb.2]
  calc
    |a^2-b^2| = |a-b| *|a+b| := by rw [← abs_mul]; congr 1; ring
    _ ≤ |a-b| *2 := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = _ := by ring

/-- The clipped polynomial representation includes the zero extension at both endpoints. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_clipped
lemma directPerturbation_clipped (beta epsilon h t : ℝ) (hh : 0 < h) :
    directPerturbation beta epsilon h t =
      epsilon*h^beta*(1-(min |t/h| 1)^2)^2 := by
  by_cases ht : |t| ≤ h
  · have hq : |t/h| ≤ 1 := by rw [abs_div, abs_of_pos hh]; exact (div_le_one hh).mpr ht
    simp only [directPerturbation, if_pos ht, min_eq_left hq, sq_abs]
  · have hq : 1 ≤ |t/h| := by
      rw [abs_div, abs_of_pos hh]; exact (le_div_iff₀ hh).mpr (by simpa using (le_of_lt (lt_of_not_ge ht)))
    simp [directPerturbation, ht, min_eq_right hq]

/-- The bump lies between zero and its tuning amplitude. [Under the stated conditions](hyp:h,he,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_bounds
lemma directPerturbation_bounds (beta epsilon h t : ℝ) (he : 0 ≤ epsilon) (hh : 0 < h) :
    directPerturbation beta epsilon h t ∈ Icc 0 (epsilon*h^beta) := by
  rw [directPerturbation_clipped beta epsilon h t hh]
  have hx : 0 ≤ min |t/h| 1 := le_min (abs_nonneg _) zero_le_one
  have hy : min |t/h| 1 ≤ 1 := min_le_right _ _
  have hz : 0 ≤ 1-(min |t/h| 1)^2 := by nlinarith
  have hw : (1-(min |t/h| 1)^2)^2 ≤ 1 := by nlinarith [sq_nonneg (min |t/h| 1)]
  have hA : 0 ≤ epsilon*h^beta := mul_nonneg he (Real.rpow_nonneg hh.le _)
  exact ⟨mul_nonneg hA (sq_nonneg _), (mul_le_mul_of_nonneg_left hw hA).trans_eq (mul_one _)⟩

/-- The compact bump vanishes off its stipulated support. [Under the stated conditions](hyp:h,ht). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_support
lemma directPerturbation_support (beta epsilon h t : ℝ)
    (ht : t ∉ Icc (-h) h) : directPerturbation beta epsilon h t = 0 := by
  have hn : ¬ |t| ≤ h := by simpa only [abs_le, mem_Icc] using ht
  simp [directPerturbation, hn]

/-- Clipping exposes continuity of the zero-extended bump without an endpoint exception. [Under the stated conditions](hyp:hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_continuous
@[fun_prop] lemma directPerturbation_continuous (beta epsilon h : ℝ) (hh : 0 < h) :
    Continuous (directPerturbation beta epsilon h) := by
  have heq : directPerturbation beta epsilon h =
      fun t => epsilon*h^beta*(1-(min |t/h| 1)^2)^2 :=
    funext (fun t => directPerturbation_clipped beta epsilon h t hh)
  rw [heq]
  fun_prop

/-- The bump's increment is bounded by four times its amplitude times scaled distance. [Under the stated conditions](hyp:h,he,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_lipschitz_bound
lemma directPerturbation_lipschitz_bound (beta epsilon h s t : ℝ)
    (he : 0 ≤ epsilon) (hh : 0 < h) :
    |directPerturbation beta epsilon h s-directPerturbation beta epsilon h t| ≤
      4*epsilon*h^beta*(|s-t|/h) := by
  let a := min |s/h| 1
  let b := min |t/h| 1
  have ha : a ∈ Icc (0 : ℝ) 1 := ⟨le_min (abs_nonneg _) zero_le_one, min_le_right _ _⟩
  have hb : b ∈ Icc (0 : ℝ) 1 := ⟨le_min (abs_nonneg _) zero_le_one, min_le_right _ _⟩
  have hab : |a-b| ≤ |s-t|/h := by
    calc
      _ ≤ max (abs (abs (s/h) - abs (t/h))) (abs ((1 : ℝ)-1)) := abs_min_sub_min_le_max _ _ _ _
      _ = abs (abs (s/h) - abs (t/h)) := by simp
      _ ≤ |s/h-t/h| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |s-t|/h := by rw [← sub_div, abs_div, abs_of_pos hh]
  have ha' : 1-a^2 ∈ Icc (0 : ℝ) 1 := by constructor <;> nlinarith [sq_nonneg a, ha.1, ha.2]
  have hb' : 1-b^2 ∈ Icc (0 : ℝ) 1 := by constructor <;> nlinarith [sq_nonneg b, hb.1, hb.2]
  have hf : |(1-a^2)^2-(1-b^2)^2| ≤ 4*(|s-t|/h) := by
    have h1 := unit_square_increment (1-a^2) (1-b^2) ha' hb'
    have h2 := unit_square_increment a b ha hb
    have heq : |(1-a^2)-(1-b^2)| = |a^2-b^2| := by
      rw [show (1-a^2)-(1-b^2) = -(a^2-b^2) by ring, abs_neg]
    rw [heq] at h1
    linarith
  rw [directPerturbation_clipped beta epsilon h s hh,
    directPerturbation_clipped beta epsilon h t hh, ← mul_sub, abs_mul,
    abs_of_nonneg (mul_nonneg he (Real.rpow_nonneg hh.le _))]
  exact (mul_le_mul_of_nonneg_left hf (mul_nonneg he (Real.rpow_nonneg hh.le _))).trans_eq (by ring)

/-- The two distance regimes in (15) give the scale-free Hölder seminorm. [Under the stated conditions](hyp:h,he,hh,hb). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_holder_bound
lemma directPerturbation_holder_bound (beta epsilon h s t : ℝ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (he : 0 ≤ epsilon) (hh : 0 < h) :
    |directPerturbation beta epsilon h s-directPerturbation beta epsilon h t| ≤
      4*epsilon*|s-t|^beta := by
  have hA : 0 ≤ epsilon*h^beta := mul_nonneg he (Real.rpow_nonneg hh.le _)
  by_cases hst : |s-t| ≤ h
  · have hr : |s-t|/h ≤ (|s-t|/h)^beta := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge'
        (div_nonneg (abs_nonneg _) hh.le) ((div_le_one hh).mpr hst) hb.1 hb.2
    calc
      _ ≤ 4*epsilon*h^beta*(|s-t|/h) := directPerturbation_lipschitz_bound _ _ _ _ _ he hh
      _ ≤ 4*epsilon*h^beta*((|s-t|/h)^beta) := by gcongr
      _ = _ := by rw [Real.div_rpow (abs_nonneg _) hh.le]; field_simp
  · have hsmall := directPerturbation_bounds beta epsilon h s he hh
    have htall := directPerturbation_bounds beta epsilon h t he hh
    have hdiff : |directPerturbation beta epsilon h s-directPerturbation beta epsilon h t| ≤
        epsilon*h^beta := by rw [abs_le]; constructor <;> linarith [hsmall.1, hsmall.2, htall.1, htall.2]
    have hp : h^beta ≤ |s-t|^beta := Real.rpow_le_rpow hh.le (le_of_lt (lt_of_not_ge hst)) hb.1
    calc
      _ ≤ epsilon*h^beta := hdiff
      _ ≤ epsilon*|s-t|^beta := mul_le_mul_of_nonneg_left hp he
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (abs_nonneg (s-t)) beta]

/-- Small direct-regime amplitudes give the two actual continuous threshold profiles,
with the paper's range and radius-one Hölder seminorm. [Under the stated conditions](hyp:h,he,heSmall,hh,hamp,hb). [This is the stated conclusion](goal). -/
-- @node: direct_threshold_profiles
lemma direct_threshold_profiles (beta epsilon h : ℝ)
    (hb : beta ∈ Icc (0 : ℝ) 1) (he : 0 ≤ epsilon) (heSmall : 4*epsilon ≤ 1)
    (hh : 0 < h) (hamp : epsilon*h^beta ≤ 3/8) :
    ∃ muPlus muMinus : ThresholdProfile,
      (∀ a : Dose, (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∧
        (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0)) ∧
      (∀ a, (muPlus a : ℝ) ∈ Icc (1/8) (7/8) ∧
        (muMinus a : ℝ) ∈ Icc (1/8) (7/8)) ∧
      (∀ a b, |(muPlus a : ℝ)-(muPlus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta ∧
        |(muMinus a : ℝ)-(muMinus b : ℝ)| ≤ |(a : ℝ)-(b : ℝ)|^beta) := by
  have hbounds (a : Dose) := directPerturbation_bounds beta epsilon h ((a : ℝ)-a0) he hh
  have hp (a : Dose) : 1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [(hbounds a).1, (hbounds a).2]
  have hm (a : Dose) : 1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0) ∈ Icc (0 : ℝ) 1 := by
    constructor <;> linarith [(hbounds a).1, (hbounds a).2]
  let muPlus : ThresholdProfile :=
    ⟨fun a => ⟨1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0), hp a⟩, by fun_prop⟩
  let muMinus : ThresholdProfile :=
    ⟨fun a => ⟨1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0), hm a⟩, by fun_prop⟩
  refine ⟨muPlus, muMinus, (fun a => ⟨rfl, rfl⟩), ?_, ?_⟩
  · intro a
    change (1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∈ Icc (1/8 : ℝ) (7/8)) ∧
      (1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0) ∈ Icc (1/8 : ℝ) (7/8))
    constructor <;> constructor <;> linarith [(hbounds a).1, (hbounds a).2]
  · intro a b
    have hinc := directPerturbation_holder_bound beta epsilon h ((a : ℝ)-a0) ((b : ℝ)-a0) hb he hh
    rw [sub_sub_sub_cancel_right] at hinc
    have hfinal := hinc.trans (mul_le_of_le_one_left
      (Real.rpow_nonneg (abs_nonneg ((a : ℝ)-(b : ℝ))) beta) heSmall)
    change |(1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0))-
        (1/2 + directPerturbation beta epsilon h ((b : ℝ)-a0))| ≤ _ ∧
      |(1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0))-
        (1/2 - directPerturbation beta epsilon h ((b : ℝ)-a0))| ≤ _
    constructor
    · simpa only [add_sub_add_left_eq_sub] using hfinal
    · simpa only [sub_sub_sub_cancel_left, abs_sub_comm] using hfinal

/-- The amplitude at the target is exactly the direct tuning amplitude. [Under the stated conditions](hyp:h,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_zero
lemma directPerturbation_zero (beta epsilon h : ℝ) (hh : 0 < h) :
    directPerturbation beta epsilon h 0 = epsilon*h^beta := by
  simp [directPerturbation, hh.le]

/-- The direct bump times the power-law design is an integrable compact signed density. [Under the stated conditions](hyp:hk,hh). [This is the stated conclusion](goal). -/
-- @node: directPerturbation_signed_integrable
@[fun_prop] lemma directPerturbation_signed_integrable (beta kappa epsilon h : ℝ)
    (hk : 0 ≤ kappa) (hh : 0 < h) :
    Integrable (fun t => witnessDesignDensity kappa t * directPerturbation beta epsilon h t) := by
  have hc : Continuous (fun t : ℝ => (kappa+1)*2^kappa*|t|^kappa *
      directPerturbation beta epsilon h t) := by fun_prop
  have heq : (fun t => witnessDesignDensity kappa t * directPerturbation beta epsilon h t) =
      (Icc (-1/2 : ℝ) (1/2)).indicator (fun t : ℝ =>
        (kappa+1)*2^kappa*|t|^kappa * directPerturbation beta epsilon h t) := by
    funext t
    simp only [witnessDesignDensity, indicator_apply]
    split_ifs <;> simp
  rw [heq]
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

end CausalSmith.Stat.NoisydoseWeakdesignTransition
