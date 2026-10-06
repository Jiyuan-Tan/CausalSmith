module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerHandle
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Regularity and model membership of the explicit shared-sign lower laws. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- The interaction region makes the macro radius at least the grid spacing. -/
-- @node: lower_macro_scale
lemma lower_macro_scale (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n) :
    lowerEll κ n ≤ lowerH κ n ∧ 0 < lowerH κ n ∧ κ.β ≤ κ.γ := by
  have hp := sub_pos.mpr hκ.1.1
  have hg := hκ.2.2.2.1
  have ha := hκ.2.1.1
  have hβ := hκ.2.2.1.1
  have hs : 0 < sumReg κ := by unfold sumReg; positivity
  have hx : 0 ≤ (2*κ.α+κ.p*κ.β)/(κ.p-1) := by
    have : 0 < κ.p := by linarith [hκ.1.1]
    positivity
  have hratio : sumReg κ/κ.γ ≤ 1 := by unfold boundary at hb; linarith
  have hsum : sumReg κ ≤ κ.γ := (div_le_one hg).mp hratio
  have he := (lower_scale_small κ n hκ hn).1
  refine ⟨?_, ?_, ?_⟩
  · unfold lowerH
    simpa using Real.rpow_le_rpow_of_exponent_ge he.1 he.2 hratio
  · unfold lowerH; exact Real.rpow_pos_of_pos he.1 _
  · unfold sumReg at hsum; linarith

/-- Bounded Lipschitz increments yield the order-at-most-one Hölder increment. -/
-- @node: lower_increment_interpolation
lemma lower_increment_interpolation {a C d h s : ℝ} (hh : 0 < h) (hd : 0 ≤ d)
    (hs : 0 < s ∧ s ≤ 1) (hC : 0 ≤ C) (hbound : a ≤ C)
    (hlip : a ≤ C*(d/h)) : a ≤ C*(d/h)^s := by
  have hu : 0 ≤ d/h := div_nonneg hd hh.le
  by_cases hsmall : d/h ≤ 1
  · have hr : d/h ≤ (d/h)^s := by
      simpa using Real.rpow_le_rpow_of_exponent_ge' hu hsmall hs.1.le hs.2
    exact hlip.trans (mul_le_mul_of_nonneg_left hr hC)
  · have hr : 1 ≤ (d/h)^s := Real.one_le_rpow (le_of_not_ge hsmall) hs.1.le
    exact hbound.trans (by simpa using mul_le_mul_of_nonneg_left hr hC)

/-- Clipped cosine coordinates have a uniform Lipschitz increment. -/
-- @node: lower_frame_increment
lemma lower_frame_increment (hn : 0 < n) (j : Fin (signCount κ n)) (x z : unitInterval) :
    |frame κ n j x-frame κ n j z| ≤ 2*(|(x : ℝ)-z|/lowerEll κ n) := by
  have he := lowerEll_pos κ n hn
  rw [frame_eq_clipped_cos, frame_eq_clipped_cos]
  have hmin := abs_min_sub_min_le_max
    |(x : ℝ)/lowerEll κ n-j.val| 1 |(z : ℝ)/lowerEll κ n-j.val| 1
  simp only [sub_self, abs_zero, max_eq_left (abs_nonneg (_ : ℝ))] at hmin
  have hab := abs_abs_sub_abs_le_abs_sub ((x : ℝ)/lowerEll κ n-j.val)
    ((z : ℝ)/lowerEll κ n-j.val)
  have hid : (x : ℝ)/lowerEll κ n-j.val-((z : ℝ)/lowerEll κ n-j.val) =
      ((x : ℝ)-z)/lowerEll κ n := by ring
  rw [hid, abs_div, abs_of_pos he] at hab
  have hc := Real.abs_cos_sub_cos_le
    (Real.pi * min |(x : ℝ)/lowerEll κ n-j.val| 1 / 2)
    (Real.pi * min |(z : ℝ)/lowerEll κ n-j.val| 1 / 2)
  have hid2 : Real.pi * min |(x : ℝ)/lowerEll κ n-j.val| 1 / 2 -
      Real.pi * min |(z : ℝ)/lowerEll κ n-j.val| 1 / 2 =
      (Real.pi/2)*(min |(x : ℝ)/lowerEll κ n-j.val| 1 -
        min |(z : ℝ)/lowerEll κ n-j.val| 1) := by ring
  rw [hid2, abs_mul, abs_of_pos (by positivity : 0 < Real.pi/2)] at hc
  calc
    _ ≤ (Real.pi/2)*|min |(x : ℝ)/lowerEll κ n-j.val| 1 -
        min |(z : ℝ)/lowerEll κ n-j.val| 1| := hc
    _ ≤ (Real.pi/2)*(|(x : ℝ)-z|/lowerEll κ n) :=
      mul_le_mul_of_nonneg_left (hmin.trans hab) (by positivity)
    _ ≤ 2*(|(x : ℝ)-z|/lowerEll κ n) := by
      have := Real.pi_lt_four
      gcongr <;> linarith

/-- The triangular cutoff has range zero to one. -/
-- @node: lower_cutoff_range
lemma lower_cutoff_range (x : unitInterval) :
    0 ≤ lowerCutoff κ n x ∧ lowerCutoff κ n x ≤ 1 := by
  have hh : 0 ≤ lowerH κ n := by unfold lowerH lowerEll lowerC; positivity
  have hd := div_nonneg (abs_nonneg ((x : ℝ)-1/2)) hh
  exact ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩

/-- Clipping preserves the triangular cutoff's Lipschitz bound. -/
-- @node: lower_cutoff_increment
lemma lower_cutoff_increment (hh : 0 < lowerH κ n) (x z : unitInterval) :
    |lowerCutoff κ n x-lowerCutoff κ n z| ≤ |(x : ℝ)-z|/lowerH κ n := by
  have h := abs_max_sub_max_le_max 0 (1-|(x : ℝ)-1/2|/lowerH κ n)
    0 (1-|(z : ℝ)-1/2|/lowerH κ n)
  simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (_ : ℝ))] at h
  have hid : 1-|(x : ℝ)-1/2|/lowerH κ n-(1-|(z : ℝ)-1/2|/lowerH κ n) =
    -(|(x : ℝ)-1/2|-|(z : ℝ)-1/2|)/lowerH κ n := by ring
  rw [hid, abs_div, abs_neg, abs_of_pos hh] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ hh.le
  simpa only [sub_sub_sub_cancel_right] using
    abs_abs_sub_abs_le_abs_sub ((x : ℝ)-1/2) ((z : ℝ)-1/2)

/-- Sparsity at the two endpoints bounds the unlocalized sign sum and its increment. -/
-- @node: lower_sign_sum_bounds
lemma lower_sign_sum_bounds (hn : 0 < n) (v : Signs κ n) (x z : unitInterval) :
    |∑ j, sign (v j)*frame κ n j x| ≤ 2 ∧
    |(∑ j, sign (v j)*frame κ n j x)-(∑ j, sign (v j)*frame κ n j z)| ≤
      8*(|(x : ℝ)-z|/lowerEll κ n) := by
  classical
  let S := Finset.univ.filter (fun j => frame κ n j x ≠ 0)
  let T := Finset.univ.filter (fun j => frame κ n j z ≠ 0)
  have hsign (j) : |sign (v j)| = 1 := by cases v j <;> norm_num [sign]
  have hcardS : (S.card : ℝ) ≤ 2 := by exact_mod_cast frame_active_card κ n x
  have hcardT : (T.card : ℝ) ≤ 2 := by exact_mod_cast frame_active_card κ n z
  have hsum : (∑ j, sign (v j)*frame κ n j x) = ∑ j ∈ S, sign (v j)*frame κ n j x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hz : frame κ n j x = 0 := by simpa [S] using hj
    simp [hz]
  refine ⟨?_, ?_⟩
  · rw [hsum]
    calc
      _ ≤ ∑ j ∈ S, |sign (v j)*frame κ n j x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, hsign, one_mul, frame_eq_clipped_cos]
        exact Real.abs_cos_le_one _
      _ ≤ 2 := by simpa using hcardS
  · have hsumdiff : (∑ j, sign (v j)*frame κ n j x)-(∑ j, sign (v j)*frame κ n j z) =
        ∑ j ∈ S ∪ T, sign (v j)*(frame κ n j x-frame κ n j z) := by
      rw [← Finset.sum_sub_distrib]
      simp_rw [← mul_sub]
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      have hx : frame κ n j x = 0 := by
        have : j ∉ S := fun h => hj (Finset.mem_union_left _ h)
        simpa [S] using this
      have hz : frame κ n j z = 0 := by
        have : j ∉ T := fun h => hj (Finset.mem_union_right _ h)
        simpa [T] using this
      simp [hx, hz]
    rw [hsumdiff]
    have hc : ((S ∪ T).card : ℝ) ≤ 4 := by
      have := Finset.card_union_le S T
      exact_mod_cast (show (S ∪ T).card ≤ 4 from by
        have hs : S.card ≤ 2 := by exact_mod_cast hcardS
        have ht : T.card ≤ 2 := by exact_mod_cast hcardT
        omega)
    calc
      _ ≤ ∑ j ∈ S ∪ T, |sign (v j)*(frame κ n j x-frame κ n j z)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ S ∪ T, 2*(|(x : ℝ)-z|/lowerEll κ n) := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, hsign, one_mul]
        exact lower_frame_increment κ n hn j x z
      _ = ((S ∪ T).card : ℝ)*(2*(|(x : ℝ)-z|/lowerEll κ n)) := by simp
      _ ≤ 8*(|(x : ℝ)-z|/lowerEll κ n) := by
        nlinarith [mul_le_mul_of_nonneg_right hc
          (show 0 ≤ 2*(|(x : ℝ)-z|/lowerEll κ n) from mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (lowerEll_pos κ n hn).le))]

/-- The localized field has a grid-scale Hölder increment. -/
-- @node: lower_field_holder_increment
lemma lower_field_holder_increment (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) (v : Signs κ n) (x z : unitInterval) :
    |lowerField κ n v x-lowerField κ n v z| ≤ 10*(|(x : ℝ)-z|/lowerEll κ n)^s := by
  have he := (lower_scale_small κ n hκ hn).1.1
  have hh := lower_macro_scale κ n hκ hb hn
  have hx := lower_cutoff_range κ n x
  have hz := lower_cutoff_range κ n z
  have hsum := lower_sign_sum_bounds κ n (by omega) v x z
  have hd := lower_cutoff_increment κ n hh.2.1 x z
  have hdiv : |(x : ℝ)-z|/lowerH κ n ≤ |(x : ℝ)-z|/lowerEll κ n :=
    div_le_div_of_nonneg_left (abs_nonneg _) he hh.1
  apply lower_increment_interpolation he (abs_nonneg _) hs (by norm_num)
  · have ht := abs_add_le (lowerField κ n v x) (-lowerField κ n v z)
    simp only [abs_neg, ← sub_eq_add_neg] at ht
    linarith [lower_field_abs_le_two κ n v x, lower_field_abs_le_two κ n v z]
  · have hid : lowerField κ n v x-lowerField κ n v z =
        lowerCutoff κ n z*((∑ j, sign (v j)*frame κ n j x)-(∑ j, sign (v j)*frame κ n j z)) +
        (lowerCutoff κ n x-lowerCutoff κ n z)*(∑ j, sign (v j)*frame κ n j x) := by
      unfold lowerField; ring
    rw [hid]
    have ht := abs_add_le
      (lowerCutoff κ n z*((∑ j, sign (v j)*frame κ n j x)-(∑ j, sign (v j)*frame κ n j z)))
      ((lowerCutoff κ n x-lowerCutoff κ n z)*(∑ j, sign (v j)*frame κ n j x))
    rw [abs_mul, abs_of_nonneg hz.1, abs_mul] at ht
    have h1 := mul_le_mul hz.2 hsum.2 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    have h2 := mul_le_mul (hd.trans hdiv) hsum.1 (abs_nonneg _) (by positivity)
    linarith

/-- The squared cutoff has a macro-scale Hölder increment and unit range. -/
-- @node: lower_square_holder_increment
lemma lower_square_holder_increment (hh : 0 < lowerH κ n) (s : ℝ)
    (hs : 0 < s ∧ s ≤ 1) (x z : unitInterval) :
    |lowerSquare κ n x-lowerSquare κ n z| ≤ 2*(|(x : ℝ)-z|/lowerH κ n)^s := by
  have hx := lower_cutoff_range κ n x
  have hz := lower_cutoff_range κ n z
  apply lower_increment_interpolation hh (abs_nonneg _) hs (by norm_num)
  · unfold lowerSquare
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (lowerCutoff κ n x), sq_nonneg (lowerCutoff κ n z)]
  · have hid : lowerSquare κ n x-lowerSquare κ n z =
        (lowerCutoff κ n x-lowerCutoff κ n z)*(lowerCutoff κ n x+lowerCutoff κ n z) := by
      unfold lowerSquare; ring
    rw [hid, abs_mul, abs_of_nonneg (show 0 ≤ lowerCutoff κ n x+lowerCutoff κ n z by linarith)]
    have hd := lower_cutoff_increment κ n hh x z
    have ht := mul_le_mul hd (show lowerCutoff κ n x+lowerCutoff κ n z ≤ 2 by linarith)
      (by linarith : 0 ≤ lowerCutoff κ n x+lowerCutoff κ n z) (by positivity)
    linarith


/-- Scaling a grid Hölder increment cancels the grid power exactly. -/
-- @node: lower_scaled_field_increment
lemma lower_scaled_field_increment (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) (v : Signs κ n) (x z : unitInterval) :
    (lowerEll κ n^s/1024)*|lowerField κ n v x-lowerField κ n v z| ≤
      (10/1024)*|(x : ℝ)-z|^s := by
  have he := (lower_scale_small κ n hκ hn).1.1
  have hf := lower_field_holder_increment κ n hκ hb hn s hs v x z
  have hpow := Real.rpow_pos_of_pos he s
  have hid : (lowerEll κ n^s/1024)*(10*(|(x : ℝ)-z|/lowerEll κ n)^s) =
      (10/1024)*|(x : ℝ)-z|^s := by
    rw [Real.div_rpow (abs_nonneg _) he.le]
    field_simp
  exact (mul_le_mul_of_nonneg_left hf (by positivity)).trans_eq hid

/-- The product of amplitudes is smaller than the macro Hölder scale. -/
-- @node: lower_product_macro_bound
lemma lower_product_macro_bound (hκ : κ.Valid) (hn : 2 ≤ n) (s : ℝ)
    (hs : 0 ≤ s ∧ s ≤ κ.γ) :
    lowerA κ n*lowerB κ n ≤ (lowerH κ n)^s/(1024 : ℝ)^2 := by
  have he := (lower_scale_small κ n hκ hn).1
  have hg := hκ.2.2.2.1
  have hS : 0 ≤ sumReg κ := by unfold sumReg; linarith [hκ.2.1.1, hκ.2.2.1.1]
  have hexp : (sumReg κ/κ.γ)*s ≤ sumReg κ := by
    have := mul_le_mul_of_nonneg_left hs.2 (div_nonneg hS hg.le)
    have hid : (sumReg κ/κ.γ)*κ.γ = sumReg κ := div_mul_cancel₀ _ hg.ne'
    linarith
  have hr := Real.rpow_le_rpow_of_exponent_ge he.1 he.2 hexp
  unfold lowerA lowerB lowerH
  rw [← Real.rpow_mul he.1.le]
  have hid : lowerEll κ n^κ.α/1024*(lowerEll κ n^κ.β/1024) =
      lowerEll κ n^(sumReg κ)/(1024 : ℝ)^2 := by
    rw [sumReg, Real.rpow_add he.1]
    ring
  rw [hid]
  exact div_le_div_of_nonneg_right hr (by norm_num)

/-- The amplitude product times a squared-cutoff increment has a uniform Hölder bound. -/
-- @node: lower_scaled_square_increment
lemma lower_scaled_square_increment (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1) (hsg : s ≤ κ.γ) (x z : unitInterval) :
    lowerA κ n*lowerB κ n*|lowerSquare κ n x-lowerSquare κ n z| ≤
      (2/(1024 : ℝ)^2)*|(x : ℝ)-z|^s := by
  have hh := (lower_macro_scale κ n hκ hb hn).2.1
  have hp := lower_product_macro_bound κ n hκ hn s ⟨hs.1.le, hsg⟩
  have hi := lower_square_holder_increment κ n hh s hs x z
  have hm := mul_le_mul hp hi (abs_nonneg _) (by positivity)
  have hid : (lowerH κ n^s/(1024 : ℝ)^2)*(2*(|(x : ℝ)-z|/lowerH κ n)^s) =
      (2/(1024 : ℝ)^2)*|(x : ℝ)-z|^s := by
    rw [Real.div_rpow (abs_nonneg _) hh.le]
    have := Real.rpow_pos_of_pos hh s
    field_simp
  exact hm.trans_eq hid

/-- The exact conditional raw moment of every three-atom arm is four. -/
-- @node: lower_conditional_moment_four
lemma lower_conditional_moment_four (hκ : κ.Valid) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) (a : Bool) (x : unitInterval) :
    (∫⁻ y, ENNReal.ofReal (|y|^κ.p) ∂lowerOutcomeKernel κ n ε v a x) = 4 := by
  have hB := (lower_rare_scale κ n hκ hn).1
  obtain ⟨hw1, hw2, hw3⟩ := lower_atom_weights_nonneg κ n hκ hn ε v a x
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (|y|^κ.p)) := by fun_prop
  change (∫⁻ y, ENNReal.ofReal (|y|^κ.p) ∂lowerOutcomeMeasure κ n ε v a x) = 4
  simp only [lowerOutcomeMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_dirac' _ hm, smul_eq_mul, abs_neg, abs_zero,
    Real.zero_rpow (show κ.p ≠ 0 by linarith [hκ.1.1]), ENNReal.ofReal_zero,
    mul_zero, add_zero, abs_of_pos hB]
  rw [← add_mul, ← ENNReal.ofReal_add hw1 hw2]
  have hw : lowerRare κ n/2+lowerMean κ n ε v a x/(2*lowerAmplitude κ n)+
      (lowerRare κ n/2-lowerMean κ n ε v a x/(2*lowerAmplitude κ n)) = lowerRare κ n := by ring
  rw [hw, ← ENNReal.ofReal_mul (by unfold lowerRare; positivity)]
  have hid : lowerRare κ n*lowerAmplitude κ n^κ.p = 4 := by
    unfold lowerRare
    rw [mul_assoc, ← Real.rpow_add hB]
    simp
  rw [hid]
  norm_num


/-- The propensity and the two deterministic mean fields obey the model's range bounds. -/
-- @node: lower_model_range_bounds
lemma lower_model_range_bounds (hκ : κ.Valid) (hn : 2 ≤ n) (ε : Bool)
    (v : Signs κ n) (x : unitInterval) :
    (1/4 ≤ lowerPropensity κ n v x ∧ lowerPropensity κ n v x ≤ 3/4) ∧
    |lowerPropensity κ n v x| ≤ 20 ∧ |lowerMean κ n ε v false x| ≤ 20 ∧
    |lowerEffect κ n ε x| ≤ 1/2 := by
  have ha := (lower_scale_small κ n hκ hn).2.1
  have hb := (lower_scale_small κ n hκ hn).2.2
  have hf := lower_field_abs_le_two κ n v x
  have hsq : |lowerSquare κ n x| ≤ 1 := by
    have hk := lower_cutoff_range κ n x
    unfold lowerSquare
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith
  have hsign : |sign ε| = 1 := by cases ε <;> norm_num [sign]
  have hprod : 0 ≤ lowerA κ n*lowerB κ n ∧ lowerA κ n*lowerB κ n ≤ 1/(1024 : ℝ)^2 := by
    exact ⟨mul_nonneg ha.1.le hb.1.le, by nlinarith [mul_le_mul ha.2 hb.2 hb.1.le (by norm_num : (0 : ℝ) ≤ 1/1024)]⟩
  have hp := mul_le_mul_of_nonneg_left hf ha.1.le
  obtain ⟨hlo, hhi⟩ := abs_le.mp hf
  have hover : 1/4 ≤ lowerPropensity κ n v x ∧ lowerPropensity κ n v x ≤ 3/4 := by
    unfold lowerPropensity lowerP0
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hlo ha.1.le,
      mul_le_mul_of_nonneg_left hhi ha.1.le]
  refine ⟨hover, ?_, ?_, ?_⟩
  · exact abs_le.mpr ⟨by linarith [hover.1], by linarith [hover.2]⟩
  · have h := abs_add_le (sign ε*lowerB κ n*lowerField κ n v x)
        ((sign ε*lowerA κ n*lowerB κ n*lowerSquare κ n x)/(1-lowerP0))
    simp only [abs_mul, abs_div, hsign, one_mul, abs_of_pos ha.1,
      abs_of_pos hb.1, lowerP0] at h
    norm_num at h
    have h1 := mul_le_mul_of_nonneg_left hf hb.1.le
    have h2 := mul_le_mul_of_nonneg_left hsq hprod.1
    change |sign ε*lowerB κ n*lowerField κ n v x+
      sign ε*lowerA κ n*lowerB κ n*lowerSquare κ n x/(1-lowerP0)| ≤ 20
    norm_num [lowerP0] at *
    nlinarith
  · unfold lowerEffect
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_mul, hsign, one_mul,
      abs_of_pos ha.1, abs_of_pos hb.1]
    norm_num [lowerP0]
    have := mul_le_mul_of_nonneg_left hsq hprod.1
    nlinarith

/-- The explicit original lower laws satisfy all seven model clauses. -/
-- @node: lower_prior_membership
lemma lower_prior_membership (hκ : κ.Valid) (hb : boundary κ ≤ 1) (hn : 2 ≤ n)
    (ε : Bool) (v : Signs κ n) :
    InModel κ (lowerPriorLaw κ n ε v) ∧
    (lowerPriorLaw κ n ε v).tau = lowerEffect κ n ε := by
  have hd : κ.Valid ∧ boundary κ ≤ 1 ∧ 2 ≤ n := ⟨hκ, hb, hn⟩
  have ha := (lower_scale_small κ n hκ hn).2.1
  have hβ := (lower_scale_small κ n hκ hn).2.2
  have hh := lower_macro_scale κ n hκ hb hn
  have hsign : |sign ε| = 1 := by cases ε <;> norm_num [sign]
  have hc : Continuous (lowerCutoff κ n) := by unfold lowerCutoff; fun_prop
  have hfield : Continuous (lowerField κ n v) := by unfold lowerField; fun_prop
  have hsquare : Continuous (lowerSquare κ n) := by unfold lowerSquare; fun_prop
  rw [lowerPriorLaw, dif_pos hd]
  refine ⟨?_, rfl⟩
  constructor
  · exact uniformRecord_marginal _ _ (lower_law_versions κ n hd ε v).1 _
      (lower_law_versions κ n hd ε v).2.1
  · exact fun x => (lower_model_range_bounds κ n hκ hn ε v x).1
  · change holderBall κ.α (lowerPropensity κ n v)
    refine ⟨by unfold lowerPropensity; fun_prop,
      fun x => (lower_model_range_bounds κ n hκ hn ε v x).2.1, ?_⟩
    intro x z
    have hi := lower_scaled_field_increment κ n hκ hb hn κ.α hκ.2.1 v x z
    have hid : lowerPropensity κ n v x-lowerPropensity κ n v z =
        lowerA κ n*(lowerField κ n v x-lowerField κ n v z) := by
      unfold lowerPropensity; ring
    rw [hid, abs_mul, abs_of_pos ha.1]
    change (lowerEll κ n^κ.α/1024)*|lowerField κ n v x-lowerField κ n v z| ≤ _
    exact hi.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · change holderBall κ.β (lowerMean κ n ε v false)
    refine ⟨by unfold lowerMean; simp only [Bool.false_eq_true, ↓reduceIte]; fun_prop,
      fun x => (lower_model_range_bounds κ n hκ hn ε v x).2.2.1, ?_⟩
    intro x z
    have hi := lower_scaled_field_increment κ n hκ hb hn κ.β hκ.2.2.1 v x z
    have hj := lower_scaled_square_increment κ n hκ hb hn κ.β hκ.2.2.1 hh.2.2 x z
    have hid : lowerMean κ n ε v false x-lowerMean κ n ε v false z =
      sign ε*lowerB κ n*(lowerField κ n v x-lowerField κ n v z) +
      sign ε*lowerA κ n*lowerB κ n*(lowerSquare κ n x-lowerSquare κ n z)/(1-lowerP0) := by
      simp only [lowerMean, Bool.false_eq_true, ↓reduceIte]; ring
    rw [hid]
    have h := abs_add_le (sign ε*lowerB κ n*(lowerField κ n v x-lowerField κ n v z))
      (sign ε*lowerA κ n*lowerB κ n*(lowerSquare κ n x-lowerSquare κ n z)/(1-lowerP0))
    simp only [abs_mul, abs_div, hsign, one_mul, abs_of_pos ha.1, abs_of_pos hβ.1] at h
    norm_num [lowerP0] at h ⊢
    change lowerB κ n*|lowerField κ n v x-lowerField κ n v z| ≤ _ at hi
    nlinarith [Real.rpow_nonneg (abs_nonneg ((x : ℝ)-z)) κ.β]
  · change holderBall κ.γ (lowerEffect κ n ε)
    refine ⟨by unfold lowerEffect; fun_prop, ?_, ?_⟩
    · intro x
      have h := (lower_model_range_bounds κ n hκ hn ε v x).2.2.2
      linarith
    · intro x z
      have hj := lower_scaled_square_increment κ n hκ hb hn κ.γ hκ.2.2.2 le_rfl x z
      have hid : lowerEffect κ n ε x-lowerEffect κ n ε z =
          -(sign ε*lowerA κ n*lowerB κ n*(lowerSquare κ n x-lowerSquare κ n z))/(lowerP0*(1-lowerP0)) := by
        unfold lowerEffect; ring
      rw [hid, abs_div, abs_neg, abs_mul, abs_mul, abs_mul, hsign, one_mul,
        abs_of_pos ha.1, abs_of_pos hβ.1]
      norm_num [lowerP0]
      nlinarith [Real.rpow_nonneg (abs_nonneg ((x : ℝ)-z)) κ.γ]
  · exact fun x => (lower_model_range_bounds κ n hκ hn ε v x).2.2.2
  · filter_upwards [] with x a
    change (∫⁻ y, ENNReal.ofReal (|y|^κ.p) ∂lowerOutcomeKernel κ n ε v a x) ≤ 10
    rw [lower_conditional_moment_four κ n hκ hn]
    norm_num

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
