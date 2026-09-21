module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.AnnotationFrontierConsequences

/-! Numerical strict-improvement characterization for the annotation frontier. -/

public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open Filter Topology Asymptotics
open MeasureTheory

-- @node: positive_two_sided_bounds_isTheta
/-- [the stated conditions](hyp:hc,hC,hf,hg,hlo,hhi) establishes [the stated conclusion](goal). -/
lemma positive_two_sided_bounds_isTheta {alpha : Type*} {l : Filter alpha}
    (f g : alpha → Real) {c C : Real} (hc : 0 < c) (hC : 0 < C)
    (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : ∀ᶠ x in l, 0 ≤ g x)
    (hlo : ∀ᶠ x in l, c * g x ≤ f x) (hhi : ∀ᶠ x in l, f x ≤ C * g x) :
    f =Θ[l] g := by
  apply IsBigO.antisymm
  · apply IsBigO.of_bound C
    filter_upwards [hf, hg, hhi] with x hfx hgx hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hfx, abs_of_nonneg hgx] using hx
  · apply IsBigO.of_bound c⁻¹
    filter_upwards [hf, hg, hlo] with x hfx hgx hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hgx, abs_of_nonneg hfx]
    have hc0 : c ≠ 0 := ne_of_gt hc
    calc
      g x = c⁻¹ * (c * g x) := by field_simp
      _ ≤ c⁻¹ * f x := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hc.le)

-- @node: minimaxRisk_le_measurable_estimator
/-- [the stated conditions](hyp:hest) establishes [the stated conclusion](goal). -/
lemma minimaxRisk_le_measurable_estimator {n m d : Nat} {eps : Real}
    (est : Sample n m d → Real) (hest : Measurable est) :
    minimaxRisk n m d eps ≤
      ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) est (ateFunctional P.1) := by
  unfold minimaxRisk
  have hnonneg (e : {f : Sample n m d → Real // Measurable f}) :
      0 ≤ ⨆ P : ClassLaw d eps,
        twoSampleMSE (annotationLaw P.1 n m) e.1 (ateFunctional P.1) := by
    cases isEmpty_or_nonempty (ClassLaw d eps) with
    | inl hempty =>
        letI := hempty
        simp
    | inr hnonempty =>
        letI := hnonempty
        by_cases hb : BddAbove (Set.range (fun P : ClassLaw d eps ↦
            twoSampleMSE (annotationLaw P.1 n m) e.1 (ateFunctional P.1)))
        · exact (integral_nonneg fun z ↦ sq_nonneg
              (e.1 z - ateFunctional (Classical.arbitrary (ClassLaw d eps)).1)).trans
            (le_ciSup hb (Classical.arbitrary _))
        · rw [show (⨆ P : ClassLaw d eps,
              twoSampleMSE (annotationLaw P.1 n m) e.1
                (ateFunctional P.1)) = sSup ∅ from csSup_of_not_bddAbove hb]
          simp
  have hb : BddBelow (Set.range (fun e :
      {f : Sample n m d → Real // Measurable f} ↦
        ⨆ P : ClassLaw d eps,
          twoSampleMSE (annotationLaw P.1 n m) e.1 (ateFunctional P.1))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨e, rfl⟩
    exact hnonneg e
  exact ciInf_le hb ⟨est, hest⟩

-- @node: min_one_sq_nonnegative
/-- [the stated conditions](hyp:hx) establishes [the stated conclusion](goal). -/
lemma min_one_sq_nonnegative {x : Real} (hx : 0 ≤ x) :
    (min 1 x) ^ 2 = min 1 (x ^ 2) := by
  by_cases h : x ≤ 1
  · rw [min_eq_right h, min_eq_right]
    nlinarith
  · have h1 : 1 ≤ x := le_of_not_ge h
    rw [min_eq_left h1, min_eq_left (by nlinarith [sq_nonneg (x - 1)])]
    norm_num

-- @node: strict_min_rates_iff_ratios
/-- [the stated conditions](hyp:hi0,hi1,ha,hb,hba) establishes [the stated conclusion](goal). -/
lemma strict_min_rates_iff_ratios {alpha : Type*} {l : Filter alpha}
    (i a b : alpha → Real)
    (hi0 : ∀ᶠ x in l, 0 < i x) (hi1 : ∀ᶠ x in l, i x ≤ 1)
    (ha : ∀ᶠ x in l, 0 < a x) (hb : ∀ᶠ x in l, 0 ≤ b x)
    (hba : ∀ᶠ x in l, b x ≤ a x) :
    (fun x ↦ min 1 (i x + b x ^ 2)) =o[l]
        (fun x ↦ min 1 (i x + a x ^ 2)) ↔
      Tendsto (fun x ↦ i x / min 1 (i x + a x ^ 2)) l (nhds 0) ∧
      Tendsto (fun x ↦ b x / min 1 (a x)) l (nhds 0) := by
  let r := fun x ↦ min 1 (i x + b x ^ 2)
  let r₀ := fun x ↦ min 1 (i x + a x ^ 2)
  let h := fun x ↦ min 1 (a x)
  have hr0 : ∀ᶠ x in l, 0 ≤ r x := by
    filter_upwards [hi0] with x hx
    dsimp [r]
    exact le_min (by norm_num) (add_pos_of_pos_of_nonneg hx (sq_nonneg _)).le
  have hr₀0 : ∀ᶠ x in l, 0 < r₀ x := by
    filter_upwards [hi0] with x hx
    dsimp [r₀]
    exact lt_min (by norm_num) (add_pos_of_pos_of_nonneg hx (sq_nonneg _))
  have hrle : ∀ᶠ x in l, r x ≤ r₀ x := by
    filter_upwards [hba, hb] with x hba' hb'
    dsimp [r, r₀]
    gcongr
  have hir : ∀ᶠ x in l, i x ≤ r x := by
    filter_upwards [hi0, hi1] with x hi hi'
    dsimp [r]
    apply le_min hi'
    exact le_add_of_nonneg_right (sq_nonneg _)
  have hh0 : ∀ᶠ x in l, 0 < h x := by
    filter_upwards [ha] with x hax
    dsimp [h]
    exact lt_min (by norm_num) hax
  constructor
  · intro ho
    have hratio : Tendsto (fun x ↦ r x / r₀ x) l (nhds 0) := by
      exact ho.tendsto_div_nhds_zero
    have hiratio : Tendsto (fun x ↦ i x / r₀ x) l (nhds 0) := by
      apply squeeze_zero' (g := fun x ↦ r x / r₀ x)
      · filter_upwards [hi0, hr₀0] with x hx hrx
        positivity
      · filter_upwards [hir, hr₀0] with x hx hrx
        exact div_le_div_of_nonneg_right hx hrx.le
      · exact hratio
    refine ⟨by simpa [r₀] using hiratio, ?_⟩
    have hratiolt : ∀ᶠ x in l, r x / r₀ x < 1 :=
      (tendsto_order.1 hratio).2 1 (by norm_num)
    have hr_eq : ∀ᶠ x in l, r x = i x + b x ^ 2 := by
      filter_upwards [hratiolt, hr₀0] with x hx hrx
      have hlt : r x < 1 := lt_of_lt_of_le
        ((div_lt_one hrx).mp hx) (min_le_left _ _)
      dsimp [r] at hlt ⊢
      exact min_eq_right (le_of_not_gt fun hsum ↦ by
        rw [min_eq_left (le_of_lt hsum)] at hlt
        exact (lt_irrefl 1 hlt).elim)
    have hb2ratio : Tendsto (fun x ↦ b x ^ 2 / r₀ x) l (nhds 0) := by
      apply squeeze_zero' (g := fun x ↦ r x / r₀ x)
      · filter_upwards [hr₀0] with x hx
        positivity
      · filter_upwards [hr_eq, hr₀0, hi0] with x hx hrx hix
        rw [hx]
        exact div_le_div_of_nonneg_right (le_add_of_nonneg_left hix.le) hrx.le
      · exact hratio
    have hihr : Tendsto (fun x ↦ i x / h x ^ 2) l (nhds 0) := by
      let q := fun x ↦ i x / r₀ x
      have hq : Tendsto q l (nhds 0) := by simpa [q] using hiratio
      have hfrac : Tendsto (fun x ↦ q x / (1 - q x)) l (nhds 0) := by
        have hden : Tendsto (fun x ↦ 1 - q x) l (nhds 1) := by
          convert tendsto_const_nhds.sub hq using 1 <;> norm_num
        change Tendsto (q / (fun x ↦ 1 - q x)) l (nhds 0)
        simpa only [zero_div] using hq.div hden (by norm_num)
      apply squeeze_zero' (g := fun x ↦ q x / (1 - q x))
      · filter_upwards [hi0, hh0] with x hix hhx
        positivity
      · filter_upwards [hi0, hi1, ha, hr₀0, hh0,
          (tendsto_order.1 hq).2 1 (by norm_num)] with x hix hi1x hax hrx hhx hqx
        have hq0 : 0 ≤ q x := by dsimp [q]; positivity
        have hden : 0 < 1 - q x := sub_pos.mpr hqx
        have hrupper : r₀ x ≤ i x + h x ^ 2 := by
          dsimp [r₀, h]
          rw [min_one_sq_nonnegative hax.le]
          by_cases ha1 : a x ^ 2 ≤ 1
          · rw [min_eq_right ha1]
            exact min_le_right _ _
          · rw [min_eq_left (le_of_not_ge ha1)]
            exact (min_le_left _ _).trans (by linarith)
        rw [div_le_div_iff₀ (sq_pos_of_pos hhx) hden]
        dsimp [q]
        have hrne : r₀ x ≠ 0 := ne_of_gt hrx
        field_simp [hrne]
        nlinarith
      · exact hfrac
    have hrh : Tendsto (fun x ↦ r₀ x / h x ^ 2) l (nhds 1) := by
      apply tendsto_const_nhds.squeeze'
          (show Tendsto (fun x ↦ 1 + i x / h x ^ 2) l (nhds 1) by
            convert tendsto_const_nhds.add hihr using 1 <;> norm_num)
      · filter_upwards [ha, hi0, hi1, hh0] with x hax hix hi1x hhx
        have hh : h x ^ 2 ≤ r₀ x := by
            dsimp [h, r₀]
            rw [min_one_sq_nonnegative hax.le]
            exact min_le_min le_rfl (le_add_of_nonneg_left hix.le)
        exact (le_div_iff₀ (sq_pos_of_pos hhx)).2 (by simpa using hh)
      · filter_upwards [ha, hi0, hi1, hh0] with x hax hix hi1x hhx
        have hrupper : r₀ x ≤ i x + h x ^ 2 := by
            dsimp [r₀, h]
            rw [min_one_sq_nonnegative hax.le]
            by_cases ha1 : a x ^ 2 ≤ 1
            · rw [min_eq_right ha1]
              exact min_le_right _ _
            · rw [min_eq_left (le_of_not_ge ha1)]
              exact (min_le_left _ _).trans (by linarith)
        rw [div_le_iff₀ (sq_pos_of_pos hhx)]
        calc r₀ x ≤ i x + h x ^ 2 := hrupper
          _ = (1 + i x / h x ^ 2) * h x ^ 2 := by field_simp; ring
    have hb2h : Tendsto (fun x ↦ b x ^ 2 / h x ^ 2) l (nhds 0) := by
      have hp := hb2ratio.mul hrh
      simpa only [zero_mul] using hp.congr' (by
        filter_upwards [hr₀0, hh0] with x hrx hhx
        field_simp)
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hb2h
    simpa only [Function.comp_apply, Real.sqrt_zero, h] using hsqrt.congr' (by
      filter_upwards [hb, hh0] with x hbx hhx
      change Real.sqrt (b x ^ 2 / h x ^ 2) = b x / h x
      rw [show b x ^ 2 / h x ^ 2 = (b x / h x) ^ 2 by field_simp,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hbx hhx.le)])
  · rintro ⟨hiratio, hbhratio⟩
    have hb2h : Tendsto (fun x ↦ b x ^ 2 / h x ^ 2) l (nhds 0) := by
      have hp := hbhratio.pow 2
      simpa only [zero_pow (by omega : 2 ≠ 0)] using hp.congr' (by
        filter_upwards [hh0] with x hhx
        dsimp [h]
        field_simp)
    have hb2r : Tendsto (fun x ↦ b x ^ 2 / r₀ x) l (nhds 0) := by
      apply squeeze_zero' (g := fun x ↦ b x ^ 2 / h x ^ 2)
      · filter_upwards [hr₀0] with x hx
        positivity
      · filter_upwards [ha, hi0, hr₀0, hh0] with x hax hix hrx hhx
        apply div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hhx)
        dsimp [h, r₀]
        rw [min_one_sq_nonnegative hax.le]
        exact min_le_min le_rfl (le_add_of_nonneg_left hix.le)
      · exact hb2h
    have hsum := hiratio.add hb2r
    have hrat : Tendsto (fun x ↦ r x / r₀ x) l (nhds 0) := by
      apply squeeze_zero' (g := fun x ↦ i x / r₀ x + b x ^ 2 / r₀ x)
      · filter_upwards [hr0, hr₀0] with x hx hrx
        positivity
      · filter_upwards [hr₀0] with x hrx
        dsimp [r]
        rw [← add_div]
        exact div_le_div_of_nonneg_right (min_le_right _ _) hrx.le
      · simpa [r₀] using hsum
    apply isLittleO_of_tendsto'
    · filter_upwards [hr₀0] with x hx
      intro hzero
      exact (hx.ne' hzero).elim
    · simpa [r, r₀] using hrat

-- @node: supervised_floor_ratio_iff
/-- [the stated conditions](hyp:hd) establishes [the stated conclusion](goal). -/
lemma supervised_floor_ratio_iff (dSeq : Nat → Nat)
    (hd : ∀ n, 1 ≤ n → 2 ≤ dSeq n) :
    Tendsto (fun n : Nat ↦ (1 / (n : Real)) / frontierRate n 0 (dSeq n))
        atTop (nhds 0) ↔
      Tendsto (fun n ↦ (dSeq n : Real) / (Real.sqrt n * logEN n))
        atTop atTop := by
  let i : Nat → Real := fun n ↦ 1 / (n : Real)
  let a : Nat → Real := fun n ↦ (dSeq n : Real) / ((n : Real) * logEN n)
  let s : Nat → Real := fun n ↦ (dSeq n : Real) / (Real.sqrt n * logEN n)
  let r₀ : Nat → Real := fun n ↦ frontierRate n 0 (dSeq n)
  have hformula : ∀ n, r₀ n = min 1 (i n + a n ^ 2) := by
    intro n
    simpa [r₀, i, a] using frontierRate_sequence_formula (fun _ ↦ 0) dSeq n
  have hpoint : ∀ n, 1 ≤ n →
      i n / (i n + a n ^ 2) = 1 / (1 + s n ^ 2) := by
    intro n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hsqrt : 0 < Real.sqrt (n : Real) := Real.sqrt_pos.2 hnR
    have hlog := logEN_pos_of_one_le n hn
    have hdR : (0 : Real) < dSeq n := by
      exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) (hd n hn)
    dsimp [i, a, s]
    field_simp [hnR.ne', hsqrt.ne', hlog.ne', hdR.ne']
    rw [Real.sq_sqrt hnR.le]
    ring
  have hipos : ∀ᶠ n in atTop, 0 < i n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [i]
    positivity
  have hapos : ∀ᶠ n in atTop, 0 < a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [a]
    exact div_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n hn)))
      (mul_pos (by exact_mod_cast hn) (logEN_pos_of_one_le n hn))
  have hrpos : ∀ᶠ n in atTop, 0 < r₀ n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (frontierRate_mem_Ioc_zero_one n 0 (dSeq n) hn).1
  constructor
  · intro hq
    have hq' : Tendsto (fun n ↦ i n / r₀ n) atTop (nhds 0) := by
      simpa [i, r₀] using hq
    rw [Filter.tendsto_atTop]
    intro M
    let K : Real := max M 0 + 1
    have hK : 0 < K := by dsimp [K]; linarith [le_max_right M 0]
    have hthreshold : 0 < 1 / (1 + K ^ 2) := by positivity
    have hevent : ∀ᶠ n in atTop, i n / r₀ n < 1 / (1 + K ^ 2) :=
      (tendsto_order.1 hq').2 _ hthreshold
    filter_upwards [eventually_ge_atTop 1, hevent] with n hn hsmall
    have hi : 0 < i n := by dsimp [i]; positivity
    have hr : 0 < r₀ n := (frontierRate_mem_Ioc_zero_one n 0 (dSeq n) hn).1
    have ha0 : 0 ≤ a n := by
      dsimp [a]
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (logEN_pos_of_one_le n hn).le)
    have hrupper : r₀ n ≤ i n + a n ^ 2 := by
      rw [hformula]
      exact min_le_right _ _
    have hlower : 1 / (1 + s n ^ 2) ≤ i n / r₀ n := by
      rw [← hpoint n hn]
      exact div_le_div_of_nonneg_left hi.le hr hrupper
    by_contra hMs
    have hsK : s n < K := (lt_of_not_ge hMs).trans_le (by
      dsimp [K]
      linarith [le_max_left M 0])
    have hs0 : 0 ≤ s n := by
      dsimp [s]
      exact div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) (logEN_pos_of_one_le n hn).le)
    have hden : 1 + s n ^ 2 < 1 + K ^ 2 := by nlinarith
    have hinv : 1 / (1 + K ^ 2) < 1 / (1 + s n ^ 2) := by
      exact one_div_lt_one_div_of_lt (by positivity) hden
    linarith
  · intro hs
    have hiZero : Tendsto i atTop (nhds 0) := by
      dsimp [i]
      simpa [one_div, Function.comp_def] using
        tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hsSq : Tendsto (fun n ↦ s n ^ 2) atTop atTop := by
      simpa [s, pow_two, Function.comp_def] using Filter.tendsto_mul_self_atTop.comp hs
    have hsInv : Tendsto (fun n ↦ 1 / s n ^ 2) atTop (nhds 0) := by
      simpa [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hsSq
    have hbound : ∀ᶠ n in atTop,
        i n / r₀ n ≤ i n + 1 / s n ^ 2 := by
      filter_upwards [eventually_ge_atTop 1, hipos, hapos, hrpos] with n hn hi ha hr
      have hs0 : 0 < s n := by
        dsimp [s]
        exact div_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n hn)))
          (mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hn)) (logEN_pos_of_one_le n hn))
      rw [hformula]
      let h : Real := min 1 (a n)
      have hh : 0 < h := lt_min (by norm_num) ha
      have hhRate : h ^ 2 ≤ min 1 (i n + a n ^ 2) := by
        dsimp [h]
        rw [min_one_sq_nonnegative ha.le]
        exact min_le_min le_rfl (le_add_of_nonneg_left hi.le)
      have hfirst : i n / min 1 (i n + a n ^ 2) ≤ i n / h ^ 2 :=
        div_le_div_of_nonneg_left hi.le (sq_pos_of_pos hh) hhRate
      apply hfirst.trans
      by_cases ha1 : a n ≤ 1
      · have hhEq : h = a n := min_eq_right ha1
        rw [hhEq]
        have heq : i n / a n ^ 2 = 1 / s n ^ 2 := by
          have hnR : (0 : Real) < n := by exact_mod_cast hn
          have hsqrt := Real.sqrt_pos.2 hnR
          have hlog := logEN_pos_of_one_le n hn
          have hdR : (0 : Real) < dSeq n := by
            exact_mod_cast lt_of_lt_of_le (by omega : 0 < 2) (hd n hn)
          dsimp [i, a, s]
          field_simp [hnR.ne', hsqrt.ne', hlog.ne', hdR.ne']
          rw [Real.sq_sqrt hnR.le]
        rw [heq]
        exact le_add_of_nonneg_left hi.le
      · have hhEq : h = 1 := min_eq_left (le_of_not_ge ha1)
        simp only [hhEq, one_pow, div_one]
        exact le_add_of_nonneg_right
          (one_div_nonneg.mpr (sq_nonneg (s n)))
    have hnonneg : ∀ᶠ n in atTop, 0 ≤ i n / r₀ n := by
      filter_upwards [hipos, hrpos] with n hi hr
      positivity
    have hzero : Tendsto (fun n ↦ i n / r₀ n) atTop (nhds 0) := by
      apply squeeze_zero' hnonneg hbound
      convert hiZero.add hsInv using 1 <;> norm_num
    simpa [i, r₀] using hzero

-- @node: annotation_frontier_strict_improvement_iff
/-- [the stated conditions](hyp:hd) establishes [the stated conclusion](goal). -/
lemma annotation_frontier_strict_improvement_iff
    (mSeq dSeq : Nat → Nat) (hd : ∀ n, 1 ≤ n → 2 ≤ dSeq n) :
    (fun n ↦ frontierRate n (mSeq n) (dSeq n)) =o[atTop]
        (fun n ↦ frontierRate n 0 (dSeq n)) ↔
      Tendsto (fun n ↦ (dSeq n : Real) / (Real.sqrt n * logEN n)) atTop atTop ∧
      Tendsto (fun n ↦
        ((dSeq n : Real) / (((n + mSeq n : Nat) : Real) * logEN n)) /
          min 1 ((dSeq n : Real) / ((n : Real) * logEN n))) atTop (nhds 0) := by
  let i : Nat → Real := fun n ↦ 1 / (n : Real)
  let a : Nat → Real := fun n ↦ (dSeq n : Real) / ((n : Real) * logEN n)
  let b : Nat → Real := fun n ↦ (dSeq n : Real) /
    (((n + mSeq n : Nat) : Real) * logEN n)
  have hi0 : ∀ᶠ n in atTop, 0 < i n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [i]
    positivity
  have hi1 : ∀ᶠ n in atTop, i n ≤ 1 := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [i]
    exact (div_le_one (by positivity)).2 (by exact_mod_cast hn)
  have ha : ∀ᶠ n in atTop, 0 < a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [a]
    exact div_pos (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) (hd n hn)))
      (mul_pos (by exact_mod_cast hn) (logEN_pos_of_one_le n hn))
  have hb : ∀ᶠ n in atTop, 0 ≤ b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [b]
    have hN : (0 : Real) < (n + mSeq n : Nat) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < n) (Nat.le_add_right n _))
    exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg hN.le (logEN_pos_of_one_le n hn).le)
  have hba : ∀ᶠ n in atTop, b n ≤ a n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    dsimp [a, b]
    have hnpos : (0 : Real) < n := by exact_mod_cast hn
    have hlog := logEN_pos_of_one_le n hn
    have hN : (n : Real) ≤ (n + mSeq n : Nat) := by exact_mod_cast Nat.le_add_right n (mSeq n)
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hnpos hlog)
      (mul_le_mul_of_nonneg_right hN hlog.le)
  have hgeneric := strict_min_rates_iff_ratios i a b hi0 hi1 ha hb hba
  rw [show (fun n ↦ frontierRate n (mSeq n) (dSeq n)) =
      (fun n ↦ min 1 (i n + b n ^ 2)) by
        funext n; exact frontierRate_sequence_formula mSeq dSeq n,
    show (fun n ↦ frontierRate n 0 (dSeq n)) =
      (fun n ↦ min 1 (i n + a n ^ 2)) by
        funext n
        simpa [i, a] using frontierRate_sequence_formula (fun _ ↦ 0) dSeq n]
  rw [hgeneric]
  have hfloorEq :
      (fun n ↦ i n / min 1 (i n + a n ^ 2)) =
        (fun n : Nat ↦ (1 / (n : Real)) / frontierRate n 0 (dSeq n)) := by
    funext n
    simp only [i, a]
    rw [frontierRate]
    simp only [Nat.add_zero]
    congr 2
    ring
  constructor
  · rintro ⟨hfloor, haux⟩
    refine ⟨(supervised_floor_ratio_iff dSeq hd).1 ?_, ?_⟩
    · rw [← hfloorEq]
      exact hfloor
    · simpa [a, b] using haux
  · rintro ⟨hfloor, haux⟩
    refine ⟨?_, ?_⟩
    · rw [hfloorEq]
      exact (supervised_floor_ratio_iff dSeq hd).2 hfloor
    · simpa [a, b] using haux

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
