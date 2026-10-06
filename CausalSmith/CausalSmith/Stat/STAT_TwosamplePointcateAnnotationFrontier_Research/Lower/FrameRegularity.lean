module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Lower.Frames
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Uniform low-order Hölder bounds for the signed, locally supported tensor frames. -/

public section
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The piecewise frame equals a globally smooth product of two transition factors.  Given [the specified input z](hyp:z), [the specified input t](hyp:t), [the frame1d product conclusion](goal) holds. -/
lemma frame1d_product (z : ℤ) (t : ℝ) :
    frame1d z t = Real.sin (frameAngle (t-z+1)) * Real.cos (frameAngle (t-z)) := by
  unfold frame1d
  simp only [frameAngle]
  split_ifs with hl hr
  · rw [Real.smoothTransition.zero_of_nonpos (x := t-z) (by linarith [hl.2]),
      mul_zero, Real.cos_zero, mul_one]
  · rw [Real.smoothTransition.one_of_one_le (x := t-z+1) (by linarith [hr.1]),
      mul_one, Real.sin_pi_div_two, one_mul]
  · by_cases ht : t < (z:ℝ)-1
    · rw [Real.smoothTransition.zero_of_nonpos (x := t-z+1) (by linarith),
        mul_zero, Real.sin_zero, zero_mul]
    · have ht' : (z:ℝ)+1 < t := by
        by_contra hn
        apply hr
        refine ⟨?_, le_of_not_gt hn⟩
        by_contra h
        apply hl
        exact ⟨le_of_not_gt ht, le_of_lt (lt_of_not_ge h)⟩
      rw [Real.smoothTransition.one_of_one_le (x := t-z) (by linarith),
        mul_one, Real.cos_pi_div_two, mul_zero]

/-- Translations of the fixed smooth frame share a single Lipschitz constant.  [the frame1d uniform lipschitz conclusion](goal) holds. -/
lemma frame1d_uniform_lipschitz :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℤ, ∀ t u : ℝ,
      |frame1d z t-frame1d z u| ≤ K*|t-u| := by
  have hf : ContDiff ℝ 1 (frame1d 0) := by
    change ContDiff ℝ 1 (fun t => frame1d 0 t)
    simp_rw [frame1d_product]
    unfold frameAngle
    fun_prop
  have hc : HasCompactSupport (frame1d 0) := by
    apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (-1:ℝ) 1))
    intro t ht
    rcases (not_and_or.mp ht) with ht | ht
    · exact frame1d_zero_left 0 t (by simpa using (le_of_lt (lt_of_not_ge ht)))
    · exact frame1d_zero_right 0 t (by simpa using (le_of_lt (lt_of_not_ge ht)))
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hf (by norm_num)
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro z t u
  have he (v : ℝ) : frame1d z v = frame1d 0 (v-z) := by
    simp_rw [frame1d_product]
    simp
  rw [he, he]
  simpa [Real.dist_eq, sub_sub_sub_cancel_right] using hK.dist_le_mul (t-z) (u-z)

/-- Products of unit-bounded factors have a telescoping difference bound.  Given [the specified input s](hyp:s), [the specified input f](hyp:f), [the specified input g](hyp:g), [the specified input hf](hyp:hf), [the specified input hg](hyp:hg), [the unit product difference le conclusion](goal) holds. -/
lemma unit_product_difference_le {ι : Type*} (s : Finset ι) (f g : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ 1) (hg : ∀ i ∈ s, |g i| ≤ 1) :
    |(∏ i ∈ s, f i)-(∏ i ∈ s, g i)| ≤ ∑ i ∈ s, |f i-g i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi]
    have hfp : |∏ j ∈ s, f j| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have hgp : |g i| ≤ 1 := hg i (Finset.mem_insert_self _ _)
    have hid := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hg j (Finset.mem_insert_of_mem hj))
    calc
      _ = |(f i-g i)*(∏ j ∈ s, f j)+g i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j))| := by congr 1; ring
      _ ≤ |(f i-g i)*(∏ j ∈ s, f j)|+|g i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j))| := abs_add_le _ _
      _ ≤ |f i-g i| + ∑ j ∈ s, |f j-g j| := by
        rw [abs_mul, abs_mul]
        exact add_le_add (by nlinarith [abs_nonneg (f i-g i)])
          ((mul_le_mul_of_nonneg_right hgp (abs_nonneg _)).trans (by simpa using hid))

/-- The dilated macro bump has a dimension-only Lipschitz bound at scale h.  Given [the specified input d](hyp:d), [the macro bump uniform lipschitz conclusion](goal) holds. -/
lemma macroBump_uniform_lipschitz (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h, 0 < h → ∀ x y : Cov d,
      |macroBump h x-macroBump h y| ≤ K/h*dist x y := by
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (macroBump_compactSupport d) (macroBump_contDiff 1) (by simp)
  refine ⟨K, K.coe_nonneg, ?_⟩
  intro h hh x y
  rw [← macroBump_dilation h x, ← macroBump_dilation h y]
  have hdist : dist (h⁻¹ • (x-x0 d)+x0 d) (h⁻¹ • (y-x0 d)+x0 d) =
      h⁻¹*dist x y := by
    rw [dist_add_right, dist_eq_norm, ← smul_sub,
      sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh),
      ← dist_eq_norm]
  have hb := hK.dist_le_mul (h⁻¹ • (x-x0 d)+x0 d) (h⁻¹ • (y-x0 d)+x0 d)
  rw [Real.dist_eq, hdist] at hb
  simpa only [div_eq_mul_inv, mul_assoc] using hb

/-- Each tensor frame has a Lipschitz bound uniform over its integer translate.  Given [the specified input d](hyp:d), [the frame uniform lipschitz conclusion](goal) holds. -/
lemma frame_uniform_lipschitz (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h delta, 0 < delta → delta ≤ h →
      ∀ z : Fin d → ℤ, ∀ x y : Cov d,
        |frame h delta z x-frame h delta z y| ≤ K/delta*dist x y := by
  obtain ⟨B, hB, hb⟩ := macroBump_uniform_lipschitz d
  obtain ⟨A, hA, ha⟩ := frame1d_uniform_lipschitz
  refine ⟨B+d*A, by positivity, ?_⟩
  intro h delta hd hdh z x y
  let f := fun i : Fin d => frame1d (z i) ((x i-1/2)/delta)
  let g := fun i : Fin d => frame1d (z i) ((y i-1/2)/delta)
  have hdiff : |(∏ i, f i)-(∏ i, g i)| ≤ (d:ℝ)*(A/delta*dist x y) := by
    calc
      _ ≤ ∑ i, |f i-g i| := unit_product_difference_le Finset.univ f g
        (fun i _ => abs_frame1d_le_one _ _) (fun i _ => abs_frame1d_le_one _ _)
      _ ≤ ∑ _ : Fin d, A/delta*dist x y := by
        apply Finset.sum_le_sum
        intro i _
        have hi := ha (z i) ((x i-1/2)/delta) ((y i-1/2)/delta)
        have he : |(x i-1/2)/delta-(y i-1/2)/delta| = |x i-y i|/delta := by
          rw [← sub_div, sub_sub_sub_cancel_right, abs_div, abs_of_pos hd]
        rw [he] at hi
        have hc : |x i-y i| ≤ dist x y := by
          simpa only [Real.dist_eq] using PiLp.dist_apply_le x y i
        exact hi.trans (by
          calc
            A*(|x i-y i|/delta) = A/delta*|x i-y i| := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hc (by positivity))
      _ = _ := by simp
  have hfp : |∏ i, f i| ≤ 1 := by
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun _ _ => abs_frame1d_le_one _ _)
  have hmy : |macroBump h y| ≤ 1 := by
    rw [abs_of_nonneg (macroBump_mem h y).1]
    exact (macroBump_mem h y).2
  have hmacro := hb h (hd.trans_le hdh) x y
  have hden : B/h ≤ B/delta := div_le_div_of_nonneg_left hB hd hdh
  calc
    _ = |(macroBump h x-macroBump h y)*(∏ i, f i)+
        macroBump h y*((∏ i, f i)-(∏ i, g i))| := by
      dsimp [frame, f, g]; congr 1; ring
    _ ≤ |macroBump h x-macroBump h y| *|∏ i, f i|+
        |macroBump h y| *|(∏ i, f i)-(∏ i, g i)| := by
      simpa only [abs_mul] using abs_add_le
        ((macroBump h x-macroBump h y)*(∏ i, f i))
        (macroBump h y*((∏ i, f i)-(∏ i, g i)))
    _ ≤ B/delta*dist x y+(d:ℝ)*(A/delta*dist x y) :=
      add_le_add
        ((mul_le_mul_of_nonneg_left hfp (abs_nonneg _)).trans
          (by simpa using hmacro.trans (mul_le_mul_of_nonneg_right hden (dist_nonneg))))
        ((mul_le_mul_of_nonneg_right hmy (abs_nonneg _)).trans (by simpa using hdiff))
    _ = _ := by ring

/-- Bounded overlap at the two endpoints controls signed-frame differences independently of grid size.  Given [the specified input d](hyp:d), [the sign field uniform lipschitz conclusion](goal) holds. -/
lemma signField_uniform_lipschitz (d : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h delta, 0 < delta → delta ≤ h →
      ∀ sigma : SignArray d h delta, ∀ control, ∀ x y : Cov d,
        |signField h delta sigma control x-signField h delta sigma control y| ≤
          K/delta*dist x y := by
  classical
  obtain ⟨B, hB, hb⟩ := frame_uniform_lipschitz d
  refine ⟨2*(2:ℝ)^d*B, by positivity, ?_⟩
  intro h delta hd hdh sigma control x y
  let A := fun x : Cov d => Finset.univ.image (fun v : Fin d → Bool =>
    fun i => ⌊(x i-1/2)/delta⌋ + if v i then 1 else 0)
  have hcard (x : Cov d) : (A x).card ≤ 2^d := by
    exact (Finset.card_image_le).trans (by simp)
  have hzero (x : Cov d) (z : Fin d → ℤ) (hz : z ∉ A x) : frame h delta z x = 0 := by
    apply frame_zero_of_not_coordinate_adjacent
    intro hadj
    apply hz
    apply Finset.mem_image.mpr
    refine ⟨fun i => decide (z i = ⌊(x i-1/2)/delta⌋+1), Finset.mem_univ _, ?_⟩
    funext i
    rcases hadj i with hi | hi <;> simp [hi]
  let S := (frameIdx d h delta).filter (fun z => z ∈ A x ∪ A y)
  have hScard : (S.card:ℝ) ≤ 2*(2:ℝ)^d := by
    have hc : S.card ≤ 2*2^d :=
      (Finset.card_le_card (show S ⊆ A x ∪ A y from fun z hz => (Finset.mem_filter.mp hz).2)).trans
        ((Finset.card_union_le _ _).trans (by have hx := hcard x; have hy := hcard y; omega))
    exact_mod_cast hc
  have he :
      (∑ z ∈ frameIdx d h delta, |frame h delta z x-frame h delta z y|) =
      ∑ z ∈ S, |frame h delta z x-frame h delta z y| := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    split_ifs with hz
    · rfl
    · have hn := not_or.mp (show ¬ (z ∈ A x ∨ z ∈ A y) by simpa using hz)
      simp [hzero x z hn.1, hzero y z hn.2]
  calc
    _ ≤ ∑ z : {z // z ∈ frameIdx d h delta}, |frame h delta z.1 x-frame h delta z.1 y| := by
      unfold signField
      rw [← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ z : {z // z ∈ frameIdx d h delta},
            |thetaSign (if control then (sigma z).2 else (sigma z).1) *
              frame h delta z.1 x-thetaSign (if control then (sigma z).2 else (sigma z).1)*frame h delta z.1 y| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z _
          rw [← mul_sub, abs_mul]
          have ht : |thetaSign (if control then (sigma z).2 else (sigma z).1)| = 1 := by
            unfold thetaSign
            split_ifs <;> norm_num
          rw [ht, one_mul]
    _ = ∑ z ∈ S, |frame h delta z x-frame h delta z y| := by
      exact (Finset.sum_coe_sort (frameIdx d h delta)
        (fun z => |frame h delta z x-frame h delta z y|)).trans he
    _ ≤ ∑ _ ∈ S, B/delta*dist x y :=
      Finset.sum_le_sum (fun z _ => hb h delta hd hdh z x y)
    _ = (S.card:ℝ)*(B/delta*dist x y) := by simp
    _ ≤ (2*(2:ℝ)^d)*(B/delta*dist x y) :=
      mul_le_mul_of_nonneg_right hScard (by positivity)
    _ = _ := by ring

/-- A coordinate partial of total order zero is the original function.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hk](hyp:hk), [the specified input x](hyp:x), [the coordinate partial order zero conclusion](goal) holds. -/
lemma coordinatePartial_order_zero {d : ℕ} (f : Cov d → ℝ) (κ : Fin d → ℕ)
    (hk : multiOrder κ = 0) (x : Cov d) : coordinatePartial f κ x = f x := by
  have he (k : ℕ) (h : k = 0) (v : Fin k → Cov d) :
      (iteratedFDerivWithin ℝ k f (cube d) x) v = f x := by
    subst k
    simp
  exact he _ hk _

/-- A bounded field with a scale-dependent Lipschitz bound has the corresponding fractional Hölder norm.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input s](hyp:s), [the specified input delta](hyp:delta), [the specified input B](hyp:B), [the specified input K](hyp:K), [the specified input hs](hyp:hs), [the specified input hs1](hyp:hs1), [the specified input hd](hyp:hd), [the specified input hd1](hyp:hd1), [the specified input hB](hyp:hB), [the specified input hK](hyp:hK), [the specified input hb](hyp:hb), [the specified input hlip](hyp:hlip), [the bounded lipschitz scaled holder conclusion](goal) holds. -/
lemma bounded_lipschitz_scaled_holder {d : ℕ} (f : Cov d → ℝ)
    (s delta B K : ℝ) (hs : 0 < s) (hs1 : s ≤ 1) (hd : 0 < delta) (hd1 : delta ≤ 1)
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hb : ∀ x, |f x| ≤ B)
    (hlip : ∀ x y, |f x-f y| ≤ K/delta*dist x y) :
    holderNorm f s ≤ ENNReal.ofReal ((2*B+K+1)*delta^(-s)) := by
  let C := 2*B+K+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hceil : Nat.ceil s - 1 = 0 := by
    have hle : Nat.ceil s ≤ 1 := Nat.ceil_le.mpr (by simpa using hs1)
    omega
  have hscale : 1 ≤ delta^(-s) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  have hcont : Continuous f := by
    have hl : LipschitzWith ⟨K/delta, by positivity⟩ f :=
      LipschitzWith.of_dist_le_mul (by intro x y; exact hlip x y)
    exact hl.continuous
  apply (holderNorm_le_iff f s (C*delta^(-s)) (by positivity)).mpr
  refine ⟨?_, ?_, ?_⟩
  · rw [hceil]
    exact (contDiff_zero.mpr hcont).contDiffOn
  · intro κ hκ x hx
    have hk : multiOrder κ = 0 := by omega
    rw [coordinatePartial_order_zero f κ hk]
    calc
      _ ≤ B := hb x
      _ ≤ C := by dsimp [C]; linarith
      _ ≤ C*delta^(-s) := by nlinarith
  · intro κ hκ x hx y hy hxy
    have hk : multiOrder κ = 0 := by omega
    rw [coordinatePartial_order_zero f κ hk, coordinatePartial_order_zero f κ hk,
      hceil]
    simp only [Nat.cast_zero, sub_zero]
    let r := dist x y
    have hr : 0 ≤ r := dist_nonneg
    have he : (r/delta)^s = delta^(-s)*r^s := by
      rw [Real.div_rpow hr hd.le, Real.rpow_neg hd.le]
      ring
    by_cases hrd : r ≤ delta
    · have hp : r/delta ≤ (r/delta)^s :=
        Real.self_le_rpow_of_le_one (by positivity) ((div_le_one hd).mpr hrd) hs1
      calc
        _ ≤ K/delta*r := hlip x y
        _ = K*(r/delta) := by ring
        _ ≤ K*(r/delta)^s := mul_le_mul_of_nonneg_left hp hK
        _ = K*(delta^(-s)*r^s) := by rw [he]
        _ ≤ C*(delta^(-s)*r^s) := mul_le_mul_of_nonneg_right
          (by dsimp [C]; linarith) (by positivity)
        _ = _ := by ring
    · have hp : 1 ≤ (r/delta)^s :=
        Real.one_le_rpow ((one_le_div hd).mpr (le_of_lt (lt_of_not_ge hrd))) hs.le
      calc
        _ ≤ |f x|+|f y| := abs_sub _ _
        _ ≤ 2*B := by linarith [hb x, hb y]
        _ ≤ C := by dsimp [C]; linarith
        _ ≤ C*(r/delta)^s := by nlinarith
        _ = _ := by rw [he]; ring

/-- Signed frames obey the prescribed exact Hölder norm uniformly in the sign array and grid size.  Given [the specified input d](hyp:d), [the specified input s](hyp:s), [the specified input hs](hyp:hs), [the specified input hs'](hyp:hs'), [the sign field holder conclusion](goal) holds. -/
lemma signField_holder (d : ℕ) (s : ℝ) (hs : 0 < s) (hs' : s ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ -- @realizes C(finite positive claim-local constant)
       ∀ h delta, 0 < delta → delta ≤ h → h ≤ 1/2 →
      ∀ sigma : SignArray d h delta, ∀ control,
        holderNorm (signField h delta sigma control) s ≤ ENNReal.ofReal (C*delta^(-s)) := by
  obtain ⟨K, hK, hlip⟩ := signField_uniform_lipschitz d
  refine ⟨2*(2:ℝ)^d+K+1, by positivity, ?_⟩
  intro h delta hd hdh hh sigma control
  exact bounded_lipschitz_scaled_holder (signField h delta sigma control)
    s delta ((2:ℝ)^d) K hs hs' hd (by linarith) (by positivity) hK
    (abs_signField_le h delta sigma control) (hlip h delta hd hdh sigma control)

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
