module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Basic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.Algebra.Support

/-! # Hölder bounds for dilated smooth compact profiles

Global derivative bounds and a bounded/Lipschitz interpolation argument give
uniform bounds in the paper's exact coordinate-partial Hölder norm.
-/

public section
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- The direction list has a dimension-only bound, sufficient for multilinear estimates.  Given [the specified input d](hyp:d), [the specified input k](hyp:k), [the coordinate directions norm le conclusion](goal) holds. -/
lemma coordinateDirections_norm_le {d : ℕ} (κ : Fin d → ℕ) (k : Fin (multiOrder κ)) :
    ‖coordinateDirections κ k‖ ≤ (d : ℝ) := by
  unfold coordinateDirections
  calc
    _ ≤ ∑ i : Fin d, ‖if (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) ≤ k.val ∧
        k.val < (∑ j ∈ Finset.univ.filter (fun j => j < i), κ j) + κ i
        then EuclideanSpace.single i (1 : ℝ) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> simp
    _ = _ := by simp

/-- A smooth compact profile has globally bounded derivatives at each fixed order.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hs](hyp:hs), [the specified input j](hyp:j), [the compact profile derivative bound conclusion](goal) holds. -/
lemma compact_profile_derivative_bound {d : ℕ} (f : Cov d → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hs : HasCompactSupport f) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ j f) :=
    hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hs.iteratedFDeriv j)
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

/-- Bounded smooth derivatives interpolate to a global fractional Hölder modulus.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hs](hyp:hs), [the specified input j](hyp:j), [the specified input a](hyp:a), [the specified input ha](hyp:ha), [the specified input ha1](hyp:ha1), [the compact profile derivative modulus conclusion](goal) holds. -/
lemma compact_profile_derivative_modulus {d : ℕ} (f : Cov d → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hs : HasCompactSupport f)
    (j : ℕ) (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ C * ‖x-y‖^a := by
  obtain ⟨B, hB0, hB⟩ := compact_profile_derivative_bound f hf hs j
  obtain ⟨L, hL0, hL⟩ := compact_profile_derivative_bound f hf hs (j+1)
  let A := max B L
  have hA : 0 ≤ A := hB0.trans (le_max_left _ _)
  refine ⟨2*A, by positivity, ?_⟩
  intro x y
  have hlip : ‖iteratedFDeriv ℝ j f x - iteratedFDeriv ℝ j f y‖ ≤ A * ‖x-y‖ := by
    apply Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ)
      (x := y) (y := x) (𝕜 := ℝ) (f := iteratedFDeriv ℝ j f)
    · intro z _
      exact hf.contDiffAt.differentiableAt_iteratedFDeriv (by exact_mod_cast (show (j : ℕ∞) < ⊤ by simp))
    · intro z _
      rw [norm_fderiv_iteratedFDeriv]
      exact (hL z).trans (le_max_right _ _)
    · exact convex_univ
    · trivial
    · trivial
  by_cases hr : ‖x-y‖ ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (norm_nonneg (x-y)) hr ha1
    calc
      _ ≤ A * ‖x-y‖ := hlip
      _ ≤ A * ‖x-y‖^a := mul_le_mul_of_nonneg_left hp hA
      _ ≤ _ := by nlinarith [Real.rpow_nonneg (norm_nonneg (x-y)) a]
  · have hp := Real.one_le_rpow (le_of_lt (lt_of_not_ge hr)) ha.le
    calc
      _ ≤ ‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j f y‖ := norm_sub_le _ _
      _ ≤ 2*A := by dsimp [A]; linarith [hB x, hB y, le_max_left B L]
      _ ≤ _ := by nlinarith

/-- Translation and dilation give the exact derivative scaling of a profile.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input h](hyp:h), [the specified input j](hyp:j), [the specified input x](hyp:x), [the dilated profile derivative conclusion](goal) holds. -/
lemma dilated_profile_derivative {d : ℕ} (f : Cov d → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (h : ℝ) (j : ℕ) (x : Cov d) :
    iteratedFDeriv ℝ j (fun z => f (h⁻¹ • (z-x0 d))) x =
      (h⁻¹)^j • iteratedFDeriv ℝ j f (h⁻¹ • (x-x0 d)) := by
  rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun z => f (h⁻¹ • z)) j (x0 d) x]
  exact congrFun (iteratedFDeriv_comp_const_smul h⁻¹
    (hf.of_le (WithTop.coe_le_coe.mpr le_top))) _

/-- The exact coordinate partial is controlled by the ambient derivative operator norm.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input x](hyp:x), [the specified input hx](hyp:hx), [the coordinate partial le operator conclusion](goal) holds. -/
lemma coordinatePartial_le_operator {d : ℕ} (f : Cov d → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (κ : Fin d → ℕ)
    (x : Cov d) (hx : x ∈ cube d) :
    |coordinatePartial f κ x| ≤
      ‖iteratedFDeriv ℝ (multiOrder κ) f x‖ * (d : ℝ)^(multiOrder κ) := by
  unfold coordinatePartial
  rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d)
    (hf.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt hx]
  change ‖(iteratedFDeriv ℝ (multiOrder κ) f x) (coordinateDirections κ)‖ ≤ _
  calc
    _ ≤ ‖iteratedFDeriv ℝ (multiOrder κ) f x‖ * ∏ i, ‖coordinateDirections κ i‖ :=
      (iteratedFDeriv ℝ (multiOrder κ) f x).le_opNorm _
    _ ≤ _ := by
      have hd := Finset.prod_le_prod (s := Finset.univ) (fun i _ => norm_nonneg (coordinateDirections κ i))
        (fun i _ => coordinateDirections_norm_le κ i)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        mul_le_mul_of_nonneg_left hd (norm_nonneg (iteratedFDeriv ℝ (multiOrder κ) f x))

/-- Smooth compact profiles obey the exact Hölder norm bound after dilation.  Given [the specified input d](hyp:d), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input hsupp](hyp:hsupp), [the specified input s](hyp:s), [the specified input hs](hyp:hs), [the compact profile scaled holder conclusion](goal) holds. -/
lemma compact_profile_scaled_holder {d : ℕ} (f : Cov d → ℝ)
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hsupp : HasCompactSupport f)
    (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∀ h, 0 < h → h ≤ 1 →
      holderNorm (fun x => f (h⁻¹ • (x-x0 d))) s ≤ ENNReal.ofReal (C*h^(-s)) := by
  let m := Nat.ceil s - 1
  let a := s - (m : ℝ)
  have hm : (m : ℝ) < s := Nat.lt_ceil.mp (by
    have := Nat.ceil_pos.mpr hs
    dsimp [m]
    omega)
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a ≤ 1 := by
    have hc := Nat.le_ceil s
    have he : m+1 = Nat.ceil s := by
      dsimp [m]
      have := Nat.ceil_pos.mpr hs
      omega
    have heR : (m : ℝ)+1 = (Nat.ceil s : ℝ) := by exact_mod_cast he
    dsimp [a]
    linarith
  let D : ℕ → ℝ := fun j => (compact_profile_derivative_bound f hf hsupp j).choose
  have hD0 (j) : 0 ≤ D j := (compact_profile_derivative_bound f hf hsupp j).choose_spec.1
  have hD (j x) : ‖iteratedFDeriv ℝ j f x‖ ≤ D j :=
    (compact_profile_derivative_bound f hf hsupp j).choose_spec.2 x
  obtain ⟨M, hM0, hM⟩ := compact_profile_derivative_modulus f hf hsupp m a ha ha1
  let B := ∑ j ∈ Finset.range (m+1), D j * (d : ℝ)^j
  let C := B + M*(d : ℝ)^m + 1
  have hB : 0 ≤ B := Finset.sum_nonneg (fun j _ => by exact mul_nonneg (hD0 j) (pow_nonneg (Nat.cast_nonneg _) _))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro h hh hh1
  let g : Cov d → ℝ := fun x => f (h⁻¹ • (x-x0 d))
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := hf.comp (by fun_prop)
  have hCB : B ≤ C := by dsimp [C]; linarith [mul_nonneg hM0 (pow_nonneg (Nat.cast_nonneg d) m)]
  have hCM : M*(d : ℝ)^m ≤ C := by dsimp [C]; linarith
  apply (holderNorm_le_iff g s (C*h^(-s)) (by positivity)).mpr
  refine ⟨(hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn, ?_, ?_⟩
  · intro κ hκ x hx
    let j := multiOrder κ
    have hj : j ≤ m := hκ
    have hjB : D j * (d : ℝ)^j ≤ B := by
      apply Finset.single_le_sum (f := fun i => D i * (d : ℝ)^i)
      · intro i _
        exact mul_nonneg (hD0 i) (by positivity)
      · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hj)
    have hscale : (h⁻¹)^j ≤ h^(-s) := by
      rw [inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hh.le]
      apply Real.rpow_le_rpow_of_exponent_ge hh hh1
      have hjR : (j : ℝ) ≤ m := by exact_mod_cast hj
      linarith
    calc
      _ ≤ ‖iteratedFDeriv ℝ j g x‖ * (d : ℝ)^j := coordinatePartial_le_operator g hg κ x hx
      _ = (h⁻¹)^j * ‖iteratedFDeriv ℝ j f (h⁻¹ • (x-x0 d))‖ * (d : ℝ)^j := by
        rw [dilated_profile_derivative f hf, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity)]
      _ ≤ (h⁻¹)^j * (D j * (d : ℝ)^j) := by
        have hp := mul_le_mul_of_nonneg_left (hD j (h⁻¹ • (x-x0 d))) (show 0 ≤ (h⁻¹)^j by positivity)
        have hp' := mul_le_mul_of_nonneg_right hp (show 0 ≤ (d : ℝ)^j by positivity)
        simpa only [mul_assoc] using hp'
      _ ≤ h^(-s) * C := mul_le_mul hscale (hjB.trans hCB) (mul_nonneg (hD0 j) (by positivity)) (by positivity)
      _ = _ := by ring
  · intro κ hκ x hx y hy hxy
    have hκm : multiOrder κ = m := hκ
    have hMj := hM
    rw [← hκm] at hMj
    have hjet (z : Cov d) (hz : z ∈ cube d) :
        coordinatePartial g κ z = (iteratedFDeriv ℝ (multiOrder κ) g z) (coordinateDirections κ) := by
      unfold coordinatePartial
      rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d)
        (hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt hz]
    rw [hjet x hx, hjet y hy]
    have hop : |(iteratedFDeriv ℝ (multiOrder κ) g x) (coordinateDirections κ) -
        (iteratedFDeriv ℝ (multiOrder κ) g y) (coordinateDirections κ)| ≤
        ‖iteratedFDeriv ℝ (multiOrder κ) g x - iteratedFDeriv ℝ (multiOrder κ) g y‖ * (d : ℝ)^(multiOrder κ) := by
      change ‖((iteratedFDeriv ℝ (multiOrder κ) g x)-(iteratedFDeriv ℝ (multiOrder κ) g y)) (coordinateDirections κ)‖ ≤ _
      calc
        _ ≤ _ := ((iteratedFDeriv ℝ (multiOrder κ) g x)-(iteratedFDeriv ℝ (multiOrder κ) g y)).le_opNorm _
        _ ≤ _ := by
          have hd := Finset.prod_le_prod (s := Finset.univ) (fun i _ => norm_nonneg (coordinateDirections κ i))
            (fun i _ => coordinateDirections_norm_le κ i)
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            mul_le_mul_of_nonneg_left hd (norm_nonneg ((iteratedFDeriv ℝ (multiOrder κ) g x)-(iteratedFDeriv ℝ (multiOrder κ) g y)))
    have hdist : ‖h⁻¹ • (x-x0 d)-h⁻¹ • (y-x0 d)‖ = ‖x-y‖/h := by
      rw [← smul_sub, sub_sub_sub_cancel_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos hh]
      ring
    have hcancel : (h⁻¹)^(multiOrder κ) * (‖x-y‖/h)^a = h^(-s) * ‖x-y‖^a := by
      rw [Real.div_rpow (norm_nonneg _) hh.le, div_eq_mul_inv,
        inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hh.le,
        ← Real.rpow_neg hh.le]
      rw [show h^(-(multiOrder κ : ℝ)) * (‖x-y‖^a * h^(-a)) =
        (h^(-(multiOrder κ : ℝ)) * h^(-a)) * ‖x-y‖^a by ring, ← Real.rpow_add hh]
      congr 2
      rw [hκm]
      dsimp [a]
      ring
    calc
      _ ≤ _ := hop
      _ = (h⁻¹)^(multiOrder κ) * ‖iteratedFDeriv ℝ (multiOrder κ) f (h⁻¹ • (x-x0 d)) -
          iteratedFDeriv ℝ (multiOrder κ) f (h⁻¹ • (y-x0 d))‖ * (d : ℝ)^(multiOrder κ) := by
        rw [dilated_profile_derivative f hf, dilated_profile_derivative f hf,
          ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      _ ≤ (h⁻¹)^(multiOrder κ) * (M*(‖x-y‖/h)^a) * (d : ℝ)^(multiOrder κ) := by
        gcongr
        simpa only [hdist] using hMj (h⁻¹ • (x-x0 d)) (h⁻¹ • (y-x0 d))
      _ = (M*(d : ℝ)^(multiOrder κ)) * h^(-s) * ‖x-y‖^a := by
        calc
          _ = (M*(d : ℝ)^(multiOrder κ)) * ((h⁻¹)^(multiOrder κ) * (‖x-y‖/h)^a) := by ring
          _ = _ := by rw [hcancel]; ring
      _ ≤ C*h^(-s)*‖x-y‖^a := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hh.le _)
        simpa only [hκm] using hCM
      _ = _ := by rw [dist_eq_norm]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
