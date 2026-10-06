module
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.CosineFamily
public import CausalSmith.Stat.STAT_PrivateCateRoughdesignFrontier_Research.Helpers.FrameRegularity
public import Mathlib.Analysis.Real.Pi.Bounds
/-! Global Lipschitz and Holder certificates for the shared-sign causal alternatives. -/
public section
noncomputable section
open Set
namespace CausalSmith.Stat.PrivateCateRoughdesign

/-- The micro radius is no larger than the macro radius in the published range.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: deltaL_le_macro
lemma deltaL_le_macro (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4) : deltaL hL ≤ hL := by
  have h1 : hL ≤ 1 := by linarith [hh.2]
  simpa only [deltaL, pow_one] using pow_le_pow_of_le_one hh.1.le h1 (by norm_num : 1 ≤ 5)

/-- Only frames supported at one of the two points contribute to the signed-sum difference.  [the theorem's stated inputs and assumptions](hyp:lam,x,y), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: signed_frame_difference_bound
lemma signed_frame_difference_bound (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) (x y : Covariate) :
    |(∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j x) -
      (∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j y)| ≤
      (3*Real.pi/deltaL hL)*|(x : ℝ)-y| := by
  classical
  have hd : 0 < deltaL hL := pow_pos hh.1 5
  let sx := Finset.univ.filter (fun j : activeSigns hL =>
    |(x : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL)
  let sy := Finset.univ.filter (fun j : activeSigns hL =>
    |(y : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL)
  let v (j : activeSigns hL) := (2*bit (lam j)-1)*(frame hL j x-frame hL j y)
  have he : (∑ j : activeSigns hL, v j) = ∑ j ∈ sx ∪ sy, v j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j hj hnot
    have hn : j ∉ sx ∧ j ∉ sy := by simpa using hnot
    have hx : ¬ |(x : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL := by
      simpa [sx] using hn.1
    have hy : ¬ |(y : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL := by
      simpa [sy] using hn.2
    simp [v, frame, hx, hy]
  have hcard : (sx ∪ sy).card ≤ 6 := by
    have hx := frame_support_card_le hL hh x
    have hy := frame_support_card_le hL hh y
    change sx.card ≤ 3 at hx
    change sy.card ≤ 3 at hy
    exact (Finset.card_union_le sx sy).trans (by omega)
  have hv (j : activeSigns hL) : |v j| ≤
      (Real.pi/(2*deltaL hL))*|(x : ℝ)-y| := by
    have hb : |2*bit (lam j)-1| = 1 := by cases h : lam j <;> norm_num [bit, h]
    simpa only [v, abs_mul, hb, one_mul] using frame_difference_bound hL hh.1 j x y
  rw [← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  change |∑ j : activeSigns hL, v j| ≤ _
  rw [he]
  calc
    _ ≤ ∑ j ∈ sx ∪ sy, |v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ sx ∪ sy, (Real.pi/(2*deltaL hL))*|(x : ℝ)-y| :=
      Finset.sum_le_sum (fun j hj => hv j)
    _ = ((sx ∪ sy).card : ℝ)*((Real.pi/(2*deltaL hL))*|(x : ℝ)-y|) := by simp
    _ ≤ 6*((Real.pi/(2*deltaL hL))*|(x : ℝ)-y|) := by
      apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by ring

/-- The same support counting bounds the unlocalized signed sum by three.  [the theorem's stated inputs and assumptions](hyp:lam,x), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: signed_frame_abs_le_three
lemma signed_frame_abs_le_three (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) (x : Covariate) :
    |∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j x| ≤ 3 := by
  classical
  calc
    _ ≤ ∑ j : activeSigns hL, |(2*bit (lam j)-1)*frame hL j x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : activeSigns hL,
        if |(x : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      have hb : |2*bit (lam j)-1| = 1 := by cases h : lam j <;> norm_num [bit, h]
      simpa only [abs_mul, hb, one_mul] using frame_abs_le hL j x
    _ = ((Finset.univ.filter (fun j : activeSigns hL =>
        |(x : ℝ)-(j : ℤ)*deltaL hL| ≤ deltaL hL)).card : ℝ) := by
      simp [← Finset.sum_filter]
    _ ≤ 3 := by exact_mod_cast frame_support_card_le hL hh x

/-- Multiplication by the macro envelope preserves a uniform micro-scale Lipschitz modulus.  [the theorem's stated inputs and assumptions](hyp:lam,x,y), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: perturbation_difference_bound
lemma perturbation_difference_bound (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) (x y : Covariate) :
    |perturbation hL lam x-perturbation hL lam y| ≤
      (24/deltaL hL)*|(x : ℝ)-y| := by
  let s (z : Covariate) := ∑ j : activeSigns hL, (2*bit (lam j)-1)*frame hL j z
  have hs := signed_frame_difference_bound hL hh lam x y
  have hsy := signed_frame_abs_le_three hL hh lam y
  have hg := envelope_difference_bound hL hh.1 x y
  have hx := envelope_range hL x
  have hd : 0 < deltaL hL := pow_pos hh.1 5
  have hinv : Real.pi/hL ≤ Real.pi/deltaL hL :=
    div_le_div_of_nonneg_left Real.pi_pos.le hd (deltaL_le_macro hL hh)
  have he : perturbation hL lam x-perturbation hL lam y =
      envelope hL x*(s x-s y)+(envelope hL x-envelope hL y)*s y := by
    dsimp [perturbation, s]; ring
  rw [he]
  calc
    _ ≤ |envelope hL x*(s x-s y)|+|(envelope hL x-envelope hL y)*s y| := abs_add_le _ _
    _ = envelope hL x*|s x-s y|+|envelope hL x-envelope hL y| *|s y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx.1]
    _ ≤ 1*((3*Real.pi/deltaL hL)*|(x : ℝ)-y|)+
        ((Real.pi/hL)*|(x : ℝ)-y|)*3 :=
      add_le_add (mul_le_mul hx.2 hs (abs_nonneg _) (by norm_num))
        (mul_le_mul hg hsy (abs_nonneg _) (mul_nonneg (div_nonneg Real.pi_pos.le hh.1.le) (abs_nonneg _)))
    _ ≤ (6*Real.pi/deltaL hL)*|(x : ℝ)-y| := by
      have := mul_le_mul_of_nonneg_right hinv (abs_nonneg ((x : ℝ)-y))
      have heq : (6*Real.pi/deltaL hL)*|(x : ℝ)-y| =
          3*((Real.pi/deltaL hL)*|(x : ℝ)-y|)+
          3*((Real.pi/deltaL hL)*|(x : ℝ)-y|) := by ring
      rw [heq]
      have heq2 : 1*((3*Real.pi/deltaL hL)*|(x : ℝ)-y|) =
          3*((Real.pi/deltaL hL)*|(x : ℝ)-y|) := by ring
      rw [heq2]
      linarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply div_le_div_of_nonneg_right _ hd.le
      linarith [Real.pi_lt_four]

/-- The effect bump satisfies the same coarse micro-scale modulus as the perturbation.  [the theorem's stated inputs and assumptions](hyp:x,y), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: bump_micro_difference_bound
lemma bump_micro_difference_bound (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (x y : Covariate) :
    |bump hL x-bump hL y| ≤ (24/deltaL hL)*|(x : ℝ)-y| := by
  have hd : 0 < deltaL hL := pow_pos hh.1 5
  have hi := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*Real.pi) hd (deltaL_le_macro hL hh)
  apply (bump_difference_bound hL hh.1 x y).trans
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  apply hi.trans
  apply div_le_div_of_nonneg_right _ hd.le
  linarith [Real.pi_lt_four]

/-- The micro radius to the one-tenth power is exactly the square root of the macro radius. The result uses [the stated assumptions](hyp:hL,hh) and establishes [the displayed conclusion](goal). -/
-- @node: deltaL_tenth_power
lemma deltaL_tenth_power (hL : ℝ) (hh : 0 < hL) :
    (deltaL hL)^(1/10 : ℝ) = Real.sqrt hL := by
  rw [deltaL, ← Real.rpow_natCast_mul hh.le, Real.sqrt_eq_rpow]
  norm_num

/-- The square-root amplitude cancels the micro-scale Holder loss with a small constant. The result uses [the stated assumptions](hyp:hL,hh) and establishes [the displayed conclusion](goal). -/
-- @node: separation_sqrt_scale
lemma separation_sqrt_scale (hL : ℝ) (hh : 0 < hL) :
    Real.sqrt (separation hL) / (deltaL hL)^(1/10 : ℝ) = 1/64 := by
  have hk : kappa = (1/64 : ℝ)^2 := by norm_num [kappa]
  rw [deltaL_tenth_power hL hh, separation, hk, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1/64)]
  exact mul_div_cancel_right₀ _ (Real.sqrt_pos.mpr hh).ne'

/-- The small effect amplitude is bounded by the square-root amplitude.  [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: separation_le_sqrt
lemma separation_le_sqrt (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4) :
    0 ≤ separation hL ∧ separation hL ≤ Real.sqrt (separation hL) := by
  have ht : 0 ≤ separation hL ∧ separation hL ≤ 1 := by
    norm_num [separation, kappa]
    constructor <;> linarith [hh.1, hh.2]
  refine ⟨ht.1, ?_⟩
  nlinarith [Real.sq_sqrt ht.1, Real.sqrt_nonneg (separation hL),
    mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]

/-- The perturbation's two-scale bounds imply the one-tenth Holder modulus.  [the theorem's stated inputs and assumptions](hyp:lam,x,y), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: perturbation_holder_bound
lemma perturbation_holder_bound (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) (x y : Covariate) :
    |perturbation hL lam x-perturbation hL lam y| ≤
      24*|(x : ℝ)-y|^(1/10 : ℝ)/(deltaL hL)^(1/10 : ℝ) := by
  apply holder_modulus_of_two_bounds _ _ _ _ (pow_pos hh.1 5) (abs_nonneg _) (by norm_num)
  · have hx := perturbation_abs_le_three hL hh lam x
    have hy := perturbation_abs_le_three hL hh lam y
    linarith [abs_sub (perturbation hL lam x) (perturbation hL lam y)]
  · convert perturbation_difference_bound hL hh lam x y using 1 <;> dsimp [deltaL] <;> ring

/-- The bounded effect bump has the analogous one-tenth Holder modulus. The result uses [the stated assumptions](hyp:hL,hh) and establishes [the displayed conclusion](goal). -/
-- @node: bump_holder_bound
lemma bump_holder_bound (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4) (x y : Covariate) :
    |bump hL x-bump hL y| ≤
      24*|(x : ℝ)-y|^(1/10 : ℝ)/(deltaL hL)^(1/10 : ℝ) := by
  apply holder_modulus_of_two_bounds _ _ _ _ (pow_pos hh.1 5) (abs_nonneg _) (by norm_num)
  · have hx := bump_range hL x
    have hy := bump_range hL y
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · convert bump_micro_difference_bound hL hh x y using 1 <;> dsimp [deltaL] <;> ring

/-- The actual propensity satisfies the model's radius-three Holder requirement.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: cosineFamily_propensity_holder
lemma cosineFamily_propensity_holder (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) : PropensityHolder (cosineFamily hL hh lam) := by
  intro x y
  change |altE hL lam x-altE hL lam y| ≤ _
  have he : altE hL lam x-altE hL lam y =
      Real.sqrt (separation hL)*(perturbation hL lam x-perturbation hL lam y)/2 := by
    dsimp [altE]; ring
  rw [he, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hb := mul_le_mul_of_nonneg_left (perturbation_holder_bound hL hh lam x y)
    (Real.sqrt_nonneg (separation hL))
  have hs := separation_sqrt_scale hL hh.1
  have hid : Real.sqrt (separation hL)*(24*|(x : ℝ)-y|^(1/10 : ℝ)/
      (deltaL hL)^(1/10 : ℝ)) = (3/8)*|(x : ℝ)-y|^(1/10 : ℝ) := by
    calc
      _ = 24*|(x : ℝ)-y|^(1/10 : ℝ)*
          (Real.sqrt (separation hL)/(deltaL hL)^(1/10 : ℝ)) := by ring
      _ = _ := by rw [hs]; ring
  rw [hid] at hb
  dsimp [L]
  nlinarith [Real.rpow_nonneg (abs_nonneg ((x : ℝ)-y)) (1/10 : ℝ)]

/-- The actual control mean satisfies the model's radius-three Holder requirement.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: cosineFamily_control_holder
lemma cosineFamily_control_holder (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) : ControlHolder (cosineFamily hL hh lam) := by
  intro x y
  change |altMu0 hL lam x-altMu0 hL lam y| ≤ _
  have he : altMu0 hL lam x-altMu0 hL lam y =
      -(Real.sqrt (separation hL)*(perturbation hL lam x-perturbation hL lam y)+
        separation hL*(bump hL x-bump hL y))/2 := by
    dsimp [altMu0]; ring
  have ht := separation_le_sqrt hL hh
  have hb := perturbation_holder_bound hL hh lam x y
  have hq := bump_holder_bound hL hh x y
  let B := 24*|(x : ℝ)-y|^(1/10 : ℝ)/(deltaL hL)^(1/10 : ℝ)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg (by norm_num)
    (Real.rpow_nonneg (abs_nonneg _) _)) (Real.rpow_nonneg (pow_pos hh.1 5).le _)
  have hs : Real.sqrt (separation hL)*B = (3/8)*|(x : ℝ)-y|^(1/10 : ℝ) := by
    dsimp [B]
    calc
      _ = 24*|(x : ℝ)-y|^(1/10 : ℝ)*
          (Real.sqrt (separation hL)/(deltaL hL)^(1/10 : ℝ)) := by ring
      _ = _ := by rw [separation_sqrt_scale hL hh.1]; ring
  have hp := mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg (separation hL))
  have hqb := (mul_le_mul_of_nonneg_left hq ht.1).trans
    (mul_le_mul_of_nonneg_right ht.2 hB)
  change Real.sqrt (separation hL)*|perturbation hL lam x-perturbation hL lam y| ≤
    Real.sqrt (separation hL)*B at hp
  rw [hs] at hp hqb
  have ha := abs_add_le
    (Real.sqrt (separation hL)*(perturbation hL lam x-perturbation hL lam y))
    (separation hL*(bump hL x-bump hL y))
  simp only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg ht.1] at ha
  rw [he, abs_div, abs_neg]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  dsimp [L]
  nlinarith [Real.rpow_nonneg (abs_nonneg ((x : ℝ)-y)) (1/10 : ℝ)]

/-- Nuisance cancellation and the effect-bump modulus give the required contrast regularity.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: cosineFamily_contrast_lipschitz
lemma cosineFamily_contrast_lipschitz (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) : ContrastLipschitz (cosineFamily hL hh lam) := by
  intro x y
  rw [cosineFamily_contrast, cosineFamily_contrast, ← mul_sub, abs_mul]
  have ht : 0 ≤ separation hL := (separation_le_sqrt hL hh).1
  rw [abs_of_nonneg ht]
  calc
    _ ≤ separation hL*((2*Real.pi/hL)*|(x : ℝ)-y|) :=
      mul_le_mul_of_nonneg_left (bump_difference_bound hL hh.1 x y) ht
    _ = (2*Real.pi*kappa)*|(x : ℝ)-y| := by
      unfold separation; field_simp [hh.1.ne']
    _ ≤ L*|(x : ℝ)-y| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      norm_num [kappa, L]
      linarith [Real.pi_lt_four]
/-- Every shared-sign alternative belongs to the complete model, with all three regularity
requirements derived from its explicit cosine construction.  [the theorem's stated inputs and assumptions](hyp:lam), and [the asserted conclusion follows](goal).  [the theorem's stated inputs and assumptions](hyp:hL,hh). -/
-- @node: cosineFamily_completeModel
lemma cosineFamily_completeModel (hL : ℝ) (hh : 0 < hL ∧ hL ≤ 1/4)
    (lam : SignVector hL) : CompleteModel (cosineFamily hL hh lam) := by
  exact binaryCausalLaw_completeModel _ _ _
    (measurable_altE hL lam) (measurable_altMu0 hL lam) (measurable_altMu1 hL lam)
    (alt_parameters_range hL hh lam) (cosineFamily_exchangeability hL hh lam)
    (altE_overlap hL hh lam) (cosineFamily_propensity_holder hL hh lam)
    (cosineFamily_control_holder hL hh lam) (cosineFamily_contrast_lipschitz hL hh lam)
end CausalSmith.Stat.PrivateCateRoughdesign
