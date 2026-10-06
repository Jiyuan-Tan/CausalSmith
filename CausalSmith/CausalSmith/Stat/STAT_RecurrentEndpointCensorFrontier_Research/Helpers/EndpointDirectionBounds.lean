module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.DirectionAnalytics
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.MidpointBaseline
public import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# Quantitative bounds for the endpoint direction

This module extracts global finite derivative bounds from the compactly
supported smooth cutoff and turns the zeroth-order bound into a uniform
small-amplitude statement for endpoint perturbations.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The cutoff bump has compact support. -/
lemma CutoffData.bump_hasCompactSupport (c : ClassConstants) (cut : CutoffData c) :
    HasCompactSupport cut.bump := by
  rcases cut.bump_compact_inside with ⟨lo, hi, hlo, hhi, hsupp⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport cut.bump) <|
    closure_minimal (fun x hx ↦ hsupp x hx) isClosed_Icc

/-- Every iterated derivative of the cutoff bump has compact support. -/
lemma CutoffData.iteratedDeriv_bump_hasCompactSupport
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j cut.bump) := by
  induction j with
  | zero => simpa using cut.bump_hasCompactSupport c
  | succ j ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Every fixed derivative of the cutoff bump admits a positive global
absolute bound. -/
lemma CutoffData.exists_iteratedDeriv_bump_bound
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ, |iteratedDeriv j cut.bump x| ≤ B := by
  have hcont : Continuous (iteratedDeriv j cut.bump) :=
    cut.bump_smooth.continuous_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)).le
  have hbdd : BddAbove (Set.range fun x : ℝ ↦ ‖iteratedDeriv j cut.bump x‖) :=
    hcont.norm.bddAbove_range_of_hasCompactSupport
      (cut.iteratedDeriv_bump_hasCompactSupport c j).norm
  rcases bddAbove_def.mp hbdd with ⟨B, hB⟩
  refine ⟨max 1 B, by positivity, fun x ↦ ?_⟩
  rw [← Real.norm_eq_abs]
  exact (hB _ ⟨x, rfl⟩).trans (le_max_right _ _)

/-- The fractional exponent paired with `holderOrder` lies in `(0,1]`. -/
lemma holderFraction_mem_Ioc (c : ClassConstants) :
    c.beta - holderOrder c ∈ Set.Ioc (0 : ℝ) 1 := by
  have hceil : 1 ≤ Nat.ceil c.beta := (Nat.ceil_pos.mpr c.beta_pos)
  have hcast : ((holderOrder c : ℕ) : ℝ) = (Nat.ceil c.beta : ℝ) - 1 := by
    rw [holderOrder, Nat.cast_sub hceil]
    norm_num
  constructor
  · rw [hcast]
    linarith [Nat.ceil_lt_add_one c.beta_pos.le]
  · rw [hcast]
    linarith [Nat.le_ceil c.beta]

/-- A smooth compactly supported bump has a finite global Hölder constant
at every exponent in `[0,1]`, for each fixed iterated derivative. -/
lemma CutoffData.exists_iteratedDeriv_bump_holder_bound
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) (γ : ℝ)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ x y : ℝ,
      |iteratedDeriv j cut.bump x - iteratedDeriv j cut.bump y| ≤
        B * |x - y| ^ γ := by
  rcases cut.exists_iteratedDeriv_bump_bound c j with ⟨B₀, hB₀pos, hB₀⟩
  rcases cut.exists_iteratedDeriv_bump_bound c (j + 1) with ⟨B₁, hB₁pos, hB₁⟩
  refine ⟨max B₁ (2 * B₀), lt_of_lt_of_le hB₁pos (le_max_left _ _), ?_⟩
  intro x y
  let d : ℝ → ℝ := iteratedDeriv j cut.bump
  have hd : Differentiable ℝ d :=
    cut.bump_smooth.differentiable_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j))
  have hderiv : ∀ z : ℝ, |deriv d z| ≤ B₁ := by
    intro z
    change |deriv (iteratedDeriv j cut.bump) z| ≤ B₁
    rw [← iteratedDeriv_succ]
    exact hB₁ z
  have hlip : |d x - d y| ≤ B₁ * |x - y| := by
    have hmv := convex_univ.norm_image_sub_le_of_norm_deriv_le
      (fun z _ ↦ hd.differentiableAt)
      (fun z _ ↦ by simpa [Real.norm_eq_abs] using hderiv z)
      (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs, abs_sub_comm] using hmv
  have hbounded : |d x - d y| ≤ 2 * B₀ := by
    calc
      |d x - d y| ≤ |d x| + |d y| := abs_sub _ _
      _ ≤ B₀ + B₀ := add_le_add (hB₀ x) (hB₀ y)
      _ = 2 * B₀ := by ring
  by_cases hxy : |x - y| ≤ 1
  · calc
      |d x - d y| ≤ B₁ * |x - y| := hlip
      _ ≤ B₁ * |x - y| ^ γ := by
        exact mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one (abs_nonneg _) hxy hγ1) hB₁pos.le
      _ ≤ max B₁ (2 * B₀) * |x - y| ^ γ := by
        exact mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (abs_nonneg _) _)
  · have hone : 1 ≤ |x - y| := le_of_not_ge hxy
    calc
      |d x - d y| ≤ 2 * B₀ := hbounded
      _ ≤ (2 * B₀) * |x - y| ^ γ := by
        nth_rewrite 1 [← mul_one (2 * B₀)]
        exact mul_le_mul_of_nonneg_left (Real.one_le_rpow hone hγ0)
          (mul_nonneg (by norm_num) hB₀pos.le)
      _ ≤ max B₁ (2 * B₀) * |x - y| ^ γ := by
        exact mul_le_mul_of_nonneg_right (le_max_right _ _)
          (Real.rpow_nonneg (abs_nonneg _) _)

/-- A named positive global bound for the cutoff bump itself. -/
@[no_expose]
noncomputable def endpointBumpBound (c : ClassConstants) (cut : CutoffData c) : ℝ :=
  Classical.choose (cut.exists_iteratedDeriv_bump_bound c 0)

lemma endpointBumpBound_pos (c : ClassConstants) (cut : CutoffData c) :
    0 < endpointBumpBound c cut :=
  (Classical.choose_spec (cut.exists_iteratedDeriv_bump_bound c 0)).1

lemma abs_bump_le_endpointBumpBound (c : ClassConstants) (cut : CutoffData c)
    (x : ℝ) : |cut.bump x| ≤ endpointBumpBound c cut := by
  simpa [endpointBumpBound] using
    (Classical.choose_spec (cut.exists_iteratedDeriv_bump_bound c 0)).2 x

/-- The endpoint direction is bounded by its amplitude times the global bump
bound. -/
lemma abs_endpointDirection_le (c : ClassConstants) (cut : CutoffData c)
    {u h t : ℝ} (hh : 0 ≤ h) :
    |endpointDirection c cut u h t| ≤
      |u| * h ^ c.beta * endpointBumpBound c cut := by
  rw [endpointDirection, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hh _)]
  gcongr
  exact abs_bump_le_endpointBumpBound c cut _

/-- At bandwidth at most one, the endpoint direction has a bandwidth-free
uniform envelope. -/
lemma abs_endpointDirection_le_uniform (c : ClassConstants) (cut : CutoffData c)
    {u h t : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    |endpointDirection c cut u h t| ≤ |u| * endpointBumpBound c cut := by
  calc
    _ ≤ |u| * h ^ c.beta * endpointBumpBound c cut :=
      abs_endpointDirection_le c cut hh0
    _ ≤ |u| * 1 * endpointBumpBound c cut := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_one hh0 hh1 c.beta_pos.le) (abs_nonneg u))
        (endpointBumpBound_pos c cut).le
    _ = _ := by ring

/-- Endpoint directions are smooth at every positive bandwidth. -/
lemma endpointDirection_contDiff (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) : ContDiff ℝ ∞ (endpointDirection c cut u h) := by
  unfold endpointDirection
  exact contDiff_const.mul (cut.bump_smooth.comp
    ((contDiff_const.sub contDiff_id).div_const h))

/-- Exact iterated-derivative formula for a rescaled endpoint direction. -/
lemma iteratedDeriv_endpointDirection (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) (hh : h ≠ 0) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (endpointDirection c cut u h) t =
      (u * h ^ c.beta) * ((-1 / h) ^ j) *
        iteratedDeriv j cut.bump ((1 - t) / h) := by
  let f : ℝ → ℝ := fun x ↦ cut.bump ((1 / h) * x)
  have hf : ContDiff ℝ j f :=
    cut.bump_smooth.of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le) |>.comp
      (contDiff_const.mul contDiff_id)
  have hscale := iteratedDeriv_comp_const_mul
    (cut.bump_smooth.of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le)) (1 / h)
  have hflip := congrFun (iteratedDeriv_comp_const_sub j f 1) t
  have hend : endpointDirection c cut u h =
      fun z : ℝ ↦ (u * h ^ c.beta) * f (1 - z) := by
    funext z
    simp only [endpointDirection, f]
    congr 2
    field_simp
  rw [hend]
  rw [iteratedDeriv_const_mul_field, hflip]
  change (u * h ^ c.beta) *
      ((-1 : ℝ) ^ j * iteratedDeriv j f (1 - t)) = _
  rw [show iteratedDeriv j f (1 - t) =
      (1 / h) ^ j * iteratedDeriv j cut.bump ((1 / h) * (1 - t)) by
        exact congrFun hscale (1 - t)]
  have hpow : (-1 : ℝ) ^ j * (1 / h) ^ j = (-1 / h) ^ j := by
    rw [← mul_pow]
    congr 2
    field_simp
  have harg : (1 / h) * (1 - t) = (1 - t) / h := by field_simp
  rw [harg]
  calc
    _ = (u * h ^ c.beta) * ((-1 : ℝ) ^ j * (1 / h) ^ j) *
        iteratedDeriv j cut.bump ((1 - t) / h) := by ring
    _ = _ := by rw [hpow]

/-- A coefficient inequality reduces Hölder control of a rescaled endpoint
direction to the global Hölder constant of the cutoff derivative. -/
lemma endpointDirection_holderSeminormLe_of_coefficient
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) (γ L B u h : ℝ)
    (hh : 0 < h)
    (hB : ∀ x y : ℝ,
      |iteratedDeriv j cut.bump x - iteratedDeriv j cut.bump y| ≤
        B * |x - y| ^ γ)
    (hcoef : |u * h ^ c.beta * (-1 / h) ^ j| * B * (1 / h) ^ γ ≤ L) :
    HolderSeminormLe j γ L (endpointDirection c cut u h) := by
  constructor
  · exact (endpointDirection_contDiff c cut u h).contDiffOn.of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le)
  · intro x hx y hy
    have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) :=
      uniqueDiffOn_Icc (by norm_num)
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
        ((endpointDirection_contDiff c cut u h).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le)) hx,
      iteratedDerivWithin_eq_iteratedDeriv hud
        ((endpointDirection_contDiff c cut u h).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le)) hy,
      iteratedDeriv_endpointDirection c cut u h hh.ne' j x,
      iteratedDeriv_endpointDirection c cut u h hh.ne' j y]
    let A : ℝ := u * h ^ c.beta * (-1 / h) ^ j
    have hscaled : |(1 - x) / h - (1 - y) / h| = (1 / h) * |x - y| := by
      rw [show (1 - x) / h - (1 - y) / h = (y - x) / h by ring]
      rw [abs_div, abs_sub_comm, abs_of_pos hh]
      field_simp
    calc
      |A * iteratedDeriv j cut.bump ((1 - x) / h) -
          A * iteratedDeriv j cut.bump ((1 - y) / h)| =
          |A| * |iteratedDeriv j cut.bump ((1 - x) / h) -
            iteratedDeriv j cut.bump ((1 - y) / h)| := by
              rw [← mul_sub, abs_mul]
      _ ≤ |A| * (B * |(1 - x) / h - (1 - y) / h| ^ γ) := by
          exact mul_le_mul_of_nonneg_left (hB _ _) (abs_nonneg A)
      _ = (|A| * B * (1 / h) ^ γ) * |x - y| ^ γ := by
          rw [hscaled, Real.mul_rpow (by positivity) (abs_nonneg _)]
          ring
      _ ≤ L * |x - y| ^ γ :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (abs_nonneg _) _)

/-- The bandwidth powers in the endpoint Hölder seminorm cancel exactly at
the prescribed derivative order. -/
lemma endpointDirection_holder_coefficient_eq
    (c : ClassConstants) (B u h : ℝ) (hh : 0 < h) :
    |u * h ^ c.beta * (-1 / h) ^ holderOrder c| * B *
        (1 / h) ^ (c.beta - holderOrder c) = |u| * B := by
  have hhr : 0 ≤ h ^ c.beta := Real.rpow_nonneg hh.le _
  have habsPow : |(-1 / h) ^ holderOrder c| = (1 / h) ^ holderOrder c := by
    rw [abs_pow, abs_div, abs_neg, abs_one, abs_of_pos hh]
  rw [abs_mul, abs_mul, abs_of_nonneg hhr, habsPow]
  rw [← Real.rpow_natCast]
  have hadd : ((holderOrder c : ℕ) : ℝ) +
      (c.beta - holderOrder c) = c.beta := by ring
  have hbase : 0 < 1 / h := by positivity
  calc
    |u| * h ^ c.beta * (1 / h) ^ (holderOrder c : ℝ) * B *
          (1 / h) ^ (c.beta - holderOrder c) =
        |u| * B * (h ^ c.beta *
          ((1 / h) ^ (holderOrder c : ℝ) *
            (1 / h) ^ (c.beta - holderOrder c))) := by ring
    _ = |u| * B * (h ^ c.beta * (1 / h) ^ c.beta) := by
      rw [← Real.rpow_add hbase, hadd]
    _ = |u| * B * ((h * (1 / h)) ^ c.beta) := by
      rw [Real.mul_rpow hh.le hbase.le]
    _ = |u| * B := by
      rw [show h * (1 / h) = 1 by field_simp, Real.one_rpow, mul_one]

/-- The endpoint direction has Hölder seminorm at most `|u| B`, uniformly
over every positive bandwidth. -/
lemma endpointDirection_holderSeminormLe_uniform
    (c : ClassConstants) (cut : CutoffData c) (B u h : ℝ)
    (hh : 0 < h)
    (hB : ∀ x y : ℝ,
      |iteratedDeriv (holderOrder c) cut.bump x -
          iteratedDeriv (holderOrder c) cut.bump y| ≤
        B * |x - y| ^ (c.beta - holderOrder c)) :
    HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) (|u| * B)
      (endpointDirection c cut u h) := by
  apply endpointDirection_holderSeminormLe_of_coefficient
      c cut (holderOrder c) (c.beta - holderOrder c) (|u| * B) B u h hh hB
  exact le_of_eq (endpointDirection_holder_coefficient_eq c B u h hh)

/-- A named positive Hölder constant for the relevant cutoff derivative. -/
@[no_expose]
noncomputable def endpointHolderBound (c : ClassConstants) (cut : CutoffData c) : ℝ :=
  Classical.choose (cut.exists_iteratedDeriv_bump_holder_bound c
    (holderOrder c) (c.beta - holderOrder c)
    (holderFraction_mem_Ioc c).1.le (holderFraction_mem_Ioc c).2)

lemma endpointHolderBound_pos (c : ClassConstants) (cut : CutoffData c) :
    0 < endpointHolderBound c cut :=
  (Classical.choose_spec (cut.exists_iteratedDeriv_bump_holder_bound c
    (holderOrder c) (c.beta - holderOrder c)
    (holderFraction_mem_Ioc c).1.le (holderFraction_mem_Ioc c).2)).1

lemma endpointHolderBound_spec (c : ClassConstants) (cut : CutoffData c)
    (x y : ℝ) :
    |iteratedDeriv (holderOrder c) cut.bump x -
        iteratedDeriv (holderOrder c) cut.bump y| ≤
      endpointHolderBound c cut * |x - y| ^ (c.beta - holderOrder c) :=
  (Classical.choose_spec (cut.exists_iteratedDeriv_bump_holder_bound c
    (holderOrder c) (c.beta - holderOrder c)
    (holderFraction_mem_Ioc c).1.le (holderFraction_mem_Ioc c).2)).2 x y

lemma HolderSeminormLe.mono_constant
    {j : ℕ} {γ L₁ L₂ : ℝ} {f : ℝ → ℝ}
    (hf : HolderSeminormLe j γ L₁ f) (hL : L₁ ≤ L₂) :
    HolderSeminormLe j γ L₂ f := by
  refine ⟨hf.1, ?_⟩
  intro x hx y hy
  exact (hf.2 x hx y hy).trans <|
    mul_le_mul_of_nonneg_right hL (Real.rpow_nonneg (abs_nonneg _) _)

/-- A positive amplitude radius that keeps the endpoint perturbation inside
both sides of the midpoint recurrence band. -/
@[no_expose]
noncomputable def endpointAmplitudeRadius (c : ClassConstants)
    (cut : CutoffData c) : ℝ :=
  min (midpointLambda c - c.lambdaMin) (c.lambdaMax - midpointLambda c) /
    (2 * endpointBumpBound c cut)

lemma endpointAmplitudeRadius_pos (c : ClassConstants) (cut : CutoffData c) :
    0 < endpointAmplitudeRadius c cut := by
  have hlo : 0 < midpointLambda c - c.lambdaMin := sub_pos.mpr (midpoint_strict_bounds c).1
  have hhi : 0 < c.lambdaMax - midpointLambda c := sub_pos.mpr (midpoint_strict_bounds c).2.1
  unfold endpointAmplitudeRadius
  exact div_pos (lt_min hlo hhi) (mul_pos (by norm_num) (endpointBumpBound_pos c cut))

/-- Every positive amplitude below the chosen radius gives pointwise band
control at every bandwidth in `[0,1]`. -/
lemma endpointDirection_small_in_midpoint_band
    (c : ClassConstants) (cut : CutoffData c)
    {u h t : ℝ} (hu0 : 0 < u) (hu : u ≤ endpointAmplitudeRadius c cut)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    |endpointDirection c cut u h t| ≤ midpointLambda c - c.lambdaMin ∧
      |endpointDirection c cut u h t| ≤ c.lambdaMax - midpointLambda c := by
  have hB : 0 < endpointBumpBound c cut := endpointBumpBound_pos c cut
  have hamp : |u| * endpointBumpBound c cut ≤
      min (midpointLambda c - c.lambdaMin) (c.lambdaMax - midpointLambda c) := by
    rw [abs_of_pos hu0]
    rw [endpointAmplitudeRadius] at hu
    have := (mul_le_mul_of_nonneg_right hu hB.le)
    calc
      u * endpointBumpBound c cut
          ≤ (min (midpointLambda c - c.lambdaMin)
              (c.lambdaMax - midpointLambda c) /
              (2 * endpointBumpBound c cut)) * endpointBumpBound c cut := this
      _ = min (midpointLambda c - c.lambdaMin)
              (c.lambdaMax - midpointLambda c) / 2 := by field_simp
      _ ≤ min (midpointLambda c - c.lambdaMin)
              (c.lambdaMax - midpointLambda c) := by
        have hm : 0 ≤ min (midpointLambda c - c.lambdaMin)
            (c.lambdaMax - midpointLambda c) :=
          (lt_min (sub_pos.mpr (midpoint_strict_bounds c).1)
            (sub_pos.mpr (midpoint_strict_bounds c).2.1)).le
        linarith
  have hdir := (abs_endpointDirection_le_uniform c cut (t := t) hh0 hh1).trans hamp
  exact ⟨hdir.trans (min_le_left _ _), hdir.trans (min_le_right _ _)⟩

/-- A positive radius enforcing both the intensity band and the recurrence
Hölder radius. -/
@[no_expose]
noncomputable def endpointModelRadius (c : ClassConstants) (cut : CutoffData c) : ℝ :=
  min (endpointAmplitudeRadius c cut)
    (c.Llambda / (2 * endpointHolderBound c cut))

lemma endpointModelRadius_pos (c : ClassConstants) (cut : CutoffData c) :
    0 < endpointModelRadius c cut := by
  unfold endpointModelRadius
  exact lt_min (endpointAmplitudeRadius_pos c cut)
    (div_pos c.Llambda_pos
      (mul_pos (by norm_num) (endpointHolderBound_pos c cut)))

/-- The bandwidth used by the endpoint alternative. -/
@[no_expose]
noncomputable def endpointBandwidth (c : ClassConstants) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))

lemma endpointBandwidth_eq (c : ClassConstants) (n : ℕ) :
    endpointBandwidth c n =
      (n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1))) := by
  rfl

lemma endpointBandwidth_pos (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n) :
    0 < endpointBandwidth c n := by
  apply Real.rpow_pos_of_pos
  exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)

lemma endpointBandwidth_le_one (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n) :
    endpointBandwidth c n ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · exact_mod_cast hn
  · have hden : 0 < 2 * c.beta + c.kappa + 1 := by
      linarith [c.beta_pos, c.kappa_pos]
    exact neg_nonpos.mpr (div_nonneg zero_le_one hden.le)

/-- Exact bandwidth balance behind the bounded endpoint KL envelope. -/
lemma endpointBandwidth_balance (c : ClassConstants) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * endpointBandwidth c n ^ (2 * c.beta + c.kappa + 1) = 1 := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < 2 * c.beta + c.kappa + 1 := by
    linarith [c.beta_pos, c.kappa_pos]
  unfold endpointBandwidth
  rw [← Real.rpow_mul hnpos.le]
  have hexp : -(1 / (2 * c.beta + c.kappa + 1)) *
      (2 * c.beta + c.kappa + 1) = -1 := by
    field_simp
  rw [hexp, Real.rpow_neg_one]
  exact mul_inv_cancel₀ hnpos.ne'

/-- The model-radius conclusion specialized to the rate-tuned endpoint
bandwidth appearing in `full_history_directions`. -/
lemma endpointDirection_rate_model_conditions
    (c : ClassConstants) (cut : CutoffData c)
    {u : ℝ} (hu0 : 0 < u) (hu : u ≤ endpointModelRadius c cut)
    {n : ℕ} (hn : 1 ≤ n) :
    (∀ t : ℝ, c.lambdaMin ≤ midpointLambda c +
        endpointDirection c cut u
          ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t ∧
      midpointLambda c + endpointDirection c cut u
          ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t ≤ c.lambdaMax) ∧
    HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
      (fun t ↦ midpointLambda c + endpointDirection c cut u
        ((n : ℝ) ^ (-(1 / (2 * c.beta + c.kappa + 1)))) t) := by
  let h := endpointBandwidth c n
  have hh0 : 0 < h := endpointBandwidth_pos c hn
  have hh1 : h ≤ 1 := endpointBandwidth_le_one c hn
  have huAmp : u ≤ endpointAmplitudeRadius c cut :=
    hu.trans (min_le_left _ _)
  have huHolder : u ≤ c.Llambda / (2 * endpointHolderBound c cut) :=
    hu.trans (min_le_right _ _)
  have hband : ∀ t : ℝ, c.lambdaMin ≤ midpointLambda c +
        endpointDirection c cut u h t ∧
      midpointLambda c + endpointDirection c cut u h t ≤ c.lambdaMax := by
    intro t
    exact endpointDirection_add_mem_band c cut
      (endpointDirection_small_in_midpoint_band c cut hu0 huAmp hh0.le hh1).1
      (endpointDirection_small_in_midpoint_band c cut hu0 huAmp hh0.le hh1).2
  have hsmall : |u| * endpointHolderBound c cut ≤ c.Llambda := by
    rw [abs_of_pos hu0]
    have hB := endpointHolderBound_pos c cut
    have hmul := mul_le_mul_of_nonneg_right huHolder hB.le
    calc
      u * endpointHolderBound c cut ≤
          (c.Llambda / (2 * endpointHolderBound c cut)) *
            endpointHolderBound c cut := hmul
      _ = c.Llambda / 2 := by field_simp
      _ ≤ c.Llambda := by linarith [c.Llambda_pos]
  have hholder : HolderSeminormLe (holderOrder c)
      (c.beta - holderOrder c) c.Llambda
      (fun t ↦ midpointLambda c + endpointDirection c cut u h t) := by
    apply HolderSeminormLe.const_add
    exact (endpointDirection_holderSeminormLe_uniform c cut
      (endpointHolderBound c cut) u h hh0 (endpointHolderBound_spec c cut)).mono_constant
        hsmall
  simpa [h, endpointBandwidth] using And.intro hband hholder

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
