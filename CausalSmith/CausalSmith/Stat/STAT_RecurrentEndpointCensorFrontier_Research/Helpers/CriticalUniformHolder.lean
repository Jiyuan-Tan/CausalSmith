module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalHolder
public import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow

/-!
# Uniform Hölder control of the critical perturbation

This file isolates the bandwidth-normalized critical profile.  Its estimates
are uniform in the sample size and provide the common amplitude radius needed
by the critical lower-bound construction.
-/

@[expose] public section

open Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The normalized cutoff-over-distance profile.  The zero branch removes the
apparent singularity on the interval where the cutoff itself vanishes. -/
@[no_expose]
noncomputable def criticalCore (c : ClassConstants) (cut : CutoffData c)
    (y : ℝ) : ℝ :=
  if y ≤ 0 then 0 else cut.chi y / y

/-- Past the cutoff transition the normalized profile is reciprocal. -/
lemma criticalCore_eq_one_div (c : ClassConstants) (cut : CutoffData c)
    {y : ℝ} (hy : 2 ≤ y) : criticalCore c cut y = 1 / y := by
  rw [criticalCore, if_neg (by linarith), cut.chi_one y hy]

/-- The normalized critical profile is smooth on the real line. -/
lemma criticalCore_contDiff (c : ClassConstants) (cut : CutoffData c) :
    ContDiff ℝ ∞ (criticalCore c cut) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_of_locally_contDiffOn
  intro y _hy
  by_cases hy : y < 1
  · refine ⟨Set.Iio 1, isOpen_Iio, hy, ?_⟩
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) _).congr
    intro z hz
    rw [criticalCore]
    by_cases hz0 : z ≤ 0
    · simp [hz0]
    · rw [if_neg hz0, cut.chi_zero z ⟨le_of_not_ge hz0, hz.2.le⟩]
      simp
  · have hy0 : 0 < y := by linarith
    refine ⟨Set.Ioi 0, isOpen_Ioi, hy0, ?_⟩
    have hchi : ContDiffOn ℝ ∞ cut.chi (Set.Ioi (0 : ℝ)) :=
      cut.chi_smooth.mono Set.Ioi_subset_Ici_self
    have hdiv : ContDiffOn ℝ ∞ (fun z : ℝ ↦ cut.chi z / z) (Set.Ioi 0) := by
      apply hchi.div contDiffOn_id
      intro z hz hzero
      simp only [id_eq] at hzero
      exact (ne_of_gt hz) hzero
    apply (hdiv.mono (inter_subset_right)).congr
    intro z hz
    rw [criticalCore, if_neg (not_le.mpr hz.2)]

/-- Every fixed derivative of the normalized profile has a global bound. -/
lemma criticalCore_iteratedDeriv_bounded (c : ClassConstants)
    (cut : CutoffData c) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ y : ℝ, |iteratedDeriv j (criticalCore c cut) y| ≤ B := by
  have hcont : Continuous (iteratedDeriv j (criticalCore c cut)) :=
    (criticalCore_contDiff c cut).continuous_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)).le
  have hbdd : BddAbove
      ((fun y : ℝ ↦ |iteratedDeriv j (criticalCore c cut) y|) ''
        Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.bddAbove_image hcont.continuousOn.abs
  let B : ℝ := max 1 (max
    (sSup ((fun y : ℝ ↦ |iteratedDeriv j (criticalCore c cut) y|) ''
      Set.Icc (0 : ℝ) 2)) (j.factorial : ℝ))
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun y ↦ ?_⟩
  by_cases hy0 : y ≤ 0
  · have heq : Set.EqOn (criticalCore c cut) (fun _ : ℝ ↦ 0) (Set.Iio 1) := by
      intro z hz
      rw [criticalCore]
      by_cases hz0 : z ≤ 0
      · simp [hz0]
      · rw [if_neg hz0, cut.chi_zero z ⟨le_of_not_ge hz0, hz.le⟩]
        simp
    have hderiv : iteratedDeriv j (criticalCore c cut) y =
        iteratedDeriv j (fun _ : ℝ ↦ 0) y :=
      (heq.iteratedDeriv_of_isOpen isOpen_Iio j) (by exact hy0.trans_lt zero_lt_one)
    rw [hderiv]
    simp [B]
  · have hypos : 0 < y := lt_of_not_ge hy0
    by_cases hy2 : y ≤ 2
    · have hs : |iteratedDeriv j (criticalCore c cut) y| ≤
          sSup ((fun z : ℝ ↦ |iteratedDeriv j (criticalCore c cut) z|) ''
            Set.Icc (0 : ℝ) 2) :=
        le_csSup hbdd ⟨y, ⟨hypos.le, hy2⟩, rfl⟩
      exact hs.trans ((le_max_left _ _).trans (le_max_right _ _))
    · have hy : 2 < y := lt_of_not_ge hy2
      have heq : Set.EqOn (criticalCore c cut) (fun z : ℝ ↦ 1 / z)
          (Set.Ioi (2 : ℝ)) := fun z hz ↦ criticalCore_eq_one_div c cut hz.le
      rw [heq.iteratedDeriv_of_isOpen isOpen_Ioi j hy]
      have hformula : iteratedDerivWithin j (fun z : ℝ ↦ 1 / z)
          (Set.Ioi (0 : ℝ)) y =
          (-1 : ℝ) ^ j * (j.factorial : ℝ) * y ^ (-1 - (j : ℤ)) :=
        (iteratedDerivWithin_one_div (s := Set.Ioi (0 : ℝ)) j isOpen_Ioi) hypos
      rw [(iteratedDerivWithin_of_isOpen isOpen_Ioi hypos)] at hformula
      rw [hformula, abs_mul, abs_mul]
      have hzpow : |y ^ (-1 - (j : ℤ))| ≤ 1 := by
        rw [abs_of_nonneg (zpow_nonneg hypos.le _)]
        have hy1 : 1 ≤ y := by linarith
        rw [show (-1 - (j : ℤ)) = -((j + 1 : ℕ) : ℤ) by omega,
          zpow_neg]
        simp only [zpow_natCast]
        exact (inv_le_one₀ (by positivity)).2 (one_le_pow₀ hy1)
      have hsign : |(-1 : ℝ) ^ j| = 1 := by rw [abs_pow]; simp
      rw [hsign, one_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact (mul_le_of_le_one_right (Nat.cast_nonneg _) hzpow).trans
        ((le_max_right _ _).trans (le_max_right _ _))

/-- The top derivative of the normalized profile has a global Hölder
coefficient at the class exponent. -/
lemma criticalCore_holder (c : ClassConstants) (cut : CutoffData c) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℝ,
      |iteratedDeriv (holderOrder c) (criticalCore c cut) u -
          iteratedDeriv (holderOrder c) (criticalCore c cut) v| ≤
        C * |u - v| ^ (c.beta - holderOrder c) := by
  let k := holderOrder c
  let gamma := c.beta - (k : ℝ)
  rcases criticalCore_iteratedDeriv_bounded c cut k with ⟨B0, hB0, hbound0⟩
  rcases criticalCore_iteratedDeriv_bounded c cut (k + 1) with ⟨B1, hB1, hbound1⟩
  let C := max B1 (2 * B0)
  have hCpos : 0 < C := hB1.trans_le (le_max_left _ _)
  have hdiff : Differentiable ℝ (iteratedDeriv k (criticalCore c cut)) :=
    (criticalCore_contDiff c cut).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top (k + 1)).le)
      |>.differentiable_iteratedDeriv' k
  have hlip : ∀ u v : ℝ,
      |iteratedDeriv k (criticalCore c cut) u -
          iteratedDeriv k (criticalCore c cut) v| ≤ B1 * |u - v| := by
    intro u v
    have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
      (𝕜 := ℝ) (s := Set.univ) (f := iteratedDeriv k (criticalCore c cut))
      (C := B1) (fun x _ ↦ hdiff x)
      (fun x _ ↦ by
        have hd : deriv (iteratedDeriv k (criticalCore c cut)) x =
            iteratedDeriv (k + 1) (criticalCore c cut) x :=
          (congrFun (iteratedDeriv_succ (n := k) (f := criticalCore c cut)) x).symm
        simpa [Real.norm_eq_abs, hd] using hbound1 x)
      convex_univ (x := v) (y := u) (Set.mem_univ _) (Set.mem_univ _)
    simpa [Real.norm_eq_abs] using hmvt
  refine ⟨C, hCpos, ?_⟩
  intro u v
  have hgamma0 := (holderFraction_mem_Ioc c).1.le
  have hgamma1 := (holderFraction_mem_Ioc c).2
  have hd0 : 0 ≤ |u - v| := abs_nonneg _
  by_cases hdle : |u - v| ≤ 1
  · calc
      _ ≤ B1 * |u - v| := hlip u v
      _ ≤ B1 * |u - v| ^ gamma :=
        mul_le_mul_of_nonneg_left
          (Real.self_le_rpow_of_le_one hd0 hdle hgamma1) hB1.le
      _ ≤ C * |u - v| ^ gamma :=
        mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hd0 gamma)
      _ = _ := by rfl
  · have hpow : 1 ≤ |u - v| ^ gamma :=
      Real.one_le_rpow (le_of_not_ge hdle) hgamma0
    have hlarge :
        |iteratedDeriv k (criticalCore c cut) u -
            iteratedDeriv k (criticalCore c cut) v| ≤ 2 * B0 := by
      calc
        _ = |iteratedDeriv k (criticalCore c cut) u +
              -iteratedDeriv k (criticalCore c cut) v| := by ring_nf
        _ ≤ |iteratedDeriv k (criticalCore c cut) u| +
              |-iteratedDeriv k (criticalCore c cut) v| := abs_add_le _ _
        _ = |iteratedDeriv k (criticalCore c cut) u| +
              |iteratedDeriv k (criticalCore c cut) v| := by simp
        _ ≤ B0 + B0 := add_le_add (hbound0 u) (hbound0 v)
        _ = 2 * B0 := by ring
    calc
      _ ≤ 2 * B0 := hlarge
      _ ≤ C := le_max_right _ _
      _ ≤ C * |u - v| ^ gamma := by
        simpa using mul_le_mul_of_nonneg_left hpow hCpos.le
      _ = _ := by rfl

/-- The bandwidth-scaled inner part of the critical direction. -/
@[no_expose]
noncomputable def scaledCriticalCore (c : ClassConstants) (cut : CutoffData c)
    (u h t : ℝ) : ℝ :=
  u * h ^ c.beta * criticalCore c cut ((1 - t) / h)

lemma scaledCriticalCore_contDiff (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) : ContDiff ℝ ∞ (scaledCriticalCore c cut u h) := by
  unfold scaledCriticalCore
  exact contDiff_const.mul ((criticalCore_contDiff c cut).comp
    ((contDiff_const.sub contDiff_id).div_const h))

/-- Exact derivative scaling for the normalized inner profile. -/
lemma iteratedDeriv_scaledCriticalCore (c : ClassConstants) (cut : CutoffData c)
    (u h : ℝ) (hh : h ≠ 0) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (scaledCriticalCore c cut u h) t =
      (u * h ^ c.beta) * ((-1 / h) ^ j) *
        iteratedDeriv j (criticalCore c cut) ((1 - t) / h) := by
  let f : ℝ → ℝ := fun x ↦ criticalCore c cut ((1 / h) * x)
  have hf : ContDiff ℝ j f :=
    (criticalCore_contDiff c cut).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le) |>.comp
      (contDiff_const.mul contDiff_id)
  have hscale := iteratedDeriv_comp_const_mul
    ((criticalCore_contDiff c cut).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le))
      (1 / h)
  have hflip := congrFun (iteratedDeriv_comp_const_sub j f 1) t
  have hfun : scaledCriticalCore c cut u h =
      fun z : ℝ ↦ (u * h ^ c.beta) * f (1 - z) := by
    funext z
    simp only [scaledCriticalCore, f]
    congr 2
    field_simp
  rw [hfun, iteratedDeriv_const_mul_field, hflip]
  change (u * h ^ c.beta) *
      ((-1 : ℝ) ^ j * iteratedDeriv j f (1 - t)) = _
  rw [show iteratedDeriv j f (1 - t) =
      (1 / h) ^ j * iteratedDeriv j (criticalCore c cut) ((1 / h) * (1 - t)) by
        exact congrFun hscale (1 - t)]
  have hpow : (-1 : ℝ) ^ j * (1 / h) ^ j = (-1 / h) ^ j := by
    rw [← mul_pow]
    congr 2
    field_simp
  have harg : (1 / h) * (1 - t) = (1 - t) / h := by field_simp
  rw [harg]
  calc
    _ = (u * h ^ c.beta) * ((-1 : ℝ) ^ j * (1 / h) ^ j) *
        iteratedDeriv j (criticalCore c cut) ((1 - t) / h) := by ring
    _ = _ := by rw [hpow]

private lemma critical_scaled_holder_cancel (c : ClassConstants)
    {h x y : ℝ} (hh : 0 < h) :
    h ^ c.beta * (h⁻¹) ^ holderOrder c *
        |(1 - x) / h - (1 - y) / h| ^ (c.beta - holderOrder c) =
      |x - y| ^ (c.beta - holderOrder c) := by
  let k := holderOrder c
  let gamma := c.beta - (k : ℝ)
  have hk : h ^ c.beta * (h⁻¹) ^ k = h ^ gamma := by
    dsimp [gamma]
    rw [Real.rpow_sub_natCast hh.ne' c.beta k, inv_pow]
    field_simp [pow_ne_zero k hh.ne']
  have hdist : |(1 - x) / h - (1 - y) / h| = |x - y| / h := by
    rw [show (1 - x) / h - (1 - y) / h = (y - x) / h by ring,
      abs_div, abs_sub_comm, abs_of_pos hh]
  rw [hk, hdist, Real.div_rpow (abs_nonneg _) hh.le gamma]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hh gamma)]
  rfl

/-- The normalized inner critical profile has a Hölder coefficient independent
of its positive bandwidth (up to one). -/
lemma exists_scaledCriticalCore_holder_uniform
    (c : ClassConstants) (cut : CutoffData c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u h : ℝ), 0 < h → h ≤ 1 →
      HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) (|u| * C)
        (scaledCriticalCore c cut u h) := by
  rcases criticalCore_holder c cut with ⟨C, hC, hholder⟩
  refine ⟨C, hC, ?_⟩
  intro u h hh _hh1
  constructor
  · exact (scaledCriticalCore_contDiff c cut u h).contDiffOn.of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top (holderOrder c)).le)
  · intro x hx y hy
    have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
    rw [iteratedDerivWithin_eq_iteratedDeriv hud
        ((scaledCriticalCore_contDiff c cut u h).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr
            (ENat.natCast_lt_top (holderOrder c)).le)) hx,
      iteratedDerivWithin_eq_iteratedDeriv hud
        ((scaledCriticalCore_contDiff c cut u h).contDiffAt.of_le
          (WithTop.coe_le_coe.mpr
            (ENat.natCast_lt_top (holderOrder c)).le)) hy,
      iteratedDeriv_scaledCriticalCore c cut u h hh.ne' (holderOrder c) x,
      iteratedDeriv_scaledCriticalCore c cut u h hh.ne' (holderOrder c) y]
    let ux := (1 - x) / h
    let uy := (1 - y) / h
    have htop := hholder ux uy
    have hfactor :
        (u * h ^ c.beta) * (-1 / h) ^ holderOrder c *
              iteratedDeriv (holderOrder c) (criticalCore c cut) ux -
            (u * h ^ c.beta) * (-1 / h) ^ holderOrder c *
              iteratedDeriv (holderOrder c) (criticalCore c cut) uy =
          (u * h ^ c.beta) * (-1 / h) ^ holderOrder c *
            (iteratedDeriv (holderOrder c) (criticalCore c cut) ux -
              iteratedDeriv (holderOrder c) (criticalCore c cut) uy) := by ring
    rw [hfactor, abs_mul, abs_mul]
    have hpows : |(-1 / h) ^ holderOrder c| = (h⁻¹) ^ holderOrder c := by
      rw [abs_pow, abs_div, abs_neg, abs_one, one_div, abs_of_pos hh]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hh.le _), hpows]
    calc
      |u| * h ^ c.beta * (h⁻¹) ^ holderOrder c *
          |iteratedDeriv (holderOrder c) (criticalCore c cut) ux -
            iteratedDeriv (holderOrder c) (criticalCore c cut) uy| ≤
        |u| * h ^ c.beta * (h⁻¹) ^ holderOrder c *
          (C * |ux - uy| ^ (c.beta - holderOrder c)) := by
            gcongr
      _ = |u| * C *
          (h ^ c.beta * (h⁻¹) ^ holderOrder c *
            |ux - uy| ^ (c.beta - holderOrder c)) := by ring
      _ = |u| * C * |x - y| ^ (c.beta - holderOrder c) := by
        rw [show h ^ c.beta * (h⁻¹) ^ holderOrder c *
            |ux - uy| ^ (c.beta - holderOrder c) =
              |x - y| ^ (c.beta - holderOrder c) by
          simpa [ux, uy] using critical_scaled_holder_cancel c hh]

/-- The fixed smooth remainder contributed by `psi - 1`. -/
@[no_expose]
noncomputable def criticalOuterRemainder (c : ClassConstants)
    (cut : CutoffData c) (t : ℝ) : ℝ :=
  let x := 1 - t
  if x = 0 then 0 else (cut.psi x - 1) / x

lemma criticalOuterRemainder_contDiffOn (c : ClassConstants) (cut : CutoffData c) :
    ContDiffOn ℝ ∞ (criticalOuterRemainder c cut) (Set.Icc (0 : ℝ) 1) := by
  apply contDiffOn_of_locally_contDiffOn
  intro t ht
  by_cases hnear : 1 - t < c.x0 / 4
  · refine ⟨{x : ℝ | 1 - x < c.x0 / 4}, isOpen_lt
        (continuous_const.sub continuous_id) continuous_const, hnear, ?_⟩
    apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) _).congr
    intro s hs
    unfold criticalOuterRemainder
    by_cases hx : 1 - s = 0
    · simp [hx]
    · rw [if_neg hx, cut.psi_one (1 - s) ⟨sub_nonneg.mpr hs.1.2, hs.2.le⟩]
      simp
  · have hx : 1 - t ≠ 0 := by
      intro hzero
      rw [hzero] at hnear
      exact hnear (div_pos c.x0_pos (by norm_num))
    refine ⟨{x : ℝ | 1 - x ≠ 0}, isOpen_compl_singleton.preimage
      (continuous_const.sub continuous_id), hx, ?_⟩
    let S := Set.Icc (0 : ℝ) 1 ∩ {x : ℝ | 1 - x ≠ 0}
    have harg : ContDiffOn ℝ ∞ (fun s : ℝ ↦ 1 - s) S := by fun_prop
    have hmap : Set.MapsTo (fun s : ℝ ↦ 1 - s) S (Set.Ici 0) := by
      intro s hs
      exact sub_nonneg.mpr hs.1.2
    have hpsi : ContDiffOn ℝ ∞ (fun s : ℝ ↦ cut.psi (1 - s)) S :=
      cut.psi_smooth.comp harg hmap
    have hreg : ContDiffOn ℝ ∞
        (fun s : ℝ ↦ (cut.psi (1 - s) - 1) / (1 - s)) S := by
      apply (hpsi.sub contDiffOn_const).div harg
      intro s hs hzero
      exact hs.2 hzero
    apply hreg.congr
    intro s hs
    unfold criticalOuterRemainder
    rw [if_neg hs.2]

/-- The fixed outer remainder has a finite positive Hölder coefficient. -/
lemma exists_criticalOuterRemainder_holder (c : ClassConstants) (cut : CutoffData c) :
    ∃ B : ℝ, 0 < B ∧ HolderSeminormLe (holderOrder c)
      (c.beta - holderOrder c) B (criticalOuterRemainder c cut) :=
  exists_holderSeminormLe_of_contDiffOn (holderOrder c)
    (c.beta - holderOrder c) (holderFraction_mem_Ioc c).1.le
    (holderFraction_mem_Ioc c).2 (criticalOuterRemainder_contDiffOn c cut)

/-- Hölder coefficients add under pointwise addition. -/
lemma HolderSeminormLe.add {k : ℕ} {gamma B D : ℝ} {f g : ℝ → ℝ}
    (hf : HolderSeminormLe k gamma B f) (hg : HolderSeminormLe k gamma D g) :
    HolderSeminormLe k gamma (B + D) (fun t ↦ f t + g t) := by
  constructor
  · exact hf.1.add hg.1
  · intro x hx y hy
    change |iteratedDerivWithin k (f + g) (Set.Icc (0 : ℝ) 1) x -
        iteratedDerivWithin k (f + g) (Set.Icc (0 : ℝ) 1) y| ≤ _
    rw [iteratedDerivWithin_add hx (uniqueDiffOn_Icc (by norm_num))
        (hf.1.contDiffWithinAt hx) (hg.1.contDiffWithinAt hx),
      iteratedDerivWithin_add hy (uniqueDiffOn_Icc (by norm_num))
        (hf.1.contDiffWithinAt hy) (hg.1.contDiffWithinAt hy)]
    calc
      |(iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x +
          iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) x) -
        (iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) y +
          iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) y)| ≤
          |iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x -
            iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) y| +
          |iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) x -
            iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) y| := by
              rw [show (iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x +
                    iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) x) -
                  (iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) y +
                    iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) y) =
                  (iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) x -
                    iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1) y) +
                  (iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) x -
                    iteratedDerivWithin k g (Set.Icc (0 : ℝ) 1) y) by ring]
              exact abs_add_le _ _
      _ ≤ B * |x - y| ^ gamma + D * |x - y| ^ gamma :=
        add_le_add (hf.2 x hx y hy) (hg.2 x hx y hy)
      _ = (B + D) * |x - y| ^ gamma := by ring

/-- The critical bandwidth normalization is exactly `h^(beta+1)`. -/
lemma critical_sqrt_normalization_eq_bandwidth_rpow (c : ClassConstants)
    {n : ℕ} (hn : 2 ≤ n) :
    1 / Real.sqrt ((n : ℝ) * Real.log n) =
      criticalBandwidth c n ^ (c.beta + 1) := by
  let z := (n : ℝ) * Real.log n
  have hz : 0 < z := mul_pos (by exact_mod_cast (show 0 < n by omega))
    (Real.log_pos (by exact_mod_cast hn))
  have hden : 2 * c.beta + 2 ≠ 0 := by nlinarith [c.beta_pos]
  have hb : 1 + c.beta ≠ 0 := by linarith [c.beta_pos]
  unfold criticalBandwidth
  change 1 / Real.sqrt z = (z ^ (-(1 / (2 * c.beta + 2)))) ^ (c.beta + 1)
  rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hz.le, ← Real.rpow_mul hz.le]
  congr 1
  rw [show 2 * c.beta + 2 = 2 * (c.beta + 1) by ring]
  field_simp [hb]
  rw [div_self (by linarith [c.beta_pos] : c.beta + 1 ≠ 0)]

/-- For sufficiently small bandwidth the critical direction splits into its
scaled inner profile and a fixed smooth outer remainder. -/
lemma criticalDirection_eq_scaledCore_add_outer (c : ClassConstants)
    (cut : CutoffData c) {u : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hhsmall : criticalBandwidth c n ≤ c.x0 / 8)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    criticalDirection c cut u n t =
      scaledCriticalCore c cut u (criticalBandwidth c n) t +
        (u / Real.sqrt ((n : ℝ) * Real.log n)) *
          criticalOuterRemainder c cut t := by
  let h := criticalBandwidth c n
  let x := 1 - t
  have hh : 0 < h := criticalBandwidth_pos c hn
  have hx0 : 0 ≤ x := sub_nonneg.mpr ht.2
  have hnorm : 1 / Real.sqrt ((n : ℝ) * Real.log n) = h ^ (c.beta + 1) :=
    critical_sqrt_normalization_eq_bandwidth_rpow c hn
  by_cases hx : x = 0
  · rw [show t = 1 by dsimp [x] at hx; linarith]
    simp [criticalDirection, scaledCriticalCore, criticalOuterRemainder, criticalCore]
  have hcore : criticalCore c cut (x / h) = cut.chi (x / h) / (x / h) := by
    rw [criticalCore, if_neg]
    exact not_le.mpr (div_pos (lt_of_le_of_ne hx0 (Ne.symm hx)) hh)
  by_cases hpsi : cut.psi x = 1
  · simp only [criticalDirection, scaledCriticalCore, criticalOuterRemainder]
    rw [show 1 - t = x by rfl, if_neg hx]
    simp only [if_neg hx]
    change (u / Real.sqrt ((n : ℝ) * Real.log n)) *
        cut.chi (x / h) * cut.psi x / x =
      u * h ^ c.beta * criticalCore c cut (x / h) +
        (u / Real.sqrt ((n : ℝ) * Real.log n)) * ((cut.psi x - 1) / x)
    rw [hpsi, sub_self, zero_div, mul_zero, add_zero, hcore]
    rw [show u / Real.sqrt ((n : ℝ) * Real.log n) =
      u * (1 / Real.sqrt ((n : ℝ) * Real.log n)) by ring, hnorm]
    rw [Real.rpow_add hh]
    field_simp [hh.ne', hx]
    simp only [Real.rpow_one]
  · have hxlarge : c.x0 / 4 < x := by
      by_contra hle
      exact hpsi (cut.psi_one x ⟨hx0, le_of_not_gt hle⟩)
    have hscaled : 2 ≤ x / h := by
      apply (le_div_iff₀ hh).2
      calc
        2 * h ≤ 2 * (c.x0 / 8) := mul_le_mul_of_nonneg_left hhsmall (by norm_num)
        _ ≤ x := (by linarith : 2 * (c.x0 / 8) < x).le
    have hchi : cut.chi (x / h) = 1 := cut.chi_one _ hscaled
    simp only [criticalDirection, scaledCriticalCore, criticalOuterRemainder]
    rw [show 1 - t = x by rfl, if_neg hx]
    simp only [if_neg hx]
    change (u / Real.sqrt ((n : ℝ) * Real.log n)) *
        cut.chi (x / h) * cut.psi x / x =
      u * h ^ c.beta * criticalCore c cut (x / h) +
        (u / Real.sqrt ((n : ℝ) * Real.log n)) * ((cut.psi x - 1) / x)
    rw [hcore, hchi]
    rw [show u / Real.sqrt ((n : ℝ) * Real.log n) =
      u * (1 / Real.sqrt ((n : ℝ) * Real.log n)) by ring, hnorm,
      Real.rpow_add hh]
    field_simp [hh.ne', hx]
    simp only [Real.rpow_one]
    ring

/-- Equality on the study interval transports a Hölder bound. -/
lemma HolderSeminormLe.congr {k : ℕ} {gamma B : ℝ} {f g : ℝ → ℝ}
    (hf : HolderSeminormLe k gamma B f)
    (hfg : Set.EqOn f g (Set.Icc (0 : ℝ) 1)) :
    HolderSeminormLe k gamma B g := by
  constructor
  · exact hf.1.congr fun x hx ↦ (hfg hx).symm
  · intro x hx y hy
    rw [iteratedDerivWithin_congr hfg.symm hx,
      iteratedDerivWithin_congr hfg.symm hy]
    exact hf.2 x hx y hy

/-- The critical bandwidth tends to zero with sample size. -/
lemma criticalBandwidth_tendsto_zero (c : ClassConstants) :
    Filter.Tendsto (criticalBandwidth c) Filter.atTop (nhds (0 : ℝ)) := by
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlog : Filter.Tendsto (fun n : ℕ ↦ Real.log (n : ℝ))
      Filter.atTop Filter.atTop := Real.tendsto_log_atTop.comp hcast
  have hprod : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) * Real.log n)
      Filter.atTop Filter.atTop := hcast.atTop_mul_atTop₀ hlog
  have ha : 0 < 1 / (2 * c.beta + 2) :=
    one_div_pos.mpr (by nlinarith [c.beta_pos])
  unfold criticalBandwidth
  convert (tendsto_rpow_neg_atTop ha).comp hprod using 1
  funext n
  rfl

/-- Eventually the critical bandwidth is at most one and lies inside the
region where `psi` is identically one. -/
lemma exists_criticalBandwidth_small (c : ClassConstants) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      criticalBandwidth c n ≤ 1 ∧ criticalBandwidth c n ≤ c.x0 / 8 := by
  have hevent : ∀ᶠ n in Filter.atTop,
      criticalBandwidth c n < min 1 (c.x0 / 8) :=
    (tendsto_order.1 (criticalBandwidth_tendsto_zero c)).2 _
      (lt_min zero_lt_one (div_pos c.x0_pos (by norm_num)))
  rcases (Filter.eventually_atTop.1 hevent) with ⟨N0, hN0⟩
  refine ⟨max 3 N0, le_max_left _ _, fun n hn ↦ ?_⟩
  have hlt := hN0 n (le_trans (le_max_right _ _) hn)
  exact ⟨hlt.le.trans (min_le_left _ _), hlt.le.trans (min_le_right _ _)⟩

/-- Uniform-in-sample-size Hölder control of the critical direction once the
bandwidth is in its asymptotic range. -/
lemma exists_criticalDirection_holder_uniform (c : ClassConstants)
    (cut : CutoffData c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ) {n : ℕ}, 3 ≤ n →
      criticalBandwidth c n ≤ 1 →
      criticalBandwidth c n ≤ c.x0 / 8 →
      HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) (|u| * C)
        (criticalDirection c cut u n) := by
  rcases exists_scaledCriticalCore_holder_uniform c cut with ⟨C, hC, hcore⟩
  rcases exists_criticalOuterRemainder_holder c cut with ⟨B, hB, houter⟩
  refine ⟨C + B, add_pos hC hB, ?_⟩
  intro u n hn hh1 hhx
  have hn2 : 2 ≤ n := by omega
  let h := criticalBandwidth c n
  let a := u / Real.sqrt ((n : ℝ) * Real.log n)
  have ha : |a| ≤ |u| := by
    have hnorm : a = u * h ^ (c.beta + 1) := by
      dsimp [a]
      rw [show u / Real.sqrt ((n : ℝ) * Real.log n) =
        u * (1 / Real.sqrt ((n : ℝ) * Real.log n)) by ring,
        critical_sqrt_normalization_eq_bandwidth_rpow c hn2]
    rw [hnorm, abs_mul, abs_of_nonneg (Real.rpow_nonneg
      (criticalBandwidth_pos c hn2).le _)]
    simpa using mul_le_mul_of_nonneg_left
      (Real.rpow_le_one (criticalBandwidth_pos c hn2).le hh1
        (by linarith [c.beta_pos] : 0 ≤ c.beta + 1)) (abs_nonneg u)
  have hout : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c)
      (|u| * B) (fun t ↦ a * criticalOuterRemainder c cut t) := by
    exact (houter.const_mul).mono_constant
      (mul_le_mul_of_nonneg_right ha hB.le)
  have hadd := (hcore u h (criticalBandwidth_pos c hn2) hh1).add hout
  have hcoeff : |u| * C + |u| * B = |u| * (C + B) := by ring
  rw [hcoeff] at hadd
  apply hadd.congr
  intro t ht
  exact (criticalDirection_eq_scaledCore_add_outer c cut hn2 hhx ht).symm

lemma critical_normalization_eq_bandwidth_beta (c : ClassConstants)
    {n : ℕ} (hn : 2 ≤ n) :
    1 / (Real.sqrt ((n : ℝ) * Real.log n) * criticalBandwidth c n) =
      criticalBandwidth c n ^ c.beta := by
  let h := criticalBandwidth c n
  have hh : 0 < h := criticalBandwidth_pos c hn
  calc
    1 / (Real.sqrt ((n : ℝ) * Real.log n) * h) =
        (1 / Real.sqrt ((n : ℝ) * Real.log n)) / h := by ring
    _ = h ^ (c.beta + 1) / h := by
      rw [critical_sqrt_normalization_eq_bandwidth_rpow c hn]
    _ = h ^ c.beta := by
      rw [Real.rpow_add hh, Real.rpow_one]
      field_simp [hh.ne']

/-- The critical direction is globally measurable.  Outside the study horizon
the support condition on `psi` makes it identically zero. -/
lemma criticalDirection_measurable (c : ClassConstants) (cut : CutoffData c)
    (u : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    Measurable (criticalDirection c cut u n) := by
  have hout : ∀ t : ℝ, t ∉ Set.Icc (0 : ℝ) 1 →
      criticalDirection c cut u n t = 0 := by
    intro t ht
    have htcase : t < 0 ∨ 1 < t := by
      by_cases h0 : 0 ≤ t
      · right
        exact lt_of_not_ge fun h1 ↦ ht ⟨h0, h1⟩
      · left
        exact lt_of_not_ge h0
    have hpsi : cut.psi (1 - t) = 0 := by
      by_contra hne
      have hs := cut.psi_support (1 - t) hne
      rcases htcase with htneg | htone
      · have hx0 : c.x0 ≤ 1 / 2 := c.x0_le
        linarith [hs.2]
      · linarith [hs.1]
    unfold criticalDirection
    by_cases hx : 1 - t = 0
    · simp [hx]
    · rw [if_neg hx, hpsi]
      ring
  have hm : Measurable (Set.piecewise (Set.Icc (0 : ℝ) 1)
      (criticalDirection c cut u n) (fun _ : ℝ ↦ (0 : ℝ))) :=
    ContinuousOn.measurable_piecewise
      (f := criticalDirection c cut u n) (g := fun _ : ℝ ↦ (0 : ℝ))
      (criticalDirection_continuousOn c cut u hn) continuousOn_const measurableSet_Icc
  convert hm using 1
  funext t
  by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
  · simp [Set.piecewise, ht]
  · simp [Set.piecewise, ht, hout t ht]

/-- A single amplitude radius and sample-size threshold simultaneously preserve
the midpoint intensity band and the recurrence Hölder radius. -/
lemma exists_criticalDirection_midpoint_band_holder_uniform
    (c : ClassConstants) (cut : CutoffData c) :
    ∃ u0 : ℝ, 0 < u0 ∧ ∃ N : ℕ, 3 ≤ N ∧
      ∀ u : ℝ, 0 < u → u ≤ u0 → ∀ n : ℕ, N ≤ n →
        (∀ t ∈ Set.Icc (0 : ℝ) 1,
          c.lambdaMin ≤ midpointLambda c + criticalDirection c cut u n t ∧
          midpointLambda c + criticalDirection c cut u n t ≤ c.lambdaMax) ∧
        HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) c.Llambda
          (fun t ↦ midpointLambda c + criticalDirection c cut u n t) := by
  rcases exists_criticalDirection_holder_uniform c cut with ⟨C, hC, hholder⟩
  rcases cut.exists_critical_abs_bounds c with
    ⟨Cchi, Cpsi, hCchi, hCpsi, hchi, hpsi⟩
  rcases exists_criticalBandwidth_small c with ⟨N, hN3, hN⟩
  let margin := min (midpointLambda c - c.lambdaMin)
    (c.lambdaMax - midpointLambda c)
  have hmargin : 0 < margin := by
    exact lt_min (sub_pos.mpr (midpoint_strict_bounds c).1)
      (sub_pos.mpr (midpoint_strict_bounds c).2.1)
  let D := Cchi * Cpsi + 1
  have hD : 0 < D := by
    dsimp [D]
    nlinarith [mul_nonneg hCchi hCpsi]
  let u0 := min (c.Llambda / C) (margin / D)
  have hu0 : 0 < u0 := lt_min (div_pos c.Llambda_pos hC) (div_pos hmargin hD)
  refine ⟨u0, hu0, N, hN3, ?_⟩
  intro u hu hu0le n hn
  have hsmall := hN n hn
  have hn3 : 3 ≤ n := hN3.trans hn
  have hn2 : 2 ≤ n := by omega
  have huabs : |u| = u := abs_of_pos hu
  have hampHolder : |u| * C ≤ c.Llambda := by
    rw [huabs]
    calc
      u * C ≤ u0 * C := mul_le_mul_of_nonneg_right hu0le hC.le
      _ ≤ (c.Llambda / C) * C :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) hC.le
      _ = c.Llambda := by field_simp [hC.ne']
  have hdirHolder := (hholder u hn3 hsmall.1 hsmall.2).mono_constant hampHolder
  have hfullHolder : HolderSeminormLe (holderOrder c)
      (c.beta - holderOrder c) c.Llambda
      (fun t ↦ midpointLambda c + criticalDirection c cut u n t) :=
    HolderSeminormLe.const_add (lambda0 := midpointLambda c) hdirHolder
  refine ⟨?_, hfullHolder⟩
  intro t ht
  have hraw := criticalDirection_abs_le c cut (u := u) hn2
    hCchi hCpsi hchi hpsi ht
  rw [div_eq_mul_inv, ← one_div,
    critical_normalization_eq_bandwidth_beta c hn2] at hraw
  have hrpow : criticalBandwidth c n ^ c.beta ≤ 1 :=
    Real.rpow_le_one (criticalBandwidth_pos c hn2).le hsmall.1 c.beta_pos.le
  have hA : Cchi * Cpsi ≤ D := by
    dsimp [D]
    linarith
  have hdir : |criticalDirection c cut u n t| ≤ margin := by
    calc
      _ ≤ |u| * Cchi * Cpsi * criticalBandwidth c n ^ c.beta := by
        simpa [mul_assoc] using hraw
      _ ≤ u * (Cchi * Cpsi) := by
        rw [huabs]
        calc
          u * Cchi * Cpsi * criticalBandwidth c n ^ c.beta =
              (u * (Cchi * Cpsi)) * criticalBandwidth c n ^ c.beta := by ring
          _ ≤ (u * (Cchi * Cpsi)) * 1 :=
            mul_le_mul_of_nonneg_left hrpow
              (mul_nonneg hu.le (mul_nonneg hCchi hCpsi))
          _ = u * (Cchi * Cpsi) := by ring
      _ ≤ u * D := mul_le_mul_of_nonneg_left hA hu.le
      _ ≤ u0 * D := mul_le_mul_of_nonneg_right hu0le hD.le
      _ ≤ (margin / D) * D :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
      _ = margin := by field_simp [hD.ne']
  constructor
  · have hl := neg_le_of_abs_le (hdir.trans (min_le_left _ _))
    linarith
  · have hu' := le_of_abs_le (hdir.trans (min_le_right _ _))
    linarith

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
