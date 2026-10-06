module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.CriticalDirection
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.EndpointDirectionBounds
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Hölder control for the critical lower-bound direction

The critical direction is smooth on the study horizon: its cutoff makes it
identically zero on a neighborhood of the apparent endpoint singularity.
Compactness then supplies a finite Hölder coefficient for its normalized
shape, and scalar multiplication gives the exact linear dependence on the
perturbation amplitude.
-/

public section

open Set
open scoped ContDiff

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Every fixed derivative of `chi` has a positive absolute bound on its
transition interval. -/
lemma CutoffData.exists_chi_iteratedDerivWithin_bound
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Set.Icc (0 : ℝ) 2,
      |iteratedDerivWithin j cut.chi (Set.Icc (0 : ℝ) 2) x| ≤ B := by
  have hsmooth : ContDiffOn ℝ ∞ cut.chi (Set.Icc (0 : ℝ) 2) :=
    cut.chi_smooth.mono Set.Icc_subset_Ici_self
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 2) := uniqueDiffOn_Icc (by norm_num)
  have hcont : ContinuousOn
      (fun x ↦ |iteratedDerivWithin j cut.chi (Set.Icc (0 : ℝ) 2) x|)
      (Set.Icc (0 : ℝ) 2) :=
    (hsmooth.continuousOn_iteratedDerivWithin
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le) hud).abs
  let B := max 1 (sSup ((fun x ↦
    |iteratedDerivWithin j cut.chi (Set.Icc (0 : ℝ) 2) x|) ''
      Set.Icc (0 : ℝ) 2))
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx ↦ ?_⟩
  exact (hcont.le_sSup_image_Icc hx).trans (le_max_right _ _)

/-- Every fixed derivative of `psi` has a positive absolute bound on the
study interval. -/
lemma CutoffData.exists_psi_iteratedDerivWithin_bound
    (c : ClassConstants) (cut : CutoffData c) (j : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin j cut.psi (Set.Icc (0 : ℝ) 1) x| ≤ B := by
  have hsmooth : ContDiffOn ℝ ∞ cut.psi (Set.Icc (0 : ℝ) 1) :=
    cut.psi_smooth.mono Set.Icc_subset_Ici_self
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hcont : ContinuousOn
      (fun x ↦ |iteratedDerivWithin j cut.psi (Set.Icc (0 : ℝ) 1) x|)
      (Set.Icc (0 : ℝ) 1) :=
    (hsmooth.continuousOn_iteratedDerivWithin
      (WithTop.coe_le_coe.mpr (ENat.natCast_lt_top j).le) hud).abs
  let B := max 1 (sSup ((fun x ↦
    |iteratedDerivWithin j cut.psi (Set.Icc (0 : ℝ) 1) x|) ''
      Set.Icc (0 : ℝ) 1))
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x hx ↦ ?_⟩
  exact (hcont.le_sSup_image_Icc hx).trans (le_max_right _ _)

/-- Any infinitely smooth function on the unit interval has a finite positive
Hölder coefficient at every exponent in `[0,1]`. -/
lemma exists_holderSeminormLe_of_contDiffOn
    {f : ℝ → ℝ} (k : ℕ) (gamma : ℝ)
    (_hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1)
    (hf : ContDiffOn ℝ ∞ f (Set.Icc (0 : ℝ) 1)) :
    ∃ B : ℝ, 0 < B ∧ HolderSeminormLe k gamma B f := by
  let g : ℝ → ℝ := iteratedDerivWithin k f (Set.Icc (0 : ℝ) 1)
  let q : ℝ → ℝ := fun x ↦
    |iteratedDerivWithin (k + 1) f (Set.Icc (0 : ℝ) 1) x|
  let B : ℝ := max 1 (sSup (q '' Set.Icc (0 : ℝ) 1))
  have hud : UniqueDiffOn ℝ (Set.Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num)
  have hk : (k : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (ENat.natCast_lt_top k).le
  have hklt : (k : WithTop ℕ∞) < ∞ :=
    WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k)
  have hk1 : ((k + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (ENat.natCast_lt_top (k + 1)).le
  have hqcont : ContinuousOn q (Set.Icc (0 : ℝ) 1) := by
    exact (hf.continuousOn_iteratedDerivWithin hk1 hud).abs
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨B, hBpos, hf.of_le hk, ?_⟩
  intro x hx y hy
  have hdiff : DifferentiableOn ℝ g (Set.Icc (0 : ℝ) 1) := by
    exact hf.differentiableOn_iteratedDerivWithin hklt hud
  have hderiv : ∀ z ∈ Set.Icc (0 : ℝ) 1,
      ‖derivWithin g (Set.Icc (0 : ℝ) 1) z‖ ≤ B := by
    intro z hz
    rw [← iteratedDerivWithin_succ]
    change q z ≤ B
    exact (hqcont.le_sSup_image_Icc hz).trans (le_max_right _ _)
  have hlip := Convex.norm_image_sub_le_of_norm_derivWithin_le
    hdiff hderiv (convex_Icc (0 : ℝ) 1) hy hx
  have hdist : |x - y| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  calc
    |g x - g y| ≤ B * |x - y| := by
      simpa [Real.norm_eq_abs, abs_sub_comm] using hlip
    _ ≤ B * |x - y| ^ gamma := by
      exact mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (abs_nonneg _) hdist hgamma1) hBpos.le

/-- Scalar multiplication multiplies a Hölder coefficient by the absolute
value of the scalar. -/
lemma HolderSeminormLe.const_mul
    {k : ℕ} {gamma B a : ℝ} {f : ℝ → ℝ}
    (hf : HolderSeminormLe k gamma B f) :
    HolderSeminormLe k gamma (|a| * B) (fun t ↦ a * f t) := by
  constructor
  · exact contDiffOn_const.mul hf.1
  · intro x hx y hy
    simp only [iteratedDerivWithin_const_mul_field]
    rw [← mul_sub, abs_mul]
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left (hf.2 x hx y hy) (abs_nonneg a)

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
