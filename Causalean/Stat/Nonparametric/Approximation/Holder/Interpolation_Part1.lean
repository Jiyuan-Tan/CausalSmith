/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Kernel
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Analytic ingredients for Hölder pointwise-to-`L¹` interpolation

This file proves the reusable analytic steps used by the interpolation capstone in
`Interpolation_Part2.lean`: bandwidth optimization, change of variables for a smoothed value,
mass and moment identities for product kernels on the unit cube, cancellation of diagonal Taylor
terms, and the one-dimensional Taylor remainder along a line. The final construction of the
moment-cancelling kernel is in `Kernel.lean`; the pointwise-to-local-`L¹` theorem is in
`Interpolation_Part2.lean`.
-/

public section

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff
/-- The bandwidth optimization converts a lower bound on a kernel-smoothed signal
into the Hölder interpolation rate: local absolute mass grows at least as the
pointwise signal to the power one plus dimension divided by smoothness.

This is the pure real-analysis kernel of the optimization step: `h⁻ᵈ = c_*⁻ᵈ ·
Δ^{-d/γ}`, so `3Δ/4 ≤ ‖K‖_∞ c_*⁻ᵈ Δ^{-d/γ} I` rearranges to the claim via
`Δ · Δ^{d/γ} = Δ^{1 + d/γ}`. -/
theorem l1_lower_of_bias_bound {d : ℕ} {γ Ksup Δ Ival cstar h : ℝ}
    (hKsup : 0 < Ksup) (hΔ : 0 < Δ) (hcstar : 0 < cstar)
    (hheq : h = cstar * Δ ^ ((1 : ℝ) / γ))
    (hbound : 3 * Δ / 4 ≤ Ksup * h⁻¹ ^ d * Ival) :
    (3 / (4 * Ksup)) * cstar ^ d * Δ ^ (1 + (d : ℝ) / γ) ≤ Ival := by
  have hqpos : (0 : ℝ) < Δ ^ ((d : ℝ) / γ) := Real.rpow_pos_of_pos hΔ _
  have hcpos : 0 < cstar ^ d := pow_pos hcstar _
  have hABpos : 0 < cstar ^ d * Δ ^ ((d : ℝ) / γ) := mul_pos hcpos hqpos
  -- `h ^ d = cstar ^ d * Δ ^ (d/γ)`.
  have hpow : h ^ d = cstar ^ d * Δ ^ ((d : ℝ) / γ) := by
    have h1 : (Δ ^ ((1 : ℝ) / γ)) ^ d = Δ ^ ((d : ℝ) / γ) := by
      rw [← Real.rpow_natCast (Δ ^ ((1 : ℝ) / γ)) d, ← Real.rpow_mul hΔ.le]
      congr 1
      ring
    rw [hheq, mul_pow, h1]
  -- Rewrite the hypothesis with the explicit `h ^ d`.
  rw [inv_pow, hpow] at hbound
  -- Clear the inverse: `(3Δ/4)·(cstar^d·Δ^{d/γ}) ≤ Ksup·Ival`.
  have hmul : 3 * Δ / 4 * (cstar ^ d * Δ ^ ((d : ℝ) / γ)) ≤ Ksup * Ival := by
    have h2 := mul_le_mul_of_nonneg_right hbound hABpos.le
    have e : Ksup * (cstar ^ d * Δ ^ ((d : ℝ) / γ))⁻¹ * Ival
        * (cstar ^ d * Δ ^ ((d : ℝ) / γ)) = Ksup * Ival := by
      field_simp
    rwa [e] at h2
  -- `Δ ^ (1 + d/γ) = Δ · Δ ^ (d/γ)`.
  have hΔadd : Δ ^ (1 + (d : ℝ) / γ) = Δ * Δ ^ ((d : ℝ) / γ) := by
    rw [Real.rpow_add hΔ, Real.rpow_one]
  have goaleq : (3 / (4 * Ksup)) * cstar ^ d * (Δ * Δ ^ ((d : ℝ) / γ))
      = (3 * Δ / 4 * (cstar ^ d * Δ ^ ((d : ℝ) / γ))) / Ksup := by
    field_simp
  rw [hΔadd, goaleq, div_le_iff₀ hKsup, mul_comm Ival Ksup]
  exact hmul

-- The basic geometry/measure API for `supBall` (`supBall_eq_pi`, `isCompact_supBall`,
-- `measurableSet_supBall`, `mem_supBall_self`, `volume_supBall`) lives next to the
-- definition in `Defs.lean`.

/-- **Change-of-variables control of the kernel-smoothed value.** The absolute value of the
kernel-smoothed value in `u`-coordinates is bounded by the
scaled local `L¹` mass: `|∫_{[-1,1]^d} K(u) g(x0 + h•u) du| ≤ B^d · h⁻ᵈ · ∫_{supBall x0 r} |g|`.
Uses `|K| ≤ B^d`, the affine change of variables `x = x0 + h•u`, and that the image cube
`supBall x0 h ⊆ supBall x0 r` when `h ≤ r`. -/
lemma smoothed_abs_le {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ} {S : Set (Fin d → ℝ)}
    {k : ℝ → ℝ} {B : ℝ}
    (hS : supBall x0 r ⊆ S)
    (hkbd : ∀ u : Fin d → ℝ, |prodKernel k d u| ≤ B ^ d)
    (g : (Fin d → ℝ) → ℝ) (hg : HolderBallStd g γ M S)
    (h : ℝ) (hh : 0 < h) (hhr : h ≤ r) :
    |∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
      ≤ B ^ d * (h⁻¹) ^ d * ∫ x in supBall x0 r, |g x| := by
  have hBd0 : 0 ≤ B ^ d := le_trans (abs_nonneg _) (hkbd 0)
  have hgS : ContinuousOn g S := hg.1.continuousOn
  -- The affine map `u ↦ x0 + h•u` sends the unit cube into `S`.
  have hmaps : Set.MapsTo (fun u => x0 + h • u) (supBall (0 : Fin d → ℝ) 1) S := by
    intro u hu
    apply hS
    intro i
    have huq : (x0 + h • u) i - x0 i = h * u i := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [huq, abs_mul, abs_of_pos hh]
    have hui : |u i| ≤ 1 := by simpa using hu i
    calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
      _ = h := mul_one h
      _ ≤ r := hhr
  have hgcomp : ContinuousOn (fun u => g (x0 + h • u)) (supBall (0 : Fin d → ℝ) 1) :=
    hgS.comp (by fun_prop : Continuous (fun u : Fin d → ℝ => x0 + h • u)).continuousOn hmaps
  have hgcomp_int : IntegrableOn (fun u => |g (x0 + h • u)|) (supBall (0 : Fin d → ℝ) 1) :=
    (hgcomp.abs).integrableOn_compact (isCompact_supBall 0 1)
  have hg_abs_int : IntegrableOn (fun x => |g x|) (supBall x0 r) :=
    ((hgS.mono hS).abs).integrableOn_compact (isCompact_supBall x0 r)
  -- Two set identities for the affine change of variables.
  have hsmul_set : h • supBall (0 : Fin d → ℝ) 1 = supBall (0 : Fin d → ℝ) h := by
    ext x
    simp only [Set.mem_smul_set]
    constructor
    · rintro ⟨u, hu, rfl⟩ i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, abs_mul, abs_of_pos hh]
      have hui : |u i| ≤ 1 := by simpa using hu i
      calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
        _ = h := mul_one h
    · intro hx
      refine ⟨h⁻¹ • x, ?_, smul_inv_smul₀ hh.ne' x⟩
      intro i
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_zero, abs_mul, abs_inv,
        abs_of_pos hh]
      have hxi : |x i| ≤ h := by simpa using hx i
      calc h⁻¹ * |x i| ≤ h⁻¹ * h := mul_le_mul_of_nonneg_left hxi (by positivity)
        _ = 1 := inv_mul_cancel₀ hh.ne'
  have hme : MeasurableEmbedding (fun w => x0 + w : (Fin d → ℝ) → (Fin d → ℝ)) :=
    (Homeomorph.addLeft x0).measurableEmbedding
  have hmp : MeasurePreserving (fun w => x0 + w) (volume : Measure (Fin d → ℝ)) volume :=
    measurePreserving_add_left volume x0
  have himg : (fun w => x0 + w) '' supBall (0 : Fin d → ℝ) h = supBall x0 h := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩ i
      simp only [Pi.add_apply, add_sub_cancel_left]
      simpa using hw i
    · intro hy
      refine ⟨y - x0, ?_, by simp⟩
      intro i
      simpa using hy i
  have htrans : ∫ y in supBall x0 h, |g y| = ∫ w in supBall (0 : Fin d → ℝ) h, |g (x0 + w)| := by
    have := hmp.setIntegral_image_emb hme (fun y => |g y|) (supBall (0 : Fin d → ℝ) h)
    rwa [himg] at this
  -- Change of variables `x = x0 + h•u` then restrict the cube to the ball of radius `r`.
  have key : ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)|
      ≤ (h ^ d)⁻¹ * ∫ x in supBall x0 r, |g x| := by
    have cov : ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)|
        = (h ^ d)⁻¹ * ∫ y in supBall x0 h, |g y| := by
      rw [Measure.setIntegral_comp_smul_of_pos (μ := volume) (fun w => |g (x0 + w)|)
        (supBall (0 : Fin d → ℝ) 1) hh, hsmul_set, Module.finrank_fin_fun, smul_eq_mul,
        ← htrans]
    rw [cov]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hsub : supBall x0 h ⊆ supBall x0 r := fun x hx i => le_trans (hx i) hhr
    exact setIntegral_mono_set hg_abs_int (ae_of_all _ (fun x => abs_nonneg _))
      (ae_of_all _ (fun x hx => hsub hx))
  calc |∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
      = ‖∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1, ‖prodKernel k d u * g (x0 + h • u)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ u in supBall (0 : Fin d → ℝ) 1, |prodKernel k d u| * |g (x0 + h • u)| := by
        simp only [Real.norm_eq_abs, abs_mul]
    _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1, B ^ d * |g (x0 + h • u)| :=
        integral_mono_of_nonneg
          (ae_of_all _ (fun u => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
          (hgcomp_int.const_mul (B ^ d))
          (ae_of_all _ (fun u => mul_le_mul_of_nonneg_right (hkbd u) (abs_nonneg _)))
    _ = B ^ d * ∫ u in supBall (0 : Fin d → ℝ) 1, |g (x0 + h • u)| :=
        integral_const_mul _ _
    _ ≤ B ^ d * ((h ^ d)⁻¹ * ∫ x in supBall x0 r, |g x|) :=
        mul_le_mul_of_nonneg_left key hBd0
    _ = B ^ d * (h⁻¹) ^ d * ∫ x in supBall x0 r, |g x| := by rw [inv_pow]; ring

/-- The tensor kernel vanishes outside the unit cube `supBall 0 1`. -/
private lemma prodKernel_eq_zero_of_not_mem {d : ℕ} {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    {u : Fin d → ℝ} (hu : u ∉ supBall (0 : Fin d → ℝ) 1) :
    prodKernel k d u = 0 := by
  simp only [supBall, Causalean.Mathlib.Analysis.supBall, Set.mem_ofPred_eq,
    not_forall, not_le] at hu
  obtain ⟨i, hi⟩ := hu
  simp only [Pi.zero_apply, sub_zero] at hi
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hk_supp _ hi)

/-- The 1-D kernel has full-line integral `1` (extend the `[-1,1]` mass by support). -/
private lemma kernel_integral_full {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1) :
    ∫ t, k t = 1 := by
  rw [← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Set.Icc (-1 : ℝ) 1) (f := k) (fun t ht => ?_)]
  · exact hk_mass
  · apply hk_supp
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith

/-- **Kernel mass over the cube.** `∫_{[-1,1]^d} K = 1`. -/
lemma prodKernel_mass_cube {d : ℕ} {k : ℝ → ℝ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u = 1 := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => prodKernel_eq_zero_of_not_mem hk_supp hu)]
  rw [prodKernel_integral, kernel_integral_full hk_supp hk_mass, one_pow]

/-- **Kernel moment over the cube.** `∫ t^j k(t) dt` on the full line agrees with the
`[-1,1]` integral (support), so vanishes for `1 ≤ j ≤ m`. -/
private lemma kernel_moment_full {k : ℝ → ℝ} {j : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0) :
    ∫ t, t ^ j * k t = ∫ t in Set.Icc (-1 : ℝ) 1, t ^ j * k t := by
  refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun t ht => ?_)).symm
  have hk0 : k t = 0 := by
    apply hk_supp
    simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · rw [lt_abs]; right; linarith
    · rw [lt_abs]; left; linarith
  rw [hk0, mul_zero]

/-- **Multi-index moment vanishing over the cube.** For a multi-index `ν` with total
degree `1 ≤ ∑ νᵢ ≤ m`, the monomial-weighted kernel integral over the cube vanishes. -/
private lemma prodKernel_multiIndex_moment_cube {d : ℕ} {k : ℝ → ℝ} {m : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (ν : Fin d → ℕ) (hν1 : 1 ≤ ∑ i, ν i) (hνm : (∑ i, ν i) ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, (∏ i, u i ^ ν i) * prodKernel k d u = 0 := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun u hu => by rw [prodKernel_eq_zero_of_not_mem hk_supp hu, mul_zero])]
  rw [prodKernel_moment]
  -- Some coordinate `i0` has `1 ≤ ν i0 ≤ m`; its 1-D moment factor vanishes.
  obtain ⟨i0, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by omega : (∑ i, ν i) ≠ 0)
  have hi0_1 : 1 ≤ ν i0 := Nat.one_le_iff_ne_zero.mpr hi0
  have hi0_m : ν i0 ≤ m :=
    le_trans (Finset.single_le_sum (fun i _ => Nat.zero_le _) (Finset.mem_univ i0)) hνm
  refine Finset.prod_eq_zero (Finset.mem_univ i0) ?_
  rw [kernel_moment_full hk_supp]
  exact hk_mom _ hi0_1 hi0_m

/-- **Single-monomial (permutation) moment vanishing.** For `p : Fin j → Fin d` with
`1 ≤ j ≤ m`, `∫ (∏ₗ u_{p l}) K(u) = 0`, by regrouping the product fibrewise into a
multi-index of total degree `j`. -/
private lemma prodKernel_monomial_p_cube {d : ℕ} {k : ℝ → ℝ} {m j : ℕ}
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (p : Fin j → Fin d) (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1, (∏ l, u (p l)) * prodKernel k d u = 0 := by
  classical
  set ν : Fin d → ℕ := fun i => (Finset.univ.filter (fun l => p l = i)).card with hνdef
  have hsum : (∑ i, ν i) = j := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin j)))
      (t := (Finset.univ : Finset (Fin d))) (f := p) (fun l _ => Finset.mem_univ (p l))
    simp only [Finset.card_univ, Fintype.card_fin] at this
    rw [hνdef]; exact this.symm
  have hreg : ∀ u : Fin d → ℝ, (∏ l : Fin j, u (p l)) = ∏ i : Fin d, u i ^ ν i := by
    intro u
    rw [← Finset.prod_fiberwise_of_maps_to (fun l _ => Finset.mem_univ (p l))
          (fun l => u (p l))]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Finset.prod_congr rfl (fun l hl => by rw [(Finset.mem_filter.mp hl).2]),
        Finset.prod_const]
  simp_rw [hreg]
  exact prodKernel_multiIndex_moment_cube hk_supp hk_mom ν (by omega) (by omega)

/-- The tensor kernel is continuous when the 1-D kernel is. -/
@[fun_prop]
lemma prodKernel_continuous {d : ℕ} {k : ℝ → ℝ} (hk : Continuous k) :
    Continuous (prodKernel k d) := by
  unfold prodKernel
  exact continuous_finset_prod _ (fun i _ => hk.comp (continuous_apply i))

/-- Almost every point of the closed unit cube lies in its interior (the boundary
`{∃ i, |uᵢ| = 1}` is Lebesgue-null). -/
lemma ae_lt_one_on_cube {d : ℕ} :
    ∀ᵐ u ∂(volume.restrict (supBall (0 : Fin d → ℝ) 1)), ∀ i, |u i| < 1 := by
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_supBall 0 1)]
  have hnull : ∀ i : Fin d, ∀ c : ℝ, volume {u : Fin d → ℝ | u i = c} = 0 := by
    intro i c
    have hsub : {u : Fin d → ℝ | u i = c}
        ⊆ Set.univ.pi (fun j => if j = i then ({c} : Set ℝ) else Set.univ) := by
      intro u hu j _
      by_cases hj : j = i
      · subst hj; simpa using hu
      · simp [hj]
    refine measure_mono_null hsub ?_
    rw [MeasureTheory.volume_pi_pi]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    simp
  have hbadnull : volume {u : Fin d → ℝ | ∃ i, |u i| = 1} = 0 := by
    have hsub : {u : Fin d → ℝ | ∃ i, |u i| = 1}
        ⊆ ⋃ i : Fin d, ({u | u i = 1} ∪ {u | u i = -1}) := by
      intro u hu
      obtain ⟨i, hi⟩ := hu
      rw [Set.mem_iUnion]
      rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hi with h | h
      · exact ⟨i, Or.inl h⟩
      · exact ⟨i, Or.inr h⟩
    refine measure_mono_null hsub ?_
    refine measure_iUnion_null (fun i => ?_)
    exact measure_union_null (hnull i 1) (hnull i (-1))
  have hae_not : ∀ᵐ u ∂(volume : Measure (Fin d → ℝ)), ¬ ∃ i, |u i| = 1 := by
    rw [MeasureTheory.ae_iff]; simpa using hbadnull
  filter_upwards [hae_not] with u hu hmem i
  have h1 : |u i| ≤ 1 := by simpa using hmem i
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd ⟨i, h⟩ hu

/-- Standard-basis decomposition `h • u = ∑ᵢ (h·uᵢ) • eᵢ` in `Fin d → ℝ`. -/
private lemma smul_eq_sum_single {d : ℕ} (h : ℝ) (u : Fin d → ℝ) :
    (h • u : Fin d → ℝ) = ∑ i : Fin d, (h * u i) • (Pi.single i 1 : Fin d → ℝ) := by
  funext a
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ a (fun i => h * u i)]
  simp

/-- **The kernel kills each nonconstant diagonal Taylor term.** For `1 ≤ j ≤ m`,
integrating the diagonal iterated derivative `iteratedFDeriv ℝ j g x0 (fun _ => h•u)`
against the kernel over the cube gives `0`: expand the diagonal multilinear map into
monomials and apply the moment cancellation `prodKernel_monomial_p_cube`. -/
lemma integral_diagonal_taylor_term_cube {d : ℕ} {k : ℝ → ℝ} {m : ℕ}
    (hk_cont : Continuous k)
    (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ m → (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (g : (Fin d → ℝ) → ℝ) (x0 : Fin d → ℝ) (h : ℝ) {j : ℕ} (hj1 : 1 ≤ j) (hjm : j ≤ m) :
    ∫ u in supBall (0 : Fin d → ℝ) 1,
        prodKernel k d u * iteratedFDeriv ℝ j g x0 (fun _ => h • u) = 0 := by
  classical
  set F := iteratedFDeriv ℝ j g x0 with hFdef
  have hKcont : Continuous (prodKernel k d) := by
    unfold prodKernel
    exact continuous_finset_prod _ (fun i _ => hk_cont.comp (continuous_apply i))
  -- pointwise monomial expansion of `K(u) · F(fun _ => h•u)`.
  have hpt : ∀ u : Fin d → ℝ, prodKernel k d u * F (fun _ => h • u)
      = ∑ p : Fin j → Fin d, (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
          * ((∏ l, u (p l)) * prodKernel k d u) := by
    intro u
    have h1 : F (fun _ : Fin j => h • u)
        = ∑ p : Fin j → Fin d,
            (∏ l, (h * u (p l))) * F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) := by
      have hexp : (fun _ : Fin j => h • u)
          = (fun _ : Fin j => ∑ i : Fin d, (h * u i) • (Pi.single i 1 : Fin d → ℝ)) := by
        funext l; exact smul_eq_sum_single h u
      rw [hexp, ContinuousMultilinearMap.map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      rw [ContinuousMultilinearMap.map_smul_univ]
      simp only [smul_eq_mul]
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    ring
  calc ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * F (fun _ => h • u)
      = ∫ u in supBall (0 : Fin d → ℝ) 1, ∑ p : Fin j → Fin d,
          (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
            * ((∏ l, u (p l)) * prodKernel k d u) := by simp_rw [hpt]
    _ = ∑ p : Fin j → Fin d, ∫ u in supBall (0 : Fin d → ℝ) 1,
          (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
            * ((∏ l, u (p l)) * prodKernel k d u) := by
        refine MeasureTheory.integral_finset_sum _ (fun p _ => ?_)
        have hc : Continuous (fun u : Fin d → ℝ =>
            (F (fun l => (Pi.single (p l) 1 : Fin d → ℝ)) * h ^ j)
              * ((∏ l, u (p l)) * prodKernel k d u)) :=
          continuous_const.mul
            ((continuous_finset_prod _ (fun l _ => continuous_apply (p l))).mul hKcont)
        exact hc.continuousOn.integrableOn_compact (isCompact_supBall 0 1)
    _ = 0 := by
        refine Finset.sum_eq_zero (fun p _ => ?_)
        rw [MeasureTheory.integral_const_mul,
          prodKernel_monomial_p_cube hk_supp hk_mom p hj1 hjm, mul_zero]

/-- **Line chain rule.** The `i`-th 1-D iterated derivative of the line
`s ↦ g (x0 + s • y)` equals the `i`-th iterated Fréchet derivative of `g` at
`x0 + t • y` evaluated on the constant diagonal `fun _ => y` (needs GLOBAL
`ContDiff ℝ i g`). -/
private lemma line_iteratedDeriv {d : ℕ} (g : (Fin d → ℝ) → ℝ) (i : ℕ)
    (hf : ContDiff ℝ i g) (x0 y : Fin d → ℝ) (t : ℝ) :
    iteratedDeriv i (fun s => g (x0 + s • y)) t
      = iteratedFDeriv ℝ i g (x0 + t • y) (fun _ => y) := by
  set L : ℝ →L[ℝ] (Fin d → ℝ) := (ContinuousLinearMap.id ℝ ℝ).smulRight y with hL
  have hL1 : L 1 = y := by simp [hL]
  have hLt : L t = t • y := by simp [hL]
  set f₁ : (Fin d → ℝ) → ℝ := fun z => g (x0 + z) with hf₁def
  have hshift : ContDiff ℝ i (fun z : Fin d → ℝ => x0 + z) :=
    ContDiff.add contDiff_const contDiff_id
  have hf₁ : ContDiff ℝ i f₁ := hf.comp hshift
  have hcomp : (fun s => g (x0 + s • y)) = f₁ ∘ L := by funext s; simp [hf₁def, hL]
  rw [hcomp, iteratedDeriv_eq_iteratedFDeriv,
    ContinuousLinearMap.iteratedFDeriv_comp_right L hf₁ t (le_refl _)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [hLt]
  have hval : (fun j : Fin i => L ((fun _ => (1 : ℝ)) j)) = (fun _ : Fin i => y) := by
    funext j; simp [hL1]
  rw [hval]
  rw [show iteratedFDeriv ℝ i f₁ (t • y) = iteratedFDeriv ℝ i g (x0 + t • y) from ?_]
  · exact congrFun (iteratedFDeriv_comp_add_left' i x0) (t • y)

/-- **Global smooth extension of a `ContDiffOn` function.** If `g` is `ContDiffOn ℝ m`
on `S`, `U ⊆ S` is open, and `K ⊆ U` is compact, then there is a GLOBALLY `ContDiff ℝ m`
function `g'` that agrees with `g` on a neighborhood of every point of `K`. -/
private lemma exists_global_contDiff_of_contDiffOn {d : ℕ} (m : ℕ)
    {g : (Fin d → ℝ) → ℝ} {S U K : Set (Fin d → ℝ)}
    (hg1 : ContDiffOn ℝ m g S) (hU : IsOpen U) (hUS : U ⊆ S)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g' : (Fin d → ℝ) → ℝ, ContDiff ℝ m g' ∧ ∀ p ∈ K, g' =ᶠ[nhds p] g := by
  obtain ⟨V, hVo, hKV, hVU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  have hKint : K ⊆ interior (closure V) := hKV.trans (interior_maximal subset_closure hVo)
  obtain ⟨χ, hχ1, hχ0, hχ01⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (𝓘(ℝ, Fin d → ℝ)) (n := (m : ℕ∞))
      hK.isClosed hKint
  have hχcd : ContDiff ℝ (m : WithTop ℕ∞) (fun x => χ x) := by
    have := χ.contMDiff.contDiff (n := (m : ℕ∞)); simpa using this
  refine ⟨fun x => χ x * g x, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ closure V
    · have hxU : x ∈ U := hVU hx
      have h1 : ContDiffAt ℝ (m : WithTop ℕ∞) (fun x => χ x) x := hχcd.contDiffAt
      have h2 : ContDiffAt ℝ (m : WithTop ℕ∞) g x :=
        (hg1.mono hUS).contDiffAt (hU.mem_nhds hxU)
      exact h1.mul h2
    · have hnhds : (closure V)ᶜ ∈ nhds x := (isClosed_closure.isOpen_compl).mem_nhds hx
      have heq : (fun x => χ x * g x) =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
        filter_upwards [hnhds] with z hz; simp [hχ0 z hz]
      exact ContDiffAt.congr_of_eventuallyEq contDiffAt_const heq
  · intro p hp
    have hp1 : ∀ᶠ x in nhds p, χ x = 1 := hχ1.filter_mono (nhds_le_nhdsSet hp)
    filter_upwards [hp1] with x hx
    simp [hx]

/-- Cast a `ℕ`-inequality into the `WithTop ℕ∞` smoothness index used by `ContDiff`. -/
private lemma natCast_le_withTop {a b : ℕ} (h : a ≤ b) :
    (a : WithTop ℕ∞) ≤ (b : WithTop ℕ∞) := Nat.mono_cast h

/-- Cast a strict `ℕ`-inequality into the `WithTop ℕ∞` smoothness index used by `ContDiff`. -/
private lemma natCast_lt_withTop {a b : ℕ} (h : a < b) :
    (a : WithTop ℕ∞) < (b : WithTop ℕ∞) := by
  rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, WithTop.coe_lt_coe]
  exact ENat.coe_lt_coe.mpr h

/-- Applying an order-`k` continuous multilinear map to the constant diagonal `fun _ => y`
is bounded by its operator norm times `‖y‖^k`. -/
private lemma cmm_diag_apply_abs_le {d k : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => (Fin d → ℝ)) ℝ) (y : Fin d → ℝ) :
    |A (fun _ => y)| ≤ ‖A‖ * ‖y‖ ^ k := by
  have h := A.le_opNorm (fun _ : Fin k => y)
  rw [Real.norm_eq_abs] at h
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

/-- Core Hölder bound on the diagonal: the difference of the order-`k` (`k = ⌈γ⌉₊-1`) iterated
Fréchet derivatives at two points `P, Q ∈ S`, evaluated on the constant diagonal `fun _ => y`,
is at most `M * ‖P - Q‖^(γ - k) * ‖y‖^k`. -/
private lemma holder_diag_diff_le {d : ℕ} {γ M : ℝ} {g : (Fin d → ℝ) → ℝ}
    {S : Set (Fin d → ℝ)} (hg : HolderBallStd g γ M S)
    (P Q : Fin d → ℝ) (hP : P ∈ S) (hQ : Q ∈ S) (y : Fin d → ℝ) :
    |iteratedFDeriv ℝ (⌈γ⌉₊ - 1) g P (fun _ => y)
        - iteratedFDeriv ℝ (⌈γ⌉₊ - 1) g Q (fun _ => y)|
      ≤ M * ‖P - Q‖ ^ (γ - ((⌈γ⌉₊ - 1 : ℕ) : ℝ)) * ‖y‖ ^ (⌈γ⌉₊ - 1) := by
  set k := ⌈γ⌉₊ - 1 with hk
  have hstep :
      |iteratedFDeriv ℝ k g P (fun _ => y) - iteratedFDeriv ℝ k g Q (fun _ => y)|
        ≤ ‖iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q‖ * ‖y‖ ^ k := by
    have h := cmm_diag_apply_abs_le (iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q) y
    rwa [ContinuousMultilinearMap.sub_apply] at h
  have hhol := hg.2.2 P hP Q hQ
  calc
    |iteratedFDeriv ℝ k g P (fun _ => y) - iteratedFDeriv ℝ k g Q (fun _ => y)|
        ≤ ‖iteratedFDeriv ℝ k g P - iteratedFDeriv ℝ k g Q‖ * ‖y‖ ^ k := hstep
    _ ≤ (M * ‖P - Q‖ ^ (γ - ((k : ℕ) : ℝ))) * ‖y‖ ^ k := by gcongr
    _ = M * ‖P - Q‖ ^ (γ - ((k : ℕ) : ℝ)) * ‖y‖ ^ k := by ring

/-- For [a dimension, smoothness order, radius, function, ambient domain, and open local
domain](hyp:d,γ,M,g,S,U), if [the smoothness order is positive](hyp:hγ), [the function lies in
the standard Hölder ball](hyp:hg), [the local domain is open](hyp:hU), and [is contained in the
ambient domain](hyp:hUS), then for [a base point and displacement](hyp:x0,y), if [their full
line segment lies in the local domain](hyp:hseg), [the function at the displaced point differs
from its diagonal Taylor polynomial by at most the Hölder remainder bound](goal).

**Per-point Taylor + Hölder crux.** For `g` in the standard Hölder ball of order `γ`
and radius `M` on `S`, `U ⊆ S` open containing the segment `{x0 + t • y : t ∈ [0,1]}`, the
value `g (x0 + y)` differs from its order-`m` diagonal Taylor polynomial (`m = ⌈γ⌉₊ - 1`) by
at most `(M / m!) ‖y‖^γ`. -/
lemma holder_line_taylor {d : ℕ} {γ M : ℝ} {g : (Fin d → ℝ) → ℝ}
    {S U : Set (Fin d → ℝ)}
    (hγ : 0 < γ) (hg : HolderBallStd g γ M S) (hU : IsOpen U) (hUS : U ⊆ S)
    (x0 y : Fin d → ℝ) (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • y ∈ U) :
    |g (x0 + y) - ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
        (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => y)|
      ≤ (M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖y‖ ^ γ := by
  have h0mem : x0 ∈ U := by
    have := hseg 0 (Set.left_mem_Icc.mpr zero_le_one); simpa using this
  have h1mem : x0 + y ∈ U := by
    have := hseg 1 (Set.right_mem_Icc.mpr zero_le_one); simpa using this
  have hx0S : x0 ∈ S := hUS h0mem
  have hx0yS : x0 + y ∈ S := hUS h1mem
  rcases Nat.eq_zero_or_pos (⌈γ⌉₊ - 1) with hm0 | hmpos
  · -- Case m = 0 (0 < γ ≤ 1): the sum is just `g x0`, no Taylor needed.
    have hb := holder_diag_diff_le hg (x0 + y) x0 hx0yS hx0S y
    rw [hm0] at hb ⊢
    simp only [zero_add, Finset.sum_range_one, Nat.factorial_zero, Nat.cast_one, one_div,
      inv_one, one_mul, iteratedFDeriv_zero_apply, div_one, Nat.cast_zero, sub_zero,
      pow_zero, mul_one] at hb ⊢
    rwa [add_sub_cancel_left] at hb
  · -- Case m ≥ 1 (γ > 1): Taylor with Lagrange remainder on the line.
    obtain ⟨n, hn⟩ : ∃ n, ⌈γ⌉₊ - 1 = n + 1 := ⟨⌈γ⌉₊ - 2, by omega⟩
    have hM : 0 ≤ M := le_trans (norm_nonneg _) (hg.2.1 0 (Nat.zero_le _) x0 hx0S)
    have hfac : (0 : ℝ) < (Nat.factorial (n + 1) : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 1)
    set K : Set (Fin d → ℝ) := (fun t : ℝ => x0 + t • y) '' Set.Icc 0 1 with hKdef
    have hcontLine : Continuous (fun t : ℝ => x0 + t • y) := by fun_prop
    have hK : IsCompact K := isCompact_Icc.image hcontLine
    have hKU : K ⊆ U := by rintro _ ⟨t, ht, rfl⟩; exact hseg t ht
    have hx0K : x0 ∈ K := ⟨0, Set.left_mem_Icc.mpr zero_le_one, by simp⟩
    have hx0yK : x0 + y ∈ K := ⟨1, Set.right_mem_Icc.mpr zero_le_one, by simp⟩
    have hxξK : ∀ ξ : ℝ, ξ ∈ Set.Ioo (0 : ℝ) 1 → x0 + ξ • y ∈ K :=
      fun ξ hξ => ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, rfl⟩
    obtain ⟨gt, hgt_cd, hgt_eq⟩ :=
      exists_global_contDiff_of_contDiffOn (⌈γ⌉₊ - 1) hg.1 hU hUS hK hKU
    have htrans : ∀ (i : ℕ) (p : Fin d → ℝ), p ∈ K →
        iteratedFDeriv ℝ i gt p = iteratedFDeriv ℝ i g p :=
      fun i p hp => ((hgt_eq p hp).iteratedFDeriv ℝ i).eq_of_nhds
    have hlineCD : ContDiff ℝ ((⌈γ⌉₊ - 1 : ℕ) : WithTop ℕ∞) (fun s : ℝ => x0 + s • y) := by
      fun_prop
    set φ : ℝ → ℝ := fun s => gt (x0 + s • y) with hφdef
    have hφCD : ContDiff ℝ ((⌈γ⌉₊ - 1 : ℕ) : WithTop ℕ∞) φ := by
      simpa [hφdef, Function.comp_def] using hgt_cd.comp hlineCD
    have hcoef : ∀ k : ℕ, k ≤ ⌈γ⌉₊ - 1 →
        iteratedDerivWithin k φ (Set.Icc (0 : ℝ) 1) 0
          = iteratedFDeriv ℝ k g x0 (fun _ => y) := by
      intro k hk
      have hCDk : ContDiff ℝ (k : WithTop ℕ∞) gt := hgt_cd.of_le (natCast_le_withTop hk)
      have hCDkφ : ContDiffAt ℝ (k : WithTop ℕ∞) φ 0 :=
        (hφCD.of_le (natCast_le_withTop hk)).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hCDkφ
        (Set.left_mem_Icc.mpr zero_le_one), hφdef, line_iteratedDeriv gt k hCDk x0 y 0]
      simp only [zero_smul, add_zero]
      rw [htrans k x0 hx0K]
    have hCDgt : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) gt := hn ▸ hgt_cd
    have hφn : ContDiffOn ℝ (n : WithTop ℕ∞) φ (Set.Icc (0 : ℝ) 1) :=
      ((hn ▸ hφCD).of_le (natCast_le_withTop (Nat.le_succ n))).contDiffOn
    have hφn1 : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ (Set.Icc (0 : ℝ) 1) :=
      (hn ▸ hφCD).contDiffOn
    have hf' : DifferentiableOn ℝ (iteratedDerivWithin n φ (Set.Icc (0 : ℝ) 1))
        (Set.Ioo 0 1) :=
      (hφn1.differentiableOn_iteratedDerivWithin (natCast_lt_withTop (Nat.lt_succ_self n))
        uniqueDiffOn_Icc_zero_one).mono Set.Ioo_subset_Icc_self
    have huIcc01 : Set.uIcc (0 : ℝ) 1 = Set.Icc (0 : ℝ) 1 := Set.uIcc_of_le zero_le_one
    have huIoo01 : Set.uIoo (0 : ℝ) 1 = Set.Ioo (0 : ℝ) 1 := Set.uIoo_of_le zero_le_one
    obtain ⟨ξ, hξ, htay⟩ :=
      taylor_mean_remainder_lagrange (f := φ) (x₀ := (0 : ℝ)) (x := (1 : ℝ))
        (zero_ne_one) (by rw [huIcc01]; exact hφn)
        (by rw [huIcc01, huIoo01]; exact hf')
    rw [huIcc01] at htay
    rw [huIoo01] at hξ
    have hφ1 : φ 1 = g (x0 + y) := by
      have := (hgt_eq (x0 + y) hx0yK).eq_of_nhds; simpa [hφdef, one_smul] using this
    have hsum : taylorWithinEval φ n (Set.Icc (0 : ℝ) 1) 0 1
        = ∑ k ∈ Finset.range (n + 1),
            1 / (Nat.factorial k : ℝ) * iteratedFDeriv ℝ k g x0 (fun _ => y) := by
      rw [taylor_within_apply]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Finset.mem_range] at hk
      rw [hcoef k (by rw [hn]; omega)]
      simp only [sub_zero, one_pow, mul_one, smul_eq_mul, one_div]
    have hR : iteratedDerivWithin (n + 1) φ (Set.Icc (0 : ℝ) 1) ξ
        = iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y) := by
      have hCDξ : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) φ ξ := (hn ▸ hφCD).contDiffAt
      rw [iteratedDerivWithin_eq_iteratedDeriv uniqueDiffOn_Icc_zero_one hCDξ
        (Set.Ioo_subset_Icc_self hξ), hφdef, line_iteratedDeriv gt (n + 1) hCDgt x0 y ξ,
        htrans (n + 1) (x0 + ξ • y) (hxξK ξ hξ)]
    have eq1 : g (x0 + y)
          - ∑ k ∈ Finset.range (n + 1),
              1 / (Nat.factorial k : ℝ) * iteratedFDeriv ℝ k g x0 (fun _ => y)
        = iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
            / (Nat.factorial (n + 1) : ℝ) := by
      rw [hφ1, hsum, hR] at htay; simpa using htay
    have hxξS : x0 + ξ • y ∈ S := hUS (hKU (hxξK ξ hξ))
    have hbound := holder_diag_diff_le hg (x0 + ξ • y) x0 hxξS hx0S y
    rw [hn] at hbound
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hξ.1] at hbound
    have hlt : ((n + 1 : ℕ) : ℝ) < γ := by
      have := Nat.lt_ceil.mp (show ⌈γ⌉₊ - 1 < ⌈γ⌉₊ by omega); rw [hn] at this; exact this
    have he_nonneg : 0 ≤ γ - ((n + 1 : ℕ) : ℝ) := by linarith
    have hem : (γ - ((n + 1 : ℕ) : ℝ)) + ((n + 1 : ℕ) : ℝ) = γ := by ring
    have hcombine : ‖y‖ ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) = ‖y‖ ^ γ := by
      rw [← Real.rpow_natCast (‖y‖) (n + 1),
        ← Real.rpow_add' (norm_nonneg y) (by rw [hem]; exact ne_of_gt hγ), hem]
    have key : (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) ≤ ‖y‖ ^ γ := by
      rw [Real.mul_rpow hξ.1.le (norm_nonneg y), mul_assoc, hcombine]
      calc ξ ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ γ
            ≤ 1 * ‖y‖ ^ γ :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_one hξ.1.le hξ.2.le he_nonneg) (Real.rpow_nonneg (norm_nonneg y) γ)
        _ = ‖y‖ ^ γ := one_mul _
    have hmid : M * (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1) ≤ M * ‖y‖ ^ γ := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left key hM
    have hgoal_eq : g (x0 + y)
          - ∑ j ∈ Finset.range (n + 1 + 1),
              1 / (Nat.factorial j : ℝ) * iteratedFDeriv ℝ j g x0 (fun _ => y)
        = 1 / (Nat.factorial (n + 1) : ℝ)
            * (iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
                - iteratedFDeriv ℝ (n + 1) g x0 (fun _ => y)) := by
      rw [Finset.sum_range_succ]; linear_combination eq1
    rw [hn, hgoal_eq, abs_mul, abs_of_pos (div_pos one_pos hfac)]
    calc 1 / (Nat.factorial (n + 1) : ℝ)
            * |iteratedFDeriv ℝ (n + 1) g (x0 + ξ • y) (fun _ => y)
                - iteratedFDeriv ℝ (n + 1) g x0 (fun _ => y)|
          ≤ 1 / (Nat.factorial (n + 1) : ℝ)
              * (M * (ξ * ‖y‖) ^ (γ - ((n + 1 : ℕ) : ℝ)) * ‖y‖ ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left hbound (div_pos one_pos hfac).le
      _ ≤ 1 / (Nat.factorial (n + 1) : ℝ) * (M * ‖y‖ ^ γ) :=
          mul_le_mul_of_nonneg_left hmid (div_pos one_pos hfac).le
      _ = M / (Nat.factorial (n + 1) : ℝ) * ‖y‖ ^ γ := by ring

end Causalean.Stat.Nonparametric
