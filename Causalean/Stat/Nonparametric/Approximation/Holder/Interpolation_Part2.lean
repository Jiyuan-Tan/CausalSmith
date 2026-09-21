/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Stat.Nonparametric.Approximation.Holder.Interpolation_Part1

/-!
# Hölder pointwise-to-local-`L¹` interpolation capstone

This file combines the moment-cancelling kernel from `Kernel.lean` with the Taylor, kernel-moment,
change-of-variables, and bandwidth-optimization lemmas from `Interpolation_Part1.lean`. Its public
result `holder_point_l1_interpolation` turns a pointwise value of a multivariate Hölder function
into a lower bound for its local absolute integral over `supBall x0 r`.
-/

public section

namespace Causalean.Stat.Nonparametric

open MeasureTheory
open scoped BigOperators Pointwise Manifold ContDiff
/-- The product-kernel smoother differs from a Hölder function at its center by at most a constant
times `M h^γ`, because all lower-order Taylor terms cancel against the kernel moments. -/
private lemma holder_taylor_bias {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ} {S : Set (Fin d → ℝ)}
    {k : ℝ → ℝ} {B : ℝ}
    (hγ : 0 < γ) (hM : 0 < M) (hS : supBall x0 r ⊆ S)
    (hk_cont : Continuous k) (hk_supp : ∀ u : ℝ, 1 < |u| → k u = 0)
    (hk_mass : (∫ u in Set.Icc (-1 : ℝ) 1, k u) = 1)
    (hk_mom : ∀ j : ℕ, 1 ≤ j → j ≤ ⌈γ⌉₊ - 1 →
      (∫ u in Set.Icc (-1 : ℝ) 1, u ^ j * k u) = 0)
    (hB : ∀ u : ℝ, |k u| ≤ B) (hB0 : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (Fin d → ℝ) → ℝ, HolderBallStd g γ M S →
      ∀ h : ℝ, 0 < h → h ≤ r →
        |g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)|
          ≤ C * M * h ^ γ := by
  classical
  have hfacne : (Nat.factorial (⌈γ⌉₊ - 1) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  refine ⟨B ^ d * (volume (supBall (0 : Fin d → ℝ) 1)).toReal / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ),
    ?_, ?_⟩
  · exact div_nonneg (mul_nonneg (pow_nonneg hB0 d) ENNReal.toReal_nonneg) (Nat.cast_nonneg _)
  · intro g hg h hh hhr
    have hKcont : Continuous (prodKernel k d) := prodKernel_continuous hk_cont
    have hg_contS : ContinuousOn g S := hg.1.continuousOn
    -- open cube of radius `r` around `x0`, contained in `S`.
    set U : Set (Fin d → ℝ) := {x | ∀ i, |x i - x0 i| < r} with hU_def
    have hUopen : IsOpen U := by
      rw [hU_def, Set.setOf_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_lt (by fun_prop) continuous_const)
    have hUS : U ⊆ S := by
      intro x hx
      simp only [hU_def, Set.mem_setOf_eq] at hx
      exact hS (fun i => le_of_lt (hx i))
    -- Taylor polynomial in `u`.
    set P : (Fin d → ℝ) → ℝ := fun u => ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
        (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u) with hP_def
    have hDcont : ∀ j : ℕ,
        Continuous (fun u : Fin d → ℝ => iteratedFDeriv ℝ j g x0 (fun _ => h • u)) := by
      intro j
      exact (iteratedFDeriv ℝ j g x0).cont.comp
        (continuous_pi (fun _ => continuous_id.const_smul h))
    have hPcont : Continuous P := by
      rw [hP_def]
      exact continuous_finset_sum _ (fun j _ => continuous_const.mul (hDcont j))
    have hmaps : Set.MapsTo (fun u => x0 + h • u) (supBall (0 : Fin d → ℝ) 1) S := by
      intro u hu
      refine hS (fun i => ?_)
      have he : (x0 + h • u) i - x0 i = h * u i := by simp [Pi.add_apply, Pi.smul_apply]
      rw [he, abs_mul, abs_of_pos hh]
      have hui : |u i| ≤ 1 := by simpa using hu i
      calc h * |u i| ≤ h * 1 := mul_le_mul_of_nonneg_left hui hh.le
        _ = h := mul_one h
        _ ≤ r := hhr
    have hgcomp : ContinuousOn (fun u => g (x0 + h • u)) (supBall (0 : Fin d → ℝ) 1) :=
      hg_contS.comp (by fun_prop) hmaps
    have hI_g : IntegrableOn (fun u => prodKernel k d u * g (x0 + h • u))
        (supBall (0 : Fin d → ℝ) 1) :=
      (hKcont.continuousOn.mul hgcomp).integrableOn_compact (isCompact_supBall 0 1)
    have hI_P : IntegrableOn (fun u => prodKernel k d u * P u) (supBall (0 : Fin d → ℝ) 1) :=
      (hKcont.mul hPcont).continuousOn.integrableOn_compact (isCompact_supBall 0 1)
    -- Mass identity: `∫ K·P = g x0`.
    have hmass_P : ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * P u = g x0 := by
      have hzero : ∀ b ∈ Finset.range (⌈γ⌉₊ - 1 + 1), b ≠ 0 →
          (∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u *
            ((1 / (Nat.factorial b : ℝ)) * iteratedFDeriv ℝ b g x0 (fun _ => h • u))) = 0 := by
        intro b hb hb0
        have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb0
        have hbm : b ≤ ⌈γ⌉₊ - 1 := by have := Finset.mem_range.mp hb; omega
        have hre : ∀ u : Fin d → ℝ, prodKernel k d u *
              ((1 / (Nat.factorial b : ℝ)) * iteratedFDeriv ℝ b g x0 (fun _ => h • u))
            = (1 / (Nat.factorial b : ℝ)) *
              (prodKernel k d u * iteratedFDeriv ℝ b g x0 (fun _ => h • u)) := fun u => by ring
        simp_rw [hre]
        rw [MeasureTheory.integral_const_mul,
          integral_diagonal_taylor_term_cube hk_cont hk_supp hk_mom g x0 h hb1 hbm, mul_zero]
      have hsum : ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * P u
          = ∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1), ∫ u in supBall (0 : Fin d → ℝ) 1,
              prodKernel k d u *
                ((1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u)) := by
        simp only [hP_def, Finset.mul_sum]
        refine MeasureTheory.integral_finset_sum _ (fun j _ => ?_)
        exact ((hKcont.mul (continuous_const.mul (hDcont j))).continuousOn).integrableOn_compact
          (isCompact_supBall 0 1)
      rw [hsum, Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (Nat.succ_pos _)) hzero]
      simp only [Nat.factorial_zero, Nat.cast_one, one_div, inv_one, one_mul,
        iteratedFDeriv_zero_apply]
      rw [MeasureTheory.integral_mul_const, prodKernel_mass_cube hk_supp hk_mass, one_mul]
    -- Rewrite the bias as `∫ K·(P - g(x0+h•u))`.
    have hbias_eq : g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u)
        = ∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)) := by
      rw [MeasureTheory.integral_sub hI_P hI_g, hmass_P]
    -- Per-point bound (a.e. on the cube via the open interior).
    have hpp : ∀ᵐ u ∂(volume.restrict (supBall (0 : Fin d → ℝ) 1)),
        |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)|
          ≤ B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ) := by
      filter_upwards [ae_lt_one_on_cube] with u hu
      have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, x0 + t • (h • u) ∈ U := by
        intro t ht
        simp only [hU_def, Set.mem_setOf_eq]
        intro i
        have he : (x0 + t • (h • u)) i - x0 i = t * (h * u i) := by
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [he, abs_mul, abs_mul, abs_of_nonneg ht.1, abs_of_pos hh]
        have hb : h * |u i| < h := by simpa using mul_lt_mul_of_pos_left (hu i) hh
        calc t * (h * |u i|) ≤ 1 * (h * |u i|) :=
              mul_le_mul_of_nonneg_right ht.2 (mul_nonneg hh.le (abs_nonneg _))
          _ = h * |u i| := one_mul _
          _ < h := hb
          _ ≤ r := hhr
      have hcrux := holder_line_taylor hγ hg hUopen hUS x0 (h • u) hseg
      have hPeq : (∑ j ∈ Finset.range (⌈γ⌉₊ - 1 + 1),
          (1 / (Nat.factorial j : ℝ)) * iteratedFDeriv ℝ j g x0 (fun _ => h • u)) = P u := by
        rw [hP_def]
      rw [hPeq] at hcrux
      have hfactor : |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)|
          = |prodKernel k d u| * |P u - g (x0 + h • u)| := by rw [← mul_sub, abs_mul]
      rw [hfactor]
      refine mul_le_mul (prodKernel_abs_le hB u) ?_ (abs_nonneg _) (pow_nonneg hB0 d)
      rw [abs_sub_comm]; exact hcrux
    -- Integrability of the pointwise bound.
    have hbound_cont : Continuous (fun u : Fin d → ℝ =>
        B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ)) :=
      continuous_const.mul (continuous_const.mul
        (((continuous_id.const_smul h).norm).rpow_const (fun _ => Or.inr hγ.le)))
    -- `∫ ‖h•u‖^γ ≤ vol(cube)·h^γ`.
    have hnorm_int : ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ
        ≤ (volume (supBall (0 : Fin d → ℝ) 1)).toReal * h ^ γ := by
      have hle : ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ
          ≤ ∫ _u in supBall (0 : Fin d → ℝ) 1, h ^ γ := by
        refine MeasureTheory.integral_mono_of_nonneg
          (ae_of_all _ (fun u => Real.rpow_nonneg (norm_nonneg _) _))
          (continuous_const.continuousOn.integrableOn_compact (isCompact_supBall 0 1)) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_supBall 0 1)] with u hu
        have hunorm : ‖u‖ ≤ 1 := by
          rw [pi_norm_le_iff_of_nonneg (by norm_num)]
          intro i; simpa using hu i
        have hhu : ‖h • u‖ ≤ h := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
          calc h * ‖u‖ ≤ h * 1 := mul_le_mul_of_nonneg_left hunorm hh.le
            _ = h := mul_one h
        exact Real.rpow_le_rpow (norm_nonneg _) hhu hγ.le
      rwa [MeasureTheory.setIntegral_const, smul_eq_mul] at hle
    -- Assemble.
    rw [hbias_eq]
    calc |∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u))|
        = ‖∫ u in supBall (0 : Fin d → ℝ) 1,
            (prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u))‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1,
            ‖prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ u in supBall (0 : Fin d → ℝ) 1,
            |prodKernel k d u * P u - prodKernel k d u * g (x0 + h • u)| := by
          simp_rw [Real.norm_eq_abs]
      _ ≤ ∫ u in supBall (0 : Fin d → ℝ) 1,
            B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) * ‖h • u‖ ^ γ) :=
          MeasureTheory.integral_mono_of_nonneg (ae_of_all _ (fun u => abs_nonneg _))
            (hbound_cont.continuousOn.integrableOn_compact (isCompact_supBall 0 1)) hpp
      _ = B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) *
            ∫ u in supBall (0 : Fin d → ℝ) 1, ‖h • u‖ ^ γ) := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ B ^ d * ((M / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)) *
            ((volume (supBall (0 : Fin d → ℝ) 1)).toReal * h ^ γ)) := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hB0 d)
          exact mul_le_mul_of_nonneg_left hnorm_int
            (div_nonneg hM.le (Nat.cast_nonneg _))
      _ = B ^ d * (volume (supBall (0 : Fin d → ℝ) 1)).toReal / (Nat.factorial (⌈γ⌉₊ - 1) : ℝ)
            * M * h ^ γ := by
          field_simp

/-- **Hölder pointwise ⟹ local `L¹` mass interpolation.** Fix a point `x0` in
`d`-dimensional Euclidean space. If [the Hölder exponent `γ` is positive](hyp:hγ), [the
Hölder constant `M` is positive](hyp:hM), [the neighbourhood radius `r` is
positive](hyp:hr), and [the sup-norm ball of radius `r` around `x0` is contained in the
domain `S`](hyp:hS), then [there is a constant `c_H > 0`, depending only on `γ`, `d`, `M`,
`r` and uniform over the Hölder ball, such that every function `g` in the standard Hölder
ball of exponent `γ`, constant `M`, and domain `S` satisfies
`c_H · |g(x0)|^{1 + d/γ} ≤ ∫_{supBall x0 r} |g|`](goal).

This estimate is useful in two-point and Assouad lower-bound arguments and is not tied to any
particular estimand. -/
theorem holder_point_l1_interpolation {d : ℕ} {γ M r : ℝ} {x0 : Fin d → ℝ}
    {S : Set (Fin d → ℝ)}
    (hγ : 0 < γ) (hM : 0 < M) (hr : 0 < r) (hS : supBall x0 r ⊆ S) :
    ∃ cH : ℝ, 0 < cH ∧ ∀ g : (Fin d → ℝ) → ℝ,
      HolderBallStd g γ M S →
      cH * |g x0| ^ (1 + (d : ℝ) / γ) ≤ ∫ x in supBall x0 r, |g x| := by
  classical
  -- Construct the moment-cancelling 1-D kernel and tensorize it as `K = prodKernel k d`.
  obtain ⟨k, hk_cont, hk_supp, hk_mass, hk_mom⟩ :=
    exists_moment_cancelling_kernel_1d (⌈γ⌉₊ - 1)
  -- `k` is bounded (continuous with support in `[-1,1]`).
  have hcs : HasCompactSupport k := by
    apply HasCompactSupport.intro (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
    intro x hx
    apply hk_supp
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [not_le] at hx; rw [lt_abs]; right; linarith
    · rw [not_le] at hx; rw [lt_abs]; left; linarith
  obtain ⟨C0, hC0⟩ := hk_cont.bounded_above_of_compact_support hcs
  set B := max C0 0 with hBdef
  have hB : ∀ u, |k u| ≤ B :=
    fun u => le_trans (by simpa [Real.norm_eq_abs] using hC0 u) (le_max_left _ _)
  have hB0 : 0 ≤ B := le_max_right _ _
  -- `B > 0`: else `k ≡ 0`, contradicting unit mass.
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hk0 : ∀ u, k u = 0 := by
        intro u
        have hle : |k u| ≤ 0 := by rw [h]; exact hB u
        exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun u _ => hk0 u)] at hk_mass
      simp at hk_mass
  have hBd : 0 < B ^ d := pow_pos hBpos d
  -- Obtain the uniform bias constant `C`.
  obtain ⟨C, hC0nn, hCbias⟩ :=
    holder_taylor_bias hγ hM hS hk_cont hk_supp hk_mass hk_mom hB hB0
  -- Choose the bandwidth constant `cstar`.
  have hMrpow_pos : 0 < M ^ ((1 : ℝ) / γ) := Real.rpow_pos_of_pos hM _
  have hC1 : (0 : ℝ) < C + 1 := by positivity
  have hden_pos : (0 : ℝ) < 4 * (C + 1) * M := by positivity
  have hb_pos : 0 < (1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ) :=
    Real.rpow_pos_of_pos (by positivity) _
  set cstar := min (r / M ^ ((1 : ℝ) / γ)) ((1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ))
    with hcstar_def
  have hcstar_pos : 0 < cstar := lt_min (div_pos hr hMrpow_pos) hb_pos
  refine ⟨(3 / (4 * B ^ d)) * cstar ^ d, ?_, ?_⟩
  · exact mul_pos (div_pos (by norm_num) (mul_pos (by norm_num) hBd)) (pow_pos hcstar_pos d)
  · intro g hg
    set Δ := |g x0| with hΔdef
    have hΔnn : 0 ≤ Δ := by rw [hΔdef]; exact abs_nonneg _
    rcases hΔnn.lt_or_eq with hΔpos | hΔ0
    swap
    · -- `Δ = 0`: RHS ≥ 0.
      rw [← hΔ0, Real.zero_rpow (by positivity : (1 : ℝ) + (d : ℝ) / γ ≠ 0), mul_zero]
      exact MeasureTheory.setIntegral_nonneg (measurableSet_supBall x0 r)
        (fun x _ => abs_nonneg _)
    · -- `Δ > 0`.
      have hx0S : x0 ∈ S := hS (mem_supBall_self x0 hr.le)
      have hΔM : Δ ≤ M := by
        have h0 := hg.2.1 0 (Nat.zero_le _) x0 hx0S
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h0
        rw [hΔdef]; exact h0
      set h := cstar * Δ ^ ((1 : ℝ) / γ) with hh_def
      have hh_pos : 0 < h := mul_pos hcstar_pos (Real.rpow_pos_of_pos hΔpos _)
      -- `h ≤ r`.
      have hh_le_r : h ≤ r := by
        rw [hh_def]
        have hΔle : Δ ^ ((1 : ℝ) / γ) ≤ M ^ ((1 : ℝ) / γ) :=
          Real.rpow_le_rpow hΔnn hΔM (one_div_nonneg.mpr hγ.le)
        have hne := hMrpow_pos.ne'
        calc cstar * Δ ^ ((1 : ℝ) / γ)
            ≤ cstar * M ^ ((1 : ℝ) / γ) := mul_le_mul_of_nonneg_left hΔle hcstar_pos.le
          _ ≤ (r / M ^ ((1 : ℝ) / γ)) * M ^ ((1 : ℝ) / γ) :=
              mul_le_mul_of_nonneg_right (min_le_left _ _) hMrpow_pos.le
          _ = r := by field_simp
      -- Remainder `C·M·hᵞ ≤ Δ/4`.
      have hpow : (Δ ^ ((1 : ℝ) / γ)) ^ γ = Δ := by
        rw [← Real.rpow_mul hΔnn, one_div_mul_cancel hγ.ne', Real.rpow_one]
      have hhg : h ^ γ = cstar ^ γ * Δ := by
        rw [hh_def, Real.mul_rpow hcstar_pos.le (Real.rpow_nonneg hΔnn _), hpow]
      have hcstar_g : cstar ^ γ ≤ 1 / (4 * (C + 1) * M) := by
        have h2 : cstar ^ γ ≤ ((1 / (4 * (C + 1) * M)) ^ ((1 : ℝ) / γ)) ^ γ :=
          Real.rpow_le_rpow hcstar_pos.le (min_le_right _ _) hγ.le
        rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ.ne', Real.rpow_one] at h2
      have hrem : C * M * h ^ γ ≤ Δ / 4 := by
        have hge : C * M * cstar ^ γ ≤ C * M * (1 / (4 * (C + 1) * M)) :=
          mul_le_mul_of_nonneg_left hcstar_g (by positivity)
        have heq : C * M * (1 / (4 * (C + 1) * M)) = C / (4 * (C + 1)) := by
          field_simp
        rw [heq] at hge
        have hle14 : C / (4 * (C + 1)) ≤ 1 / 4 := by
          rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * (C + 1))]; nlinarith [hC0nn]
        have hCMc : C * M * cstar ^ γ ≤ 1 / 4 := le_trans hge hle14
        rw [hhg]
        calc C * M * (cstar ^ γ * Δ) = (C * M * cstar ^ γ) * Δ := by ring
          _ ≤ (1 / 4) * Δ := mul_le_mul_of_nonneg_right hCMc hΔnn
          _ = Δ / 4 := by ring
      -- Bias and change-of-variables combine into the `l1` hypothesis.
      have hbias := hCbias g hg h hh_pos hh_le_r
      have hbias' : |g x0 - ∫ u in supBall (0 : Fin d → ℝ) 1,
          prodKernel k d u * g (x0 + h • u)| ≤ Δ / 4 := le_trans hbias hrem
      have hVlow : 3 * Δ / 4 ≤ |∫ u in supBall (0 : Fin d → ℝ) 1,
          prodKernel k d u * g (x0 + h • u)| := by
        have h1 := abs_sub_abs_le_abs_sub (g x0)
          (∫ u in supBall (0 : Fin d → ℝ) 1, prodKernel k d u * g (x0 + h • u))
        rw [← hΔdef] at h1
        linarith [le_trans h1 hbias']
      have hsm := smoothed_abs_le hS (prodKernel_abs_le hB) g hg h hh_pos hh_le_r
      have hbound : 3 * Δ / 4 ≤ B ^ d * h⁻¹ ^ d * ∫ x in supBall x0 r, |g x| :=
        le_trans hVlow hsm
      have hfin := l1_lower_of_bias_bound hBd hΔpos hcstar_pos hh_def hbound
      rw [hΔdef]
      exact hfin

end Causalean.Stat.Nonparametric
