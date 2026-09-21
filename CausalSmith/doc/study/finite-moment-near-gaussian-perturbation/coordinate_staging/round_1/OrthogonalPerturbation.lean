/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/
import Causalean.Stat.Nonparametric.MomentProblems.FiniteMomentNearGaussianPerturbation.Basic

/-!
# Bounded perturbations orthogonal to finitely many Gaussian monomials

This module isolates the finite-dimensional nullspace construction.  It produces a
nonzero bounded measurable function orthogonal, under the standard Gaussian law, to
every monomial through any prescribed finite degree.
-/

namespace Causalean.Stat.MomentProblems

open MeasureTheory ProbabilityTheory
open scoped BigOperators

private def gaussianBlock {n : ℕ} (i : Fin n) : Set ℝ :=
  Set.Ioc (i.val : ℝ) ((i.val : ℝ) + 1)

private lemma gaussianBlock_measurable {n : ℕ} (i : Fin n) :
    MeasurableSet (gaussianBlock i) :=
  measurableSet_Ioc

private lemma gaussianBlock_disjoint {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    Disjoint (gaussianBlock i) (gaussianBlock j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases Nat.lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with hij' | hji'
  · have hs : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hij')
    exact (not_lt_of_ge (hxi.2.trans hs)) hxj.1
  · have hs : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hji')
    exact (not_lt_of_ge (hxj.2.trans hs)) hxi.1

private lemma integrable_gaussianBlock_pow {n k : ℕ} (i : Fin n) :
    Integrable ((gaussianBlock i).indicator fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  have hI : IntegrableOn (fun x : ℝ => x ^ k)
      (Set.Ioc (i.val : ℝ) ((i.val : ℝ) + 1)) (gaussianReal 0 1) :=
    (show Continuous (fun x : ℝ => x ^ k) by fun_prop).integrableOn_Ioc
  exact hI.integrable_indicator measurableSet_Ioc

private lemma gaussianBlock_measure_pos {n : ℕ} (i : Fin n) :
    0 < (gaussianReal 0 1) (gaussianBlock i) := by
  have hlt : (i.val : ℝ) < (i.val : ℝ) + 1 := by linarith
  have hfi : IntervalIntegrable (gaussianPDFReal 0 1) volume
      (i.val : ℝ) ((i.val : ℝ) + 1) :=
    (integrable_gaussianPDFReal 0 1).intervalIntegrable
  have hposInt : 0 < ∫ x in (i.val : ℝ)..((i.val : ℝ) + 1), gaussianPDFReal 0 1 x :=
    intervalIntegral.intervalIntegral_pos_of_pos hfi
      (fun x => gaussianPDFReal_pos 0 1 x one_ne_zero) hlt
  have hposSet : 0 < ∫ x in gaussianBlock i, gaussianPDFReal 0 1 x := by
    simpa [gaussianBlock, intervalIntegral.integral_of_le hlt.le] using hposInt
  rw [gaussianReal_apply_eq_integral (μ := 0) (v := 1) one_ne_zero]
  exact ENNReal.ofReal_pos.mpr hposSet

private lemma gaussianBlock_indicator_sum_eq {n : ℕ} (a : Fin n → ℝ)
    (i : Fin n) {x : ℝ} (hx : x ∈ gaussianBlock i) :
    ∑ j : Fin n, (gaussianBlock j).indicator (fun _ => a j) x = a i := by
  classical
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem hx _
  · intro j _ hji
    rw [Set.indicator_apply, if_neg]
    intro hxj
    exact (Set.disjoint_left.mp (gaussianBlock_disjoint hji)) hxj hx
  · simp

/-- For [a finite degree cutoff](hyp:K), [there is a measurable profile bounded by one,
nonzero under the standard Gaussian law, and orthogonal to every monomial through that
cutoff](goal). -/
theorem exists_bounded_gaussian_orthogonal_perturbation (K : ℕ) :
    ∃ h : ℝ → ℝ,
      Measurable h ∧
      (∀ x, |h x| ≤ 1) ∧
      0 < ∫ x, |h x| ∂gaussianReal 0 1 ∧
      ∀ k, k ≤ K →
        Integrable (fun x => x ^ k * h x) (gaussianReal 0 1) ∧
        (∫ x, x ^ k * h x ∂gaussianReal 0 1) = 0 := by
  classical
  let A : Matrix (Fin (K + 1)) (Fin (K + 2)) ℝ := fun j i =>
    ∫ x in gaussianBlock i, x ^ (j : ℕ) ∂gaussianReal 0 1
  let T : (Fin (K + 2) → ℝ) →ₗ[ℝ] (Fin (K + 1) → ℝ) := A.mulVecLin
  have hT_not_injective : ¬ Function.Injective T := by
    intro hT
    have hdim := LinearMap.finrank_le_finrank_of_injective hT
    simp only [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  obtain ⟨c, d, hTcd, hcd⟩ := Function.not_injective_iff.mp hT_not_injective
  let v : Fin (K + 2) → ℝ := c - d
  have hv_ne : v ≠ 0 := sub_ne_zero.mpr hcd
  have hTv : T v = 0 := by
    dsimp [v]
    rw [map_sub, hTcd, sub_self]
  have hv_norm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv_ne
  let a : Fin (K + 2) → ℝ := fun i => v i / ‖v‖
  let h : ℝ → ℝ := fun x =>
    ∑ i : Fin (K + 2), (gaussianBlock i).indicator (fun _ => a i) x
  have ha_le (i : Fin (K + 2)) : |a i| ≤ 1 := by
    have hvi : |v i| ≤ ‖v‖ := by
      rw [Pi.norm_def]
      exact_mod_cast Finset.le_sup (f := fun j => ‖v j‖₊) (Finset.mem_univ i)
    change |v i / ‖v‖| ≤ 1
    rw [abs_div, abs_of_nonneg (norm_nonneg v)]
    exact (div_le_one hv_norm_pos).mpr hvi
  have hh_meas : Measurable h := by
    dsimp [h]
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator (gaussianBlock_measurable i)
  have hh_bound : ∀ x, |h x| ≤ 1 := by
    intro x
    by_cases hx : ∃ i : Fin (K + 2), x ∈ gaussianBlock i
    · obtain ⟨i, hxi⟩ := hx
      change |∑ j : Fin (K + 2),
        (gaussianBlock j).indicator (fun _ => a j) x| ≤ 1
      rw [gaussianBlock_indicator_sum_eq a i hxi]
      exact ha_le i
    · have hz : h x = 0 := by
        dsimp [h]
        apply Finset.sum_eq_zero
        intro i _
        rw [Set.indicator_apply, if_neg]
        exact fun hxi => hx ⟨i, hxi⟩
      simp [hz]
  have hh_integrable : Integrable (fun x => |h x|) (gaussianReal 0 1) := by
    apply (integrable_const (μ := gaussianReal 0 1) (1 : ℝ)).mono'
    · exact hh_meas.abs.aestronglyMeasurable
    · filter_upwards [] with x
      simpa only [Real.norm_eq_abs, abs_abs] using hh_bound x
  have hh_pos : 0 < ∫ x, |h x| ∂gaussianReal 0 1 := by
    obtain ⟨i, hvi⟩ : ∃ i, v i ≠ 0 := by
      simpa [Function.ne_iff] using hv_ne
    let g : ℝ → ℝ := (gaussianBlock i).indicator (fun _ => |a i|)
    have hg_integrable : Integrable g (gaussianReal 0 1) := by
      exact (integrable_const (μ := gaussianReal 0 1) |a i|).indicator
        (gaussianBlock_measurable i)
    have hg_le : ∀ x, g x ≤ |h x| := by
      intro x
      by_cases hx : x ∈ gaussianBlock i
      · simp only [g, Set.indicator_of_mem hx]
        change |a i| ≤ |∑ j : Fin (K + 2),
          (gaussianBlock j).indicator (fun _ => a j) x|
        rw [gaussianBlock_indicator_sum_eq a i hx]
      · simp [g, hx]
    have hg_pos : 0 < ∫ x, g x ∂gaussianReal 0 1 := by
      rw [integral_indicator (gaussianBlock_measurable i), setIntegral_const]
      exact mul_pos
        (ENNReal.toReal_pos (ne_of_gt (gaussianBlock_measure_pos i))
          (MeasureTheory.measure_ne_top _ _))
        (abs_pos.mpr (div_ne_zero hvi (ne_of_gt hv_norm_pos)))
    exact hg_pos.trans_le (integral_mono hg_integrable hh_integrable hg_le)
  refine ⟨h, hh_meas, hh_bound, hh_pos, ?_⟩
  intro k hk
  have hterm (i : Fin (K + 2)) :
      Integrable (fun x => a i * (gaussianBlock i).indicator (fun x : ℝ => x ^ k) x)
        (gaussianReal 0 1) :=
    (integrable_gaussianBlock_pow i).const_mul (a i)
  have hfun : (fun x => x ^ k * h x) = fun x =>
      ∑ i : Fin (K + 2), a i * (gaussianBlock i).indicator (fun x : ℝ => x ^ k) x := by
    funext x
    dsimp [h]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hxi : x ∈ gaussianBlock i
    · simp [hxi, mul_comm]
    · simp [hxi]
  have hint : Integrable (fun x => x ^ k * h x) (gaussianReal 0 1) := by
    rw [hfun]
    simpa only [Finset.sum_const_zero, Finset.sum_attach] using
      integrable_finsetSum Finset.univ (fun i _ => hterm i)
  refine ⟨hint, ?_⟩
  rw [hfun, integral_finsetSum Finset.univ (fun i _ => hterm i)]
  simp_rw [integral_const_mul, integral_indicator (gaussianBlock_measurable _)]
  have hj : k < K + 1 := by omega
  have hTvj : (T v) (⟨k, hj⟩ : Fin (K + 1)) = 0 := by
    rw [hTv]
    rfl
  change (∑ i : Fin (K + 2), (v i / ‖v‖) * A ⟨k, hj⟩ i) = 0
  calc
    (∑ i : Fin (K + 2), (v i / ‖v‖) * A ⟨k, hj⟩ i)
        = (1 / ‖v‖) * (T v) ⟨k, hj⟩ := by
            simp only [T, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = 0 := by rw [hTvj, mul_zero]

end Causalean.Stat.MomentProblems
