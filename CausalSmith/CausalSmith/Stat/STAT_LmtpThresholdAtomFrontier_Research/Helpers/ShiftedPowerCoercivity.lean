/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import CausalSmith.Stat.STAT_LmtpThresholdAtomFrontier_Research.Helpers.Design
import Causalean.Stat.Nonparametric.LocalPolynomial.GramCoercivity

/-!
# Uniform coercivity for shifted-power moment matrices

This module isolates the reusable compactification step behind the population
Gram lower bound for polynomially thinned local designs.
-/

namespace CausalSmith.Stat.LmtpThresholdAtomFrontier

open MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

open Causalean.Stat.Nonparametric.LocalPolynomial

private noncomputable def powerPolynomialEnergy (ell : ℕ) (kappa : ℝ)
    (z : Fin (ell + 1) → ℝ) : ℝ :=
  ∑ i, ∑ j, z i * z j /
    ((i : ℕ) + (j : ℕ) + kappa + 1)

private lemma powerPolynomialEnergy_eq_integral (ell : ℕ) {kappa : ℝ}
    (hkappa : 0 ≤ kappa) (z : Fin (ell + 1) → ℝ) :
    powerPolynomialEnergy ell kappa z =
      ∫ u in (0 : ℝ)..1,
        (∑ i, z i * u ^ (i : ℕ)) ^ 2 * u ^ kappa := by
  rw [powerPolynomialEnergy]
  simp_rw [pow_two, Fintype.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  have hexp : -1 < ((i : ℕ) + (j : ℕ) : ℝ) + kappa := by
    have hn : 0 ≤ ((i : ℕ) + (j : ℕ) : ℝ) := by positivity
    linarith
  rw [show (∫ u in (0 : ℝ)..1,
      (z i * u ^ (i : ℕ)) * (z j * u ^ (j : ℕ)) * u ^ kappa) =
      ∫ u in (0 : ℝ)..1,
        (z i * z j) * u ^ (((i : ℕ) + (j : ℕ) : ℝ) + kappa) by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have hu0 : 0 ≤ u := hu.1
    let n : ℕ := (i : ℕ) + (j : ℕ)
    calc
      (z i * u ^ (i : ℕ)) * (z j * u ^ (j : ℕ)) * u ^ kappa =
          (z i * z j) * (u ^ (i : ℕ) * u ^ (j : ℕ)) * u ^ kappa := by ring
      _ = (z i * z j) * u ^ ((i : ℕ) + (j : ℕ)) * u ^ kappa := by rw [pow_add]
      _ = (z i * z j) * (u ^ (n : ℝ)) * u ^ kappa := by
        simp only [Real.rpow_natCast, n]
      _ = (z i * z j) * u ^ (((i : ℕ) + (j : ℕ) : ℝ) + kappa) := by
        rw [Real.rpow_add_of_nonneg hu0 (by positivity) hkappa]
        norm_num [n]
        ring]
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hexp)]
  rw [Real.one_rpow]
  have hzero : (0 : ℝ) ^ (((i : ℕ) + (j : ℕ) : ℝ) + kappa + 1) = 0 := by
    rw [Real.zero_rpow]
    positivity
  rw [hzero]
  ring
  all_goals
    intros
    apply Continuous.intervalIntegrable
    fun_prop

private lemma powerPolynomialEnergy_pos (ell : ℕ) {kappa : ℝ}
    (hkappa : 0 ≤ kappa) {z : Fin (ell + 1) → ℝ} (hz : z ≠ 0) :
    0 < powerPolynomialEnergy ell kappa z := by
  let f : ℝ → ℝ := fun u =>
    (∑ i, z i * u ^ (i : ℕ)) ^ 2 * u ^ kappa
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    fun_prop
  have hfint : IntervalIntegrable f volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hfcont
  rw [powerPolynomialEnergy_eq_integral ell hkappa]
  have hpoly : localPolynomial ell z ≠ 0 := by
    simpa [localPolynomial_eq_zero_iff] using hz
  have hroots : Set.Finite {u : ℝ | Polynomial.IsRoot (localPolynomial ell z) u} :=
    (Polynomial.roots (localPolynomial ell z)).toFinset.finite_toSet.subset (by
      intro u hu
      simpa [Polynomial.mem_roots hpoly] using hu)
  have hinter : Set.Infinite (Set.Ioo (0 : ℝ) 1) := Set.Ioo_infinite (by norm_num)
  obtain ⟨u, huI, huroot⟩ := (hinter.sdiff hroots).nonempty
  have hune : (∑ i, z i * u ^ (i : ℕ)) ≠ 0 := by
    rw [← localPolynomial_eval]
    intro he
    exact huroot (by simpa [Polynomial.IsRoot] using he)
  have hfu : f u ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hune) (ne_of_gt (Real.rpow_pos_of_pos huI.1 kappa))
  rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae'
    (by
      filter_upwards [ae_restrict_mem
        (measurableSet_uIoc : MeasurableSet (Set.uIoc (0 : ℝ) 1))] with x hx
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx.1.le _)) hfint]
  refine ⟨by norm_num, ?_⟩
  have hfcu : ContinuousAt f u := by
    dsimp [f]
    fun_prop
  have hsupport_nhds : Function.support f ∈ 𝓝 u := by
    exact hfcu (isOpen_compl_singleton.mem_nhds hfu)
  obtain ⟨V, hVsub, hVopen, huV⟩ := mem_nhds_iff.mp hsupport_nhds
  let U := V ∩ Set.Ioo (0 : ℝ) 1
  have hUopen : IsOpen U := hVopen.inter isOpen_Ioo
  have hUne : U.Nonempty := ⟨u, huV, huI⟩
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono (by
    intro x hx
    exact ⟨hVsub hx.1, hx.2.1, hx.2.2.le⟩))

private lemma powerPolynomialEnergy_continuous (ell : ℕ) (kappa : ℝ) :
    Continuous (powerPolynomialEnergy ell kappa) := by
  unfold powerPolynomialEnergy
  fun_prop

private lemma powerPolynomialEnergy_smul (ell : ℕ) (kappa a : ℝ)
    (z : Fin (ell + 1) → ℝ) :
    powerPolynomialEnergy ell kappa (a • z) =
      a ^ 2 * powerPolynomialEnergy ell kappa z := by
  unfold powerPolynomialEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private lemma powerPolynomialEnergy_coercive (ell : ℕ) {kappa : ℝ}
    (hkappa : 0 ≤ kappa) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Fin (ell + 1) → ℝ,
      c * ∑ i, (z i) ^ 2 ≤ powerPolynomialEnergy ell kappa z := by
  let S : Set (Fin (ell + 1) → ℝ) := Metric.sphere 0 1
  have hScompact : IsCompact S := isCompact_sphere 0 1
  have hSne : S.Nonempty := by
    refine ⟨fun _i => 1, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right]
    simpa using (pi_norm_const' (ι := Fin (ell + 1)) (1 : ℝ))
  obtain ⟨z0, hz0S, hz0min⟩ := hScompact.exists_isMinOn hSne
    (powerPolynomialEnergy_continuous ell kappa).continuousOn
  have hz0ne : z0 ≠ 0 := by
    intro h
    subst z0
    simpa [S] using hz0S
  let c := powerPolynomialEnergy ell kappa z0 / (ell + 1 : ℝ)
  have hqpos : (0 : ℝ) < ell + 1 := by positivity
  refine ⟨c, div_pos (powerPolynomialEnergy_pos ell hkappa hz0ne) hqpos, ?_⟩
  intro z
  by_cases hz : z = 0
  · subst z
    simp [powerPolynomialEnergy]
  · let r : ℝ := ‖z‖
    have hrpos : 0 < r := norm_pos_iff.mpr hz
    let v : Fin (ell + 1) → ℝ := r⁻¹ • z
    have hvS : v ∈ S := by
      rw [Metric.mem_sphere, dist_zero_right]
      change ‖r⁻¹ • z‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hrpos]
      exact inv_mul_cancel₀ hrpos.ne'
    have hmin := hz0min hvS
    have hscale := powerPolynomialEnergy_smul ell kappa r v
    have hrv : r • v = z := by
      ext i
      simp [v, r, hrpos.ne']
    rw [hrv] at hscale
    have hsum : ∑ i, (z i) ^ 2 ≤ (ell + 1 : ℝ) * r ^ 2 := by
      calc
        ∑ i, (z i) ^ 2 ≤ ∑ _i : Fin (ell + 1), r ^ 2 := by
          apply Finset.sum_le_sum
          intro i hi
          simpa [sq_abs, r] using
            (sq_le_sq₀ (abs_nonneg (z i)) (norm_nonneg z)).2
              (norm_le_pi_norm z i)
        _ = (ell + 1 : ℝ) * r ^ 2 := by simp
    dsimp [c]
    calc
      powerPolynomialEnergy ell kappa z0 / (ell + 1 : ℝ) * ∑ i, (z i) ^ 2
          = powerPolynomialEnergy ell kappa z0 *
              ((∑ i, (z i) ^ 2) / (ell + 1 : ℝ)) := by ring
      _ ≤ powerPolynomialEnergy ell kappa z0 * r ^ 2 := by
        apply mul_le_mul_of_nonneg_left _
          (powerPolynomialEnergy_pos ell hkappa hz0ne).le
        exact (div_le_iff₀ hqpos).2 (by simpa [mul_comm] using hsum)
      _ ≤ powerPolynomialEnergy ell kappa v * r ^ 2 := by
        exact mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
      _ = powerPolynomialEnergy ell kappa z := by
        rw [mul_comm, ← hscale]

private lemma matrixQuadratic_refMomentMatrix_eq (ell : ℕ) {kappa : ℝ}
    (hkappa : 0 ≤ kappa) (rho : ℝ)
    (z : Fin (ell + 1) → ℝ) :
    matrixQuadratic (refMomentMatrix ell kappa rho) z =
      (∫ u in (0 : ℝ)..1,
        (∑ i, z i * u ^ (i : ℕ)) ^ 2 * (rho + u) ^ kappa) /
      (∫ u in (0 : ℝ)..1, (rho + u) ^ kappa) := by
  unfold matrixQuadratic refMomentMatrix
  simp_rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp_rw [pow_two, Fintype.sum_mul_sum, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rw [intervalIntegral.integral_finsetSum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show z i *
      ((∫ u in (0 : ℝ)..1,
        monomialVec ell u i * monomialVec ell u j * (rho + u) ^ kappa) /
        (∫ u in (0 : ℝ)..1, (rho + u) ^ kappa)) * z j =
      (z i * (∫ u in (0 : ℝ)..1,
        monomialVec ell u i * monomialVec ell u j * (rho + u) ^ kappa) * z j) /
        (∫ u in (0 : ℝ)..1, (rho + u) ^ kappa) by ring]
  congr 1
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_mul_const]
  congr 1
  funext u
  dsimp [monomialVec]
  ring
  all_goals
    intros
    apply Continuous.intervalIntegrable
    fun_prop

/-- Normalized monomial moment matrices weighted by `(ρ + u)^κ` are uniformly
coercive over all nonnegative shifts `ρ` when `κ` is nonnegative. The result uses [the `hkappa` condition](hyp:hkappa). [This is the stated conclusion](goal).
-/
theorem uniform_shifted_power_moment_coercivity
    (ell : ℕ) {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    ∃ c : ℝ, 0 < c ∧ ∀ rho : ℝ, 0 ≤ rho →
      ∀ z : Fin (ell + 1) → ℝ,
        c * (∑ i, (z i) ^ 2) ≤
          matrixQuadratic (refMomentMatrix ell kappa rho) z := by
  obtain ⟨c, hcpos, hcoercive⟩ := powerPolynomialEnergy_coercive ell hkappa
  refine ⟨c, hcpos, ?_⟩
  intro rho hrho z
  let P : ℝ → ℝ := fun u => ∑ i, z i * u ^ (i : ℕ)
  let D : ℝ := ∫ u in (0 : ℝ)..1, (rho + u) ^ kappa
  let N : ℝ := ∫ u in (0 : ℝ)..1, (P u) ^ 2 * (rho + u) ^ kappa
  let E : ℝ := powerPolynomialEnergy ell kappa z
  let R : ℝ := (rho + 1) ^ kappa
  have hrho1 : 0 < rho + 1 := by linarith
  have hRpos : 0 < R := Real.rpow_pos_of_pos hrho1 kappa
  have hDpos : 0 < D := by
    dsimp [D]
    apply intervalIntegral.integral_pos (by norm_num)
    · fun_prop
    · intro x hx
      exact Real.rpow_nonneg (by linarith [hx.1]) _
    · refine ⟨1, by norm_num, ?_⟩
      exact Real.rpow_pos_of_pos hrho1 kappa
  have hDle : D ≤ R := by
    dsimp [D, R]
    have hmono := intervalIntegral.integral_mono_on
      (show (0 : ℝ) ≤ 1 by norm_num)
      (show IntervalIntegrable (fun u : ℝ => (rho + u) ^ kappa) volume 0 1 by
        apply Continuous.intervalIntegrable
        fun_prop)
      (show IntervalIntegrable (fun _u : ℝ => (rho + 1) ^ kappa) volume 0 1 by
        apply Continuous.intervalIntegrable
        fun_prop)
      (fun u hu => Real.rpow_le_rpow (by linarith [hu.1]) (by linarith [hu.2]) hkappa)
    simpa using hmono
  have hEN : R * E ≤ N := by
    dsimp [N, E, R]
    rw [powerPolynomialEnergy_eq_integral ell hkappa]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on (by norm_num)
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro u hu
      have hu0 : 0 ≤ u := hu.1
      have hbase : u * (rho + 1) ≤ rho + u := by
        nlinarith [hrho, hu.2]
      have hpow := Real.rpow_le_rpow (mul_nonneg hu0 hrho1.le) hbase hkappa
      rw [Real.mul_rpow hu0 hrho1.le] at hpow
      have hsq : 0 ≤ (∑ i, z i * u ^ (i : ℕ)) ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left hpow hsq]
  have hE_nonneg : 0 ≤ E := by
    exact (mul_nonneg hcpos.le (Finset.sum_nonneg fun _ _ => sq_nonneg _)).trans
      (hcoercive z)
  have hED : D * E ≤ N :=
    (mul_le_mul_of_nonneg_right hDle hE_nonneg).trans hEN
  calc
    c * ∑ i, (z i) ^ 2 ≤ E := hcoercive z
    _ ≤ N / D := (le_div_iff₀ hDpos).2 (by simpa [mul_comm] using hED)
    _ = matrixQuadratic (refMomentMatrix ell kappa rho) z := by
      rw [matrixQuadratic_refMomentMatrix_eq ell hkappa rho]

/-- The uniform population-Gram constant is positive under positive envelope
constants and a nonnegative thinning exponent. The result uses [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus). [This is the stated conclusion](goal).
-/
theorem lambdaStar_pos
    (ell : ℕ) {kappa cminus cplus : ℝ}
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 < cplus) :
    0 < lambdaStar ell kappa cminus cplus := by
  obtain ⟨c, hcpos, hcoercive⟩ :=
    uniform_shifted_power_moment_coercivity ell hkappa
  have hqmin (rho : ℝ) (hrho : 0 ≤ rho) :
      c ≤ quadraticMin (refMomentMatrix ell kappa rho) := by
    unfold quadraticMin
    apply le_csInf
    · let e : Fin (ell + 1) := 0
      let zunit : Fin (ell + 1) → ℝ := Pi.single e 1
      refine ⟨matrixQuadratic (refMomentMatrix ell kappa rho) zunit,
        zunit, ?_, rfl⟩
      classical
      simp [zunit, e, Pi.single_apply]
    · intro q hq
      rcases hq with ⟨z, hzunit, rfl⟩
      have h := hcoercive rho hrho z
      rw [hzunit, mul_one] at h
      exact h
  have hset_nonempty :
      {q : ℝ | ∃ rho : ℝ, 0 ≤ rho ∧
        q = quadraticMin (refMomentMatrix ell kappa rho)}.Nonempty := by
    refine ⟨quadraticMin (refMomentMatrix ell kappa 0), 0, le_rfl, rfl⟩
  have hsinf : c ≤ sInf {q : ℝ | ∃ rho : ℝ, 0 ≤ rho ∧
      q = quadraticMin (refMomentMatrix ell kappa rho)} := by
    apply le_csInf hset_nonempty
    intro q hq
    rcases hq with ⟨rho, hrho, rfl⟩
    exact hqmin rho hrho
  unfold lambdaStar
  exact mul_pos (div_pos hcminus hcplus) (lt_of_lt_of_le hcpos hsinf)

/-- `lambdaStar` gives the advertised coercivity for every normalized shifted
power moment matrix. The result uses [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hrho` condition](hyp:hrho). [This is the stated conclusion](goal).
-/
-- @node: lambdaStar_refMomentMatrix_coercive
theorem lambdaStar_refMomentMatrix_coercive
    (ell : ℕ) {kappa cminus cplus : ℝ}
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 < cplus)
    (rho : ℝ) (hrho : 0 ≤ rho) (v : Fin (ell + 1) → ℝ) :
    lambdaStar ell kappa cminus cplus * (∑ i, (v i) ^ 2) ≤
      (cminus / cplus) * matrixQuadratic (refMomentMatrix ell kappa rho) v := by
  classical
  obtain ⟨c, hc, hcoercive⟩ :=
    uniform_shifted_power_moment_coercivity ell hkappa
  let Q := {q : ℝ | ∃ z : Fin (ell + 1) → ℝ,
    (∑ i, (z i) ^ 2) = 1 ∧
      q = matrixQuadratic (refMomentMatrix ell kappa rho) z}
  have hQne : Q.Nonempty := by
    let e : Fin (ell + 1) := 0
    let z : Fin (ell + 1) → ℝ := Pi.single e 1
    refine ⟨matrixQuadratic (refMomentMatrix ell kappa rho) z, z, ?_, rfl⟩
    simp [z, e, Pi.single_apply]
  have hQbelow : BddBelow Q := by
    refine ⟨c, ?_⟩
    intro q hq
    rcases hq with ⟨z, hz, rfl⟩
    simpa [hz] using hcoercive rho hrho z
  have hsinf_le : sInf {q : ℝ | ∃ r : ℝ, 0 ≤ r ∧
      q = quadraticMin (refMomentMatrix ell kappa r)} ≤
      quadraticMin (refMomentMatrix ell kappa rho) := by
    apply csInf_le
    · refine ⟨c, ?_⟩
      intro q hq
      rcases hq with ⟨r, hr, rfl⟩
      unfold quadraticMin
      exact le_csInf (by
        let e : Fin (ell + 1) := 0
        let z : Fin (ell + 1) → ℝ := Pi.single e 1
        refine ⟨matrixQuadratic (refMomentMatrix ell kappa r) z, z, ?_, rfl⟩
        simp [z, e, Pi.single_apply]) (by
          intro q hq
          rcases hq with ⟨z, hz, rfl⟩
          simpa [hz] using hcoercive r hr z)
    · exact ⟨rho, hrho, rfl⟩
  have hqmin : quadraticMin (refMomentMatrix ell kappa rho) *
      (∑ i, (v i) ^ 2) ≤ matrixQuadratic (refMomentMatrix ell kappa rho) v := by
    let S : ℝ := ∑ i, (v i) ^ 2
    by_cases hS : S = 0
    · have hv : v = 0 := by
        funext i
        have hi : (v i) ^ 2 = 0 := le_antisymm
          (hS ▸ Finset.single_le_sum (fun j _ => sq_nonneg (v j))
            (Finset.mem_univ i)) (sq_nonneg _)
        exact sq_eq_zero_iff.mp hi
      simp [S, hS, hv, matrixQuadratic]
    · have hSpos : 0 < S := lt_of_le_of_ne
          (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Ne.symm hS)
      let r := Real.sqrt S
      let z : Fin (ell + 1) → ℝ := r⁻¹ • v
      have hr : 0 < r := Real.sqrt_pos.2 hSpos
      have hr_sq0 : r ^ 2 = S := Real.sq_sqrt hSpos.le
      have hz : ∑ i, (z i) ^ 2 = 1 := by
        change ∑ i, (r⁻¹ * v i) ^ 2 = 1
        calc
          ∑ i, (r⁻¹ * v i) ^ 2 = r⁻¹ ^ 2 * ∑ i, (v i) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = r⁻¹ ^ 2 * r ^ 2 := by rw [show (∑ i, (v i) ^ 2) = S from rfl, ← hr_sq0]
          _ = 1 := by field_simp
      have hmin : quadraticMin (refMomentMatrix ell kappa rho) ≤
          matrixQuadratic (refMomentMatrix ell kappa rho) z := by
        unfold quadraticMin
        exact csInf_le hQbelow ⟨z, hz, rfl⟩
      have hscale : matrixQuadratic (refMomentMatrix ell kappa rho) z =
          r⁻¹ ^ 2 * matrixQuadratic (refMomentMatrix ell kappa rho) v := by
        simp [z, matrixQuadratic, Finset.mul_sum]
        ring_nf
      rw [hscale] at hmin
      rw [show (∑ i, (v i) ^ 2) = r ^ 2 by exact hr_sq0.symm]
      calc
        quadraticMin (refMomentMatrix ell kappa rho) * r ^ 2 ≤
            (r⁻¹ ^ 2 * matrixQuadratic (refMomentMatrix ell kappa rho) v) * r ^ 2 :=
          mul_le_mul_of_nonneg_right hmin (sq_nonneg r)
        _ = _ := by field_simp
  unfold lambdaStar
  have hcoef : 0 ≤ cminus / cplus := div_nonneg hcminus.le hcplus.le
  have hsum : 0 ≤ ∑ i, (v i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc
    cminus / cplus * sInf {q : ℝ | ∃ r : ℝ, 0 ≤ r ∧
        q = quadraticMin (refMomentMatrix ell kappa r)} *
          (∑ i, (v i) ^ 2) ≤
        cminus / cplus * quadraticMin (refMomentMatrix ell kappa rho) *
          (∑ i, (v i) ^ 2) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsinf_le hcoef) hsum
    _ ≤ cminus / cplus * matrixQuadratic (refMomentMatrix ell kappa rho) v := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hqmin (div_pos hcminus hcplus).le

/-- The normalized `lambdaStar` coercivity, transported from the unit interval
to a positive local window. The result uses [the `hkappa` condition](hyp:hkappa), [the `hcminus` condition](hyp:hcminus), [the `hcplus` condition](hyp:hcplus), [the `hdelta` condition](hyp:hdelta), [the `hh` condition](hyp:hh). [This is the stated conclusion](goal).
-/
-- @node: lambdaStar_scaled_power_window_coercive
theorem lambdaStar_scaled_power_window_coercive
    (ell : ℕ) {kappa cminus cplus delta h : ℝ}
    (hkappa : 0 ≤ kappa) (hcminus : 0 < cminus) (hcplus : 0 < cplus)
    (hdelta : 0 ≤ delta) (hh : 0 < h) (v : Fin (ell + 1) → ℝ) :
    lambdaStar ell kappa cminus cplus * cplus *
          (∫ a in delta..delta + h, a ^ kappa) * (∑ i, (v i) ^ 2) ≤
      cminus * ∫ a in delta..delta + h,
        (∑ i, v i * ((a - delta) / h) ^ (i : ℕ)) ^ 2 * a ^ kappa := by
  let rho := delta / h
  let D := ∫ u in (0 : ℝ)..1, (rho + u) ^ kappa
  let N := ∫ u in (0 : ℝ)..1,
    (∑ i, v i * u ^ (i : ℕ)) ^ 2 * (rho + u) ^ kappa
  have hrho : 0 ≤ rho := div_nonneg hdelta hh.le
  have hD : 0 < D := by
    dsimp [D]
    apply intervalIntegral.integral_pos (by norm_num)
    · fun_prop
    · intro u hu
      exact Real.rpow_nonneg (by linarith [hu.1]) _
    · refine ⟨1, by norm_num, ?_⟩
      exact Real.rpow_pos_of_pos (by dsimp [rho]; positivity) _
  have href := lambdaStar_refMomentMatrix_coercive ell hkappa hcminus hcplus
    rho hrho v
  rw [matrixQuadratic_refMomentMatrix_eq ell hkappa rho] at href
  change lambdaStar ell kappa cminus cplus * (∑ i, (v i) ^ 2) ≤
    (cminus / cplus) * (N / D) at href
  have hunit :
      lambdaStar ell kappa cminus cplus * cplus * D * (∑ i, (v i) ^ 2) ≤
        cminus * N := by
    have hcD : 0 < cplus * D := mul_pos hcplus hD
    calc
      lambdaStar ell kappa cminus cplus * cplus * D * (∑ i, (v i) ^ 2) =
          (lambdaStar ell kappa cminus cplus * (∑ i, (v i) ^ 2)) *
            (cplus * D) := by ring
      _ ≤ ((cminus / cplus) * (N / D)) * (cplus * D) :=
        mul_le_mul_of_nonneg_right href hcD.le
      _ = cminus * N := by field_simp [hcplus.ne', hD.ne']
  have hscale (F : ℝ → ℝ) :
      (∫ a in delta..delta + h, F a) = h * ∫ u in (0 : ℝ)..1, F (delta + h * u) := by
    rw [intervalIntegral.mul_integral_comp_add_mul]
    congr 1 <;> ring
  have hpow (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (delta + h * u) ^ kappa = h ^ kappa * (rho + u) ^ kappa := by
    have hr : delta + h * u = h * (rho + u) := by
      dsimp [rho]
      field_simp [hh.ne']
    rw [hr, Real.mul_rpow hh.le (add_nonneg hrho hu.1)]
  have hden :
      (∫ a in delta..delta + h, a ^ kappa) = h * h ^ kappa * D := by
    rw [hscale]
    change h * (∫ u in (0 : ℝ)..1, (delta + h * u) ^ kappa) = _
    rw [show (∫ u in (0 : ℝ)..1, (delta + h * u) ^ kappa) =
        ∫ u in (0 : ℝ)..1, h ^ kappa * (rho + u) ^ kappa by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      exact hpow u hu]
    rw [intervalIntegral.integral_const_mul]
    simp only [D]
    ring
  have hnum :
      (∫ a in delta..delta + h,
          (∑ i, v i * ((a - delta) / h) ^ (i : ℕ)) ^ 2 * a ^ kappa) =
        h * h ^ kappa * N := by
    rw [hscale]
    change h * (∫ u in (0 : ℝ)..1,
      (∑ i, v i * ((delta + h * u - delta) / h) ^ (i : ℕ)) ^ 2 *
        (delta + h * u) ^ kappa) = _
    rw [show (∫ u in (0 : ℝ)..1,
        (∑ i, v i * ((delta + h * u - delta) / h) ^ (i : ℕ)) ^ 2 *
          (delta + h * u) ^ kappa) =
        ∫ u in (0 : ℝ)..1,
          h ^ kappa * ((∑ i, v i * u ^ (i : ℕ)) ^ 2 * (rho + u) ^ kappa) by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num)] at hu
      dsimp only
      rw [show (delta + h * u - delta) / h = u by
          field_simp [hh.ne'] <;> ring,
        hpow u hu]
      ring]
    rw [intervalIntegral.integral_const_mul]
    simp only [N]
    ring
  rw [hden, hnum]
  have hhpow : 0 ≤ h * h ^ kappa :=
    mul_nonneg hh.le (Real.rpow_nonneg hh.le _)
  calc
    lambdaStar ell kappa cminus cplus * cplus * (h * h ^ kappa * D) *
          (∑ i, (v i) ^ 2) =
        (h * h ^ kappa) *
          (lambdaStar ell kappa cminus cplus * cplus * D *
            (∑ i, (v i) ^ 2)) := by ring
    _ ≤ (h * h ^ kappa) * (cminus * N) :=
      mul_le_mul_of_nonneg_left hunit hhpow
    _ = cminus * (h * h ^ kappa * N) := by ring

end

end CausalSmith.Stat.LmtpThresholdAtomFrontier
