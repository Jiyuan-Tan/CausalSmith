/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Experimentation.DesignBased.InProb
public import Causalean.Experimentation.FinitePopulationMoments

/-!
# Consistency of finite-population sample variances

This file supplies the variance-estimation half of finite-population inference. It defines the
ordinary sample variance of a simple random sample, proves its centered-second-moment identity,
and establishes consistency under Li--Ding's maximal-deviation regularity. The proof uses only the
exact simple-random-sampling variance formula and Chebyshev's inequality; variance consistency is
not assumed.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter Finset

namespace Causalean
namespace Experimentation
namespace FinitePopulationMoments

open DesignBased

/-- For [a finite population](hyp:U), [a sample size](hyp:n), [outcomes](hyp:y), and [a sample of
that size](hyp:S), the [ordinary sample variance](goal) is the sum of squared deviations from the
sample mean divided by one fewer than the sample size. -/
noncomputable def sampleVariance {U : Type*} [Fintype U] [DecidableEq U]
    (n : ℕ) (y : U → ℝ) (S : {S : Finset U // S.card = n}) : ℝ :=
  (∑ i, if i ∈ S.val then (y i - sampleMean n y S) ^ 2 else 0) / ((n : ℝ) - 1)

/-- For [a nonempty simple random sample](hyp:hn), [its outcomes](hyp:y), and [its realized
sample](hyp:S), [the sample variance equals `n/(n-1)` times the sampled centered second moment
minus the squared sampled centered first moment](goal). -/
lemma sampleVariance_eq_centered {U : Type*} [Fintype U] [DecidableEq U]
    (n : ℕ) (hn : 0 < n) (y : U → ℝ) (S : {S : Finset U // S.card = n}) :
    sampleVariance n y S =
      ((n : ℝ) / ((n : ℝ) - 1)) *
        (sampleMean n (fun i => (y i - popMean y) ^ 2) S -
          (sampleMean n (fun i => y i - popMean y) S) ^ 2) := by
  classical
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcenter : sampleMean n (fun i => y i - popMean y) S =
      sampleMean n y S - popMean y := by
    unfold sampleMean
    have hsum : (∑ i : U, if i ∈ S.val then y i - popMean y else 0) =
        (∑ i : U, if i ∈ S.val then y i else 0) - (n : ℝ) * popMean y := by
      rw [← Finset.sum_filter, Finset.sum_sub_distrib]
      simp [S.property]
    rw [hsum]
    field_simp
  let x : U → ℝ := fun i => y i - popMean y
  let xb : ℝ := sampleMean n x S
  have hsumxS : (∑ i ∈ S.val, x i) = (n : ℝ) * xb := by
    dsimp [xb]
    unfold sampleMean
    rw [show (∑ i : U, if i ∈ S.val then x i else 0) = ∑ i ∈ S.val, x i by simp]
    field_simp
  have hsq : (∑ i : U, if i ∈ S.val then (x i - xb) ^ 2 else 0) =
      (∑ i : U, if i ∈ S.val then (x i) ^ 2 else 0) - (n : ℝ) * xb ^ 2 := by
    rw [show (∑ i : U, if i ∈ S.val then (x i - xb) ^ 2 else 0) =
      ∑ i ∈ S.val, (x i - xb) ^ 2 by simp]
    rw [show (∑ i : U, if i ∈ S.val then x i ^ 2 else 0) =
      ∑ i ∈ S.val, x i ^ 2 by simp]
    have hterm : ∀ i, (x i - xb) ^ 2 = x i ^ 2 - 2 * xb * x i + xb ^ 2 := by
      intro i
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hsumxS]
    simp [S.property]
    ring
  unfold sampleVariance
  have hshift :
      (∑ i : U, if i ∈ S.val then (y i - sampleMean n y S) ^ 2 else 0) =
        ∑ i : U, if i ∈ S.val then (x i - xb) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i ∈ S.val <;> simp [hi, x, xb, hcenter]
  rw [hshift, hsq]
  change ((∑ i : U, if i ∈ S.val then (y i - popMean y) ^ 2 else 0) -
      (n : ℝ) * (sampleMean n (fun i => y i - popMean y) S) ^ 2) /
        ((n : ℝ) - 1) = _
  unfold sampleMean
  field_simp

/-- For [a population containing at least two units](hyp:hN) and [its outcomes](hyp:y), [the
finite-population variance of the squared centered outcomes is at most the largest squared
centered outcome times the original finite-population variance](goal). -/
lemma popVar_centeredSq_le_max_mul_popVar {U : Type*} [Fintype U]
    [Nonempty U] (hN : 2 ≤ Fintype.card U) (y : U → ℝ) :
    popVar (fun i => (y i - popMean y) ^ 2) ≤ popMaxSqDev y * popVar y := by
  classical
  let N : ℕ := Fintype.card U
  let x : U → ℝ := fun i => y i - popMean y
  let z : U → ℝ := fun i => x i ^ 2
  have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hraw : (∑ i, (z i - popMean z) ^ 2) =
      (∑ i, z i ^ 2) - (∑ i, z i) ^ 2 / (N : ℝ) := by
    unfold popMean
    change (∑ i, (z i - (∑ j, z j) / (N : ℝ)) ^ 2) = _
    have hterm : ∀ i, (z i - (∑ j, z j) / (N : ℝ)) ^ 2 =
        z i ^ 2 - 2 * ((∑ j, z j) / (N : ℝ)) * z i +
          ((∑ j, z j) / (N : ℝ)) ^ 2 := by
      intro i
      ring
    simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change _ = (∑ i, z i ^ 2) - (∑ i, z i) ^ 2 / (N : ℝ)
    field_simp
    ring
  have hraw_le : (∑ i, (z i - popMean z) ^ 2) ≤ ∑ i, z i ^ 2 := by
    rw [hraw]
    have hnonneg : 0 ≤ (∑ i, z i) ^ 2 / (N : ℝ) :=
      div_nonneg (sq_nonneg _) hNpos.le
    linarith
  have hzmax : ∀ i, z i ≤ popMaxSqDev y := by
    intro i
    exact Finset.le_sup' (fun j => (y j - popMean y) ^ 2) (Finset.mem_univ i)
  have hsum_le : (∑ i, z i ^ 2) ≤ popMaxSqDev y * ∑ i, z i := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    change z i ^ 2 ≤ popMaxSqDev y * z i
    rw [sq]
    exact mul_le_mul_of_nonneg_right (hzmax i) (sq_nonneg (x i))
  unfold popVar
  change (∑ i, (z i - popMean z) ^ 2) / ((N : ℝ) - 1) ≤
    popMaxSqDev y * ((∑ i, x i ^ 2) / ((N : ℝ) - 1))
  rw [div_le_iff₀ hN1pos]
  calc
    (∑ i, (z i - popMean z) ^ 2) ≤ ∑ i, z i ^ 2 := hraw_le
    _ ≤ popMaxSqDev y * ∑ i, z i := hsum_le
    _ = (popMaxSqDev y * ((∑ i, x i ^ 2) / ((N : ℝ) - 1))) *
        ((N : ℝ) - 1) := by
      dsimp [z]
      field_simp

/-- For [a nonempty finite population](hyp:U) with [outcomes](hyp:y), [the population mean of
the centered outcomes is zero](goal). -/
lemma popMean_centered_eq_zero {U : Type*} [Fintype U] [Nonempty U]
    (y : U → ℝ) : popMean (fun i => y i - popMean y) = 0 := by
  classical
  have hN : (Fintype.card U : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold popMean
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

namespace SampleVarianceConsistency

variable {U : ℕ → Type*} [∀ k, Fintype (U k)] [∀ k, DecidableEq (U k)]
  [∀ k, Nonempty (U k)]

private lemma FiniteDesign.TendstoInProb.mul_deterministic_of_bounded
    {D : ∀ k, FiniteDesign (U k)} {X : ∀ k, U k → ℝ} (a : ℕ → ℝ)
    (C : ℝ) (ha : ∀ k, |a k| ≤ C)
    (hX : FiniteDesign.TendstoInProb D X (fun _ => 0)) :
    FiniteDesign.TendstoInProb D (fun k w => a k * X k w) (fun _ => 0) := by
  intro ε hε
  have hCp : 0 < |C| + 1 := by positivity
  have hδ : 0 < ε / (|C| + 1) := by positivity
  refine squeeze_zero (fun k => (D k).Pr_nonneg _) (fun k => ?_)
    (hX (ε / (|C| + 1)) hδ)
  apply (D k).Pr_mono
  intro w hw
  simp only [sub_zero] at hw ⊢
  rw [abs_mul] at hw
  rw [div_le_iff₀ hCp]
  have haC : |a k| ≤ |C| + 1 := (ha k).trans (by linarith [le_abs_self C])
  nlinarith [abs_nonneg (X k w)]

private lemma FiniteDesign.TendstoInProb.sq_zero
    {D : ∀ k, FiniteDesign (U k)} {X : ∀ k, U k → ℝ}
    (hX : FiniteDesign.TendstoInProb D X (fun _ => 0)) :
    FiniteDesign.TendstoInProb D (fun k w => (X k w) ^ 2) (fun _ => 0) := by
  intro ε hε
  have hδ : 0 < min 1 ε := lt_min zero_lt_one hε
  refine squeeze_zero (fun k => (D k).Pr_nonneg _) (fun k => ?_)
    (hX (min 1 ε) hδ)
  apply (D k).Pr_mono
  intro w hw
  simp only [sub_zero] at hw ⊢
  rw [abs_pow] at hw
  by_contra hsmall
  have hlt : |X k w| < min 1 ε := lt_of_not_ge hsmall
  have hlt1 : |X k w| < 1 := hlt.trans_le (min_le_left 1 ε)
  have hltε : |X k w| < ε := hlt.trans_le (min_le_right 1 ε)
  nlinarith [abs_nonneg (X k w)]

private lemma sampleVariance_scale_tendsto (n : ℕ → ℕ)
    (hnTop : Tendsto n atTop atTop) :
    Tendsto (fun k => (n k : ℝ) / ((n k : ℝ) - 1)) atTop (𝓝 1) := by
  have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hnTop
  have hinv : Tendsto (fun k => 1 / (n k : ℝ)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hnR using 1 <;> simp [Function.comp_def, one_div]
  have hden : Tendsto (fun k => 1 - 1 / (n k : ℝ)) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hratio : Tendsto (fun k => 1 / (1 - 1 / (n k : ℝ))) atTop (𝓝 1) := by
    simpa [one_div] using hden.inv₀ one_ne_zero
  apply hratio.congr'
  filter_upwards [hnTop.eventually_ge_atTop 1] with k hk
  have hk0 : n k ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk)
  field_simp [Nat.cast_ne_zero.mpr hk0]

private lemma centeredSq_sampleMean_tendstoInProb
    (n : ℕ → ℕ) (hn2 : ∀ k, 2 ≤ n k)
    (hnle : ∀ k, n k ≤ Fintype.card (U k))
    (y : ∀ k, U k → ℝ) (v : ℝ)
    (hvar : Tendsto (fun k => popVar (y k)) atTop (𝓝 v))
    (hmax : Tendsto (fun k => popMaxSqDev (y k) / (n k : ℝ)) atTop (𝓝 0)) :
    FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k => sampleMean (n k) (fun i => (y k i - popMean (y k)) ^ 2))
      (fun k => popMean (fun i => (y k i - popMean (y k)) ^ 2)) := by
  classical
  let z : ∀ k, U k → ℝ := fun k i => (y k i - popMean (y k)) ^ 2
  have hN2 : ∀ k, 2 ≤ Fintype.card (U k) := fun k => (hn2 k).trans (hnle k)
  have hn0 : ∀ k, 0 < n k := fun k => lt_of_lt_of_le (by norm_num) (hn2 k)
  let D : ∀ k, FiniteDesign {S : Finset (U k) // S.card = n k} :=
    fun k => completeRandomization (n k) (hnle k)
  have hvarZ0 : Tendsto (fun k => (D k).Var (sampleMean (n k) (z k))) atTop (𝓝 0) := by
    have hupper0 : Tendsto
        (fun k => (popMaxSqDev (y k) / (n k : ℝ)) * popVar (y k))
        atTop (𝓝 0) := by
      simpa using hmax.mul hvar
    refine squeeze_zero (fun k => (D k).Var_nonneg _) (fun k => ?_) hupper0
    rw [show D k = completeRandomization (n k) (hnle k) by rfl,
      Var_sampleMean (n k) (hnle k) (hn0 k) (hN2 k) (z k)]
    have hfactor_nonneg : 0 ≤ 1 / (n k : ℝ) - 1 / (Fintype.card (U k) : ℝ) := by
      have hnR : (0 : ℝ) < (n k : ℝ) := by exact_mod_cast hn0 k
      have hNR : (0 : ℝ) < (Fintype.card (U k) : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) (hN2 k))
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hnR (by exact_mod_cast hnle k))
    have hpopVarZ : 0 ≤ popVar (z k) := by
      unfold popVar
      apply div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have hN2R : (2 : ℝ) ≤ (Fintype.card (U k) : ℝ) := by exact_mod_cast hN2 k
      linarith
    calc
      (1 / (n k : ℝ) - 1 / (Fintype.card (U k) : ℝ)) * popVar (z k)
          ≤ (1 / (n k : ℝ)) * popVar (z k) := by
            apply mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity))
            exact hpopVarZ
      _ ≤ (1 / (n k : ℝ)) * (popMaxSqDev (y k) * popVar (y k)) := by
            exact mul_le_mul_of_nonneg_left
              (popVar_centeredSq_le_max_mul_popVar (hN2 k) (y k)) (by positivity)
      _ = (popMaxSqDev (y k) / (n k : ℝ)) * popVar (y k) := by ring
  have hz : FiniteDesign.TendstoInProb D
      (fun k => sampleMean (n k) (z k))
      (fun k => popMean (z k)) := by
    have h := FiniteDesign.tendstoInProb_of_var D
      (fun k => sampleMean (n k) (z k)) hvarZ0
    convert h using 1
    funext k
    exact (E_sampleMean (n k) (hnle k) (hn0 k) (z k)).symm
  simpa [D, z]

private lemma centered_sampleMean_tendstoInProb
    (n : ℕ → ℕ) (hn2 : ∀ k, 2 ≤ n k)
    (hnle : ∀ k, n k ≤ Fintype.card (U k))
    (y : ∀ k, U k → ℝ) (v : ℝ)
    (hnTop : Tendsto n atTop atTop)
    (hvar : Tendsto (fun k => popVar (y k)) atTop (𝓝 v)) :
    FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k => sampleMean (n k) (fun i => y k i - popMean (y k)))
      (fun _ => 0) := by
  classical
  let D : ∀ k, FiniteDesign {S : Finset (U k) // S.card = n k} :=
    fun k => completeRandomization (n k) (hnle k)
  let x : ∀ k, U k → ℝ := fun k i => y k i - popMean (y k)
  have hN2 : ∀ k, 2 ≤ Fintype.card (U k) := fun k => (hn2 k).trans (hnle k)
  have hn0 : ∀ k, 0 < n k := fun k => lt_of_lt_of_le (by norm_num) (hn2 k)
  have hvarX0 : Tendsto (fun k => (D k).Var (sampleMean (n k) (x k))) atTop (𝓝 0) := by
    have hnR : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hnTop
    have hinv : Tendsto (fun k => 1 / (n k : ℝ)) atTop (𝓝 0) := by
      convert tendsto_inv_atTop_zero.comp hnR using 1 <;> simp [Function.comp_def, one_div]
    have hupper0 : Tendsto (fun k => (1 / (n k : ℝ)) * popVar (y k))
        atTop (𝓝 0) := by simpa using hinv.mul hvar
    refine squeeze_zero (fun k => (D k).Var_nonneg _) (fun k => ?_) hupper0
    rw [show D k = completeRandomization (n k) (hnle k) by rfl,
      Var_sampleMean (n k) (hnle k) (hn0 k) (hN2 k) (x k)]
    have hpopVarX : popVar (x k) = popVar (y k) := by
      unfold popVar x
      rw [popMean_centered_eq_zero]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hpopVarX]
    have hpopVarY : 0 ≤ popVar (y k) := by
      unfold popVar
      apply div_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _)
      have hN2R : (2 : ℝ) ≤ (Fintype.card (U k) : ℝ) := by exact_mod_cast hN2 k
      linarith
    exact mul_le_mul_of_nonneg_right (sub_le_self _ (by positivity)) hpopVarY
  have hx : FiniteDesign.TendstoInProb D
      (fun k => sampleMean (n k) (x k)) (fun _ => 0) := by
    have h := FiniteDesign.tendstoInProb_of_var D
      (fun k => sampleMean (n k) (x k)) hvarX0
    convert h using 1
    funext k
    rw [E_sampleMean (n k) (hnle k) (hn0 k) (x k), popMean_centered_eq_zero]
  simpa [D, x] using hx

private lemma scaled_popMean_centeredSq_sub_popVar_tendsto
    (n : ℕ → ℕ) (hn2 : ∀ k, 2 ≤ n k)
    (hnle : ∀ k, n k ≤ Fintype.card (U k))
    (y : ∀ k, U k → ℝ) (v : ℝ)
    (hnTop : Tendsto n atTop atTop)
    (hvar : Tendsto (fun k => popVar (y k)) atTop (𝓝 v)) :
    Tendsto (fun k =>
      ((n k : ℝ) / ((n k : ℝ) - 1)) *
        popMean (fun i => (y k i - popMean (y k)) ^ 2) - popVar (y k))
      atTop (𝓝 0) := by
  classical
  have hN2 : ∀ k, 2 ≤ Fintype.card (U k) := fun k => (hn2 k).trans (hnle k)
  have hscale := sampleVariance_scale_tendsto n hnTop
  have hNTop : Tendsto (fun k => Fintype.card (U k)) atTop atTop :=
    tendsto_atTop_mono (fun k => hnle k) hnTop
  have hNR : Tendsto (fun k => (Fintype.card (U k) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_iff.mpr hNTop
  have hNinv : Tendsto (fun k => 1 / (Fintype.card (U k) : ℝ)) atTop (𝓝 0) := by
    convert tendsto_inv_atTop_zero.comp hNR using 1 <;> simp [Function.comp_def, one_div]
  have hpopMeanZ : ∀ k, popMean (fun i => (y k i - popMean (y k)) ^ 2) =
      (1 - 1 / (Fintype.card (U k) : ℝ)) * popVar (y k) := by
    intro k
    have hNRne : (Fintype.card (U k) : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    have hN1Rne : (Fintype.card (U k) : ℝ) - 1 ≠ 0 := by
      have : (2 : ℝ) ≤ (Fintype.card (U k) : ℝ) := by exact_mod_cast hN2 k
      linarith
    change (∑ i, (y k i - popMean (y k)) ^ 2) / (Fintype.card (U k) : ℝ) =
      (1 - 1 / (Fintype.card (U k) : ℝ)) *
        ((∑ i, (y k i - popMean (y k)) ^ 2) /
          ((Fintype.card (U k) : ℝ) - 1))
    field_simp
  simp_rw [hpopMeanZ]
  have hcoef : Tendsto (fun k =>
      ((n k : ℝ) / ((n k : ℝ) - 1)) *
        (1 - 1 / (Fintype.card (U k) : ℝ))) atTop (𝓝 1) := by
    simpa using hscale.mul (tendsto_const_nhds.sub hNinv)
  have hprod := hcoef.mul hvar
  simpa only [mul_assoc, one_mul, sub_self] using hprod.sub hvar

/-- **Absolute finite-population sample-variance consistency.** Along
[outcome vectors](hyp:y) and [growing simple random samples](hyp:hnTop) whose [sizes are between two and their population
sizes](hyp:hn2,hnle), suppose [the finite-population variances converge](hyp:hvar) and [the largest
squared centered outcome divided by the sample size vanishes](hyp:hmax). Then [the ordinary sample
variance converges in randomization probability to the finite-population variance](goal).

This is an absolute-consistency corollary under alternative assumptions.  It is not Li and Ding
(2017), Proposition 1, whose conclusion is ratio consistency under their central-limit condition.

The conclusion is derived from the exact sampling-without-replacement variance formula: the
sampled centered second moment is controlled by
`popMaxSqDev · popVar / n`, while the sampled centered first moment is controlled by the usual
finite-population mean variance. -/
theorem sampleVariance_tendstoInProb
    (n : ℕ → ℕ) (hn2 : ∀ k, 2 ≤ n k)
    (hnle : ∀ k, n k ≤ Fintype.card (U k))
    (y : ∀ k, U k → ℝ) (v : ℝ)
    (hnTop : Tendsto n atTop atTop)
    (hvar : Tendsto (fun k => popVar (y k)) atTop (𝓝 v))
    (hmax : Tendsto (fun k => popMaxSqDev (y k) / (n k : ℝ)) atTop (𝓝 0)) :
    FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k => sampleVariance (n k) (y k))
      (fun k => popVar (y k)) := by
  classical
  letI hsampleNonempty : ∀ k, Nonempty {S : Finset (U k) // S.card = n k} := fun k => by
    obtain ⟨S, _hsub, hS⟩ := Finset.exists_subset_card_eq
      (s := Finset.univ) (by simpa using hnle k)
    exact ⟨⟨S, hS⟩⟩
  have hn0 : ∀ k, 0 < n k := fun k => lt_of_lt_of_le (by norm_num) (hn2 k)
  have hz := centeredSq_sampleMean_tendstoInProb n hn2 hnle y v hvar hmax
  have hzCentered : FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k S => sampleMean (n k) (fun i => (y k i - popMean (y k)) ^ 2) S -
        popMean (fun i => (y k i - popMean (y k)) ^ 2)) (fun _ => 0) := by
    intro ε hε
    simpa using hz ε hε
  have hx := centered_sampleMean_tendstoInProb n hn2 hnle y v hnTop hvar
  have hxSq : FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k S => (sampleMean (n k) (fun i => y k i - popMean (y k)) S) ^ 2)
      (fun _ => 0) := by
    exact FiniteDesign.TendstoInProb.sq_zero hx
  have hscaleBdd : ∀ k, |(n k : ℝ) / ((n k : ℝ) - 1)| ≤ (2 : ℝ) := by
    intro k
    have hnR : (2 : ℝ) ≤ (n k : ℝ) := by exact_mod_cast hn2 k
    have hden : (0 : ℝ) < (n k : ℝ) - 1 := by linarith
    rw [abs_of_nonneg (div_nonneg (by positivity) hden.le)]
    rw [div_le_iff₀ hden]
    linarith
  have hzScaled := FiniteDesign.TendstoInProb.mul_deterministic_of_bounded
    (fun k => (n k : ℝ) / ((n k : ℝ) - 1)) 2 hscaleBdd hzCentered
  have hxScaled := FiniteDesign.TendstoInProb.mul_deterministic_of_bounded
    (fun k => (n k : ℝ) / ((n k : ℝ) - 1)) 2 hscaleBdd hxSq
  have hdet := scaled_popMean_centeredSq_sub_popVar_tendsto
    n hn2 hnle y v hnTop hvar
  have hdetProb := FiniteDesign.deterministic_tendstoInProb
    (fun k => completeRandomization (n k) (hnle k))
    (fun k => ((n k : ℝ) / ((n k : ℝ) - 1)) *
      popMean (fun i => (y k i - popMean (y k)) ^ 2) - popVar (y k)) 0 hdet
  have hsum : FiniteDesign.TendstoInProb
      (fun k => completeRandomization (n k) (hnle k))
      (fun k S => sampleVariance (n k) (y k) S - popVar (y k)) (fun _ => 0) := by
    convert (hzScaled.sub hxScaled).add hdetProb using 1
    · funext k S
      rw [sampleVariance_eq_centered (n k) (hn0 k) (y k) S]
      ring
    · funext k
      ring
  intro ε hε
  simpa using hsum ε hε

end SampleVarianceConsistency

end FinitePopulationMoments
end Experimentation
end Causalean
