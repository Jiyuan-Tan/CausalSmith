/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Stat.Concentration.EntropyMethod.FiniteTensorization
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Modified logarithmic-Sobolev inequality

This file proves the independent-replacement form of the modified logarithmic-Sobolev
inequality.  The one-coordinate estimate is obtained by symmetrizing the entropy against an
independent copy and applying the elementary exponential increment inequality.  Finite entropy
tensorization then sums this estimate over all coordinates.

The resulting Boucheron--Lugosi--Massart variant has constant `1` multiplying the positive-part
replacement square.  This is the independent-copy form, rather than the deletion-coordinate
form with constant `1 / 2`.
-/

@[expose] public section

open MeasureTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u

private lemma integral_le_log_integral_exp
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {g : X → ℝ} (hg : Integrable g μ)
    (hexp : Integrable (fun x => Real.exp (g x)) μ) :
    (∫ x, g x ∂μ) ≤ Real.log (∫ x, Real.exp (g x) ∂μ) := by
  let m := ∫ x, g x ∂μ
  have hcenter : Integrable (fun x => g x - m) μ := hg.sub (integrable_const m)
  have hcenterInt : (∫ x, g x - m ∂μ) = 0 := by
    rw [integral_sub hg (integrable_const m)]
    simp [m]
  have hcenterExp : Integrable (fun x => Real.exp (g x - m)) μ := by
    have h := hexp.const_mul (Real.exp (-m))
    convert h using 1
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hone : (1 : ℝ) ≤ ∫ x, Real.exp (g x - m) ∂μ := by
    have hleft : Integrable (fun x => 1 + (g x - m)) μ :=
      (integrable_const 1).add hcenter
    have hmono := integral_mono hleft hcenterExp
      (fun x => by simpa [add_comm] using Real.add_one_le_exp (g x - m))
    rw [integral_add (integrable_const 1) hcenter, integral_const, probReal_univ,
      one_smul, hcenterInt, add_zero] at hmono
    exact hmono
  have hfactor : (∫ x, Real.exp (g x - m) ∂μ) =
      Real.exp (-m) * ∫ x, Real.exp (g x) ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [← Real.exp_add]
    congr 1
    ring
  have hMpos : 0 < ∫ x, Real.exp (g x) ∂μ := integral_exp_pos hexp
  rw [hfactor] at hone
  have hexple : Real.exp m ≤ ∫ x, Real.exp (g x) ∂μ := by
    calc
      Real.exp m = Real.exp m * 1 := by ring
      _ ≤ Real.exp m * (Real.exp (-m) * ∫ x, Real.exp (g x) ∂μ) :=
        mul_le_mul_of_nonneg_left hone (Real.exp_pos m).le
      _ = ∫ x, Real.exp (g x) ∂μ := by
        rw [← mul_assoc, ← Real.exp_add]
        simp
  change m ≤ Real.log (∫ x, Real.exp (g x) ∂μ)
  exact (Real.le_log_iff_exp_le hMpos).2 hexple

private lemma exp_sub_mul_sub_le_posSq (a b : ℝ) :
    (Real.exp a - Real.exp b) * (a - b) ≤
      Real.exp a * (max (a - b) 0) ^ 2 +
        Real.exp b * (max (b - a) 0) ^ 2 := by
  rcases le_total b a with hba | hab
  · have hd : 0 ≤ a - b := sub_nonneg.mpr hba
    have hneg : b - a ≤ 0 := sub_nonpos.mpr hba
    rw [max_eq_left hd, max_eq_right hneg]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero]
    have hexprel : Real.exp b = Real.exp a * Real.exp (b - a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlin := Real.add_one_le_exp (b - a)
    rw [hexprel]
    have heapos : 0 < Real.exp a := Real.exp_pos a
    nlinarith [mul_nonneg heapos.le hd]
  · have hd : 0 ≤ b - a := sub_nonneg.mpr hab
    have hneg : a - b ≤ 0 := sub_nonpos.mpr hab
    rw [max_eq_right hneg, max_eq_left hd]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_add]
    have hexprel : Real.exp a = Real.exp b * Real.exp (a - b) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hlin := Real.add_one_le_exp (a - b)
    rw [hexprel]
    have hebpos : 0 < Real.exp b := Real.exp_pos b
    nlinarith [mul_nonneg hebpos.le hd]

/-- Given [a probability law `μ`](hyp:μ), [a real function `g`](hyp:g), [integrability of `g`,
its exponential, and their product](hyp:hg,hexp,hexpg), and [integrability of the exponentially
weighted positive replacement square](hyp:hplus), the [entropy of `exp g` is at most the expected
positive replacement square against an independent copy](goal). -/
theorem entropy_exp_le_replacement
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ)
    (hg : Integrable g μ)
    (hexp : Integrable (fun x => Real.exp (g x)) μ)
    (hexpg : Integrable (fun x => Real.exp (g x) * g x) μ)
    (hplus : Integrable (fun p : X × X =>
      Real.exp (g p.1) * (max (g p.1 - g p.2) 0) ^ 2) (μ.prod μ)) :
    entropy μ (fun x => Real.exp (g x)) ≤
      ∫ p : X × X, Real.exp (g p.1) * (max (g p.1 - g p.2) 0) ^ 2
        ∂(μ.prod μ) := by
  let M := ∫ x, Real.exp (g x) ∂μ
  let m := ∫ x, g x ∂μ
  have hJ := integral_le_log_integral_exp hg hexp
  have hMnonneg : 0 ≤ M := integral_nonneg fun x => (Real.exp_pos _).le
  have hent_le :
      entropy μ (fun x => Real.exp (g x)) ≤
        (∫ x, Real.exp (g x) * g x ∂μ) - M * m := by
    rw [entropy]
    simp_rw [Real.log_exp]
    dsimp [M, m] at hJ hMnonneg ⊢
    nlinarith [mul_le_mul_of_nonneg_left hJ hMnonneg]
  let A : X × X → ℝ := fun p => (Real.exp (g p.1) * g p.1) * 1
  let B : X × X → ℝ := fun p => Real.exp (g p.1) * g p.2
  let C : X × X → ℝ := fun p => g p.1 * Real.exp (g p.2)
  let D : X × X → ℝ := fun p => 1 * (Real.exp (g p.2) * g p.2)
  have hA : Integrable A (μ.prod μ) := hexpg.mul_prod (integrable_const 1)
  have hB : Integrable B (μ.prod μ) := hexp.mul_prod hg
  have hC : Integrable C (μ.prod μ) := hg.mul_prod hexp
  have hD : Integrable D (μ.prod μ) := (integrable_const 1).mul_prod hexpg
  let s : X × X → ℝ := fun p =>
    (Real.exp (g p.1) - Real.exp (g p.2)) * (g p.1 - g p.2)
  have hs : Integrable s (μ.prod μ) := by
    have heq : s = fun p => (A p - B p - C p) + D p := by
      funext p
      dsimp [s, A, B, C, D]
      ring
    rw [heq]
    exact ((hA.sub hB).sub hC).add hD
  have hsInt : (∫ p, s p ∂(μ.prod μ)) =
      2 * ((∫ x, Real.exp (g x) * g x ∂μ) - M * m) := by
    have hsub1 : (∫ p, A p - B p ∂(μ.prod μ)) =
        (∫ p, A p ∂(μ.prod μ)) - ∫ p, B p ∂(μ.prod μ) := by
      simpa only [Pi.sub_apply] using integral_sub hA hB
    have hsub2 : (∫ p, A p - B p - C p ∂(μ.prod μ)) =
        (∫ p, A p - B p ∂(μ.prod μ)) - ∫ p, C p ∂(μ.prod μ) := by
      simpa only [Pi.sub_apply] using integral_sub (hA.sub hB) hC
    have hAi : (∫ p, A p ∂(μ.prod μ)) =
        ∫ x, Real.exp (g x) * g x ∂μ := by
      simpa [A] using (integral_prod_mul (μ := μ) (ν := μ)
        (fun x => Real.exp (g x) * g x) (fun _ : X => (1 : ℝ)))
    have hBi : (∫ p, B p ∂(μ.prod μ)) =
        (∫ x, Real.exp (g x) ∂μ) * ∫ x, g x ∂μ := by
      simpa [B] using (integral_prod_mul (μ := μ) (ν := μ)
        (fun x => Real.exp (g x)) g)
    have hCi : (∫ p, C p ∂(μ.prod μ)) =
        (∫ x, g x ∂μ) * ∫ x, Real.exp (g x) ∂μ := by
      simpa [C] using (integral_prod_mul (μ := μ) (ν := μ)
        g (fun x => Real.exp (g x)))
    have hDi : (∫ p, D p ∂(μ.prod μ)) =
        ∫ x, Real.exp (g x) * g x ∂μ := by
      simpa [D] using (integral_prod_mul (μ := μ) (ν := μ)
        (fun _ : X => (1 : ℝ)) (fun x => Real.exp (g x) * g x))
    calc
      (∫ p, s p ∂(μ.prod μ)) =
          ∫ p, (A p - B p - C p) + D p ∂(μ.prod μ) := by
            apply integral_congr_ae
            filter_upwards with p
            dsimp [s, A, B, C, D]
            ring
      _ = (∫ p, A p - B p - C p ∂(μ.prod μ)) + ∫ p, D p ∂(μ.prod μ) :=
        integral_add ((hA.sub hB).sub hC) hD
      _ = ((∫ p, A p ∂(μ.prod μ)) - ∫ p, B p ∂(μ.prod μ)) -
          ∫ p, C p ∂(μ.prod μ) + ∫ p, D p ∂(μ.prod μ) := by
            rw [hsub2, hsub1]
      _ = 2 * ((∫ x, Real.exp (g x) * g x ∂μ) - M * m) := by
            rw [hAi, hBi, hCi, hDi]
            dsimp [M, m]
            ring
  let q : X × X → ℝ := fun p =>
    Real.exp (g p.1) * (max (g p.1 - g p.2) 0) ^ 2
  have hqswap : Integrable (fun p : X × X => q p.swap) (μ.prod μ) := by
    simpa [q, Function.comp_def] using hplus.swap
  have hsumInt : Integrable (fun p : X × X => q p + q p.swap) (μ.prod μ) :=
    hplus.add hqswap
  have hsymBound :
      (∫ p, s p ∂(μ.prod μ)) ≤ ∫ p, q p + q p.swap ∂(μ.prod μ) := by
    apply integral_mono hs hsumInt
    intro p
    exact exp_sub_mul_sub_le_posSq (g p.1) (g p.2)
  have hswap : (∫ p : X × X, q p.swap ∂(μ.prod μ)) =
      ∫ p : X × X, q p ∂(μ.prod μ) := integral_prod_swap q
  have hsum : (∫ p, q p + q p.swap ∂(μ.prod μ)) =
      2 * ∫ p, q p ∂(μ.prod μ) := by
    rw [integral_add hplus hqswap, hswap]
    ring
  rw [hsInt, hsum] at hsymBound
  exact hent_le.trans (by
    change (∫ x, Real.exp (g x) * g x ∂μ) - M * m ≤ ∫ p, q p ∂(μ.prod μ)
    linarith)

private lemma max_mul_sub_zero {a b lam : ℝ} (hlam : 0 ≤ lam) :
    max (lam * a - lam * b) 0 = lam * max (a - b) 0 := by
  rw [← mul_sub]
  rcases le_total a b with hab | hba
  · have hsub : a - b ≤ 0 := sub_nonpos.mpr hab
    rw [max_eq_right hsub, mul_zero]
    exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hlam hsub)
  · have hsub : 0 ≤ a - b := sub_nonneg.mpr hba
    rw [max_eq_left hsub]
    exact max_eq_left (mul_nonneg hlam hsub)

/-- Given [a probability law `μ`](hyp:μ), [a random variable `Z`](hyp:Z), [a nonnegative tilt
`lam`](hyp:hlam), [integrability of `Z`, its exponential tilt, and their
product](hyp:hZ,hexp,hexpZ),
and [integrability of the tilted positive replacement square](hyp:hplus), the [entropy of the
exponential tilt is bounded by `lam²` times the expected positive replacement square](goal). -/
theorem entropy_exp_mul_le_replacement
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (Z : X → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hZ : Integrable Z μ)
    (hexp : Integrable (fun x => Real.exp (lam * Z x)) μ)
    (hexpZ : Integrable (fun x => Real.exp (lam * Z x) * Z x) μ)
    (hplus : Integrable (fun p : X × X =>
      Real.exp (lam * Z p.1) * (max (Z p.1 - Z p.2) 0) ^ 2) (μ.prod μ)) :
    entropy μ (fun x => Real.exp (lam * Z x)) ≤
      lam ^ 2 * ∫ p : X × X,
        Real.exp (lam * Z p.1) * (max (Z p.1 - Z p.2) 0) ^ 2 ∂(μ.prod μ) := by
  let g : X → ℝ := fun x => lam * Z x
  have hg : Integrable g μ := hZ.const_mul lam
  have hexpg : Integrable (fun x => Real.exp (g x) * g x) μ := by
    have h := hexpZ.const_mul lam
    convert h using 1
    funext x
    dsimp [g]
    ring
  have hplusg : Integrable (fun p : X × X =>
      Real.exp (g p.1) * (max (g p.1 - g p.2) 0) ^ 2) (μ.prod μ) := by
    have h := hplus.const_mul (lam ^ 2)
    convert h using 1
    funext p
    dsimp [g]
    rw [max_mul_sub_zero hlam]
    ring
  have h := entropy_exp_le_replacement μ g hg (by simpa [g] using hexp) hexpg hplusg
  calc
    entropy μ (fun x => Real.exp (lam * Z x)) =
        entropy μ (fun x => Real.exp (g x)) := by rfl
    _ ≤ ∫ p : X × X,
        Real.exp (g p.1) * (max (g p.1 - g p.2) 0) ^ 2 ∂(μ.prod μ) := h
    _ = lam ^ 2 * ∫ p : X × X,
        Real.exp (lam * Z p.1) * (max (Z p.1 - Z p.2) 0) ^ 2 ∂(μ.prod μ) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with p
          dsimp [g]
          rw [max_mul_sub_zero hlam]
          ring

/-- For [a coordinate law `μ`](hyp:μ), [a tilt `lam`](hyp:lam), and [a random variable
`Z`](hyp:Z), the one-coordinate replacement conditions require [integrability of
`Z`](hyp:hZ), [integrability of the exponential tilt](hyp:hexp), [integrability of the tilted
product](hyp:hexpZ), and [integrability of the positive replacement square](hyp:hplus). -/
structure ReplacementEntropyIntegrable {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (lam : ℝ) (Z : X → ℝ) : Prop where
  hZ : Integrable Z μ
  hexp : Integrable (fun x => Real.exp (lam * Z x)) μ
  hexpZ : Integrable (fun x => Real.exp (lam * Z x) * Z x) μ
  hplus : Integrable (fun p : X × X =>
    Real.exp (lam * Z p.1) * (max (Z p.1 - Z p.2) 0) ^ 2) (μ.prod μ)

/-- Given [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), a tilt
`lam`, and a statistic `Z`, the [tilted sum of expected positive coordinate
replacement squares](goal) is [zero with no coordinates](step:1), while [at a positive number of
coordinates it adds the expected head replacement square and the recursively averaged tail
sum](step:2). -/
noncomputable def exponentialReplacementSquareSum {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ℝ → ((Fin n → X) → ℝ) → ℝ
  | 0, _, _ => 0
  | n + 1, lam, Z =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ν := Measure.pi (fun j : Fin n => μ (j.val + 1))
      (∫ tail, ∫ p : X × X,
        Real.exp (lam * Z (e.symm (p.1, tail))) *
          (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
        ∂(μ 0).prod (μ 0) ∂ν) +
      ∫ x, exponentialReplacementSquareSum (fun i => μ (i + 1)) n lam
        (fun tail => Z (e.symm (x, tail))) ∂μ 0

/-- Given [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), a tilt
`lam`, and a statistic `Z`, the [regularity conditions for the finite modified
logarithmic-Sobolev induction](goal) require the one-coordinate replacement conditions in every
head section, recursive tail conditions, and integrability of the four functions compared by the
two induction integrals: [the zero-coordinate condition is automatic](step:1), and [the
positive-coordinate condition contains the head and tail regularity plus the four integrability
clauses](step:2). -/
def ModifiedLogSobolevRegularity {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ℝ → ((Fin n → X) → ℝ) → Prop
  | 0, _, _ => True
  | n + 1, lam, Z =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ν := Measure.pi (fun j : Fin n => μ (j.val + 1))
      (∀ tail, ReplacementEntropyIntegrable (μ 0) lam
        (fun x => Z (e.symm (x, tail)))) ∧
      (∀ x, ModifiedLogSobolevRegularity (fun i => μ (i + 1)) n lam
        (fun tail => Z (e.symm (x, tail)))) ∧
      Integrable (fun tail => entropy (μ 0)
        (fun x => Real.exp (lam * Z (e.symm (x, tail))))) ν ∧
      Integrable (fun tail => ∫ p : X × X,
        Real.exp (lam * Z (e.symm (p.1, tail))) *
          (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
        ∂(μ 0).prod (μ 0)) ν ∧
      Integrable (fun x => coordinateEntropySum (fun i => μ (i + 1)) n
        (fun tail => Real.exp (lam * Z (e.symm (x, tail))))) (μ 0) ∧
      Integrable (fun x => exponentialReplacementSquareSum (fun i => μ (i + 1))
        n lam (fun tail => Z (e.symm (x, tail)))) (μ 0)

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the tilt `lam` is
nonnegative](hyp:hlam), [the product has `n` coordinates](hyp:n), [the statistic is
`Z`](hyp:Z), and [the replacement integrability conditions hold recursively](hyp:h), then [the
finite coordinate-entropy sum of the exponential tilt is at most `lam²` times the tilted sum of
expected positive coordinate replacement squares](goal). -/
theorem coordinateEntropySum_exp_le
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    {lam : ℝ} (hlam : 0 ≤ lam)
    (n : ℕ) (Z : (Fin n → X) → ℝ)
    (h : ModifiedLogSobolevRegularity μ n lam Z) :
    coordinateEntropySum μ n (fun x => Real.exp (lam * Z x)) ≤
      lam ^ 2 * exponentialReplacementSquareSum μ n lam Z := by
  induction n generalizing μ with
  | zero =>
      simp [coordinateEntropySum, exponentialReplacementSquareSum]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ν : Measure (Fin n → X) := Measure.pi (fun j : Fin n => μ (j.val + 1))
      change
        (∀ tail, ReplacementEntropyIntegrable (μ 0) lam
          (fun x => Z (e.symm (x, tail)))) ∧
        (∀ x, ModifiedLogSobolevRegularity (fun i => μ (i + 1)) n lam
          (fun tail => Z (e.symm (x, tail)))) ∧
        Integrable (fun tail => entropy (μ 0)
          (fun x => Real.exp (lam * Z (e.symm (x, tail))))) ν ∧
        Integrable (fun tail => ∫ p : X × X,
          Real.exp (lam * Z (e.symm (p.1, tail))) *
            (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
          ∂(μ 0).prod (μ 0)) ν ∧
        Integrable (fun x => coordinateEntropySum (fun i => μ (i + 1)) n
          (fun tail => Real.exp (lam * Z (e.symm (x, tail))))) (μ 0) ∧
        Integrable (fun x => exponentialReplacementSquareSum (fun i => μ (i + 1))
          n lam (fun tail => Z (e.symm (x, tail)))) (μ 0) at h
      rcases h with ⟨hhead, htail, hHeadEntInt, hHeadBoundInt,
        hTailEntInt, hTailBoundInt⟩
      let headBound : (Fin n → X) → ℝ := fun tail => ∫ p : X × X,
        Real.exp (lam * Z (e.symm (p.1, tail))) *
          (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
        ∂(μ 0).prod (μ 0)
      let tailEnt : X → ℝ := fun x =>
        coordinateEntropySum (fun i => μ (i + 1)) n
          (fun tail => Real.exp (lam * Z (e.symm (x, tail))))
      let tailBound : X → ℝ := fun x =>
        exponentialReplacementSquareSum (fun i => μ (i + 1)) n lam
          (fun tail => Z (e.symm (x, tail)))
      have hHeadPoint :
          (fun tail => entropy (μ 0)
            (fun x => Real.exp (lam * Z (e.symm (x, tail))))) ≤ᵐ[ν]
            fun tail => lam ^ 2 * headBound tail := by
        filter_upwards with tail
        exact entropy_exp_mul_le_replacement (μ 0)
          (fun x => Z (e.symm (x, tail))) hlam
          (hhead tail).hZ (hhead tail).hexp (hhead tail).hexpZ (hhead tail).hplus
      have hHeadIntegral :
          (∫ tail, entropy (μ 0)
            (fun x => Real.exp (lam * Z (e.symm (x, tail)))) ∂ν) ≤
          ∫ tail, lam ^ 2 * headBound tail ∂ν := by
        exact integral_mono_ae hHeadEntInt
          (hHeadBoundInt.const_mul (lam ^ 2)) hHeadPoint
      have hTailPoint : tailEnt ≤ᵐ[μ 0] fun x => lam ^ 2 * tailBound x := by
        filter_upwards with x
        exact ih (fun i => μ (i + 1)) (fun tail => Z (e.symm (x, tail))) (htail x)
      have hTailIntegral :
          (∫ x, tailEnt x ∂μ 0) ≤ ∫ x, lam ^ 2 * tailBound x ∂μ 0 := by
        exact integral_mono_ae hTailEntInt
          (hTailBoundInt.const_mul (lam ^ 2)) hTailPoint
      have hHeadScale : (∫ tail, lam ^ 2 * headBound tail ∂ν) =
          lam ^ 2 * ∫ tail, headBound tail ∂ν := by
        rw [integral_const_mul]
      have hTailScale : (∫ x, lam ^ 2 * tailBound x ∂μ 0) =
          lam ^ 2 * ∫ x, tailBound x ∂μ 0 := by
        rw [integral_const_mul]
      change
        (∫ tail, entropy (μ 0)
          (fun x => Real.exp (lam * Z (e.symm (x, tail)))) ∂ν) +
          (∫ x, tailEnt x ∂μ 0) ≤
        lam ^ 2 * ((∫ tail, headBound tail ∂ν) + ∫ x, tailBound x ∂μ 0)
      rw [hHeadScale] at hHeadIntegral
      rw [hTailScale] at hTailIntegral
      linarith

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the tilt `lam` is
nonnegative](hyp:hlam), [the product has `n` coordinates](hyp:n), [the statistic is
`Z`](hyp:Z), [finite entropy tensorization applies to its exponential tilt](hyp:hTensor), and [the
replacement integrability conditions hold recursively](hyp:hReplacement), then [the entropy of
the exponential tilt under the independent product law is at most `lam²` times the tilted sum of
expected positive coordinate replacement squares](goal). -/
theorem modifiedLogSobolev_pi
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    {lam : ℝ} (hlam : 0 ≤ lam)
    (n : ℕ) (Z : (Fin n → X) → ℝ)
    (hTensor : FiniteTensorizationRegularity μ n (fun x => Real.exp (lam * Z x)))
    (hReplacement : ModifiedLogSobolevRegularity μ n lam Z) :
    entropy (Measure.pi (fun i : Fin n => μ i.val))
        (fun x => Real.exp (lam * Z x)) ≤
      lam ^ 2 * exponentialReplacementSquareSum μ n lam Z :=
  (entropy_pi_le_coordinateEntropySum μ n _ hTensor).trans
    (coordinateEntropySum_exp_le μ hlam n Z hReplacement)

end Causalean.Stat.Concentration.EntropyMethod
