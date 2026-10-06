/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module

public import Causalean.Mathlib.Analysis.DifferentialComparison
public import Causalean.Stat.Concentration.EntropyMethod.Herbst
public import Causalean.Stat.Concentration.EntropyMethod.ModifiedLogSobolev

/-!
# Replacement self-bounding functions

This file connects the recursive replacement-square expression in the modified
logarithmic-Sobolev inequality to a pointwise replacement variance.  It then records the
entropy consequence of the standard weak self-bounding condition.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace Causalean.Stat.Concentration.EntropyMethod

universe u

/-- Given [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), and a statistic
`Z`, the [pointwise sum of conditional positive coordinate replacement
squares](goal) is [zero with no coordinates](step:1), while [at a positive number of coordinates
it integrates the head replacement square against a fresh head coordinate and adds the
tail-coordinate sum](step:2). -/
noncomputable def replacementSquareSum {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ((Fin n → X) → ℝ) → (Fin n → X) → ℝ
  | 0, _, _ => 0
  | n + 1, Z, s =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let p := e s
      (∫ y, (max (Z s - Z (e.symm (y, p.2))) 0) ^ 2 ∂μ 0) +
        replacementSquareSum (fun i => μ (i + 1)) n
          (fun tail => Z (e.symm (p.1, tail))) p.2

/-- Given [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), a tilt
`lam`, and a statistic `Z`, the [Fubini regularity conditions for replacement
squares](goal) recursively require integrability of the tilted head and tail replacement
contributions under the head--tail product law: [the zero-coordinate condition is
automatic](step:1), and [the positive-coordinate condition contains recursive tail regularity and
integrability of the tilted head and tail contributions](step:2). -/
def ReplacementSquareFubiniRegularity {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) :
    (n : ℕ) → ℝ → ((Fin n → X) → ℝ) → Prop
  | 0, _, _ => True
  | n + 1, lam, Z =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => X) 0
      let ν := Measure.pi (fun j : Fin n => μ (j.val + 1))
      (∀ x, ReplacementSquareFubiniRegularity (fun i => μ (i + 1)) n lam
        (fun tail => Z (e.symm (x, tail)))) ∧
      Integrable (fun p : X × (Fin n → X) =>
        Real.exp (lam * Z (e.symm p)) *
          (∫ y, (max (Z (e.symm p) - Z (e.symm (y, p.2))) 0) ^ 2 ∂μ 0))
        ((μ 0).prod ν) ∧
      Integrable (fun p : X × (Fin n → X) =>
        Real.exp (lam * Z (e.symm p)) *
          replacementSquareSum (fun i => μ (i + 1)) n
            (fun tail => Z (e.symm (p.1, tail))) p.2)
        ((μ 0).prod ν)

/-- Given [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), [a statistic
`Z`](hyp:Z), and [coefficients `a` and `b`](hyp:a,b), weak replacement self-bounding means that
[the sum of positive coordinate replacement squares is pointwise at most `a Z + b`](hyp:bound).

This is a custom independent-replacement analogue of the deletion-coordinate self-bounding
conditions in Boucheron--Lugosi--Massart (2013), not the condition of their Theorem 6.12.
Its analytic starting point is the symmetrized modified logarithmic-Sobolev inequality in
Theorem 6.15. For comparison, Theorem 6.19 assumes a nonnegative statistic and
nonnegative deletion functions, a squared deletion-increment bound, and `f_i ≤ f`; those
hypotheses are not supplied by `bound`. This file provides no bridge showing that the book's
configuration-function or VC-entropy examples satisfy `ReplacementSelfBounding`. The centered
empirical supremum is also not an example: a finite two-level counterexample shows that its
replacement-square sum cannot satisfy this field with universal constants, so users should not
attempt to discharge `bound` for that statistic. -/
structure ReplacementSelfBounding {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) (n : ℕ) (Z : (Fin n → X) → ℝ) (a b : ℝ) : Prop where
  bound : ∀ s, replacementSquareSum μ n Z s ≤ a * Z s + b

/-- For [coordinate laws `μ`](hyp:μ), [a coordinate count `n`](hyp:n), [a statistic
`Z`](hyp:Z), and [self-bounding coefficients `a,b`](hyp:a,b), cumulant-generating-function
regularity consists of [exponential integrability at every real tilt](hyp:exp_integrable),
[finite-product entropy regularity](hyp:tensorization), [modified logarithmic-Sobolev
regularity](hyp:modifiedLogSobolev), [replacement Fubini regularity](hyp:replacementFubini), and
[integrability of both sides of the tilted replacement
comparison](hyp:left_integrable,right_integrable)
at every positive tilt below the linear pole. -/
structure ReplacementSelfBoundingCGFRegularity {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) (n : ℕ) (Z : (Fin n → X) → ℝ) (a b : ℝ) : Prop where
  exp_integrable : ∀ t : ℝ, Integrable (fun s => Real.exp (t * Z s))
    (Measure.pi (fun i : Fin n => μ i.val))
  tensorization : ∀ t, 0 < t → a * t < 1 →
    FiniteTensorizationRegularity μ n (fun s => Real.exp (t * Z s))
  modifiedLogSobolev : ∀ t, 0 < t → a * t < 1 →
    ModifiedLogSobolevRegularity μ n t Z
  replacementFubini : ∀ t, 0 < t → a * t < 1 →
    ReplacementSquareFubiniRegularity μ n t Z
  left_integrable : ∀ t, 0 < t → a * t < 1 → Integrable (fun s =>
    Real.exp (t * Z s) * replacementSquareSum μ n Z s)
    (Measure.pi (fun i : Fin n => μ i.val))
  right_integrable : ∀ t, 0 < t → a * t < 1 → Integrable (fun s =>
    Real.exp (t * Z s) * (a * Z s + b))
    (Measure.pi (fun i : Fin n => μ i.val))

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the tilt is `lam`](hyp:lam), [the statistic is `Z`](hyp:Z), [the modified
logarithmic-Sobolev integrability conditions hold](hyp:hModified), and [the additional Fubini
conditions hold](hyp:hFubini), then [the recursive tilted replacement-square sum equals the
product expectation of the exponential tilt times the pointwise replacement-square sum](goal). -/
theorem exponentialReplacementSquareSum_eq_integral
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (lam : ℝ) (Z : (Fin n → X) → ℝ)
    (hModified : ModifiedLogSobolevRegularity μ n lam Z)
    (hFubini : ReplacementSquareFubiniRegularity μ n lam Z) :
    exponentialReplacementSquareSum μ n lam Z =
      ∫ s, Real.exp (lam * Z s) * replacementSquareSum μ n Z s
        ∂Measure.pi (fun i : Fin n => μ i.val) := by
  induction n generalizing μ with
  | zero =>
      simp [exponentialReplacementSquareSum, replacementSquareSum]
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
          n lam (fun tail => Z (e.symm (x, tail)))) (μ 0) at hModified
      rcases hModified with ⟨hhead, htailModified, _, _, _, _⟩
      change
        (∀ x, ReplacementSquareFubiniRegularity (fun i => μ (i + 1)) n lam
          (fun tail => Z (e.symm (x, tail)))) ∧
        Integrable (fun p : X × (Fin n → X) =>
          Real.exp (lam * Z (e.symm p)) *
            (∫ y, (max (Z (e.symm p) - Z (e.symm (y, p.2))) 0) ^ 2 ∂μ 0))
          ((μ 0).prod ν) ∧
        Integrable (fun p : X × (Fin n → X) =>
          Real.exp (lam * Z (e.symm p)) *
            replacementSquareSum (fun i => μ (i + 1)) n
              (fun tail => Z (e.symm (p.1, tail))) p.2)
          ((μ 0).prod ν) at hFubini
      rcases hFubini with ⟨htailFubini, hHeadInt, hTailInt⟩
      let headPart : X × (Fin n → X) → ℝ := fun p =>
        Real.exp (lam * Z (e.symm p)) *
          (∫ y, (max (Z (e.symm p) - Z (e.symm (y, p.2))) 0) ^ 2 ∂μ 0)
      let tailPart : X × (Fin n → X) → ℝ := fun p =>
        Real.exp (lam * Z (e.symm p)) *
          replacementSquareSum (fun i => μ (i + 1)) n
            (fun tail => Z (e.symm (p.1, tail))) p.2
      have hHead :
          (∫ tail, ∫ p : X × X,
            Real.exp (lam * Z (e.symm (p.1, tail))) *
              (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
            ∂(μ 0).prod (μ 0) ∂ν) =
          ∫ p, headPart p ∂((μ 0).prod ν) := by
        calc
          _ = ∫ tail, ∫ x,
              Real.exp (lam * Z (e.symm (x, tail))) *
                (∫ y, (max (Z (e.symm (x, tail)) - Z (e.symm (y, tail))) 0) ^ 2
                  ∂μ 0) ∂μ 0 ∂ν := by
                apply integral_congr_ae
                filter_upwards with tail
                rw [integral_prod _ (hhead tail).hplus]
                apply integral_congr_ae
                filter_upwards with x
                rw [← integral_const_mul]
          _ = ∫ p, headPart p ∂((μ 0).prod ν) := by
                simpa [headPart] using (integral_prod_symm headPart hHeadInt).symm
      have hTail :
          (∫ x, exponentialReplacementSquareSum (fun i => μ (i + 1)) n lam
            (fun tail => Z (e.symm (x, tail))) ∂μ 0) =
          ∫ p, tailPart p ∂((μ 0).prod ν) := by
        calc
          _ = ∫ x, ∫ tail,
              Real.exp (lam * Z (e.symm (x, tail))) *
                replacementSquareSum (fun i => μ (i + 1)) n
                  (fun tail' => Z (e.symm (x, tail'))) tail
              ∂ν ∂μ 0 := by
                apply integral_congr_ae
                filter_upwards with x
                exact ih (fun i => μ (i + 1))
                  (fun tail => Z (e.symm (x, tail)))
                  (htailModified x) (htailFubini x)
          _ = ∫ p, tailPart p ∂((μ 0).prod ν) := by
                simpa [tailPart] using (integral_prod tailPart hTailInt).symm
      have hsplit : MeasurePreserving e
          (Measure.pi (fun i : Fin (n + 1) => μ i.val)) ((μ 0).prod ν) := by
        simpa [e, ν] using
          (MeasureTheory.measurePreserving_piFinSuccAbove
            (μ := fun i : Fin (n + 1) => μ i.val) 0)
      have hProduct :
          (∫ p, headPart p + tailPart p ∂((μ 0).prod ν)) =
          ∫ s, Real.exp (lam * Z s) * replacementSquareSum μ (n + 1) Z s
            ∂Measure.pi (fun i : Fin (n + 1) => μ i.val) := by
        let G : X × (Fin n → X) → ℝ := fun p =>
          Real.exp (lam * Z (e.symm p)) *
            replacementSquareSum μ (n + 1) Z (e.symm p)
        have hcomp : G ∘ e = fun s =>
            Real.exp (lam * Z s) * replacementSquareSum μ (n + 1) Z s := by
          funext s
          dsimp [G]
          rw [e.symm_apply_apply]
        have htransport := hsplit.integral_comp' G
        have hpoint : G = fun p => headPart p + tailPart p := by
          funext p
          dsimp [G, headPart, tailPart, replacementSquareSum]
          rw [e.apply_symm_apply]
          ring
        calc
          (∫ p, headPart p + tailPart p ∂((μ 0).prod ν)) =
              ∫ p, G p ∂((μ 0).prod ν) := by
            apply integral_congr_ae
            exact ae_of_all _ (congrFun hpoint.symm)
          _ =
              ∫ s, G (e s) ∂Measure.pi (fun i : Fin (n + 1) => μ i.val) :=
            htransport.symm
          _ = ∫ s, Real.exp (lam * Z s) * replacementSquareSum μ (n + 1) Z s
                ∂Measure.pi (fun i : Fin (n + 1) => μ i.val) := by
            apply integral_congr_ae
            exact ae_of_all _ (congrFun hcomp)
      change
        (∫ tail, ∫ p : X × X,
          Real.exp (lam * Z (e.symm (p.1, tail))) *
            (max (Z (e.symm (p.1, tail)) - Z (e.symm (p.2, tail))) 0) ^ 2
          ∂(μ 0).prod (μ 0) ∂ν) +
        (∫ x, exponentialReplacementSquareSum (fun i => μ (i + 1)) n lam
          (fun tail => Z (e.symm (x, tail))) ∂μ 0) = _
      rw [hHead, hTail, ← integral_add hHeadInt hTailInt, hProduct]

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the tilt `lam` is
nonnegative](hyp:hlam), [the product has `n` coordinates](hyp:n), [the statistic is
`Z`](hyp:Z), [the self-bounding coefficients are `a` and `b`](hyp:a,b), [the tensorization and
replacement regularity conditions hold](hyp:hTensor,hModified),
[the replacement Fubini conditions hold](hyp:hFubini), [the statistic is weakly
self-bounding](hyp:hSelf), and [both tilted comparison integrands are
integrable](hyp:hLeftInt,hRightInt), then [the entropy of the exponential tilt is at most
`lam²` times the tilted expectation of `a Z + b`](goal). -/
theorem ReplacementSelfBounding.entropy_exp_le
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    {lam : ℝ} (hlam : 0 ≤ lam)
    (n : ℕ) (Z : (Fin n → X) → ℝ) {a b : ℝ}
    (hTensor : FiniteTensorizationRegularity μ n (fun x => Real.exp (lam * Z x)))
    (hModified : ModifiedLogSobolevRegularity μ n lam Z)
    (hFubini : ReplacementSquareFubiniRegularity μ n lam Z)
    (hSelf : ReplacementSelfBounding μ n Z a b)
    (hLeftInt : Integrable (fun s =>
      Real.exp (lam * Z s) * replacementSquareSum μ n Z s)
      (Measure.pi (fun i : Fin n => μ i.val)))
    (hRightInt : Integrable (fun s => Real.exp (lam * Z s) * (a * Z s + b))
      (Measure.pi (fun i : Fin n => μ i.val))) :
    entropy (Measure.pi (fun i : Fin n => μ i.val))
        (fun s => Real.exp (lam * Z s)) ≤
      lam ^ 2 * ∫ s, Real.exp (lam * Z s) * (a * Z s + b)
        ∂Measure.pi (fun i : Fin n => μ i.val) := by
  have hmlsi := modifiedLogSobolev_pi μ hlam n Z hTensor hModified
  rw [exponentialReplacementSquareSum_eq_integral μ n lam Z hModified hFubini] at hmlsi
  have hpoint :
      (fun s => Real.exp (lam * Z s) * replacementSquareSum μ n Z s) ≤ᵐ[
        Measure.pi (fun i : Fin n => μ i.val)]
      fun s => Real.exp (lam * Z s) * (a * Z s + b) := by
    filter_upwards with s
    exact mul_le_mul_of_nonneg_left (hSelf.bound s) (Real.exp_pos _).le
  have hint := integral_mono_ae hLeftInt hRightInt hpoint
  exact hmlsi.trans (mul_le_mul_of_nonneg_left hint (sq_nonneg lam))

private lemma integral_exp_mul_affine_eq_mgf_mul
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} {a b t : ℝ}
    (hExp : ∀ u : ℝ, Integrable (fun ω => Real.exp (u * Z ω)) μ) :
    (∫ s, Real.exp (t * Z s) * (a * Z s + b) ∂μ) =
      mgf Z μ t * (a * deriv (cgf Z μ) t + b) := by
  have hset : interior (integrableExpSet Z μ) = Set.univ := by
    rw [interior_eq_univ]
    ext u
    simpa [integrableExpSet] using hExp u
  have hmem : t ∈ interior (integrableExpSet Z μ) := by simp [hset]
  have hZexp : Integrable (fun s => Z s * Real.exp (t * Z s)) μ := by
    simpa using
      (integrable_pow_mul_exp_of_mem_interior_integrableExpSet hmem 1)
  have hrewrite :
      (∫ s, Real.exp (t * Z s) * (a * Z s + b) ∂μ) =
        a * (∫ s, Z s * Real.exp (t * Z s) ∂μ) +
          b * (∫ s, Real.exp (t * Z s) ∂μ) := by
    calc
      _ = ∫ s, a * (Z s * Real.exp (t * Z s)) +
          b * Real.exp (t * Z s) ∂μ := by
            apply integral_congr_ae
            filter_upwards with s
            ring
      _ = _ := by
        rw [integral_add (hZexp.const_mul a) ((hExp t).const_mul b)]
        rw [integral_const_mul, integral_const_mul]
  rw [hrewrite, deriv_cgf hmem]
  dsimp [mgf]
  have hMpos : 0 < ∫ s, Real.exp (t * Z s) ∂μ := mgf_pos (hExp t)
  field_simp [hMpos.ne']
  simp only [mul_comm]

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the statistic is `Z`](hyp:Z), [the self-bounding coefficients `a,b` are
nonnegative](hyp:ha,hb), [the statistic is weakly replacement self-bounding](hyp:hSelf), and
[the exponential-tilt regularity conditions hold](hyp:hReg), then at [a nonnegative tilt
`lam`](hyp:hlam0) [below the linear pole](hyp:hlam), [the centered cumulant-generating function is
at most `(a E[Z] + b) lam² / (1 - a lam)`](goal). -/
theorem ReplacementSelfBounding.cgf_centered_le
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (Z : (Fin n → X) → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSelf : ReplacementSelfBounding μ n Z a b)
    (hReg : ReplacementSelfBoundingCGFRegularity μ n Z a b)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : a * lam < 1) :
    cgf Z (Measure.pi (fun i : Fin n => μ i.val)) lam -
        lam * (∫ s, Z s ∂Measure.pi (fun i : Fin n => μ i.val)) ≤
      (a * (∫ s, Z s ∂Measure.pi (fun i : Fin n => μ i.val)) + b) * lam ^ 2 /
        (1 - a * lam) := by
  let ν : Measure (Fin n → X) := Measure.pi (fun i : Fin n => μ i.val)
  have hset : interior (integrableExpSet Z ν) = Set.univ := by
    rw [interior_eq_univ]
    ext t
    simpa [ν, integrableExpSet] using hReg.exp_integrable t
  have hdiff : Differentiable ℝ (cgf Z ν) := by
    intro t
    exact (analyticAt_cgf (by simp [hset])).differentiableAt
  have hderiv0 : deriv (cgf Z ν) 0 = ∫ s, Z s ∂ν := by
    simpa using deriv_cgf_zero (X := Z) (μ := ν) (by simp [hset])
  have hdifferential : ∀ t, 0 < t → a * t < 1 →
      t * (1 - a * t) * deriv (cgf Z ν) t - cgf Z ν t ≤ b * t ^ 2 := by
    intro t ht hta
    have hmem : t ∈ interior (integrableExpSet Z ν) := by simp [hset]
    have hMpos : 0 < mgf Z ν t := mgf_pos (by simpa [ν] using hReg.exp_integrable t)
    have hidentity :
        entropy ν (fun s => Real.exp (t * Z s)) =
          mgf Z ν t * (t * deriv (cgf Z ν) t - cgf Z ν t) := by
      rw [entropy]
      simp_rw [Real.log_exp]
      rw [show (∫ s, Real.exp (t * Z s) * (t * Z s) ∂ν) =
          t * ∫ s, Z s * Real.exp (t * Z s) ∂ν by
        rw [← integral_const_mul]
        congr with s
        ring]
      rw [show (∫ s, Real.exp (t * Z s) ∂ν) = mgf Z ν t by rfl]
      rw [deriv_cgf hmem]
      dsimp [cgf]
      field_simp [hMpos.ne']
    have hweighted :
        (∫ s, Real.exp (t * Z s) * (a * Z s + b) ∂ν) =
          mgf Z ν t * (a * deriv (cgf Z ν) t + b) := by
      exact integral_exp_mul_affine_eq_mgf_mul
        (by intro u; simpa [ν] using hReg.exp_integrable u)
    have hEnt := hSelf.entropy_exp_le μ ht.le n Z
      (hReg.tensorization t ht hta)
      (hReg.modifiedLogSobolev t ht hta)
      (hReg.replacementFubini t ht hta)
      (hReg.left_integrable t ht hta)
      (hReg.right_integrable t ht hta)
    change entropy ν (fun s => Real.exp (t * Z s)) ≤
      t ^ 2 * ∫ s, Real.exp (t * Z s) * (a * Z s + b) ∂ν at hEnt
    rw [hidentity, hweighted] at hEnt
    have hbase :
        t * deriv (cgf Z ν) t - cgf Z ν t ≤
          t ^ 2 * (a * deriv (cgf Z ν) t + b) := by
      apply (mul_le_mul_iff_of_pos_left hMpos).mp
      simpa [mul_assoc, mul_left_comm, mul_comm] using hEnt
    nlinarith
  have hcalc := Causalean.Mathlib.Analysis.centered_le_of_differential_inequality
    (hdiff 0) (fun t _ _ => hdiff t) cgf_zero ha hb hdifferential hlam0 hlam
  simpa [ν, hderiv0] using hcalc

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the statistic is `Z`](hyp:Z), [the self-bounding coefficients `a,b` are
nonnegative](hyp:ha,hb), [the statistic is weakly replacement self-bounding](hyp:hSelf), and
[the exponential-tilt regularity conditions hold](hyp:hReg), then at [a nonnegative tilt
`lam`](hyp:hlam0) [below the linear pole](hyp:hlam), [the centered moment-generating function is
at most the exponential of `(a E[Z] + b) lam² / (1 - a lam)`](goal). -/
theorem ReplacementSelfBounding.mgf_centered_le
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (Z : (Fin n → X) → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSelf : ReplacementSelfBounding μ n Z a b)
    (hReg : ReplacementSelfBoundingCGFRegularity μ n Z a b)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : a * lam < 1) :
    mgf (fun s => Z s - ∫ x, Z x ∂Measure.pi (fun i : Fin n => μ i.val))
        (Measure.pi (fun i : Fin n => μ i.val)) lam ≤
      Real.exp ((a * (∫ s, Z s ∂Measure.pi (fun i : Fin n => μ i.val)) + b) *
        lam ^ 2 / (1 - a * lam)) := by
  let ν : Measure (Fin n → X) := Measure.pi (fun i : Fin n => μ i.val)
  let m := ∫ s, Z s ∂ν
  have hcgf := hSelf.cgf_centered_le μ n Z ha hb hReg hlam0 hlam
  change mgf (fun s => Z s + -m) ν lam ≤
    Real.exp ((a * m + b) * lam ^ 2 / (1 - a * lam))
  rw [mgf_add_const, ← exp_cgf (by simpa [ν] using hReg.exp_integrable lam)]
  rw [← Real.exp_add, Real.exp_le_exp]
  dsimp [m, ν] at hcgf ⊢
  linarith

/-- If [the coordinate laws `μ` are probability laws](hyp:hprob), [the product has `n`
coordinates](hyp:n), [the statistic is `Z`](hyp:Z), [the self-bounding coefficients `a,b` are
nonnegative](hyp:ha,hb), [the statistic is weakly replacement self-bounding](hyp:hSelf), [the
exponential-tilt regularity conditions hold](hyp:hReg), and [the variance factor `a E[Z] + b` is
positive](hyp:hscale), then every [positive deviation `t`](hyp:ht) satisfies [the Bernstein upper
tail bound with exponent `-t² / (4(a E[Z] + b) + 2at)`](goal).

This is a custom independent-replacement consequence of the symmetrized modified
logarithmic-Sobolev machinery in Boucheron--Lugosi--Massart (2013), Theorem 6.15, not a
specialization of Theorem 6.12 or Theorem 6.19. Theorem 6.12 uses bounded linear
deletion-coordinate increments, while Theorem 6.19 uses a nonnegative statistic and
nonnegative deletion functions, a squared deletion-increment bound, and the additional
condition `f_i ≤ f`. Under its different hypotheses, the bound here has an exponent a factor of
two more conservative than Theorem 6.19. No conversion theorem in this file makes the book's
configuration-function or VC-entropy examples into applications of
`ReplacementSelfBounding.upper_tail`. In particular, the centered empirical supremum does not
satisfy `ReplacementSelfBounding.bound` with universal constants, as established by a finite
counterexample rather than by a missing proof. -/
theorem ReplacementSelfBounding.upper_tail
    {X : Type u} [MeasurableSpace X]
    (μ : ℕ → Measure X) [hprob : ∀ i, IsProbabilityMeasure (μ i)]
    (n : ℕ) (Z : (Fin n → X) → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hSelf : ReplacementSelfBounding μ n Z a b)
    (hReg : ReplacementSelfBoundingCGFRegularity μ n Z a b)
    (hscale : 0 < a * (∫ s, Z s ∂Measure.pi (fun i : Fin n => μ i.val)) + b)
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun i : Fin n => μ i.val)).real
        {s | t ≤ Z s - ∫ x, Z x ∂Measure.pi (fun i : Fin n => μ i.val)} ≤
      Real.exp (-t ^ 2 /
        (4 * (a * (∫ s, Z s ∂Measure.pi (fun i : Fin n => μ i.val)) + b) +
          2 * a * t)) := by
  let ν : Measure (Fin n → X) := Measure.pi (fun i : Fin n => μ i.val)
  let m := ∫ s, Z s ∂ν
  let c := a * m + b
  let lam := t / (2 * c + a * t)
  have hc : 0 < c := by simpa [c, m, ν] using hscale
  have hden : 0 < 2 * c + a * t := by positivity
  have hlam0 : 0 ≤ lam := (div_pos ht hden).le
  have hlam : a * lam < 1 := by
    rw [show lam = t / (2 * c + a * t) by rfl, ← mul_div_assoc]
    rw [div_lt_iff₀ hden]
    nlinarith
  have hint : Integrable (fun s => Real.exp (lam * (Z s - m))) ν := by
    have h := (hReg.exp_integrable lam).mul_const (Real.exp (-lam * m))
    change Integrable (fun s => Real.exp (lam * (Z s - m)))
      (Measure.pi (fun i : Fin n => μ i.val))
    convert h using 1
    funext s
    rw [← Real.exp_add]
    congr 1
    ring
  have hchernoff := measure_ge_le_exp_mul_mgf t hlam0 hint
  have hmgf : mgf (fun s => Z s - m) ν lam ≤
      Real.exp (c * lam ^ 2 / (1 - a * lam)) := by
    simpa [c, m, ν] using hSelf.mgf_centered_le μ n Z ha hb hReg hlam0 hlam
  calc
    ν.real {s | t ≤ Z s - m} ≤
        Real.exp (-lam * t) * mgf (fun s => Z s - m) ν lam := hchernoff
    _ ≤ Real.exp (-lam * t) * Real.exp (c * lam ^ 2 / (1 - a * lam)) :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = Real.exp (-t ^ 2 / (4 * c + 2 * a * t)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [lam]
      have hpole : 1 - a * (t / (2 * c + a * t)) ≠ 0 := ne_of_gt (sub_pos.mpr hlam)
      field_simp [hden.ne', hpole]
      ring

end Causalean.Stat.Concentration.EntropyMethod
