/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

import Causalean.Stat.CLT.MartingaleArray.Basic
import Causalean.Stat.CLT.MartingaleArray.ConditionalTaylor

/-! # Conditional telescoping for finite martingale rows

This module turns the one-increment conditional Taylor formula into exact and
bounded telescoping formulas for a finite martingale-difference row.  It keeps
the random conditional variances visible; later stopping and blocking arguments
can therefore compare them with deterministic Gaussian time without assuming
independence.
-/

namespace Causalean.Stat

open Complex MeasureTheory ProbabilityTheory

variable {Ω : ℕ → Type*} {mΩ : (n : ℕ) → MeasurableSpace (Ω n)}
  {μ : (n : ℕ) → Measure (Ω n)}

namespace MartingaleDifferenceArray

/-- The partial row sum through time `r` adds the first `r` increments, capped
at the row length. -/
noncomputable def partialRowSum
    (A : MartingaleDifferenceArray Ω μ) (n r : ℕ) : Ω n → ℝ :=
  ∑ k ∈ Finset.range (min r (A.rowLength n)), A.increment n k

/-- For [a martingale-difference triangular array](hyp:A), [a row](hyp:n), and [a time
index](hyp:r), [the partial row sum is measurable with respect to that row's filtration at
that time](goal). -/
theorem partialRowSum_stronglyMeasurable
    (A : MartingaleDifferenceArray Ω μ) (n r : ℕ) :
    StronglyMeasurable[A.filtration n r] (A.partialRowSum n r) := by
  unfold partialRowSum
  apply Finset.stronglyMeasurable_sum
  intro k hk
  have hkmin : k < min r (A.rowLength n) := Finset.mem_range.mp hk
  exact (A.adapted n k (lt_of_lt_of_le hkmin (min_le_right _ _))).mono
    ((A.filtration n).mono (Nat.succ_le_of_lt (lt_of_lt_of_le hkmin (min_le_left _ _))))

/-- For [an active increment](hyp:hk), [the integral characteristic function
after that increment equals the preceding exponential weight times the exact
conditional quadratic expansion](goal). -/
theorem integral_cexp_partialRowSum_succ
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) (t : ℝ) :
    (∫ ω, Complex.exp (Complex.I *
        ((t * A.partialRowSum n (k + 1) ω : ℝ) : ℂ)) ∂(μ n)) =
      ∫ ω, Complex.exp (Complex.I *
          ((t * A.partialRowSum n k ω : ℝ) : ℂ)) *
        (1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
            (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
              A.filtration n k] ω : ℝ) : ℂ)) +
          (μ n)[(fun ω => expQuadraticRemainder
            (t * A.increment n k ω)) | A.filtration n k] ω) ∂(μ n) := by
  let f : Ω n → ℂ := fun ω =>
    Complex.exp (Complex.I * ((t * A.increment n k ω : ℝ) : ℂ))
  let g : Ω n → ℂ := fun ω =>
    Complex.exp (Complex.I * ((t * A.partialRowSum n k ω : ℝ) : ℂ))
  have hfMeas : AEStronglyMeasurable f (μ n) := by
    have hX := (A.squareIntegrable n k hk).aestronglyMeasurable
    dsimp [f]
    fun_prop
  have hf : Integrable f (μ n) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hfMeas ?_
    filter_upwards with ω
    dsimp [f]
    rw [Complex.norm_exp]
    simp
  have hg : StronglyMeasurable[A.filtration n k] g := by
    have hS := A.partialRowSum_stronglyMeasurable n k
    dsimp [g]
    fun_prop
  have hgBound : ∀ᵐ ω ∂(μ n), ‖g ω‖ ≤ 1 := by
    filter_upwards with ω
    dsimp [g]
    rw [Complex.norm_exp]
    simp
  have hpull : (μ n)[(fun ω => g ω * f ω) | A.filtration n k] =ᵐ[μ n]
      fun ω => g ω * (μ n)[f | A.filtration n k] ω := by
    convert condExp_stronglyMeasurable_bilin_of_bound
      (ContinuousLinearMap.mul ℝ ℂ) ((A.filtration n).le k) hg hf 1 hgBound using 1 <;>
      ext ω <;> rfl
  have htaylor : (μ n)[f | A.filtration n k] =ᵐ[μ n] fun ω =>
      1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
        (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
          A.filtration n k] ω : ℝ) : ℂ)) +
        (μ n)[(fun ω => expQuadraticRemainder
          (t * A.increment n k ω)) | A.filtration n k] ω := by
    let X := A.increment n k
    have hX2 := A.squareIntegrable n k hk
    have hX1 : Integrable X (μ n) := hX2.integrable (by norm_num)
    have hsq : Integrable (fun ω => X ω ^ 2) (μ n) := hX2.integrable_sq
    have hlin : Integrable (fun ω =>
        (Complex.I * (t : ℂ)) * (X ω : ℂ)) (μ n) :=
      hX1.ofReal.const_mul _
    have hquad : Integrable (fun ω =>
        ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) (μ n) :=
      hsq.ofReal.const_mul _
    have hrem : Integrable
        (fun ω => expQuadraticRemainder (t * X ω)) (μ n) := by
      apply (((hf.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).congr
      filter_upwards with ω
      dsimp [f, X]
      rw [expQuadraticRemainder]
      push_cast
      ring
    have hpoint : f = fun ω =>
        (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ) +
          expQuadraticRemainder (t * X ω) := by
      funext ω
      dsimp [f, X]
      rw [expQuadraticRemainder]
      push_cast
      ring
    rw [hpoint]
    have hconst : Integrable (fun _ : Ω n => (1 : ℂ)) (μ n) := integrable_const _
    have hbase : Integrable (fun ω =>
        (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) (μ n) :=
      (hconst.add hlin).sub hquad
    have hsplitCE : (μ n)[(fun ω =>
        (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ) +
          expQuadraticRemainder (t * X ω)) | A.filtration n k] =ᵐ[μ n]
        fun ω =>
          (μ n)[(fun ω => (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
            ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) |
              A.filtration n k] ω +
          (μ n)[(fun ω => expQuadraticRemainder (t * X ω)) |
            A.filtration n k] ω := by
      convert condExp_add hbase hrem (A.filtration n k) using 1 <;> ext ω <;> rfl
    have hsub : (μ n)[(fun ω =>
        (1 : ℂ) + (Complex.I * (t : ℂ)) * (X ω : ℂ) -
          ((t ^ 2 / 2 : ℝ) : ℂ) * ((X ω ^ 2 : ℝ) : ℂ)) |
            A.filtration n k] =ᵐ[μ n] fun ω =>
          (μ n)[(fun ω => (1 : ℂ) +
            (Complex.I * (t : ℂ)) * (X ω : ℂ)) | A.filtration n k] ω -
          (μ n)[(fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
            ((X ω ^ 2 : ℝ) : ℂ)) | A.filtration n k] ω := by
      convert condExp_sub (hconst.add hlin) hquad (A.filtration n k) using 1 <;>
        ext ω <;> rfl
    have hadd : (μ n)[(fun ω => (1 : ℂ) +
        (Complex.I * (t : ℂ)) * (X ω : ℂ)) | A.filtration n k] =ᵐ[μ n]
        fun ω => (μ n)[(fun _ : Ω n => (1 : ℂ)) | A.filtration n k] ω +
          (μ n)[(fun ω => (Complex.I * (t : ℂ)) * (X ω : ℂ)) |
            A.filtration n k] ω := by
      convert condExp_add hconst hlin (A.filtration n k) using 1 <;> ext ω <;> rfl
    have hXComplex : (μ n)[(fun ω => (X ω : ℂ)) | A.filtration n k] =ᵐ[μ n] 0 := by
      change (μ n)[Complex.ofRealCLM ∘ X | A.filtration n k] =ᵐ[μ n] 0
      calc
        (μ n)[Complex.ofRealCLM ∘ X | A.filtration n k] =ᵐ[μ n]
            Complex.ofRealCLM ∘ (μ n)[X | A.filtration n k] :=
          (Complex.ofRealCLM.comp_condExp_comm hX1).symm
        _ =ᵐ[μ n] 0 := (A.condExp_zero n k hk).mono (fun ω hω => by
          simp [Function.comp_apply, X, hω])
    have hlinZero : (μ n)[(fun ω =>
        (Complex.I * (t : ℂ)) * (X ω : ℂ)) | A.filtration n k] =ᵐ[μ n] 0 := by
      have hsmul : (μ n)[(fun ω =>
          (Complex.I * (t : ℂ)) * (X ω : ℂ)) | A.filtration n k] =ᵐ[μ n]
          fun ω => (Complex.I * (t : ℂ)) *
            (μ n)[(fun ω => (X ω : ℂ)) | A.filtration n k] ω := by
        convert condExp_smul (μ := μ n) (Complex.I * (t : ℂ))
          (fun ω => (X ω : ℂ)) (A.filtration n k) using 1 <;> ext ω <;> rfl
      filter_upwards [hsmul, hXComplex] with ω hsmulω hzeroω
      simpa only [Pi.zero_apply, mul_zero] using
        hsmulω.trans (congrArg ((Complex.I * (t : ℂ)) * ·) hzeroω)
    have hquadComm : (μ n)[(fun ω => ((X ω ^ 2 : ℝ) : ℂ)) |
        A.filtration n k] =ᵐ[μ n] fun ω =>
          (((μ n)[(fun ω => X ω ^ 2) | A.filtration n k] ω : ℝ) : ℂ) := by
      change (μ n)[Complex.ofRealCLM ∘ (fun ω => X ω ^ 2) |
        A.filtration n k] =ᵐ[μ n]
          Complex.ofRealCLM ∘ (μ n)[(fun ω => X ω ^ 2) | A.filtration n k]
      exact (Complex.ofRealCLM.comp_condExp_comm hsq).symm
    have hquadCE : (μ n)[(fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
        ((X ω ^ 2 : ℝ) : ℂ)) | A.filtration n k] =ᵐ[μ n] fun ω =>
          ((t ^ 2 / 2 : ℝ) : ℂ) *
            (μ n)[(fun ω => ((X ω ^ 2 : ℝ) : ℂ)) | A.filtration n k] ω := by
      convert condExp_smul (μ := μ n) ((t ^ 2 / 2 : ℝ) : ℂ)
        (fun ω => ((X ω ^ 2 : ℝ) : ℂ)) (A.filtration n k) using 1 <;>
        ext ω <;> rfl
    have hone := condExp_const (μ := μ n) ((A.filtration n).le k) (1 : ℂ)
    filter_upwards [hsplitCE, hsub, hadd, hlinZero, hquadCE, hquadComm]
      with ω hsplitω hsubω haddω hlinZeroω hquadCEω hquadCommω
    rw [hsplitω, hsubω, haddω, hlinZeroω, hquadCEω, hquadCommω]
    rw [congrFun hone ω]
    simp only [Pi.zero_apply, X]
    ring
  have hsplit : (fun ω => Complex.exp (Complex.I *
      ((t * A.partialRowSum n (k + 1) ω : ℝ) : ℂ))) =
      fun ω => g ω * f ω := by
    funext ω
    dsimp [g, f]
    unfold partialRowSum
    rw [Nat.min_eq_left (Nat.succ_le_of_lt hk)]
    rw [Nat.min_eq_left (le_trans (Nat.le_succ k) (Nat.succ_le_of_lt hk))]
    rw [Finset.sum_range_succ, ← Complex.exp_add]
    congr 1
    simp only [Pi.add_apply, Finset.sum_apply]
    push_cast
    ring
  rw [hsplit]
  calc
    (∫ ω, g ω * f ω ∂(μ n)) =
        ∫ ω, (μ n)[(fun ω => g ω * f ω) | A.filtration n k] ω ∂(μ n) := by
      rw [integral_condExp ((A.filtration n).le k)]
    _ = ∫ ω, g ω * (μ n)[f | A.filtration n k] ω ∂(μ n) :=
      integral_congr_ae hpull
    _ = ∫ ω, g ω *
        (1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
            (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
              A.filtration n k] ω : ℝ) : ℂ)) +
          (μ n)[(fun ω => expQuadraticRemainder
            (t * A.increment n k ω)) | A.filtration n k] ω) ∂(μ n) := by
      apply integral_congr_ae
      filter_upwards [htaylor] with ω hω
      exact congrArg (g ω * ·) hω
    _ = _ := rfl

/-- For [an active increment](hyp:hk), [the error in replacing its conditional
characteristic-function factor by the quadratic factor is bounded by the
expected norm of its Taylor remainder](goal). -/
theorem norm_integral_cexp_partialRowSum_succ_sub_quadratic_le
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n k : ℕ)
    (hk : k < A.rowLength n) (t : ℝ) :
    ‖(∫ ω, Complex.exp (Complex.I *
          ((t * A.partialRowSum n (k + 1) ω : ℝ) : ℂ)) ∂(μ n)) -
        ∫ ω, Complex.exp (Complex.I *
            ((t * A.partialRowSum n k ω : ℝ) : ℂ)) *
          (1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
            (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
              A.filtration n k] ω : ℝ) : ℂ))) ∂(μ n)‖ ≤
      ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n) := by
  let rem : Ω n → ℂ := fun ω =>
    expQuadraticRemainder (t * A.increment n k ω)
  let g : Ω n → ℂ := fun ω =>
    Complex.exp (Complex.I * ((t * A.partialRowSum n k ω : ℝ) : ℂ))
  let q : Ω n → ℂ := fun ω =>
    1 - (((t ^ 2 / 2 : ℝ) : ℂ) *
      (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
        A.filtration n k] ω : ℝ) : ℂ))
  have hX1 : Integrable (A.increment n k) (μ n) :=
    (A.squareIntegrable n k hk).integrable (by norm_num)
  have hX2 : Integrable (fun ω => (A.increment n k ω) ^ 2) (μ n) :=
    (A.squareIntegrable n k hk).integrable_sq
  have hexp : Integrable (fun ω => Complex.exp (Complex.I *
      ((t * A.increment n k ω : ℝ) : ℂ))) (μ n) := by
    have hmeas : AEStronglyMeasurable (fun ω => Complex.exp (Complex.I *
        ((t * A.increment n k ω : ℝ) : ℂ))) (μ n) := by
      have := hX1.aestronglyMeasurable
      fun_prop
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas ?_
    filter_upwards with ω
    rw [Complex.norm_exp]
    simp
  have hlin : Integrable (fun ω =>
      (Complex.I * (t : ℂ)) * (A.increment n k ω : ℂ)) (μ n) :=
    hX1.ofReal.const_mul _
  have hquad : Integrable (fun ω => ((t ^ 2 / 2 : ℝ) : ℂ) *
      (((A.increment n k ω) ^ 2 : ℝ) : ℂ)) (μ n) :=
    hX2.ofReal.const_mul _
  have hrem : Integrable rem (μ n) := by
    apply (((hexp.sub (integrable_const (1 : ℂ))).sub hlin).add hquad).congr
    filter_upwards with ω
    dsimp [rem]
    rw [expQuadraticRemainder]
    push_cast
    ring
  have hg : StronglyMeasurable[A.filtration n k] g := by
    have hS := A.partialRowSum_stronglyMeasurable n k
    dsimp [g]
    fun_prop
  have hgBound : ∀ᵐ ω ∂(μ n), ‖g ω‖ ≤ 1 := by
    filter_upwards with ω
    dsimp [g]
    rw [Complex.norm_exp]
    simp
  have hgAmbient : StronglyMeasurable g :=
    hg.mono ((A.filtration n).le k)
  have hq : Integrable q (μ n) := by
    have hce : Integrable
        ((μ n)[(fun ω => (A.increment n k ω) ^ 2) | A.filtration n k]) (μ n) :=
      integrable_condExp
    exact (integrable_const (1 : ℂ)).sub (hce.ofReal.const_mul _)
  have hgq : Integrable (fun ω => g ω * q ω) (μ n) :=
    hq.bdd_mul hgAmbient.aestronglyMeasurable hgBound
  have hceRem : Integrable ((μ n)[rem | A.filtration n k]) (μ n) :=
    integrable_condExp
  have hgceRem : Integrable
      (fun ω => g ω * (μ n)[rem | A.filtration n k] ω) (μ n) :=
    hceRem.bdd_mul hgAmbient.aestronglyMeasurable hgBound
  have hpull : (μ n)[(fun ω => g ω * rem ω) | A.filtration n k] =ᵐ[μ n]
      fun ω => g ω * (μ n)[rem | A.filtration n k] ω := by
    convert condExp_stronglyMeasurable_bilin_of_bound
      (ContinuousLinearMap.mul ℝ ℂ) ((A.filtration n).le k) hg hrem 1 hgBound using 1 <;>
      ext ω <;> rfl
  have hnorm : ‖∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)‖ ≤
      ∫ ω, ‖rem ω‖ ∂(μ n) := by
    have hgf : Integrable (fun ω => g ω * rem ω) (μ n) :=
      hrem.bdd_mul hgAmbient.aestronglyMeasurable hgBound
    calc
      ‖∫ ω, g ω * (μ n)[rem | A.filtration n k] ω ∂(μ n)‖ =
          ‖∫ ω, (μ n)[(fun ω => g ω * rem ω) | A.filtration n k] ω ∂(μ n)‖ := by
        rw [integral_congr_ae hpull]
      _ = ‖∫ ω, g ω * rem ω ∂(μ n)‖ := by
        rw [integral_condExp ((A.filtration n).le k)]
      _ ≤ ∫ ω, ‖g ω * rem ω‖ ∂(μ n) := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, ‖rem ω‖ ∂(μ n) := by
        apply integral_mono_ae hgf.norm hrem.norm
        filter_upwards [hgBound] with ω hω
        rw [norm_mul]
        simpa using mul_le_mul_of_nonneg_right hω (norm_nonneg (rem ω))
  rw [A.integral_cexp_partialRowSum_succ n k hk t]
  change ‖(∫ ω, g ω * (q ω + (μ n)[rem | A.filtration n k] ω) ∂(μ n)) -
      ∫ ω, g ω * q ω ∂(μ n)‖ ≤ ∫ ω, ‖rem ω‖ ∂(μ n)
  rw [show (fun ω => g ω * (q ω + (μ n)[rem | A.filtration n k] ω)) =
      fun ω => g ω * q ω + g ω * (μ n)[rem | A.filtration n k] ω by
        funext ω
        ring]
  rw [integral_add hgq hgceRem, add_sub_cancel_left]
  exact hnorm

/-- For [one finite martingale-difference row](hyp:A), [the error in its full
characteristic function after extracting all conditional quadratic terms is
bounded by the sum of the expected one-increment Taylor remainders](goal). -/
theorem norm_integral_cexp_rowSum_sub_quadraticTelescoping_le
    [∀ n, IsProbabilityMeasure (μ n)]
    (A : MartingaleDifferenceArray Ω μ) (n : ℕ) (t : ℝ) :
    ‖(∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) - 1 +
        ((t ^ 2 / 2 : ℝ) : ℂ) *
          (∑ k ∈ Finset.range (A.rowLength n),
            ∫ ω, Complex.exp (Complex.I *
                ((t * A.partialRowSum n k ω : ℝ) : ℂ)) *
              (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
                A.filtration n k] ω : ℝ) : ℂ) ∂(μ n))‖ ≤
      ∑ k ∈ Finset.range (A.rowLength n),
        ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n) := by
  let F : ℕ → ℂ := fun k => ∫ ω, Complex.exp (Complex.I *
    ((t * A.partialRowSum n k ω : ℝ) : ℂ)) ∂(μ n)
  let V : ℕ → ℂ := fun k => ∫ ω, Complex.exp (Complex.I *
    ((t * A.partialRowSum n k ω : ℝ) : ℂ)) *
      (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
        A.filtration n k] ω : ℝ) : ℂ) ∂(μ n)
  let R : ℕ → ℝ := fun k =>
    ∫ ω, ‖expQuadraticRemainder (t * A.increment n k ω)‖ ∂(μ n)
  let c : ℂ := ((t ^ 2 / 2 : ℝ) : ℂ)
  have hstep : ∀ k < A.rowLength n,
      ‖F (k + 1) - F k + c * V k‖ ≤ R k := by
    intro k hk
    let g : Ω n → ℂ := fun ω => Complex.exp (Complex.I *
      ((t * A.partialRowSum n k ω : ℝ) : ℂ))
    let v : Ω n → ℂ := fun ω =>
      (((μ n)[(fun ω => (A.increment n k ω) ^ 2) |
        A.filtration n k] ω : ℝ) : ℂ)
    have hgFil : StronglyMeasurable[A.filtration n k] g := by
      have hS := A.partialRowSum_stronglyMeasurable n k
      dsimp [g]
      fun_prop
    have hg : StronglyMeasurable g :=
      hgFil.mono ((A.filtration n).le k)
    have hgBound : ∀ᵐ ω ∂(μ n), ‖g ω‖ ≤ 1 := by
      filter_upwards with ω
      dsimp [g]
      rw [Complex.norm_exp]
      simp
    have hgInt : Integrable g (μ n) := by
      refine Integrable.mono' (integrable_const (1 : ℝ))
        hg.aestronglyMeasurable ?_
      exact hgBound
    have hv : Integrable v (μ n) := by
      have hce : Integrable
          ((μ n)[(fun ω => (A.increment n k ω) ^ 2) | A.filtration n k]) (μ n) :=
        integrable_condExp
      exact hce.ofReal
    have hgv : Integrable (fun ω => g ω * v ω) (μ n) :=
      hv.bdd_mul hg.aestronglyMeasurable hgBound
    have hrewrite : (∫ ω, g ω * (1 - c * v ω) ∂(μ n)) =
        F k - c * V k := by
      calc
        (∫ ω, g ω * (1 - c * v ω) ∂(μ n)) =
            ∫ ω, g ω - c * (g ω * v ω) ∂(μ n) := by
          apply integral_congr_ae
          filter_upwards with ω
          ring
        _ = (∫ ω, g ω ∂(μ n)) -
            ∫ ω, c * (g ω * v ω) ∂(μ n) :=
          integral_sub hgInt (hgv.const_mul c)
        _ = F k - c * V k := by
          rw [integral_const_mul]
    have h := A.norm_integral_cexp_partialRowSum_succ_sub_quadratic_le
      n k hk t
    change ‖F (k + 1) - (∫ ω, g ω * (1 - c * v ω) ∂(μ n))‖ ≤ R k at h
    rw [hrewrite] at h
    have heq : F (k + 1) - (F k - c * V k) =
        F (k + 1) - F k + c * V k := by ring
    rw [heq] at h
    exact h
  have hF0 : F 0 = 1 := by
    simp [F, partialRowSum]
  have hFlast : F (A.rowLength n) =
      ∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n) := by
    simp [F, partialRowSum, rowSum]
  have htel : (∑ k ∈ Finset.range (A.rowLength n),
      (F (k + 1) - F k + c * V k)) =
      (∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
        1 + c * (∑ k ∈ Finset.range (A.rowLength n), V k) := by
    rw [Finset.sum_add_distrib, Finset.sum_range_sub, ← Finset.mul_sum]
    rw [hF0, hFlast]
  change ‖(∫ ω, Complex.exp (Complex.I * ((t * A.rowSum n ω : ℝ) : ℂ)) ∂(μ n)) -
      1 + c * (∑ k ∈ Finset.range (A.rowLength n), V k)‖ ≤
    ∑ k ∈ Finset.range (A.rowLength n), R k
  rw [← htel]
  calc
    ‖∑ k ∈ Finset.range (A.rowLength n), (F (k + 1) - F k + c * V k)‖ ≤
        ∑ k ∈ Finset.range (A.rowLength n), ‖F (k + 1) - F k + c * V k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (A.rowLength n), R k := by
      apply Finset.sum_le_sum
      intro k hk
      exact hstep k (Finset.mem_range.mp hk)

end MartingaleDifferenceArray

end Causalean.Stat
