/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.ML.Lasso.OracleInequality
public import Causalean.Stat.Concentration.TailBounds.MaximalInequality

/-! # Sub-Gaussian score control for fixed-design Lasso

This module discharges the score-domination event used by the deterministic
Lasso oracle inequality.  Independent centered noise coordinates with common
sub-Gaussian proxy `σ²`, combined with design columns of squared norm at most
`n`, make every coordinate of `Xᵀw/n` sub-Gaussian with proxy `σ²/n`.

The finite-family maximal inequality then shows that
`λ = 2σ √(2 log(2p/δ)/n)` dominates twice the score infinity norm with
probability at least `1-δ`.
-/

public section

namespace Causalean.ML

open MeasureTheory ProbabilityTheory
open scoped NNReal

private lemma hasSubgaussianMGF_mono_parameter
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ} {c d : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) (hcd : c ≤ d) :
    HasSubgaussianMGF Z d μ where
  integrable_exp_mul := hZ.integrable_exp_mul
  mgf_le t := hZ.mgf_le t |>.trans <| Real.exp_le_exp.mpr <| by
    gcongr

private lemma hasSubgaussianMGF_to_subexponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ} {c : ℝ≥0}
    (hZ : HasSubgaussianMGF Z c μ) :
    Causalean.Stat.Concentration.HasSubexponentialMGF Z c 0 μ where
  integrable_exp_mul t _ := hZ.integrable_exp_mul t
  mgf_le t _ := hZ.mgf_le t

private lemma lassoScore_hasSubgaussianMGF
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → Ω → ℝ)
    (sigma : ℝ) (hn : 0 < n)
    (hindep : iIndepFun w μ)
    (hsubg : ∀ i, HasSubgaussianMGF (w i) ⟨sigma ^ 2, sq_nonneg sigma⟩ μ)
    (hcol : ∀ j, ∑ i, X i j ^ 2 ≤ (n : ℝ)) (j : Fin p) :
    HasSubgaussianMGF
      (fun ω => lassoScore X (fun i => w i ω) j)
      ⟨sigma ^ 2 / n, div_nonneg (sq_nonneg sigma) (Nat.cast_nonneg n)⟩ μ := by
  classical
  let a : Fin n → ℝ := fun i => (n : ℝ)⁻¹ * X i j
  let c : Fin n → ℝ≥0 := fun i => ⟨a i ^ 2, sq_nonneg (a i)⟩ *
    ⟨sigma ^ 2, sq_nonneg sigma⟩
  have hindep' : iIndepFun (fun i ω => a i * w i ω) μ :=
    hindep.comp (fun i x => a i * x) (fun _ => by fun_prop)
  have hscaled : ∀ i, HasSubgaussianMGF (fun ω => a i * w i ω) (c i) μ := by
    intro i
    exact (hsubg i).const_mul (a i)
  have hsum : HasSubgaussianMGF (fun ω => ∑ i, a i * w i ω) (∑ i, c i) μ := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hindep'
      (s := (Finset.univ : Finset (Fin n))) (fun i _ => hscaled i)
  have hc_le : (∑ i, c i) ≤
      ⟨sigma ^ 2 / n, div_nonneg (sq_nonneg sigma) (Nat.cast_nonneg n)⟩ := by
    apply (NNReal.coe_le_coe).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    dsimp [c, a]
    simp only [NNReal.coe_sum]
    have hscale : (∑ i, ((n : ℝ)⁻¹ * X i j) ^ 2) ≤ (n : ℝ)⁻¹ := by
      calc
        (∑ i, ((n : ℝ)⁻¹ * X i j) ^ 2) =
            (n : ℝ)⁻¹ ^ 2 * ∑ i, X i j ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ (n : ℝ)⁻¹ ^ 2 * n :=
          mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (n : ℝ)⁻¹)
        _ = (n : ℝ)⁻¹ := by field_simp
    calc
      (∑ i, ((n : ℝ)⁻¹ * X i j) ^ 2 * sigma ^ 2) =
          (∑ i, ((n : ℝ)⁻¹ * X i j) ^ 2) * sigma ^ 2 := by
        rw [Finset.sum_mul]
      _ ≤ (n : ℝ)⁻¹ * sigma ^ 2 :=
        mul_le_mul_of_nonneg_right hscale (sq_nonneg sigma)
      _ = sigma ^ 2 / n := by field_simp
  have hsum' := hasSubgaussianMGF_mono_parameter hsum hc_le
  refine hsum'.congr (ae_of_all _ fun ω => ?_)
  unfold lassoScore
  dsimp [a]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- **Sub-Gaussian Lasso score event.** Given [a probability measure](hyp:μ),
[positive sample and coefficient dimensions](hyp:hn,hp), [a fixed design
matrix](hyp:X), [measurable independent noise coordinates](hyp:hwmeas,hindep)
that are [sub-Gaussian with proxy `σ²`](hyp:hsubg), [a positive noise
scale](hyp:hsigma), [design columns with squared norm at most `n`](hyp:hcol),
and [a confidence level strictly between zero and one](hyp:hdelta,hdelta1),
[twice the score infinity norm is at most
`2σ√(2 log(2p/δ)/n)` with probability at least `1-δ`](goal).

This is the standard union-bound calibration for fixed-design Lasso. -/
theorem lasso_score_event_of_subgaussian
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (w : Fin n → Ω → ℝ)
    (sigma delta : ℝ)
    (hn : 0 < n) (hp : 0 < p)
    (hsigma : 0 < sigma)
    (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (hwmeas : ∀ i, Measurable (w i))
    (hindep : iIndepFun w μ)
    (hsubg : ∀ i, HasSubgaussianMGF (w i) ⟨sigma ^ 2, sq_nonneg sigma⟩ μ)
    (hcol : ∀ j, ∑ i, X i j ^ 2 ≤ (n : ℝ)) :
    μ.real {ω | 2 * lassoScoreSupNorm X (fun i => w i ω) ≤
        2 * sigma * Real.sqrt (2 * Real.log (2 * p / delta) / n)} ≥
      1 - delta := by
  classical
  let eps : ℝ := sigma * Real.sqrt (2 * Real.log (2 * p / delta) / n)
  let v : ℝ≥0 :=
    ⟨sigma ^ 2 / n, div_nonneg (sq_nonneg sigma) (Nat.cast_nonneg n)⟩
  let Y : Fin p → Ω → ℝ := fun j ω => lassoScore X (fun i => w i ω) j
  let _ : Nonempty (Fin p) := Fin.pos_iff_nonempty.mp hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hratio : 1 < 2 * (p : ℝ) / delta := by
    rw [lt_div_iff₀ hdelta]
    nlinarith
  have hlog : 0 < Real.log (2 * (p : ℝ) / delta) := Real.log_pos hratio
  have heps0 : 0 ≤ eps := mul_nonneg hsigma.le (Real.sqrt_nonneg _)
  have hY : ∀ j, HasSubgaussianMGF (Y j) v μ := by
    intro j
    exact lassoScore_hasSubgaussianMGF X w sigma hn hindep hsubg hcol j
  have hYexp : ∀ j ∈ (Finset.univ : Finset (Fin p)),
      Causalean.Stat.Concentration.HasSubexponentialMGF (Y j) v 0 μ := by
    intro j _
    exact hasSubgaussianMGF_to_subexponential (hY j)
  have htail := Causalean.Stat.Concentration.measure_sup'_ge_le
    (Finset.univ : Finset (Fin p)) Finset.univ_nonempty Y hYexp heps0
  have hvpos : 0 < (v : ℝ) := by
    change 0 < sigma ^ 2 / (n : ℝ)
    positivity
  have heps_sq : eps ^ 2 =
      sigma ^ 2 * (2 * Real.log (2 * (p : ℝ) / delta) / n) := by
    dsimp [eps]
    rw [mul_pow, Real.sq_sqrt]
    positivity
  have htail_delta :
      μ.real {ω | eps ≤ (Finset.univ : Finset (Fin p)).sup'
        Finset.univ_nonempty (fun j => |Y j ω|)} ≤ delta := by
    refine htail.trans_eq ?_
    simp only [Finset.card_univ, Fintype.card_fin, NNReal.coe_zero, zero_mul, add_zero]
    change (p : ℝ) * (2 * Real.exp (-eps ^ 2 /
      (2 * (sigma ^ 2 / (n : ℝ))))) = delta
    rw [heps_sq]
    have hden : 2 * (sigma ^ 2 / (n : ℝ)) ≠ 0 := by positivity
    have hexponent :
        -(sigma ^ 2 * (2 * Real.log (2 * (p : ℝ) / delta) / n)) /
            (2 * (sigma ^ 2 / n)) = -Real.log (2 * (p : ℝ) / delta) := by
      field_simp
    rw [hexponent, Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  have hsup_eq : ∀ ω,
      lassoScoreSupNorm X (fun i => w i ω) =
        (Finset.univ : Finset (Fin p)).sup' Finset.univ_nonempty
          (fun j => |Y j ω|) := by
    intro ω
    unfold lassoScoreSupNorm
    have hnn : (Finset.univ : Finset (Fin p)).sup
        (fun j => ‖lassoScore X (fun i => w i ω) j‖₊) =
      (Finset.univ : Finset (Fin p)).sup'
        Finset.univ_nonempty (fun j => ‖lassoScore X (fun i => w i ω) j‖₊) := by
      exact (Finset.sup'_eq_sup Finset.univ_nonempty _).symm
    rw [hnn]
    apply le_antisymm
    · have hreal0 : 0 ≤ (Finset.univ : Finset (Fin p)).sup'
          Finset.univ_nonempty (fun j => |Y j ω|) := by
        obtain ⟨j⟩ := Fin.pos_iff_nonempty.mp hp
        exact (abs_nonneg (Y j ω)).trans
          (Finset.le_sup' (fun k => |Y k ω|) (Finset.mem_univ j))
      let R : ℝ≥0 := ⟨(Finset.univ : Finset (Fin p)).sup'
        Finset.univ_nonempty (fun j => |Y j ω|), hreal0⟩
      have hle : (Finset.univ : Finset (Fin p)).sup'
          Finset.univ_nonempty
            (fun j => ‖lassoScore X (fun i => w i ω) j‖₊) ≤ R := by
        apply Finset.sup'_le
        intro j hj
        apply (NNReal.coe_le_coe).1
        change |Y j ω| ≤ (Finset.univ : Finset (Fin p)).sup'
          Finset.univ_nonempty (fun k => |Y k ω|)
        exact Finset.le_sup' (fun k => |Y k ω|) hj
      exact_mod_cast hle
    · apply Finset.sup'_le
      intro j hj
      change |Y j ω| ≤ ↑((Finset.univ : Finset (Fin p)).sup'
        Finset.univ_nonempty
          (fun k => ‖lassoScore X (fun i => w i ω) k‖₊))
      exact_mod_cast Finset.le_sup'
        (fun k => ‖lassoScore X (fun i => w i ω) k‖₊) hj
  let good : Set Ω := {ω | 2 * lassoScoreSupNorm X (fun i => w i ω) ≤ 2 * eps}
  have hgood_meas : MeasurableSet good := by
    have hYmeas : ∀ j, Measurable (Y j) := by
      intro j
      unfold Y lassoScore
      fun_prop
    have hsupmeas : Measurable (fun ω =>
        (Finset.univ : Finset (Fin p)).sup' Finset.univ_nonempty
          (fun j => |Y j ω|)) := by
      fun_prop
    have hscoremeas : Measurable (fun ω => lassoScoreSupNorm X (fun i => w i ω)) := by
      simpa only [hsup_eq] using hsupmeas
    exact measurableSet_le (measurable_const.mul hscoremeas)
      (measurable_const.mul measurable_const)
  have hbad_subset : goodᶜ ⊆
      {ω | eps ≤ (Finset.univ : Finset (Fin p)).sup'
        Finset.univ_nonempty (fun j => |Y j ω|)} := by
    intro ω hω
    simp only [good, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω
    change eps ≤ (Finset.univ : Finset (Fin p)).sup'
      Finset.univ_nonempty (fun j => |Y j ω|)
    rw [← hsup_eq ω]
    linarith
  have hbad : μ.real goodᶜ ≤ delta :=
    (measureReal_mono hbad_subset).trans htail_delta
  have hgood : μ.real good ≥ 1 - delta := by
    rw [measureReal_compl hgood_meas, probReal_univ] at hbad
    linarith
  simpa only [good, eps, mul_assoc] using hgood

end Causalean.ML
