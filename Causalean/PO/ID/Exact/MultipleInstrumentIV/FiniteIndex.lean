/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan

# Ordered-score finite index algebra

Pure finite-support algebra for an arbitrary weakly increasing score. The
`MatrixScoreAdapter` converts supplied numeric matrix data into such a score.
It does not connect those data to observed treatment moments, so neither the
adapter nor an arbitrary `FiniteIndex` is by itself a population 2SLS first
stage, a saturated first stage, or a propensity score.

Background labels whose 2SLS interpretation requires the projected-score
condition above:

* `def:po-estimand-mtw-population-2sls`
* `def:po-estimand-mtw-tail-coefficients`
* `thm:po-estimand-mtw-signed-decomposition`
* `rem:po-estimand-mtw-lean-implementation`
-/

module
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Invertible
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Causalean.Stat.Weighted.NormalizedWeights

/-! # Multiple-Instrument IV Finite Index Algebra

This file develops finite algebra for an ordered support score. It defines
support masses, ordered scores, centered scores, tail coefficients, and a
numeric matrix score adapter. The adapter performs an inverse-Gram transform
but does not tie its inputs to observed random variables. Thus this file does
not assert the population-projection, saturated-first-stage, or
propensity-score conditions used by Mogstad, Torgovitsky, and Walters. -/

@[expose] public section

namespace Causalean
namespace PO.ID.Exact
namespace MultipleInstrumentIV

open Finset
open MeasureTheory

/-- [Adjacent thresholds](goal) are the positive positions in [a finite ordered instrument
support](hyp:K), each marking the boundary between consecutive support points. -/
abbrev Adj (K : ℕ) := {j : Fin K // 0 < j.val}

namespace Adj

/-- [The lower endpoint of an adjacent threshold](goal) is the support point immediately before
[that threshold](hyp:j) in [the finite ordered support](hyp:K). -/
def lower {K : ℕ} (j : Adj K) : Fin K :=
  ⟨j.1.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.1.isLt⟩

/-- [The upper endpoint of an adjacent threshold](goal) is [the threshold's own support
position](hyp:j) in [the finite ordered support](hyp:K). -/
def upper {K : ℕ} (j : Adj K) : Fin K :=
  j.1

end Adj

/-- A finite ordered-score index on [a finite instrument support](hyp:K) records
[instrument support masses](hyp:rho) that [are nonnegative](hyp:rho_nonneg) and [sum to
one](hyp:rho_sum_one), together with [a supplied real score](hyp:dhat) that [is weakly increasing
in the displayed support order](hyp:dhat_mono). -/
structure FiniteIndex (K : ℕ) where
  /-- Instrument support mass `ρ_k`. -/
  rho : Fin K → ℝ
  /-- Supplied ordered score `dhat_k`; no projection condition is part of this structure. -/
  dhat : Fin K → ℝ
  /-- Support masses are nonnegative. -/
  rho_nonneg : ∀ k, 0 ≤ rho k
  /-- Support masses sum to one. -/
  rho_sum_one : ∑ k, rho k = 1
  /-- The displayed support order is weakly increasing in the supplied score. -/
  dhat_mono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l

/-- [The probability mass at an instrument support point](goal) is the real-valued measure under
[the population law](hyp:μ) of units whose [finite-valued instrument](hyp:Z) equals [that
point](hyp:k), on [the measurable sample space and finite support](hyp:Ω,K). -/
noncomputable def supportMass {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Z : Ω → Fin K) (k : Fin K) : ℝ :=
  (μ {ω | Z ω = k}).toReal

/-- [Every instrument support mass is nonnegative](goal) for [a measurable sample space and
finite support](hyp:Ω,K), [population measure](hyp:μ), [finite-valued instrument](hyp:Z), and
[support point](hyp:k). -/
theorem supportMass_nonneg {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (Z : Ω → Fin K) (k : Fin K) :
    0 ≤ supportMass μ Z k := by
  exact ENNReal.toReal_nonneg

/-- [Instrument support masses sum to one](goal) under [a probability measure](hyp:μ), for [a
measurable finite-valued instrument](hyp:Z,hZ) on [the measurable sample space and finite
support](hyp:Ω,K). This makes the masses population weights. -/
theorem supportMass_sum_eq_one {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Fin K) (hZ : Measurable Z) :
    ∑ k : Fin K, supportMass μ Z k = 1 := by
  have hsum :
      (Finset.univ).sum
          (fun k : Fin K => (μ (Z ⁻¹' ({k} : Set (Fin K)))).toReal) =
        (μ (Z ⁻¹' (Set.univ : Set (Fin K)))).toReal := by
    simpa [Measure.real] using
      (MeasureTheory.sum_measureReal_preimage_singleton
        (μ := μ) (s := (Finset.univ : Finset (Fin K))) (f := Z)
        (hf := by
          intro k _hk
          exact hZ (measurableSet_singleton k))
        (h := by
          intro k _hk
          exact ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ _))
            (by simp [IsProbabilityMeasure.measure_univ])))
  have hpre : ∀ k : Fin K, ({ω | Z ω = k} : Set Ω) = Z ⁻¹' ({k} : Set (Fin K)) :=
    fun _ => rfl
  simpa [supportMass, hpre, Set.preimage_univ] using hsum

/-- [The measure-backed ordered score index](goal) combines [instrument-cell probabilities under
a population law](hyp:μ) with [a supplied support score](hyp:dhat) that is [weakly increasing
in support order](hyp:hdhat_mono), for [a measurable instrument](hyp:Z,hZ) on [the measurable
sample space and finite support](hyp:Ω,K). -/
noncomputable def FiniteIndex.fromMeasureScore {Ω : Type*} [MeasurableSpace Ω]
    {K : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Fin K) (hZ : Measurable Z)
    (dhat : Fin K → ℝ)
    (hdhat_mono : ∀ {k l : Fin K}, k.val ≤ l.val → dhat k ≤ dhat l) :
    FiniteIndex K where
  rho := supportMass μ Z
  dhat := dhat
  rho_nonneg := supportMass_nonneg μ Z
  rho_sum_one := supportMass_sum_eq_one μ Z hZ
  dhat_mono := hdhat_mono

namespace FiniteIndex

variable {K : ℕ} (I : FiniteIndex K)

/-- [The population mean score](goal) averages the supplied support score using the instrument
masses in [an ordered finite score index](hyp:I). -/
noncomputable def meanIndex : ℝ :=
  ∑ k, I.rho k * I.dhat k

/-- [The centered score at a support point](goal) subtracts the population mean score from [that
point's score](hyp:k) in [an ordered finite score index](hyp:I). -/
noncomputable def centeredIndex (k : Fin K) : ℝ :=
  I.dhat k - I.meanIndex

/-- [The upper-tail support set](goal) contains the points at or above [an adjacent
threshold](hyp:j) in [a finite ordered support](hyp:K). -/
noncomputable def upperTail (j : Adj K) : Finset (Fin K) :=
  Finset.univ.filter fun k => j.1.val ≤ k.val

/-- [The ordered-score tail coefficient](goal) is the covariance contribution above [an adjacent
threshold](hyp:j) in [an ordered finite score index](hyp:I): upper-tail masses times centered
scores. With a projected first-stage score, it is the MTW tail coefficient. -/
noncomputable def tailCoeff (j : Adj K) : ℝ :=
  ∑ k ∈ upperTail j, I.rho k * I.centeredIndex k

/-- [The support-mass-weighted centered score sums to zero](goal) for [an ordered finite score
index](hyp:I), which removes baseline components from centered-score moments.

This is the finite algebra behind subtracting the baseline term in
`thm:po-estimand-mtw-signed-decomposition`. -/
theorem centered_weight_sum_zero :
    ∑ k, I.rho k * I.centeredIndex k = 0 := by
  calc
    ∑ k, I.rho k * I.centeredIndex k =
        ∑ k, (I.rho k * I.dhat k - I.rho k * I.meanIndex) := by
      simp [centeredIndex, sub_eq_add_neg, mul_add]
    _ = ∑ k, I.rho k * I.dhat k - ∑ k, I.rho k * I.meanIndex := by
      rw [Finset.sum_sub_distrib]
    _ = I.meanIndex - I.meanIndex * ∑ k, I.rho k := by
      simp [meanIndex, Finset.sum_mul, mul_comm]
    _ = 0 := by
      simp [I.rho_sum_one]

/-- [Every ordered-score tail coefficient is nonnegative](goal) in [an ordered finite score
index](hyp:I) at [an adjacent threshold](hyp:j), because higher support points have weakly higher
scores. For a projected first stage, this is the MTW coefficient sign result. -/
theorem tailCoeff_nonneg (j : Adj K) :
    0 ≤ I.tailCoeff j := by
  classical
  let T := upperTail j
  let L : Finset (Fin K) := Finset.univ.filter fun l => l.val < j.1.val
  let A : ℝ := ∑ k ∈ T, I.rho k
  let B : ℝ := ∑ l ∈ L, I.rho l
  let ST : ℝ := ∑ k ∈ T, I.rho k * I.dhat k
  let SL : ℝ := ∑ l ∈ L, I.rho l * I.dhat l
  have hmass : B + A = 1 := by
    have h :=
      Finset.sum_filter_not_add_sum_filter
        (s := Finset.univ) (p := fun k : Fin K => j.1.val ≤ k.val) (f := I.rho)
    simpa [A, B, T, L, upperTail, Nat.not_le] using h.trans I.rho_sum_one
  have hmean : I.meanIndex = SL + ST := by
    have h :=
      Finset.sum_filter_not_add_sum_filter
        (s := Finset.univ) (p := fun k : Fin K => j.1.val ≤ k.val)
        (f := fun k => I.rho k * I.dhat k)
    simpa [ST, SL, T, L, upperTail, meanIndex, Nat.not_le] using h.symm
  have htail_basic : I.tailCoeff j = ST - A * I.meanIndex := by
    calc
      I.tailCoeff j =
          ∑ k ∈ T, (I.rho k * I.dhat k - I.rho k * I.meanIndex) := by
        simp [tailCoeff, centeredIndex, T, upperTail, mul_sub]
      _ = ST - ∑ k ∈ T, I.rho k * I.meanIndex := by
        rw [Finset.sum_sub_distrib]
      _ = ST - I.meanIndex * A := by
        simp [A, ST, Finset.mul_sum, mul_comm]
      _ = ST - A * I.meanIndex := by
        rw [mul_comm I.meanIndex A]
  have htail : I.tailCoeff j = B * ST - A * SL := by
    rw [htail_basic, hmean]
    have hB : B = 1 - A := by linarith
    rw [hB]
    ring
  have hfirst :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat k) = B * ST := by
    simp [B, ST, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]
  have hsecond :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat l) = A * SL := by
    rw [Finset.sum_comm]
    simp [A, SL, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm]
  have hdouble :
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * (I.dhat k - I.dhat l)) =
        B * ST - A * SL := by
    calc
      (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * (I.dhat k - I.dhat l)) =
          (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat k) -
            (∑ k ∈ T, ∑ l ∈ L, I.rho k * I.rho l * I.dhat l) := by
        simp [mul_sub, Finset.sum_sub_distrib]
      _ = B * ST - A * SL := by
        rw [hfirst, hsecond]
  rw [htail, ← hdouble]
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro l hl
  have hkT : j.1.val ≤ k.val := by
    simpa [T, upperTail] using hk
  have hlL : l.val < j.1.val := by
    simpa [L] using hl
  have hle : l.val ≤ k.val := by omega
  have hdhat : 0 ≤ I.dhat k - I.dhat l := sub_nonneg.mpr (I.dhat_mono hle)
  exact mul_nonneg (mul_nonneg (I.rho_nonneg k) (I.rho_nonneg l)) hdhat

/-- [A support-point sum of cumulative margin contributions equals the tail-coefficient-weighted
sum over margins](goal) for [an ordered finite score index](hyp:I) and [a margin contribution
schedule](hyp:x). This is the interchange that exposes signed causal-response weights. -/
theorem tail_sum_interchange (x : Adj K → ℝ) :
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ j : Adj K, if j.1.val ≤ k.val then x j else 0)) =
      ∑ j : Adj K, I.tailCoeff j * x j := by
  simp only [tailCoeff, upperTail]
  calc
    (∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ j : Adj K, if j.1.val ≤ k.val then x j else 0)) =
        ∑ k : Fin K, ∑ j : Adj K,
          if j.1.val ≤ k.val then (I.rho k * I.centeredIndex k) * x j else 0 := by
      simp [Finset.mul_sum, mul_ite, mul_zero, mul_assoc]
    _ = ∑ j : Adj K, ∑ k : Fin K,
          if j.1.val ≤ k.val then (I.rho k * I.centeredIndex k) * x j else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Adj K, x j * ∑ k : Fin K,
          if j.1.val ≤ k.val then I.rho k * I.centeredIndex k else 0 := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      by_cases h : j.1.val ≤ k.val
      · simp [h, mul_comm]
      · simp [h]
    _ = ∑ j : Adj K,
        (∑ k ∈ Finset.univ.filter fun k => j.1.val ≤ k.val,
          I.rho k * I.centeredIndex k) * x j := by
      simp [Finset.sum_filter, mul_comm]

/-- **Covariance identity.** For [an ordered finite score index](hyp:I) and [an adjacent
threshold](hyp:j), [the threshold's tail coefficient equals the finite-support covariance
between the instrument score and the indicator for assignment at or above that threshold](goal).

Formally, with `ind_k := if k ∈ upperTail j then (1 : ℝ) else 0` and
`mean_ind := Σ_l ρ_l * ind_l`,

    B_j = Σ_k ρ_k * (dhat_k − dbar) * (ind_k − mean_ind)
         = Cov_ρ(dhat, 1_{T_j}).

The centering of the indicator drops out because `Σ_k ρ_k * centeredIndex_k = 0`
(`centered_weight_sum_zero`). This identity bridges the tail-coefficient
algebra to score moments. It has the cited 2SLS meaning only when `dhat` is a
fitted first-stage value.

Source location: `def:po-estimand-mtw-tail-coefficients` (TeX:135–138). -/
theorem tailCoeff_eq_cov (j : Adj K) :
    I.tailCoeff j =
      ∑ k : Fin K,
        I.rho k * (I.dhat k - I.meanIndex) *
          ((if k ∈ upperTail j then (1 : ℝ) else 0) -
            ∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
  -- The subtracted cross-term is (Σ_k ρ_k centeredIndex_k) * (Σ_l ρ_l ind_l) = 0.
  have hcross :
      ∑ k : Fin K,
        I.rho k * I.centeredIndex k *
          (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
    have : (∑ k : Fin K, I.rho k * I.centeredIndex k) *
        (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
      rw [I.centered_weight_sum_zero]; ring
    calc ∑ k : Fin K,
          I.rho k * I.centeredIndex k *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0))
        = (∑ k : Fin K, I.rho k * I.centeredIndex k) *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
          rw [Finset.sum_mul]
      _ = 0 := this
  -- Rewrite the whole RHS directly and cancel cross-term.
  -- Let C := Σ_l ρ_l * ind_l (a constant w.r.t. k).
  -- RHS = Σ_k ρ_k*(dhat_k - mean)*(ind_k - C)
  --     = Σ_k ρ_k*centeredIndex_k*ind_k  -  C * Σ_k ρ_k*centeredIndex_k
  --     = Σ_k ρ_k*centeredIndex_k*ind_k  -  C * 0
  --     = Σ_{k∈T_j} ρ_k*centeredIndex_k  = tailCoeff j.
  have key : ∑ k : Fin K,
        I.rho k * (I.dhat k - I.meanIndex) *
          ((if k ∈ upperTail j then (1 : ℝ) else 0) -
            ∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) =
      ∑ k : Fin K,
          I.rho k * I.centeredIndex k * (if k ∈ upperTail j then (1 : ℝ) else 0) := by
    -- unfold centeredIndex so ring can see everything
    simp only [centeredIndex]
    have hcross2 :
        (∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex)) *
          (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) = 0 := by
      have : ∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex) = 0 := by
        have := I.centered_weight_sum_zero
        simp only [centeredIndex] at this; exact this
      rw [this]; ring
    calc ∑ k : Fin K,
          I.rho k * (I.dhat k - I.meanIndex) *
            ((if k ∈ upperTail j then (1 : ℝ) else 0) -
              ∑ l, I.rho l * (if l ∈ upperTail j then 1 else 0))
        = (∑ k : Fin K,
            I.rho k * (I.dhat k - I.meanIndex) * (if k ∈ upperTail j then (1 : ℝ) else 0)) -
          (∑ k : Fin K, I.rho k * (I.dhat k - I.meanIndex)) *
            (∑ l : Fin K, I.rho l * (if l ∈ upperTail j then (1 : ℝ) else 0)) := by
          rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
          congr 1; ext k; ring
      _ = ∑ k : Fin K,
            I.rho k * (I.dhat k - I.meanIndex) * (if k ∈ upperTail j then (1 : ℝ) else 0) := by
          rw [hcross2, sub_zero]
  rw [key]
  -- Now: Σ_k ρ_k*centeredIndex_k*indicator(k∈T_j) = Σ_{k∈T_j} ρ_k*centeredIndex_k = tailCoeff j
  simp only [tailCoeff, upperTail, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  split_ifs <;> ring

end FiniteIndex

/-! ### Numeric matrix score adapter -/

/-- [The weighted score Gram matrix](goal) is the mass-weighted second moment of [supplied score
vectors](hyp:score) under [supplied weights](hyp:rho), for [finite support and score
dimensions](hyp:K,L). -/
noncomputable def weightedScoreGram {K L : ℕ}
    (rho : Fin K → ℝ) (score : Fin K → Fin L → ℝ) :
    Matrix (Fin L) (Fin L) ℝ :=
  fun a b => ∑ k : Fin K, rho k * score k a * score k b

/-- A finite matrix score adapter, for [finite support and score dimensions](hyp:K,L),
stores [nonnegative support weights](hyp:rho,rho_nonneg) that [sum to one](hyp:rho_sum_one),
[support score vectors](hyp:score), and [a numeric moment vector](hyp:momentVector), together with
[an invertibility certificate](hyp:gram_invertible) and [monotonicity of the resulting
inverse-Gram score](hyp:adaptedScore_mono).

The stored moment vector is not linked to an observed treatment variable. This structure is
therefore numeric input for the ordered-score algebra, not by itself a population first stage or
a 2SLS construction. -/
structure MatrixScoreAdapter (K L : ℕ) where
  /-- Instrument support mass `ρ_k`. -/
  rho : Fin K → ℝ
  /-- Score vector `q(zᵏ)`. -/
  score : Fin K → Fin L → ℝ
  /-- Supplied numeric moment vector; no observed-moment equality is assumed. -/
  momentVector : Fin L → ℝ
  /-- Support masses are nonnegative. -/
  rho_nonneg : ∀ k, 0 ≤ rho k
  /-- Support masses sum to one. -/
  rho_sum_one : ∑ k, rho k = 1
  /-- The finite second-moment matrix is invertible. -/
  gram_invertible : Invertible (weightedScoreGram rho score)
  /-- The inverse-Gram transformed score is weakly increasing in the displayed support order. -/
  adaptedScore_mono :
    ∀ {k l : Fin K}, k.val ≤ l.val →
      (∑ a : Fin L,
          (∑ b : Fin L,
            (⅟(weightedScoreGram rho score)) a b *
              momentVector b) *
            score k a) ≤
        (∑ a : Fin L,
          (∑ b : Fin L,
            (⅟(weightedScoreGram rho score)) a b *
              momentVector b) *
            score l a)

namespace MatrixScoreAdapter

variable {K L : ℕ} (S : MatrixScoreAdapter K L)

/-- [The weighted score Gram matrix](goal) is the mass-weighted second moment specified by [a
finite matrix score adapter](hyp:S). -/
noncomputable def scoreGram : Matrix (Fin L) (Fin L) ℝ :=
  weightedScoreGram S.rho S.score

/-- [The weighted score Gram matrix is invertible](goal) for [a finite matrix score
adapter](hyp:S).

This is exactly the invertibility certificate stored by the adapter. -/
noncomputable instance instInvertibleScoreGram : Invertible S.scoreGram := by
  change Invertible (weightedScoreGram S.rho S.score)
  exact S.gram_invertible

/-- [An inverse-Gram transformed coefficient](goal) is the selected coordinate of the numeric
transformation specified by [a finite matrix score adapter](hyp:S), at [the selected score
coordinate](hyp:a). -/
noncomputable def transformedCoeff (a : Fin L) : ℝ :=
  ∑ b : Fin L, (⅟S.scoreGram) a b * S.momentVector b

/-- [The adapted score at a support point](goal) is the score--coefficient inner product in [a
finite matrix score adapter](hyp:S) at [that support point](hyp:k). -/
noncomputable def adaptedScore (k : Fin K) : ℝ :=
  ∑ a : Fin L, S.transformedCoeff a * S.score k a

/-- [The adapted ordered-score index](goal) retains the weights from [a finite matrix score
adapter](hyp:S) and uses its transformed values as the monotone score. Additional hypotheses are
needed to identify the supplied weights and moment vector with population treatment moments. -/
noncomputable def toFiniteIndex : FiniteIndex K where
  rho := S.rho
  dhat := S.adaptedScore
  rho_nonneg := S.rho_nonneg
  rho_sum_one := S.rho_sum_one
  dhat_mono := by
    intro k l hkl
    simp only [adaptedScore, transformedCoeff, scoreGram]
    exact S.adaptedScore_mono hkl

end MatrixScoreAdapter

end MultipleInstrumentIV
end PO.ID.Exact
end Causalean
