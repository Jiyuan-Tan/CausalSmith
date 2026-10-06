module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ContinuationBias
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitInterpolation
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.RiskEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpFirstOrderTaylor
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Explicit risk envelopes and first-order target regularity

The declared bias, variance, and extinction constants are finite formulas in
class constants. Sharp interpolation controls the first-order intensity and
hazard jets; the hazard equation then gives the survival and target-product
Hölder bounds with exactly the declared envelopes.
-/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

noncomputable def taylorRatio (c : ClassConstants) : ℝ :=
  if holderOrder c = 0 then 1 else
    Real.Gamma (c.beta - holderOrder c + 1) / Real.Gamma (c.beta + 1)

noncomputable def derivativeEnvelope (c : ClassConstants) (M L : ℝ) : ℝ :=
  if holderOrder c = 0 then M else
    interpolationInverseNorm (holderOrder c) *
      (M + taylorRatio c * L * (2 : ℝ) ^ (-c.beta))

noncomputable def derivativeHolderEnvelope (c : ClassConstants) (M L : ℝ)
    (j : ℕ) : ℝ :=
  if j < holderOrder c then derivativeEnvelope c M L else L

noncomputable def survivalDerivativeEnvelope (c : ClassConstants) : ℕ → ℝ
  | 0 => 1
  | j + 1 => ∑ r ∈ Finset.range (j + 1),
      (Nat.choose j r : ℝ) * derivativeEnvelope c c.dMax c.Ld *
        survivalDerivativeEnvelope c (j - r)

noncomputable def survivalHolderEnvelope (c : ClassConstants) (j : ℕ) : ℝ :=
  if j < holderOrder c then survivalDerivativeEnvelope c (j + 1)
  else if holderOrder c = 0 then c.dMax else
    ∑ r ∈ Finset.range (holderOrder c),
      (Nat.choose (holderOrder c - 1) r : ℝ) *
        (derivativeEnvelope c c.dMax c.Ld *
          survivalDerivativeEnvelope c (holderOrder c - r) +
          derivativeHolderEnvelope c c.dMax c.Ld r *
            survivalDerivativeEnvelope c (holderOrder c - 1 - r))

noncomputable def productHolderEnvelope (c : ClassConstants) : ℝ :=
  ∑ r ∈ Finset.range (holderOrder c + 1),
    (Nat.choose (holderOrder c) r : ℝ) *
      (survivalDerivativeEnvelope c r *
        derivativeHolderEnvelope c c.lambdaMax c.Llambda (holderOrder c - r) +
       survivalHolderEnvelope c r *
        derivativeEnvelope c c.lambdaMax c.Llambda)

noncomputable def explicitBiasEnvelope (c : ClassConstants) : ℝ :=
  taylorRatio c * productHolderEnvelope c *
    (continuationNorm c * ((2 : ℝ) ^ (c.beta + 1) - 1) /
      (c.beta + 1) + 1 / (c.beta + 1))

noncomputable def explicitBiasRisk (c : ClassConstants) : ℝ :=
  2 * (explicitBiasEnvelope c) ^ 2

noncomputable def explicitVarianceRisk (c : ClassConstants) : ℝ :=
  12 * reciprocalRetentionEnvelope c * (weightEnvelope c) ^ 2 / c.pMin *
    (c.lambdaMax * Real.exp c.dMax +
      c.lambdaMax ^ 2 * c.dMax * Real.exp (3 * c.dMax))

noncomputable def explicitExtinctionRisk (c : ClassConstants) : ℝ :=
  6 * (weightEnvelope c) ^ 2 * c.lambdaMax ^ 2 * Real.exp (2 * c.dMax)

noncomputable def extinctionExponent (c : ClassConstants) : ℝ :=
  c.pMin * c.gMin * Real.exp (-c.dMax) / 2

/-- At first order, the declared Gamma quotient is the sharp integral coefficient. -/
-- @node: taylorRatio_orderOne
lemma taylorRatio_orderOne (c : ClassConstants) (hone : holderOrder c = 1) :
    taylorRatio c = 1 / c.beta := by
  have hΓ : Real.Gamma c.beta ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos c.beta_pos)
  have hβ : c.beta ≠ 0 := c.beta_pos.ne'
  simp only [taylorRatio, hone, Nat.cast_one, one_ne_zero, ↓reduceIte,
    sub_add_cancel]
  rw [Real.Gamma_add_one hβ]
  field_simp

/-- The paper's first-order interpolation envelope bounds both within jets,
using its exact Gamma coefficient and the prescribed one-sided grid. -/
-- @node: derivativeEnvelope_orderOne_jet_bound
lemma derivativeEnvelope_orderOne_jet_bound (c : ClassConstants)
    (hone : holderOrder c = 1) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (1 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤ derivativeEnvelope c M L := by
  have hα := (holderOrder_remainder_exponent c).1
  rw [hone, Nat.cast_one] at hα
  have hβ : 1 < c.beta := by linarith
  have h := firstOrder_interpolation_jet_bound f hβ hM hL
    (by simpa only [hone, Nat.cast_one] using hf) hv hx j
  simpa only [derivativeEnvelope, hone, one_ne_zero, ↓reduceIte,
    taylorRatio_orderOne c hone, one_div, div_eq_mul_inv, one_mul, mul_comm L] using h

/-- The recurrence intensity jets obey the declared envelope at first order. -/
-- @node: recurrence_orderOne_jet_bound
lemma recurrence_orderOne_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (1 + 1)) :
    |iteratedDerivWithin j.val (P.lam a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.lambdaMax c.Llambda := by
  apply derivativeEnvelope_orderOne_jet_bound c hone (P.lam a)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
    (hP.recurrenceHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
  exact (hP.recurrenceBounds a t ht).2

/-- The death hazard jets obey the same declared envelope at first order. -/
-- @node: death_orderOne_jet_bound
lemma death_orderOne_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (1 + 1)) :
    |iteratedDerivWithin j.val (P.hazard a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.dMax c.Ld := by
  apply derivativeEnvelope_orderOne_jet_bound c hone (P.hazard a)
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
  exact (hP.deathBounds a t ht).2

/-- The declared jet envelope is nonnegative at first order. -/
-- @node: derivativeEnvelope_orderOne_nonneg
lemma derivativeEnvelope_orderOne_nonneg (c : ClassConstants)
    (hone : holderOrder c = 1) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ derivativeEnvelope c M L := by
  simp only [derivativeEnvelope, hone, one_ne_zero, ↓reduceIte,
    taylorRatio_orderOne c hone]
  have hInv : 0 ≤ interpolationInverseNorm 1 := by
    unfold interpolationInverseNorm
    positivity
  exact mul_nonneg hInv (add_nonneg hM
    (mul_nonneg (mul_nonneg (one_div_nonneg.mpr c.beta_pos.le) hL)
      (Real.rpow_nonneg (by norm_num) _)))

/-- Integrating the hazard gives a smooth survival function on the closed horizon. -/
-- @node: survival_orderOne_contDiffOn
lemma survival_orderOne_contDiffOn (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm) :
    ContDiffOn ℝ 1 (survival P a) (Icc (0 : ℝ) 1) := by
  have hd : ContDiffOn ℝ 0 (P.hazard a) (Icc (0 : ℝ) 1) :=
    (hP.deathHolder a).1.of_le (by simp [hone])
  unfold survival
  simpa only [Nat.cast_zero, zero_add] using
    (Causalean.Mathlib.Analysis.Calculus.HolderTaylor.interval_primitive_contDiffOn
      0 0 1 (by norm_num) (P.hazard a) (by simpa using hd)).neg.exp

/-- The survival derivative solves the hazard equation even at the horizon endpoints. -/
-- @node: survival_orderOne_derivWithin
lemma survival_orderOne_derivWithin (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    derivWithin (survival P a) (Icc (0 : ℝ) 1) t =
      -P.hazard a t * survival P a t := by
  have hd : ContDiffOn ℝ 0 (P.hazard a) (Icc (0 : ℝ) 1) :=
    (hP.deathHolder a).1.of_le (by simp [hone])
  unfold survival
  simpa only [Nat.cast_zero, zero_add] using
    Causalean.Mathlib.Analysis.Calculus.HolderTaylor.survival_derivWithin
      0 1 (by norm_num) (P.hazard a) (by simpa using hd) t (by simpa using ht)

/-- First-order survival jets obey exactly the declared finite recursion. -/
-- @node: survival_orderOne_jet_bound
lemma survival_orderOne_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (j : Fin (1 + 1)) :
    |iteratedDerivWithin j.val (survival P a) (Icc (0 : ℝ) 1) t| ≤
      survivalDerivativeEnvelope c j.val := by
  have hs : |survival P a t| ≤ 1 := by
    rw [abs_of_pos (show 0 < survival P a _ from Real.exp_pos _)]
    exact (survival_bounds_of_deathBounds c P hP.deathBounds a ht).2
  fin_cases j
  · simpa only [Fin.val_zero, iteratedDerivWithin_zero,
      survivalDerivativeEnvelope] using hs
  · have hd := death_orderOne_jet_bound c P hP hone a ht (0 : Fin (1 + 1))
    simp only [Fin.val_zero, iteratedDerivWithin_zero] at hd
    simp [iteratedDerivWithin_one, survivalDerivativeEnvelope]
    rw [survival_orderOne_derivWithin c P hP hone a ht, abs_mul, abs_neg]
    exact (mul_le_mul hd hs (abs_nonneg _) 
      (derivativeEnvelope_orderOne_nonneg c hone
        (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le)).trans_eq (mul_one _)

/-- The value increments of either hazard/intensity are controlled by their
next-jet envelope, with the paper's exponent and no extra length factor. -/
-- @node: derivativeEnvelope_orderOne_value_holder
lemma derivativeEnvelope_orderOne_value_holder (c : ClassConstants)
    (hone : holderOrder c = 1) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |f x - f y| ≤ derivativeEnvelope c M L * |x - y| ^ (c.beta - 1) := by
  have hα := holderOrder_remainder_exponent c
  simp only [hone, Nat.cast_one] at hα
  have h := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
    0 (c.beta - 1) 0 1 (derivativeEnvelope c M L) hα.1 hα.2
    (by norm_num) (derivativeEnvelope_orderOne_nonneg c hone hM hL) f
    (by simpa only [hone, Nat.cast_one, Nat.cast_zero, zero_add] using hf.1)
    (by
      intro t ht
      simpa using derivativeEnvelope_orderOne_jet_bound c hone f hM hL hf hv
        (by simpa using ht) (1 : Fin (1 + 1))) x (by simpa using hx) y (by simpa using hy)
  simpa only [iteratedDerivWithin_zero, zero_add, Real.one_rpow, mul_one] using h

/-- The survival value increments have the declared first-derivative envelope. -/
-- @node: survival_orderOne_value_holder
lemma survival_orderOne_value_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |survival P a x - survival P a y| ≤
      derivativeEnvelope c c.dMax c.Ld * |x - y| ^ (c.beta - 1) := by
  have hα := holderOrder_remainder_exponent c
  simp only [hone, Nat.cast_one] at hα
  have h := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
    0 (c.beta - 1) 0 1 (derivativeEnvelope c c.dMax c.Ld) hα.1 hα.2
    (by norm_num) (derivativeEnvelope_orderOne_nonneg c hone
      (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le) (survival P a)
    (by simpa using survival_orderOne_contDiffOn c P hP hone a)
    (by
      intro t ht
      simpa [survivalDerivativeEnvelope] using
        survival_orderOne_jet_bound c P hP hone a (by simpa using ht) (1 : Fin (1 + 1)))
    x (by simpa using hx) y (by simpa using hy)
  simpa only [iteratedDerivWithin_zero, zero_add, Real.one_rpow, mul_one] using h

/-- A product increment keeps separate value and increment envelopes. -/
-- @node: sharpProduct_increment_bound
lemma sharpProduct_increment_bound {u v u' v' A B C D q : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hu : |u'| ≤ A) (hv : |v| ≤ B)
    (hdu : |u - u'| ≤ C * q) (hdv : |v - v'| ≤ D * q) :
    |u * v - u' * v'| ≤ (C * B + A * D) * q := by
  calc
    _ = |(u - u') * v + u' * (v - v')| := by congr 1; ring
    _ ≤ |u - u'| * |v| + |u'| * |v - v'| := by
      simpa only [abs_mul] using abs_add_le ((u - u') * v) (u' * (v - v'))
    _ ≤ (C * q) * B + A * (D * q) :=
      add_le_add (mul_le_mul hdu hv (abs_nonneg _) (mul_nonneg hC hq))
        (mul_le_mul hu hdv (abs_nonneg _) hA)
    _ = _ := by ring

/-- The survival derivative has the precise first-order Hölder envelope
obtained by applying the product inequality to the hazard equation. -/
-- @node: survival_orderOne_derivative_holder
lemma survival_orderOne_derivative_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |derivWithin (survival P a) (Icc (0 : ℝ) 1) x -
      derivWithin (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c 1 * |x - y| ^ (c.beta - 1) := by
  have hD := derivativeEnvelope_orderOne_nonneg c hone
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.hazard a t| ≤ c.dMax := by
    intro t ht
    rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
    exact (hP.deathBounds a t ht).2
  have hdx := death_orderOne_jet_bound c P hP hone a hy (0 : Fin (1 + 1))
  simp only [Fin.val_zero, iteratedDerivWithin_zero] at hdx
  have hsx : |survival P a x| ≤ 1 := by
    rw [abs_of_pos (show 0 < survival P a _ from Real.exp_pos _)]
    exact (survival_bounds_of_deathBounds c P hP.deathBounds a hx).2
  have hh := sharpProduct_increment_bound hD (by norm_num : (0 : ℝ) ≤ 1) hD
    (Real.rpow_nonneg (abs_nonneg _) _) hdx hsx
    (derivativeEnvelope_orderOne_value_holder c hone (P.hazard a)
      (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le (hP.deathHolder a) hv hx hy)
    (survival_orderOne_value_holder c P hP hone a hx hy)
  rw [survival_orderOne_derivWithin c P hP hone a hx,
    survival_orderOne_derivWithin c P hP hone a hy,
    neg_mul, neg_mul, neg_sub_neg, abs_sub_comm]
  have he : survivalHolderEnvelope c 1 =
      derivativeEnvelope c c.dMax c.Ld + derivativeEnvelope c c.dMax c.Ld ^ 2 := by
    simp [survivalHolderEnvelope, hone, survivalDerivativeEnvelope,
      derivativeHolderEnvelope, pow_two]
    <;> ring
  rw [he]
  simpa only [mul_one, pow_two] using hh

/-- Leibniz's rule and the two factor moduli give the paper's explicit
first-order target-product Hölder envelope. -/
-- @node: survival_product_orderOne_holder
lemma survival_product_orderOne_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hone : holderOrder c = 1) (a : Arm) :
    HolderSeminormLe 1 (c.beta - 1) (productHolderEnvelope c)
      (fun t => survival P a t * P.lam a t) := by
  have hS := survival_orderOne_contDiffOn c P hP hone a
  have hLam : ContDiffOn ℝ 1 (P.lam a) (Icc (0 : ℝ) 1) := by
    simpa only [hone, Nat.cast_one] using (hP.recurrenceHolder a).1
  refine ⟨hS.mul hLam, ?_⟩
  intro x hx y hy
  let D := derivativeEnvelope c c.dMax c.Ld
  let R := derivativeEnvelope c c.lambdaMax c.Llambda
  have hD : 0 ≤ D := derivativeEnvelope_orderOne_nonneg c hone
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR : 0 ≤ R := derivativeEnvelope_orderOne_nonneg c hone
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.lam a t| ≤ c.lambdaMax := by
    intro t ht
    rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
    exact (hP.recurrenceBounds a t ht).2
  have hLamv := recurrence_orderOne_jet_bound c P hP hone a hx (0 : Fin (1 + 1))
  have hLamd := recurrence_orderOne_jet_bound c P hP hone a hx (1 : Fin (1 + 1))
  have hSv := survival_orderOne_jet_bound c P hP hone a hy (0 : Fin (1 + 1))
  have hSd := survival_orderOne_jet_bound c P hP hone a hy (1 : Fin (1 + 1))
  simp only [Fin.val_zero, iteratedDerivWithin_zero, survivalDerivativeEnvelope] at hLamv hSv
  simp only [Fin.val_one, iteratedDerivWithin_one] at hLamd
  have hSd' : |derivWithin (survival P a) (Icc (0 : ℝ) 1) y| ≤ D := by
    simpa [survivalDerivativeEnvelope, D] using hSd
  have hq : 0 ≤ |x - y| ^ (c.beta - 1) := Real.rpow_nonneg (abs_nonneg _) _
  have hmod := survival_orderOne_derivative_holder c P hP hone a hx hy
  have hH : 0 ≤ survivalHolderEnvelope c 1 := by
    have he : survivalHolderEnvelope c 1 = D + D ^ 2 := by
      simp [survivalHolderEnvelope, survivalDerivativeEnvelope,
        derivativeHolderEnvelope, hone, D, pow_two]
      <;> ring
    rw [he]
    positivity
  have hfirst := sharpProduct_increment_bound hD hR hH hq hSd' hLamv hmod
    (derivativeEnvelope_orderOne_value_holder c hone (P.lam a)
      (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
      (hP.recurrenceHolder a) hv hx hy)
  have hLammod : |derivWithin (P.lam a) (Icc (0 : ℝ) 1) x -
      derivWithin (P.lam a) (Icc (0 : ℝ) 1) y| ≤ c.Llambda * |x - y| ^ (c.beta - 1) := by
    simpa only [hone, Nat.cast_one, iteratedDerivWithin_one] using
      (hP.recurrenceHolder a).2 x hx y hy
  have hsecond := sharpProduct_increment_bound (by norm_num : (0 : ℝ) ≤ 1)
    hR hD hq hSv hLamd (survival_orderOne_value_holder c P hP hone a hx hy) hLammod
  simp only [iteratedDerivWithin_one]
  rw [derivWithin_fun_mul (hS.differentiableOn (by norm_num) x hx)
    (hLam.differentiableOn (by norm_num) x hx),
    derivWithin_fun_mul (hS.differentiableOn (by norm_num) y hy)
    (hLam.differentiableOn (by norm_num) y hy)]
  have he : productHolderEnvelope c =
      (survivalHolderEnvelope c 1 * R + D * R) + (D * R + 1 * c.Llambda) := by
    simp [productHolderEnvelope, hone, Finset.sum_range_succ, survivalDerivativeEnvelope,
      derivativeHolderEnvelope, survivalHolderEnvelope, D, R]
    ring
  rw [he]
  calc
    _ = |(derivWithin (survival P a) (Icc (0 : ℝ) 1) x * P.lam a x -
        derivWithin (survival P a) (Icc (0 : ℝ) 1) y * P.lam a y) +
        (survival P a x * derivWithin (P.lam a) (Icc (0 : ℝ) 1) x -
        survival P a y * derivWithin (P.lam a) (Icc (0 : ℝ) 1) y)| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
