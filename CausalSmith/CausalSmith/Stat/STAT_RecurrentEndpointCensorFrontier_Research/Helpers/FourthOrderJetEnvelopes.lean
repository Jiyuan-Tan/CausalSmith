module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpFourthOrderTaylor

/-! # Quartic interpolation and jet envelopes

The five-point one-sided solve converts sharp fourth-order Taylor remainders
into the declared derivative envelopes.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The five-point one-sided interpolation solve bounds all fourth-order
jets with the sharp Taylor coefficient and the declared finite inverse norm. -/
-- @node: fourthOrder_interpolation_jet_bound
lemma fourthOrder_interpolation_jet_bound (f : ℝ → ℝ) {β M L : ℝ}
    (hβ : 4 < β) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe 4 (β - 4) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (4 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤
      interpolationInverseNorm 4 *
        (M + L / ((β - 3) * (β - 2) * (β - 1) * β) * (2 : ℝ) ^ (-β)) := by
  let v : Fin (4 + 1) → ℝ := fun j => iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x
  let R := L / ((β - 3) * (β - 2) * (β - 1) * β) * (2 : ℝ) ^ (-β)
  have hβ0 : 0 < β := by linarith
  have hβ1 : 0 < β - 1 := by linarith
  have hβ3 : 0 < β - 3 := by linarith
  have hβ2 : 0 < β - 2 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hα : 0 < β - 4 := by linarith
  have hpow : (1 / 2 : ℝ) ^ β = (2 : ℝ) ^ (-β) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have hr {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htx : |t - x| ≤ 1 / 2) :
      |f t - f x - derivWithin f (Icc (0 : ℝ) 1) x * (t - x) -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (t - x) ^ 2 / 2 -
        iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * (t - x) ^ 3 / 6 -
          iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * (t - x) ^ 4 / 24| ≤ R := by
    have hb := fourthOrder_remainder_bound f hα hf hx ht
    rw [show β - 4 + 1 = β - 3 by ring, show β - 4 + 2 = β - 2 by ring, show β - 4 + 3 = β - 1 by ring, show β - 4 + 4 = β by ring] at hb
    refine hb.trans ?_
    dsimp [R]
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) htx (by linarith))
      (div_nonneg hL (mul_nonneg (mul_nonneg (mul_nonneg hβ3.le hβ2.le) hβ1.le) hβ0.le))
  have hcalc (r : Fin (4 + 1)) :
      (interpolationMatrix 4).mulVec v r =
        f x + derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) +
          iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 2 / 2 +
          iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 3 / 6 +
          iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 4 / 24 := by
    simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
      iteratedDerivWithin_one]
    <;> ring
  by_cases hleft : x ≤ 1 / 2
  · let y : Fin (4 + 1) → ℝ := fun r => f (x + (r.val : ℝ) / 8)
    have ht (r : Fin (4 + 1)) : x + (r.val : ℝ) / 8 ∈ Icc (0 : ℝ) 1 := by
      have hr2 : (r.val : ℝ) ≤ 4 := by exact_mod_cast (show r.val ≤ 4 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.1]
    apply interpolationMatrix_jet_bound_of_remainder 4 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    rw [hcalc]
    have hr2 : (r.val : ℝ) ≤ 4 := by exact_mod_cast (show r.val ≤ 4 by omega)
    have hd : |x + (r.val : ℝ) / 8 - x| ≤ 1 / 2 := by
      rw [show x + (r.val : ℝ) / 8 - x = (r.val : ℝ) / 8 by ring,
        abs_of_nonneg (by positivity)]
      linarith
    simpa only [y, show x + (r.val : ℝ) / 8 - x = (r.val : ℝ) / 8 by ring,
      sub_add_eq_sub_sub] using hr (ht r) hd
  · let y : Fin (4 + 1) → ℝ := fun r => f (x - (r.val : ℝ) / 8)
    have ht (r : Fin (4 + 1)) : x - (r.val : ℝ) / 8 ∈ Icc (0 : ℝ) 1 := by
      have hr2 : (r.val : ℝ) ≤ 4 := by exact_mod_cast (show r.val ≤ 4 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.2]
    apply interpolationMatrix_backward_jet_bound_of_remainder 4 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    have hr2 : (r.val : ℝ) ≤ 4 := by exact_mod_cast (show r.val ≤ 4 by omega)
    have hd : |x - (r.val : ℝ) / 8 - x| ≤ 1 / 2 := by
      rw [show x - (r.val : ℝ) / 8 - x = -((r.val : ℝ) / 8) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
      linarith
    have hc : (interpolationMatrix 4).mulVec (fun j => (-1 : ℝ) ^ j.val * v j) r =
        f x - derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) +
          iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 2 / 2 -
          iteratedDerivWithin 3 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 3 / 6 +
          iteratedDerivWithin 4 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 8) ^ 4 / 24 := by
      simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
        iteratedDerivWithin_one]
      <;> ring
    rw [hc]
    convert hr (ht r) hd using 1 <;> dsimp [y] <;> congr 1 <;> ring

/-- The Gamma quotient retains all four sharp integration factors. -/
-- @node: taylorRatio_orderFour
lemma taylorRatio_orderFour (c : ClassConstants) (hfour : holderOrder c = 4) :
    taylorRatio c = 1 / ((c.beta - 3) * (c.beta - 2) * (c.beta - 1) * c.beta) := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [hfour, Nat.cast_ofNat] at hα
  have hβ : c.beta ≠ 0 := c.beta_pos.ne'
  have hβ1 : c.beta - 1 ≠ 0 := by linarith
  have hβ2 : c.beta - 2 ≠ 0 := by linarith
  have hβ3 : c.beta - 3 ≠ 0 := by linarith
  have hΓ : Real.Gamma (c.beta - 3) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  simp only [taylorRatio, hfour, Nat.cast_ofNat, OfNat.ofNat_ne_zero, ↓reduceIte,
    show c.beta - 4 + 1 = c.beta - 3 by ring]
  rw [Real.Gamma_add_one hβ]
  have he : Real.Gamma c.beta = (c.beta - 1) * Real.Gamma (c.beta - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hβ1
  have he' : Real.Gamma (c.beta - 1) = (c.beta - 2) * Real.Gamma (c.beta - 2) := by
    simpa only [show c.beta - 2 + 1 = c.beta - 1 by ring] using Real.Gamma_add_one hβ2
  have he'' : Real.Gamma (c.beta - 2) = (c.beta - 3) * Real.Gamma (c.beta - 3) := by
    simpa only [show c.beta - 3 + 1 = c.beta - 2 by ring] using Real.Gamma_add_one hβ3
  rw [he, he', he'']
  field_simp

/-- The order-four interpolation solve gives all five within jets exactly
with the envelope declared in the risk roadmap. -/
-- @node: derivativeEnvelope_orderFour_jet_bound
lemma derivativeEnvelope_orderFour_jet_bound (c : ClassConstants)
    (hfour : holderOrder c = 4) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (4 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤ derivativeEnvelope c M L := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [hfour, Nat.cast_ofNat] at hα
  have hβ : 4 < c.beta := by linarith
  have h := fourthOrder_interpolation_jet_bound f hβ hM hL
    (by simpa only [hfour, Nat.cast_ofNat] using hf) hv hx j
  simpa only [derivativeEnvelope, hfour, OfNat.ofNat_ne_zero, ↓reduceIte,
    taylorRatio_orderFour c hfour, one_div, div_eq_mul_inv, one_mul, mul_comm L] using h

/-- All recurrence jets through order four satisfy the declared class envelope. -/
-- @node: recurrence_orderFour_jet_bound
lemma recurrence_orderFour_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (4 + 1)) :
    |iteratedDerivWithin j.val (P.lam a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.lambdaMax c.Llambda := by
  apply derivativeEnvelope_orderFour_jet_bound c hfour (P.lam a)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
    (hP.recurrenceHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
  exact (hP.recurrenceBounds a t ht).2

/-- All death-hazard jets through order four satisfy the same class envelope. -/
-- @node: death_orderFour_jet_bound
lemma death_orderFour_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (4 + 1)) :
    |iteratedDerivWithin j.val (P.hazard a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.dMax c.Ld := by
  apply derivativeEnvelope_orderFour_jet_bound c hfour (P.hazard a)
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
  exact (hP.deathBounds a t ht).2

/-- The fourth-order jet envelope is nonnegative for nonnegative value
and Hölder bounds. -/
-- @node: derivativeEnvelope_orderFour_nonneg
lemma derivativeEnvelope_orderFour_nonneg (c : ClassConstants)
    (hfour : holderOrder c = 4) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ derivativeEnvelope c M L := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [hfour, Nat.cast_ofNat] at hα
  have hβ1 : 0 < c.beta - 1 := by linarith
  simp only [derivativeEnvelope, hfour, OfNat.ofNat_ne_zero, ↓reduceIte,
    taylorRatio_orderFour c hfour]
  have hInv : 0 ≤ interpolationInverseNorm 4 := by
    unfold interpolationInverseNorm
    positivity
  exact mul_nonneg hInv (add_nonneg hM
    (mul_nonneg (mul_nonneg (one_div_nonneg.mpr
      (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hβ1.le) c.beta_pos.le)) hL) (Real.rpow_nonneg (by norm_num) _)))

/-- Each lower jet inherits the declared Hölder modulus from its next jet;
the top jet keeps the original modulus of the model assumption. -/
-- @node: derivativeHolderEnvelope_orderFour_modulus
lemma derivativeHolderEnvelope_orderFour_modulus (c : ClassConstants)
    (hfour : holderOrder c = 4) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    (j : Fin (4 + 1)) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) y| ≤
      derivativeHolderEnvelope c M L j.val * |x - y| ^ (c.beta - 4) := by
  by_cases hj : j.val < 4
  · have hα := holderOrder_remainder_exponent c
    simp only [hfour, Nat.cast_ofNat] at hα
    have hc : ContDiffOn ℝ (j.val + 1 : ℕ) f (Icc (0 : ℝ) 1) :=
      hf.1.of_le (by rw [hfour]; exact_mod_cast (show j.val + 1 ≤ 4 by omega))
    have h := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
      j.val (c.beta - 4) 0 1 (derivativeEnvelope c M L) hα.1 hα.2
      (by norm_num) (derivativeEnvelope_orderFour_nonneg c hfour hM hL) f
      (by simpa using hc)
      (by
        intro t ht
        simpa using derivativeEnvelope_orderFour_jet_bound c hfour f hM hL hf hv
          (by simpa using ht) ⟨j.val + 1, by omega⟩)
      x (by simpa using hx) y (by simpa using hy)
    simpa only [derivativeHolderEnvelope, hfour, hj, ↓reduceIte,
      zero_add, Real.one_rpow, mul_one] using h
  · have he : j.val = 4 := by omega
    simpa only [derivativeHolderEnvelope, hfour, he, lt_self_iff_false,
      ↓reduceIte, Nat.cast_ofNat] using hf.2 x hx y hy

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
