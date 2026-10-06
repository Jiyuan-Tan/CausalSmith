module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ExplicitRiskEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpFirstOrderTaylor

/-!
# Sharp second-order Taylor remainders

Integrating the first-order remainder of the derivative retains both factors
in the sharp second-order coefficient, on either side of an endpoint base.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The derivative inherits the top modulus of a twice differentiable function. -/
-- @node: secondOrder_derivative_holder
lemma secondOrder_derivative_holder (f : ℝ → ℝ) {α L : ℝ}
    (hf : HolderSeminormLe 2 α L f) :
    HolderSeminormLe 1 α L (derivWithin f (Icc (0 : ℝ) 1)) := by
  refine ⟨hf.1.derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num), ?_⟩
  intro x hx y hy
  simpa only [show 2 = 1 + 1 from rfl, iteratedDerivWithin_succ'] using hf.2 x hx y hy

/-- The quadratic Taylor remainder is the integral of the linear remainder
of the derivative; the identity holds for any expansion base. -/
-- @node: secondOrder_remainder_integral
lemma secondOrder_remainder_integral (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Icc (0 : ℝ) 1))
    {x y b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    (∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) b -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b * (u - b)) =
      f y - f x - derivWithin f (Icc (0 : ℝ) 1) b * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b *
        ((y - b) ^ 2 - (x - b) ^ 2) / 2 := by
  have hc := hf.continuousOn_derivWithin (uniqueDiffOn_Icc (by norm_num)) (by norm_num)
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hi : IntervalIntegrable (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) b) volume x y :=
    ((hc.mono hsub).sub continuousOn_const).intervalIntegrable_of_Icc hxy
  have hp : IntervalIntegrable (fun u : ℝ =>
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) b * (u - b)) volume x y := by
    exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hi hp, firstOrder_remainder_integral f hf hx hy hxy,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_sub_right (f := fun u : ℝ => u)]
  have hid : (∫ u in (x - b)..(y - b), u) =
      ((y - b) ^ 2 - (x - b) ^ 2) / 2 := by
    simpa using
      (integral_pow (a := x - b) (b := y - b) 1)
  rw [hid]
  ring

/-- Integrating the derivative remainder to the right gives the sharp
second-order coefficient, without replacing the power by a supremum. -/
-- @node: secondOrder_forward_remainder_bound
lemma secondOrder_forward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 2 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (y - x) ^ 2 / 2| ≤
      L / ((α + 1) * (α + 2)) * (y - x) ^ (α + 2) := by
  have hdf := secondOrder_derivative_holder f hf
  have hid := secondOrder_remainder_integral f (hf.1.of_le (by norm_num))
    (b := x) hx hy hxy
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hid
  rw [← hid]
  have hc := hdf.1.continuousOn
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hr : ContinuousOn (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (u - x)) (Icc x y) :=
    ((hc.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hp : Continuous (fun u : ℝ => (u - x) ^ (α + 1)) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) x -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (u - x)| :=
      intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L / (α + 1) * (u - x) ^ (α + 1) := by
      apply intervalIntegral.integral_mono_on hxy
        (hr.abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_one,
        iteratedDerivWithin_zero, Pi.mul_apply] using
        firstOrder_forward_remainder_bound (derivWithin f (Icc (0 : ℝ) 1)) hα hdf
          hx (hsub hu) hu.1
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        firstOrder_forward_power_integral (by linarith : 0 < α + 1)]
      simp only [show α + 1 + 1 = α + 2 by ring]
      field_simp
      <;> ring

/-- Integrating to a right-hand expansion base gives the same sharp
second-order constant on the backward interpolation grid. -/
-- @node: secondOrder_backward_remainder_bound
lemma secondOrder_backward_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 2 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1)
    (hxy : x ≤ y) :
    |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (x - y) ^ 2 / 2| ≤
      L / ((α + 1) * (α + 2)) * (y - x) ^ (α + 2) := by
  have hdf := secondOrder_derivative_holder f hf
  have hid := secondOrder_remainder_integral f (hf.1.of_le (by norm_num))
    (b := y) hx hy hxy
  have heq : |f x - f y - derivWithin f (Icc (0 : ℝ) 1) y * (x - y) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (x - y) ^ 2 / 2| =
      |∫ u in x..y, derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y)| := by
    rw [hid, ← abs_neg]
    congr 1
    ring
  rw [heq]
  have hc := hdf.1.continuousOn
  have hsub : Icc x y ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc hx.1 hy.2
  have hr : ContinuousOn (fun u => derivWithin f (Icc (0 : ℝ) 1) u -
      derivWithin f (Icc (0 : ℝ) 1) y -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y)) (Icc x y) :=
    ((hc.mono hsub).sub continuousOn_const).sub
      (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
  have hp : Continuous (fun u : ℝ => (y - u) ^ (α + 1)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
  calc
    _ ≤ ∫ u in x..y, |derivWithin f (Icc (0 : ℝ) 1) u -
        derivWithin f (Icc (0 : ℝ) 1) y -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) y * (u - y)| :=
      intervalIntegral.abs_integral_le_integral_abs hxy
    _ ≤ ∫ u in x..y, L / (α + 1) * (y - u) ^ (α + 1) := by
      apply intervalIntegral.integral_mono_on hxy
        (hr.abs.intervalIntegrable_of_Icc hxy)
        ((continuous_const.mul hp).intervalIntegrable _ _)
      intro u hu
      simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_one,
        iteratedDerivWithin_zero, Pi.mul_apply] using
        firstOrder_backward_remainder_bound (derivWithin f (Icc (0 : ℝ) 1)) hα hdf
          (hsub hu) hy hu.2
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        firstOrder_backward_power_integral (by linarith : 0 < α + 1)]
      simp only [show α + 1 + 1 = α + 2 by ring]
      field_simp
      <;> ring

/-- The quadratic Taylor remainder has its exact integrated Hölder coefficient
at every base in the closed horizon, including both endpoints. -/
-- @node: secondOrder_remainder_bound
lemma secondOrder_remainder_bound (f : ℝ → ℝ) {α L : ℝ}
    (hα : 0 < α) (hf : HolderSeminormLe 2 α L f)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |f y - f x - derivWithin f (Icc (0 : ℝ) 1) x * (y - x) -
      iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (y - x) ^ 2 / 2| ≤
      L / ((α + 1) * (α + 2)) * |y - x| ^ (α + 2) := by
  by_cases hxy : x ≤ y
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hxy)] using
      secondOrder_forward_remainder_bound f hα hf hx hy hxy
  · have hyx := le_of_not_ge hxy
    simpa only [abs_of_nonpos (sub_nonpos.mpr hyx), neg_sub] using
      secondOrder_backward_remainder_bound f hα hf hy hx hyx

/-- The three-point one-sided interpolation solve bounds all second-order
jets with the sharp Taylor coefficient and the declared finite inverse norm. -/
-- @node: secondOrder_interpolation_jet_bound
lemma secondOrder_interpolation_jet_bound (f : ℝ → ℝ) {β M L : ℝ}
    (hβ : 2 < β) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe 2 (β - 2) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (2 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤
      interpolationInverseNorm 2 *
        (M + L / ((β - 1) * β) * (2 : ℝ) ^ (-β)) := by
  let v : Fin (2 + 1) → ℝ := fun j => iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x
  let R := L / ((β - 1) * β) * (2 : ℝ) ^ (-β)
  have hβ0 : 0 < β := by linarith
  have hβ1 : 0 < β - 1 := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hα : 0 < β - 2 := by linarith
  have hpow : (1 / 2 : ℝ) ^ β = (2 : ℝ) ^ (-β) := by
    rw [one_div, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num)]
  have hr {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (htx : |t - x| ≤ 1 / 2) :
      |f t - f x - derivWithin f (Icc (0 : ℝ) 1) x * (t - x) -
        iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * (t - x) ^ 2 / 2| ≤ R := by
    have hb := secondOrder_remainder_bound f hα hf hx ht
    rw [show β - 2 + 1 = β - 1 by ring, show β - 2 + 2 = β by ring] at hb
    refine hb.trans ?_
    dsimp [R]
    rw [← hpow]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) htx (by linarith))
      (div_nonneg hL (mul_nonneg (by linarith) (by linarith)))
  have hcalc (r : Fin (2 + 1)) :
      (interpolationMatrix 2).mulVec v r =
        f x + derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 4) +
          iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 4) ^ 2 / 2 := by
    simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
      iteratedDerivWithin_one]
    <;> ring
  by_cases hleft : x ≤ 1 / 2
  · let y : Fin (2 + 1) → ℝ := fun r => f (x + (r.val : ℝ) / 4)
    have ht (r : Fin (2 + 1)) : x + (r.val : ℝ) / 4 ∈ Icc (0 : ℝ) 1 := by
      have hr2 : (r.val : ℝ) ≤ 2 := by exact_mod_cast (show r.val ≤ 2 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.1]
    apply interpolationMatrix_jet_bound_of_remainder 2 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    rw [hcalc]
    have hr2 : (r.val : ℝ) ≤ 2 := by exact_mod_cast (show r.val ≤ 2 by omega)
    have hd : |x + (r.val : ℝ) / 4 - x| ≤ 1 / 2 := by
      rw [show x + (r.val : ℝ) / 4 - x = (r.val : ℝ) / 4 by ring,
        abs_of_nonneg (by positivity)]
      linarith
    simpa only [y, show x + (r.val : ℝ) / 4 - x = (r.val : ℝ) / 4 by ring,
      sub_add_eq_sub_sub] using hr (ht r) hd
  · let y : Fin (2 + 1) → ℝ := fun r => f (x - (r.val : ℝ) / 4)
    have ht (r : Fin (2 + 1)) : x - (r.val : ℝ) / 4 ∈ Icc (0 : ℝ) 1 := by
      have hr2 : (r.val : ℝ) ≤ 2 := by exact_mod_cast (show r.val ≤ 2 by omega)
      have hr0 : (0 : ℝ) ≤ r.val := by positivity
      constructor <;> linarith [hx.2]
    apply interpolationMatrix_backward_jet_bound_of_remainder 2 (by omega) v y hM hR
      (fun r => hv _ (ht r)) _ j
    intro r
    have hr2 : (r.val : ℝ) ≤ 2 := by exact_mod_cast (show r.val ≤ 2 by omega)
    have hd : |x - (r.val : ℝ) / 4 - x| ≤ 1 / 2 := by
      rw [show x - (r.val : ℝ) / 4 - x = -((r.val : ℝ) / 4) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
      linarith
    have hc : (interpolationMatrix 2).mulVec (fun j => (-1 : ℝ) ^ j.val * v j) r =
        f x - derivWithin f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 4) +
          iteratedDerivWithin 2 f (Icc (0 : ℝ) 1) x * ((r.val : ℝ) / 4) ^ 2 / 2 := by
      simp [interpolationMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, v,
        iteratedDerivWithin_one]
      <;> ring
    rw [hc]
    convert hr (ht r) hd using 1 <;> dsimp [y] <;> congr 1 <;> ring

/-- At order two the Gamma quotient equals the two successive integration
factors in the sharp Taylor remainder. -/
-- @node: taylorRatio_orderTwo
lemma taylorRatio_orderTwo (c : ClassConstants) (htwo : holderOrder c = 2) :
    taylorRatio c = 1 / ((c.beta - 1) * c.beta) := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [htwo, Nat.cast_ofNat] at hα
  have hβ : c.beta ≠ 0 := c.beta_pos.ne'
  have hβ1 : c.beta - 1 ≠ 0 := by linarith
  have hΓ : Real.Gamma (c.beta - 1) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  simp only [taylorRatio, htwo, Nat.cast_ofNat, OfNat.ofNat_ne_zero, ↓reduceIte,
    show c.beta - 2 + 1 = c.beta - 1 by ring]
  rw [Real.Gamma_add_one hβ]
  have he : Real.Gamma c.beta = (c.beta - 1) * Real.Gamma (c.beta - 1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hβ1
  rw [he]
  field_simp

/-- The order-two interpolation solve gives all three within jets exactly
with the envelope declared in the risk roadmap. -/
-- @node: derivativeEnvelope_orderTwo_jet_bound
lemma derivativeEnvelope_orderTwo_jet_bound (c : ClassConstants)
    (htwo : holderOrder c = 2) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (2 + 1)) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x| ≤ derivativeEnvelope c M L := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [htwo, Nat.cast_ofNat] at hα
  have hβ : 2 < c.beta := by linarith
  have h := secondOrder_interpolation_jet_bound f hβ hM hL
    (by simpa only [htwo, Nat.cast_ofNat] using hf) hv hx j
  simpa only [derivativeEnvelope, htwo, OfNat.ofNat_ne_zero, ↓reduceIte,
    taylorRatio_orderTwo c htwo, one_div, div_eq_mul_inv, one_mul, mul_comm L] using h

/-- All recurrence jets through order two satisfy the declared class envelope. -/
-- @node: recurrence_orderTwo_jet_bound
lemma recurrence_orderTwo_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (2 + 1)) :
    |iteratedDerivWithin j.val (P.lam a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.lambdaMax c.Llambda := by
  apply derivativeEnvelope_orderTwo_jet_bound c htwo (P.lam a)
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
    (hP.recurrenceHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
  exact (hP.recurrenceBounds a t ht).2

/-- All death-hazard jets through order two satisfy the same class envelope. -/
-- @node: death_orderTwo_jet_bound
lemma death_orderTwo_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (j : Fin (2 + 1)) :
    |iteratedDerivWithin j.val (P.hazard a) (Icc (0 : ℝ) 1) x| ≤
      derivativeEnvelope c c.dMax c.Ld := by
  apply derivativeEnvelope_orderTwo_jet_bound c htwo (P.hazard a)
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) _ hx j
  intro t ht
  rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
  exact (hP.deathBounds a t ht).2

/-- The second-order jet envelope is nonnegative for nonnegative value
and Hölder bounds. -/
-- @node: derivativeEnvelope_orderTwo_nonneg
lemma derivativeEnvelope_orderTwo_nonneg (c : ClassConstants)
    (htwo : holderOrder c = 2) {M L : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ derivativeEnvelope c M L := by
  have hα := (holderOrder_remainder_exponent c).1
  simp only [htwo, Nat.cast_ofNat] at hα
  have hβ1 : 0 < c.beta - 1 := by linarith
  simp only [derivativeEnvelope, htwo, OfNat.ofNat_ne_zero, ↓reduceIte,
    taylorRatio_orderTwo c htwo]
  have hInv : 0 ≤ interpolationInverseNorm 2 := by
    unfold interpolationInverseNorm
    positivity
  exact mul_nonneg hInv (add_nonneg hM
    (mul_nonneg (mul_nonneg (one_div_nonneg.mpr
      (mul_nonneg hβ1.le c.beta_pos.le)) hL) (Real.rpow_nonneg (by norm_num) _)))

/-- Each lower jet inherits the declared Hölder modulus from its next jet;
the top jet keeps the original modulus of the model assumption. -/
-- @node: derivativeHolderEnvelope_orderTwo_modulus
lemma derivativeHolderEnvelope_orderTwo_modulus (c : ClassConstants)
    (htwo : holderOrder c = 2) (f : ℝ → ℝ) {M L : ℝ}
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hf : HolderSeminormLe (holderOrder c) (c.beta - holderOrder c) L f)
    (hv : ∀ t ∈ Icc (0 : ℝ) 1, |f t| ≤ M)
    (j : Fin (2 + 1)) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j.val f (Icc (0 : ℝ) 1) y| ≤
      derivativeHolderEnvelope c M L j.val * |x - y| ^ (c.beta - 2) := by
  by_cases hj : j.val < 2
  · have hα := holderOrder_remainder_exponent c
    simp only [htwo, Nat.cast_ofNat] at hα
    have hc : ContDiffOn ℝ (j.val + 1 : ℕ) f (Icc (0 : ℝ) 1) :=
      hf.1.of_le (by rw [htwo]; exact_mod_cast (show j.val + 1 ≤ 2 by omega))
    have h := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
      j.val (c.beta - 2) 0 1 (derivativeEnvelope c M L) hα.1 hα.2
      (by norm_num) (derivativeEnvelope_orderTwo_nonneg c htwo hM hL) f
      (by simpa using hc)
      (by
        intro t ht
        simpa using derivativeEnvelope_orderTwo_jet_bound c htwo f hM hL hf hv
          (by simpa using ht) ⟨j.val + 1, by omega⟩)
      x (by simpa using hx) y (by simpa using hy)
    simpa only [derivativeHolderEnvelope, htwo, hj, ↓reduceIte,
      zero_add, Real.one_rpow, mul_one] using h
  · have he : j.val = 2 := by omega
    simpa only [derivativeHolderEnvelope, htwo, he, lt_self_iff_false,
      ↓reduceIte, Nat.cast_ofNat] using hf.2 x hx y hy

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
