module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SharpSecondOrderTaylor

/-! # Second-order survival envelopes

The hazard equation and the sharp intensity interpolation bounds give the
survival jets and their moduli with the declared finite recursion constants.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- The survival function has one more derivative than the model hazard. -/
-- @node: survival_modelClass_contDiffOn
lemma survival_modelClass_contDiffOn (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    ContDiffOn ℝ (holderOrder c + 1 : ℕ) (survival P a) (Icc (0 : ℝ) 1) := by
  unfold survival
  simpa only [zero_add, Nat.cast_add, Nat.cast_one] using
    (Causalean.Mathlib.Analysis.Calculus.HolderTaylor.interval_primitive_contDiffOn
      (holderOrder c) 0 1 (by norm_num) (P.hazard a)
      (by simpa only [zero_add] using (hP.deathHolder a).1)).neg.exp

/-- The hazard differential equation gives every within survival jet. -/
-- @node: survival_modelClass_jet_recurrence
lemma survival_modelClass_jet_recurrence (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) {j : ℕ} (hj : j ≤ holderOrder c)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    iteratedDerivWithin (j + 1) (survival P a) (Icc (0 : ℝ) 1) t =
      -(∑ r ∈ Finset.range (j + 1), (Nat.choose j r : ℝ) *
        iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) t *
        iteratedDerivWithin (j - r) (survival P a) (Icc (0 : ℝ) 1) t) := by
  unfold survival
  simpa only [zero_add] using
    Causalean.Mathlib.Analysis.Calculus.HolderTaylor.survival_iteratedDerivWithin_succ
      (holderOrder c) 0 1 (by norm_num) (P.hazard a)
      (by simpa only [zero_add] using (hP.deathHolder a).1) j hj t
      (by simpa only [zero_add] using ht)

/-- Nonnegative hazard jet bounds give nonnegative survival recursion bounds. -/
-- @node: survivalDerivativeEnvelope_nonneg
lemma survivalDerivativeEnvelope_nonneg (c : ClassConstants)
    (hD : 0 ≤ derivativeEnvelope c c.dMax c.Ld) (j : ℕ) :
    0 ≤ survivalDerivativeEnvelope c j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero => simp [survivalDerivativeEnvelope]
    | succ k =>
      rw [survivalDerivativeEnvelope]
      apply Finset.sum_nonneg
      intro r hr
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD)
        (ih (k - r) (by omega))

/-- The hazard recurrence bounds survival jets from any available hazard jets. -/
-- @node: survival_jet_bound_of_hazard_jets
lemma survival_jet_bound_of_hazard_jets (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    (hD : 0 ≤ derivativeEnvelope c c.dMax c.Ld)
    (hjets : ∀ j ≤ holderOrder c, ∀ t ∈ Icc (0 : ℝ) 1,
      |iteratedDerivWithin j (P.hazard a) (Icc (0 : ℝ) 1) t| ≤
        derivativeEnvelope c c.dMax c.Ld)
    {j : ℕ} (hj : j ≤ holderOrder c + 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) t| ≤
      survivalDerivativeEnvelope c j := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      simp only [iteratedDerivWithin_zero, survivalDerivativeEnvelope]
      rw [abs_of_pos (show 0 < survival P a t from Real.exp_pos _)]
      exact (survival_bounds_of_deathBounds c P hP.deathBounds a ht).2
    | succ k =>
      rw [survival_modelClass_jet_recurrence c P hP a (by omega) ht, abs_neg,
        survivalDerivativeEnvelope]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro r hr
      have hrk : r ≤ k := by have := Finset.mem_range.mp hr; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hjets r (by omega) t ht) (Nat.cast_nonneg _))
        (ih (k - r) (by omega) (by omega)) (abs_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) hD)

/-- Sharp second-order hazard interpolation supplies all survival jets
through order three via the hazard equation. -/
-- @node: survival_orderTwo_jet_bound
lemma survival_orderTwo_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {j : ℕ} (hj : j ≤ 3) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) t| ≤
      survivalDerivativeEnvelope c j := by
  apply survival_jet_bound_of_hazard_jets c P hP a
    (derivativeEnvelope_orderTwo_nonneg c htwo
      (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le) _ (by omega) ht
  intro k hk u hu
  exact death_orderTwo_jet_bound c P hP htwo a hu ⟨k, by omega⟩

/-- Lower survival jets inherit the Hölder modulus of their next-jet bounds. -/
-- @node: survival_orderTwo_lower_jet_holder
lemma survival_orderTwo_lower_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {j : ℕ} (hj : j < 2) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - 2) := by
  have hα := holderOrder_remainder_exponent c
  simp only [htwo, Nat.cast_ofNat] at hα
  have hD := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hc : ContDiffOn ℝ (j + 1 : ℕ) (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by
      rw [htwo]; exact_mod_cast (show j + 1 ≤ 3 by omega))
  have hb := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
    j (c.beta - 2) 0 1 (survivalDerivativeEnvelope c (j + 1)) hα.1 hα.2
    (by norm_num) (survivalDerivativeEnvelope_nonneg c hD _) (survival P a)
    (by simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hc)
    (by
      intro t ht
      simpa only [zero_add] using survival_orderTwo_jet_bound c P hP htwo a (j := j + 1)
        (by omega) (by simpa only [zero_add] using ht))
    x (by simpa only [zero_add] using hx) y (by simpa only [zero_add] using hy)
  simpa only [survivalHolderEnvelope, htwo, hj, ↓reduceIte, zero_add,
    Real.one_rpow, mul_one] using hb

/-- The declared survival Hölder envelope is nonnegative when the hazard
value and jet envelopes are nonnegative. -/
-- @node: survivalHolderEnvelope_nonneg
lemma survivalHolderEnvelope_nonneg (c : ClassConstants)
    (hD : 0 ≤ derivativeEnvelope c c.dMax c.Ld) (j : ℕ) :
    0 ≤ survivalHolderEnvelope c j := by
  unfold survivalHolderEnvelope
  split_ifs
  · exact survivalDerivativeEnvelope_nonneg c hD _
  · exact c.dMin_pos.le.trans c.dMin_lt.le
  · apply Finset.sum_nonneg
    intro r hr
    have hL : 0 ≤ derivativeHolderEnvelope c c.dMax c.Ld r := by
      unfold derivativeHolderEnvelope
      split_ifs
      · exact hD
      · exact c.Ld_pos.le
    exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (mul_nonneg hD (survivalDerivativeEnvelope_nonneg c hD _))
      (mul_nonneg hL (survivalDerivativeEnvelope_nonneg c hD _)))

/-- The top quadratic survival jet inherits its exact product modulus
from the differentiated hazard equation. -/
-- @node: survival_orderTwo_top_jet_holder
lemma survival_orderTwo_top_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin 2 (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin 2 (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c 2 * |x - y| ^ (c.beta - 2) := by
  let D := derivativeEnvelope c c.dMax c.Ld
  have hD : 0 ≤ D := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.hazard a t| ≤ c.dMax := by
    intro t ht
    rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
    exact (hP.deathBounds a t ht).2
  have hdmod (j : Fin (2 + 1)) := derivativeHolderEnvelope_orderTwo_modulus c
    htwo (P.hazard a) (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) hv j hx hy
  have hsmod (j : ℕ) (hj : j < 2) :=
    survival_orderTwo_lower_jet_holder c P hP htwo a hj hx hy
  have hterm (r : ℕ) (hr : r ≤ 1) :
      |iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) y| ≤
      (D * survivalDerivativeEnvelope c (2 - r) +
        D * survivalDerivativeEnvelope c (1 - r)) * |x - y| ^ (c.beta - 2) := by
    have hm := sharpProduct_increment_bound hD
      (survivalDerivativeEnvelope_nonneg c hD (1 - r)) hD hq
      (death_orderTwo_jet_bound c P hP htwo a hy ⟨r, by omega⟩)
      (survival_orderTwo_jet_bound c P hP htwo a (by omega) hx)
      (by simpa only [derivativeHolderEnvelope, htwo,
        show r < 2 by omega, ↓reduceIte] using hdmod ⟨r, by omega⟩)
      (hsmod (1 - r) (by omega))
    have he : survivalHolderEnvelope c (1 - r) =
        survivalDerivativeEnvelope c (2 - r) := by
      simp only [survivalHolderEnvelope, htwo, show 1 - r < 2 by omega, ↓reduceIte]
      rw [show 1 - r + 1 = 2 - r by omega]
    simpa only [he, mul_comm D, add_comm] using hm
  have hxrec := survival_modelClass_jet_recurrence c P hP a (j := 1) (by omega) hx
  have hyrec := survival_modelClass_jet_recurrence c P hP a (j := 1) (by omega) hy
  rw [hxrec, hyrec, neg_sub_neg, abs_sub_comm]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range (1 + 1), (Nat.choose 1 r : ℝ) *
        ((D * survivalDerivativeEnvelope c (2 - r) +
          D * survivalDerivativeEnvelope c (1 - r)) * |x - y| ^ (c.beta - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [show (Nat.choose 1 r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        (Nat.choose 1 r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) y =
        (Nat.choose 1 r : ℝ) *
          (iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin (1 - r) (survival P a) (Icc (0 : ℝ) 1) y) by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hterm r (by
        have := Finset.mem_range.mp hr; omega)) (Nat.cast_nonneg _)
    _ = _ := by
      simp [survivalHolderEnvelope, htwo, derivativeHolderEnvelope, D,
        Finset.sum_range_succ]
      ring

/-- Every quadratic survival jet has the declared Hölder modulus. -/
-- @node: survival_orderTwo_jet_holder
lemma survival_orderTwo_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm)
    {j : ℕ} (hj : j ≤ 2) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - 2) := by
  by_cases hlt : j < 2
  · exact survival_orderTwo_lower_jet_holder c P hP htwo a hlt hx hy
  · have he : j = 2 := by omega
    subst j
    exact survival_orderTwo_top_jet_holder c P hP htwo a hx hy

/-- The declared product modulus is nonnegative at quadratic order. -/
-- @node: productHolderEnvelope_orderTwo_nonneg
lemma productHolderEnvelope_orderTwo_nonneg (c : ClassConstants)
    (htwo : holderOrder c = 2) : 0 ≤ productHolderEnvelope c := by
  have hD := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  unfold productHolderEnvelope
  apply Finset.sum_nonneg
  intro r hr
  have hL : 0 ≤ derivativeHolderEnvelope c c.lambdaMax c.Llambda (holderOrder c - r) := by
    unfold derivativeHolderEnvelope
    split_ifs
    · exact hR
    · exact c.Llambda_pos.le
  exact mul_nonneg (Nat.cast_nonneg _) (add_nonneg
    (mul_nonneg (survivalDerivativeEnvelope_nonneg c hD _) hL)
    (mul_nonneg (survivalHolderEnvelope_nonneg c hD _) hR))

/-- Leibniz's rule assembles the quadratic target-product modulus using
exactly the class's declared hazard and recurrence envelopes. -/
-- @node: survival_product_orderTwo_holder
lemma survival_product_orderTwo_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (htwo : holderOrder c = 2) (a : Arm) :
    HolderSeminormLe 2 (c.beta - 2) (productHolderEnvelope c)
      (fun t => survival P a t * P.lam a t) := by
  have hS : ContDiffOn ℝ 2 (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by norm_num [htwo])
  have hL : ContDiffOn ℝ 2 (P.lam a) (Icc (0 : ℝ) 1) := by
    simpa only [htwo, Nat.cast_ofNat] using (hP.recurrenceHolder a).1
  refine ⟨hS.mul hL, ?_⟩
  intro x hx y hy
  have hD := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_orderTwo_nonneg c htwo
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - 2) := Real.rpow_nonneg (abs_nonneg _) _
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.lam a t| ≤ c.lambdaMax := by
    intro t ht
    rw [abs_of_nonneg (c.lambdaMin_pos.le.trans (hP.recurrenceBounds a t ht).1)]
    exact (hP.recurrenceBounds a t ht).2
  rw [show (fun t => survival P a t * P.lam a t) = survival P a * P.lam a from rfl,
    iteratedDerivWithin_mul hx (uniqueDiffOn_Icc (by norm_num)) (hS x hx) (hL x hx),
    iteratedDerivWithin_mul hy (uniqueDiffOn_Icc (by norm_num)) (hS y hy) (hL y hy),
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range (2 + 1), (Nat.choose 2 r : ℝ) *
        ((survivalDerivativeEnvelope c r *
          derivativeHolderEnvelope c c.lambdaMax c.Llambda (2 - r) +
          survivalHolderEnvelope c r * derivativeEnvelope c c.lambdaMax c.Llambda) *
          |x - y| ^ (c.beta - 2)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : r ≤ 2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hm := sharpProduct_increment_bound
        (survivalDerivativeEnvelope_nonneg c hD r) hR
        (survivalHolderEnvelope_nonneg c hD r) hq
        (survival_orderTwo_jet_bound c P hP htwo a (j := r) (hr2.trans (by norm_num)) hy)
        (recurrence_orderTwo_jet_bound c P hP htwo a hx ⟨2 - r, by omega⟩)
        (survival_orderTwo_jet_holder c P hP htwo a hr2 hx hy)
        (derivativeHolderEnvelope_orderTwo_modulus c htwo (P.lam a)
          (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
          (hP.recurrenceHolder a) hv ⟨2 - r, by omega⟩ hx hy)
      have he : (Nat.choose 2 r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (2 - r) (P.lam a) (Icc (0 : ℝ) 1) x -
        (Nat.choose 2 r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (2 - r) (P.lam a) (Icc (0 : ℝ) 1) y =
        (Nat.choose 2 r : ℝ) *
          (iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin (2 - r) (P.lam a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin (2 - r) (P.lam a) (Icc (0 : ℝ) 1) y) := by ring
      rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hm.trans_eq (by ring)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [productHolderEnvelope, htwo, Finset.sum_mul, mul_assoc]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
