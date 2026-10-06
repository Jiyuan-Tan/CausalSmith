module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.ThirdOrderSurvivalEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.FourthOrderJetEnvelopes

/-! # Quartic survival and target envelopes

The differentiated hazard equation and Leibniz rule give the declared quartic
survival and target Hölder envelopes from the sharp five-point jet bounds.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Sharp fourth-order hazard interpolation supplies all survival jets
through order four via the hazard equation. -/
-- @node: survival_orderFour_jet_bound
lemma survival_orderFour_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {j : ℕ} (hj : j ≤ 5) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) t| ≤
      survivalDerivativeEnvelope c j := by
  apply survival_jet_bound_of_hazard_jets c P hP a
    (derivativeEnvelope_orderFour_nonneg c hfour
      (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le) _ (by omega) ht
  intro k hk u hu
  exact death_orderFour_jet_bound c P hP hfour a hu ⟨k, by omega⟩

/-- Lower survival jets inherit the Hölder modulus of their next-jet bounds. -/
-- @node: survival_orderFour_lower_jet_holder
lemma survival_orderFour_lower_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {j : ℕ} (hj : j < 4) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - 4) := by
  have hα := holderOrder_remainder_exponent c
  simp only [hfour, Nat.cast_ofNat] at hα
  have hD := derivativeEnvelope_orderFour_nonneg c hfour
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hc : ContDiffOn ℝ (j + 1 : ℕ) (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by
      rw [hfour]; exact_mod_cast (show j + 1 ≤ 5 by omega))
  have hb := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
    j (c.beta - 4) 0 1 (survivalDerivativeEnvelope c (j + 1)) hα.1 hα.2
    (by norm_num) (survivalDerivativeEnvelope_nonneg c hD _) (survival P a)
    (by simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hc)
    (by
      intro t ht
      simpa only [zero_add] using survival_orderFour_jet_bound c P hP hfour a (j := j + 1)
        (by omega) (by simpa only [zero_add] using ht))
    x (by simpa only [zero_add] using hx) y (by simpa only [zero_add] using hy)
  simpa only [survivalHolderEnvelope, hfour, hj, ↓reduceIte, zero_add,
    Real.one_rpow, mul_one] using hb

/-- The top quartic survival jet inherits its exact product modulus
from the differentiated hazard equation. -/
-- @node: survival_orderFour_top_jet_holder
lemma survival_orderFour_top_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin 4 (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin 4 (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c 4 * |x - y| ^ (c.beta - 4) := by
  let D := derivativeEnvelope c c.dMax c.Ld
  have hD : 0 ≤ D := derivativeEnvelope_orderFour_nonneg c hfour
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - 4) := Real.rpow_nonneg (abs_nonneg _) _
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.hazard a t| ≤ c.dMax := by
    intro t ht
    rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
    exact (hP.deathBounds a t ht).2
  have hdmod (j : Fin (4 + 1)) := derivativeHolderEnvelope_orderFour_modulus c
    hfour (P.hazard a) (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) hv j hx hy
  have hsmod (j : ℕ) (hj : j < 4) :=
    survival_orderFour_lower_jet_holder c P hP hfour a hj hx hy
  have hterm (r : ℕ) (hr : r ≤ 3) :
      |iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) y| ≤
      (D * survivalDerivativeEnvelope c (4 - r) +
        D * survivalDerivativeEnvelope c (3 - r)) * |x - y| ^ (c.beta - 4) := by
    have hm := sharpProduct_increment_bound hD
      (survivalDerivativeEnvelope_nonneg c hD (3 - r)) hD hq
      (death_orderFour_jet_bound c P hP hfour a hy ⟨r, by omega⟩)
      (survival_orderFour_jet_bound c P hP hfour a (by omega) hx)
      (by simpa only [derivativeHolderEnvelope, hfour,
        show r < 4 by omega, ↓reduceIte] using hdmod ⟨r, by omega⟩)
      (hsmod (3 - r) (by omega))
    have he : survivalHolderEnvelope c (3 - r) =
        survivalDerivativeEnvelope c (4 - r) := by
      simp only [survivalHolderEnvelope, hfour, show 3 - r < 4 by omega, ↓reduceIte]
      rw [show 3 - r + 1 = 4 - r by omega]
    simpa only [he, mul_comm D, add_comm] using hm
  have hxrec := survival_modelClass_jet_recurrence c P hP a (j := 3) (by omega) hx
  have hyrec := survival_modelClass_jet_recurrence c P hP a (j := 3) (by omega) hy
  rw [hxrec, hyrec, neg_sub_neg, abs_sub_comm]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range (3 + 1), (Nat.choose 3 r : ℝ) *
        ((D * survivalDerivativeEnvelope c (4 - r) +
          D * survivalDerivativeEnvelope c (3 - r)) * |x - y| ^ (c.beta - 4)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [show (Nat.choose 3 r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        (Nat.choose 3 r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) y =
        (Nat.choose 3 r : ℝ) *
          (iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin (3 - r) (survival P a) (Icc (0 : ℝ) 1) y) by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hterm r (by
        have := Finset.mem_range.mp hr; omega)) (Nat.cast_nonneg _)
    _ = _ := by
      simp [survivalHolderEnvelope, hfour, derivativeHolderEnvelope, D,
        Finset.sum_range_succ]
      ring

/-- Every quartic survival jet has the declared Hölder modulus. -/
-- @node: survival_orderFour_jet_holder
lemma survival_orderFour_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm)
    {j : ℕ} (hj : j ≤ 4) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - 4) := by
  by_cases hlt : j < 4
  · exact survival_orderFour_lower_jet_holder c P hP hfour a hlt hx hy
  · have he : j = 4 := by omega
    subst j
    exact survival_orderFour_top_jet_holder c P hP hfour a hx hy

/-- The declared product modulus is nonnegative at quartic order. -/
-- @node: productHolderEnvelope_orderFour_nonneg
lemma productHolderEnvelope_orderFour_nonneg (c : ClassConstants)
    (hfour : holderOrder c = 4) : 0 ≤ productHolderEnvelope c := by
  have hD := derivativeEnvelope_orderFour_nonneg c hfour
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_orderFour_nonneg c hfour
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

/-- Leibniz's rule assembles the quartic target-product modulus using
exactly the class's declared hazard and recurrence envelopes. -/
-- @node: survival_product_orderFour_holder
lemma survival_product_orderFour_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hfour : holderOrder c = 4) (a : Arm) :
    HolderSeminormLe 4 (c.beta - 4) (productHolderEnvelope c)
      (fun t => survival P a t * P.lam a t) := by
  have hS : ContDiffOn ℝ 4 (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by norm_num [hfour])
  have hL : ContDiffOn ℝ 4 (P.lam a) (Icc (0 : ℝ) 1) := by
    simpa only [hfour, Nat.cast_ofNat] using (hP.recurrenceHolder a).1
  refine ⟨hS.mul hL, ?_⟩
  intro x hx y hy
  have hD := derivativeEnvelope_orderFour_nonneg c hfour
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_orderFour_nonneg c hfour
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - 4) := Real.rpow_nonneg (abs_nonneg _) _
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
    _ ≤ ∑ r ∈ Finset.range (4 + 1), (Nat.choose 4 r : ℝ) *
        ((survivalDerivativeEnvelope c r *
          derivativeHolderEnvelope c c.lambdaMax c.Llambda (4 - r) +
          survivalHolderEnvelope c r * derivativeEnvelope c c.lambdaMax c.Llambda) *
          |x - y| ^ (c.beta - 4)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : r ≤ 4 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hm := sharpProduct_increment_bound
        (survivalDerivativeEnvelope_nonneg c hD r) hR
        (survivalHolderEnvelope_nonneg c hD r) hq
        (survival_orderFour_jet_bound c P hP hfour a (j := r) (hr2.trans (by norm_num)) hy)
        (recurrence_orderFour_jet_bound c P hP hfour a hx ⟨4 - r, by omega⟩)
        (survival_orderFour_jet_holder c P hP hfour a hr2 hx hy)
        (derivativeHolderEnvelope_orderFour_modulus c hfour (P.lam a)
          (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
          (hP.recurrenceHolder a) hv ⟨4 - r, by omega⟩ hx hy)
      have he : (Nat.choose 4 r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (4 - r) (P.lam a) (Icc (0 : ℝ) 1) x -
        (Nat.choose 4 r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (4 - r) (P.lam a) (Icc (0 : ℝ) 1) y =
        (Nat.choose 4 r : ℝ) *
          (iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin (4 - r) (P.lam a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin (4 - r) (P.lam a) (Icc (0 : ℝ) 1) y) := by ring
      rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hm.trans_eq (by ring)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [productHolderEnvelope, hfour, Finset.sum_mul, mul_assoc]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
