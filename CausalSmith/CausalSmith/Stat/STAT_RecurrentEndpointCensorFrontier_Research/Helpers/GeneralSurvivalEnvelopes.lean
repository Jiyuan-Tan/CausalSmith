module
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.SecondOrderSurvivalEnvelopes
public import CausalSmith.Stat.STAT_RecurrentEndpointCensorFrontier_Research.Helpers.GeneralJetEnvelopes

/-! # Arbitrary-order survival and target envelopes

The differentiated hazard equation and Leibniz rule give the declared arbitrary-order
survival and target Hölder envelopes from the sharp one-sided jet bounds.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.RecurrentEndpointCensorFrontier

/-- Sharp arbitrary-order hazard interpolation supplies all survival jets
through one more than the hazard order via the hazard equation. -/
-- @node: survival_jet_bound
lemma survival_jet_bound (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    {j : ℕ} (hj : j ≤ holderOrder c + 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) t| ≤
      survivalDerivativeEnvelope c j := by
  apply survival_jet_bound_of_hazard_jets c P hP a
    (derivativeEnvelope_nonneg c 
      (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le) _ (by omega) ht
  intro k hk u hu
  exact death_jet_bound c P hP a hu ⟨k, by omega⟩

/-- Lower survival jets inherit the Hölder modulus of their next-jet bounds. -/
-- @node: survival_lower_jet_holder
lemma survival_lower_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    {j : ℕ} (hj : j < (holderOrder c)) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - (holderOrder c)) := by
  have hα := holderOrder_remainder_exponent c
  have hD := derivativeEnvelope_nonneg c 
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hc : ContDiffOn ℝ (j + 1 : ℕ) (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by
      exact_mod_cast (show j + 1 ≤ (holderOrder c + 1) by omega))
  have hb := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
    j (c.beta - (holderOrder c)) 0 1 (survivalDerivativeEnvelope c (j + 1)) hα.1 hα.2
    (by norm_num) (survivalDerivativeEnvelope_nonneg c hD _) (survival P a)
    (by simpa only [zero_add, Nat.cast_add, Nat.cast_one] using hc)
    (by
      intro t ht
      simpa only [zero_add] using survival_jet_bound c P hP a (j := j + 1)
        (by omega) (by simpa only [zero_add] using ht))
    x (by simpa only [zero_add] using hx) y (by simpa only [zero_add] using hy)
  simpa only [survivalHolderEnvelope, hj, ↓reduceIte, zero_add,
    Real.one_rpow, mul_one] using hb

/-- The positive-order top survival jet inherits its exact product modulus
from the differentiated hazard equation and the bounded lower jets. -/
-- @node: survival_top_jet_holder
lemma survival_top_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (hk : 0 < holderOrder c) (a : Arm)
    {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin (holderOrder c) (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin (holderOrder c) (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c (holderOrder c) *
        |x - y| ^ (c.beta - holderOrder c) := by
  let k := holderOrder c
  let D := derivativeEnvelope c c.dMax c.Ld
  have hD : 0 ≤ D := derivativeEnvelope_nonneg c
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - k) := Real.rpow_nonneg (abs_nonneg _) _
  have hv : ∀ t ∈ Icc (0 : ℝ) 1, |P.hazard a t| ≤ c.dMax := by
    intro t ht
    rw [abs_of_nonneg (c.dMin_pos.le.trans (hP.deathBounds a t ht).1)]
    exact (hP.deathBounds a t ht).2
  have hdmod (j : Fin (k + 1)) := derivativeHolderEnvelope_modulus c
    (P.hazard a) (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
    (hP.deathHolder a) hv j hx hy
  have hterm (r : ℕ) (hr : r < k) :
      |iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) y| ≤
      (D * survivalDerivativeEnvelope c (k - r) +
        derivativeHolderEnvelope c c.dMax c.Ld r *
          survivalDerivativeEnvelope c (k - 1 - r)) * |x - y| ^ (c.beta - k) := by
    have hm := sharpProduct_increment_bound hD
      (survivalDerivativeEnvelope_nonneg c hD (k - 1 - r)) hD hq
      (death_jet_bound c P hP a hy ⟨r, by omega⟩)
      (survival_jet_bound c P hP a (by dsimp [k] at *; omega) hx)
      (by simpa only [derivativeHolderEnvelope, show r < holderOrder c from hr,
        ↓reduceIte] using hdmod ⟨r, by omega⟩)
      (survival_lower_jet_holder c P hP a (by dsimp [k] at *; omega) hx hy)
    have he : survivalHolderEnvelope c (k - 1 - r) =
        survivalDerivativeEnvelope c (k - r) := by
      simp only [survivalHolderEnvelope, show k - 1 - r < holderOrder c by
        dsimp [k] at *; omega, ↓reduceIte]
      rw [show k - 1 - r + 1 = k - r by omega]
    simpa only [he, derivativeHolderEnvelope, show r < holderOrder c from hr,
      ↓reduceIte, D, mul_comm, add_comm]
      using hm
  have hkk : k - 1 + 1 = k := by omega
  have hxrec := survival_modelClass_jet_recurrence c P hP a
    (j := k - 1) (by dsimp [k]; omega) hx
  have hyrec := survival_modelClass_jet_recurrence c P hP a
    (j := k - 1) (by dsimp [k]; omega) hy
  rw [hkk] at hxrec hyrec
  rw [hxrec, hyrec, neg_sub_neg, abs_sub_comm, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ r ∈ Finset.range k, (Nat.choose (k - 1) r : ℝ) *
        ((D * survivalDerivativeEnvelope c (k - r) +
          derivativeHolderEnvelope c c.dMax c.Ld r *
            survivalDerivativeEnvelope c (k - 1 - r)) * |x - y| ^ (c.beta - k)) := by
      apply Finset.sum_le_sum
      intro r hr
      rw [show (Nat.choose (k - 1) r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
        (Nat.choose (k - 1) r : ℝ) *
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) y =
        (Nat.choose (k - 1) r : ℝ) *
          (iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (P.hazard a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin (k - 1 - r) (survival P a) (Icc (0 : ℝ) 1) y) by ring,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hterm r (Finset.mem_range.mp hr))
        (Nat.cast_nonneg _)
    _ = _ := by
      simp only [survivalHolderEnvelope, lt_self_iff_false, ↓reduceIte,
        show holderOrder c ≠ 0 by omega, Finset.sum_mul, mul_assoc]
      rfl

/-- Every survival jet has the declared Hölder modulus. -/
-- @node: survival_jet_holder
lemma survival_jet_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm)
    {j : ℕ} (hj : j ≤ (holderOrder c)) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    |iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) x -
      iteratedDerivWithin j (survival P a) (Icc (0 : ℝ) 1) y| ≤
      survivalHolderEnvelope c j * |x - y| ^ (c.beta - (holderOrder c)) := by
  by_cases hlt : j < (holderOrder c)
  · exact survival_lower_jet_holder c P hP a hlt hx hy
  · have he : j = (holderOrder c) := by omega
    subst j
    by_cases hk : holderOrder c = 0
    · have hα := holderOrder_remainder_exponent c
      have hc := survival_modelClass_contDiffOn c P hP a
      have hnext : ∀ t ∈ Icc (0 : ℝ) 1,
          |iteratedDerivWithin 1 (survival P a) (Icc (0 : ℝ) 1) t| ≤ c.dMax := by
        intro t ht
        simpa [survivalDerivativeEnvelope, derivativeEnvelope, hk] using
          survival_jet_bound c P hP a (j := 1) (by omega) ht
      have hb := Causalean.Mathlib.Analysis.Calculus.HolderTaylor.lower_jet_holder_of_next_bound
        0 (c.beta - holderOrder c) 0 1 c.dMax hα.1 hα.2 (by norm_num)
        (c.dMin_pos.le.trans c.dMin_lt.le) (survival P a)
        (by simpa [hk] using hc) (by simpa using hnext)
        x (by simpa using hx) y (by simpa using hy)
      simpa [hk, survivalHolderEnvelope] using hb
    · exact survival_top_jet_holder c P hP (Nat.pos_of_ne_zero hk) a hx hy

/-- The declared product modulus is nonnegative at every order. -/
-- @node: productHolderEnvelope_nonneg
lemma productHolderEnvelope_nonneg (c : ClassConstants)
    : 0 ≤ productHolderEnvelope c := by
  have hD := derivativeEnvelope_nonneg c 
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_nonneg c 
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

/-- Leibniz's rule assembles the arbitrary-order target-product modulus using
exactly the class's declared hazard and recurrence envelopes. -/
-- @node: survival_product_holder
lemma survival_product_holder (c : ClassConstants) (P : SubjectLaw)
    (hP : ModelClass c P) (a : Arm) :
    HolderSeminormLe (holderOrder c) (c.beta - (holderOrder c)) (productHolderEnvelope c)
      (fun t => survival P a t * P.lam a t) := by
  have hS : ContDiffOn ℝ (holderOrder c) (survival P a) (Icc (0 : ℝ) 1) :=
    (survival_modelClass_contDiffOn c P hP a).of_le (by
      exact_mod_cast (show holderOrder c ≤ holderOrder c + 1 by omega))
  have hL : ContDiffOn ℝ (holderOrder c) (P.lam a) (Icc (0 : ℝ) 1) := by
    simpa only [] using (hP.recurrenceHolder a).1
  refine ⟨hS.mul hL, ?_⟩
  intro x hx y hy
  have hD := derivativeEnvelope_nonneg c 
    (c.dMin_pos.le.trans c.dMin_lt.le) c.Ld_pos.le
  have hR := derivativeEnvelope_nonneg c 
    (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
  have hq : 0 ≤ |x - y| ^ (c.beta - (holderOrder c)) := Real.rpow_nonneg (abs_nonneg _) _
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
    _ ≤ ∑ r ∈ Finset.range ((holderOrder c) + 1), (Nat.choose (holderOrder c) r : ℝ) *
        ((survivalDerivativeEnvelope c r *
          derivativeHolderEnvelope c c.lambdaMax c.Llambda ((holderOrder c) - r) +
          survivalHolderEnvelope c r * derivativeEnvelope c c.lambdaMax c.Llambda) *
          |x - y| ^ (c.beta - (holderOrder c))) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr2 : r ≤ (holderOrder c) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      have hm := sharpProduct_increment_bound
        (survivalDerivativeEnvelope_nonneg c hD r) hR
        (survivalHolderEnvelope_nonneg c hD r) hq
        (survival_jet_bound c P hP a (j := r) (hr2.trans (by norm_num)) hy)
        (recurrence_jet_bound c P hP a hx ⟨(holderOrder c) - r, by omega⟩)
        (survival_jet_holder c P hP a hr2 hx hy)
        (derivativeHolderEnvelope_modulus c (P.lam a)
          (c.lambdaMin_pos.le.trans c.lambdaMin_lt.le) c.Llambda_pos.le
          (hP.recurrenceHolder a) hv ⟨(holderOrder c) - r, by omega⟩ hx hy)
      have he : (Nat.choose (holderOrder c) r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
          iteratedDerivWithin ((holderOrder c) - r) (P.lam a) (Icc (0 : ℝ) 1) x -
        (Nat.choose (holderOrder c) r : ℝ) *
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
          iteratedDerivWithin ((holderOrder c) - r) (P.lam a) (Icc (0 : ℝ) 1) y =
        (Nat.choose (holderOrder c) r : ℝ) *
          (iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) x *
            iteratedDerivWithin ((holderOrder c) - r) (P.lam a) (Icc (0 : ℝ) 1) x -
          iteratedDerivWithin r (survival P a) (Icc (0 : ℝ) 1) y *
            iteratedDerivWithin ((holderOrder c) - r) (P.lam a) (Icc (0 : ℝ) 1) y) := by ring
      rw [he, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hm.trans_eq (by ring)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [productHolderEnvelope, Finset.sum_mul, mul_assoc]

end CausalSmith.Stat.RecurrentEndpointCensorFrontier
