module
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Basic
public import CausalSmith.Stat.STAT_DiscreteBudgetvalueCurve_Research.Helpers.TwoSampleL1
public import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TCausalOptimalValueCorollary

/-! Real atom sums for the observed margin of the explicit paired law. -/

@[expose] public section

namespace CausalSmith.Stat.DiscreteBudgetvalueCurve

open scoped BigOperators

/-- Summing out both potential outcomes gives the paired observed atom mass. With [the specified inputs and conditions](hyp:k,r,theta,i,sigma,a,y), [the stated relationship holds](goal). -/
-- @node: pairedFullMass_observedSum
lemma pairedFullMass_observedSum {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (i : Fin k) (sigma a y : Bool) :
    (∑ y0 : Bool, ∑ y1 : Bool,
      pairedFullMass r theta
        ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))
          (if sigma then 1 else 0, i), a, y, y0, y1)) =
      r.1 i / 4 * bernoulliMass
        (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i
         else 1 / 4) y := by
  classical
  have hk : k ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)
  cases sigma <;> cases a <;> cases y <;>
    simp [pairedFullMass, bernoulliMass, finProdFinEquiv,
    Fin.modNat, Fin.divNat, Nat.mod_eq_of_lt i.isLt, hk] <;> ring

/-- Every atom of the paired full-data construction has nonnegative mass. With [the specified inputs and conditions](hyp:k,r,theta,z), [the stated relationship holds](goal). -/
-- @node: pairedFullMass_nonneg
lemma pairedFullMass_nonneg {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (z : FullObs (2 * k)) :
    0 ≤ pairedFullMass r theta z := by
  let i := ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).2
  have ht := theta.2 i
  have hr := r.2.1 i
  simp only [Set.mem_Icc] at ht
  have hmu : 0 ≤ (1 / 2 : ℝ) +
      (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
       then 1 else -1) * theta.1 i ∧
      (1 / 2 : ℝ) +
      (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
       then 1 else -1) * theta.1 i ≤ 1 := by
    split_ifs <;> constructor <;> nlinarith [ht.1, ht.2]
  have h0 : 0 ≤ bernoulliMass (1 / 4) z.2.2.2.1 := by
    cases z.2.2.2.1 <;> norm_num [bernoulliMass]
  have h1 : 0 ≤ bernoulliMass
      ((1 / 2 : ℝ) +
        (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1).1 = 0
         then 1 else -1) * theta.1 i) z.2.2.2.2 := by
    cases z.2.2.2.2 <;> simp only [bernoulliMass, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [hmu.1, hmu.2]
  by_cases hy : z.2.2.1 = (if z.2.1 then z.2.2.2.2 else z.2.2.2.1)
  · simpa [pairedFullMass, hy, i] using
      (mul_nonneg (mul_nonneg (div_nonneg hr (by norm_num)) h0) h1)
  · simp [pairedFullMass, hy]

/-- The real mass of an explicit paired-law atom is its defining mass. With [the specified inputs and conditions](hyp:k,r,theta,z), [the stated relationship holds](goal). -/
-- @node: pairedLaw_fullMass
lemma pairedLaw_fullMass {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (z : FullObs (2 * k)) :
    fullMass (pairedLaw r theta) z = pairedFullMass r theta z := by
  change (ENNReal.ofReal (pairedFullMass r theta z)).toReal = _
  exact ENNReal.toReal_ofReal (pairedFullMass_nonneg r theta z)

/-- An observed paired-law atom has the stated Bernoulli mass. With [the specified inputs and conditions](hyp:k,r,theta,i,sigma,a,y), [the stated relationship holds](goal). -/
-- @node: pairedLaw_observedAtom
lemma pairedLaw_observedAtom {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (i : Fin k) (sigma a y : Bool) :
    jointMass (observedMarginal (pairedLaw r theta))
      ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))
        (if sigma then 1 else 0, i)) a y =
      r.1 i / 4 * bernoulliMass
        (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i
         else 1 / 4) y := by
  dsimp only [jointMass, observedMarginal]
  rw [CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.observedMarginal_jointMass]
  simp only [pairedLaw_fullMass]
  exact pairedFullMass_observedSum r theta i sigma a y

/-- Conditional mass of one generated record from one draw of each input law. -/
-- @node: pairedKernelAtom
noncomputable def pairedKernelAtom {k : ℕ} (xy : Fin k × Fin k) (z : Obs (2 * k)) : ℝ :=
  let pair := (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm z.1
  ((if pair.2 = xy.1 then
      bernoulliMass
        (if z.2.1 then 1 / 2 + (if pair.1 = 0 then (1 : ℝ) else -1) / 8
         else 1 / 4) z.2.2 else 0) +
    (if pair.2 = xy.2 then
      bernoulliMass
        (if z.2.1 then 1 / 2 - (if pair.1 = 0 then (1 : ℝ) else -1) / 8
         else 1 / 4) z.2.2 else 0)) / 8

/-- The one-record kernel mass is nonnegative. With [the specified inputs and conditions](hyp:k,xy,z), [the stated relationship holds](goal). -/
-- @node: pairedKernelAtom_nonneg
lemma pairedKernelAtom_nonneg {k : ℕ} (xy : Fin k × Fin k) (z : Obs (2 * k)) :
    0 ≤ pairedKernelAtom xy z := by
  rcases z with ⟨j, a, y⟩
  by_cases hs : ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
  · have hs' : j.divNat = 0 := by simpa [finProdFinEquiv] using hs
    cases a <;> cases y <;>
      simp [pairedKernelAtom, bernoulliMass, finProdFinEquiv, hs'] <;> positivity
  · have hs' : j.divNat ≠ 0 := by simpa [finProdFinEquiv] using hs
    cases a <;> cases y <;>
      simp [pairedKernelAtom, bernoulliMass, finProdFinEquiv, hs'] <;> positivity

/-- The conditional record masses sum to one. With [the specified inputs and conditions](hyp:k,xy), [the stated relationship holds](goal). -/
-- @node: pairedKernelAtom_sum
lemma pairedKernelAtom_sum {k : ℕ} (xy : Fin k × Fin k) :
    ∑ z : Obs (2 * k), pairedKernelAtom xy z = 1 := by
  classical
  simp only [Fintype.sum_prod_type]
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))]
  simp [pairedKernelAtom, bernoulliMass, Fintype.sum_prod_type]
  norm_num [Finset.sum_add_distrib]
  simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib]
  simp
  ring

/-- The conditional distribution of one record given a draw from each input law. -/
-- @node: pairedKernelPMF
noncomputable def pairedKernelPMF {k : ℕ} (xy : Fin k × Fin k) : PMF (Obs (2 * k)) :=
  PMF.ofFintype (fun z => ENNReal.ofReal (pairedKernelAtom xy z)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => pairedKernelAtom_nonneg xy z),
      pairedKernelAtom_sum]
    norm_num)

/-- Independent conditional randomization at each sample coordinate. -/
-- @node: pairedSampleKernel
noncomputable def pairedSampleKernel {k : ℕ} (n : ℕ)
    (x : (Fin n → Fin k) × (Fin n → Fin k)) : PMF (Fin n → Obs (2 * k)) :=
  (MeasureTheory.Measure.pi
    (fun t : Fin n => (pairedKernelPMF (x.1 t, x.2 t)).toMeasure)).toPMF

/-- The conditional sample law factors over record coordinates. With [the specified inputs and conditions](hyp:k,n,x,z), [the stated relationship holds](goal). -/
-- @node: pairedSampleKernel_singleton
lemma pairedSampleKernel_singleton {k : ℕ} (n : ℕ)
    (x : (Fin n → Fin k) × (Fin n → Fin k)) (z : Fin n → Obs (2 * k)) :
    pairedSampleKernel n x z =
      ∏ t : Fin n, ENNReal.ofReal (pairedKernelAtom (x.1 t, x.2 t) (z t)) := by
  simp only [pairedSampleKernel, MeasureTheory.Measure.toPMF_apply,
    MeasureTheory.Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro t _
  rw [PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)]
  rfl

/-- Mixing the conditional atom over independent input labels gives the target atom. With [the specified inputs and conditions](hyp:k,R,S,i,u,v), [the stated relationship holds](goal). -/
-- @node: pairedKernelMix_aux
lemma pairedKernelMix_aux {k : ℕ} (R S : ProbabilitySimplex k)
    (i : Fin k) (u v : ℝ) :
    (∑ xy : Fin k × Fin k, R.1 xy.1 * S.1 xy.2 *
      ((if i = xy.1 then u else 0) + (if i = xy.2 then v else 0)) / 8) =
      (R.1 i * u + S.1 i * v) / 8 := by
  classical
  simp only [Fintype.sum_prod_type, div_eq_mul_inv, mul_add, mul_assoc,
    Finset.sum_add_distrib, Finset.sum_mul]
  simp [Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, R.2.2, S.2.2]

/-- Mixing the conditional atom over independent input labels gives the target atom. With [the specified inputs and conditions](hyp:k,R,S,i,sigma,a,y), [the stated relationship holds](goal). -/
-- @node: pairedKernelAtom_mixed
lemma pairedKernelAtom_mixed {k : ℕ} (R S : ProbabilitySimplex k)
    (i : Fin k) (sigma a y : Bool) :
    (∑ xy : Fin k × Fin k, R.1 xy.1 * S.1 xy.2 *
      pairedKernelAtom xy
        ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k))
          (if sigma then 1 else 0, i), a, y)) =
      (R.1 i * bernoulliMass
          (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) / 8
           else 1 / 4) y +
        S.1 i * bernoulliMass
          (if a then 1 / 2 - (if sigma then (-1 : ℝ) else 1) / 8
           else 1 / 4) y) / 8 := by
  classical
  have h := pairedKernelMix_aux R S i
    (bernoulliMass (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) / 8
      else 1 / 4) y)
    (bernoulliMass (if a then 1 / 2 - (if sigma then (-1 : ℝ) else 1) / 8
      else 1 / 4) y)
  cases sigma <;>
    simpa [pairedKernelAtom, mul_div_assoc] using h

/-- Pairing the two input samples coordinatewise is an equivalence. -/
-- @node: pairedSampleEquiv
def pairedSampleEquiv (n k : ℕ) :
    ((Fin n → Fin k) × (Fin n → Fin k)) ≃ (Fin n → Fin k × Fin k) where
  toFun x t := (x.1 t, x.2 t)
  invFun w := (fun t => (w t).1, fun t => (w t).2)
  left_inv := by intro x; cases x; rfl
  right_inv := by intro w; funext t; exact Prod.eta (w t)

/-- Finite product sums factor coordinatewise for paired samples. With [the specified inputs and conditions](hyp:n,k,R,S,z), [the stated relationship holds](goal). -/
-- @node: pairedSample_realFactorization
lemma pairedSample_realFactorization {n k : ℕ}
    (R S : ProbabilitySimplex k) (z : Fin n → Obs (2 * k)) :
    (∑ x : (Fin n → Fin k) × (Fin n → Fin k),
      (∏ t, R.1 (x.1 t)) * (∏ t, S.1 (x.2 t)) *
        (∏ t, pairedKernelAtom (x.1 t, x.2 t) (z t))) =
      ∏ t : Fin n, (∑ xy : Fin k × Fin k,
        R.1 xy.1 * S.1 xy.2 * pairedKernelAtom xy (z t)) := by
  classical
  rw [Fintype.prod_sum]
  rw [← Equiv.sum_comp (pairedSampleEquiv n k)]
  apply Finset.sum_congr rfl
  intro x _
  simp only [pairedSampleEquiv, Equiv.coe_fn_mk]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- The fixed-sample kernel mixture factors into its one-record marginals. With [the specified inputs and conditions](hyp:n,k,R,S,z), [the stated relationship holds](goal). -/
-- @node: pairedSampleKernel_mixed
lemma pairedSampleKernel_mixed {n k : ℕ} (R S : ProbabilitySimplex k)
    (z : Fin n → Obs (2 * k)) :
    (∑ x : (Fin n → Fin k) × (Fin n → Fin k),
      (twoSampleLaw n (R, S)) {x} * pairedSampleKernel n x z) =
      ∏ t : Fin n, ENNReal.ofReal
        (∑ xy : Fin k × Fin k, R.1 xy.1 * S.1 xy.2 *
          pairedKernelAtom xy (z t)) := by
  classical
  have hterm_nonneg (x : (Fin n → Fin k) × (Fin n → Fin k)) :
      0 ≤ (∏ t, R.1 (x.1 t)) * (∏ t, S.1 (x.2 t)) *
        (∏ t, pairedKernelAtom (x.1 t, x.2 t) (z t)) := by
    exact mul_nonneg
      (mul_nonneg
        (Finset.prod_nonneg (fun t _ => R.2.1 (x.1 t)))
        (Finset.prod_nonneg (fun t _ => S.2.1 (x.2 t))))
      (Finset.prod_nonneg (fun t _ => pairedKernelAtom_nonneg (x.1 t, x.2 t) (z t)))
  have hmix_nonneg (t : Fin n) :
      0 ≤ ∑ xy : Fin k × Fin k,
        R.1 xy.1 * S.1 xy.2 * pairedKernelAtom xy (z t) := by
    apply Finset.sum_nonneg
    intro xy _
    exact mul_nonneg (mul_nonneg (R.2.1 xy.1) (S.2.1 xy.2))
      (pairedKernelAtom_nonneg xy (z t))
  calc
    _ = ∑ x : (Fin n → Fin k) × (Fin n → Fin k),
        ENNReal.ofReal ((∏ t, R.1 (x.1 t)) * (∏ t, S.1 (x.2 t)) *
          (∏ t, pairedKernelAtom (x.1 t, x.2 t) (z t))) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [twoSampleLaw_singleton, pairedSampleKernel_singleton]
            simp only [simplexPMF,
              Causalean.Stat.Minimax.Multinomial.TwoSampleL1.simplexPMF,
              PMF.ofFintype_apply]
            have hR : 0 ≤ ∏ t, R.1 (x.1 t) :=
              Finset.prod_nonneg (fun t _ => R.2.1 (x.1 t))
            have hS : 0 ≤ ∏ t, S.1 (x.2 t) :=
              Finset.prod_nonneg (fun t _ => S.2.1 (x.2 t))
            rw [ENNReal.ofReal_mul (mul_nonneg hR hS), ENNReal.ofReal_mul hR,
              ENNReal.ofReal_prod_of_nonneg (fun t _ => R.2.1 (x.1 t)),
              ENNReal.ofReal_prod_of_nonneg (fun t _ => S.2.1 (x.2 t)),
              ENNReal.ofReal_prod_of_nonneg
                (fun t _ => pairedKernelAtom_nonneg (x.1 t, x.2 t) (z t))]
    _ = ENNReal.ofReal
        (∑ x : (Fin n → Fin k) × (Fin n → Fin k),
          (∏ t, R.1 (x.1 t)) * (∏ t, S.1 (x.2 t)) *
            (∏ t, pairedKernelAtom (x.1 t, x.2 t) (z t))) := by
              rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hterm_nonneg x)]
    _ = ENNReal.ofReal (∏ t : Fin n,
        (∑ xy : Fin k × Fin k, R.1 xy.1 * S.1 xy.2 *
          pairedKernelAtom xy (z t))) := by
            rw [pairedSample_realFactorization]
    _ = _ := ENNReal.ofReal_prod_of_nonneg (fun t _ => hmix_nonneg t)

/-- The explicit paired law has the prescribed mass in each covariate cell. With [the specified inputs and conditions](hyp:k,r,theta,j), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poCellMass
lemma pairedLaw_poCellMass {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k)) :
    poCellMass (pairedLaw r theta) j =
      r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 := by
  simp [poCellMass,
    CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.poCellMass,
    pairedLaw_fullMass, pairedFullMass, bernoulliMass]
  ring

/-- Both arms of a paired cell have equal treatment mass. With [the specified inputs and conditions](hyp:k,r,theta,j,a), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poTreatmentAtom
lemma pairedLaw_poTreatmentAtom {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k)) (a : Bool) :
    poTreatmentAtom (pairedLaw r theta) j a =
      r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 4 := by
  cases a <;>
    simp [poTreatmentAtom, pairedLaw_fullMass, pairedFullMass, bernoulliMass] <;> ring

/-- Joint potential-outcome and treatment atoms factor under the paired law. With [the specified inputs and conditions](hyp:k,r,theta,j,a,y0,y1), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poJointAtom
lemma pairedLaw_poJointAtom {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k))
    (a y0 y1 : Bool) :
    poJointAtom (pairedLaw r theta) j a y0 y1 =
      r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 4 *
        bernoulliMass (1 / 4) y0 *
        bernoulliMass
          (1 / 2 +
            (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
             then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) y1 := by
  cases a <;> cases y0 <;> cases y1 <;>
    simp [poJointAtom, pairedLaw_fullMass, pairedFullMass, bernoulliMass]

/-- The paired potential-outcome atom is twice either arm's joint atom. With [the specified inputs and conditions](hyp:k,r,theta,j,y0,y1), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poPairAtom
lemma pairedLaw_poPairAtom {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k)) (y0 y1 : Bool) :
    poPairAtom (pairedLaw r theta) j y0 y1 =
      r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
        bernoulliMass (1 / 4) y0 *
        bernoulliMass
          (1 / 2 +
            (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
             then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) y1 := by
  change (∑ a : Bool, poJointAtom (pairedLaw r theta) j a y0 y1) = _
  simp [pairedLaw_poJointAtom]
  ring

/-- The explicit paired law obeys consistency and joint exchangeability. With [the specified inputs and conditions](hyp:k,r,theta), [the stated relationship holds](goal). -/
-- @node: pairedLaw_causalRestrictions
lemma pairedLaw_causalRestrictions {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) :
    Consistency (pairedLaw r theta) ∧
      ConditionalExchangeability (pairedLaw r theta) := by
  constructor
  · intro z hz
    rw [pairedLaw_fullMass]
    simp [pairedFullMass, hz]
  · intro j a y0 y1
    rw [pairedLaw_poJointAtom, pairedLaw_poCellMass,
      pairedLaw_poTreatmentAtom, pairedLaw_poPairAtom]
    ring

/-- The numerator of a paired cell's conditional potential-outcome mean. With [the specified inputs and conditions](hyp:k,r,theta,j,a), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poNumerator
lemma pairedLaw_poNumerator {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k)) (a : Fin 2) :
    (∑ arm : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      (if (if a = 0 then y0 else y1) then 1 else 0 : ℝ) *
        fullMass (pairedLaw r theta) (j, arm, y, y0, y1)) =
      r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2 *
        (if a = 0 then (1 / 4 : ℝ)
         else 1 / 2 +
            (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
             then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
  fin_cases a <;>
    simp [pairedLaw_fullMass, pairedFullMass, bernoulliMass] <;> ring

/-- Weighted conditional means of the explicit paired law match its parameters. With [the specified inputs and conditions](hyp:k,r,theta,j,a), [the stated relationship holds](goal). -/
-- @node: pairedLaw_poRegression_weighted
lemma pairedLaw_poRegression_weighted {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) (j : Fin (2 * k)) (a : Fin 2) :
    poCellMass (pairedLaw r theta) j *
      poRegression (pairedLaw r theta) a j =
      poCellMass (pairedLaw r theta) j *
        (if a = 0 then (1 / 4 : ℝ)
         else 1 / 2 +
            (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
             then 1 else -1) *
              theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2) := by
  let p := r.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2 / 2
  let mu : ℝ := if a = 0 then 1 / 4
    else 1 / 2 +
      (if ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).1 = 0
       then 1 else -1) *
        theta.1 ((finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).symm j).2
  change poCellMass (pairedLaw r theta) j *
      ((∑ arm : Bool, ∑ y : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
        (if (if a = 0 then y0 else y1) then 1 else 0 : ℝ) *
          fullMass (pairedLaw r theta) (j, arm, y, y0, y1)) /
        poCellMass (pairedLaw r theta) j) = _
  rw [pairedLaw_poCellMass, pairedLaw_poNumerator]
  change p * (p * mu / p) = p * mu
  by_cases hp : p = 0
  · simp [hp]
  · field_simp

/-- The explicit paired law is one of the admissible causal completions. With [the specified inputs and conditions](hyp:k,r,theta), [the stated relationship holds](goal). -/
-- @node: pairedLaw_completion
lemma pairedLaw_completion {k : ℕ} (r : ProbabilitySimplex k)
    (theta : PairedContrasts k) : PairedCompletion (pairedLaw r theta) r theta := by
  refine ⟨(pairedLaw_causalRestrictions r theta).1,
    (pairedLaw_causalRestrictions r theta).2, ?_⟩
  intro j
  refine ⟨pairedLaw_poCellMass r theta j, ?_, ?_, ?_⟩
  · rw [pairedLaw_poTreatmentAtom, pairedLaw_poCellMass]
    ring
  · simpa using pairedLaw_poRegression_weighted r theta j 0
  · simpa using pairedLaw_poRegression_weighted r theta j 1

/-- The fixed-sample observed law factors into its one-record atom masses. With [the specified inputs and conditions](hyp:d,P,n,z), [the stated relationship holds](goal). -/
-- @node: productLaw_singleton_budget
lemma productLaw_singleton_budget {d : ℕ} (P : DiscreteLaw d) (n : ℕ)
    (z : Fin n → Obs d) :
    productLaw P n {z} = ∏ t : Fin n, P.pmf (z t) := by
  simp only [productLaw, CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched.productLaw,
    MeasureTheory.Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro t _
  exact PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _)

/-- The normalized contrast has the exact signed mass needed by the sampling kernel. With [the specified inputs and conditions](hyp:k,R,S,r,theta,hr,htheta,i), [the stated relationship holds](goal). -/
-- @node: normalizedPairedMassContrast
lemma normalizedPairedMassContrast {k : ℕ} (R S r : ProbabilitySimplex k)
    (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)))
    (i : Fin k) :
    r.1 i * theta.1 i = (R.1 i - S.1 i) / 16 := by
  rw [hr i, htheta i]
  by_cases h : R.1 i + S.1 i = 0
  · have hR : R.1 i = 0 := by linarith [R.2.1 i, S.2.1 i]
    have hS : S.1 i = 0 := by linarith [R.2.1 i, S.2.1 i]
    simp [h, hR, hS]
  · simp only [h, ↓reduceIte]
    field_simp
    nlinarith [h]

/-- The treated outcome atom is a fixed mixture of the two input-label atoms. With [the specified inputs and conditions](hyp:k,R,S,r,theta,hr,htheta,i,sigma,y), [the stated relationship holds](goal). -/
-- @node: normalizedPairedTreatedAtom
lemma normalizedPairedTreatedAtom {k : ℕ} (R S r : ProbabilitySimplex k)
    (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)))
    (i : Fin k) (sigma y : Bool) :
    r.1 i * bernoulliMass
        (1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i) y =
      (R.1 i * bernoulliMass
          (1 / 2 + (if sigma then (-1 : ℝ) else 1) / 8) y +
        S.1 i * bernoulliMass
          (1 / 2 - (if sigma then (-1 : ℝ) else 1) / 8) y) / 2 := by
  have hm := normalizedPairedMassContrast R S r theta hr htheta i
  have hr' := hr i
  cases sigma <;> cases y <;> simp only [Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, bernoulliMass] <;> nlinarith

/-- Every observed atom of the normalized pair is an equal mixture of
the corresponding atoms produced from the two input labels. With [the specified inputs and conditions](hyp:k,R,S,r,theta,hr,htheta,i,sigma,a,y), [the stated relationship holds](goal). -/
-- @node: normalizedPairedObservedAtom
lemma normalizedPairedObservedAtom {k : ℕ} (R S r : ProbabilitySimplex k)
    (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)))
    (i : Fin k) (sigma a y : Bool) :
    r.1 i / 4 * bernoulliMass
        (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i
         else 1 / 4) y =
      (R.1 i * bernoulliMass
          (if a then 1 / 2 + (if sigma then (-1 : ℝ) else 1) / 8
           else 1 / 4) y +
        S.1 i * bernoulliMass
          (if a then 1 / 2 - (if sigma then (-1 : ℝ) else 1) / 8
           else 1 / 4) y) / 8 := by
  cases a
  · rw [hr i]
    cases y <;> simp [bernoulliMass] <;> ring
  · have h := normalizedPairedTreatedAtom R S r theta hr htheta i sigma y
    simp only [↓reduceIte]
    calc
      r.1 i / 4 * bernoulliMass
          (1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i) y =
        (r.1 i * bernoulliMass
          (1 / 2 + (if sigma then (-1 : ℝ) else 1) * theta.1 i) y) / 4 := by ring
      _ = ((R.1 i * bernoulliMass
          (1 / 2 + (if sigma then (-1 : ℝ) else 1) / 8) y +
        S.1 i * bernoulliMass
          (1 / 2 - (if sigma then (-1 : ℝ) else 1) / 8) y) / 2) / 4 := by rw [h]
      _ = _ := by ring

/-- The kernel mixture is exactly each normalized paired observed atom. With [the specified inputs and conditions](hyp:k,R,S,r,theta,hr,htheta,z), [the stated relationship holds](goal). -/
-- @node: pairedKernelAtom_mixed_observed
lemma pairedKernelAtom_mixed_observed {k : ℕ}
    (R S r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)))
    (z : Obs (2 * k)) :
    (∑ xy : Fin k × Fin k,
      R.1 xy.1 * S.1 xy.2 * pairedKernelAtom xy z) =
      jointMass (observedMarginal (pairedLaw r theta)) z.1 z.2.1 z.2.2 := by
  rcases z with ⟨j, a, y⟩
  obtain ⟨⟨s, i⟩, rfl⟩ :=
    (finProdFinEquiv : Fin 2 × Fin k ≃ Fin (2 * k)).surjective j
  fin_cases s
  · exact (pairedKernelAtom_mixed R S i false a y).trans
      ((normalizedPairedObservedAtom R S r theta hr htheta i false a y).symm.trans
        (pairedLaw_observedAtom r theta i false a y).symm)
  · exact (pairedKernelAtom_mixed R S i true a y).trans
      ((normalizedPairedObservedAtom R S r theta hr htheta i true a y).symm.trans
        (pairedLaw_observedAtom r theta i true a y).symm)

/-- The parameter-free fixed-sample kernel reproduces the normalized observed law. With [the specified inputs and conditions](hyp:n,k,R,S,r,theta,hr,htheta,z), [the stated relationship holds](goal). -/
-- @node: pairedSampleKernel_reproduces
lemma pairedSampleKernel_reproduces {n k : ℕ}
    (R S r : ProbabilitySimplex k) (theta : PairedContrasts k)
    (hr : ∀ i, r.1 i = (R.1 i + S.1 i) / 2)
    (htheta : ∀ i, theta.1 i =
      if R.1 i + S.1 i = 0 then 0
      else (R.1 i - S.1 i) / (8 * (R.1 i + S.1 i)))
    (z : Fin n → Obs (2 * k)) :
    (∑ x : (Fin n → Fin k) × (Fin n → Fin k),
      (twoSampleLaw n (R, S)) {x} * pairedSampleKernel n x z) =
      (productLaw (observedMarginal (pairedLaw r theta)) n) {z} := by
  rw [pairedSampleKernel_mixed, productLaw_singleton_budget]
  apply Finset.prod_congr rfl
  intro t _
  rw [pairedKernelAtom_mixed_observed R S r theta hr htheta]
  change ENNReal.ofReal
      (((observedMarginal (pairedLaw r theta)).pmf (z t)).toReal) = _
  exact ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)

end CausalSmith.Stat.DiscreteBudgetvalueCurve
