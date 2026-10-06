module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentSecondDerivative
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Bounds
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Calculus
public import Causalean.Mathlib.Analysis.Calculus.FiniteProduct.Support

/-! Coordinate finite-product jets for the component likelihood. -/
@[expose] public section
noncomputable section
open scoped BigOperators
open Causalean.Mathlib.Analysis.Calculus.FiniteProduct
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The seven record jets needed through coordinate order `(2,2)`. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the p parameter](hyp:p), [the aug parameter](hyp:aug), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def componentFactorJets (ν s : Bool) (n K M : ℕ) (p : CoefficientPairs K)
    (aug : Augmentation n K) (labels : Labels n) : FactorJets (Fin n) where
  f00 i a u := labelDensity ν K M a u ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f10 i a u := labelPropensityDerivative ν K M a u ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f20 i a u := labelPropensityCurvature ν K M a u ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f01 i a _ := labelOutcomeDerivative ν K M a ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f11 i a _ := labelMixedDerivative ν K M a ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f21 i a _ := labelMixedCurvature ν K M a ((fun _ => s),p)
    (aug.1 i) (aug.2.1 i) (labels i)
  f22 _ _ _ := 0

/-- The concrete record jets satisfy both propensity derivative links. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
lemma componentFactorJets_aChains (ν s : Bool) (n K M : ℕ) (p : CoefficientPairs K)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    AChainsAt C (componentFactorJets ν s n K M p aug labels) a u := by
  constructor
  · intro i _
    exact labelDensity_hasDerivAt_propensity ν K M a u ha _ _ _ _
  · intro i _
    exact labelPropensityDerivative_hasDerivAt ν K M a u ha _ _ _ _

/-- The concrete record jets satisfy all outcome derivative links, including affinity. [This is the stated conclusion](goal). -/
lemma componentFactorJets_uChains (ν s : Bool) (n K M : ℕ) (p : CoefficientPairs K)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    UChainsAt C (componentFactorJets ν s n K M p aug labels) a u := by
  constructor
  · intro i _
    exact labelDensity_hasDerivAt_outcome ν K M a u _ _ _ _
  · intro i _
    exact (label_second_outcome_derivatives ν K M a u _ _ _ _).1
  · intro i _
    exact labelPropensityDerivative_hasDerivAt_outcome ν K M a u _ _ _ _
  · intro i _
    exact (label_second_outcome_derivatives ν K M a u _ _ _ _).2.1
  · intro i _
    exact labelPropensityCurvature_hasDerivAt_outcome ν K M a u _ _ _ _
  · intro i _
    exact (label_second_outcome_derivatives ν K M a u _ _ _ _).2.2

/-- Every concrete record jet has the envelope required by the generic product bound. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
lemma componentFactorJets_bounds (ν s : Bool) (n K M : ℕ) (p : CoefficientPairs K)
    (a u : ℝ) (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16)
    (hu : 0 ≤ u ∧ u ≤ 1/16) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    FactorBoundsAt C (componentFactorJets ν s n K M p aug labels) a u := by
  constructor
  · intro i _
    exact labelDensity_abs_le_two_closed ν K M a u hK ha hu _ _ _ _
  · intro i _
    exact (label_propensity_derivative_bounds ν K M hK a u ha hu _ _ _ _).1
  · intro i _
    exact (label_propensity_derivative_bounds ν K M hK a u ha hu _ _ _ _).2
  · intro i _
    exact (label_mixed_derivative_bounds ν K M hK a ha _ _ _ _).1
  · intro i _
    exact (label_mixed_derivative_bounds ν K M hK a ha _ _ _ _).2.1
  · intro i _
    exact (label_mixed_derivative_bounds ν K M hK a ha _ _ _ _).2.2
  · intro i _
    simp [componentFactorJets]

/-- The existing component propensity slope is the generic first product jet. [This is the stated conclusion](goal). -/
lemma componentPropensityDerivative_eq_productJet10 (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentPropensityDerivative ν s n K M a u aug C labels =
      ∑ p : CoefficientPairs K,
        conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
          productJet10 C (componentFactorJets ν s n K M p aug labels) a u := by
  unfold componentPropensityDerivative
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  unfold productJet10
  apply Finset.sum_congr rfl
  intro i hi
  rw [leibnizTerm_cons_a C _ [] [] i a u hi]
  simp only [List.count_nil, zero_add, componentFactorJets, factorJet]
  ring

/-- The coefficient-averaged product jet of orders `(2,q)`. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def componentProductJet20 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    productJet20 C (componentFactorJets ν s n K M p aug labels) a u

/-- [The component Product Jet21 object](goal) is defined from [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def componentProductJet21 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    productJet21 C (componentFactorJets ν s n K M p aug labels) a u

/-- [The component Product Jet22 object](goal) is defined from [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def componentProductJet22 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    productJet22 C (componentFactorJets ν s n K M p aug labels) a u

/-- The previously certified `(2,0)` component curvature is the generic second product jet. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
lemma componentPropensityCurvature_eq_productJet20 (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    componentPropensityCurvature ν s n K M a u aug C labels =
      componentProductJet20 ν s n K M a u aug C labels := by
  apply (componentPropensityDerivative_hasDerivAt_propensity ν s n K M a u ha
    aug C labels).unique
  rw [funext fun b => componentPropensityDerivative_eq_productJet10 ν s n K M b u
    aug C labels]
  unfold componentProductJet20
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact hasDerivAt_productJet10_a C _ a u
    (componentFactorJets_aChains ν s n K M p a u ha aug C labels)

/-- The `(2,0)` component jet differentiates to the `(2,1)` jet. [This is the stated conclusion](goal). -/
lemma componentProductJet20_hasDerivAt_outcome (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun v => componentProductJet20 ν s n K M a v aug C labels)
      (componentProductJet21 ν s n K M a u aug C labels) u := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact hasDerivAt_productJet20_u C _ a u
    (componentFactorJets_uChains ν s n K M p a u aug C labels)

/-- The `(2,1)` component jet differentiates to the `(2,2)` jet. [This is the stated conclusion](goal). -/
lemma componentProductJet21_hasDerivAt_outcome (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun v => componentProductJet21 ν s n K M a v aug C labels)
      (componentProductJet22 ν s n K M a u aug C labels) u := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  exact hasDerivAt_productJet21_u C _ a u
    (componentFactorJets_uChains ν s n K M p a u aug C labels)

/-- The concrete fourth mixed component jet has the sharp generic envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
lemma componentProductJet22_abs_le (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |componentProductJet22 ν s n K M a u aug C labels| ≤
      256*(C.card:ℝ)^4*2^C.card := by
  apply conditionalPairWeight_abs_average_bound
  intro p
  exact productJet22_abs_le C _ a u
    (componentFactorJets_bounds ν s n K M p a u hK ha hu aug C labels)

/-- The even contrasts of the three product jets used by the rectangular remainder. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def evenProductJet20 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentProductJet20 true true n K M a u aug C labels +
    componentProductJet20 true false n K M a u aug C labels) / 2 -
    componentProductJet20 false false n K M a u aug C labels

/-- [The even Product Jet21 object](goal) is defined from [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def evenProductJet21 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentProductJet21 true true n K M a u aug C labels +
    componentProductJet21 true false n K M a u aug C labels) / 2 -
    componentProductJet21 false false n K M a u aug C labels

/-- [The even Product Jet22 object](goal) is defined from [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def evenProductJet22 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentProductJet22 true true n K M a u aug C labels +
    componentProductJet22 true false n K M a u aug C labels) / 2 -
    componentProductJet22 false false n K M a u aug C labels

/-- The old explicit curvature and the generic `(2,0)` even jet agree away from the poles. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
lemma evenDiscrepancyPropensityCurvature_eq_evenProductJet20 (n K M : ℕ)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    evenDiscrepancyPropensityCurvature n K M a u aug C labels =
      evenProductJet20 n K M a u aug C labels := by
  unfold evenDiscrepancyPropensityCurvature evenProductJet20
  rw [componentPropensityCurvature_eq_productJet20 true true n K M a u ha,
    componentPropensityCurvature_eq_productJet20 true false n K M a u ha,
    componentPropensityCurvature_eq_productJet20 false false n K M a u ha]

/-- The even `(2,0)` jet differentiates to its `(2,1)` jet. [This is the stated conclusion](goal). -/
lemma evenProductJet20_hasDerivAt_outcome (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun v => evenProductJet20 n K M a v aug C labels)
      (evenProductJet21 n K M a u aug C labels) u := by
  exact (((componentProductJet20_hasDerivAt_outcome true true n K M a u aug C labels).add
    (componentProductJet20_hasDerivAt_outcome true false n K M a u aug C labels)).div_const 2).sub
      (componentProductJet20_hasDerivAt_outcome false false n K M a u aug C labels)

/-- The even `(2,1)` jet differentiates to its `(2,2)` jet. [This is the stated conclusion](goal). -/
lemma evenProductJet21_hasDerivAt_outcome (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun v => evenProductJet21 n K M a v aug C labels)
      (evenProductJet22 n K M a u aug C labels) u := by
  exact (((componentProductJet21_hasDerivAt_outcome true true n K M a u aug C labels).add
    (componentProductJet21_hasDerivAt_outcome true false n K M a u aug C labels)).div_const 2).sub
      (componentProductJet21_hasDerivAt_outcome false false n K M a u aug C labels)

/-- Averaging the three component envelopes gives the required fourth mixed envelope. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
lemma evenProductJet22_abs_le (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 ≤ a ∧ a ≤ 1/16) (hu : 0 ≤ u ∧ u ≤ 1/16)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    |evenProductJet22 n K M a u aug C labels| ≤ 512*(C.card:ℝ)^4*2^C.card := by
  have hp := componentProductJet22_abs_le true true n K M a u hK ha hu aug C labels
  have hm := componentProductJet22_abs_le true false n K M a u hK ha hu aug C labels
  have h0 := componentProductJet22_abs_le false false n K M a u hK ha hu aug C labels
  unfold evenProductJet22
  calc
    |_ / 2 - componentProductJet22 false false n K M a u aug C labels| ≤
        |_ / 2| + |componentProductJet22 false false n K M a u aug C labels| := abs_sub _ _
    _ ≤ (|componentProductJet22 true true n K M a u aug C labels| +
        |componentProductJet22 true false n K M a u aug C labels|) / 2 +
        |componentProductJet22 false false n K M a u aug C labels| := by
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact add_le_add
        ((div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 (abs_add_le _ _)) le_rfl
    _ ≤ _ := by linarith

/-- The `(2,0)` even jet vanishes on the outcome axis throughout the amplitude rectangle. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
lemma evenProductJet20_zero_outcome (n K M : ℕ) (a : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1/16) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    evenProductJet20 n K M a 0 aug C labels = 0 := by
  have hden : 1-a^2 ≠ 0 := by
    have hd := correction_denominator_bounds a ha
    linarith [hd.2.2.1]
  rw [← evenDiscrepancyPropensityCurvature_eq_evenProductJet20 n K M a 0 hden]
  apply (evenDiscrepancy_second_propensity_jet n K M a 0 hden aug C labels).unique
  apply (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < a by linarith) (show a < 1 by linarith)]
    with b hb
  have hbden : 1-b^2 ≠ 0 := by
    have hp : 0 < (1-b)*(1+b) := mul_pos (by linarith [hb.2]) (by linarith [hb.1])
    nlinarith
  apply (evenDiscrepancy_first_propensity_jet n K M b 0 hbden aug C labels).unique
  have he : (fun t => evenDiscrepancy n K M t 0 aug C labels) = fun _ => 0 := by
    funext t
    exact (component_discrepancies_on_axes n K M t 0 aug C labels).1
  rw [he]
  exact hasDerivAt_const b 0

/-- Replace one factor by its first outcome jet, retaining its first two propensity jets. This statement assumes [the J parameter](hyp:J), [the k parameter](hyp:k). [This is the stated defined object](goal). -/
def outcomeHitFactorJets (J : FactorJets (Fin n)) (k : Fin n) : FactorJets (Fin n) where
  f00 i a u := if i = k then J.f01 i a u else J.f00 i a u
  f10 i a u := if i = k then J.f11 i a u else J.f10 i a u
  f20 i a u := if i = k then J.f21 i a u else J.f20 i a u
  f01 _ _ _ := 0
  f11 _ _ _ := 0
  f21 _ _ _ := 0
  f22 _ _ _ := 0

/-- [the product outcome Hit Factor Jets statement holds](goal). -/
lemma product_outcomeHitFactorJets (C : Finset (Fin n)) (J : FactorJets (Fin n))
    (k : Fin n) (a u : ℝ) :
    product C (outcomeHitFactorJets J k) a u = leibnizTerm C J [] [k] a u := by
  unfold product leibnizTerm
  apply Finset.prod_congr rfl
  intro i _
  by_cases hik : i = k <;> subst_vars <;>
    simp_all [outcomeHitFactorJets, factorJet, List.count_cons, eq_comm]

/-- [the product Jet20 outcome Hit Factor Jets statement holds](goal). -/
lemma productJet20_outcomeHitFactorJets (C : Finset (Fin n)) (J : FactorJets (Fin n))
    (k : Fin n) (a u : ℝ) :
    productJet20 C (outcomeHitFactorJets J k) a u =
      ∑ i ∈ C, ∑ j ∈ C, leibnizTerm C J [i, j] [k] a u := by
  unfold productJet20 leibnizTerm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro r _
  by_cases hrk : r = k <;> by_cases hri : r = i <;> by_cases hrj : r = j <;>
    subst_vars <;> simp_all [outcomeHitFactorJets, factorJet, List.count_cons, eq_comm]

/-- The one-outcome-hit family retains both propensity derivative links. This statement assumes [the ha condition](hyp:ha). [This is the stated conclusion](goal). -/
lemma outcomeHitFactorJets_aChains (ν s : Bool) (n K M : ℕ) (p : CoefficientPairs K)
    (k : Fin n) (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    AChainsAt C (outcomeHitFactorJets (componentFactorJets ν s n K M p aug labels) k) a u := by
  constructor
  · intro i _
    by_cases hik : i = k
    · subst i
      simpa [outcomeHitFactorJets, componentFactorJets] using
        labelOutcomeDerivative_hasDerivAt ν K M a ha ((fun _ => s),p)
          (aug.1 k) (aug.2.1 k) (labels k)
    · simpa [outcomeHitFactorJets, hik, componentFactorJets] using
        labelDensity_hasDerivAt_propensity ν K M a u ha ((fun _ => s),p)
          (aug.1 i) (aug.2.1 i) (labels i)
  · intro i _
    by_cases hik : i = k
    · subst i
      simpa [outcomeHitFactorJets, componentFactorJets] using
        labelMixedDerivative_hasDerivAt ν K M a ha ((fun _ => s),p)
          (aug.1 k) (aug.2.1 k) (labels k)
    · simpa [outcomeHitFactorJets, hik, componentFactorJets] using
        labelPropensityDerivative_hasDerivAt ν K M a u ha ((fun _ => s),p)
          (aug.1 i) (aug.2.1 i) (labels i)

/-- The first outcome jet and its first two propensity derivatives, written as sums of ordinary products with one distinguished outcome-hit factor. This statement assumes [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). [This is the stated defined object](goal). -/
def componentOutcomeHitJet01 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ k ∈ C, product C
      (outcomeHitFactorJets (componentFactorJets ν s n K M p aug labels) k) a u

/-- [The component Outcome Hit Jet11 object](goal) is defined from [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def componentOutcomeHitJet11 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ k ∈ C, productJet10 C
      (outcomeHitFactorJets (componentFactorJets ν s n K M p aug labels) k) a u

/-- [The component Outcome Hit Jet21 object](goal) is defined from [the ν parameter](hyp:ν), [the s parameter](hyp:s), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def componentOutcomeHitJet21 (ν s : Bool) (n K M : ℕ) (a u : ℝ)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  ∑ p : CoefficientPairs K, conditionalPairWeight ν K M (fun _ => s) aug.2.2 p *
    ∑ k ∈ C, productJet20 C
      (outcomeHitFactorJets (componentFactorJets ν s n K M p aug labels) k) a u

/-- [the component Outcome Derivative eq outcome Hit Jet01 statement holds](goal). -/
lemma componentOutcomeDerivative_eq_outcomeHitJet01 (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentOutcomeDerivative ν s n K M a u aug C labels =
      componentOutcomeHitJet01 ν s n K M a u aug C labels := by
  unfold componentOutcomeDerivative componentOutcomeHitJet01
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [product_outcomeHitFactorJets]
  rw [leibnizTerm_cons_u C _ [] [] k a u hk]
  simp only [List.count_nil, zero_add, componentFactorJets, factorJet]
  ring

/-- [the component Outcome Hit Jet21 eq component Product Jet21 statement holds](goal). -/
lemma componentOutcomeHitJet21_eq_componentProductJet21 (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    componentOutcomeHitJet21 ν s n K M a u aug C labels =
      componentProductJet21 ν s n K M a u aug C labels := by
  unfold componentOutcomeHitJet21 componentProductJet21
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  simp_rw [productJet20_outcomeHitFactorJets]
  unfold productJet21
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

/-- Under [the ha condition](hyp:ha), [the component Outcome Hit Jet01 has Deriv At propensity statement holds](goal). -/
lemma componentOutcomeHitJet01_hasDerivAt_propensity (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentOutcomeHitJet01 ν s n K M b u aug C labels)
      (componentOutcomeHitJet11 ν s n K M a u aug C labels) a := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro k _
  exact hasDerivAt_product_a C _ a u
    (outcomeHitFactorJets_aChains ν s n K M p k a u ha aug C labels)

/-- Under [the ha condition](hyp:ha), [the component Outcome Hit Jet11 has Deriv At propensity statement holds](goal). -/
lemma componentOutcomeHitJet11_hasDerivAt_propensity (ν s : Bool) (n K M : ℕ)
    (a u : ℝ) (ha : 1-a^2 ≠ 0) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    HasDerivAt (fun b => componentOutcomeHitJet11 ν s n K M b u aug C labels)
      (componentOutcomeHitJet21 ν s n K M a u aug C labels) a := by
  apply HasDerivAt.fun_sum
  intro p _
  apply HasDerivAt.const_mul
  apply HasDerivAt.fun_sum
  intro k _
  exact hasDerivAt_productJet10_a C _ a u
    (outcomeHitFactorJets_aChains ν s n K M p k a u ha aug C labels)

/-- [The even Outcome Hit Jet01 object](goal) is defined from [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def evenOutcomeHitJet01 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentOutcomeHitJet01 true true n K M a u aug C labels +
    componentOutcomeHitJet01 true false n K M a u aug C labels) / 2 -
    componentOutcomeHitJet01 false false n K M a u aug C labels

/-- [The even Outcome Hit Jet11 object](goal) is defined from [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def evenOutcomeHitJet11 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentOutcomeHitJet11 true true n K M a u aug C labels +
    componentOutcomeHitJet11 true false n K M a u aug C labels) / 2 -
    componentOutcomeHitJet11 false false n K M a u aug C labels

/-- [The even Outcome Hit Jet21 object](goal) is defined from [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the aug parameter](hyp:aug), [the C parameter](hyp:C), [the labels parameter](hyp:labels). -/
def evenOutcomeHitJet21 (n K M : ℕ) (a u : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) : ℝ :=
  (componentOutcomeHitJet21 true true n K M a u aug C labels +
    componentOutcomeHitJet21 true false n K M a u aug C labels) / 2 -
    componentOutcomeHitJet21 false false n K M a u aug C labels

/-- Under [the ha condition](hyp:ha), [the even Outcome Hit Jet01 has Deriv At propensity statement holds](goal). -/
lemma evenOutcomeHitJet01_hasDerivAt_propensity (n K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n))
    (labels : Labels n) :
    HasDerivAt (fun b => evenOutcomeHitJet01 n K M b u aug C labels)
      (evenOutcomeHitJet11 n K M a u aug C labels) a := by
  exact (((componentOutcomeHitJet01_hasDerivAt_propensity true true n K M a u ha aug C labels).add
    (componentOutcomeHitJet01_hasDerivAt_propensity true false n K M a u ha aug C labels)).div_const 2).sub
      (componentOutcomeHitJet01_hasDerivAt_propensity false false n K M a u ha aug C labels)

/-- Under [the ha condition](hyp:ha), [the even Outcome Hit Jet11 has Deriv At propensity statement holds](goal). -/
lemma evenOutcomeHitJet11_hasDerivAt_propensity (n K M : ℕ) (a u : ℝ)
    (ha : 1-a^2 ≠ 0) (aug : Augmentation n K) (C : Finset (Fin n))
    (labels : Labels n) :
    HasDerivAt (fun b => evenOutcomeHitJet11 n K M b u aug C labels)
      (evenOutcomeHitJet21 n K M a u aug C labels) a := by
  exact (((componentOutcomeHitJet11_hasDerivAt_propensity true true n K M a u ha aug C labels).add
    (componentOutcomeHitJet11_hasDerivAt_propensity true false n K M a u ha aug C labels)).div_const 2).sub
      (componentOutcomeHitJet11_hasDerivAt_propensity false false n K M a u ha aug C labels)

/-- [the even Outcome Hit Jet01 zero statement holds](goal). -/
lemma evenOutcomeHitJet01_zero (n K M : ℕ) (a : ℝ) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    evenOutcomeHitJet01 n K M a 0 aug C labels = 0 := by
  unfold evenOutcomeHitJet01
  rw [← componentOutcomeDerivative_eq_outcomeHitJet01 true true,
    ← componentOutcomeDerivative_eq_outcomeHitJet01 true false,
    ← componentOutcomeDerivative_eq_outcomeHitJet01 false false]
  apply (((componentDensity_hasDerivAt_outcome true true n K M a 0 aug C labels).add
    (componentDensity_hasDerivAt_outcome true false n K M a 0 aug C labels)).div_const 2).sub
      (componentDensity_hasDerivAt_outcome false false n K M a 0 aug C labels) |>.unique
  exact evenDiscrepancy_hasDerivAt_outcome_zero n K M a aug C labels

/-- Under [the ha condition](hyp:ha), [the even Outcome Hit Jet11 zero statement holds](goal). -/
lemma evenOutcomeHitJet11_zero (n K M : ℕ) (a : ℝ) (ha : 1-a^2 ≠ 0)
    (aug : Augmentation n K) (C : Finset (Fin n)) (labels : Labels n) :
    evenOutcomeHitJet11 n K M a 0 aug C labels = 0 := by
  apply (evenOutcomeHitJet01_hasDerivAt_propensity n K M a 0 ha aug C labels).unique
  have he : (fun b => evenOutcomeHitJet01 n K M b 0 aug C labels) = fun _ => 0 := by
    funext b
    exact evenOutcomeHitJet01_zero n K M b aug C labels
  rw [he]
  exact hasDerivAt_const a 0

/-- Under [the ha condition](hyp:ha), [the even Product Jet21 zero outcome statement holds](goal). -/
lemma evenProductJet21_zero_outcome (n K M : ℕ) (a : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1/16) (aug : Augmentation n K)
    (C : Finset (Fin n)) (labels : Labels n) :
    evenProductJet21 n K M a 0 aug C labels = 0 := by
  rw [← show evenOutcomeHitJet21 n K M a 0 aug C labels =
      evenProductJet21 n K M a 0 aug C labels by
    unfold evenOutcomeHitJet21 evenProductJet21
    rw [componentOutcomeHitJet21_eq_componentProductJet21 true true,
      componentOutcomeHitJet21_eq_componentProductJet21 true false,
      componentOutcomeHitJet21_eq_componentProductJet21 false false]]
  have hden : 1-a^2 ≠ 0 := by
    have hd := correction_denominator_bounds a ha
    linarith [hd.2.2.1]
  apply (evenOutcomeHitJet11_hasDerivAt_propensity n K M a 0 hden aug C labels).unique
  apply (hasDerivAt_const a (0 : ℝ)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < a by linarith) (show a < 1 by linarith)]
    with b hb
  have hbden : 1-b^2 ≠ 0 := by
    have hp : 0 < (1-b)*(1+b) := mul_pos (by linarith [hb.2]) (by linarith [hb.1])
    nlinarith
  exact evenOutcomeHitJet11_zero n K M b hbden aug C labels

end CausalSmith.Stat.FinitepHomogeneityDensegamma
