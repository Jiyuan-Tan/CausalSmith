module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentCoefficientFactorization

/-! Exact finite coefficient disintegration across boundary-only disclosure. -/
public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Averaging the conditional coefficient mass over fair boundary disclosure recovers the original independent sign-copula coefficient mass. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_disclosure_average
lemma conditionalPairWeight_disclosure_average (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (p : CoefficientPairs K) :
    (4:ℝ)^(-(K+1:ℤ)) *
      (∑ q : CoefficientPairs K, conditionalPairWeight ν K M σ (disclose K M q) p) =
      ∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2 := by
  classical
  let w (i : Fin (K+1)) (q : Bool × Bool) : ℝ :=
    if boundaryNode K M i then (if p i = q then 1 else 0)
    else pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2
  have hw : (∑ q : CoefficientPairs K,
      conditionalPairWeight ν K M σ (disclose K M q) p) =
      ∏ i : Fin (K+1), ∑ q : Bool × Bool, w i q := by
    have he (q : CoefficientPairs K) :
        conditionalPairWeight ν K M σ (disclose K M q) p = ∏ i, w i (q i) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hb : boundaryNode K M i <;> simp [disclose, w, hb]
    simp_rw [he]
    exact (Fintype.prod_sum w).symm
  have hi (i : Fin (K+1)) : (∑ q : Bool × Bool, w i q) =
      4 * pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2 := by
    by_cases hb : boundaryNode K M i
    · rw [coarseTent_boundaryNode_zero K M hK i hb σ]
      simp [w, hb, pairWeight]
    · simp [w, hb]
  rw [hw]
  simp_rw [hi]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← mul_assoc]
  have hc : (4:ℝ)^(-(K+1:ℤ)) * (4:ℝ)^(K+1) = 1 := by
    rw [zpow_neg, ← Nat.cast_add_one, zpow_natCast]
    exact inv_mul_cancel₀ (by positivity)
  rw [hc, one_mul]

/-- Any complete coefficient-dependent likelihood obeys the same exact disclosure averaging identity; finite summation requires no integrability gate. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_disclosure_expectation
lemma conditionalPairWeight_disclosure_expectation (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (f : CoefficientPairs K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) *
      (∑ q : CoefficientPairs K, ∑ p : CoefficientPairs K,
        conditionalPairWeight ν K M σ (disclose K M q) p * f p) =
      ∑ p : CoefficientPairs K,
        (∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2) * f p := by
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_mul, ← mul_assoc, conditionalPairWeight_disclosure_average ν K M hK σ p]

/-- Under actual boundary disclosure the product null-component likelihood is exactly the complete likelihood averaged over the conditional coefficient law. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the hactual condition](hyp:hactual). [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_eq_coefficient_average
lemma nullConditionalDensity_eq_coefficient_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (aug : Augmentation n K) (labels : Labels n)
    (hactual : ∃ q : CoefficientPairs K, aug.2.2 = disclose K M q) :
    nullConditionalDensity n K M a u aug labels =
      ∑ p : CoefficientPairs K,
        conditionalPairWeight false K M (fun _ => false) aug.2.2 p *
          ∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
            (aug.1 i) (aug.2.1 i) (labels i) := by
  classical
  let g (C : Finset (Fin n)) : Fin (M/2) :=
    if hC : C ∈ components n K M aug then
      ⟨pairIndex M aug C, pairIndex_lt_half n K M hM heven aug hC⟩
    else ⟨0, by omega⟩
  have hg : ∀ C ∈ components n K M aug, (g C).val = pairIndex M aug C := by
    intro C hC
    simp [g, hC]
  exact (conditional_record_component_factorization false n K M a u hK hM hdiv heven
    (fun _ => false) aug labels hactual g hg).symm

/-- Integrating disclosure in the null full-label density recovers the uncoupled original prior likelihood, including all treatment-only records. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_disclosure_average
lemma nullConditionalDensity_disclosure_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n) :
    (4:ℝ)^(-(K+1:ℤ)) *
      (∑ q : CoefficientPairs K,
        nullConditionalDensity n K M a u (xs,marks,disclose K M q) labels) =
      ∑ p : CoefficientPairs K,
        (∏ i : Fin (K+1), pairWeight false (coarseTent M (fun _ => false) ((i:ℝ)/K))
          (p i).1 (p i).2) *
          ∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
            (xs i) (marks i) (labels i) := by
  have he (q : CoefficientPairs K) :=
    nullConditionalDensity_eq_coefficient_average n K M a u hK hM hdiv heven
      (xs,marks,disclose K M q) labels ⟨q,rfl⟩
  simp_rw [he]
  exact conditionalPairWeight_disclosure_expectation false K M hK (fun _ => false) _

/-- Averaging disclosure in the alternative full-label density recovers the original prior's joint coarse-sign and coefficient likelihood exactly. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalDensity_disclosure_average
lemma alternativeConditionalDensity_disclosure_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n) :
    (4:ℝ)^(-(K+1:ℤ)) *
      (∑ q : CoefficientPairs K,
        alternativeConditionalDensity n K M a u (xs,marks,disclose K M q) labels) =
      ∑ idx : CopulaIndex K M, copulaWeight true K M idx *
        ∏ i : Fin n, labelDensity true K M a u idx (xs i) (marks i) (labels i) := by
  unfold alternativeConditionalDensity
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm ((4:ℝ)^(-(K+1:ℤ))), mul_assoc,
    Finset.sum_comm, Finset.mul_sum]
  have he (σ : Fin (M/2) → Bool) :=
    conditionalPairWeight_disclosure_expectation true K M hK σ
      (fun p => ∏ i : Fin n, labelDensity true K M a u (σ,p) (xs i) (marks i) (labels i))
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  have hc : (2:ℝ)^(-(M/2:ℤ)) = (1/2:ℝ)^(M/2) := by
    have hcast : (M:ℤ)/2 = ((M/2:ℕ):ℤ) := by omega
    rw [hcast, zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hc]
  simp only [copulaWeight, Finset.mul_sum, mul_assoc]

/-- The common boundary-disclosure measure integrates every real function by its exact finite fair-coefficient enumeration. [This is the stated conclusion](goal). -/
-- @node: integral_disclosureLaw
lemma integral_disclosureLaw (K M : ℕ) (f : Disclosure K → ℝ) :
    (∫ δ, f δ ∂disclosureLaw K M) =
      (4:ℝ)^(-(K+1:ℤ)) * ∑ q : CoefficientPairs K, f (disclose K M q) := by
  unfold disclosureLaw
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by positivity), Finset.mul_sum]
  · intro q _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- The actual common disclosure integral of the alternative label likelihood is the original finite prior likelihood. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalDensity_integral_disclosure
lemma alternativeConditionalDensity_integral_disclosure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n) :
    (∫ δ, alternativeConditionalDensity n K M a u (xs,marks,δ) labels
      ∂disclosureLaw K M) =
      ∑ idx : CopulaIndex K M, copulaWeight true K M idx *
        ∏ i : Fin n, labelDensity true K M a u idx (xs i) (marks i) (labels i) := by
  rw [integral_disclosureLaw]
  exact alternativeConditionalDensity_disclosure_average n K M a u hK xs marks labels

/-- In the uncoupled branch a full record-label likelihood does not depend on any coarse sign; the deterministic correction vanishes identically. [This is the stated conclusion](goal). -/
-- @node: labelDensity_null_coarse_invariant
lemma labelDensity_null_coarse_invariant (K M : ℕ) (a u : ℝ)
    (σ τ : Fin (M/2) → Bool) (p : CoefficientPairs K)
    (x : unitInterval) (marked : Bool) (label : Bool × Bool) :
    labelDensity false K M a u (σ,p) x marked label =
      labelDensity false K M a u (τ,p) x marked label := by
  simp [labelDensity, copulaXi, copulaUpsilon, copulaZeta, copulaT]

/-- Averaging the redundant null coarse signs leaves the original uncoupled coefficient likelihood, with its exact probability normalization. [This is the stated conclusion](goal). -/
-- @node: null_copula_label_prior_reduction
lemma null_copula_label_prior_reduction (n K M : ℕ) (a u : ℝ)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n) :
    (∑ idx : CopulaIndex K M, copulaWeight false K M idx *
      ∏ i : Fin n, labelDensity false K M a u idx (xs i) (marks i) (labels i)) =
      ∑ p : CoefficientPairs K,
        (∏ i : Fin (K+1), pairWeight false (coarseTent M (fun _ => false) ((i:ℝ)/K))
          (p i).1 (p i).2) *
          ∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
            (xs i) (marks i) (labels i) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  have he (σ : Fin (M/2) → Bool) :
      (∏ i : Fin n, labelDensity false K M a u (σ,p) (xs i) (marks i) (labels i)) =
      ∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
        (xs i) (marks i) (labels i) := by
    apply Finset.prod_congr rfl
    intro i _
    exact labelDensity_null_coarse_invariant K M a u σ (fun _ => false) p _ _ _
  simp only [copulaWeight, he, pairWeight, Bool.false_eq_true, ↓reduceIte, zero_mul,
    add_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hc : (2:ℝ)^(M/2)*(1/2:ℝ)^(M/2) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [← mul_assoc, ← mul_assoc, hc, one_mul]

/-- The actual common disclosure integral of the null label likelihood is the original finite prior likelihood, including its redundant coarse-sign mixing. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_integral_disclosure
lemma nullConditionalDensity_integral_disclosure (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n) :
    (∫ δ, nullConditionalDensity n K M a u (xs,marks,δ) labels
      ∂disclosureLaw K M) =
      ∑ idx : CopulaIndex K M, copulaWeight false K M idx *
        ∏ i : Fin n, labelDensity false K M a u idx (xs i) (marks i) (labels i) := by
  rw [integral_disclosureLaw, null_copula_label_prior_reduction]
  exact nullConditionalDensity_disclosure_average n K M a u hK hM hdiv heven xs marks labels

end CausalSmith.Stat.FinitepHomogeneityDensegamma
