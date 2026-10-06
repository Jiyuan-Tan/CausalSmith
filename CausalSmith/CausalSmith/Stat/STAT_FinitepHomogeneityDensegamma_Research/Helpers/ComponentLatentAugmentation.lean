module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDisclosureTransport

/-! Actual latent prior coupling, normalization, and independence of boundary disclosure
from all coarse signs in the complete label experiment. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Independent complete labels normalize before any coefficient or coarse sign is averaged. [This is the stated conclusion](goal). -/
-- @node: copula_full_label_product_sum
lemma copula_full_label_product_sum (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    (∑ labels : Labels n, ∏ i : Fin n,
      labelDensity ν K M a u idx (xs i) (marks i) (labels i)) = (4:ℝ)^n := by
  rw [← Fintype.prod_sum]
  simp_rw [labelDensity_sum]
  simp

/-- The complete label law for a fixed latent draw is a probability measure. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copula_full_label_probability
lemma copula_full_label_probability (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    IsProbabilityMeasure (fairLabelMeasure n (fun labels =>
      ∏ i : Fin n, labelDensity ν K M a u idx (xs i) (marks i) (labels i))) := by
  apply fairLabelMeasure_isProbabilityMeasure
  · intro labels
    exact Finset.prod_nonneg (fun i _ =>
      le_trans (by norm_num) (labelDensity_bounds ν K M a u hK ha hu idx _ _ _).1)
  · exact copula_full_label_product_sum ν n K M a u idx xs marks

/-- Retain the fixed latent draw and its actual boundary disclosure while sampling labels. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the idx parameter](hyp:idx), [the xm parameter](hyp:xm). [This is the stated defined object](goal). -/
-- @node: copulaLatentLabelFibre
def copulaLatentLabelFibre (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
    Measure (CopulaIndex K M × (Augmentation n K × Labels n)) :=
  (fairLabelMeasure n (fun labels =>
    ∏ i : Fin n, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))).map
      (fun labels => (idx, ((xm.1, xm.2, disclose K M idx.2), labels)))

/-- Sampling the fixed latent fibre depends measurably on the design and mark flags. [This is the stated conclusion](goal). -/
-- @node: measurable_copulaLatentLabelFibre
@[fun_prop] lemma measurable_copulaLatentLabelFibre (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) : Measurable (copulaLatentLabelFibre ν n K M a u idx) := by
  unfold copulaLatentLabelFibre
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [Measure.map_apply (measurable_of_finite _) hs, fairLabelMeasure,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ (hs.preimage (measurable_of_finite _))]
  apply Finset.measurable_sum
  intro labels _
  have hd : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      ∏ i : Fin n, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i)) := by
    fun_prop
  have ho : Measurable (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      (idx, ((xm.1, xm.2, disclose K M idx.2), labels))) := by fun_prop
  exact (ENNReal.measurable_ofReal.comp (hd.const_mul ((4:ℝ)^(-(n:ℤ))))).mul
    (Measurable.ite (hs.preimage ho) measurable_const measurable_const)

/-- Retaining a deterministic latent index and disclosure preserves the fibre's normalization. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copulaLatentLabelFibre_probability
lemma copulaLatentLabelFibre_probability (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
    IsProbabilityMeasure (copulaLatentLabelFibre ν n K M a u idx xm) := by
  let : IsProbabilityMeasure (fairLabelMeasure n (fun labels =>
      ∏ i : Fin n, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))) :=
    copula_full_label_probability ν n K M a u hK ha hu idx xm.1 xm.2
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- Couple the actual sign-copula prior draws to the complete six-category label experiment, disclosing only the boundary coefficient pairs from those same draws. The latent index is retained solely to certify disclosure; it is forgotten by the augmented experiment's projection. This statement assumes [the ν parameter](hyp:ν), [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε). [This is the stated defined object](goal). -/
-- @node: copulaLatentAugmentedLaw
def copulaLatentAugmentedLaw (ν : Bool) (n K M : ℕ) (a u ε : ℝ) :
    Measure (CopulaIndex K M × (Augmentation n K × Labels n)) :=
  ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
    (((Measure.pi fun _ : Fin n => design).prod
      (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind
        (copulaLatentLabelFibre ν n K M a u idx))

/-- The actual finite prior-and-label coupling is normalized in both branches. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε). [This is the stated conclusion](goal). -/
-- @node: copulaLatentAugmentedLaw_probability
lemma copulaLatentAugmentedLaw_probability (ν : Bool) (n K M : ℕ) (a u ε : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (hε : 0 ≤ ε ∧ ε ≤ 1) :
    IsProbabilityMeasure (copulaLatentAugmentedLaw ν n K M a u ε) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  have hp (idx : CopulaIndex K M) : IsProbabilityMeasure
      (((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind
          (copulaLatentLabelFibre ν n K M a u idx)) :=
    isProbabilityMeasure_bind (measurable_copulaLatentLabelFibre ν n K M a u idx).aemeasurable
      (Filter.Eventually.of_forall (copulaLatentLabelFibre_probability ν n K M a u hK ha hu idx))
  constructor
  simp only [copulaLatentAugmentedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  have he (idx : CopulaIndex K M) :
      (((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)).bind
          (copulaLatentLabelFibre ν n K M a u idx)) Set.univ = 1 :=
    (hp idx).measure_univ
  simp_rw [he, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun idx _ => copulaWeight_nonneg ν K M idx),
    copulaWeight_sum]
  norm_num

/-- The disclosure-support predicate is measurable, since the coefficient space is finite. [This is the stated conclusion](goal). -/
-- @node: measurableSet_copulaLatent_disclosure
lemma measurableSet_copulaLatent_disclosure (n K M : ℕ) :
    MeasurableSet {z : CopulaIndex K M × (Augmentation n K × Labels n) |
      z.2.1.2.2 = disclose K M z.1.2} := by
  exact measurableSet_eq_fun (by fun_prop)
    ((measurable_of_finite (disclose K M)).comp (by fun_prop))

/-- Every fixed-draw fibre records exactly that draw's boundary coefficient pairs. [This is the stated conclusion](goal). -/
-- @node: copulaLatentLabelFibre_ae_disclosure
lemma copulaLatentLabelFibre_ae_disclosure (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (idx : CopulaIndex K M) (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
    ∀ᵐ z ∂copulaLatentLabelFibre ν n K M a u idx xm,
      z.2.1.2.2 = disclose K M z.1.2 := by
  unfold copulaLatentLabelFibre
  apply (ae_map_iff (measurable_of_finite _).aemeasurable
    (measurableSet_copulaLatent_disclosure n K M)).2
  exact Filter.Eventually.of_forall (fun _ => rfl)

/-- Integrating all designs, marks and latent draws preserves actual-draw disclosure. [This is the stated conclusion](goal). -/
-- @node: copulaLatentAugmentedLaw_ae_disclosure
lemma copulaLatentAugmentedLaw_ae_disclosure (ν : Bool) (n K M : ℕ) (a u ε : ℝ) :
    ∀ᵐ z ∂copulaLatentAugmentedLaw ν n K M a u ε,
      z.2.1.2.2 = disclose K M z.1.2 := by
  rw [ae_iff]
  simp only [copulaLatentAugmentedLaw, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul]
  apply Finset.sum_eq_zero
  intro idx _
  have hs : MeasurableSet {z : CopulaIndex K M × (Augmentation n K × Labels n) |
      ¬ z.2.1.2.2 = disclose K M z.1.2} :=
    (measurableSet_copulaLatent_disclosure n K M).compl
  rw [Measure.bind_apply hs
    (measurable_copulaLatentLabelFibre ν n K M a u idx).aemeasurable]
  have he (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
      copulaLatentLabelFibre ν n K M a u idx xm
        {z | ¬ z.2.1.2.2 = disclose K M z.1.2} = 0 :=
    ae_iff.mp (copulaLatentLabelFibre_ae_disclosure ν n K M a u idx xm)
  simp_rw [he]
  simp

/-- Boundary disclosure has the fair coefficient expectation for every coarse sign. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: copula_disclosure_expectation
lemma copula_disclosure_expectation (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) (f : Disclosure K → ℝ) :
    (∑ p : CoefficientPairs K,
      (∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2) *
        f (disclose K M p)) =
      (4:ℝ)^(-(K+1:ℤ)) * ∑ p : CoefficientPairs K, f (disclose K M p) := by
  have he := finite_weighted_local_congr
    (fun (i : Fin (K+1)) (q : Bool × Bool) => pairWeight ν (coarseTent M σ ((i:ℝ)/K)) q.1 q.2)
    (fun (_ : Fin (K+1)) (_ : Bool × Bool) => (1/4:ℝ))
    (fun i => pairWeight_sum ν _) (fun _ => by norm_num [Fintype.sum_prod_type])
    (boundaryNode K M) (fun p => f (disclose K M p))
    (by
      intro x y hxy
      congr 1
      funext i
      by_cases hb : boundaryNode K M i
      · simp [disclose, hb, hxy i hb]
      · simp [disclose, hb])
    (by
      intro i hi
      funext q
      rw [coarseTent_boundaryNode_zero K M hK i hi σ]
      simp [pairWeight])
  rw [he]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  congr 1
  rw [zpow_neg, ← Nat.cast_add_one, zpow_natCast, ← inv_pow]
  norm_num

/-- The tilted coefficient law pushes to the same fair boundary disclosure law. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: copula_coefficient_disclosure_law
lemma copula_coefficient_disclosure_law (ν : Bool) (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) :
    (∑ p : CoefficientPairs K,
      ENNReal.ofReal (∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2) •
        Measure.dirac (disclose K M p)) = disclosureLaw K M := by
  classical
  ext s hs
  simp only [disclosureLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  have hw (p : CoefficientPairs K) :
      0 ≤ ∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2 :=
    Finset.prod_nonneg (fun i _ => pairWeight_nonneg ν _ (coarseTent_abs_le_one M σ _) _ _)
  have hi (p : CoefficientPairs K) :
      s.indicator (1 : Disclosure K → ℝ≥0∞) (disclose K M p) =
        ENNReal.ofReal (if disclose K M p ∈ s then (1:ℝ) else 0) := by
    by_cases hp : disclose K M p ∈ s <;> simp [hp]
  simp_rw [hi, ← ENNReal.ofReal_mul (hw _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hw p) (by split <;> positivity))]
  rw [copula_disclosure_expectation ν K M hK σ (fun δ => if δ ∈ s then 1 else 0)]
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
    (fun p _ => by split <;> positivity), Finset.mul_sum]

/-- Forgetting labels in a fixed latent fibre leaves the deterministic actual disclosure. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copulaLatentLabelFibre_map_sign_augmentation
lemma copulaLatentLabelFibre_map_sign_augmentation (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (idx : CopulaIndex K M) (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
    (copulaLatentLabelFibre ν n K M a u idx xm).map (fun z => (z.1.1,z.2.1)) =
      Measure.dirac (idx.1,(xm.1,xm.2,disclose K M idx.2)) := by
  let : IsProbabilityMeasure (fairLabelMeasure n (fun labels =>
      ∏ i, labelDensity ν K M a u idx (xm.1 i) (xm.2 i) (labels i))) :=
    copula_full_label_probability ν n K M a u hK ha hu idx xm.1 xm.2
  unfold copulaLatentLabelFibre
  rw [Measure.map_map (by fun_prop) (measurable_of_finite _)]
  simp only [Function.comp_def]
  simp

/-- Integrating the normalized labels leaves only the actual latent signs and disclosure. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copulaLatentAugmentedLaw_map_sign_augmentation
lemma copulaLatentAugmentedLaw_map_sign_augmentation (ν : Bool) (n K M : ℕ) (a u ε : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16) :
    (copulaLatentAugmentedLaw ν n K M a u ε).map (fun z => (z.1.1,z.2.1)) =
      ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
        (((Measure.pi fun _ : Fin n => design).prod
          (Measure.pi fun _ : Fin n => markFlagLaw ε)).map
            (fun xm => (idx.1,(xm.1,xm.2,disclose K M idx.2)))) := by
  ext s hs
  have ho : Measurable (fun z : CopulaIndex K M × (Augmentation n K × Labels n) =>
      (z.1.1,z.2.1)) := by fun_prop
  rw [Measure.map_apply ho hs]
  simp only [copulaLatentAugmentedLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro idx _
  congr 1
  rw [Measure.bind_apply (hs.preimage ho)
    (measurable_copulaLatentLabelFibre ν n K M a u idx).aemeasurable,
    Measure.map_apply (by fun_prop) hs]
  have he (xm : (Fin n → unitInterval) × (Fin n → Bool)) :
      copulaLatentLabelFibre ν n K M a u idx xm ((fun z => (z.1.1,z.2.1)) ⁻¹' s) =
        Measure.dirac (idx.1,(xm.1,xm.2,disclose K M idx.2)) s := by
    rw [← copulaLatentLabelFibre_map_sign_augmentation ν n K M a u hK ha hu idx xm,
      Measure.map_apply ho hs]
  simp_rw [he, Measure.dirac_apply' _ hs]
  convert lintegral_indicator_one (hs.preimage (show Measurable
    (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
      (idx.1,(xm.1,xm.2,disclose K M idx.2))) by fun_prop)) using 1
  congr 1

/-- The finite latent prior makes coarse signs independent of boundary disclosure. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: copula_sign_disclosure_product
lemma copula_sign_disclosure_product (ν : Bool) (K M : ℕ) (hK : 0 < K) :
    (∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
      Measure.dirac (idx.1,disclose K M idx.2)) =
      (∑ σ : Fin (M/2) → Bool, ENNReal.ofReal ((1/2:ℝ)^(M/2)) •
        Measure.dirac σ).prod (disclosureLaw K M) := by
  classical
  ext s hs
  rw [Measure.prod_apply hs, lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  rw [← copula_coefficient_disclosure_law ν K M hK σ]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    smul_eq_mul, copulaWeight, ENNReal.ofReal_mul
      (by positivity : (0:ℝ) ≤ (1/2)^(M/2)), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [Measure.dirac_apply' _ hs,
    Measure.dirac_apply' _ (hs.preimage measurable_prodMk_left)]
  simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply]
  ring

/-- The whole augmentation is independent of every coarse sign in both prior branches. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε). [This is the stated conclusion](goal). -/
-- @node: copulaLatentAugmentedLaw_sign_independent
lemma copulaLatentAugmentedLaw_sign_independent (ν : Bool) (n K M : ℕ) (a u ε : ℝ)
    (hK : 0 < K) (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (hε : 0 ≤ ε ∧ ε ≤ 1) :
    (copulaLatentAugmentedLaw ν n K M a u ε).map (fun z => (z.1.1,z.2.1)) =
      (∑ σ : Fin (M/2) → Bool, ENNReal.ofReal ((1/2:ℝ)^(M/2)) •
        Measure.dirac σ).prod (commonAugmentation n K M ε) := by
  classical
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let : IsProbabilityMeasure (disclosureLaw K M) := disclosureLaw_probability K M
  let : IsProbabilityMeasure (commonAugmentation n K M ε) := by
    unfold commonAugmentation
    infer_instance
  rw [copulaLatentAugmentedLaw_map_sign_augmentation ν n K M a u ε hK ha hu]
  ext s hs
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  have hm (idx : CopulaIndex K M) : Measurable
      (fun xm : (Fin n → unitInterval) × (Fin n → Bool) =>
        (idx.1,(xm.1,xm.2,disclose K M idx.2))) := by fun_prop
  simp_rw [Measure.map_apply (hm _) hs]
  have hi (idx : CopulaIndex K M) :
      (((Measure.pi fun _ : Fin n => design).prod
        (Measure.pi fun _ : Fin n => markFlagLaw ε)))
        ((fun xm => (idx.1,(xm.1,xm.2,disclose K M idx.2))) ⁻¹' s) =
      ∫⁻ xm, s.indicator 1 (idx.1,(xm.1,xm.2,disclose K M idx.2))
        ∂((Measure.pi fun _ : Fin n => design).prod
          (Measure.pi fun _ : Fin n => markFlagLaw ε)) := by
    simpa only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply] using
      (lintegral_indicator_one (hs.preimage (hm idx))).symm
  have hc (idx : CopulaIndex K M) := lintegral_const_mul
    (μ := (Measure.pi fun _ : Fin n => design).prod
      (Measure.pi fun _ : Fin n => markFlagLaw ε))
    (ENNReal.ofReal (copulaWeight ν K M idx)) ((measurable_one.indicator hs).comp (hm idx))
  simp only [Function.comp_def] at hc
  simp_rw [hi, ← hc]
  rw [← lintegral_finsetSum]
  · rw [Measure.prod_apply hs, lintegral_finsetSum_measure]
    simp only [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    simp_rw [commonAugmentation, Measure.prod_apply (hs.preimage measurable_prodMk_left)]
    simp_rw [Measure.prod_apply (measurable_prodMk_left
      (hs.preimage measurable_prodMk_left))]
    have hc2 (σ : Fin (M/2) → Bool) := lintegral_const_mul
      (μ := Measure.pi fun _ : Fin n => design)
      (ENNReal.ofReal ((1/2:ℝ)^(M/2)))
      (measurable_measure_prodMk_left
        (ν := (Measure.pi fun _ : Fin n => markFlagLaw ε).prod (disclosureLaw K M))
        (hs.preimage (measurable_prodMk_left (x := σ))))
    simp_rw [Measure.prod_apply (measurable_prodMk_left
      (hs.preimage measurable_prodMk_left))] at hc2
    simp_rw [← hc2]
    rw [← lintegral_finsetSum]
    · rw [lintegral_prod]
      · apply lintegral_congr
        intro xs
        have hc3 (σ : Fin (M/2) → Bool) := lintegral_const_mul
          (μ := Measure.pi fun _ : Fin n => markFlagLaw ε)
          (ENNReal.ofReal ((1/2:ℝ)^(M/2)))
          (measurable_measure_prodMk_left (ν := disclosureLaw K M)
            (measurable_prodMk_left (x := xs)
              (hs.preimage (measurable_prodMk_left (x := σ)))))
        simp_rw [← hc3]
        rw [← lintegral_finsetSum]
        · apply lintegral_congr
          intro marks
          have he := congrArg (fun μ : Measure ((Fin (M/2) → Bool) × Disclosure K) =>
            μ ((fun sd => (sd.1,(xs,marks,sd.2))) ⁻¹' s))
              (copula_sign_disclosure_product ν K M hK)
          have ht : MeasurableSet ((fun sd : (Fin (M/2) → Bool) × Disclosure K =>
              (sd.1,(xs,marks,sd.2))) ⁻¹' s) := hs.preimage (by fun_prop)
          rw [Measure.prod_apply ht, lintegral_finsetSum_measure] at he
          simpa only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
            smul_eq_mul, Measure.dirac_apply' _ ht, lintegral_smul_measure,
            lintegral_dirac, Set.indicator_apply, Set.mem_preimage, Pi.one_apply,
            Set.preimage_preimage, Function.comp_def] using he
        · intro σ _
          exact measurable_const.mul (measurable_measure_prodMk_left
            (measurable_prodMk_left (hs.preimage measurable_prodMk_left)))
      · apply Measurable.aemeasurable
        apply Finset.measurable_sum
        intro idx _
        exact measurable_const.mul ((measurable_one.indicator hs).comp (hm idx))
    · intro σ _
      have hg := measurable_measure_prodMk_left
        (ν := (Measure.pi fun _ : Fin n => markFlagLaw ε).prod (disclosureLaw K M))
        (hs.preimage (measurable_prodMk_left (x := σ)))
      simp_rw [Measure.prod_apply (measurable_prodMk_left
        (hs.preimage measurable_prodMk_left))] at hg
      exact measurable_const.mul hg
  · intro idx _
    exact measurable_const.mul ((measurable_one.indicator hs).comp (hm idx))

end CausalSmith.Stat.FinitepHomogeneityDensegamma
