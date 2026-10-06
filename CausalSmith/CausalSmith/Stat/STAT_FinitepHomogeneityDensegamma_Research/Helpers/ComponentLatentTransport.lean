module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentLatentAugmentation

/-! Disclosure-preserving disintegration of the actual latent coefficient and label law. -/
public section
set_option linter.style.whitespace false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A conditional coefficient draw cannot disagree with any actually disclosed pair. This statement assumes [the hne condition](hyp:hne). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_eq_zero_of_disclosure_ne
lemma conditionalPairWeight_eq_zero_of_disclosure_ne (ν : Bool) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (q p : CoefficientPairs K)
    (hne : disclose K M p ≠ disclose K M q) :
    conditionalPairWeight ν K M σ (disclose K M q) p = 0 := by
  classical
  have hex : ∃ i : Fin (K+1), boundaryNode K M i ∧ p i ≠ q i := by
    by_contra h
    apply hne
    funext i
    by_cases hb : boundaryNode K M i
    · have he : p i = q i := by
        by_contra hne
        exact h ⟨i, hb, hne⟩
      simp [disclose, hb, he]
    · simp [disclose, hb]
  obtain ⟨i, hi, hpi⟩ := hex
  unfold conditionalPairWeight
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [disclose, hi, hpi]

/-- Finite conditional averaging preserves arbitrary functions of disclosure as well as the coefficient draw. This strengthens averaging that forgets disclosure. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: conditionalPairWeight_joint_disclosure_expectation
lemma conditionalPairWeight_joint_disclosure_expectation (ν : Bool) (K M : ℕ)
    (hK : 0 < K) (σ : Fin (M/2) → Bool)
    (f : Disclosure K → CoefficientPairs K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) *
      (∑ q : CoefficientPairs K, ∑ p : CoefficientPairs K,
        conditionalPairWeight ν K M σ (disclose K M q) p * f (disclose K M q) p) =
      ∑ p : CoefficientPairs K,
        (∏ i : Fin (K+1), pairWeight ν (coarseTent M σ ((i:ℝ)/K)) (p i).1 (p i).2) *
          f (disclose K M p) p := by
  classical
  have he (q p : CoefficientPairs K) :
      conditionalPairWeight ν K M σ (disclose K M q) p * f (disclose K M q) p =
      conditionalPairWeight ν K M σ (disclose K M q) p * f (disclose K M p) p := by
    by_cases h : disclose K M p = disclose K M q
    · rw [h]
    · rw [conditionalPairWeight_eq_zero_of_disclosure_ne ν K M σ q p h]
      simp
  conv_lhs => arg 2; arg 2; ext q; arg 2; ext p; rw [he q p]
  exact conditionalPairWeight_disclosure_expectation ν K M hK σ _

/-- Null conditional label densities preserve disclosure in arbitrary label tests. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_joint_disclosure_average
lemma nullConditionalDensity_joint_disclosure_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n)
    (f : Disclosure K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) * (∑ q : CoefficientPairs K,
      nullConditionalDensity n K M a u (xs,marks,disclose K M q) labels *
        f (disclose K M q)) =
      ∑ p : CoefficientPairs K,
        (∏ i : Fin (K+1), pairWeight false (coarseTent M (fun _ => false) ((i:ℝ)/K))
          (p i).1 (p i).2) *
        ((∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
          (xs i) (marks i) (labels i)) * f (disclose K M p)) := by
  simp_rw [nullConditionalDensity_eq_coefficient_average n K M a u hK hM hdiv heven
    (xs,marks,disclose K M _) labels ⟨_,rfl⟩, Finset.sum_mul, mul_assoc]
  exact conditionalPairWeight_joint_disclosure_expectation false K M hK (fun _ => false)
    (fun δ p => (∏ i : Fin n, labelDensity false K M a u ((fun _ => false),p)
      (xs i) (marks i) (labels i)) * f δ)

/-- Alternative conditional densities preserve joint disclosure tests before the coarse signs are averaged. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: alternativeConditionalDensity_joint_disclosure_average
lemma alternativeConditionalDensity_joint_disclosure_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (xs : Fin n → unitInterval) (marks : Fin n → Bool)
    (labels : Labels n) (f : Disclosure K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) * (∑ q : CoefficientPairs K,
      alternativeConditionalDensity n K M a u (xs,marks,disclose K M q) labels *
        f (disclose K M q)) =
      ∑ idx : CopulaIndex K M, copulaWeight true K M idx *
        ((∏ i : Fin n, labelDensity true K M a u idx (xs i) (marks i) (labels i)) *
          f (disclose K M idx.2)) := by
  unfold alternativeConditionalDensity
  simp_rw [mul_assoc, Finset.sum_mul, mul_assoc]
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm ((4:ℝ)^(-(K+1:ℤ))), mul_assoc,
    Finset.sum_comm, Finset.mul_sum]
  have he (σ : Fin (M/2) → Bool) :=
    conditionalPairWeight_joint_disclosure_expectation true K M hK σ
      (fun δ p => (∏ i : Fin n, labelDensity true K M a u (σ,p)
        (xs i) (marks i) (labels i)) * f δ)
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  have hc : (2:ℝ)^(-(M/2:ℤ)) = (1/2:ℝ)^(M/2) := by
    have hcast : (M:ℤ)/2 = ((M/2:ℕ):ℤ) := by omega
    rw [hcast, zpow_neg, zpow_natCast, one_div, inv_pow]
  rw [hc]
  simp only [copulaWeight, Finset.mul_sum, mul_assoc]

/-- The redundant null coarse signs average out even for tests retaining disclosure. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: nullConditionalDensity_joint_prior_average
lemma nullConditionalDensity_joint_prior_average (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n)
    (f : Disclosure K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) * (∑ q : CoefficientPairs K,
      nullConditionalDensity n K M a u (xs,marks,disclose K M q) labels *
        f (disclose K M q)) =
      ∑ idx : CopulaIndex K M, copulaWeight false K M idx *
        ((∏ i : Fin n, labelDensity false K M a u idx (xs i) (marks i) (labels i)) *
          f (disclose K M idx.2)) := by
  rw [nullConditionalDensity_joint_disclosure_average n K M a u hK hM hdiv heven]
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
  simp only [← mul_assoc]
  rw [hc, one_mul]

/-- The actual null and alternative likelihoods both satisfy joint test averaging. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven). [This is the stated conclusion](goal). -/
-- @node: copulaConditionalDensity_joint_prior_average
lemma copulaConditionalDensity_joint_prior_average (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) (labels : Labels n)
    (f : Disclosure K → ℝ) :
    (4:ℝ)^(-(K+1:ℤ)) * (∑ q : CoefficientPairs K,
      (if ν then alternativeConditionalDensity n K M a u (xs,marks,disclose K M q) labels
        else nullConditionalDensity n K M a u (xs,marks,disclose K M q) labels) *
          f (disclose K M q)) =
      ∑ idx : CopulaIndex K M, copulaWeight ν K M idx *
        ((∏ i : Fin n, labelDensity ν K M a u idx (xs i) (marks i) (labels i)) *
          f (disclose K M idx.2)) := by
  cases ν
  · exact nullConditionalDensity_joint_prior_average n K M a u hK hM hdiv heven xs marks labels f
  · exact alternativeConditionalDensity_joint_disclosure_average n K M a u hK xs marks labels f

/-- For each design and mark vector, the conditional label law coupled with its disclosure equals the actual prior's disclosed full-label law. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copulaConditionalLaw_joint_disclosure
lemma copulaConditionalLaw_joint_disclosure (ν : Bool) (n K M : ℕ) (a u : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (xs : Fin n → unitInterval) (marks : Fin n → Bool) :
    (disclosureLaw K M).bind (fun δ =>
      (if ν then alternativeConditionalLaw n K M a u (xs,marks,δ)
        else nullConditionalLaw n K M a u (xs,marks,δ)).map
          (fun labels => (((xs,marks,δ) : Augmentation n K),labels))) =
      ∑ idx : CopulaIndex K M, ENNReal.ofReal (copulaWeight ν K M idx) •
        (fairLabelMeasure n (fun labels =>
          ∏ i : Fin n, labelDensity ν K M a u idx (xs i) (marks i) (labels i))).map
            (fun labels => (((xs,marks,disclose K M idx.2) : Augmentation n K),labels)) := by
  classical
  let d (δ : Disclosure K) (l : Labels n) : ℝ :=
    if ν then alternativeConditionalDensity n K M a u (xs,marks,δ) l
      else nullConditionalDensity n K M a u (xs,marks,δ) l
  have hd (δ : Disclosure K) (l : Labels n) : 0 ≤ d δ l := by
    cases ν
    · change 0 ≤ nullConditionalDensity n K M a u (xs,marks,δ) l
      unfold nullConditionalDensity
      apply Finset.prod_nonneg
      intro C _
      exact le_trans (by positivity)
        (component_denominator_bounds n K M a u hK ha hu (xs,marks,δ) C l).1
    · exact alternativeConditionalDensity_nonneg n K M a u hK ha hu (xs,marks,δ) l
  have hv (idx : CopulaIndex K M) (l : Labels n) :
      0 ≤ ∏ i : Fin n, labelDensity ν K M a u idx (xs i) (marks i) (l i) :=
    Finset.prod_nonneg (fun i _ => le_trans (by norm_num)
      (labelDensity_bounds ν K M a u hK ha hu idx _ _ _).1)
  have hlaw (δ : Disclosure K) :
      (if ν then alternativeConditionalLaw n K M a u (xs,marks,δ)
        else nullConditionalLaw n K M a u (xs,marks,δ)) = fairLabelMeasure n (d δ) := by
    cases ν <;> rfl
  simp_rw [hlaw]
  ext s hs
  rw [Measure.bind_apply hs (measurable_of_finite _).aemeasurable]
  simp only [Measure.map_apply (measurable_of_finite _) hs, fairLabelMeasure,
    Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.dirac_apply' _ (hs.preimage (measurable_of_finite _))]
  rw [lintegral_finsetSum]
  · simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    let f (δ : Disclosure K) : ℝ := if (((xs,marks,δ) : Augmentation n K),l) ∈ s then 1 else 0
    have hf (δ : Disclosure K) : 0 ≤ f δ := by dsimp [f]; split <;> positivity
    have hi (δ : Disclosure K) :
        ((fun labels => (((xs,marks,δ) : Augmentation n K),labels)) ⁻¹' s).indicator
          (1 : Labels n → ℝ≥0∞) l = ENNReal.ofReal (f δ) := by
      simp only [Set.indicator_apply, Set.mem_preimage, Pi.one_apply, f]
      split <;> norm_num
    simp_rw [hi]
    have heL (δ : Disclosure K) := ENNReal.ofReal_mul
      (mul_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ)^(-(n:ℤ))) (hd δ l)) (q := f δ)
    have heR (idx : CopulaIndex K M) := ENNReal.ofReal_mul
      (mul_nonneg (by positivity : (0:ℝ) ≤ (4:ℝ)^(-(n:ℤ))) (hv idx l))
      (q := f (disclose K M idx.2))
    simp_rw [← heL, ← heR]
    rw [lintegral_disclosure_ofReal K M _ (fun δ => mul_nonneg (mul_nonneg (by positivity)
      (hd δ l)) (hf δ)), integral_disclosureLaw]
    simp_rw [← ENNReal.ofReal_mul (copulaWeight_nonneg ν K M _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun idx _ =>
      mul_nonneg (copulaWeight_nonneg ν K M idx)
        (mul_nonneg (mul_nonneg (by positivity) (hv idx l)) (hf _)))]
    congr 1
    have he := copulaConditionalDensity_joint_prior_average ν n K M a u hK hM hdiv heven
      xs marks l f
    change (4:ℝ)^(-(K+1:ℤ)) * (∑ q, (4:ℝ)^(-(n:ℤ)) * d (disclose K M q) l * f (disclose K M q)) = _
    simp only [mul_assoc, ← Finset.mul_sum]
    rw [← mul_assoc, mul_comm ((4:ℝ)^(-(K+1:ℤ))), mul_assoc]
    rw [show (4:ℝ)^(-(K+1:ℤ)) * (∑ q, d (disclose K M q) l * f (disclose K M q)) = _ from he]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro idx _
    ring
  · intro l _
    exact measurable_of_finite _

/-- Forgetting the latent index gives exactly the common augmentation composed with the normalized conditional kernel, while retaining the actual disclosure. This statement assumes [the hK condition](hyp:hK), [the hM condition](hyp:hM), [the hdiv condition](hyp:hdiv), [the heven condition](hyp:heven), [the ha condition](hyp:ha), [the hu condition](hyp:hu), [the hε condition](hyp:hε), [the hP condition](hyp:hP). [This is the stated conclusion](goal). -/
-- @node: copulaLatentAugmentedLaw_map_conditional
lemma copulaLatentAugmentedLaw_map_conditional (ν : Bool) (n K M : ℕ) (a u ε : ℝ)
    (hK : 0 < K) (hM : 0 < M) (hdiv : M ∣ K) (heven : 2 ∣ M)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16) (hε : 0 ≤ ε ∧ ε ≤ 1)
    (P : Kernel (Augmentation n K) (Labels n)) [IsSFiniteKernel P]
    (hP : ∀ aug, P aug = if ν then alternativeConditionalLaw n K M a u aug
      else nullConditionalLaw n K M a u aug) :
    (copulaLatentAugmentedLaw ν n K M a u ε).map Prod.snd =
      commonAugmentation n K M ε ⊗ₘ P := by
  classical
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let : IsProbabilityMeasure (disclosureLaw K M) := disclosureLaw_probability K M
  let : IsProbabilityMeasure (commonAugmentation n K M ε) := by
    unfold commonAugmentation
    infer_instance
  ext s hs
  rw [Measure.map_apply measurable_snd hs]
  simp only [copulaLatentAugmentedLaw, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul]
  simp_rw [Measure.bind_apply (hs.preimage measurable_snd)
    (measurable_copulaLatentLabelFibre ν n K M a u _).aemeasurable]
  have hc (idx : CopulaIndex K M) := lintegral_const_mul
    (μ := (Measure.pi fun _ : Fin n => design).prod
      (Measure.pi fun _ : Fin n => markFlagLaw ε))
    (ENNReal.ofReal (copulaWeight ν K M idx))
    ((Measure.measurable_coe (hs.preimage measurable_snd)).comp
      (measurable_copulaLatentLabelFibre ν n K M a u idx))
  simp only [Function.comp_def] at hc
  simp_rw [← hc]
  rw [← lintegral_finsetSum]
  · rw [Measure.compProd_apply hs]
    have hg := P.measurable_kernel_prodMk_left hs
    rw [commonAugmentation, lintegral_prod _ hg.aemeasurable]
    rw [lintegral_prod]
    · apply lintegral_congr
      intro xs
      have hi := hg.comp (measurable_prodMk_left (x := xs))
      dsimp only [Function.comp_def] at hi
      rw [lintegral_prod _ hi.aemeasurable]
      apply lintegral_congr
      intro marks
      have he := congrArg (fun μ : Measure (Augmentation n K × Labels n) => μ s)
        (copulaConditionalLaw_joint_disclosure ν n K M a u hK hM hdiv heven ha hu xs marks)
      rw [Measure.bind_apply hs (measurable_of_finite _).aemeasurable] at he
      simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
        smul_eq_mul] at he
      have hf (idx : CopulaIndex K M) :
          copulaLatentLabelFibre ν n K M a u idx (xs,marks) (Prod.snd ⁻¹' s) =
          ((fairLabelMeasure n (fun labels =>
            ∏ i : Fin n, labelDensity ν K M a u idx (xs i) (marks i) (labels i))).map
              (fun labels => (((xs,marks,disclose K M idx.2) : Augmentation n K),labels))) s := by
        rw [← Measure.map_apply measurable_snd hs]
        unfold copulaLatentLabelFibre
        rw [Measure.map_map measurable_snd (measurable_of_finite _)]
        rfl
      simp_rw [hf]
      simp_rw [Measure.map_apply (measurable_of_finite _) hs] at he
      simp_rw [hP, Measure.map_apply (measurable_of_finite _) hs]
      exact he.symm
    · apply Measurable.aemeasurable
      apply Finset.measurable_sum
      intro idx _
      exact measurable_const.mul ((Measure.measurable_coe (hs.preimage measurable_snd)).comp
        (measurable_copulaLatentLabelFibre ν n K M a u idx))
  · intro idx _
    exact measurable_const.mul ((Measure.measurable_coe (hs.preimage measurable_snd)).comp
      (measurable_copulaLatentLabelFibre ν n K M a u idx))

end CausalSmith.Stat.FinitepHomogeneityDensegamma
