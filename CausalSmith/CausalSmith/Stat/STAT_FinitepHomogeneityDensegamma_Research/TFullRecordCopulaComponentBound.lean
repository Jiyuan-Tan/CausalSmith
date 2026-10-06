module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDisclosure
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentDisclosureTransport
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentLatentAugmentation
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentLatentTransport
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentTotalVariation
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.TCopulaFrameLegality
public import Mathlib.MeasureTheory.Function.Floor

/-! Finite-moment homogeneity testing: TFullRecordCopulaComponentBound. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- The explicit nullConditionalLaw construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_nullConditionalLaw
@[fun_prop] lemma measurable_nullConditionalLaw (n K M : ℕ) (a u : ℝ) : Measurable (nullConditionalLaw n K M a u) := by
  unfold nullConditionalLaw fairLabelMeasure
  apply Finset.measurable_sum
  intro labels _
  have hd : Measurable (fun aug : Augmentation n K => nullConditionalDensity n K M a u aug labels) := by
    simp only [nullConditionalDensity]
    have he (aug : Augmentation n K) :
        (∏ C ∈ components n K M aug, nullComponent n K M a u aug C labels) =
        ∏ C : Finset (Fin n), if C ∈ components n K M aug then
          nullComponent n K M a u aug C labels else 1 := by
      simp
    simp_rw [he]
    apply Finset.measurable_prod
    intro C _
    apply Measurable.ite (measurableSet_componentMembership n K M C)
    · unfold nullComponent
      fun_prop
    · fun_prop
  fun_prop
/-- The explicit alternativeConditionalLaw construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_alternativeConditionalLaw
@[fun_prop] lemma measurable_alternativeConditionalLaw (n K M : ℕ) (a u : ℝ) : Measurable (alternativeConditionalLaw n K M a u) := by
  unfold alternativeConditionalLaw fairLabelMeasure
  apply Finset.measurable_sum
  intro labels _
  unfold alternativeConditionalDensity
  fun_prop
/-- The explicit intermediateConditionalLaw construction is Borel measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_intermediateConditionalLaw
@[fun_prop] lemma measurable_intermediateConditionalLaw (n K M : ℕ) (a u : ℝ) : Measurable (intermediateConditionalLaw n K M a u) := by
  unfold intermediateConditionalLaw fairLabelMeasure
  apply Finset.measurable_sum
  intro labels _
  have hd : Measurable (fun aug : Augmentation n K => intermediateDensity n K M a u aug labels) := by
    simp only [intermediateDensity]
    have he (aug : Augmentation n K) :
        (∏ C ∈ components n K M aug, averageComponent n K M a u aug C labels) =
        ∏ C : Finset (Fin n), if C ∈ components n K M aug then
          averageComponent n K M a u aug C labels else 1 := by
      simp
    simp_rw [he]
    apply Finset.measurable_prod
    intro C _
    apply Measurable.ite (measurableSet_componentMembership n K M C)
    · unfold averageComponent
      fun_prop
    · fun_prop
  fun_prop
/-- The augmentation has the common design and mark marginals, and reveals exactly boundary coefficient pairs. Its probability normalization is independent of all coarse signs. This statement assumes [the hε condition](hyp:hε). [This is the stated conclusion](goal). -/
-- @node: copula_common_augmentation_certificate
lemma copula_common_augmentation_certificate (n K M : ℕ) (ε : ℝ)
    (hε : 0 ≤ ε ∧ ε ≤ 1) :
    IsProbabilityMeasure (commonAugmentation n K M ε) ∧
    (commonAugmentation n K M ε).map Prod.fst = Measure.pi (fun _ : Fin n => design) ∧
    (commonAugmentation n K M ε).map (fun aug => aug.2.1) =
      Measure.pi (fun _ : Fin n => markFlagLaw ε) ∧
    (∀ᵐ aug ∂commonAugmentation n K M ε, ∀ i : Fin (K+1),
      (aug.2.2 i).isSome = true ↔ boundaryNode K M i) := by
  let : IsProbabilityMeasure design := by unfold design; infer_instance
  let : IsProbabilityMeasure (markFlagLaw ε) := markFlagLaw_probability ε hε.1 hε.2
  let : IsProbabilityMeasure (disclosureLaw K M) := disclosureLaw_probability K M
  have hf : MeasurePreserving (fun aug : Augmentation n K => aug.1)
      (commonAugmentation n K M ε) (Measure.pi (fun _ : Fin n => design)) :=
    measurePreserving_fst
  have hb : MeasurePreserving (fun aug : Augmentation n K => aug.2.1)
      (commonAugmentation n K M ε) (Measure.pi (fun _ : Fin n => markFlagLaw ε)) :=
    measurePreserving_fst.comp measurePreserving_snd
  refine ⟨by unfold commonAugmentation; infer_instance, hf.map_eq, hb.map_eq, ?_⟩
  filter_upwards [commonAugmentation_ae_actual_disclosure n K M ε] with aug haug
  obtain ⟨p, hp⟩ := haug
  intro i
  rw [hp]
  simp only [disclose]
  split <;> simp_all

/-- The strictly positive null and intermediate full-label densities dominate the intermediate and alternative laws, respectively, for every disclosed design. This statement assumes [the hK condition](hyp:hK), [the ha condition](hyp:ha), [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: copula_conditional_absolute_continuity
lemma copula_conditional_absolute_continuity (n K M : ℕ) (a u : ℝ) (hK : 0 < K)
    (ha : 0 < a ∧ a ≤ 1/16) (hu : 0 < u ∧ u ≤ 1/16)
    (aug : Augmentation n K) :
    intermediateConditionalLaw n K M a u aug ≪ nullConditionalLaw n K M a u aug ∧
    alternativeConditionalLaw n K M a u aug ≪ intermediateConditionalLaw n K M a u aug := by
  have hp (l : Labels n) : 0 < nullConditionalDensity n K M a u aug l ∧
      0 < intermediateDensity n K M a u aug l := by
    constructor
    · apply Finset.prod_pos
      intro C _
      exact lt_of_lt_of_le (by positivity)
        (component_denominator_bounds n K M a u hK ha hu aug C l).1
    · apply Finset.prod_pos
      intro C _
      exact lt_of_lt_of_le (by positivity)
        (component_denominator_bounds n K M a u hK ha hu aug C l).2
  exact ⟨fairLabelMeasure_absolutelyContinuous n _ _ (fun l => (hp l).1),
    fairLabelMeasure_absolutelyContinuous n _ _ (fun l => (hp l).2)⟩

/-- The actual normalized component kernels and their two conditional chi-square bounds form the certificate used by the full-record comparison. [This is the stated conclusion](goal). -/
-- @node: copula_conditional_comparison_certificate
lemma copula_conditional_comparison_certificate (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) :
    ∀ᵐ aug ∂commonAugmentation n K M ε,
      IsProbabilityMeasure (intermediateConditionalLaw n K M a u aug) ∧
      IsProbabilityMeasure (nullConditionalLaw n K M a u aug) ∧
      IsProbabilityMeasure (alternativeConditionalLaw n K M a u aug) ∧
      intermediateConditionalLaw n K M a u aug ≪ nullConditionalLaw n K M a u aug ∧
      alternativeConditionalLaw n K M a u aug ≪ intermediateConditionalLaw n K M a u aug ∧
      0 ≤ activityA n K M a u aug ∧ 0 ≤ activityB n K M a u aug ∧
      1+Causalean.Stat.chiSqDiv (intermediateConditionalLaw n K M a u aug)
        (nullConditionalLaw n K M a u aug) ≤ Real.exp (activityA n K M a u aug) ∧
      1+Causalean.Stat.chiSqDiv (alternativeConditionalLaw n K M a u aug)
        (intermediateConditionalLaw n K M a u aug) ≤ Real.exp (activityB n K M a u aug) := by
  have hpos : 0 < K := by have := h.2.2.2.1; have := h.2.2.2.2.1; omega
  filter_upwards [conditional_component_comparisons n K M a u ε L h] with aug hc
  have hac := copula_conditional_absolute_continuity n K M a u hpos
    h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 aug
  exact ⟨hc.1, hc.2.1, hc.2.2.1, hac.1, hac.2, hc.2.2.2⟩

/-- A legitimate augmentation is the marginal of the actual prior-and-label coupling in both experiments. Its disclosed pairs equal the boundary pairs of that latent draw, and its joint law with all coarse signs is a product, so the entire augmentation reveals no information about any coarse sign. This statement assumes [the n parameter](hyp:n), [the K parameter](hyp:K), [the M parameter](hyp:M), [the a parameter](hyp:a), [the u parameter](hyp:u), [the ε parameter](hyp:ε), [the μ parameter](hyp:μ), [the P0 parameter](hyp:P0), [the P1 parameter](hyp:P1). [This is the stated defined object](goal). -/
-- @node: LegitimateCopulaAugmentation
def LegitimateCopulaAugmentation (n K M : ℕ) (a u ε : ℝ)
    (μ : Measure (Augmentation n K))
    (P0 P1 : Kernel (Augmentation n K) (Labels n)) : Prop :=
  ∀ ν : Bool,
    IsProbabilityMeasure (copulaLatentAugmentedLaw ν n K M a u ε) ∧
    (copulaLatentAugmentedLaw ν n K M a u ε).map Prod.snd =
      μ ⊗ₘ (if ν then P1 else P0) ∧
    (∀ᵐ z ∂copulaLatentAugmentedLaw ν n K M a u ε,
      z.2.1.2.2 = disclose K M z.1.2) ∧
    (copulaLatentAugmentedLaw ν n K M a u ε).map (fun z => (z.1.1, z.2.1)) =
      (∑ σ : Fin (M/2) → Bool,
        ENNReal.ofReal ((1/2:ℝ)^(M/2)) • Measure.dirac σ).prod μ

/-- [Full record copula component bound](goal). For the priors of Definition \(\mathrm{def:copula\mbox{-}frame\mbox{-}priors}\), suppose \(K\ge2^{40}n\), \(K\ge16M\), \(M\ge2\), and \(0<a,u\le1/16\). There is a common-design augmentation and a normalized intermediate probability law \(Q\) such that, conditional on the full covariate, nonzero-outcome mark-flag and boundary-disclosure triple, \(\chi^2(Q\Vert P_0)\le\exp(\mathcal A)-1\) and \(\chi^2(P_1\Vert Q)\le\exp(\mathcal B)-1\), where \[ E\mathcal A\le2^{38}a^4u^4\varepsilon^2 n^2/K,\qquad E\mathcal B\le2^{56}a^4u^4\varepsilon^2 n^4/(MK^2). \] The expectations include every occupancy and all six record categories. In particular, if the sum of these two displayed upper bounds is at most \(2^{-16}\), then \[ \operatorname{TV}\left(\int P^{\otimes n}\pi_0(dP), \int P^{\otimes n}\pi_1(dP)\right)<1/8. \] No transition tensor is assumed zero, and no coarse sign is disclosed. This statement assumes [the hK condition](hyp:hK).

The conditioning coordinate is exactly `Augmentation n K`: all covariates
\((X_i)_{i=1}^n\), all flags \(B_i=\mathbf1\{Y_i\ne0\}\), and the disclosure
\(\mathcal D_{\partial}\) of exactly the coefficient pairs \((\lambda_j,\eta_j)\)
at boundary nodes \(j/K=k/M\), \(0\le k\le M\). Under both mixtures, the covariates
are iid uniform on \([0,1]\), the flags are iid Bernoulli \(\varepsilon\), and the
covariates, flags and boundary disclosure are mutually independent. The disclosed boundary
pairs are independent fair pairs with the same law under both priors and are independent
of all coarse signs; no coarse sign is disclosed. Both conditional chi-square bounds use
this full triple, and the expectations of \(\mathcal A\) and \(\mathcal B\) integrate
its common law.

The common augmentation and both conditional kernels are existential witnesses, constrained by
their common design and mark marginals, a coupling to the actual latent prior draws with
boundary-only disclosure and independence from all coarse signs, and projections to the two
original-record mixtures. The proof selects
`commonAugmentation`, `nullConditionalLaw`, and `alternativeConditionalLaw` as these witnesses. -/
-- @node: lem:full-record-copula-component-bound
lemma full_record_copula_component_bound (v : Params) (n K M : ℕ) (a u ε L : ℝ)
    (h : CopulaDomain n K M a u ε L) (hK : 2^40*n ≤ K) :
    ∃ μ : Measure (Augmentation n K),
    ∃ P0 P1 : Kernel (Augmentation n K) (Labels n),
    ∃ Q : Kernel (Augmentation n K) (Labels n),
    ∃ 𝒜 ℬ : Augmentation n K → ℝ,
    IsProbabilityMeasure μ ∧
    μ.map Prod.fst = Measure.pi (fun _ : Fin n => design) ∧
    μ.map (fun aug => aug.2.1) = Measure.pi (fun _ : Fin n => markFlagLaw ε) ∧
    (∀ᵐ aug ∂μ, ∀ i : Fin (K+1), (aug.2.2 i).isSome = true ↔ boundaryNode K M i) ∧
    LegitimateCopulaAugmentation n K M a u ε μ P0 P1 ∧
    (μ ⊗ₘ P0).map (augmentedObserve n K L) = copulaMixture false n v K M a u ε L ∧
    (μ ⊗ₘ P1).map (augmentedObserve n K L) = copulaMixture true n v K M a u ε L ∧
    (μ ⊗ₘ P0).map Prod.fst = μ ∧ (μ ⊗ₘ P1).map Prod.fst = μ ∧
    IsProbabilityMeasure (μ ⊗ₘ Q) ∧
    (∀ᵐ aug ∂μ,
      IsProbabilityMeasure (Q aug) ∧ IsProbabilityMeasure (P0 aug) ∧ IsProbabilityMeasure (P1 aug) ∧
      Q aug ≪ P0 aug ∧ P1 aug ≪ Q aug ∧
      0 ≤ 𝒜 aug ∧ 0 ≤ ℬ aug ∧
      1+Causalean.Stat.chiSqDiv (Q aug) (P0 aug) ≤ Real.exp (𝒜 aug) ∧
      1+Causalean.Stat.chiSqDiv (P1 aug) (Q aug) ≤ Real.exp (ℬ aug)) ∧
    Measurable 𝒜 ∧ Measurable ℬ ∧ Integrable 𝒜 μ ∧ Integrable ℬ μ ∧
    (∫ aug, 𝒜 aug ∂μ) ≤ activityBudgetA n K a u ε ∧
    (∫ aug, ℬ aug ∂μ) ≤ activityBudgetB n K M a u ε ∧
    (activityBudgetA n K a u ε+activityBudgetB n K M a u ε ≤ (2:ℝ)^(-16:ℤ) →
      Causalean.Stat.tvDist (copulaMixture false n v K M a u ε L) (copulaMixture true n v K M a u ε L) < 1/8) := by
  let P0 : Kernel (Augmentation n K) (Labels n) :=
    ⟨nullConditionalLaw n K M a u, measurable_nullConditionalLaw n K M a u⟩
  let P1 : Kernel (Augmentation n K) (Labels n) :=
    ⟨alternativeConditionalLaw n K M a u, measurable_alternativeConditionalLaw n K M a u⟩
  let Q : Kernel (Augmentation n K) (Labels n) :=
    ⟨intermediateConditionalLaw n K M a u, measurable_intermediateConditionalLaw n K M a u⟩
  have hpos : 0 < K := by have := h.2.2.2.1; have := h.2.2.2.2.1; omega
  have ha := h.2.2.2.2.2.1
  have hu := h.2.2.2.2.2.2.1
  have hε : 0 ≤ ε ∧ ε ≤ 1 := ⟨h.2.2.2.2.2.2.2.1.1.le,
    h.2.2.2.2.2.2.2.1.2.le⟩
  obtain ⟨hμ, hdesign, hmarks, hdisclose⟩ :=
    copula_common_augmentation_certificate n K M ε hε
  let : IsProbabilityMeasure (commonAugmentation n K M ε) := hμ
  let : IsMarkovKernel P0 := ⟨fun aug =>
    nullConditionalLaw_isProbabilityMeasure n K M a u hpos ha hu aug⟩
  let : IsMarkovKernel P1 := ⟨fun aug =>
    alternativeConditionalLaw_isProbabilityMeasure n K M a u hpos ha hu aug⟩
  let : IsMarkovKernel Q := ⟨fun aug =>
    intermediateConditionalLaw_isProbabilityMeasure n K M a u hpos ha hu aug⟩
  have hP0fst : (commonAugmentation n K M ε ⊗ₘ P0).map Prod.fst =
      commonAugmentation n K M ε := Measure.fst_compProd _ _
  have hP1fst : (commonAugmentation n K M ε ⊗ₘ P1).map Prod.fst =
      commonAugmentation n K M ε := Measure.fst_compProd _ _
  have hQ : IsProbabilityMeasure (commonAugmentation n K M ε ⊗ₘ Q) := inferInstance
  have hconditional := copula_conditional_comparison_certificate n K M a u ε L h
  have hbudget := component_occupancy_budgets n K M a u ε L h hK
  obtain ⟨k, hk⟩ := h.2.1
  obtain ⟨m, hm⟩ := h.2.2.1
  have hM2 := h.2.2.2.2.1
  have hMK : M ≤ K := by have := h.2.2.2.1; omega
  have hmk : m ≤ k := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    rw [← hm, ← hk]
    exact hMK
  have hdiv : M ∣ K := by
    rw [hm, hk]
    exact Nat.pow_dvd_pow 2 hmk
  have heven : 2 ∣ M := by
    have hmpos : 0 < m := by
      by_contra hm0
      have : m = 0 := by omega
      have hMone : M = 1 := by simp [hm, this]
      omega
    obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hmpos.ne'
    rw [hm, pow_succ]
    simpa only [mul_comm] using dvd_mul_right 2 (2 ^ r)
  have hMpos : 0 < M := by omega
  have hrecords :
      (commonAugmentation n K M ε ⊗ₘ P0).map (augmentedObserve n K L) =
        copulaMixture false n v K M a u ε L ∧
      (commonAugmentation n K M ε ⊗ₘ P1).map (augmentedObserve n K L) =
        copulaMixture true n v K M a u ε L := by
    constructor
    · rw [null_augmented_projection_label_bind n K M a u ε L hpos hMpos hdiv heven
        ha hu hε P0 (fun _ => rfl)]
      exact prior_label_design_bind_eq_mixture false v n K M a u ε L h
    · rw [alternative_augmented_projection_label_bind n K M a u ε L hpos ha hu hε P1
        (fun _ => rfl)]
      exact prior_label_design_bind_eq_mixture true v n K M a u ε L h
  have htv : activityBudgetA n K a u ε+activityBudgetB n K M a u ε ≤ (2:ℝ)^(-16:ℤ) →
      Causalean.Stat.tvDist (copulaMixture false n v K M a u ε L)
        (copulaMixture true n v K M a u ε L) < 1/8 := by
    intro hsmall
    have ht := copula_augmented_tv_budget n K M a u ε L h hK P0 P1
      (fun _ => rfl) (fun _ => rfl) hsmall
    have hp := copula_tv_map_le (commonAugmentation n K M ε ⊗ₘ P0)
      (commonAugmentation n K M ε ⊗ₘ P1) (augmentedObserve n K L)
      (measurable_augmentedObserve n K L)
    rw [hrecords.1, hrecords.2] at hp
    exact lt_of_le_of_lt (hp.trans ht) (by norm_num)
  have hlegitimate : LegitimateCopulaAugmentation n K M a u ε
      (commonAugmentation n K M ε) P0 P1 := by
    intro ν
    refine ⟨copulaLatentAugmentedLaw_probability ν n K M a u ε hpos ha hu hε,
      ?_, copulaLatentAugmentedLaw_ae_disclosure ν n K M a u ε, ?_⟩
    · cases ν
      · exact copulaLatentAugmentedLaw_map_conditional false n K M a u ε hpos hMpos
          hdiv heven ha hu hε P0 (fun _ => rfl)
      · exact copulaLatentAugmentedLaw_map_conditional true n K M a u ε hpos hMpos
          hdiv heven ha hu hε P1 (fun _ => rfl)
    · exact copulaLatentAugmentedLaw_sign_independent ν n K M a u ε hpos ha hu hε
  exact ⟨commonAugmentation n K M ε, P0, P1, Q,
    activityA n K M a u, activityB n K M a u, hμ, hdesign, hmarks, hdisclose, hlegitimate,
    hrecords.1, hrecords.2, hP0fst, hP1fst, hQ, hconditional,
    hbudget.1, hbudget.2.1, hbudget.2.2.1, hbudget.2.2.2.1,
    hbudget.2.2.2.2.1, hbudget.2.2.2.2.2, htv⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
