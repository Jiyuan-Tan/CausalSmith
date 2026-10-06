module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalGraphMixture

/-!
# Finite conditional likelihood bounds

The finite row-channel mixture bounds actual conditional likelihoods and supplies
square integrability without an extra regularity premise.
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier

/-- Tensorizing the finite row bound gives a finite bound for every fixed allocation.  [For the stated data and conditions](hyp:B,d,h,ε), [the stated conclusion holds](goal). -/
-- @node: translatedRows_le_reference
lemma translatedRows_le_reference (B d : ℕ) (h : ℝ)
    (ε : Fin B → Fin d → Bool) :
    Measure.pi (fun ℓ => volume.withDensity
      (fun w => ENNReal.ofReal (rowDensity d h (ε ℓ) w))) ≤
      (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B • Measure.pi (fun _ : Fin B =>
        volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) := by
  let ν := volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))
  let μ := fun δ : Fin d → Bool => volume.withDensity
    (fun w => ENNReal.ofReal (rowDensity d h δ w))
  let c := ENNReal.ofReal ((2 : ℝ) ^ d)
  let := referenceRowLaw_probability d h
  have (δ : Fin d → Bool) : IsProbabilityMeasure (μ δ) := translatedRowLaw_probability d h δ
  change Measure.pi (fun ℓ => μ (ε ℓ)) ≤ c ^ B • Measure.pi (fun _ : Fin B => ν)
  induction B with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty]; simp
  | succ B ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (B + 1) => ℝ) 0
    have hμ := (measurePreserving_piFinSuccAbove (fun ℓ => μ (ε ℓ)) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (B + 1) => ν) 0).map_eq
    have hp := Measure.prod_mono (rowLaw_le_reference d h (ε 0))
      (ih (fun ℓ => ε ((0 : Fin (B + 1)).succAbove ℓ)))
    rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul] at hp
    have hm : (Measure.pi (fun ℓ => μ (ε ℓ))).map e ≤
        (c ^ (B + 1) • Measure.pi (fun _ : Fin (B + 1) => ν)).map e := by
      rw [Measure.map_smul, hμ, hν, pow_succ, mul_comm (c ^ B) c]
      exact hp
    have hm' := Measure.map_mono hm e.symm.measurable
    simpa only [Measure.map_map e.symm.measurable e.measurable,
      MeasurableEquiv.symm_comp_self, Measure.map_id] using hm'

/-- Every actual fixed-partition response law obeys the finite row-channel bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: block_responseLaw_le_reference
lemma block_responseLaw_le_reference (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    (blockBaselineLaw B).map (fun U =>
      distinctResponses n B d (recordOf (blockSchedule n B d true h (s, U)) ω)) ≤
      (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B • Measure.pi (fun _ : Fin B =>
        volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))) := by
  obtain ⟨ε, he⟩ := block_responseLaw_eq_translatedRows n B d hd hfit h s ω
  rw [he]
  exact translatedRows_le_reference B d h ε

/-- Averaging actual partition and design draws preserves the uniform density bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_snd_le_reference
lemma reducedBlockLaw_snd_le_reference (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] (h : ℝ) :
    (reducedBlockLaw n B d D true h).map Prod.snd ≤
      (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B • hiddenReferenceLaw n B d D h := by
  let ν := Measure.pi (fun _ : Fin B => volume.withDensity
    (fun w => ENNReal.ofReal (refDensity d h w)))
  let c := (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B
  let := referenceRowLaw_probability d h
  let := blockBaselineLaw_probability B
  let := partitionLaw_probability B d
  let f := fun o : Record (Fin n) => (o.2.1, distinctResponses n B d o)
  have hf : Measurable f := by fun_prop
  have hrec : Measurable (fun x : (SourcePartition B d × (Fin B → ℝ)) ×
      (Assign (Fin n) × Audit (Fin n)) => f (recordOf (blockSchedule n B d true h x.1) x.2)) :=
    hf.comp (block_record_measurable n B d true h)
  let K := fun ξ : SourcePartition B d × (Fin B → ℝ) =>
    D.map (fun ω => f (recordOf (blockSchedule n B d true h ξ) ω))
  have hK : Measurable K := block_measurable_map_parameter D _ hrec
  have heq : (reducedBlockLaw n B d D true h).map Prod.snd = (blockParamLaw B d).bind K := by
    rw [reducedBlockLaw, Measure.map_map (by fun_prop) (by fun_prop)]
    change (blockMixtureLawOf n B d D true h).map f = _
    rw [blockMixtureLawOf, mixtureLaw, block_map_bind _ _ _
      (block_measurable_map_parameter D _ (block_record_measurable n B d true h)) hf]
    congr 1
    funext ξ
    exact Measure.map_map hf (measurable_of_finite _)
  rw [heq]
  apply Measure.le_iff.mpr
  intro E hE
  have hs (s : SourcePartition B d) :
      (∫⁻ U, K (s, U) E ∂blockBaselineLaw B) ≤ c * hiddenReferenceLaw n B d D h E := by
    let g := fun x : (Fin B → ℝ) × (Assign (Fin n) × Audit (Fin n)) =>
      f (recordOf (blockSchedule n B d true h (s, x.1)) x.2)
    have hg : Measurable g := hrec.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have he : (∫⁻ U, K (s, U) E ∂blockBaselineLaw B) =
        ((blockBaselineLaw B).prod D) (g ⁻¹' E) := by
      rw [Measure.prod_apply (hg hE)]
      apply lintegral_congr
      intro U
      exact Measure.map_apply (measurable_of_finite _) hE
    rw [he, Measure.prod_apply_symm (hg hE)]
    have href : hiddenReferenceLaw n B d D h E = ∫⁻ ω, ν (Prod.mk ω.1 ⁻¹' E) ∂D := by
      rw [hiddenReferenceLaw, Measure.prod_apply hE,
        lintegral_map (measurable_of_finite _) (by fun_prop)]
    rw [href, ← lintegral_const_mul' c _ (by simp [c])]
    apply lintegral_mono
    intro ω
    have hle := block_responseLaw_le_reference n B d hd hfit h s ω
    have hm : Measurable (fun U => distinctResponses n B d
        (recordOf (blockSchedule n B d true h (s, U)) ω)) :=
      (distinctResponses_measurable n B d).comp
        ((block_record_measurable n B d true h).comp
          ((measurable_const.prodMk measurable_id).prodMk measurable_const))
    have hp := hle (Prod.mk ω.1 ⁻¹' E)
    rw [Measure.map_apply hm (measurable_prodMk_left hE), Measure.smul_apply,
      smul_eq_mul] at hp
    exact hp
  rw [Measure.bind_apply hE hK.aemeasurable, blockParamLaw,
    lintegral_prod (fun ξ => K ξ E) ((Measure.measurable_coe hE).comp hK).aemeasurable]
  change _ ≤ c * hiddenReferenceLaw n B d D h E
  exact (lintegral_mono hs).trans_eq (by simp)

/-- Restricting to a graph atom costs only its inverse probability in the density bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h,H), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_le_reference
lemma conditionalBlockLaw_le_reference (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d D true h H ≤
      ((retainedGraphMarginal n B d D {H})⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B) •
        hiddenReferenceLaw n B d D h := by
  have hle : ((reducedBlockLaw n B d D true h).restrict {x | x.1 = H}).map Prod.snd ≤
      (reducedBlockLaw n B d D true h).map Prod.snd :=
    Measure.map_mono Measure.restrict_le_self (by fun_prop)
  rw [conditionalBlockLaw, ← smul_smul]
  exact smul_le_smul_left _ (hle.trans (reducedBlockLaw_snd_le_reference n B d hd hfit D h))

/-- A finite domination constant bounds the Radon--Nikodym derivative almost everywhere.  [For the stated data and conditions](hyp:α,P,Q,c,hle), [the stated conclusion holds](goal). -/
-- @node: block_rnDeriv_le_of_le_smul
lemma block_rnDeriv_le_of_le_smul {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [SigmaFinite Q] (c : ℝ≥0∞)
    (hle : P ≤ c • Q) : P.rnDeriv Q ≤ᵐ[Q] fun _ => c := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (P.measurable_rnDeriv Q)
  intro E hE hfin
  rw [lintegral_const, Measure.restrict_apply_univ]
  exact (Measure.setLIntegral_rnDeriv_le E).trans (hle E)

/-- Finite measure domination supplies the square-integrability used by the testing step.  [For the stated data and conditions](hyp:α,P,Q,c,hc,hle), [the stated conclusion holds](goal). -/
-- @node: block_rnDeriv_sub_one_sq_integrable
lemma block_rnDeriv_sub_one_sq_integrable {α : Type*} [MeasurableSpace α]
    (P Q : Measure α) [IsFiniteMeasure Q] (c : ℝ≥0∞) (hc : c ≠ ∞)
    (hle : P ≤ c • Q) :
    Integrable (fun x => ((P.rnDeriv Q x).toReal - 1) ^ 2) Q := by
  have hb := block_rnDeriv_le_of_le_smul P Q c hle
  apply (integrable_const ((c.toReal + 1) ^ 2)).mono'
    (((P.measurable_rnDeriv Q).ennreal_toReal.sub measurable_const).pow_const
      2).aestronglyMeasurable
  filter_upwards [hb] with x hx
  have ht : (P.rnDeriv Q x).toReal ≤ c.toReal := ENNReal.toReal_mono hc hx
  have hn : 0 ≤ (P.rnDeriv Q x).toReal := ENNReal.toReal_nonneg
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ((P.rnDeriv Q x).toReal - 1) ^ 2 ≤ (c.toReal + 1) ^ 2
  have hab : |(P.rnDeriv Q x).toReal - 1| ≤ c.toReal + 1 :=
    (by
      have ha := abs_add_le (P.rnDeriv Q x).toReal (-1)
      simpa [sub_eq_add_neg, abs_of_nonneg hn] using ha.trans (by
        simpa [abs_of_nonneg hn] using add_le_add_right ht 1))
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hab 2

/-- Conditional likelihoods have finite second moments on each positive graph atom.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h,H,hH,σ), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_likelihood_sq_integrable
lemma conditionalBlockLaw_likelihood_sq_integrable (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d D {H} ≠ 0) (σ : Bool) :
    Integrable (fun x =>
      (((conditionalBlockLaw n B d D σ h H).rnDeriv (hiddenReferenceLaw n B d D h) x).toReal
        - 1) ^ 2) (hiddenReferenceLaw n B d D h) := by
  let := hiddenReferenceLaw_probability n B d h D
  let c := (retainedGraphMarginal n B d D {H})⁻¹ * (ENNReal.ofReal ((2 : ℝ) ^ d)) ^ B
  have hc : c ≠ ∞ := ENNReal.mul_ne_top (by simpa using hH) (by simp)
  have hp := conditionalBlockLaw_le_reference n B d hd hfit D h H
  have hbound : conditionalBlockLaw n B d D σ h H ≤ c • hiddenReferenceLaw n B d D h := by
    cases σ
    · have hm := Measure.map_mono hp
        (show Measurable (fun x : Assign (Fin n) × (Fin B → ℝ) =>
          (x.1, fun ℓ => -x.2 ℓ)) by fun_prop)
      rwa [conditionalBlockLaw_sign_reflection, Measure.map_smul, hiddenReferenceLaw_map_neg] at hm
    · exact hp
  exact block_rnDeriv_sub_one_sq_integrable _ _ c hc hbound

/-- The roadmap's conditional testing bound requires no extra square-integrability assumption.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,D,H,hH), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_tvDist_le_sqrt_chiSq_unconditional
lemma conditionalBlockLaw_tvDist_le_sqrt_chiSq_unconditional (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (H : OffDiag (Fin n) → Bool) (hH : retainedGraphMarginal n B d D {H} ≠ 0) :
    Causalean.Stat.tvDist (conditionalBlockLaw n B d D true h H)
      (conditionalBlockLaw n B d D false h H) ≤ Real.sqrt (hiddenChiSq n B d D h H) := by
  exact conditionalBlockLaw_tvDist_le_sqrt_chiSq n B d hd hfit h D H hH
    (conditionalBlockLaw_likelihood_sq_integrable n B d hd hfit D h H hH)

/-- Averaging over the actual complete graph marginal gives the good-event testing bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,D,h,E), [the stated conclusion holds](goal). -/
-- @node: blockMixture_tvDist_good_event_chiSq_le
lemma blockMixture_tvDist_good_event_chiSq_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) (E : Set (OffDiag (Fin n) → Bool)) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤
      (retainedGraphMarginal n B d D).real Eᶜ +
        Real.sqrt (∫ H, E.indicator (hiddenChiSq n B d D h) H
          ∂(retainedGraphMarginal n B d D)) := by
  apply blockMixture_tvDist_good_event_le n B d hd hfit D h E
  have hpos : ∀ᵐ H ∂(retainedGraphMarginal n B d D),
      retainedGraphMarginal n B d D {H} ≠ 0 := ae_iff_of_countable.mpr (fun _ => id)
  filter_upwards [hpos] with H hH
  intro _
  exact conditionalBlockLaw_tvDist_le_sqrt_chiSq_unconditional n B d hd hfit h D H hH

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
