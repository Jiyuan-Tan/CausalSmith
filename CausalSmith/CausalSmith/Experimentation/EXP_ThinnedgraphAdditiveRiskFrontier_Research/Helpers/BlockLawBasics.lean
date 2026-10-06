module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTranslationAffinity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockReveal
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockSupport
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DetailedGraphLikelihood

/-!
# Complete original-record block likelihood
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A normalized baseline remains a probability law after taking independent blocks.  [For the stated data and conditions](hyp:B), [the stated conclusion holds](goal). -/
-- @node: blockBaselineLaw_probability
lemma blockBaselineLaw_probability (B : ℕ) : IsProbabilityMeasure (blockBaselineLaw B) := by
  have hnorm : (volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))) Set.univ = 1 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal cosSqDensity_integrable_normalized.1
        (Filter.Eventually.of_forall cosSqDensity_nonneg),
      cosSqDensity_integrable_normalized.2]
    simp
  let : IsProbabilityMeasure (volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))) :=
    ⟨hnorm⟩
  unfold blockBaselineLaw
  infer_instance

/-- Mapping a measurable channel commutes with mixing its input laws.  [For the stated data and conditions](hyp:α,β,γ,μ,K,g,hK,hg), [the stated conclusion holds](goal). -/
-- @node: block_map_bind
lemma block_map_bind {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (K : α → Measure β) (g : β → γ)
    (hK : Measurable K) (hg : Measurable g) :
    (μ.bind K).map g = μ.bind (fun a => (K a).map g) := by
  rw [← Measure.bind_dirac_eq_map _ hg,
    Measure.bind_bind (g := fun x => Measure.dirac (g x)) hK.aemeasurable
      (show AEMeasurable (fun x => Measure.dirac (g x)) _ from
        (Measure.measurable_dirac.comp hg).aemeasurable)]
  congr 1
  funext a
  exact Measure.bind_dirac_eq_map _ hg

/-- [A jointly measurable recording function](hyp:hf) yields [a measurable family of output laws](goal). -/
-- @node: block_measurable_map_parameter
@[fun_prop]
lemma block_measurable_map_parameter {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure β) [SFinite μ]
    (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => μ.map (fun b => f (a, b))) := by
  have h := (Measure.measurable_map f hf).comp
    (Measurable.map_prodMk_left (ν := μ))
  simpa only [Measure.map_map hf measurable_prodMk_left, Function.comp_def] using h

/-- [The complete block record depends measurably on its prior parameters and design draw](goal). -/
-- @node: block_record_measurable
@[fun_prop]
lemma block_record_measurable (n B d : ℕ) (σ : Bool) (h : ℝ) :
    Measurable (fun x : (SourcePartition B d × (Fin B → ℝ)) ×
      (Assign (Fin n) × Audit (Fin n)) => recordOf (blockSchedule n B d σ h x.1) x.2) := by
  apply measurable_from_prod_countable_left
  intro ω
  apply measurable_from_prod_countable_right
  intro s
  simp only [recordOf, potentialOutcome, blockSchedule, inNbhd, zero_mul, add_zero]
  apply measurable_const.prodMk
  apply measurable_const.prodMk
  apply measurable_pi_lambda
  intro i
  apply Measurable.add
  · apply Finset.measurable_sum
    intro ℓ hℓ
    by_cases hi : i ∈ recipientBlock n B d ℓ <;> simp only [hi, ite_true, ite_false] <;> fun_prop
  · exact measurable_const

/-- Mixing independent baselines preserves the detailed retained graph and the entire
assignment marginal, for either sign and every amplitude.  [For the stated data and conditions](hyp:n,B,d,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: block_mixture_graphAssignMarginal
lemma block_mixture_graphAssignMarginal (n B d : ℕ) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [SFinite D] :
    (blockMixtureLawOf n B d D σ h).map (fun o => (o.1, o.2.1)) =
      graphAssignMarginal n B d D := by
  let := blockBaselineLaw_probability B
  unfold blockMixtureLawOf mixtureLaw
  rw [block_map_bind _ _ _
    (block_measurable_map_parameter D _ (block_record_measurable n B d σ h))
    (by fun_prop)]
  have hrecord (ξ : SourcePartition B d × (Fin B → ℝ)) :
      (D.map (recordOf (blockSchedule n B d σ h ξ))).map (fun o => (o.1, o.2.1)) =
        D.map (fun ω => ((recordOf (blockSchedule n B d true 0
          (ξ.1, fun _ => 0)) ω).1, ω.1)) := by
    rw [Measure.map_map (by fun_prop) (measurable_of_finite _)]
    rfl
  simp_rw [hrecord]
  unfold blockParamLaw graphAssignMarginal
  ext E hE
  let K := fun s : SourcePartition B d =>
    D.map (fun ω => ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1))
  have hK : Measurable K := measurable_of_finite _
  change ((partitionLaw B d).prod (blockBaselineLaw B)).bind (K ∘ Prod.fst) E =
    (partitionLaw B d).bind K E
  rw [Measure.bind_apply hE (hK.comp measurable_fst).aemeasurable,
    Measure.bind_apply hE hK.aemeasurable]
  rw [lintegral_prod (fun ξ : SourcePartition B d × (Fin B → ℝ) => ((K ∘ Prod.fst) ξ) E)
    (show AEMeasurable (fun ξ : SourcePartition B d × (Fin B → ℝ) => ((K ∘ Prod.fst) ξ) E) _ from
      ((Measure.measurable_coe hE).comp (hK.comp measurable_fst)).aemeasurable)]
  simp

/-- With no hidden capacity, the observed hidden treated count and its binomial denominator
are fixed at zero and one.  [For the stated data and conditions](hyp:n,B,d,D,hfit), [the stated conclusion holds](goal). -/
-- @node: block_hidden_zero_endpoint
lemma block_hidden_zero_endpoint (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (hfit : 2 * (B * d) ≤ n) :
    ∀ᵐ hz ∂(graphAssignMarginal n B d D),
      undiscovered n B d hz.1 = 0 → hiddenTreated n B d hz.1 hz.2 = 0 ∧
        (undiscovered n B d hz.1).choose (hiddenTreated n B d hz.1 hz.2) = 1 := by
  have hv := (ae_map_iff (by fun_prop) (by measurability)).mp
    (retainedGraphMarginal_valid n B d D hfit)
  filter_upwards [hv] with hz hhz
  intro hzero
  have hK := hiddenTreated_le n B d hz.1 hhz hz.2
  have hKzero : hiddenTreated n B d hz.1 hz.2 = 0 := Nat.eq_zero_of_le_zero (hzero ▸ hK)
  exact ⟨hKzero, by rw [hzero, hKzero]; rfl⟩

/-- Every finite product of weighted translated baseline densities is integrable,
and its integral is the product of the weights.  [For the stated data and conditions](hyp:B,c,s), [the stated conclusion holds](goal). -/
-- @node: block_weighted_baseline_product_integrable_normalized
lemma block_weighted_baseline_product_integrable_normalized (B : ℕ)
    (c s : Fin B → ℝ) :
    Integrable (fun y : Fin B → ℝ => ∏ ℓ, c ℓ * cosSqDensity (y ℓ - s ℓ)) ∧
      (∫ y : Fin B → ℝ, ∏ ℓ, c ℓ * cosSqDensity (y ℓ - s ℓ)) = ∏ ℓ, c ℓ := by
  constructor
  · exact Integrable.fintype_prod (fun ℓ =>
      (translated_cosSqDensity_integrable_normalized (s ℓ)).1.const_mul (c ℓ))
  · rw [integral_fintype_prod_volume_eq_prod
      (fun ℓ w => c ℓ * cosSqDensity (w - s ℓ))]
    simp_rw [integral_const_mul, (translated_cosSqDensity_integrable_normalized _).2,
      mul_one]

/-- The constrained density integrates to one on every valid retained graph, since its
finite allocation weights are normalized; no posterior-law identification is assumed.  [For the stated data and conditions](hyp:n,B,d,σ,h,H,hH,z), [the stated conclusion holds](goal). -/
-- @node: blockDensity_integrable_normalized
lemma blockDensity_integrable_normalized (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (hH : ValidRetainedGraph n B d H)
    (z : Assign (Fin n)) :
    Integrable (blockDensity n B d σ h H z) ∧
      (∫ y, blockDensity n B d σ h H z y) = 1 := by
  let c := fun (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) (ℓ : Fin B) =>
    ((capacity n B d H ℓ).choose (k ℓ).val : ℝ)
  let s := fun (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) (ℓ : Fin B) =>
    signOf σ * h *
      (revealedSignSum n B d H z ℓ + 2 * (k ℓ).val - capacity n B d H ℓ) / (2 * d)
  let f := fun (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) (y : Fin B → ℝ) =>
    if hiddenTreated n B d H z = ∑ ℓ, (k ℓ).val then
      ∏ ℓ, c k ℓ * cosSqDensity (y ℓ - s k ℓ) else 0
  have hf (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) : Integrable (f k) := by
    dsimp only [f]
    split_ifs
    · exact (block_weighted_baseline_product_integrable_normalized B (c k) (s k)).1
    · exact integrable_zero (Fin B → ℝ) ℝ volume
  have he : blockDensity n B d σ h H z = fun y =>
      (∑ k, f k y) / ((undiscovered n B d H).choose (hiddenTreated n B d H z) : ℝ) := by
    funext y
    exact blockDensity_allocation_sum n B d σ h H z y
  rw [he]
  constructor
  · exact (integrable_finsetSum _ (fun k _ => hf k)).div_const _
  · rw [integral_div, integral_finsetSum _ (fun k _ => hf k)]
    have hfi (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) :
        (∫ y, f k y) =
          if hiddenTreated n B d H z = ∑ ℓ, (k ℓ).val then ∏ ℓ, c k ℓ else 0 := by
      dsimp only [f]
      split_ifs
      · exact (block_weighted_baseline_product_integrable_normalized B (c k) (s k)).2
      · simp
    simp_rw [hfi]
    rw [Finset.sum_div]
    exact block_allocation_weights_normalized B (capacity n B d H)
      (hiddenTreated n B d H z) (hiddenTreated_le n B d H hH z)

/-- On a valid retained graph, the displayed conditional density defines a probability
law of the distinct responses, including the zero-hidden-capacity endpoint.  [For the stated data and conditions](hyp:n,B,d,σ,h,H,hH,z), [the stated conclusion holds](goal). -/
-- @node: blockDensityLaw_probability
lemma blockDensityLaw_probability (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (hH : ValidRetainedGraph n B d H)
    (z : Assign (Fin n)) :
    IsProbabilityMeasure (volume.withDensity
      (fun y => ENNReal.ofReal (blockDensity n B d σ h H z y))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      (blockDensity_integrable_normalized n B d σ h H hH z).1
      (Filter.Eventually.of_forall (blockDensity_nonneg n B d σ h H z)),
    (blockDensity_integrable_normalized n B d σ h H hH z).2]
  simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
