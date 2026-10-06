module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompleteBlockDensity

/-!
# Fixed-partition density of the original hidden-allocation experiment

Before averaging compatible source partitions, the actual responses are independent
translations of the prior baselines. The identities here preserve the complete
retained graph and every assignment coordinate for either sign.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The actual distinct response when all block baselines are zero. -/
-- @node: partitionResponseShift
def partitionResponseShift (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) : Fin B → ℝ :=
  distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, fun _ => 0)) ω)

/-- Adding independent baselines adds them coordinatewise to the actual distinct responses.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,U), [the stated conclusion holds](goal). -/
-- @node: distinctResponses_record_translation
lemma distinctResponses_record_translation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (U : Fin B → ℝ) :
    distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, U)) ω) =
      fun ℓ => U ℓ + partitionResponseShift n B d σ h s ω ℓ := by
  obtain ⟨ε, hε⟩ := distinctResponses_record_row_signs n B d hd hfit σ h s ω
  have hzero := hε (fun _ => 0)
  unfold partitionResponseShift
  rw [hε U, hzero]
  simp only [zero_add]

/-- Product baseline densities translated by the actual fixed-partition response shifts. -/
-- @node: partitionResponseDensity
def partitionResponseDensity (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n))
    (y : Fin B → ℝ) : ℝ :=
  ∏ ℓ, cosSqDensity (y ℓ - partitionResponseShift n B d σ h s ω ℓ)

/-- [The fixed-partition density is measurable jointly in the full design and responses](goal). -/
-- @node: partitionResponseDensity_measurable
@[fun_prop]
lemma partitionResponseDensity_measurable (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) :
    Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
      partitionResponseDensity n B d σ h s x.1 x.2) := by
  apply measurable_from_prod_countable_right
  intro ω
  unfold partitionResponseDensity cosSqDensity
  apply Finset.measurable_prod
  intro ℓ _
  apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const) <;> fun_prop

/-- Conditional on any fixed partition and complete design draw, independent prior baselines
have exactly the translated product response density, for both signs.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: partition_response_density_law
lemma partition_response_density_law (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    (blockBaselineLaw B).map (fun U =>
      distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, U)) ω)) =
    volume.withDensity (fun y => ENNReal.ofReal (partitionResponseDensity n B d σ h s ω y)) := by
  simp_rw [distinctResponses_record_translation n B d hd hfit σ h s ω]
  exact blockBaselineLaw_map_translation B (partitionResponseShift n B d σ h s ω)

/-- Copying the shifted baselines reconstructs the original record for any actual design
realization; detailed edges and ancillary assignments remain in the record.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,U), [the stated conclusion holds](goal). -/
-- @node: partition_record_translation
lemma partition_record_translation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (U : Fin B → ℝ) :
    recordOf (blockSchedule n B d σ h (s, U)) ω =
      copyOutcomes n B d
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)
        (fun ℓ => U ℓ + partitionResponseShift n B d σ h s ω ℓ) := by
  rw [← distinctResponses_record_translation n B d hd hfit σ h s ω U]
  exact (copyOutcomes_distinctResponses_record n B d hd hfit σ h (s, U) ω).symm

/-- Integrating the fixed-partition density against the complete design is equivalent to
independent baselines followed by their actual response translations.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,D), [the stated conclusion holds](goal). -/
-- @node: partition_densityJoint_eq_product_map
lemma partition_densityJoint_eq_product_map (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) :
    densityJoint D volume (partitionResponseDensity n B d σ h s) =
      (D.prod (blockBaselineLaw B)).map (fun x => (x.1,
        distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, x.2)) x.1))) := by
  let := blockBaselineLaw_probability B
  have hm : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
      (x.1, distinctResponses n B d
        (recordOf (blockSchedule n B d σ h (s, x.2)) x.1))) := by
    apply measurable_fst.prodMk
    exact (distinctResponses_measurable n B d).comp
      ((block_record_measurable n B d σ h).comp
        ((measurable_const.prodMk measurable_snd).prodMk measurable_fst))
  ext E hE
  rw [densityJoint, Measure.bind_apply hE
    (measurable_densityJoint_fiber volume _
      (partitionResponseDensity_measurable n B d σ h s)).aemeasurable,
    Measure.map_apply hm hE, Measure.prod_apply (hm hE)]
  apply lintegral_congr
  intro ω
  rw [← partition_response_density_law n B d hd hfit σ h s ω,
    Measure.map_map measurable_prodMk_left (by
      exact (distinctResponses_measurable n B d).comp
        ((block_record_measurable n B d σ h).comp
          ((measurable_const.prodMk measurable_id).prodMk measurable_const))),
    Measure.map_apply (measurable_prodMk_left.comp (by
      exact (distinctResponses_measurable n B d).comp
        ((block_record_measurable n B d σ h).comp
          ((measurable_const.prodMk measurable_id).prodMk measurable_const)))) hE]
  rfl

set_option maxHeartbeats 800000 in
-- The composed record maps need extra elaboration budget.
/-- For a fixed source partition, the complete original-record mixture is exactly obtained
by drawing the actual design and the translated product response density, then copying.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,D), [the stated conclusion holds](goal). -/
-- @node: partition_mixture_density_representation
lemma partition_mixture_density_representation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d σ h (s, U)) =
      (densityJoint D volume (partitionResponseDensity n B d σ h s)).map
        (fun x => copyOutcomes n B d
          ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1)
          x.2) := by
  let := blockBaselineLaw_probability B
  have hr : Measurable (fun x : (Fin B → ℝ) × (Assign (Fin n) × Audit (Fin n)) =>
      recordOf (blockSchedule n B d σ h (s, x.1)) x.2) :=
    (block_record_measurable n B d σ h).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hc : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
      copyOutcomes n B d
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1) x.2) := by
    let f : ((Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ)) →
        (OffDiag (Fin n) → Bool) × (Assign (Fin n) × (Fin B → ℝ)) := fun x =>
      ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1, x.2)
    have hf : Measurable f := by
      apply Measurable.prodMk
      · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1)).comp measurable_fst
      · exact measurable_fst.fst.prodMk measurable_snd
    exact (copyOutcomes_measurable n B d).comp hf
  have hm : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
      (x.1, distinctResponses n B d
        (recordOf (blockSchedule n B d σ h (s, x.2)) x.1))) :=
    measurable_fst.prodMk ((distinctResponses_measurable n B d).comp (hr.comp measurable_swap))
  rw [mixtureLaw_eq_product_map D _ _ hr,
    partition_densityJoint_eq_product_map n B d hd hfit, ← Measure.prod_swap,
    Measure.map_map hr measurable_swap, Measure.map_map hc hm]
  congr 1
  funext x
  dsimp only [Function.comp_apply, Prod.swap]
  exact (copyOutcomes_distinctResponses_record n B d hd hfit σ h (s, x.2) x.1).symm

/-- Drawing partition and baselines independently is equivalent to first mixing the
fixed-partition original-record laws. This identity uses the actual complete design.  [For the stated data and conditions](hyp:n,B,d,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_bind_partition
lemma blockMixtureLawOf_bind_partition (n B d : ℕ) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    blockMixtureLawOf n B d D σ h = (partitionLaw B d).bind (fun s =>
      mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d σ h (s, U))) := by
  let := blockBaselineLaw_probability B
  let K := fun ξ : SourcePartition B d × (Fin B → ℝ) =>
    D.map (recordOf (blockSchedule n B d σ h ξ))
  have hK : Measurable K :=
    block_measurable_map_parameter D _ (block_record_measurable n B d σ h)
  have hL : Measurable (fun s : SourcePartition B d =>
      mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d σ h (s, U))) :=
    measurable_of_finite _
  ext E hE
  change ((partitionLaw B d).prod (blockBaselineLaw B)).bind K E = _
  rw [Measure.bind_apply hE hK.aemeasurable,
    lintegral_prod (fun ξ => K ξ E) ((Measure.measurable_coe hE).comp hK).aemeasurable,
    Measure.bind_apply hE hL.aemeasurable]
  apply lintegral_congr
  intro s
  change _ = (blockBaselineLaw B).bind (fun U => K (s, U)) E
  exact (Measure.bind_apply hE
    (show AEMeasurable (fun U => K (s, U)) (blockBaselineLaw B) from
      (hK.comp (measurable_const.prodMk measurable_id)).aemeasurable)).symm

/-- The full original-record block mixture has an exact density representation conditional
on the true partition and actual design, prior to the posterior-completion calculation.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_partition_density_representation
lemma blockMixtureLawOf_partition_density_representation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    blockMixtureLawOf n B d D σ h = (partitionLaw B d).bind (fun s =>
      (densityJoint D volume (partitionResponseDensity n B d σ h s)).map
        (fun x => copyOutcomes n B d
          ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1)
          x.2)) := by
  rw [blockMixtureLawOf_bind_partition]
  congr 1
  funext s
  exact partition_mixture_density_representation n B d hd hfit σ h s D

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
