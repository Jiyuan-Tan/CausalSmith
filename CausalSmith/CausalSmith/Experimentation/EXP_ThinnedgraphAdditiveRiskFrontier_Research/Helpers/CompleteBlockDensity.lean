module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTransport
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompleteBlockRecord

/-!
# Complete-block conditional density identification

Translation of the independent prior baselines gives the normalized product
response density, conditional on every coordinate of the actual design.
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The product of translated baseline laws is the product density against vector volume.  [For the stated data and conditions](hyp:B,s), [the stated conclusion holds](goal). -/
-- @node: baseline_pi_translated_density
lemma baseline_pi_translated_density (B : ℕ) (s : Fin B → ℝ) :
    Measure.pi (fun v => volume.withDensity
      (fun w => ENNReal.ofReal (cosSqDensity (w - s v)))) =
    volume.withDensity (fun y : Fin B → ℝ =>
      ENNReal.ofReal (∏ v, cosSqDensity (y v - s v))) := by
  apply Measure.pi_eq
  intro E hE
  rw [withDensity_apply _ (.univ_pi hE), ← lintegral_indicator (.univ_pi hE)]
  have he : (Set.univ.pi E).indicator
      (fun y : Fin B → ℝ => ENNReal.ofReal (∏ v, cosSqDensity (y v - s v))) =
      fun y => ENNReal.ofReal (∏ v, (E v).indicator
        (fun w => cosSqDensity (w - s v)) (y v)) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi E
    · have hy' : ∀ v, y v ∈ E v := by simpa using hy
      simp [hy']
    · have hy' : ∃ v, y v ∉ E v := by simpa using hy
      obtain ⟨v, hv⟩ := hy'
      rw [Set.indicator_of_notMem hy]
      have hz : (∏ v, (E v).indicator (fun w => cosSqDensity (w - s v)) (y v)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        exact Set.indicator_of_notMem hv _
      rw [hz, ENNReal.ofReal_zero]
  rw [he]
  change (∫⁻ y : Fin B → ℝ, ENNReal.ofReal (∏ v,
    (E v).indicator (fun w => cosSqDensity (w - s v)) (y v))
      ∂Measure.pi (fun _ => volume)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun v =>
      ((translated_cosSqDensity_integrable_normalized (s v)).1.indicator (hE v))))
    (Filter.Eventually.of_forall (fun y => Finset.prod_nonneg (fun v _ =>
      Set.indicator_nonneg (fun _ _ => cosSqDensity_nonneg _) _))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg
    (fun w => Set.indicator_nonneg (fun _ _ => cosSqDensity_nonneg _) w))]
  apply Finset.prod_congr rfl
  intro v _
  rw [withDensity_apply _ (hE v), ← lintegral_indicator (hE v)]
  have he' : (E v).indicator (fun w => ENNReal.ofReal (cosSqDensity (w - s v))) =
      fun w => ENNReal.ofReal ((E v).indicator (fun w => cosSqDensity (w - s v)) w) := by
    funext w
    by_cases hw : w ∈ E v <;> simp [Set.indicator, hw]
  rw [he']
  exact ofReal_integral_eq_lintegral_ofReal
    ((translated_cosSqDensity_integrable_normalized (s v)).1.indicator (hE v))
    (Filter.Eventually.of_forall (fun w =>
      Set.indicator_nonneg (fun _ _ => cosSqDensity_nonneg _) w))

/-- Independently translating all prior baselines gives the exact vector response density.  [For the stated data and conditions](hyp:B,s), [the stated conclusion holds](goal). -/
-- @node: blockBaselineLaw_map_translation
lemma blockBaselineLaw_map_translation (B : ℕ) (s : Fin B → ℝ) :
    (blockBaselineLaw B).map (fun U v => U v + s v) =
      volume.withDensity (fun y : Fin B → ℝ =>
        ENNReal.ofReal (∏ v, cosSqDensity (y v - s v))) := by
  have hp (v : Fin B) : IsProbabilityMeasure
      ((volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))).map
        (fun w => w + s v)) := by
    rw [baseline_map_add_density]
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal
        (translated_cosSqDensity_integrable_normalized (s v)).1
        (Filter.Eventually.of_forall (fun _ => cosSqDensity_nonneg _)),
      (translated_cosSqDensity_integrable_normalized (s v)).2]
    simp
  let _ := hp
  rw [blockBaselineLaw, Measure.pi_map_pi (f := fun v w => w + s v) (fun _ => (by fun_prop))]
  simp_rw [baseline_map_add_density]
  exact baseline_pi_translated_density B s

/-- Conditional on the entire assignment, complete-block responses have the stated density.  [For the stated data and conditions](hyp:n,d,σ,h,z), [the stated conclusion holds](goal). -/
-- @node: completeBlock_response_law
lemma completeBlock_response_law (n d : ℕ) (σ : Bool) (h : ℝ) (z : Assign (Fin n)) :
    (blockBaselineLaw (n / (d + 1))).map
      (fun U v => U v + completeBlockShift n d σ h z v) =
    volume.withDensity (fun y => ENNReal.ofReal (completeBlockResponseDensity n d σ h z y)) := by
  exact blockBaselineLaw_map_translation _ (completeBlockShift n d σ h z)

/-- Mixing a jointly measurable recording channel is the pushforward of the independent
prior-design product law.  [For the stated data and conditions](hyp:V,Ξ,D,π,s,hm), [the stated conclusion holds](goal). -/
-- @node: mixtureLaw_eq_product_map
lemma mixtureLaw_eq_product_map {V Ξ : Type*} [Fintype V] [DecidableEq V]
    [MeasurableSpace Ξ] (D : Measure (Assign V × Audit V)) [IsProbabilityMeasure D]
    (π : Measure Ξ) (s : Ξ → Schedule V)
    (hm : Measurable (fun x : Ξ × (Assign V × Audit V) => recordOf (s x.1) x.2)) :
    mixtureLaw D π s = (π.prod D).map (fun x => recordOf (s x.1) x.2) := by
  ext E hE
  rw [mixtureLaw, Measure.bind_apply hE (measurable_record_components D s hm).aemeasurable,
    Measure.map_apply hm hE, Measure.prod_apply (hm hE)]
  apply lintegral_congr
  intro ξ
  have hr : Measurable (recordOf (s ξ)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  rw [Measure.map_apply hr hE]
  rfl

/-- Retaining the entire design draw, the conditional product-density joint law is exactly
independent baselines translated by the observed signs.  [For the stated data and conditions](hyp:n,d,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: completeBlock_densityJoint_eq_product_map
lemma completeBlock_densityJoint_eq_product_map (n d : ℕ) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) :
    densityJoint D volume (fun ω y => completeBlockResponseDensity n d σ h ω.1 y) =
      (D.prod (blockBaselineLaw (n / (d + 1)))).map
        (fun x => (x.1, fun v => x.2 v + completeBlockShift n d σ h x.1.1 v)) := by
  let := blockBaselineLaw_probability (n / (d + 1))
  have hm : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ) =>
      (x.1, fun v => x.2 v + completeBlockShift n d σ h x.1.1 v)) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro v
    apply Measurable.add
    · fun_prop
    · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
        completeBlockShift n d σ h ω.1 v)).comp measurable_fst
  ext E hE
  rw [densityJoint, Measure.bind_apply hE
    (measurable_densityJoint_fiber volume _
      (completeBlockResponseDensity_measurable n d σ h)).aemeasurable,
    Measure.map_apply hm hE, Measure.prod_apply (hm hE)]
  apply lintegral_congr
  intro ω
  rw [← completeBlock_response_law,
    Measure.map_map measurable_prodMk_left (by fun_prop),
    Measure.map_apply (show Measurable (Prod.mk ω ∘
      (fun (U : Fin (n / (d + 1)) → ℝ) v =>
        U v + completeBlockShift n d σ h ω.1 v)) from
        measurable_prodMk_left.comp (by fun_prop)) hE]
  rfl

/-- The actual full-record prior mixture is the copying of the conditional-density joint
law with its full assignment-audit marginal.  [For the stated data and conditions](hyp:n,d,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: completeBlock_mixture_density_representation
lemma completeBlock_mixture_density_representation (n d : ℕ) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    mixtureLaw D (blockBaselineLaw (n / (d + 1))) (completeBlockSchedule n d σ h) =
      (densityJoint D volume (fun ω y => completeBlockResponseDensity n d σ h ω.1 y)).map
        (fun x => completeBlockCopy n d
          (((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) x.1).1,
            x.1.1), x.2)) := by
  let := blockBaselineLaw_probability (n / (d + 1))
  have hc : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ) => completeBlockCopy n d
        (((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) x.1).1,
          x.1.1), x.2)) := by
    apply (completeBlockCopy_measurable n d).comp
    apply Measurable.prodMk
    · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
        ((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) ω).1, ω.1))).comp
          measurable_fst
    · fun_prop
  rw [mixtureLaw_eq_product_map D _ _ (completeBlock_record_measurable n d σ h),
    completeBlock_densityJoint_eq_product_map, ← Measure.prod_swap]
  rw [Measure.map_map (completeBlock_record_measurable n d σ h) measurable_swap,
    Measure.map_map hc (by
      apply measurable_fst.prodMk
      apply measurable_pi_lambda
      intro v
      apply Measurable.add
      · fun_prop
      · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
          completeBlockShift n d σ h ω.1 v)).comp measurable_fst)]
  congr 1
  funext x
  dsimp only [Function.comp_apply, Prod.swap]
  rw [completeBlock_record_reconstruction, completeBlock_record_graph]

/-- The common full-design marginal makes the joint response distance at most the square
root of the averaged translation energy.  [For the stated data and conditions](hyp:n,d,h,D), [the stated conclusion holds](goal). -/
-- @node: completeBlock_densityJoint_tv_le
lemma completeBlock_densityJoint_tv_le (n d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    Causalean.Stat.tvDist
      (densityJoint D volume (fun ω y => completeBlockResponseDensity n d true h ω.1 y))
      (densityJoint D volume (fun ω y => completeBlockResponseDensity n d false h ω.1 y)) ≤
    Real.sqrt (∫ ω, hellingerEnergy volume (completeBlockResponseDensity n d true h ω.1)
      (completeBlockResponseDensity n d false h ω.1) ∂D) := by
  let P := densityJoint D volume (fun ω y => completeBlockResponseDensity n d true h ω.1 y)
  let M := densityJoint D volume (fun ω y => completeBlockResponseDensity n d false h ω.1 y)
  let := densityJoint_probability D volume _
    (completeBlockResponseDensity_measurable n d true h)
    (fun ω => completeBlockResponseDensity_probability n d true h ω.1)
  let := densityJoint_probability D volume _
    (completeBlockResponseDensity_measurable n d false h)
    (fun ω => completeBlockResponseDensity_probability n d false h ω.1)
  have he := (common_marginal_hellinger_averaging D volume _ _
    (completeBlockResponseDensity_measurable n d true h)
    (completeBlockResponseDensity_measurable n d false h)
    (fun ω => completeBlockResponseDensity_nonneg n d true h ω.1)
    (fun ω => completeBlockResponseDensity_nonneg n d false h ω.1)
    (fun ω => completeBlockResponseDensity_probability n d true h ω.1)
    (fun ω => completeBlockResponseDensity_probability n d false h ω.1)).1
  have he0 : 0 ≤ Causalean.Stat.Minimax.hellingerSqMeasure P M := by
    rw [he]
    exact integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  calc
    _ ≤ Real.sqrt (Causalean.Stat.Minimax.hellingerSqMeasure P M *
      (1 - Causalean.Stat.Minimax.hellingerSqMeasure P M / 4)) :=
        Causalean.Stat.Minimax.tvDist_le_sharp_hellinger P M
    _ ≤ Real.sqrt (Causalean.Stat.Minimax.hellingerSqMeasure P M) := by
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (Causalean.Stat.Minimax.hellingerSqMeasure P M)]
    _ = _ := by rw [he]

/-- The genuine complete original-record mixtures satisfy the population translation bound;
projection retains the labeled graph and every treatment coordinate.  [For the stated data and conditions](hyp:n,d,h,D,ha), [the stated conclusion holds](goal). -/
-- @node: completeBlock_mixture_tv_population_le
lemma completeBlock_mixture_tv_population_le (n d : ℕ) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (ha : AssignmentLaw D) :
    Causalean.Stat.tvDist
      (mixtureLaw D (blockBaselineLaw (n / (d + 1))) (completeBlockSchedule n d true h))
      (mixtureLaw D (blockBaselineLaw (n / (d + 1))) (completeBlockSchedule n d false h)) ≤
      Real.sqrt (4 * Real.pi ^ 2 * h ^ 2 * n / ((d : ℝ) + 1) ^ 2) := by
  let := densityJoint_probability D volume _
    (completeBlockResponseDensity_measurable n d true h)
    (fun ω => completeBlockResponseDensity_probability n d true h ω.1)
  let := densityJoint_probability D volume _
    (completeBlockResponseDensity_measurable n d false h)
    (fun ω => completeBlockResponseDensity_probability n d false h ω.1)
  have hc : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ) => completeBlockCopy n d
        (((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) x.1).1,
          x.1.1), x.2)) := by
    apply (completeBlockCopy_measurable n d).comp
    apply Measurable.prodMk
    · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
        ((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) ω).1, ω.1))).comp
          measurable_fst
    · fun_prop
  rw [completeBlock_mixture_density_representation, completeBlock_mixture_density_representation]
  exact (block_tvDist_map_le _ _ _ hc).trans
    ((completeBlock_densityJoint_tv_le n d h D).trans
      (Real.sqrt_le_sqrt (completeBlock_response_energy_population_le n d h D ha)))

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
