module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLaw
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalLikelihoodBounds
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActualLabelWalshBridge

/-!
# The actual positive-graph conditional density

Normalize the full retained-graph fiber without discarding assignment coordinates.
-/

public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Reduction of the reconstructed original record preserves its exact density kernel.  [For the stated data and conditions](hyp:n,B,d,σ,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma reducedBlockLaw_density_bind (n B d : ℕ) (σ : Bool) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    reducedBlockLaw n B d (thinnedDesign (Fin n) q) σ h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (blockDensity n B d σ h hz.1 hz.2 y))).map
          (fun y => (hz.1, hz.2, y))) := by
  have hlaw := (block_law n B d σ h q (thinnedDesign (Fin n) q)
    hn hB hd hfit hh hq (thinnedDesign_assignment (V := Fin n) q hq)
    (thinnedDesign_audit (V := Fin n) q hq)
    (thinnedDesign_independent (V := Fin n) q hq)).2.2.1
  rw [reducedBlockLaw, hlaw, reconstructedLaw,
    block_map_bind _ _ _ (measurable_of_finite _) (by fun_prop)]
  apply Measure.bind_congr_right
  filter_upwards [] with hz
  rw [Measure.map_map (by fun_prop)
    (show Measurable (copyOutcomes n B d hz) from
      (copyOutcomes_measurable n B d).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id)))]
  congr 1
  funext y
  dsimp only [Function.comp_apply]
  rw [distinctResponses_copyOutcomes n B d hd hfit]
  rfl

/-- Graph and full assignment atoms factor under the actual independent design.  [For the stated data and conditions](hyp:n,B,d,q,hq,H,z), [the stated conclusion holds](goal). -/
-- @node: graphAssignMarginal_atom_factor
lemma graphAssignMarginal_atom_factor (n B d : ℕ) (q : ℝ)
    (hq : q ∈ Set.Icc 0 1) (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) :
    graphAssignMarginal n B d (thinnedDesign (Fin n) q) {(H,z)} =
      retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} *
        halfBernoulli (Fin n) {z} := by
  let g := fun s : SourcePartition B d =>
    ((auditLaw (Fin n) q).map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H}
  have ha : graphAssignMarginal n B d (thinnedDesign (Fin n) q) {(H,z)} =
      halfBernoulli (Fin n) {z} * ∫⁻ s, g s ∂partitionLaw B d := by
    rw [graphAssignMarginal, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
    change (∫⁻ s, partitionGraphAssignLaw n B d (thinnedDesign (Fin n) q) s {(H,z)}
      ∂partitionLaw B d) = _
    simp_rw [partitionGraphAssignLaw_atom n B d q hq]
    exact lintegral_const_mul _ (measurable_of_finite _)
  have hg : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} =
      ∫⁻ s, g s ∂partitionLaw B d := by
    rw [retainedGraphMarginal, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      graphAssignMarginal, Measure.bind_apply (by measurability) (by fun_prop)]
    apply lintegral_congr
    intro s
    rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
      Measure.map_map (by fun_prop) (by fun_prop)]
    have he := congrArg (fun μ => μ.map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e))
      (thinnedDesign_audit (V := Fin n) q hq).2.2
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at he
    exact congrArg (fun μ => μ {H}) he
  rw [ha, hg, mul_comm]

/-- [The actual finite response density is measurable jointly with the assignment](goal). -/
-- @node: blockDensity_assignment_measurable
@[fun_prop] lemma blockDensity_assignment_measurable (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) :
    Measurable (fun p : Assign (Fin n) × (Fin B → ℝ) =>
      blockDensity n B d σ h H p.1 p.2) := by
  apply measurable_from_prod_countable_right
  intro z
  simp_rw [blockDensity_allocation_sum]
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro k hk
  split_ifs
  · apply Finset.measurable_prod
    intro ℓ hℓ
    apply measurable_const.mul
    unfold cosSqDensity
    apply Measurable.ite
    · exact measurableSet_le (by fun_prop) measurable_const
    · fun_prop
    · fun_prop
  · fun_prop

/-- Independent reference responses have the product reference density.  [For the stated data and conditions](hyp:B,d,h), [the stated conclusion holds](goal). -/
-- @node: reference_pi_density
lemma reference_pi_density (B d : ℕ) (h : ℝ) :
    Measure.pi (fun v => volume.withDensity
      (fun w => ENNReal.ofReal (refDensity d h w))) =
    volume.withDensity (fun y : Fin B → ℝ =>
      ENNReal.ofReal (∏ v, refDensity d h (y v))) := by
  apply Measure.pi_eq
  intro E hE
  rw [withDensity_apply _ (.univ_pi hE), ← lintegral_indicator (.univ_pi hE)]
  have he : (Set.univ.pi E).indicator
      (fun y : Fin B → ℝ => ENNReal.ofReal (∏ v, refDensity d h (y v))) =
      fun y => ENNReal.ofReal (∏ v, (E v).indicator
        (fun w => refDensity d h w) (y v)) := by
    funext y
    by_cases hy : y ∈ Set.univ.pi E
    · have hy' : ∀ v, y v ∈ E v := by simpa using hy
      simp [hy']
    · have hy' : ∃ v, y v ∉ E v := by simpa using hy
      obtain ⟨v, hv⟩ := hy'
      rw [Set.indicator_of_notMem hy]
      have hz : (∏ v, (E v).indicator (fun w => refDensity d h w) (y v)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        exact Set.indicator_of_notMem hv _
      rw [hz, ENNReal.ofReal_zero]
  rw [he]
  change (∫⁻ y : Fin B → ℝ, ENNReal.ofReal (∏ v,
    (E v).indicator (fun w => refDensity d h w) (y v))
      ∂Measure.pi (fun _ => volume)) = _
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (fun v =>
      ((refDensity_integrable_normalized d h).1.indicator (hE v))))
    (Filter.Eventually.of_forall (fun y => Finset.prod_nonneg (fun v _ =>
      Set.indicator_nonneg (fun _ _ => refDensity_nonneg d h _) _))),
    integral_fintype_prod_eq_prod]
  rw [ENNReal.ofReal_prod_of_nonneg (fun v _ => integral_nonneg
    (fun w => Set.indicator_nonneg (fun _ _ => refDensity_nonneg d h _) w))]
  apply Finset.prod_congr rfl
  intro v _
  rw [withDensity_apply _ (hE v), ← lintegral_indicator (hE v)]
  have he' : (E v).indicator (fun w => ENNReal.ofReal (refDensity d h w)) =
      fun w => ENNReal.ofReal ((E v).indicator (fun w => refDensity d h w) w) := by
    funext w
    by_cases hw : w ∈ E v <;> simp [Set.indicator, hw]
  rw [he']
  exact ofReal_integral_eq_lintegral_ofReal
    ((refDensity_integrable_normalized d h).1.indicator (hE v))
    (Filter.Eventually.of_forall (fun w =>
      Set.indicator_nonneg (fun _ _ => refDensity_nonneg d h _) w))

/-- The normalized positive-graph fiber has the displayed response density and
keeps the entire actual assignment vector.  [For the stated data and conditions](hyp:n,B,d,σ,h,q,hn,hB,hd,hfit,hh,hq,H,hH), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_eq_densityJoint (n B d : ℕ) (σ : Bool) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) σ h H =
      densityJoint (halfBernoulli (Fin n)) volume (blockDensity n B d σ h H) := by
  let ρ := retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H}
  have hρ : ρ ≠ ∞ := by
    let := design_isProbabilityMeasure (thinnedDesign (Fin n) q) q
      (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
      (thinnedDesign_independent q hq)
    let := retainedGraphMarginal_probability n B d (thinnedDesign (Fin n) q)
    exact measure_ne_top _ _
  ext E hE
  rw [conditionalBlockLaw, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply measurable_snd hE, Measure.restrict_apply (measurable_snd hE),
    reducedBlockLaw_density_bind n B d σ h q hn hB hd hfit hh hq,
    Measure.bind_apply (by measurability) (measurable_of_finite _).aemeasurable,
    lintegral_fintype]
  have hf (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) :
      ((volume.withDensity (fun y => ENNReal.ofReal
        (blockDensity n B d σ h hz.1 hz.2 y))).map (fun y => (hz.1, hz.2, y)))
          (Prod.snd ⁻¹' E ∩ {x | x.1 = H}) =
      if hz.1 = H then
        (volume.withDensity (fun y => ENNReal.ofReal
          (blockDensity n B d σ h hz.1 hz.2 y))) (Prod.mk hz.2 ⁻¹' E) else 0 := by
    rw [Measure.map_apply (by fun_prop) (by measurability)]
    by_cases he : hz.1 = H
    · rw [if_pos he]
      congr 1
      ext y
      simp [he]
    · rw [if_neg he]
      have hempty : (fun y => (hz.1, hz.2, y)) ⁻¹'
          (Prod.snd ⁻¹' E ∩ {x | x.1 = H}) = ∅ := by
        ext y
        simp [he]
      rw [hempty, measure_empty]
  simp_rw [hf, graphAssignMarginal_atom_factor n B d q hq]
  rw [Fintype.sum_prod_type]
  have hsum : (∑ G : OffDiag (Fin n) → Bool, ∑ z : Assign (Fin n),
      (if G = H then
        (volume.withDensity (fun y => ENNReal.ofReal (blockDensity n B d σ h G z y)))
          (Prod.mk z ⁻¹' E) else 0) *
        (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {G} *
          halfBernoulli (Fin n) {z})) =
      ρ * ∑ z : Assign (Fin n),
        (volume.withDensity (fun y => ENNReal.ofReal (blockDensity n B d σ h H z y)))
          (Prod.mk z ⁻¹' E) * halfBernoulli (Fin n) {z} := by
    simp only [ite_mul, zero_mul]
    simp_rw [Finset.sum_ite_irrel]
    simp only [Finset.sum_const_zero]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ H), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    dsimp [ρ]
    ring
  rw [hsum, ← mul_assoc, ENNReal.inv_mul_cancel hH hρ, one_mul,
    densityJoint, Measure.bind_apply hE
      (measurable_of_finite _).aemeasurable, lintegral_fintype]
  apply Finset.sum_congr rfl
  intro z _
  rw [Measure.map_apply measurable_prodMk_left hE]

/-- The displayed posterior density is a density relative to the actual
assignment and independent reference responses, including reference-zero sets.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H,hH,s), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_eq_reference_withDensity (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0)
    (s : CompatiblePartition n B d H) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h).withDensity
        (fun p => ENNReal.ofReal
          (blockDensity n B d true h H p.1 p.2 / (∏ ℓ, refDensity d h (p.2 ℓ)))) := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (halfBernoulli (Fin n)) := by
    unfold halfBernoulli; infer_instance
  let := bernoulliLaw_probability q hq
  let : IsProbabilityMeasure (auditLaw (Fin n) q) := by unfold auditLaw; infer_instance
  rw [conditionalBlockLaw_eq_densityJoint n B d true h q hn hB hd hfit hh hq H hH,
    densityJoint_eq_withDensity _ _ _ (blockDensity_assignment_measurable n B d true h H),
    hiddenReferenceLaw, show (thinnedDesign (Fin n) q).map Prod.fst =
      halfBernoulli (Fin n) from thinnedDesign_assignment q hq,
    reference_pi_density, prod_withDensity_right (by fun_prop),
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  dsimp only [Pi.mul_apply]
  have hprod : 0 ≤ ∏ ℓ, refDensity d h (p.2 ℓ) :=
    Finset.prod_nonneg (fun ℓ _ => refDensity_nonneg d h _)
  by_cases hz : (∏ ℓ, refDensity d h (p.2 ℓ)) = 0
  · obtain ⟨ℓ, _, hℓ⟩ := Finset.prod_eq_zero_iff.mp hz
    rw [blockDensity_zero_of_reference_zero n B d hd hfit h H p.1 s p.2 ℓ hℓ,
      hz]
    simp
  · rw [← ENNReal.ofReal_mul hprod, mul_div_cancel₀ _ hz]

/-- The actual conditional Radon--Nikodym likelihood is the complete-label
posterior density ratio almost everywhere under the reference.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H,hH,s), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_rnDeriv_density_ratio (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0)
    (s : CompatiblePartition n B d H) :
    (fun p => ((conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H).rnDeriv
      (hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h) p).toReal) =ᵐ[
        hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h]
      fun p => blockDensity n B d true h H p.1 p.2 / (∏ ℓ, refDensity d h (p.2 ℓ)) := by
  let := design_isProbabilityMeasure (thinnedDesign (Fin n) q) q
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)
  let := hiddenReferenceLaw_probability n B d h (thinnedDesign (Fin n) q)
  rw [conditionalBlockLaw_eq_reference_withDensity n B d h q hn hB hd hfit hh hq H hH s]
  have he := Measure.rnDeriv_withDensity
    (hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h)
    (show Measurable (fun p : Assign (Fin n) × (Fin B → ℝ) => ENNReal.ofReal
      (blockDensity n B d true h H p.1 p.2 / (∏ ℓ, refDensity d h (p.2 ℓ)))) by fun_prop)
  filter_upwards [he] with p hp
  rw [hp, ENNReal.toReal_ofReal (div_nonneg
    (blockDensity_nonneg n B d true h H p.1 p.2)
    (Finset.prod_nonneg (fun ℓ _ => refDensity_nonneg d h _)))]

/-- Conditional chi-square is exactly the original-assignment density energy;
the density identification and Fubini step use the actual conditional law.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H,hH,s), [the stated conclusion holds](goal). -/
lemma hiddenChiSq_eq_actualDensityEnergy (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool)
    (hH : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0)
    (s : CompatiblePartition n B d H) :
    hiddenChiSq n B d (thinnedDesign (Fin n) q) h H = actualDensityEnergy n B d h H := by
  let := design_isProbabilityMeasure (thinnedDesign (Fin n) q) q
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)
  have he := conditionalBlockLaw_rnDeriv_density_ratio n B d h q
    hn hB hd hfit hh hq H hH s
  have hs : (fun p =>
      (((conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H).rnDeriv
        (hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h) p).toReal - 1) ^ 2) =ᵐ[
          hiddenReferenceLaw n B d (thinnedDesign (Fin n) q) h]
      fun p => (blockDensity n B d true h H p.1 p.2 /
        (∏ ℓ, refDensity d h (p.2 ℓ)) - 1) ^ 2 := by
    filter_upwards [he] with p hp
    rw [hp]
  have hi := (conditionalBlockLaw_likelihood_sq_integrable n B d hd hfit
    (thinnedDesign (Fin n) q) h H hH true).congr hs
  rw [hiddenReferenceLaw, show (thinnedDesign (Fin n) q).map Prod.fst =
    halfBernoulli (Fin n) from thinnedDesign_assignment q hq] at hi
  rw [hiddenChiSq, Causalean.Stat.chiSqDiv, integral_congr_ae hs,
    hiddenReferenceLaw, show (thinnedDesign (Fin n) q).map Prod.fst =
      halfBernoulli (Fin n) from thinnedDesign_assignment q hq,
    integral_prod_symm _ hi]
  rfl

/-- The good-event comparison is an equality after averaging over every detailed
graph atom. Null atoms need no conditional likelihood convention.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma hiddenChiSq_good_integral_eq_actualDensityEnergy (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
      (hiddenChiSq n B d (thinnedDesign (Fin n) q) h) H
      ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) =
    (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
      (actualDensityEnergy n B d h) H
      ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) := by
  have hpos : ∀ᵐ H ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q),
      retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0 :=
    ae_iff_of_countable.mpr (fun _ => id)
  apply integral_congr_ae
  filter_upwards [hpos, retainedGraphMarginal_valid n B d
    (thinnedDesign (Fin n) q) hfit] with H hH hv
  obtain ⟨_, s, hs⟩ := hv
  by_cases hg : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H
  · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_true]
    exact hiddenChiSq_eq_actualDensityEnergy n B d h q hn hB hd hfit hh hq H hH ⟨s, hs⟩
  · simp only [Set.indicator, Set.mem_ofPred_eq, hg, if_false]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
