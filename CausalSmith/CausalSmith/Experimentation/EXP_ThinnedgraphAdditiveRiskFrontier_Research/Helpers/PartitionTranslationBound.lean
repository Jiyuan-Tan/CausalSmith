module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PartitionResponseDensity

/-!
# Translation testing bound conditional on the true partition

The actual labeled source sums have second moment d under the assignment marginal.
Tensorized baseline translation and common-marginal Hellinger averaging then bound
the complete original-record distance for each fixed partition.
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The fixed-partition shift uses the actual incoming source labels of any recipient.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: partitionResponseShift_eq_source_sum
lemma partitionResponseShift_eq_source_sum (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (ℓ : Fin B) (i : Fin n)
    (hi : i ∈ recipientBlock n B d ℓ) :
    partitionResponseShift n B d σ h s ω ℓ = signOf σ * h / (2 * d) *
      ∑ j ∈ inNbhd (blockSchedule n B d true 0 (s, fun _ => 0)) i, signOf (ω.1 j) := by
  unfold partitionResponseShift
  rw [distinctResponses_record_recipient n B d hd hfit σ h (s, fun _ => 0) ω ℓ i hi,
    blockSchedule_response_centered n B d hd hfit σ h (s, fun _ => 0) ω.1 ℓ i hi]
  simp only [zero_add]
  rfl

/-- Opposite signs have exactly h squared over d expected squared shift separation.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,D,ha,ℓ), [the stated conclusion holds](goal). -/
-- @node: partition_shift_separation_moment
lemma partition_shift_separation_moment (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (ha : AssignmentLaw D) (ℓ : Fin B) :
    (∫ ω, (partitionResponseShift n B d true h s ω ℓ -
      partitionResponseShift n B d false h s ω ℓ) ^ 2 ∂D) = h ^ 2 / d := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (recipientBlock n B d ℓ).card by
    rw [recipientBlock_card n B d hfit ℓ]; omega)
  let N := inNbhd (blockSchedule n B d true 0 (s, fun _ => 0)) i
  have hc : N.card = d := blockSchedule_inNbhd_card n B d hd hfit true 0 _ i ℓ hi
  have hm : (∫ ω, (∑ j ∈ N, signOf (ω.1 j)) ^ 2 ∂D) = (d : ℝ) := by
    rw [← integral_map measurable_fst.aemeasurable
      (show AEStronglyMeasurable (fun z : Assign (Fin n) =>
        (∑ j ∈ N, signOf (z j)) ^ 2) (D.map Prod.fst) from
        (measurable_of_finite _).aestronglyMeasurable), ha,
      reverse_revealed_second_moment, hc]
  have he (ω : Assign (Fin n) × Audit (Fin n)) :
      (partitionResponseShift n B d true h s ω ℓ -
        partitionResponseShift n B d false h s ω ℓ) ^ 2 =
      (h / d) ^ 2 * (∑ j ∈ N, signOf (ω.1 j)) ^ 2 := by
    rw [partitionResponseShift_eq_source_sum n B d hd hfit true h s ω ℓ i hi,
      partitionResponseShift_eq_source_sum n B d hd hfit false h s ω ℓ i hi]
    simp only [signOf, Bool.false_eq_true, ite_true, ite_false]
    dsimp only [N]
    ring
  simp_rw [he]
  rw [integral_const_mul, hm]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp

/-- Tensorized translation controls fixed-partition response energy at each design draw.  [For the stated data and conditions](hyp:n,B,d,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: partition_response_energy_le
lemma partition_response_energy_le (n B d : ℕ) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    hellingerEnergy volume (partitionResponseDensity n B d true h s ω)
      (partitionResponseDensity n B d false h s ω) ≤
    ∑ ℓ : Fin B, 4 * Real.pi ^ 2 *
      (partitionResponseShift n B d true h s ω ℓ -
        partitionResponseShift n B d false h s ω ℓ) ^ 2 := by
  exact baseline_translation_affinity.2.2.2.1 B
    (partitionResponseShift n B d true h s ω) (partitionResponseShift n B d false h s ω)

/-- Averaging the translation bound keeps every assignment and audit coordinate.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,D,ha), [the stated conclusion holds](goal). -/
-- @node: partition_response_energy_mean_le
lemma partition_response_energy_mean_le (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (ha : AssignmentLaw D) :
    (∫ ω, hellingerEnergy volume (partitionResponseDensity n B d true h s ω)
      (partitionResponseDensity n B d false h s ω) ∂D) ≤
      4 * Real.pi ^ 2 * h ^ 2 * B / d := by
  calc
    _ ≤ ∫ ω, ∑ ℓ : Fin B, 4 * Real.pi ^ 2 *
        (partitionResponseShift n B d true h s ω ℓ -
          partitionResponseShift n B d false h s ω ℓ) ^ 2 ∂D :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun ω => partition_response_energy_le n B d h s ω)
    _ = _ := by
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      simp_rw [integral_const_mul, partition_shift_separation_moment n B d hd hfit h s D ha]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Fixed-partition product densities are nonnegative.  [For the stated data and conditions](hyp:n,B,d,σ,h,s,ω,y), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_nonneg
lemma partitionResponseDensity_nonneg (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ) :
    0 ≤ partitionResponseDensity n B d σ h s ω y := by
  exact Finset.prod_nonneg (fun _ _ => cosSqDensity_nonneg _)

/-- Independent translated baselines normalize every fixed-partition response density.  [For the stated data and conditions](hyp:n,B,d,σ,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_probability
lemma partitionResponseDensity_probability (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) :
    IsProbabilityMeasure (volume.withDensity
      (fun y => ENNReal.ofReal (partitionResponseDensity n B d σ h s ω y))) := by
  unfold partitionResponseDensity
  rw [← blockBaselineLaw_map_translation B (partitionResponseShift n B d σ h s ω)]
  let := blockBaselineLaw_probability B
  exact Measure.isProbabilityMeasure_map (show AEMeasurable
    (fun (U : Fin B → ℝ) v => U v + partitionResponseShift n B d σ h s ω v) _ from
      (show Measurable (fun (U : Fin B → ℝ) v => U v + partitionResponseShift n B d σ h s ω v) by
        fun_prop).aemeasurable)

/-- Common full-design marginals turn the averaged response energy into a joint TV bound.  [For the stated data and conditions](hyp:n,B,d,h,s,D), [the stated conclusion holds](goal). -/
-- @node: partition_densityJoint_tv_le
lemma partition_densityJoint_tv_le (n B d : ℕ) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    Causalean.Stat.tvDist
      (densityJoint D volume (partitionResponseDensity n B d true h s))
      (densityJoint D volume (partitionResponseDensity n B d false h s)) ≤
    Real.sqrt (∫ ω, hellingerEnergy volume (partitionResponseDensity n B d true h s ω)
      (partitionResponseDensity n B d false h s ω) ∂D) := by
  rw [densityJoint_eq_withDensity D volume _ (partitionResponseDensity_measurable n B d true h s),
    densityJoint_eq_withDensity D volume _ (partitionResponseDensity_measurable n B d false h s)]
  let := densityJoint_probability D volume _
    (partitionResponseDensity_measurable n B d true h s)
    (partitionResponseDensity_probability n B d true h s)
  let := densityJoint_probability D volume _
    (partitionResponseDensity_measurable n B d false h s)
    (partitionResponseDensity_probability n B d false h s)
  have hp : IsProbabilityMeasure ((D.prod volume).withDensity
      (fun x => ENNReal.ofReal (partitionResponseDensity n B d true h s x.1 x.2))) := by
    rw [← densityJoint_eq_withDensity D volume _
      (partitionResponseDensity_measurable n B d true h s)]
    infer_instance
  have hm : IsProbabilityMeasure ((D.prod volume).withDensity
      (fun x => ENNReal.ofReal (partitionResponseDensity n B d false h s x.1 x.2))) := by
    rw [← densityJoint_eq_withDensity D volume _
      (partitionResponseDensity_measurable n B d false h s)]
    infer_instance
  let := hp
  let := hm
  have hb := density_tv_le_sqrt_hellingerEnergy (D.prod volume) _ _
    (partitionResponseDensity_measurable n B d true h s)
    (partitionResponseDensity_measurable n B d false h s)
    (fun x => partitionResponseDensity_nonneg n B d true h s x.1 x.2)
    (fun x => partitionResponseDensity_nonneg n B d false h s x.1 x.2)
  have hf := (probability_density_integrable_normalized (D.prod volume) _
    (partitionResponseDensity_measurable n B d true h s)
    (fun x => partitionResponseDensity_nonneg n B d true h s x.1 x.2)).1
  have hg := (probability_density_integrable_normalized (D.prod volume) _
    (partitionResponseDensity_measurable n B d false h s)
    (fun x => partitionResponseDensity_nonneg n B d false h s x.1 x.2)).1
  have he := integral_prod _ (Causalean.Stat.Minimax.integrable_sqrt_sum_sub_sq
    (D.prod volume) _ _ hf hg
    (fun x => partitionResponseDensity_nonneg n B d true h s x.1 x.2)
    (fun x => partitionResponseDensity_nonneg n B d false h s x.1 x.2)).2
  exact hb.trans_eq (congrArg Real.sqrt he)

/-- The full original record conditional on the true partition satisfies the genie bound.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hh,s,D,ha), [the stated conclusion holds](goal). -/
-- @node: partition_mixture_tv_le
lemma partition_mixture_tv_le (n B d : ℕ) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (h : ℝ) (hh : 0 ≤ h) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (ha : AssignmentLaw D) :
    Causalean.Stat.tvDist
      (mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d true h (s, U)))
      (mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d false h (s, U))) ≤
      2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) := by
  let := densityJoint_probability D volume _
    (partitionResponseDensity_measurable n B d true h s)
    (partitionResponseDensity_probability n B d true h s)
  let := densityJoint_probability D volume _
    (partitionResponseDensity_measurable n B d false h s)
    (partitionResponseDensity_probability n B d false h s)
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
  rw [partition_mixture_density_representation n B d hd hfit,
    partition_mixture_density_representation n B d hd hfit]
  refine (block_tvDist_map_le _ _ _ hc).trans
    ((partition_densityJoint_tv_le n B d h s D).trans
      ((Real.sqrt_le_sqrt (partition_response_energy_mean_le n B d hd hfit h s D ha)).trans_eq ?_))
  have he : 4 * Real.pi ^ 2 * h ^ 2 * B / d =
      (2 * Real.pi * h) ^ 2 * ((B : ℝ) / d) := by ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
