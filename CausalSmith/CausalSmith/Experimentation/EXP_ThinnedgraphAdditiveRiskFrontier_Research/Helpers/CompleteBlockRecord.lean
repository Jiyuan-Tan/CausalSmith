module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.LikelihoodExpansion
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompleteBlockConstruction

/-!
# Complete-block copying and reconstruction

The distinct responses determine every labeled outcome, including padding. Reading
one fixed member of each block recovers the responses without discarding the graph
or any treatment coordinate.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Padding labels have identically zero outcome under the complete-block prior.  [For the stated data and conditions](hyp:n,d,σ,h,U,i,z,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockSchedule_response_padding
lemma completeBlockSchedule_response_padding (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (i : Fin n) (z : Assign (Fin n))
    (hi : ¬ i.val < (n / (d + 1)) * (d + 1)) :
    potentialOutcome (completeBlockSchedule n d σ h U) i z = 0 := by
  unfold potentialOutcome
  rw [completeBlockSchedule_baseline_padding n d σ h U i hi,
    completeBlockSchedule_inNbhd_padding n d σ h U i hi]
  simp [completeBlockSchedule, hi]

/-- A fixed labeled representative of each full block. -/
-- @node: completeBlockRepresentative
def completeBlockRepresentative (n d : ℕ) (v : Fin (n / (d + 1))) : Fin n :=
  ⟨v.val * (d + 1), by
    have hv := Nat.mul_le_mul_right (d + 1) (show v.val + 1 ≤ n / (d + 1) by omega)
    have hn := Nat.div_mul_le_self n (d + 1)
    rw [Nat.add_mul] at hv
    omega⟩

/-- The chosen member belongs to its intended block.  [For the stated data and conditions](hyp:n,d,v), [the stated conclusion holds](goal). -/
-- @node: completeBlockRepresentative_quotient
lemma completeBlockRepresentative_quotient (n d : ℕ) (v : Fin (n / (d + 1))) :
    (completeBlockRepresentative n d v).val / (d + 1) = v.val := by
  simp [completeBlockRepresentative]

/-- Copy each distinct block response to all its labeled members; padding stays zero. -/
-- @node: completeBlockCopy
def completeBlockCopy (n d : ℕ)
    (x : ((OffDiag (Fin n) → Bool) × Assign (Fin n)) × (Fin (n / (d + 1)) → ℝ)) :
    Record (Fin n) :=
  (x.1.1, x.1.2, fun i => ∑ v : Fin (n / (d + 1)),
    if i.val / (d + 1) = v.val then x.2 v else 0)

/-- Read the distinct responses while preserving all graph and treatment coordinates. -/
-- @node: completeBlockExtract
def completeBlockExtract (n d : ℕ) (o : Record (Fin n)) :
    ((OffDiag (Fin n) → Bool) × Assign (Fin n)) × (Fin (n / (d + 1)) → ℝ) :=
  ((o.1, o.2.1), fun v => o.2.2 (completeBlockRepresentative n d v))

/-- [Copying is measurable on the full labeled record space.](goal) -/
-- @node: completeBlockCopy_measurable
@[fun_prop]
lemma completeBlockCopy_measurable (n d : ℕ) : Measurable (completeBlockCopy n d) := by
  unfold completeBlockCopy
  apply measurable_fst.fst.prodMk
  apply measurable_fst.snd.prodMk
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_sum
  intro v _
  by_cases hi : i.val / (d + 1) = v.val <;> simp only [hi, ite_true, ite_false] <;> fun_prop

/-- [Reading the fixed representatives is measurable.](goal) -/
-- @node: completeBlockExtract_measurable
@[fun_prop]
lemma completeBlockExtract_measurable (n d : ℕ) : Measurable (completeBlockExtract n d) := by
  unfold completeBlockExtract
  fun_prop

/-- At a full block member the copying map returns exactly that block's response.  [For the stated data and conditions](hyp:n,d,x,i,v,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockCopy_member
lemma completeBlockCopy_member (n d : ℕ)
    (x : ((OffDiag (Fin n) → Bool) × Assign (Fin n)) × (Fin (n / (d + 1)) → ℝ))
    (i : Fin n) (v : Fin (n / (d + 1))) (hi : i.val / (d + 1) = v.val) :
    (completeBlockCopy n d x).2.2 i = x.2 v := by
  change (∑ w, if i.val / (d + 1) = w.val then x.2 w else 0) = x.2 v
  rw [Finset.sum_eq_single v]
  · simp [hi]
  · intro w _ hw
    apply if_neg
    intro he
    exact hw (Fin.ext (he.symm.trans hi))
  · simp

/-- At padding labels all terms in the copying sum vanish.  [For the stated data and conditions](hyp:n,d,x,i,hi), [the stated conclusion holds](goal). -/
-- @node: completeBlockCopy_padding
lemma completeBlockCopy_padding (n d : ℕ)
    (x : ((OffDiag (Fin n) → Bool) × Assign (Fin n)) × (Fin (n / (d + 1)) → ℝ))
    (i : Fin n) (hi : ¬ i.val < (n / (d + 1)) * (d + 1)) :
    (completeBlockCopy n d x).2.2 i = 0 := by
  change (∑ v : Fin (n / (d + 1)), if i.val / (d + 1) = v.val then x.2 v else 0) = 0
  apply Finset.sum_eq_zero
  intro v _
  apply if_neg
  intro he
  exact hi ((completeBlock_active_iff n d i).mpr (he ▸ v.isLt))

/-- Reading the copied outcomes is an exact left inverse, including graph labels and assignment.  [For the stated data and conditions](hyp:n,d,x), [the stated conclusion holds](goal). -/
-- @node: completeBlockExtract_copy
lemma completeBlockExtract_copy (n d : ℕ)
    (x : ((OffDiag (Fin n) → Bool) × Assign (Fin n)) × (Fin (n / (d + 1)) → ℝ)) :
    completeBlockExtract n d (completeBlockCopy n d x) = x := by
  apply Prod.ext
  · rfl
  · funext v
    exact completeBlockCopy_member n d x _ v (completeBlockRepresentative_quotient n d v)

/-- The original record is exactly the copying of its translated block baselines.  [For the stated data and conditions](hyp:n,d,σ,h,U,ω), [the stated conclusion holds](goal). -/
-- @node: completeBlock_record_reconstruction
lemma completeBlock_record_reconstruction (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (ω : Assign (Fin n) × Audit (Fin n)) :
    recordOf (completeBlockSchedule n d σ h U) ω =
      completeBlockCopy n d
        (((recordOf (completeBlockSchedule n d σ h U) ω).1, ω.1),
          fun v => U v + completeBlockShift n d σ h ω.1 v) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext i
      by_cases hi : i.val < (n / (d + 1)) * (d + 1)
      · let v : Fin (n / (d + 1)) :=
          ⟨i.val / (d + 1), (completeBlock_active_iff n d i).mp hi⟩
        rw [completeBlockCopy_member n d _ i v rfl]
        exact completeBlockSchedule_response n d σ h U i ω.1 hi
      · rw [completeBlockCopy_padding n d _ i hi]
        exact completeBlockSchedule_response_padding n d σ h U i ω.1 hi

/-- The complete retained graph is independent of the sign, amplitude, and baseline draws.  [For the stated data and conditions](hyp:n,d,σ,h,U,ω), [the stated conclusion holds](goal). -/
-- @node: completeBlock_record_graph
lemma completeBlock_record_graph (n d : ℕ) (σ : Bool) (h : ℝ)
    (U : Fin (n / (d + 1)) → ℝ) (ω : Assign (Fin n) × Audit (Fin n)) :
    (recordOf (completeBlockSchedule n d σ h U) ω).1 =
      (recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) ω).1 := by
  rfl

/-- [The full recording channel is jointly measurable in baselines and the actual design draw.](goal) -/
-- @node: completeBlock_record_measurable
@[fun_prop]
lemma completeBlock_record_measurable (n d : ℕ) (σ : Bool) (h : ℝ) :
    Measurable (fun x : (Fin (n / (d + 1)) → ℝ) ×
      (Assign (Fin n) × Audit (Fin n)) => recordOf (completeBlockSchedule n d σ h x.1) x.2) := by
  have he : (fun x : (Fin (n / (d + 1)) → ℝ) ×
      (Assign (Fin n) × Audit (Fin n)) => recordOf (completeBlockSchedule n d σ h x.1) x.2) =
      fun x => completeBlockCopy n d
        (((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) x.2).1, x.2.1),
          fun v => x.1 v + completeBlockShift n d σ h x.2.1 v) := by
    funext x
    rw [completeBlock_record_reconstruction, completeBlock_record_graph]
  rw [he]
  apply (completeBlockCopy_measurable n d).comp
  apply Measurable.prodMk
  · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
      ((recordOf (completeBlockSchedule n d true 0 (fun _ => 0)) ω).1, ω.1))).comp measurable_snd
  · apply measurable_pi_lambda
    intro v
    apply Measurable.add
    · fun_prop
    · exact (measurable_of_finite (fun z : Assign (Fin n) =>
        completeBlockShift n d σ h z v)).comp measurable_snd.fst

/-- Extracting after copying recovers any law of distinct responses and ancillary coordinates.  [For the stated data and conditions](hyp:n,d,μ), [the stated conclusion holds](goal). -/
-- @node: completeBlockCopy_map_extract
lemma completeBlockCopy_map_extract (n d : ℕ)
    (μ : Measure (((OffDiag (Fin n) → Bool) × Assign (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ))) :
    (μ.map (completeBlockCopy n d)).map (completeBlockExtract n d) = μ := by
  rw [Measure.map_map (completeBlockExtract_measurable n d) (completeBlockCopy_measurable n d)]
  have he : completeBlockExtract n d ∘ completeBlockCopy n d = id := by
    funext x
    exact completeBlockExtract_copy n d x
  rw [he, Measure.map_id]

/-- No testing information is lost when distinct responses are copied into the original record.  [For the stated data and conditions](hyp:n,d,μ,ν), [the stated conclusion holds](goal). -/
-- @node: completeBlockCopy_tvDist_eq
lemma completeBlockCopy_tvDist_eq (n d : ℕ)
    (μ ν : Measure (((OffDiag (Fin n) → Bool) × Assign (Fin n)) ×
      (Fin (n / (d + 1)) → ℝ))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Causalean.Stat.tvDist (μ.map (completeBlockCopy n d)) (ν.map (completeBlockCopy n d)) =
      Causalean.Stat.tvDist μ ν := by
  let : IsProbabilityMeasure (μ.map (completeBlockCopy n d)) :=
    Measure.isProbabilityMeasure_map (completeBlockCopy_measurable n d).aemeasurable
  let : IsProbabilityMeasure (ν.map (completeBlockCopy n d)) :=
    Measure.isProbabilityMeasure_map (completeBlockCopy_measurable n d).aemeasurable
  apply le_antisymm
  · exact block_tvDist_map_le μ ν _ (completeBlockCopy_measurable n d)
  · have ht := block_tvDist_map_le (μ.map (completeBlockCopy n d))
      (ν.map (completeBlockCopy n d)) _ (completeBlockExtract_measurable n d)
    simpa only [completeBlockCopy_map_extract] using ht

/-- For any joint baseline-design law, the original-record law is exactly the copied reduced law.  [For the stated data and conditions](hyp:n,d,σ,h,μ), [the stated conclusion holds](goal). -/
-- @node: completeBlock_record_map_reconstruction
lemma completeBlock_record_map_reconstruction (n d : ℕ) (σ : Bool) (h : ℝ)
    (μ : Measure ((Fin (n / (d + 1)) → ℝ) × (Assign (Fin n) × Audit (Fin n)))) :
    μ.map (fun x => recordOf (completeBlockSchedule n d σ h x.1) x.2) =
      (μ.map (fun x => completeBlockExtract n d
        (recordOf (completeBlockSchedule n d σ h x.1) x.2))).map (completeBlockCopy n d) := by
  rw [Measure.map_map (completeBlockCopy_measurable n d)
    (show Measurable (fun x : (Fin (n / (d + 1)) → ℝ) ×
        (Assign (Fin n) × Audit (Fin n)) => completeBlockExtract n d
      (recordOf (completeBlockSchedule n d σ h x.1) x.2)) from
      (completeBlockExtract_measurable n d).comp (completeBlock_record_measurable n d σ h))]
  congr 1
  funext x
  have hr := completeBlock_record_reconstruction n d σ h x.1 x.2
  dsimp only [Function.comp_apply]
  conv_rhs => rw [hr, completeBlockExtract_copy]
  exact hr

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
