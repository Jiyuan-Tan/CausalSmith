module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.CompletionCounting

/-!
# Full-record posterior completion mixture

Disintegration over the complete retained graph and assignment preserves every
coordinate. The compatible-partition posterior is uniform and its denominator
is the exact labeled multinomial count.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The finite full graph-assignment law for a fixed labeled source partition. -/
-- @node: partitionGraphAssignLaw
def partitionGraphAssignLaw (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) (s : SourcePartition B d) :=
  D.map (fun ω => ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1))

/-- A fixed-partition response channel depends on the assignment but not the audit marks. -/
-- @node: partitionResponseKernel
def partitionResponseKernel (n B d : ℕ) (σ : Bool) (h : ℝ)
    (s : SourcePartition B d) (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) :
    Measure (Record (Fin n)) :=
  (volume.withDensity (fun y => ENNReal.ofReal
    (partitionResponseDensity n B d σ h s (hz.2, fun _ => false) y))).map
      (copyOutcomes n B d hz)

/-- The fixed-partition original-record law factors through its full graph-assignment law.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,D), [the stated conclusion holds](goal). -/
-- @node: partition_mixture_graphAssign_bind
lemma partition_mixture_graphAssign_bind (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    mixtureLaw D (blockBaselineLaw B) (fun U => blockSchedule n B d σ h (s, U)) =
      (partitionGraphAssignLaw n B d D s).bind (partitionResponseKernel n B d σ h s) := by
  rw [partition_mixture_density_representation n B d hd hfit]
  ext E hE
  have hc : Measurable (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
      copyOutcomes n B d
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1) x.2) :=
    (copyOutcomes_measurable n B d).comp (show Measurable
      (fun x : (Assign (Fin n) × Audit (Fin n)) × (Fin B → ℝ) =>
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1, x.2)) from by
      apply Measurable.prodMk
      · exact (measurable_of_finite (fun ω : Assign (Fin n) × Audit (Fin n) =>
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1)).comp measurable_fst
      · exact measurable_fst.fst.prodMk measurable_snd)
  rw [Measure.map_apply hc hE, densityJoint, Measure.bind_apply (hc hE)
    (measurable_densityJoint_fiber volume _
      (partitionResponseDensity_measurable n B d σ h s)).aemeasurable,
    Measure.bind_apply hE (measurable_of_finite _).aemeasurable,
    partitionGraphAssignLaw, lintegral_map (measurable_of_finite _) (measurable_of_finite _)]
  apply lintegral_congr
  intro ω
  have hmω : Measurable (copyOutcomes n B d
      ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)) :=
    hc.comp measurable_prodMk_left
  rw [Measure.map_apply measurable_prodMk_left (hc hE), partitionResponseKernel,
    Measure.map_apply hmω hE]
  rfl

/-- A graph-assignment atom factors into its exact detailed graph likelihood and the
probability of the entire assignment vector.  [For the stated data and conditions](hyp:n,B,d,q,hq,s,H,z), [the stated conclusion holds](goal). -/
-- @node: partitionGraphAssignLaw_atom
lemma partitionGraphAssignLaw_atom (n B d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) :
    partitionGraphAssignLaw n B d (thinnedDesign (Fin n) q) s {(H,z)} =
      halfBernoulli (Fin n) {z} *
        ((auditLaw (Fin n) q).map (fun w e =>
          decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} := by
  let := bernoulliLaw_probability q hq
  let _ : IsProbabilityMeasure (auditLaw (Fin n) q) := by unfold auditLaw; infer_instance
  rw [partitionGraphAssignLaw, Measure.map_apply (measurable_of_finite _)
    (measurableSet_singleton _)]
  have he : (fun ω : Assign (Fin n) × Audit (Fin n) =>
      ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)) ⁻¹'
        {(H,z)} = {z} ×ˢ ((fun w e =>
          decide (blockEdge n B d s e.val.1 e.val.2) && w e) ⁻¹' {H}) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_prod,
      recordOf, blockSchedule]
    exact and_comm
  rw [he, thinnedDesign, Measure.prod_prod,
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]

/-- The common likelihood includes every assignment coordinate and retained-edge subset.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,s,hz), [the stated conclusion holds](goal). -/
-- @node: partitionGraphAssignLaw_atom_ite
lemma partitionGraphAssignLaw_atom_ite (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) :
    partitionGraphAssignLaw n B d (thinnedDesign (Fin n) q) s {hz} =
      if (∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2) then
        halfBernoulli (Fin n) {hz.2} *
          (ENNReal.ofReal q ^ (Finset.univ.filter (fun e => hz.1 e = true)).card *
            ENNReal.ofReal (1-q) ^
              (B*d*d - (Finset.univ.filter (fun e => hz.1 e = true)).card)) else 0 := by
  rw [partitionGraphAssignLaw_atom n B d q hq s hz.1 hz.2,
    block_detailed_graph_mass_ite n B d hfit q hq]
  split_ifs <;> simp only [mul_zero]

/-- Uniform finite mixing followed by a common-likelihood observation channel gives the
uniform posterior over compatible completions, including null observation atoms.  [For the stated data and conditions](hyp:β,γ,B,d,μ,K,R,a,hμ), [the stated conclusion holds](goal). -/
-- @node: partitionLaw_bind_uniform_fibers
lemma partitionLaw_bind_uniform_fibers {β γ : Type*} [Fintype β]
    [MeasurableSpace β] [MeasurableSingletonClass β] [MeasurableSpace γ]
    (B d : ℕ) (μ : SourcePartition B d → Measure β)
    (K : SourcePartition B d → β → Measure γ) (R : SourcePartition B d → β → Prop)
    [∀ s b, Decidable (R s b)] (a : β → ℝ≥0∞)
    (hμ : ∀ s b, μ s {b} = if R s b then a b else 0) :
    (partitionLaw B d).bind (fun s => (μ s).bind (K s)) =
      ((partitionLaw B d).bind μ).bind (fun b =>
        (((Finset.univ.filter (fun s => R s b)).card : ℝ≥0∞)⁻¹) •
          ∑ s ∈ Finset.univ.filter (fun s => R s b), K s b) := by
  ext E hE
  rw [Measure.bind_apply hE (measurable_of_finite _).aemeasurable,
    partitionLaw_lintegral,
    Measure.bind_apply hE (measurable_of_finite _).aemeasurable,
    lintegral_countable', tsum_fintype]
  simp_rw [Measure.bind_apply hE (measurable_of_finite _).aemeasurable,
    lintegral_countable', tsum_fintype, hμ]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.bind_apply (measurableSet_singleton _) (measurable_of_finite _).aemeasurable,
    partitionLaw_lintegral]
  simp_rw [hμ]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero]
  have hs : (∑ s, (K s b) E * (if R s b then a b else 0)) =
      (∑ s ∈ Finset.univ.filter (fun s => R s b), (K s b) E) * a b := by
    rw [Finset.sum_mul]
    simp_rw [mul_ite, mul_zero]
    rw [Finset.sum_ite]
    simp
  rw [hs]
  let C := Finset.univ.filter (fun s : SourcePartition B d => R s b)
  by_cases hC : C.card = 0
  · have he : C = ∅ := Finset.card_eq_zero.mp hC
    change _ * ((∑ s ∈ C, (K s b) E) * a b) = _
    simp only [he, Finset.sum_empty, zero_mul, mul_zero, C] at *
  · have hc : (C.card : ℝ≥0∞)⁻¹ * C.card = 1 :=
      ENNReal.inv_mul_cancel (by exact_mod_cast hC) (by finiteness)
    change _ * ((∑ s ∈ C, (K s b) E) * a b) = _
    calc
      _ = ((C.card : ℝ≥0∞)⁻¹ * C.card) *
          ((Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ *
            ((∑ s ∈ C, (K s b) E) * a b)) := by rw [hc, one_mul]
      _ = _ := by ac_rfl

/-- The complete original-record mixture is the actual full graph-assignment marginal
followed by a uniform mixture of all compatible fixed-partition response kernels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hq), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_uniform_completion_bind
lemma blockMixtureLawOf_uniform_completion_bind (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    blockMixtureLawOf n B d (thinnedDesign (Fin n) q) σ h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (((Finset.univ.filter (fun s : SourcePartition B d =>
          ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2)).card : ℝ≥0∞)⁻¹) •
        ∑ s ∈ Finset.univ.filter (fun s : SourcePartition B d =>
          ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2),
          partitionResponseKernel n B d σ h s hz) := by
  let : IsProbabilityMeasure (thinnedDesign (Fin n) q) :=
    thinnedDesign_probabilityDesign (V := Fin n) q hq
  rw [blockMixtureLawOf_bind_partition]
  simp_rw [partition_mixture_graphAssign_bind n B d hd hfit]
  have he := partitionLaw_bind_uniform_fibers
    (β := (OffDiag (Fin n) → Bool) × Assign (Fin n)) (γ := Record (Fin n)) B d
    (partitionGraphAssignLaw n B d (thinnedDesign (Fin n) q))
    (partitionResponseKernel n B d σ h)
    (fun s hz => ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2)
    (fun hz => halfBernoulli (Fin n) {hz.2} *
      (ENNReal.ofReal q ^ (Finset.univ.filter (fun e => hz.1 e = true)).card *
        ENNReal.ofReal (1-q) ^
          (B*d*d - (Finset.univ.filter (fun e => hz.1 e = true)).card)))
    (partitionGraphAssignLaw_atom_ite n B d hfit q hq)
  exact he

/-- The response posterior indexed by capacity-constrained words on the original hidden
labels. The extension copies every revealed row, and zero-mass invalid graphs contribute zero. -/
-- @node: hiddenCompletionKernel
def hiddenCompletionKernel (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) : Measure (Record (Fin n)) :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    ((∏ ℓ, (capacity n B d hz.1 ℓ).factorial : ℕ) /
      (undiscovered n B d hz.1).factorial : ℝ≥0∞) •
      ∑ g : HiddenCompletion n B d hz.1,
        partitionResponseKernel n B d σ h
          (hiddenCompletionPartition n B d hfit hz.1 hs.some g).1 hz
  else 0

/-- The uniform posterior over actual partitions is exactly the factorial-weighted
mixture of hidden-label completions, retaining every graph and assignment coordinate.  [For the stated data and conditions](hyp:n,B,d,hfit,σ,h,hz), [the stated conclusion holds](goal). -/
-- @node: uniform_completion_kernel_eq_hiddenCompletionKernel
lemma uniform_completion_kernel_eq_hiddenCompletionKernel (n B d : ℕ)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) :
    (((Finset.univ.filter (fun s : SourcePartition B d =>
      ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2)).card : ℝ≥0∞)⁻¹) •
      (∑ s ∈ Finset.univ.filter (fun s : SourcePartition B d =>
        ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2),
        partitionResponseKernel n B d σ h s hz) =
      hiddenCompletionKernel n B d hfit σ h hz := by
  rw [hiddenCompletionKernel]
  split_ifs with hs
  · have hcard : (Finset.univ.filter (fun s : SourcePartition B d =>
        ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2)).card =
        Fintype.card (CompatiblePartition n B d hz.1) := by
      simp only [CompatiblePartition, Fintype.card_subtype]
    rw [hcard, Finset.sum_subtype
      (p := fun s : SourcePartition B d =>
        ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2) _ (by simp)]
    rw [compatiblePartition_average_eq_hiddenCompletion n B d hfit hz.1 hs.some,
      hiddenCompletion_inverse_card n B d hfit hz.1 hs.some]
  · have he : (Finset.univ.filter (fun s : SourcePartition B d =>
        ∀ e, hz.1 e = true → blockEdge n B d s e.val.1 e.val.2)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro s hs'
      exact hs ⟨⟨s, (Finset.mem_filter.mp hs').2⟩⟩
    rw [he, Finset.sum_empty, smul_zero]

/-- The actual original-record law is now reconstructed from its actual full graph-assignment
marginal and the exact labeled-completion kernel. Only the treated-count grouping remains.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,q,hq), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_hidden_completion_bind
lemma blockMixtureLawOf_hidden_completion_bind (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    blockMixtureLawOf n B d (thinnedDesign (Fin n) q) σ h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind
        (hiddenCompletionKernel n B d hfit σ h) := by
  rw [blockMixtureLawOf_uniform_completion_bind n B d hd hfit σ h q hq]
  congr 1
  funext hz
  exact uniform_completion_kernel_eq_hiddenCompletionKernel n B d hfit σ h hz

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
