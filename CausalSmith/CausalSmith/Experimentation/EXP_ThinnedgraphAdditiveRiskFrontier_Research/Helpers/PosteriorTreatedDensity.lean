module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.TreatedCompletionCounting

/-!
# Exact posterior response density

The treated-label word average is the coefficient-extraction density on the
complete retained graph and the entire assignment vector.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Treatment status of an original hidden label, read from the full assignment. -/
-- @node: hiddenSourceTreated
def hiddenSourceTreated (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (j : HiddenSource n B d H) : Prop := z ⟨j.1.val, by have := j.1.isLt; omega⟩ = true

/-- The treated hidden-label subtype has exactly the observed global count K.  [For the stated data and conditions](hyp:n,B,d,hfit,H,z), [the stated conclusion holds](goal). -/
-- @node: hiddenSourceTreated_card
lemma hiddenSourceTreated_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) :
    Fintype.card {j : HiddenSource n B d H // hiddenSourceTreated n B d hfit H z j} =
      hiddenTreated n B d H z := by
  let e : {j : HiddenSource n B d H // hiddenSourceTreated n B d hfit H z j} ≃
      {j : Fin n // j.val < B * d ∧ z j = true ∧
        ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true} := {
    toFun := fun j => ⟨⟨j.1.1.val, by have := j.1.1.isLt; omega⟩,
      j.1.1.isLt, j.2, (sourceReveals_false_iff n B d H _ j.1.1.isLt).mp j.1.2⟩
    invFun := fun j => ⟨⟨⟨j.1.val,j.2.1⟩,
      (sourceReveals_false_iff n B d H j.1 j.2.1).mpr j.2.2.2⟩,j.2.2.1⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; rfl }
  simpa only [hiddenTreated, Fintype.card_subtype] using Fintype.card_congr e

/-- The actual compatible partition's row treated count is the restricted word's row count.  [For the stated data and conditions](hyp:n,B,d,hfit,H,z,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_treatedRowCount
lemma compatiblePartition_treatedRowCount (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s : CompatiblePartition n B d H) (ℓ : Fin B) :
    treatedRowCount (hiddenSourceTreated n B d hfit H z) (fun j => s.1.1 j.1) ℓ =
      partitionHiddenTreated n B d s.1 H z ℓ := by
  let e : {j : {j : HiddenSource n B d H // hiddenSourceTreated n B d hfit H z j} //
      s.1.1 j.1.1 = ℓ} ≃
      {j : Fin n // j ∈ partitionHiddenLabels n B d s.1 H ℓ ∧ z j = true} := {
    toFun := fun j => ⟨⟨j.1.1.1.val, by have := j.1.1.1.isLt; omega⟩,
      (partitionHiddenLabels_mem_iff n B d s.1 H s.2 ℓ _).mpr
        ⟨⟨j.1.1.1.isLt,j.2⟩,
          (sourceReveals_false_iff n B d H _ j.1.1.1.isLt).mp j.1.1.2⟩,j.1.2⟩
    invFun := fun j =>
      let hj := (partitionHiddenLabels_mem_iff n B d s.1 H s.2 ℓ j.1).mp j.2.1
      ⟨⟨⟨⟨j.1.val,hj.1.choose⟩,
        (sourceReveals_false_iff n B d H j.1 hj.1.choose).mpr hj.2⟩,j.2.2⟩,
        hj.1.choose_spec⟩
    left_inv := by intro j; rfl
    right_inv := by intro j; rfl }
  simpa only [treatedRowCount, partitionHiddenTreated, Fintype.card_subtype,
    ← Finset.filter_filter, Finset.filter_univ_mem] using Fintype.card_congr e

/-- Compatible partitions have the displayed response shift for the observed detailed
retained graph, independently of the audit representative used to write the density.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,H,z,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: compatiblePartition_responseShift
lemma compatiblePartition_responseShift (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s : CompatiblePartition n B d H) (ℓ : Fin B) :
    partitionResponseShift n B d σ h s.1 (z, fun _ => false) ℓ =
      signOf σ * h * (revealedSignSum n B d H z ℓ +
        2 * (partitionHiddenTreated n B d s.1 H z ℓ : ℝ) - capacity n B d H ℓ) /
          (2 * d) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
    rw [recipientBlock_card n B d hfit ℓ]
    omega)
  rw [partitionResponseShift_eq_source_sum n B d hd hfit σ h s.1 _ ℓ i hi,
    ← partitionSourceLabels_eq_inNbhd n B d s.1 ℓ i hi,
    partitionSourceLabels_sign_sum n B d hfit s.1 H s.2]
  ring

/-- The product response at an admissible row treated-count vector. -/
-- @node: treatedAllocationResponseDensity
def treatedAllocationResponseDensity (n B d : ℕ) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (k : ∀ ℓ, Fin (capacity n B d H ℓ + 1)) (y : Fin B → ℝ) : ℝ :=
  ∏ ℓ, cosSqDensity (y ℓ - signOf σ * h *
    (revealedSignSum n B d H z ℓ + 2 * (k ℓ).val - capacity n B d H ℓ) / (2 * d))

/-- The hidden word determines the compatible partition's actual response density through
its treated row counts.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,H,z,s₀,g,y), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletion_responseDensity
lemma hiddenCompletion_responseDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (g : HiddenCompletion n B d H) (y : Fin B → ℝ) :
    partitionResponseDensity n B d σ h
      (hiddenCompletionPartition n B d hfit H s₀ g).1 (z, fun _ => false) y =
    treatedAllocationResponseDensity n B d σ h H z
      (finiteRowAllocation (hiddenSourceTreated n B d hfit H z) (capacity n B d H) g) y := by
  unfold partitionResponseDensity treatedAllocationResponseDensity
  apply Finset.prod_congr rfl
  intro ℓ _
  rw [compatiblePartition_responseShift n B d hd hfit σ h H z,
    ← compatiblePartition_treatedRowCount n B d hfit H z]
  have ht : treatedRowCount (hiddenSourceTreated n B d hfit H z)
      (fun j => (hiddenCompletionPartition n B d hfit H s₀ g).1.1 j.1) ℓ =
        treatedRowCount (hiddenSourceTreated n B d hfit H z) g.1 ℓ := by
    unfold treatedRowCount
    congr 1
    apply Finset.filter_congr
    intro j _
    simp only [hiddenCompletionPartition, hiddenCompletionExtension, dif_pos j.1.2]
  simp only [ht, finiteRowAllocation]

/-- Uniform averaging over original hidden labels is precisely the displayed polynomial
density, with every label and every treatment coordinate retained.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,H,z,s₀,y), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletion_density_average
lemma hiddenCompletion_density_average (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ) :
    (Fintype.card (HiddenCompletion n B d H) : ℝ≥0∞)⁻¹ *
      (∑ g : HiddenCompletion n B d H,
        ENNReal.ofReal (partitionResponseDensity n B d σ h
          (hiddenCompletionPartition n B d hfit H s₀ g).1 (z, fun _ => false) y)) =
      ENNReal.ofReal (blockDensity n B d σ h H z y) := by
  simp_rw [hiddenCompletion_responseDensity n B d hd hfit σ h H z s₀]
  rw [finiteRowWord_average_eq_treated_counts
    (hiddenSourceTreated n B d hfit H z) (capacity n B d H)
    (hiddenSource_card n B d hfit H s₀).symm
    (fun k => ENNReal.ofReal (treatedAllocationResponseDensity n B d σ h H z k y))]
  rw [hiddenSourceTreated_card, hiddenSource_card n B d hfit H s₀,
    blockDensity_allocation_sum]
  have hK : hiddenTreated n B d H z ≤ undiscovered n B d H :=
    hiddenTreated_le n B d H ⟨hfit, s₀.1, s₀.2⟩ z
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast Nat.choose_pos hK),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => by
      split_ifs
      · exact Finset.prod_nonneg (fun ℓ _ =>
          mul_nonneg (Nat.cast_nonneg _) (cosSqDensity_nonneg _))
      · exact le_rfl), ENNReal.ofReal_natCast]
  simp_rw [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs with hk
  · rw [ENNReal.ofReal_prod_of_nonneg (fun ℓ _ =>
      mul_nonneg (Nat.cast_nonneg _) (cosSqDensity_nonneg _))]
    simp_rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    rw [Finset.prod_mul_distrib]
    unfold treatedAllocationResponseDensity
    rw [ENNReal.ofReal_prod_of_nonneg (fun _ _ => cosSqDensity_nonneg _)]
    simp only [div_eq_mul_inv]
    ac_rfl
  · simp

/-- The genuine compatible-completion posterior kernel is exactly the displayed
conditional density followed by copying all labeled outcomes.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,hz,hH), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletionKernel_eq_blockDensity
lemma hiddenCompletionKernel_eq_blockDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (hH : ValidRetainedGraph n B d hz.1) :
    hiddenCompletionKernel n B d hfit σ h hz =
      (volume.withDensity (fun y => ENNReal.ofReal
        (blockDensity n B d σ h hz.1 hz.2 y))).map (copyOutcomes n B d hz) := by
  have hs : Nonempty (CompatiblePartition n B d hz.1) := by
    obtain ⟨s, hs⟩ := hH.2
    exact ⟨⟨s, hs⟩⟩
  let s₀ : CompatiblePartition n B d hz.1 := hs.some
  have hm (g : HiddenCompletion n B d hz.1) : Measurable (fun y => ENNReal.ofReal
      (partitionResponseDensity n B d σ h
        (hiddenCompletionPartition n B d hfit hz.1 s₀ g).1 (hz.2, fun _ => false) y)) := by
    fun_prop
  have hc : Measurable (copyOutcomes n B d hz) :=
    (copyOutcomes_measurable n B d).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [hiddenCompletionKernel, dif_pos hs,
    ← hiddenCompletion_inverse_card n B d hfit hz.1 s₀]
  ext E hE
  rw [Measure.smul_apply, smul_eq_mul, Measure.finsetSum_apply,
    Measure.map_apply hc hE, withDensity_apply _ (hc hE)]
  simp_rw [partitionResponseKernel, Measure.map_apply hc hE,
    withDensity_apply _ (hc hE)]
  rw [← lintegral_finsetSum _ (fun g _ => hm g),
    ← lintegral_const_mul _ (Finset.measurable_sum _ (fun g _ => hm g))]
  apply lintegral_congr
  intro y
  exact hiddenCompletion_density_average n B d hd hfit σ h hz.1 hz.2 s₀ y

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
