module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PosteriorTreatedDensity
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenSignEnergy
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLaw

/-!
# Actual labeled-completion Walsh likelihood

Enumerate each completed row using its original source labels, expand its actual
translated response density, and average over the exact compatible posterior.
The reference-zero set is kept separate from the positive-density expansion.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A row sign vector reads the original assignment at every completed source label. -/
-- @node: partitionRowSigns
def partitionRowSigns (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (z : Assign (Fin n)) (ℓ : Fin B) : Fin d → Bool :=
  fun j => z ((Finset.equivFinOfCardEq
    (partitionSourceLabels_card n B d hfit s ℓ)).symm j).val

/-- Enumerating a completed row preserves its full labeled sign sum.  [For the stated data and conditions](hyp:n,B,d,hfit,s,z,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionRowSigns_sum
lemma partitionRowSigns_sum (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (z : Assign (Fin n)) (ℓ : Fin B) :
    (∑ j, signOf (partitionRowSigns n B d hfit s z ℓ j)) =
      ∑ j ∈ partitionSourceLabels n B d s ℓ, signOf (z j) := by
  conv_rhs => rw [← Finset.sum_attach]
  exact (Fintype.sum_equiv
    (Finset.equivFinOfCardEq (partitionSourceLabels_card n B d hfit s ℓ))
    (fun j => signOf (z j.val))
    (fun j => signOf (partitionRowSigns n B d hfit s z ℓ j))
    (fun j => by simp [partitionRowSigns])).symm

/-- The positive-prior density is a product of actual completed-row channels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,ω,y), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_eq_rowDensity
lemma partitionResponseDensity_eq_rowDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ) :
    partitionResponseDensity n B d true h s ω y =
      ∏ ℓ, rowDensity d h (partitionRowSigns n B d hfit s ω.1 ℓ) (y ℓ) := by
  apply Finset.prod_congr rfl
  intro ℓ _
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
    rw [recipientBlock_card n B d hfit ℓ]; omega)
  rw [partitionResponseShift_eq_source_sum n B d hd hfit true h s ω ℓ i hi]
  rw [rowDensity, partitionRowSigns_sum,
    partitionSourceLabels_eq_inNbhd n B d s ℓ i hi]
  simp only [signOf, ite_true, one_mul]

/-- The full fixed-partition likelihood expands row by row without losing labels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,ω,y,hy), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_walsh_expansion
lemma partitionResponseDensity_walsh_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    partitionResponseDensity n B d true h s ω y / (∏ ℓ, refDensity d h (y ℓ)) =
      ∏ ℓ, ∑ E : Finset (Fin d), walshCoeff d h E.card (y ℓ) *
        ∏ j ∈ E, signOf (partitionRowSigns n B d hfit s ω.1 ℓ j) := by
  rw [partitionResponseDensity_eq_rowDensity n B d hd hfit,
    ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro ℓ _
  exact rowDensity_walsh_expansion d h (y ℓ) (hy ℓ) _

/-- Every completed density vanishes when any reference row density is zero.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,s,ω,y,ℓ,hy), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_zero_of_reference_zero
lemma partitionResponseDensity_zero_of_reference_zero (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ)
    (ℓ : Fin B) (hy : refDensity d h (y ℓ) = 0) :
    partitionResponseDensity n B d true h s ω y = 0 := by
  rw [partitionResponseDensity_eq_rowDensity n B d hd hfit]
  exact Finset.prod_eq_zero (Finset.mem_univ ℓ)
    (rowDensity_eq_zero_of_refDensity_eq_zero d h (y ℓ) hy _)

/-- The exact posterior density average also holds as an identity of real densities.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y), [the stated conclusion holds](goal). -/
-- @node: hiddenCompletion_density_average_real
lemma hiddenCompletion_density_average_real (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ) :
    (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
      (∑ g : HiddenCompletion n B d H,
        partitionResponseDensity n B d true h
          (hiddenCompletionPartition n B d hfit H s₀ g).1 (z, fun _ => false) y) =
      blockDensity n B d true h H z y := by
  have he := congrArg ENNReal.toReal
    (hiddenCompletion_density_average n B d hd hfit true h H z s₀ y)
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)] at he
  have hn (s : SourcePartition B d) :
      0 ≤ partitionResponseDensity n B d true h s (z, fun _ => false) y :=
    Finset.prod_nonneg (fun _ _ => cosSqDensity_nonneg _)
  simpa only [ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (blockDensity_nonneg n B d true h H z y),
    ENNReal.toReal_ofReal (hn _)] using he

/-- On positive reference density, the actual conditional response likelihood is
exactly the uniform posterior average of products of labeled Walsh expansions.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_completion_walsh_expansion
lemma blockDensity_completion_walsh_expansion (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (hy : ∀ ℓ, 0 < refDensity d h (y ℓ)) :
    blockDensity n B d true h H z y / (∏ ℓ, refDensity d h (y ℓ)) =
      (Fintype.card (HiddenCompletion n B d H) : ℝ)⁻¹ *
        ∑ g : HiddenCompletion n B d H,
          ∏ ℓ, ∑ E : Finset (Fin d), walshCoeff d h E.card (y ℓ) *
            ∏ j ∈ E, signOf (partitionRowSigns n B d hfit
              (hiddenCompletionPartition n B d hfit H s₀ g).1 z ℓ j) := by
  rw [← hiddenCompletion_density_average_real n B d hd hfit h H z s₀ y,
    mul_div_assoc, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro g _
  exact partitionResponseDensity_walsh_expansion n B d hd hfit h _ _ y hy

/-- The averaged actual density vanishes on the reference-zero set as well.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,H,z,s₀,y,ℓ,hy), [the stated conclusion holds](goal). -/
-- @node: blockDensity_zero_of_reference_zero
lemma blockDensity_zero_of_reference_zero (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n))
    (s₀ : CompatiblePartition n B d H) (y : Fin B → ℝ)
    (ℓ : Fin B) (hy : refDensity d h (y ℓ) = 0) :
    blockDensity n B d true h H z y = 0 := by
  rw [← hiddenCompletion_density_average_real n B d hd hfit h H z s₀ y]
  simp_rw [partitionResponseDensity_zero_of_reference_zero n B d hd hfit h _ _ y ℓ hy]
  simp

/-- The exact completion-averaged Walsh density, extended by zero off its reference
support and off compatible graphs. Completion averaging retains the assignment labels. -/
-- @node: completionWalshDensity
def completionWalshDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) : ℝ :=
  if hs : Nonempty (CompatiblePartition n B d hz.1) then
    if ∀ ℓ, 0 < refDensity d h (y ℓ) then
      (∏ ℓ, refDensity d h (y ℓ)) *
        ((Fintype.card (HiddenCompletion n B d hz.1) : ℝ)⁻¹ *
          ∑ g : HiddenCompletion n B d hz.1,
            ∏ ℓ, ∑ E : Finset (Fin d), walshCoeff d h E.card (y ℓ) *
              ∏ j ∈ E, signOf (partitionRowSigns n B d hfit
                (hiddenCompletionPartition n B d hfit hz.1 hs.some g).1 hz.2 ℓ j))
    else 0
  else 0

/-- On the actual graph support this finite Walsh density equals the actual density.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,h,hz,hH,y), [the stated conclusion holds](goal). -/
-- @node: completionWalshDensity_eq_blockDensity
lemma completionWalshDensity_eq_blockDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (h : ℝ)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (hH : ValidRetainedGraph n B d hz.1) (y : Fin B → ℝ) :
    completionWalshDensity n B d hfit h hz y = blockDensity n B d true h hz.1 hz.2 y := by
  have hs : Nonempty (CompatiblePartition n B d hz.1) := by
    obtain ⟨_, s, hs⟩ := hH
    exact ⟨⟨s, hs⟩⟩
  rw [completionWalshDensity, dif_pos hs]
  split_ifs with hy
  · rw [← blockDensity_completion_walsh_expansion n B d hd hfit h hz.1 hz.2 hs.some y hy]
    exact mul_div_cancel₀ _ (ne_of_gt (Finset.prod_pos (fun ℓ _ => hy ℓ)))
  · obtain ⟨ℓ, hℓ⟩ := not_forall.mp hy
    have hz0 : refDensity d h (y ℓ) = 0 :=
      le_antisymm (not_lt.mp hℓ) (refDensity_nonneg d h (y ℓ))
    exact (blockDensity_zero_of_reference_zero n B d hd hfit h hz.1 hz.2 hs.some y ℓ hz0).symm

/-- Replacing the posterior density by its finite Walsh expansion gives exactly
 the full original-record law, with all edge subsets and outcome copies.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma blockMixtureLawOf_completion_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    blockMixtureLawOf n B d (thinnedDesign (Fin n) q) true h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (completionWalshDensity n B d hfit h hz y))).map (copyOutcomes n B d hz)) := by
  rw [(block_law n B d true h q (thinnedDesign (Fin n) q) hn hB hd hfit hh hq
    (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
    (thinnedDesign_independent q hq)).2.2.1, reconstructedLaw]
  apply Measure.bind_congr_right
  have hv : ∀ᵐ hz ∂(graphAssignMarginal n B d (thinnedDesign (Fin n) q)),
      ValidRetainedGraph n B d hz.1 :=
    (ae_map_iff (by fun_prop) (by measurability)).mp
      (retainedGraphMarginal_valid n B d (thinnedDesign (Fin n) q) hfit)
  filter_upwards [hv] with hz hH
  simp_rw [completionWalshDensity_eq_blockDensity n B d hd hfit h hz hH]

/-- Recovering distinct responses from the Walsh density preserves the complete
retained graph and every assignment coordinate.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq), [the stated conclusion holds](goal). -/
lemma reducedBlockLaw_completion_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1) :
    reducedBlockLaw n B d (thinnedDesign (Fin n) q) true h =
      (graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
        (volume.withDensity (fun y => ENNReal.ofReal
          (completionWalshDensity n B d hfit h hz y))).map
            (fun y => (hz.1, hz.2, y))) := by
  rw [reducedBlockLaw, blockMixtureLawOf_completion_walsh_representation n B d h q
    hn hB hd hfit hh hq, block_map_bind _ _ _ (measurable_of_finite _) (by fun_prop)]
  congr 1
  funext hz
  have hm : Measurable (copyOutcomes n B d hz) := by
    simpa only [Function.comp_def] using (copyOutcomes_measurable n B d).comp
      (show Measurable (fun y : Fin B → ℝ => (hz.1, hz.2, y)) from by fun_prop)
  rw [Measure.map_map (by fun_prop) hm]
  congr 1
  funext y
  simp only [Function.comp_apply, distinctResponses_copyOutcomes n B d hd hfit]
  rfl

/-- The actual conditional positive-prior law, expressed using its finite
completion-averaged Walsh density. Restriction conditions on the entire graph.  [For the stated data and conditions](hyp:n,B,d,h,q,hn,hB,hd,hfit,hh,hq,H), [the stated conclusion holds](goal). -/
lemma conditionalBlockLaw_completion_walsh_representation (n B d : ℕ) (h q : ℝ)
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d (thinnedDesign (Fin n) q) true h H =
      (retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H})⁻¹ •
        (((graphAssignMarginal n B d (thinnedDesign (Fin n) q)).bind (fun hz =>
          (volume.withDensity (fun y => ENNReal.ofReal
            (completionWalshDensity n B d hfit h hz y))).map
              (fun y => (hz.1, hz.2, y)))).restrict {x | x.1 = H}).map Prod.snd := by
  rw [conditionalBlockLaw,
    reducedBlockLaw_completion_walsh_representation n B d h q hn hB hd hfit hh hq]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
