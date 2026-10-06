module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.PartitionTranslationBound

/-!
# Compatible-completion response shifts

A compatible labeled partition splits each source row into the observed signs
and its hidden labels. The hidden treated count supplies the exact shift used
in the polynomial conditional density; no treatment coordinate is discarded.
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The original source labels assigned to a specified block by a completion. -/
-- @node: partitionSourceLabels
def partitionSourceLabels (n B d : ℕ) (s : SourcePartition B d) (ℓ : Fin B) :
    Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ hj : j.val < B * d, s.1 ⟨j.val, hj⟩ = ℓ)

/-- Hidden labels in a completed row retain their original population labels. -/
-- @node: partitionHiddenLabels
def partitionHiddenLabels (n B d : ℕ) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool) (ℓ : Fin B) : Finset (Fin n) :=
  partitionSourceLabels n B d s ℓ \ revealedSources n B d H ℓ

/-- Count treated hidden labels in a specified compatible completed row. -/
-- @node: partitionHiddenTreated
def partitionHiddenTreated (n B d : ℕ) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool) (z : Assign (Fin n)) (ℓ : Fin B) : ℕ :=
  ((partitionHiddenLabels n B d s H ℓ).filter (fun j => z j = true)).card

/-- Every completed row has exactly d original source labels.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionSourceLabels_card
lemma partitionSourceLabels_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ℓ : Fin B) :
    (partitionSourceLabels n B d s ℓ).card = d := by
  let emb : Fin (B * d) → Fin n := fun j => ⟨j.val, by omega⟩
  have hemb : Function.Injective emb := by
    intro a b hab
    exact Fin.ext (congrArg (fun j : Fin n => j.val) hab)
  have he : partitionSourceLabels n B d s ℓ =
      (Finset.univ.filter (fun j => s.1 j = ℓ)).image emb := by
    ext j
    simp only [partitionSourceLabels, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_image]
    constructor
    · rintro ⟨hj, hs⟩
      exact ⟨⟨j.val, hj⟩, hs, Fin.ext rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.isLt, hk⟩
  rw [he, Finset.card_image_of_injective _ hemb]
  exact s.2 ℓ

/-- Compatibility with the complete graph fixes the row of every revealed label.  [For the stated data and conditions](hyp:n,B,d,s,H,hs,ℓ), [the stated conclusion holds](goal). -/
-- @node: revealedSources_subset_partitionSourceLabels
lemma revealedSources_subset_partitionSourceLabels (n B d : ℕ)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2) (ℓ : Fin B) :
    revealedSources n B d H ℓ ⊆ partitionSourceLabels n B d s ℓ := by
  intro j hj
  obtain ⟨hjlt, i, hi, hji, he⟩ := (Finset.mem_filter.mp hj).2
  obtain ⟨⟨hjlt', k, hsk, hik⟩, _⟩ := hs ⟨(j, i), hji⟩ he
  have hk : k = ℓ := recipientBlock_unique n B d i k ℓ hik hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjlt, by simpa [hk] using hsk⟩

/-- A compatible completion has exactly the observed remaining capacity in each row.  [For the stated data and conditions](hyp:n,B,d,hfit,s,H,hs,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenLabels_card
lemma partitionHiddenLabels_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2) (ℓ : Fin B) :
    (partitionHiddenLabels n B d s H ℓ).card = capacity n B d H ℓ := by
  rw [partitionHiddenLabels, Finset.card_sdiff_of_subset
    (revealedSources_subset_partitionSourceLabels n B d s H hs ℓ),
    partitionSourceLabels_card n B d hfit]
  rfl

/-- The completed row's treated hidden count is an admissible polynomial index.  [For the stated data and conditions](hyp:n,B,d,hfit,s,H,hs,z,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenTreated_le_capacity
lemma partitionHiddenTreated_le_capacity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (z : Assign (Fin n)) (ℓ : Fin B) :
    partitionHiddenTreated n B d s H z ℓ ≤ capacity n B d H ℓ := by
  rw [← partitionHiddenLabels_card n B d hfit s H hs ℓ]
  exact Finset.card_filter_le _ _

/-- Within a compatible completion, a hidden row label is precisely a source in that
row with no retained arrow anywhere in the complete graph.  [For the stated data and conditions](hyp:n,B,d,s,H,hs,ℓ,j), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenLabels_mem_iff
lemma partitionHiddenLabels_mem_iff (n B d : ℕ) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (ℓ : Fin B) (j : Fin n) :
    j ∈ partitionHiddenLabels n B d s H ℓ ↔
      (∃ hj : j.val < B * d, s.1 ⟨j.val, hj⟩ = ℓ) ∧
        ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i), hji⟩ = true := by
  simp only [partitionHiddenLabels, Finset.mem_sdiff, partitionSourceLabels, revealedSources,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨hj, hrow⟩, hn⟩
    refine ⟨⟨hj, hrow⟩, ?_⟩
    rintro ⟨i, hji, he⟩
    obtain ⟨⟨hj', k, hsk, hik⟩, _⟩ := hs ⟨(j,i), hji⟩ he
    have hk : k = ℓ := hsk.symm.trans hrow
    apply hn
    exact ⟨hj, i, by simpa [hk] using hik, hji, he⟩
  · rintro ⟨hrow, hn⟩
    refine ⟨hrow, ?_⟩
    rintro ⟨_, i, _, hji, he⟩
    exact hn ⟨i, hji, he⟩

/-- Completed row treated counts sum to the observed global hidden treated count;
this equality uses every assignment coordinate of each original hidden source label.  [For the stated data and conditions](hyp:n,B,d,s,H,hs,z), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenTreated_sum
lemma partitionHiddenTreated_sum (n B d : ℕ) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (z : Assign (Fin n)) :
    (∑ ℓ, partitionHiddenTreated n B d s H z ℓ) = hiddenTreated n B d H z := by
  by_cases hB : B = 0
  · subst B
    simp [hiddenTreated]
  let label : Fin n → Fin B := fun j =>
    if hj : j.val < B * d then s.1 ⟨j.val, hj⟩ else ⟨0, Nat.pos_of_ne_zero hB⟩
  let hidden := Finset.univ.filter (fun j : Fin n => j.val < B * d ∧ z j = true ∧
    ¬ ∃ i : Fin n, ∃ hji : j ≠ i, H ⟨(j,i),hji⟩ = true)
  have hrow (ℓ : Fin B) : hidden.filter (fun j => label j = ℓ) =
      (partitionHiddenLabels n B d s H ℓ).filter (fun j => z j = true) := by
    ext j
    simp only [Finset.mem_filter, hidden, Finset.mem_univ, true_and,
      partitionHiddenLabels_mem_iff n B d s H hs]
    constructor
    · rintro ⟨⟨hj, hz, hn⟩, hℓ⟩
      exact ⟨⟨⟨hj, by simpa only [label, dif_pos hj] using hℓ⟩, hn⟩, hz⟩
    · rintro ⟨⟨⟨hj, hℓ⟩, hn⟩, hz⟩
      exact ⟨⟨hj, hz, hn⟩, by simpa only [label, dif_pos hj] using hℓ⟩
  have hsplit : hidden.card = ∑ ℓ : Fin B, (hidden.filter (fun j => label j = ℓ)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
  simpa only [hrow, partitionHiddenTreated, hiddenTreated, hidden] using hsplit.symm

/-- Incoming neighbors of any block recipient are the completion's original source labels.  [For the stated data and conditions](hyp:n,B,d,s,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: partitionSourceLabels_eq_inNbhd
lemma partitionSourceLabels_eq_inNbhd (n B d : ℕ) (s : SourcePartition B d)
    (ℓ : Fin B) (i : Fin n) (hi : i ∈ recipientBlock n B d ℓ) :
    partitionSourceLabels n B d s ℓ =
      inNbhd (blockSchedule n B d true 0 (s, fun _ => 0)) i := by
  ext j
  simp only [partitionSourceLabels, inNbhd, blockSchedule, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hj, hs⟩
    exact (blockEdge_source_iff n B d s j i hj).mpr (by simpa [hs] using hi)
  · rintro ⟨⟨hj, k, hsk, hik⟩, _⟩
    exact ⟨hj, hsk.trans (recipientBlock_unique n B d i k ℓ hik hi)⟩

/-- A sum of centered Boolean signs is twice the treated-label count minus the row size.  [For the stated data and conditions](hyp:ι,S,z), [the stated conclusion holds](goal). -/
-- @node: partition_sign_sum_eq_treated
lemma partition_sign_sum_eq_treated {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (z : ι → Bool) :
    (∑ j ∈ S, signOf (z j)) = 2 * ((S.filter (fun j => z j = true)).card : ℝ) - S.card := by
  have he (j : ι) : signOf (z j) = 2 * (if z j = true then (1 : ℝ) else 0) - 1 := by
    cases z j <;> norm_num [signOf]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_filter]
  simp

/-- The completed source sum is exactly the revealed signs plus twice the hidden treated
count minus the remaining capacity.  [For the stated data and conditions](hyp:n,B,d,hfit,s,H,hs,z,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionSourceLabels_sign_sum
lemma partitionSourceLabels_sign_sum (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (z : Assign (Fin n)) (ℓ : Fin B) :
    (∑ j ∈ partitionSourceLabels n B d s ℓ, signOf (z j)) =
      revealedSignSum n B d H z ℓ + 2 * (partitionHiddenTreated n B d s H z ℓ : ℝ) -
        capacity n B d H ℓ := by
  have hsplit := Finset.sum_sdiff (f := fun j => signOf (z j))
    (revealedSources_subset_partitionSourceLabels n B d s H hs ℓ)
  change (∑ j ∈ partitionHiddenLabels n B d s H ℓ, signOf (z j)) +
    revealedSignSum n B d H z ℓ = _ at hsplit
  rw [partition_sign_sum_eq_treated, partitionHiddenLabels_card n B d hfit s H hs ℓ]
    at hsplit
  change 2 * (partitionHiddenTreated n B d s H z ℓ : ℝ) - capacity n B d H ℓ +
    revealedSignSum n B d H z ℓ = _ at hsplit
  linarith

/-- The actual fixed-partition response shift equals the shift in the polynomial density
for the completed row's hidden treated count.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,ℓ), [the stated conclusion holds](goal). -/
-- @node: partitionResponseShift_eq_hiddenTreated
lemma partitionResponseShift_eq_hiddenTreated (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (ℓ : Fin B) :
    partitionResponseShift n B d σ h s ω ℓ =
      signOf σ * h *
        (revealedSignSum n B d
            (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 ℓ +
          2 * (partitionHiddenTreated n B d s
            (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 ℓ : ℝ) -
          capacity n B d (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ℓ) /
        (2 * d) := by
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
    rw [recipientBlock_card n B d hfit ℓ]
    omega)
  rw [partitionResponseShift_eq_source_sum n B d hd hfit σ h s ω ℓ i hi,
    ← partitionSourceLabels_eq_inNbhd n B d s ℓ i hi,
    partitionSourceLabels_sign_sum n B d hfit s
      (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) (fun e he => by
      have he' : blockEdge n B d s e.val.1 e.val.2 ∧ ω.2 e = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using he
      exact he'.1)]
  ring

/-- The actual completed hidden counts are admissible polynomial indices, retaining
all original labels and the detailed retained edge subsets. -/
-- @node: partitionHiddenAllocation
def partitionHiddenAllocation (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) :
    ∀ ℓ, Fin (capacity n B d
      (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ℓ + 1) :=
  fun ℓ => ⟨partitionHiddenTreated n B d s
    (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 ℓ,
    Nat.lt_succ_of_le (partitionHiddenTreated_le_capacity n B d hfit s _
      (fun e he => by
        have he' : blockEdge n B d s e.val.1 e.val.2 ∧ ω.2 e = true := by
          simpa only [Bool.and_eq_true, decide_eq_true_eq] using he
        exact he'.1) ω.1 ℓ)⟩

/-- The actual admissible allocation satisfies the coefficient extraction's global degree
constraint, including the endpoint of zero hidden capacity.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ω), [the stated conclusion holds](goal). -/
-- @node: partitionHiddenAllocation_sum
lemma partitionHiddenAllocation_sum (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) :
    (∑ ℓ, (partitionHiddenAllocation n B d hfit s ω ℓ).val) =
      hiddenTreated n B d
        (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 := by
  exact partitionHiddenTreated_sum n B d s
    (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) (fun e he => by
    have he' : blockEdge n B d s e.val.1 e.val.2 ∧ ω.2 e = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using he
    exact he'.1) ω.1

/-- The product row density associated with the actual compatible allocation. Its shifts
are precisely those appearing in the coefficient-extraction formula. -/
-- @node: partitionAllocationDensity
def partitionAllocationDensity (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ) : ℝ :=
  ∏ ℓ, cosSqDensity (y ℓ - signOf σ * h *
    (revealedSignSum n B d
        (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 ℓ +
      2 * ((partitionHiddenAllocation n B d hfit s ω ℓ).val : ℝ) -
      capacity n B d (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ℓ) /
    (2 * d))

/-- The original fixed-partition density is exactly the row product at the completed
hidden treated allocation.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,y), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_eq_allocationDensity
lemma partitionResponseDensity_eq_allocationDensity (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ) :
    partitionResponseDensity n B d σ h s ω y =
      partitionAllocationDensity n B d hfit σ h s ω y := by
  unfold partitionResponseDensity partitionAllocationDensity partitionHiddenAllocation
  simp_rw [partitionResponseShift_eq_hiddenTreated n B d hd hfit]

/-- The fixed-partition product density satisfies exactly the total-degree constraint
used in the hypergeometric polynomial formula.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,s,ω,y), [the stated conclusion holds](goal). -/
-- @node: partitionResponseDensity_eq_constrainedAllocation
lemma partitionResponseDensity_eq_constrainedAllocation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) (y : Fin B → ℝ) :
    partitionResponseDensity n B d σ h s ω y =
      if hiddenTreated n B d
        (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 =
          ∑ ℓ, (partitionHiddenAllocation n B d hfit s ω ℓ).val then
        partitionAllocationDensity n B d hfit σ h s ω y else 0 := by
  rw [if_pos (partitionHiddenAllocation_sum n B d hfit s ω).symm]
  exact partitionResponseDensity_eq_allocationDensity n B d hd hfit σ h s ω y

/-- Before the compatible-allocation counting step, the actual full mixture is exactly
the partition average of the allocation row density followed by copying every outcome.
This representation preserves all retained edges and all assignment coordinates.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,D), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_allocation_density_representation
lemma blockMixtureLawOf_allocation_density_representation (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] :
    blockMixtureLawOf n B d D σ h = (partitionLaw B d).bind (fun s =>
      (densityJoint D volume (fun ω y =>
        if hiddenTreated n B d
          (fun e => decide (blockEdge n B d s e.val.1 e.val.2) && ω.2 e) ω.1 =
            ∑ ℓ, (partitionHiddenAllocation n B d hfit s ω ℓ).val then
          partitionAllocationDensity n B d hfit σ h s ω y else 0)).map
        (fun x => copyOutcomes n B d
          ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) x.1).1, x.1.1)
          x.2)) := by
  rw [blockMixtureLawOf_partition_density_representation n B d hd hfit]
  simp_rw [densityJoint, partitionResponseDensity_eq_constrainedAllocation n B d hd hfit]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
