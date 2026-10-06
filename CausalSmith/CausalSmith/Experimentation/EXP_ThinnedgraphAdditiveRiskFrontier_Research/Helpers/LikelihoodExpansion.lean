module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BaselineTransport
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockLawBasics
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RowReferenceDomination
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.SymmetricSignPolys
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.TwoPriorRisk
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.WalshChannelEnergy

/-!
# Conditional likelihood for the hidden-allocation record
-/

@[expose] public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

variable (n B d : ℕ)

/-- Extract distinct block responses by averaging identical recipient outcomes. -/
def distinctResponses (o : Record (Fin n)) : Fin B → ℝ :=
  fun ℓ => (d : ℝ)⁻¹ * ∑ i ∈ recipientBlock n B d ℓ, o.2.2 i

/-- Full retained graph together with all assignments and distinct block responses. -/
def reducedBlockLaw (D : Measure (Assign (Fin n) × Audit (Fin n))) (σ : Bool) (h : ℝ) :
    Measure ((OffDiag (Fin n) → Bool) × (Assign (Fin n) × (Fin B → ℝ))) :=
  (blockMixtureLawOf n B d D σ h).map (fun o => (o.1, o.2.1, distinctResponses n B d o))

/-- Copying a block response gives that same value at every recipient in its block.  [For the stated data and conditions](hyp:hz,y,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: copyOutcomes_recipient
lemma copyOutcomes_recipient (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n))
    (y : Fin B → ℝ) (ℓ : Fin B) (i : Fin n) (hi : i ∈ recipientBlock n B d ℓ) :
    (copyOutcomes n B d hz y).2.2 i = y ℓ := by
  change (∑ k : Fin B, if i ∈ recipientBlock n B d k then y k else 0) = y ℓ
  rw [Finset.sum_eq_single ℓ]
  · simp [hi]
  · intro k _ hk
    rw [if_neg]
    exact fun hik => hk (recipientBlock_unique n B d i k ℓ hik hi)
  · simp

/-- Averaging the copied recipients recovers the distinct response exactly.  [For the stated data and conditions](hyp:hd,hfit,hz,y), [the stated conclusion holds](goal). -/
-- @node: distinctResponses_copyOutcomes
lemma distinctResponses_copyOutcomes (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hz : (OffDiag (Fin n) → Bool) × Assign (Fin n)) (y : Fin B → ℝ) :
    distinctResponses n B d (copyOutcomes n B d hz y) = y := by
  funext ℓ
  unfold distinctResponses
  rw [Finset.sum_congr rfl (fun i hi => copyOutcomes_recipient n B d hz y ℓ i hi)]
  simp only [Finset.sum_const, nsmul_eq_mul, recipientBlock_card n B d hfit]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]

/-- Two recipients in the same block have identical potential outcomes for every assignment.  [For the stated data and conditions](hyp:σ,h,ξ,z,ℓ,i,k,hi,hk), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_response_constant
lemma blockSchedule_response_constant (σ : Bool) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) (z : Assign (Fin n))
    (ℓ : Fin B) (i k : Fin n)
    (hi : i ∈ recipientBlock n B d ℓ) (hk : k ∈ recipientBlock n B d ℓ) :
    potentialOutcome (blockSchedule n B d σ h ξ) i z =
      potentialOutcome (blockSchedule n B d σ h ξ) k z := by
  have hmem (r : Fin n) (hr : r ∈ recipientBlock n B d ℓ) (t : Fin B) :
      r ∈ recipientBlock n B d t ↔ t = ℓ := by
    constructor
    · intro ht
      exact recipientBlock_unique n B d r t ℓ ht hr
    · rintro rfl
      exact hr
  have hedge (r : Fin n) (hr : r ∈ recipientBlock n B d ℓ) (j : Fin n) :
      blockEdge n B d ξ.1 j r ↔ ∃ hj : j.val < B * d, ξ.1.1 ⟨j.val, hj⟩ = ℓ := by
    constructor
    · rintro ⟨⟨hj, t, ht, hrt⟩, _⟩
      exact ⟨hj, ht.trans ((hmem r hr t).mp hrt)⟩
    · rintro ⟨hj, ht⟩
      apply (blockEdge_source_iff n B d ξ.1 j r hj).mpr
      simpa [ht] using hr
  simp only [potentialOutcome, blockSchedule, inNbhd, zero_mul, add_zero,
    hmem i hi, hmem k hk, hedge i hi, hedge k hk]

/-- Sources and padding labels have zero response under every constructed schedule.  [For the stated data and conditions](hyp:σ,h,ξ,z,i,hi), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_response_zero
lemma blockSchedule_response_zero (σ : Bool) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) (z : Assign (Fin n)) (i : Fin n)
    (hi : ∀ ℓ, i ∉ recipientBlock n B d ℓ) :
    potentialOutcome (blockSchedule n B d σ h ξ) i z = 0 := by
  rw [potentialOutcome, blockSchedule_inNbhd_empty n B d σ h ξ i hi]
  simp [blockSchedule, hi]

/-- On a genuine block record, the distinct-response average is each recipient's response.  [For the stated data and conditions](hyp:hd,hfit,σ,h,ξ,ω,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: distinctResponses_record_recipient
lemma distinctResponses_record_recipient (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (ξ : SourcePartition B d × (Fin B → ℝ))
    (ω : Assign (Fin n) × Audit (Fin n)) (ℓ : Fin B) (i : Fin n)
    (hi : i ∈ recipientBlock n B d ℓ) :
    distinctResponses n B d (recordOf (blockSchedule n B d σ h ξ) ω) ℓ =
      potentialOutcome (blockSchedule n B d σ h ξ) i ω.1 := by
  unfold distinctResponses
  change (d : ℝ)⁻¹ * (∑ k ∈ recipientBlock n B d ℓ,
    potentialOutcome (blockSchedule n B d σ h ξ) k ω.1) = _
  rw [Finset.sum_congr rfl (fun k hk =>
    blockSchedule_response_constant n B d σ h ξ ω.1 ℓ k i hk hi)]
  simp only [Finset.sum_const, nsmul_eq_mul, recipientBlock_card n B d hfit]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [← mul_assoc, inv_mul_cancel₀ hd0, one_mul]

/-- Copying the recovered distinct responses reconstructs the entire original record,
including every retained edge and treatment coordinate.  [For the stated data and conditions](hyp:hd,hfit,σ,h,ξ,ω), [the stated conclusion holds](goal). -/
-- @node: copyOutcomes_distinctResponses_record
lemma copyOutcomes_distinctResponses_record (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (ξ : SourcePartition B d × (Fin B → ℝ))
    (ω : Assign (Fin n) × Audit (Fin n)) :
    copyOutcomes n B d
      ((recordOf (blockSchedule n B d σ h ξ) ω).1, ω.1)
      (distinctResponses n B d (recordOf (blockSchedule n B d σ h ξ) ω)) =
        recordOf (blockSchedule n B d σ h ξ) ω := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · rfl
  funext i
  by_cases hi : ∃ ℓ, i ∈ recipientBlock n B d ℓ
  · obtain ⟨ℓ, hi⟩ := hi
    exact (copyOutcomes_recipient n B d _ _ ℓ i hi).trans
      (distinctResponses_record_recipient n B d hd hfit σ h ξ ω ℓ i hi)
  · have hn := not_exists.mp hi
    change (∑ ℓ : Fin B, if i ∈ recipientBlock n B d ℓ then _ else 0) = _
    simp only [hn, ite_false, Finset.sum_const_zero]
    exact (blockSchedule_response_zero n B d σ h ξ ω.1 i hn).symm

/-- [The response-copying channel is measurable jointly in the full finite marginal
and the distinct real responses.](goal) -/
-- @node: copyOutcomes_measurable
@[fun_prop] lemma copyOutcomes_measurable :
    Measurable (fun x : (OffDiag (Fin n) → Bool) × (Assign (Fin n) × (Fin B → ℝ)) =>
      copyOutcomes n B d (x.1, x.2.1) x.2.2) := by
  unfold copyOutcomes
  apply measurable_fst.prodMk
  apply (measurable_fst.comp measurable_snd).prodMk
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_sum
  intro ℓ _
  by_cases hi : i ∈ recipientBlock n B d ℓ <;> simp only [hi, ite_true, ite_false] <;> fun_prop

/-- [Recovering distinct responses is a measurable statistic of the complete original record.](goal) -/
-- @node: distinctResponses_measurable
@[fun_prop] lemma distinctResponses_measurable : Measurable (distinctResponses n B d) := by
  unfold distinctResponses
  fun_prop

/-- Applying the measurable copying channel to the reduced law recovers the complete
original-record mixture, without using the unfinished conditional-density identity.  [For the stated data and conditions](hyp:hd,hfit,D,σ,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_copy_eq
lemma reducedBlockLaw_copy_eq (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [SFinite D] (σ : Bool) (h : ℝ) :
    (reducedBlockLaw n B d D σ h).map
      (fun x => copyOutcomes n B d (x.1, x.2.1) x.2.2) =
        blockMixtureLawOf n B d D σ h := by
  unfold reducedBlockLaw
  rw [Measure.map_map (copyOutcomes_measurable n B d) (by fun_prop)]
  unfold blockMixtureLawOf mixtureLaw
  rw [block_map_bind _ _ _
    (block_measurable_map_parameter D _ (block_record_measurable n B d σ h))
    ((copyOutcomes_measurable n B d).comp (by fun_prop))]
  congr 1
  funext ξ
  rw [Measure.map_map
    ((copyOutcomes_measurable n B d).comp (by fun_prop)) (measurable_of_finite _)]
  congr 1
  funext ω
  exact copyOutcomes_distinctResponses_record n B d hd hfit σ h ξ ω

/-- A measurable map contracts total variation by taking preimages of test events.  [For the stated data and conditions](hyp:α,β,μ,ν,f,hf), [the stated conclusion holds](goal). -/
-- @node: block_tvDist_map_le
lemma block_tvDist_map_le {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α → β) (hf : Measurable f) :
    Causalean.Stat.tvDist (μ.map f) (ν.map f) ≤ Causalean.Stat.tvDist μ ν := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  rw [map_measureReal_apply_of_aemeasurable hf.aemeasurable hA,
    map_measureReal_apply_of_aemeasurable hf.aemeasurable hA]
  exact Causalean.Stat.abs_measureReal_sub_le_tvDist (hf hA)

/-- Complete block mixtures are probability laws for every sign and amplitude.  [For the stated data and conditions](hyp:D,σ,h), [the stated conclusion holds](goal). -/
-- @node: blockMixtureLawOf_probability
lemma blockMixtureLawOf_probability
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (σ : Bool) (h : ℝ) : IsProbabilityMeasure (blockMixtureLawOf n B d D σ h) := by
  let := partitionLaw_probability B d
  let := blockBaselineLaw_probability B
  let : IsProbabilityMeasure (blockParamLaw B d) := by unfold blockParamLaw; infer_instance
  exact mixtureLaw_probability D (blockParamLaw B d) (blockSchedule n B d σ h)
    (block_record_measurable n B d σ h)

/-- Recovering and copying distinct responses preserve total variation exactly. Thus
working with distinct outcomes retains all the information in the original record.  [For the stated data and conditions](hyp:hd,hfit,D,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_tvDist_eq
lemma reducedBlockLaw_tvDist_eq (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) :
    Causalean.Stat.tvDist (reducedBlockLaw n B d D true h)
      (reducedBlockLaw n B d D false h) =
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) := by
  let (σ : Bool) : IsProbabilityMeasure (blockMixtureLawOf n B d D σ h) :=
    blockMixtureLawOf_probability n B d D σ h
  have hm : Measurable (fun o : Record (Fin n) =>
      (o.1, o.2.1, distinctResponses n B d o)) := by fun_prop
  let (σ : Bool) : IsProbabilityMeasure (reducedBlockLaw n B d D σ h) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  apply le_antisymm
  · exact block_tvDist_map_le _ _ _ hm
  · rw [← reducedBlockLaw_copy_eq n B d hd hfit D true h,
      ← reducedBlockLaw_copy_eq n B d hd hfit D false h]
    exact block_tvDist_map_le _ _ _ (copyOutcomes_measurable n B d)

/-- A recipient response is its baseline plus the centered source-sign shift.  [For the stated data and conditions](hyp:hd,hfit,σ,h,ξ,z,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_response_centered
lemma blockSchedule_response_centered (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (ξ : SourcePartition B d × (Fin B → ℝ))
    (z : Assign (Fin n)) (ℓ : Fin B) (i : Fin n)
    (hi : i ∈ recipientBlock n B d ℓ) :
    potentialOutcome (blockSchedule n B d σ h ξ) i z =
      ξ.2 ℓ + signOf σ * h / (2 * d) *
        ∑ j ∈ inNbhd (blockSchedule n B d σ h ξ) i, signOf (z j) := by
  have ha : (blockSchedule n B d σ h ξ).a i = ξ.2 ℓ - signOf σ * h / 2 := by
    change (∑ k : Fin B, if i ∈ recipientBlock n B d k then _ else 0) = _
    rw [Finset.sum_eq_single ℓ]
    · simp [hi]
    · intro k _ hk
      rw [if_neg]
      exact fun hik => hk (recipientBlock_unique n B d i k ℓ hik hi)
    · simp
  have hz (j : Fin n) : (if z j then (1 : ℝ) else 0) = (signOf (z j) + 1) / 2 := by
    cases z j <;> norm_num [signOf]
  rw [potentialOutcome, ha]
  simp only [blockSchedule, zero_mul, add_zero]
  simp_rw [treatment, hz]
  simp only [add_div, mul_add, Finset.sum_add_distrib, Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  have hc := blockSchedule_inNbhd_card n B d hd hfit σ h ξ i ℓ hi
  simp only [blockSchedule] at hc
  rw [hc, ← Finset.sum_div]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  field_simp
  <;> ring

/-- Enumerating a recipient's actual d source labels gives a row-channel sign vector.  [For the stated data and conditions](hyp:hd,hfit,σ,h,s,z,ℓ,i,hi), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_response_row_signs
lemma blockSchedule_response_row_signs (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (s : SourcePartition B d) (z : Assign (Fin n))
    (ℓ : Fin B) (i : Fin n) (hi : i ∈ recipientBlock n B d ℓ) :
    ∃ ε : Fin d → Bool, ∀ U : Fin B → ℝ,
      potentialOutcome (blockSchedule n B d σ h (s, U)) i z =
        U ℓ + signOf σ * h / (2 * d) * ∑ j, signOf (ε j) := by
  let N := inNbhd (blockSchedule n B d σ h (s, fun _ => 0)) i
  have hc : N.card = d := blockSchedule_inNbhd_card n B d hd hfit σ h _ i ℓ hi
  let e : N ≃ Fin d := Finset.equivFinOfCardEq hc
  refine ⟨fun j => z (e.symm j).val, ?_⟩
  intro U
  rw [blockSchedule_response_centered n B d hd hfit σ h (s, U) z ℓ i hi]
  have he : (∑ j ∈ N, signOf (z j)) = ∑ j : Fin d, signOf (z (e.symm j).val) := by
    rw [← Finset.sum_attach]
    exact Fintype.sum_equiv e _ _ (fun j => by simp)
  change U ℓ + signOf σ * h / (2 * d) * (∑ j ∈ N, signOf (z j)) = _
  rw [he]

/-- All distinct responses, conditional on a fixed partition and the entire design draw,
are independent baseline translations by actual source signs.  [For the stated data and conditions](hyp:hd,hfit,σ,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: distinctResponses_record_row_signs
lemma distinctResponses_record_row_signs (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (σ : Bool) (h : ℝ) (s : SourcePartition B d)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    ∃ ε : Fin B → Fin d → Bool, ∀ U : Fin B → ℝ,
      distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, U)) ω) =
        fun ℓ => U ℓ + signOf σ * h / (2 * d) * ∑ j, signOf (ε ℓ j) := by
  have hrow (ℓ : Fin B) : ∃ ε : Fin d → Bool, ∀ U : Fin B → ℝ,
      distinctResponses n B d (recordOf (blockSchedule n B d σ h (s, U)) ω) ℓ =
        U ℓ + signOf σ * h / (2 * d) * ∑ j, signOf (ε j) := by
    have hc := recipientBlock_card n B d hfit ℓ
    have hn : (recipientBlock n B d ℓ).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨i, hi⟩ := hn
    obtain ⟨ε, hε⟩ := blockSchedule_response_row_signs n B d hd hfit σ h s ω.1 ℓ i hi
    refine ⟨ε, fun U => ?_⟩
    rw [distinctResponses_record_recipient n B d hd hfit σ h (s, U) ω ℓ i hi]
    exact hε U
  choose ε hε using hrow
  exact ⟨ε, fun U => funext (fun ℓ => hε ℓ U)⟩

/-- For a fixed partition and complete design draw, the positive-sign response law is
exactly a product of row-channel components indexed by the actual source labels.  [For the stated data and conditions](hyp:hd,hfit,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: block_responseLaw_eq_translatedRows
lemma block_responseLaw_eq_translatedRows (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (h : ℝ) (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) :
    ∃ ε : Fin B → Fin d → Bool,
      (blockBaselineLaw B).map (fun U =>
        distinctResponses n B d (recordOf (blockSchedule n B d true h (s, U)) ω)) =
      Measure.pi (fun ℓ => volume.withDensity
        (fun w => ENNReal.ofReal (rowDensity d h (ε ℓ) w))) := by
  obtain ⟨ε, hε⟩ := distinctResponses_record_row_signs n B d hd hfit true h s ω
  refine ⟨ε, ?_⟩
  have he : (fun U => distinctResponses n B d
      (recordOf (blockSchedule n B d true h (s, U)) ω)) =
      fun U ℓ => U ℓ + h / (2 * d) * ∑ j, signOf (ε ℓ j) := by
    funext U
    simpa [signOf] using hε U
  let : IsProbabilityMeasure (volume.withDensity
      (fun w => ENNReal.ofReal (cosSqDensity w))) := by
    simpa [rowDensity] using translatedRowLaw_probability 0 0 (fun _ => false)
  let (ℓ : Fin B) : IsProbabilityMeasure
      ((volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))).map
        (fun w => w + h / (2 * d) * ∑ j, signOf (ε ℓ j))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  rw [he, blockBaselineLaw,
    Measure.pi_map_pi (f := fun ℓ w => w + h / (2 * d) * ∑ j, signOf (ε ℓ j))
      (fun _ => by fun_prop)]
  simp_rw [baseline_map_add_density]
  rfl

/-- Every fixed-partition, fixed-design response law is dominated by the independent
reference responses, before any conditional allocation calculation.  [For the stated data and conditions](hyp:hd,hfit,h,s,ω), [the stated conclusion holds](goal). -/
-- @node: block_responseLaw_absolutelyContinuous_reference
lemma block_responseLaw_absolutelyContinuous_reference
    (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (h : ℝ) (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n)) :
    (blockBaselineLaw B).map (fun U =>
      distinctResponses n B d (recordOf (blockSchedule n B d true h (s, U)) ω)) ≪
      Measure.pi (fun _ : Fin B => volume.withDensity
        (fun w => ENNReal.ofReal (refDensity d h w))) := by
  obtain ⟨ε, he⟩ := block_responseLaw_eq_translatedRows n B d hd hfit h s ω
  rw [he]
  exact translatedRows_absolutelyContinuous_reference B d h ε

/-- Conditioning on a finite retained-graph atom; values on null atoms are immaterial. -/
def conditionalBlockLaw (D : Measure (Assign (Fin n) × Audit (Fin n))) (σ : Bool) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) : Measure (Assign (Fin n) × (Fin B → ℝ)) :=
  ((retainedGraphMarginal n B d D) {H})⁻¹ •
    ((reducedBlockLaw n B d D σ h).restrict {x | x.1 = H}).map Prod.snd

/-- Actual assignment marginal with independent reference responses. -/
def hiddenReferenceLaw (D : Measure (Assign (Fin n) × Audit (Fin n))) (h : ℝ) :
    Measure (Assign (Fin n) × (Fin B → ℝ)) :=
  (D.map Prod.fst).prod (Measure.pi (fun _ : Fin B =>
    volume.withDensity (fun w => ENNReal.ofReal (refDensity d h w))))

/-- After mixing the partition and baselines, the assignment-response marginal is
still dominated by the actual assignment marginal times the reference responses.  [For the stated data and conditions](hyp:hd,hfit,D,h), [the stated conclusion holds](goal). -/
-- @node: reducedBlockLaw_snd_absolutelyContinuous_reference
lemma reducedBlockLaw_snd_absolutelyContinuous_reference
    (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D] (h : ℝ) :
    (reducedBlockLaw n B d D true h).map Prod.snd ≪ hiddenReferenceLaw n B d D h := by
  let ν := Measure.pi (fun _ : Fin B => volume.withDensity
    (fun w => ENNReal.ofReal (refDensity d h w)))
  let := referenceRowLaw_probability d h
  let := blockBaselineLaw_probability B
  let f := fun o : Record (Fin n) => (o.2.1, distinctResponses n B d o)
  have hf : Measurable f := by fun_prop
  have hrec : Measurable (fun x : (SourcePartition B d × (Fin B → ℝ)) ×
      (Assign (Fin n) × Audit (Fin n)) => f (recordOf (blockSchedule n B d true h x.1) x.2)) :=
    hf.comp (block_record_measurable n B d true h)
  let K := fun ξ : SourcePartition B d × (Fin B → ℝ) =>
    D.map (fun ω => f (recordOf (blockSchedule n B d true h ξ) ω))
  have hK : Measurable K := block_measurable_map_parameter D _ hrec
  have heq : (reducedBlockLaw n B d D true h).map Prod.snd = (blockParamLaw B d).bind K := by
    rw [reducedBlockLaw, Measure.map_map (by fun_prop) (by fun_prop)]
    change (blockMixtureLawOf n B d D true h).map f = _
    rw [blockMixtureLawOf, mixtureLaw, block_map_bind _ _ _
      (block_measurable_map_parameter D _ (block_record_measurable n B d true h)) hf]
    congr 1
    funext ξ
    exact Measure.map_map hf (measurable_of_finite _)
  rw [heq]
  apply Measure.AbsolutelyContinuous.mk
  intro E hE hzero
  have hz : ∀ᵐ z ∂D.map Prod.fst, ν (Prod.mk z ⁻¹' E) = 0 :=
    Measure.measure_ae_null_of_prod_null hzero
  have hω : ∀ᵐ ω ∂D, ν (Prod.mk ω.1 ⁻¹' E) = 0 :=
    ae_of_ae_map (by fun_prop) hz
  have hs (s : SourcePartition B d) :
      (∫⁻ U, K (s, U) E ∂blockBaselineLaw B) = 0 := by
    let g := fun x : (Fin B → ℝ) × (Assign (Fin n) × Audit (Fin n)) =>
      f (recordOf (blockSchedule n B d true h (s, x.1)) x.2)
    have hg : Measurable g := hrec.comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
    have hp : ((blockBaselineLaw B).prod D) (g ⁻¹' E) = 0 := by
      rw [Measure.prod_apply_symm (hg hE)]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hω] with ω hω
      have hac := block_responseLaw_absolutelyContinuous_reference n B d hd hfit h s ω
      have hz' := hac hω
      have hm : Measurable (fun U => distinctResponses n B d
          (recordOf (blockSchedule n B d true h (s, U)) ω)) :=
        (distinctResponses_measurable n B d).comp
          ((block_record_measurable n B d true h).comp
            ((measurable_const.prodMk measurable_id).prodMk measurable_const))
      rw [Measure.map_apply hm (measurable_prodMk_left hE)] at hz'
      exact hz'
    rw [Measure.prod_apply (hg hE)] at hp
    convert hp using 1
    apply lintegral_congr
    intro U
    exact Measure.map_apply (measurable_of_finite _) hE
  have hm : Measurable (fun ξ => K ξ E) := (Measure.measurable_coe hE).comp hK
  rw [Measure.bind_apply hE hK.aemeasurable, blockParamLaw,
    lintegral_prod (fun ξ => K ξ E) hm.aemeasurable]
  simp_rw [hs]
  simp

/-- Restriction to a retained-graph atom and rescaling preserve reference domination;
this also covers null atoms under the total ENNReal convention.  [For the stated data and conditions](hyp:hd,hfit,D,h,H), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_absolutelyContinuous_of_probability
lemma conditionalBlockLaw_absolutelyContinuous_of_probability
    (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) [IsProbabilityMeasure D]
    (h : ℝ) (H : OffDiag (Fin n) → Bool) :
    conditionalBlockLaw n B d D true h H ≪ hiddenReferenceLaw n B d D h := by
  have hac := reducedBlockLaw_snd_absolutelyContinuous_reference n B d hd hfit D h
  have hle : ((reducedBlockLaw n B d D true h).restrict {x | x.1 = H}).map Prod.snd ≤
      (reducedBlockLaw n B d D true h).map Prod.snd :=
    Measure.map_mono Measure.restrict_le_self (by fun_prop)
  exact (hle.absolutelyContinuous.trans hac).smul_left _

/-- The positive-sign conditional block law is dominated by the reference law on almost every
retained graph.  [For the stated data and conditions](hyp:n,B,d,h,q,μZ,hB,hd,hfit,hh,hq,ha), [the stated conclusion holds](goal). -/
-- @node: conditionalBlockLaw_absolutelyContinuous
lemma conditionalBlockLaw_absolutelyContinuous (n B d : ℕ) (h q : ℝ)
    (μZ : Measure (Assign (Fin n))) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (hh : h ∈ Set.Icc 0 (1 / 4)) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw (μZ.prod (auditLaw (Fin n) q))) :
    ∀ᵐ H ∂(retainedGraphMarginal n B d (μZ.prod (auditLaw (Fin n) q))),
      conditionalBlockLaw n B d (μZ.prod (auditLaw (Fin n) q)) true h H ≪
        hiddenReferenceLaw n B d (μZ.prod (auditLaw (Fin n) q)) h := by
  let : IsProbabilityMeasure (bernoulliLaw (1 / 2)) :=
    bernoulliLaw_probability _ (by constructor <;> norm_num)
  let : IsProbabilityMeasure (halfBernoulli (Fin n)) := by
    unfold halfBernoulli
    infer_instance
  let : IsProbabilityMeasure (μZ.prod (auditLaw (Fin n) q)) := by
    constructor
    have ht := congrArg (fun μ : Measure (Assign (Fin n)) => μ Set.univ) ha
    rw [Measure.map_apply (by fun_prop) MeasurableSet.univ] at ht
    simpa using ht
  exact Filter.Eventually.of_forall (fun H =>
    conditionalBlockLaw_absolutelyContinuous_of_probability n B d hd hfit _ h H)

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
