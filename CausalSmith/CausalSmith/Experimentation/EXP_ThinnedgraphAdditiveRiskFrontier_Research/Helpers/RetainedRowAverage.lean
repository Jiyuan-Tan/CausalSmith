module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ActiveRowAverage
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockReveal
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.RevealedSubsetEnergyBridge

/-!
# Averaging actual partition-dependent retained rows

Enumerate the source fiber of each original partition before reducing the
full retained graph to its row counts.
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Under a fixed original partition, membership in a revealed row is exactly
source revelation together with membership in that partition's source fiber.  [For the stated data and conditions](hyp:n,B,d,hfit,s,ω,ℓ,j), [the stated conclusion holds](goal). -/
-- @node: fixed_partition_revealed_source_iff
lemma fixed_partition_revealed_source_iff (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (ω : Assign (Fin n) × Audit (Fin n))
    (ℓ : Fin B) (j : Fin n) :
    j ∈ revealedSources n B d
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 ℓ ↔
    ∃ a : Fin (B * d), a.val = j.val ∧ s.1 a = ℓ ∧
      sourceReveals n B d
        (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 a = true := by
  classical
  let H := (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1
  have hs (e : OffDiag (Fin n)) (he : H e = true) :
      blockEdge n B d s e.1.1 e.1.2 := by
    change (decide (blockEdge n B d s e.1.1 e.1.2) && ω.2 e) = true at he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    exact he.1
  constructor
  · intro hj
    obtain ⟨hjl, i, hi, hji, he⟩ := (Finset.mem_filter.mp hj).2
    let a : Fin (B * d) := ⟨j.val, hjl⟩
    have hedge := hs ⟨(j,i),hji⟩ he
    obtain ⟨_, k, hk, hik⟩ := hedge.1
    have hkl := recipientBlock_unique n B d i k ℓ hik hi
    refine ⟨a, rfl, ?_, ?_⟩
    · simpa [a, hkl] using hk
    · simp only [sourceReveals, decide_eq_true_eq]
      exact ⟨j, rfl, i, hji, he⟩
  · rintro ⟨a, haj, haℓ, ha⟩
    obtain ⟨v, hv, i, hvi, he⟩ := of_decide_eq_true ha
    have hvj : v = j := Fin.ext (hv.trans haj)
    subst v
    obtain ⟨_, k, hk, hik⟩ := (hs ⟨(j,i),hvi⟩ he).1
    have hka : (⟨j.val, by omega⟩ : Fin (B * d)) = a := Fin.ext haj.symm
    have hkℓ : k = ℓ := by simpa [hka, haℓ] using hk.symm
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, i, ?_, hvi, he⟩
    · simpa [← haj] using a.isLt
    · simpa [hkℓ] using hik

/-- A size-d source fiber can be enumerated without dropping any labels. The
revealed row count then equals the count in its enumerated source-reveal row.  [For the stated data and conditions](hyp:n,B,d,hfit,s), [the stated conclusion holds](goal). -/
-- @node: fixed_partition_row_enumeration
lemma fixed_partition_row_enumeration (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) :
    ∃ e : Fin B × Fin d → Fin (B * d), Function.Injective e ∧
      ∀ ω : Assign (Fin n) × Audit (Fin n), ∀ ℓ : Fin B,
        revealedCount n B d
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 ℓ =
          (Finset.univ.filter (fun k : Fin d => sourceReveals n B d
            (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k)) = true)).card := by
  classical
  let r (ℓ : Fin B) : Fin d ≃ {a : Fin (B * d) // s.1 a = ℓ} :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_fin, Fintype.card_subtype] using (s.2 ℓ).symm)
  let e : Fin B × Fin d → Fin (B * d) := fun x => (r x.1 x.2).val
  have he : Function.Injective e := by
    intro x y hxy
    have hℓ : x.1 = y.1 := by
      rw [← (r x.1 x.2).property, ← (r y.1 y.2).property]
      exact congrArg s.1 hxy
    apply Prod.ext hℓ
    have hv : (r x.1 x.2).val = (r x.1 y.2).val := by
      change (r x.1 x.2).val = (r y.1 y.2).val at hxy
      rw [← hℓ] at hxy
      exact hxy
    exact (r x.1).injective (Subtype.ext hv)
  refine ⟨e, he, ?_⟩
  intro ω ℓ
  let H := (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1
  let v (k : Fin d) : Fin n := ⟨(e (ℓ,k)).val, by have := (e (ℓ,k)).isLt; omega⟩
  have hv : Function.Injective v := by
    intro k k' hkk
    have hh : e (ℓ,k) = e (ℓ,k') := Fin.ext (congrArg (fun j : Fin n => j.val) hkk)
    exact congrArg Prod.snd (he hh)
  have hset : revealedSources n B d H ℓ =
      (Finset.univ.filter (fun k : Fin d => sourceReveals n B d H (e (ℓ,k)) = true)).image v := by
    ext j
    rw [fixed_partition_revealed_source_iff n B d hfit s ω ℓ j]
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, haj, haℓ, ha⟩
      obtain ⟨k, hk⟩ := (r ℓ).surjective ⟨a, haℓ⟩
      have hek : e (ℓ,k) = a := congrArg Subtype.val hk
      exact ⟨k, by simpa [hek] using ha, Fin.ext (by simpa [v, hek] using haj)⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨e (ℓ,k), rfl, (r ℓ k).property, hk⟩
  change (revealedSources n B d H ℓ).card = _
  rw [hset, Finset.card_image_of_injective _ hv]

/-- The enumerated reveals in any fixed original partition have the independent
row law, even though the observed retained graph keeps all edge subsets.  [For the stated data and conditions](hyp:n,B,d,q,hfit,hq,s,e,he), [the stated conclusion holds](goal). -/
-- @node: fixed_partition_reveal_rows_law
lemma fixed_partition_reveal_rows_law (n B d : ℕ) (q : ℝ)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (s : SourcePartition B d) (e : Fin B × Fin d → Fin (B * d))
    (he : Function.Injective e) :
    (thinnedDesign (Fin n) q).map (fun ω ℓ k => sourceReveals n B d
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k))) =
      Measure.pi (fun _ : Fin B => Measure.pi (fun _ : Fin d =>
        bernoulliLaw (retentionP d q))) := by
  have hsource := block_reveal_fixed_partition n B d q hfit hq s
  have hselect := bernoulli_select_coordinates e he (retentionP d q)
    (retentionP_mem_Icc d q hq)
  have hrows := bernoulli_curry_coordinates (I := Fin B) (J := Fin d)
    (retentionP d q) (retentionP_mem_Icc d q hq)
  have hfirst := congrArg (fun μ : Measure (Fin (B * d) → Bool) =>
    μ.map (fun w x => w (e x))) hsource
  rw [Measure.map_map (by fun_prop) (by fun_prop), hselect] at hfirst
  have hsecond := congrArg (fun μ : Measure (Fin B × Fin d → Bool) =>
    μ.map (fun w ℓ k => w (ℓ,k))) hfirst
  rw [Measure.map_map (by fun_prop) (by fun_prop), hrows] at hsecond
  exact hsecond

/-- Canonical count patterns preserve both row energies for any actual reveal row.  [For the stated data and conditions](hyp:d,h,r), [the stated conclusion holds](goal). -/
-- @node: countRevealRow_energy_eq
lemma countRevealRow_energy_eq (d : ℕ) (h : ℝ) (r : Fin d → Bool) :
    rowRevealedEnergy d h (countRevealRow d
      (Finset.univ.filter (fun j => r j = true)).card) = rowRevealedEnergy d h r ∧
    rowHiddenEnergy d h (countRevealRow d
      (Finset.univ.filter (fun j => r j = true)).card) = rowHiddenEnergy d h r := by
  classical
  apply rowRevealEnergy_eq_of_hidden_count_eq
  rw [(countRevealRow_counts d _ (by
    exact (Finset.card_filter_le _ _).trans_eq (by simp))).2]
  have hc : Finset.univ.filter (fun j : Fin d => r j = false) =
      Finset.univ \ Finset.univ.filter (fun j : Fin d => r j = true) := by
    ext j
    cases hj : r j <;> simp [hj]
  rw [hc, Finset.card_sdiff_of_subset (Finset.filter_subset _ _)]
  simp

/-- The nonconstant retained envelope is the independent-row expression under
any label-preserving enumeration of the original source partition.  [For the stated data and conditions](hyp:n,B,d,h,s,e,hc,ω), [the stated conclusion holds](goal). -/
-- @node: fixed_partition_envelope_eq
lemma fixed_partition_envelope_eq (n B d : ℕ) (h : ℝ)
    (s : SourcePartition B d) (e : Fin B × Fin d → Fin (B * d))
    (hc : ∀ ω : Assign (Fin n) × Audit (Fin n), ∀ ℓ : Fin B,
      revealedCount n B d
        (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 ℓ =
        (Finset.univ.filter (fun k : Fin d => sourceReveals n B d
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k)) = true)).card)
    (ω : Assign (Fin n) × Audit (Fin n)) :
    retainedRowEnergyEnvelope n B d h
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 =
      ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
        if A.card + E.card = 0 then 0 else
          (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
            ((∏ ℓ ∈ A, rowRevealedEnergy d h (fun k => sourceReveals n B d
              (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k)))) *
             (∏ ℓ ∈ E, rowHiddenEnergy d h (fun k => sourceReveals n B d
              (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k))))) := by
  unfold retainedRowEnergyEnvelope
  simp_rw [hc ω, (countRevealRow_energy_eq d h _).1,
    (countRevealRow_energy_eq d h _).2]

/-- The exact graph marginal is the uniform mixture of the fixed-partition
graph laws, before any row-count reduction.  [For the stated data and conditions](hyp:n,B,d,D), [the stated conclusion holds](goal). -/
-- @node: retainedGraphMarginal_partition_sum
lemma retainedGraphMarginal_partition_sum (n B d : ℕ)
    (D : Measure (Assign (Fin n) × Audit (Fin n))) :
    retainedGraphMarginal n B d D =
      (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ •
        ∑ s : SourcePartition B d, D.map (fun ω =>
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1) := by
  unfold retainedGraphMarginal graphAssignMarginal partitionLaw
  rw [Measure.bind_smul, ← Measure.sum_fintype,
    Measure.bind_sum _ _ (by fun_prop), Measure.sum_fintype]
  have hm : Measurable (fun s : SourcePartition B d =>
      D.map (fun ω => ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1))) := by fun_prop
  simp_rw [Measure.dirac_bind hm]
  rw [Measure.map_smul, ← Measure.sum_fintype, Measure.map_sum (by fun_prop),
    Measure.sum_fintype]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Each actual retained-row contribution is nonnegative, so removing the good
indicator is valid before partitionwise averaging.  [For the stated data and conditions](hyp:n,B,d,h,H), [the stated conclusion holds](goal). -/
-- @node: retainedRowEnergyEnvelope_nonneg
lemma retainedRowEnergyEnvelope_nonneg (n B d : ℕ) (h : ℝ)
    (H : OffDiag (Fin n) → Bool) : 0 ≤ retainedRowEnergyEnvelope n B d h H := by
  unfold retainedRowEnergyEnvelope
  apply Finset.sum_nonneg
  intro A _
  apply Finset.sum_nonneg
  intro E _
  split_ifs
  · exact le_rfl
  · apply mul_nonneg (by positivity)
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun ℓ _ => (rowRevealEnergy_bounds d h _).1)
    · exact Finset.prod_nonneg (fun ℓ _ => (rowRevealEnergy_bounds d h _).2.1)

/-- Fixed-partition averaging of the actual row-count envelope uses independent
reveals only after its original labels have been enumerated.  [For the stated data and conditions](hyp:n,B,d,h,q,hfit,hq,s), [the stated conclusion holds](goal). -/
-- @node: fixed_partition_row_energy_average_le
lemma fixed_partition_row_energy_average_le (n B d : ℕ) (h q : ℝ)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (s : SourcePartition B d) :
    (∫ ω, retainedRowEnergyEnvelope n B d h
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1
      ∂thinnedDesign (Fin n) q) ≤
      ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
        if a + b = 0 then 0 else
          (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
            (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
              (retentionP d q * etaOne d h) ^ a * eta d h ^ b := by
  classical
  obtain ⟨e, he, hc⟩ := fixed_partition_row_enumeration n B d hfit s
  let F (rows : Fin B → Fin d → Bool) : ℝ :=
    ∑ A : Finset (Fin B), ∑ E ∈ (Finset.univ \ A).powerset,
      if A.card + E.card = 0 then 0 else
        (min 1 (4 * (A.card + E.card : ℕ) / (B : ℝ))) ^ E.card *
          ((∏ ℓ ∈ A, rowRevealedEnergy d h (rows ℓ)) *
           (∏ ℓ ∈ E, rowHiddenEnergy d h (rows ℓ)))
  let rows (ω : Assign (Fin n) × Audit (Fin n)) := fun ℓ k => sourceReveals n B d
    (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 (e (ℓ,k))
  have hpoint (ω) : retainedRowEnergyEnvelope n B d h
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 = F (rows ω) :=
    fixed_partition_envelope_eq n B d h s e hc ω
  simp_rw [hpoint]
  have hlaw := fixed_partition_reveal_rows_law n B d q hfit hq s e he
  change (∫ ω, F (rows ω) ∂thinnedDesign (Fin n) q) ≤ _
  rw [← integral_map (by fun_prop : AEMeasurable rows (thinnedDesign (Fin n) q))
    (by fun_prop : AEStronglyMeasurable F ((thinnedDesign (Fin n) q).map rows)), hlaw]
  simpa only [Set.indicator_univ] using
    active_row_nonconstant_average_le B d h (retentionP d q)
      (retentionP_mem_Icc d q hq) Set.univ

/-- Averaging the full detailed graph mixture gives the finite nonconstant
contraction series. No source or edge labels are discarded in forming the law.  [For the stated data and conditions](hyp:n,B,d,h,q,hfit,hq), [the stated conclusion holds](goal). -/
-- @node: retained_row_energy_average_le
lemma retained_row_energy_average_le (n B d : ℕ) (h q : ℝ)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) :
    (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
      (retainedRowEnergyEnvelope n B d h) H
      ∂retainedGraphMarginal n B d (thinnedDesign (Fin n) q)) ≤
      ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
        if a + b = 0 then 0 else
          (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
            (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
              (retentionP d q * etaOne d h) ^ a * eta d h ^ b := by
  classical
  let _ := bernoulliLaw_probability q hq
  let _ : IsProbabilityMeasure (thinnedDesign (Fin n) q) := by
    exact design_isProbabilityMeasure (thinnedDesign (Fin n) q) q
      (thinnedDesign_assignment q hq) (thinnedDesign_audit q hq)
      (thinnedDesign_independent q hq)
  let C : ℝ := ∑ a ∈ Finset.range (B + 1), ∑ b ∈ Finset.range (B + 1),
    if a + b = 0 then 0 else
      (B.choose a : ℝ) * ((B - a).choose b : ℝ) *
        (min 1 (4 * (a + b : ℕ) / (B : ℝ))) ^ b *
          (retentionP d q * etaOne d h) ^ a * eta d h ^ b
  let _ := sourcePartition_nonempty B d
  have hprob := partitionLaw_probability B d
  rw [retainedGraphMarginal_partition_sum, integral_smul_measure,
    integral_finsetSum_measure (fun _ _ => Integrable.of_finite)]
  have havg : ∀ s : SourcePartition B d,
      (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
        (retainedRowEnergyEnvelope n B d h) H
        ∂(thinnedDesign (Fin n) q).map (fun ω =>
          (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1)) ≤ C := by
    intro s
    rw [integral_map (by fun_prop) (by fun_prop)]
    apply le_trans _ (fixed_partition_row_energy_average_le n B d h q hfit hq s)
    apply integral_mono
    · first | fun_prop | exact Integrable.of_finite
    · first | fun_prop | exact Integrable.of_finite
    intro ω
    by_cases hg : (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1
    · simp only [Set.indicator, Set.mem_setOf_eq, hg, if_true, le_refl]
    · simpa only [Set.indicator, Set.mem_setOf_eq, hg, if_false] using
        retainedRowEnergyEnvelope_nonneg n B d h _
  calc
    _ ≤ ((Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹).toReal *
        ∑ _s : SourcePartition B d, C :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun s _ => havg s)) (by positivity)
    _ = C := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.toReal_inv,
        ENNReal.toReal_natCast]
      have hn : (Fintype.card (SourcePartition B d) : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      field_simp

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
