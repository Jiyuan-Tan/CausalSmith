module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockStatistics
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.DesignBridge
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockSupport

/-!
# Independent revealed source associations
-/

public section

noncomputable section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Selecting distinct coordinates of independent Bernoulli marks preserves their product law.  [For the stated data and conditions](hyp:I,J,e,he,q,hq), [the stated conclusion holds](goal). -/
-- @node: bernoulli_select_coordinates
lemma bernoulli_select_coordinates {I J : Type*} [Fintype I] [Fintype J]
    (e : J → I) (he : Function.Injective e)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (Measure.pi (fun _ : I => bernoulliLaw q)).map (fun w j => w (e j)) =
      Measure.pi (fun _ : J => bernoulliLaw q) := by
  let _ := bernoulliLaw_probability q hq
  have hind := (ProbabilityTheory.iIndepFun_pi
    (μ := fun _ : I => bernoulliLaw q) (X := fun _ => id)
    (fun _ => aemeasurable_id)).precomp he
  have hm (j : J) : (Measure.pi (fun _ : I => bernoulliLaw q)).map
      (fun w => w (e j)) = bernoulliLaw q :=
    (measurePreserving_eval (fun _ : I => bernoulliLaw q) (e j)).map_eq
  simpa only [Function.comp_def, hm] using
    hind.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)

/-- Regroup a rectangular collection of independent marks into independent rows.  [For the stated data and conditions](hyp:I,J,q,hq), [the stated conclusion holds](goal). -/
-- @node: bernoulli_curry_coordinates
lemma bernoulli_curry_coordinates {I J : Type*} [Fintype I] [Fintype J]
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (Measure.pi (fun _ : I × J => bernoulliLaw q)).map (fun w i j => w (i,j)) =
      Measure.pi (fun _ : I => Measure.pi (fun _ : J => bernoulliLaw q)) := by
  let _ := bernoulliLaw_probability q hq
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
  have hp : (fun v : I × J → Bool => fun i j => v (i,j)) ⁻¹' {w} =
      {fun ij : I × J => w ij.1 ij.2} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      funext ij
      exact congrFun (congrFun h ij.1) ij.2
    · intro h
      subst v
      rfl
  rw [hp, Measure.pi_singleton, Measure.pi_singleton]
  simp_rw [Measure.pi_singleton]
  exact Fintype.prod_prod_type _

/-- The OR of d independent audit marks has success probability one minus their joint failure.  [For the stated data and conditions](hyp:d,q,hq), [the stated conclusion holds](goal). -/
-- @node: bernoulli_any_coordinate
lemma bernoulli_any_coordinate (d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1) :
    (Measure.pi (fun _ : Fin d => bernoulliLaw q)).map
      (fun w => decide (∃ k, w k = true)) = bernoulliLaw (retentionP d q) := by
  let _ := bernoulliLaw_probability q hq
  let _ := bernoulliLaw_probability (retentionP d q) (retentionP_mem_Icc d q hq)
  let μ := (Measure.pi (fun _ : Fin d => bernoulliLaw q)).map
    (fun w => decide (∃ k, w k = true))
  let _ : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hf : μ {false} = ENNReal.ofReal ((1 - q) ^ d) := by
    dsimp [μ]
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    have hp : (fun w : Fin d → Bool => decide (∃ k, w k = true)) ⁻¹' {false} =
        {fun _ => false} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_false_iff_not,
        not_exists]
      constructor
      · intro h
        funext k
        cases hk : w k
        · rfl
        · exact False.elim (h k hk)
      · intro h k
        simp [h]
    rw [hp, Measure.pi_singleton]
    simp only [bernoulliLaw, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply' _ (measurableSet_singleton _),
      smul_eq_mul]
    simp [← ENNReal.ofReal_pow, sub_nonneg.mpr hq.2]
  apply Measure.ext_of_singleton
  intro b
  cases b
  · change μ {false} = _
    rw [hf]
    simp [bernoulliLaw, retentionP]
  · have hc : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
    change μ {true} = _
    rw [← hc, measure_compl (measurableSet_singleton _) (measure_ne_top _ _), measure_univ, hf]
    have hp : 0 ≤ (1 - q) ^ d := pow_nonneg (sub_nonneg.mpr hq.2) _
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 hp]
    simp [bernoulliLaw, retentionP]

/-- For a fixed source partition, its true audit marks can be enumerated in disjoint rows;
the full retained graph reveals a source exactly when one mark in its row is true.  [For the stated data and conditions](hyp:n,B,d,hfit,s), [the stated conclusion holds](goal). -/
-- @node: block_audit_rows
lemma block_audit_rows (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) :
    ∃ e : Fin (B * d) × Fin d → OffDiag (Fin n), Function.Injective e ∧
      ∀ ω : Assign (Fin n) × Audit (Fin n),
        sourceReveals n B d (recordOf
          (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1 =
          fun j => decide (∃ k : Fin d, ω.2 (e (j,k)) = true) := by
  let v : Fin (B * d) → Fin n := fun j => ⟨j.val, by omega⟩
  let r (j : Fin (B * d)) : Fin d ≃
      {i : Fin n // i ∈ recipientBlock n B d (s.1 j)} :=
    Fintype.equivOfCardEq (by simp [recipientBlock_card n B d hfit])
  have hr (j : Fin (B * d)) (k : Fin d) :
      blockEdge n B d s (v j) (r j k).val :=
    (blockEdge_source_iff n B d s (v j) (r j k).val j.isLt).mpr (r j k).property
  let e : Fin (B * d) × Fin d → OffDiag (Fin n) :=
    fun jk => ⟨(v jk.1, (r jk.1 jk.2).val), (hr jk.1 jk.2).2⟩
  refine ⟨e, ?_, ?_⟩
  · intro a b hab
    have hj : a.1 = b.1 := Fin.ext (congrArg (fun edge => edge.val.1.val) hab)
    apply Prod.ext hj
    have hi := congrArg (fun edge => edge.val.2) hab
    dsimp [e] at hi
    rw [← hj] at hi
    exact (r a.1).injective (Subtype.ext hi)
  · intro ω
    funext j
    unfold sourceReveals
    apply Bool.decide_congr
    constructor
    · rintro ⟨v', hv', i, hvi, he⟩
      have hv : v' = v j := Fin.ext hv'
      subst v'
      have hedge : blockEdge n B d s (v j) i ∧ ω.2 ⟨(v j,i), hvi⟩ = true := by
        simpa only [recordOf, blockSchedule, Bool.and_eq_true, decide_eq_true_eq] using he
      have hi := (blockEdge_source_iff n B d s (v j) i j.isLt).mp hedge.1
      obtain ⟨k, hk⟩ := (r j).surjective ⟨i, hi⟩
      refine ⟨k, ?_⟩
      have heq : e (j,k) = ⟨(v j,i), hvi⟩ := by
        apply Subtype.ext
        exact Prod.ext rfl (congrArg Subtype.val hk)
      rw [heq]
      exact hedge.2
    · rintro ⟨k, hk⟩
      refine ⟨v j, rfl, (r j k).val, (hr j k).2, ?_⟩
      change (decide (blockEdge n B d s (v j) (r j k).val) && ω.2 (e (j,k))) = true
      simp [hr, hk]

/-- Conditional on any true partition, the vector of labeled source reveals has the same
independent Bernoulli law.  [For the stated data and conditions](hyp:n,B,d,q,hfit,hq,s), [the stated conclusion holds](goal). -/
-- @node: block_reveal_fixed_partition
lemma block_reveal_fixed_partition (n B d : ℕ) (q : ℝ)
    (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d) :
    (thinnedDesign (Fin n) q).map (fun ω => sourceReveals n B d
      (recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1) =
      Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)) := by
  let _ := bernoulliLaw_probability q hq
  let _ : IsProbabilityMeasure ((Measure.pi (fun _ : Fin d => bernoulliLaw q)).map
      (fun w => decide (∃ k : Fin d, w k = true))) :=
    Measure.isProbabilityMeasure_map (by fun_prop)
  obtain ⟨e, he, hrows⟩ := block_audit_rows n B d hfit s
  have hselect := bernoulli_select_coordinates e he q hq
  have hcurry := bernoulli_curry_coordinates (I := Fin (B * d)) (J := Fin d) q hq
  have hany := bernoulli_any_coordinate d q hq
  have hmap : (auditLaw (Fin n) q).map
      (fun w j => decide (∃ k : Fin d, w (e (j,k)) = true)) =
        Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)) := by
    have hr := congrArg (fun μ : Measure (Fin (B * d) → Fin d → Bool) =>
      μ.map (fun rows j => decide (∃ k : Fin d, rows j k = true))) hcurry
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at hr
    have hor := Measure.pi_map_pi (μ := fun _ : Fin (B * d) =>
      Measure.pi (fun _ : Fin d => bernoulliLaw q))
      (f := fun _ => fun w => decide (∃ k : Fin d, w k = true))
      (fun _ => (by fun_prop))
    rw [hor, hany] at hr
    have hs := congrArg (fun μ : Measure (Fin (B * d) × Fin d → Bool) =>
      μ.map (fun w j => decide (∃ k : Fin d, w (j,k) = true))) hselect
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at hs
    exact hs.trans hr
  have hm : (thinnedDesign (Fin n) q).map Prod.snd = auditLaw (Fin n) q :=
    (thinnedDesign_audit q hq).2.2
  have ht := congrArg (fun μ : Measure (Audit (Fin n)) => μ.map
    (fun w j => decide (∃ k : Fin d, w (e (j,k)) = true))) hm
  rw [Measure.map_map (by fun_prop) (by fun_prop), hmap] at ht
  simpa only [hrows, Function.comp_def] using ht

/-- A rectangular enumeration provides an ordered source partition for every block layout.  [For the stated data and conditions](hyp:B,d), [the stated conclusion holds](goal). -/
-- @node: sourcePartition_nonempty
lemma sourcePartition_nonempty (B d : ℕ) : Nonempty (SourcePartition B d) := by
  let e : Fin (B * d) ≃ Fin B × Fin d := finProdFinEquiv.symm
  refine ⟨⟨fun j => (e j).1, ?_⟩⟩
  intro ℓ
  have hf : Finset.univ.filter (fun j : Fin (B * d) => (e j).1 = ℓ) =
      Finset.univ.image (fun k : Fin d => e.symm (ℓ,k)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      refine ⟨(e j).2, ?_⟩
      rw [← hj, Prod.mk.eta, e.symm_apply_apply]
    · rintro ⟨k, rfl⟩
      simp
  rw [hf, Finset.card_image_of_injective]
  · simp
  · intro k k' h
    exact congrArg Prod.snd (e.symm.injective h)

/-- The uniform prior on ordered source partitions has total mass one.  [For the stated data and conditions](hyp:B,d), [the stated conclusion holds](goal). -/
-- @node: partitionLaw_probability
lemma partitionLaw_probability (B d : ℕ) : IsProbabilityMeasure (partitionLaw B d) := by
  let _ := sourcePartition_nonempty B d
  refine ⟨?_⟩
  simp only [partitionLaw, Measure.smul_apply, Measure.finsetSum_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const, Finset.card_univ,
    smul_eq_mul, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero) (by simp)

/-- Source associations are revealed independently with the stated retention probability.  [For the stated data and conditions](hyp:n,B,d,q,D,hB,hd,hfit,hq,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: block_reveal_law
lemma block_reveal_law (n B d : ℕ) (q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    (retainedGraphMarginal n B d D).map (sourceReveals n B d) =
      Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q)) := by
  rw [design_eq_thinnedDesign D q ha hw hi]
  let _ := partitionLaw_probability B d
  rw [retainedGraphMarginal, Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.ext
  intro E hE
  rw [Measure.map_apply (by fun_prop) hE, graphAssignMarginal,
    Measure.bind_apply (hE.preimage (by fun_prop)) (by fun_prop)]
  have hfixed (s : SourcePartition B d) :
      ((thinnedDesign (Fin n) q).map (fun ω =>
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)))
        ((sourceReveals n B d ∘ Prod.fst) ⁻¹' E) =
          (Measure.pi (fun _ : Fin (B * d) => bernoulliLaw (retentionP d q))) E := by
    rw [← Measure.map_apply (by fun_prop) hE,
      Measure.map_map (by fun_prop) (by fun_prop)]
    exact congrArg (fun μ => μ E) (block_reveal_fixed_partition n B d q hfit hq s)
  simp_rw [hfixed]
  rw [lintegral_const, measure_univ, mul_one]

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
