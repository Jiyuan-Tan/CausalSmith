module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockReveal

/-!
# Likelihood of a complete detailed retained graph

Independent audit marks give a product likelihood on every labeled edge. For
compatible graphs this likelihood depends only on the true and retained edge
counts, including at audit probabilities zero and one.
-/

public section

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- A retained coordinate is Bernoulli on a true edge and identically false on a nonedge.  [For the stated data and conditions](hyp:q,hq,e,b), [the stated conclusion holds](goal). -/
-- @node: retained_coordinate_mass
lemma retained_coordinate_mass (q : ℝ) (hq : q ∈ Set.Icc 0 1) (e b : Bool) :
    ((bernoulliLaw q).map (fun w => e && w)) {b} =
      if e then (if b then ENNReal.ofReal q else ENNReal.ofReal (1 - q))
      else (if b then 0 else 1) := by
  let := bernoulliLaw_probability q hq
  cases e
  · have hu : ({false, true} : Set Bool) = Set.univ := by
      ext b; cases b <;> simp
    cases b
    · simp only [Bool.false_and, Measure.map_const, Bool.univ_eq, Measure.smul_apply,
        MeasurableSpace.measurableSet_top, Measure.dirac_apply', Set.mem_singleton_iff,
        Set.indicator_of_mem, Pi.one_apply, smul_eq_mul, mul_one, Bool.false_eq_true,
        ↓reduceIte]
      rw [hu, measure_univ]
    · simp [Measure.map_const]
  · cases b <;> simp [bernoulliLaw]

/-- The probability of the full retained indicator vector is the product over all labeled
coordinates, with no summation or deletion of retained-edge subsets.  [For the stated data and conditions](hyp:I,q,hq,E,H), [the stated conclusion holds](goal). -/
-- @node: detailed_thinning_mass_product
lemma detailed_thinning_mass_product {I : Type*} [Fintype I]
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (E H : I → Bool) :
    ((Measure.pi (fun _ : I => bernoulliLaw q)).map
      (fun w i => E i && w i)) {H} =
      ∏ i, if E i then (if H i then ENNReal.ofReal q else ENNReal.ofReal (1 - q))
        else (if H i then 0 else 1) := by
  let := bernoulliLaw_probability q hq
  let _ (i : I) : IsProbabilityMeasure ((bernoulliLaw q).map (fun w => E i && w)) :=
    Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable
  rw [Measure.pi_map_pi (fun _ => (measurable_of_finite _).aemeasurable), Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun i _ => retained_coordinate_mass q hq (E i) (H i))

/-- A graph containing an arrow absent from the true graph has zero probability.  [For the stated data and conditions](hyp:I,q,hq,E,H,hi), [the stated conclusion holds](goal). -/
-- @node: detailed_thinning_mass_incompatible
lemma detailed_thinning_mass_incompatible {I : Type*} [Fintype I]
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (E H : I → Bool)
    (hi : ∃ i, H i = true ∧ E i = false) :
    ((Measure.pi (fun _ : I => bernoulliLaw q)).map
      (fun w i => E i && w i)) {H} = 0 := by
  rw [detailed_thinning_mass_product q hq E H]
  obtain ⟨i, hH, hE⟩ := hi
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hH, hE]

/-- For a compatible detailed graph the likelihood is q to the retained-edge count times
one minus q to the number of unretained true edges. This formula includes both endpoints.  [For the stated data and conditions](hyp:I,q,hq,E,H,hc), [the stated conclusion holds](goal). -/
-- @node: detailed_thinning_mass_compatible
lemma detailed_thinning_mass_compatible {I : Type*} [Fintype I]
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (E H : I → Bool)
    (hc : ∀ i, H i = true → E i = true) :
    ((Measure.pi (fun _ : I => bernoulliLaw q)).map
      (fun w i => E i && w i)) {H} =
      ENNReal.ofReal q ^ (Finset.univ.filter (fun i => H i = true)).card *
      ENNReal.ofReal (1 - q) ^
        ((Finset.univ.filter (fun i => E i = true)).card -
          (Finset.univ.filter (fun i => H i = true)).card) := by
  classical
  rw [detailed_thinning_mass_product q hq E H]
  have hp : (∏ i, if E i then
      (if H i then ENNReal.ofReal q else ENNReal.ofReal (1 - q))
      else (if H i then 0 else 1)) =
      ∏ i, if H i = true then ENNReal.ofReal q
        else if E i = true then ENNReal.ofReal (1 - q) else 1 := by
    apply Finset.prod_congr rfl
    intro i _
    cases he : E i <;> cases hh : H i <;> simp_all
  rw [hp, Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, one_pow, mul_one]
  have hcard : (Finset.univ.filter (fun i => ¬ H i = true)).filter
      (fun i => E i = true) =
      (Finset.univ.filter (fun i => E i = true)).filter (fun i => ¬ H i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  rw [hcard]
  have heq : (Finset.univ.filter (fun i => E i = true)).filter
      (fun i => H i = true) = Finset.univ.filter (fun i => H i = true) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hh => ⟨hc i hh, hh⟩⟩
  have hsum := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun i => E i = true)) (fun i => H i = true)
  rw [heq] at hsum
  rw [show ((Finset.univ.filter (fun i => E i = true)).filter
    (fun i => ¬ H i = true)).card =
      (Finset.univ.filter (fun i => E i = true)).card -
        (Finset.univ.filter (fun i => H i = true)).card by omega]

/-- Every source partition has exactly B*d*d true arrows, counted with their full labels.  [For the stated data and conditions](hyp:n,B,d,hfit,s), [the stated conclusion holds](goal). -/
-- @node: blockEdge_total_card
lemma blockEdge_total_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) :
    (Finset.univ.filter (fun e : OffDiag (Fin n) =>
      blockEdge n B d s e.val.1 e.val.2)).card = B * d * d := by
  classical
  have he : (Finset.univ.filter (fun e : OffDiag (Fin n) =>
      blockEdge n B d s e.val.1 e.val.2)).card =
      (Finset.univ.filter (fun ji : Fin n × Fin n =>
        blockEdge n B d s ji.1 ji.2)).card := by
    apply Finset.card_bij (fun e _ => e.val)
    · intro e he
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using he
    · intro e he f hf hef
      exact Subtype.ext hef
    · intro ji hji
      have hj : blockEdge n B d s ji.1 ji.2 := (Finset.mem_filter.mp hji).2
      refine ⟨⟨ji, hj.2⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
  rw [he, Finset.card_filter, Fintype.sum_prod_type]
  simp_rw [← Finset.card_filter, blockEdge_outgoing_card n B d hfit s]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero,
    block_source_card n B d hfit, Nat.cast_id]

/-- Conditional on a true partition, the complete retained-graph probability has the common
likelihood q^|H| (1-q)^(B*d*d-|H|) for every compatible completion.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,s,H,hc), [the stated conclusion holds](goal). -/
-- @node: block_detailed_graph_mass
lemma block_detailed_graph_mass (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hc : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2) :
    ((auditLaw (Fin n) q).map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} =
      ENNReal.ofReal q ^ (Finset.univ.filter (fun e => H e = true)).card *
      ENNReal.ofReal (1 - q) ^
        (B * d * d - (Finset.univ.filter (fun e => H e = true)).card) := by
  rw [auditLaw, detailed_thinning_mass_compatible q hq
    (fun e => decide (blockEdge n B d s e.val.1 e.val.2)) H
    (fun e he => by simpa using hc e he)]
  simp only [decide_eq_true_eq, blockEdge_total_card n B d hfit s]

/-- Detailed retained subsets have the same likelihood under any two compatible source
partitions, even at the audit endpoints.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,s,t,H,hs,ht), [the stated conclusion holds](goal). -/
-- @node: block_detailed_graph_mass_eq
lemma block_detailed_graph_mass_eq (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (s t : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)
    (ht : ∀ e, H e = true → blockEdge n B d t e.val.1 e.val.2) :
    ((auditLaw (Fin n) q).map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} =
    ((auditLaw (Fin n) q).map (fun w e =>
      decide (blockEdge n B d t e.val.1 e.val.2) && w e)) {H} := by
  rw [block_detailed_graph_mass n B d hfit q hq s H hs,
    block_detailed_graph_mass n B d hfit q hq t H ht]

/-- The full fixed-partition graph likelihood vanishes off compatible completions and is
constant on them. Compatibility records every observed arrow with both endpoint labels.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,s,H), [the stated conclusion holds](goal). -/
-- @node: block_detailed_graph_mass_ite
lemma block_detailed_graph_mass_ite (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool) :
    ((auditLaw (Fin n) q).map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} =
      if ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2 then
        ENNReal.ofReal q ^ (Finset.univ.filter (fun e => H e = true)).card *
        ENNReal.ofReal (1 - q) ^
          (B * d * d - (Finset.univ.filter (fun e => H e = true)).card)
      else 0 := by
  classical
  by_cases hc : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2
  · rw [if_pos hc]
    exact block_detailed_graph_mass n B d hfit q hq s H hc
  · rw [if_neg hc, auditLaw]
    apply detailed_thinning_mass_incompatible q hq
    push Not at hc
    obtain ⟨e, he, hn⟩ := hc
    exact ⟨e, he, by simp [hn]⟩

/-- Integrating any function over the uniform partition prior is its finite arithmetic mean.  [For the stated data and conditions](hyp:B,d,f), [the stated conclusion holds](goal). -/
-- @node: partitionLaw_lintegral
lemma partitionLaw_lintegral (B d : ℕ) (f : SourcePartition B d → ℝ≥0∞) :
    (∫⁻ s, f s ∂partitionLaw B d) =
      (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ * ∑ s, f s := by
  rw [partitionLaw, lintegral_smul_measure, lintegral_finsetSum_measure]
  simp only [lintegral_dirac, smul_eq_mul]

/-- Under the actual audit law, averaging the full detailed graph likelihood over the
uniform source partitions gives the compatible-completion count times its common likelihood.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,H), [the stated conclusion holds](goal). -/
-- @node: block_retained_graph_mass
lemma block_retained_graph_mass (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (H : OffDiag (Fin n) → Bool) :
    retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} =
      (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ *
      ((Finset.univ.filter (fun s : SourcePartition B d =>
        ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2)).card : ℝ≥0∞) *
      (ENNReal.ofReal q ^ (Finset.univ.filter (fun e => H e = true)).card *
        ENNReal.ofReal (1 - q) ^
          (B * d * d - (Finset.univ.filter (fun e => H e = true)).card)) := by
  classical
  rw [retainedGraphMarginal, Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    graphAssignMarginal, Measure.bind_apply
      ((measurableSet_singleton H).preimage (by fun_prop)) (by fun_prop)]
  have hfixed (s : SourcePartition B d) :
      ((thinnedDesign (Fin n) q).map (fun ω =>
        ((recordOf (blockSchedule n B d true 0 (s, fun _ => 0)) ω).1, ω.1)))
        (Prod.fst ⁻¹' {H}) =
      ((auditLaw (Fin n) q).map (fun w e =>
        decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} := by
    rw [← Measure.map_apply (by fun_prop) (measurableSet_singleton H),
      Measure.map_map (by fun_prop) (by fun_prop)]
    have hm := congrArg (fun μ : Measure (Audit (Fin n)) => μ.map (fun w e =>
      decide (blockEdge n B d s e.val.1 e.val.2) && w e))
      (thinnedDesign_audit (V := Fin n) q hq).2.2
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at hm
    exact congrArg (fun μ => μ {H}) hm
  simp_rw [hfixed, block_detailed_graph_mass_ite n B d hfit q hq]
  rw [partitionLaw_lintegral, Finset.sum_ite]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_zero, add_zero, mul_assoc]

/-- Each labeled partition has the same atom mass in the construction prior.  [For the stated data and conditions](hyp:B,d,s), [the stated conclusion holds](goal). -/
-- @node: partitionLaw_singleton
lemma partitionLaw_singleton (B d : ℕ) (s : SourcePartition B d) :
    partitionLaw B d {s} = (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ := by
  classical
  simp [partitionLaw, Measure.finsetSum_apply, Measure.dirac_apply' _
    (measurableSet_singleton s)]

/-- The joint atom for a fixed labeled partition and detailed retained graph is the prior
partition mass times its exact full graph likelihood.  [For the stated data and conditions](hyp:n,B,d,q,hq,s,H), [the stated conclusion holds](goal). -/
-- @node: block_partition_graph_joint_mass
lemma block_partition_graph_joint_mass (n B d : ℕ) (q : ℝ) (hq : q ∈ Set.Icc 0 1)
    (s : SourcePartition B d) (H : OffDiag (Fin n) → Bool) :
    (((partitionLaw B d).prod (auditLaw (Fin n) q)).map (fun x =>
      (x.1, fun e => decide (blockEdge n B d x.1 e.val.1 e.val.2) && x.2 e))) {(s, H)} =
      (Fintype.card (SourcePartition B d) : ℝ≥0∞)⁻¹ *
      ((auditLaw (Fin n) q).map (fun w e =>
        decide (blockEdge n B d s e.val.1 e.val.2) && w e)) {H} := by
  classical
  let := bernoulliLaw_probability q hq
  let _ : IsProbabilityMeasure (auditLaw (Fin n) q) := by unfold auditLaw; infer_instance
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have he : (fun x : SourcePartition B d × Audit (Fin n) =>
      (x.1, fun e => decide (blockEdge n B d x.1 e.val.1 e.val.2) && x.2 e)) ⁻¹'
      {(s,H)} = {s} ×ˢ ((fun w e =>
        decide (blockEdge n B d s e.val.1 e.val.2) && w e) ⁻¹' {H}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Set.mem_prod]
    constructor
    · rintro ⟨hx, hh⟩
      exact ⟨hx, by simpa only [hx] using hh⟩
    · rintro ⟨hx, hh⟩
      exact ⟨hx, by simpa only [hx] using hh⟩
  rw [he, Measure.prod_prod, partitionLaw_singleton,
    Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]

/-- At every positive-probability detailed graph, Bayes' rule assigns each compatible
labeled partition exactly the reciprocal of the number of compatible completions.  [For the stated data and conditions](hyp:n,B,d,hfit,q,hq,s,H,hpos,hs), [the stated conclusion holds](goal). -/
-- @node: block_partition_posterior_atom
lemma block_partition_posterior_atom (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (q : ℝ) (hq : q ∈ Set.Icc 0 1) (s : SourcePartition B d)
    (H : OffDiag (Fin n) → Bool)
    (hpos : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} ≠ 0)
    (hs : ∀ e, H e = true → blockEdge n B d s e.val.1 e.val.2) :
    ((((partitionLaw B d).prod (auditLaw (Fin n) q)).map (fun x =>
      (x.1, fun e => decide (blockEdge n B d x.1 e.val.1 e.val.2) && x.2 e))) {(s, H)}) /
      retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} =
      ((Finset.univ.filter (fun t : SourcePartition B d =>
        ∀ e, H e = true → blockEdge n B d t e.val.1 e.val.2)).card : ℝ≥0∞)⁻¹ := by
  classical
  let N : ℝ≥0∞ := Fintype.card (SourcePartition B d)
  let C : ℝ≥0∞ := (Finset.univ.filter (fun t : SourcePartition B d =>
    ∀ e, H e = true → blockEdge n B d t e.val.1 e.val.2)).card
  let c : ℝ≥0∞ := ENNReal.ofReal q ^ (Finset.univ.filter (fun e => H e = true)).card *
    ENNReal.ofReal (1 - q) ^
      (B * d * d - (Finset.univ.filter (fun e => H e = true)).card)
  have hg : retainedGraphMarginal n B d (thinnedDesign (Fin n) q) {H} = N⁻¹ * C * c :=
    block_retained_graph_mass n B d hfit q hq H
  have hc : c ≠ 0 := by
    intro hc
    apply hpos
    rw [hg, hc, mul_zero]
  let := sourcePartition_nonempty B d
  have hN : N ≠ 0 := by
    dsimp [N]
    exact_mod_cast Fintype.card_ne_zero
  have hf : N⁻¹ * c ≠ 0 := mul_ne_zero (by simp [N]) hc
  have hft : N⁻¹ * c ≠ ⊤ := by
    have hn : N⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hN
    have hct : c ≠ ⊤ := by dsimp [c]; finiteness
    exact ENNReal.mul_ne_top hn hct
  rw [block_partition_graph_joint_mass n B d q hq,
    block_detailed_graph_mass n B d hfit q hq s H hs, hg]
  change (N⁻¹ * c) / (N⁻¹ * C * c) = C⁻¹
  rw [show N⁻¹ * C * c = (N⁻¹ * c) * C by ac_rfl]
  simpa only [mul_one, one_div] using ENNReal.mul_div_mul_left 1 C hf hft

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
