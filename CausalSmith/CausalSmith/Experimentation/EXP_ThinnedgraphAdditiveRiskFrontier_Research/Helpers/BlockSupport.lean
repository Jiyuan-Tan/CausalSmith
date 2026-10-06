module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.BlockStatistics

/-!
# Support and causal target of the block prior
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- Recipient blocks contain exactly d labels when the bipartite layout fits.  [For the stated data and conditions](hyp:n,B,d,hfit,ℓ), [the stated conclusion holds](goal). -/
-- @node: recipientBlock_card
lemma recipientBlock_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) (ℓ : Fin B) :
    (recipientBlock n B d ℓ).card = d := by
  have hlmul : (ℓ.val + 1) * d = ℓ.val * d + d := by simp [Nat.add_mul]
  let f : Fin d → Fin n := fun k => ⟨B * d + ℓ.val * d + k.val, by
    have hl := ℓ.isLt
    have hk := k.isLt
    have hb : (ℓ.val + 1) * d ≤ B * d := Nat.mul_le_mul_right d (by omega)
    omega⟩
  have he : recipientBlock n B d ℓ = Finset.univ.image f := by
    ext i
    simp only [recipientBlock, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hi
      refine ⟨⟨i.val - (B * d + ℓ.val * d), by omega⟩, ?_⟩
      apply Fin.ext
      dsimp [f]
      omega
    · rintro ⟨k, _, rfl⟩
      dsimp [f]
      have hk := k.isLt
      constructor <;> omega
  rw [he, Finset.card_image_of_injective]
  · simp
  · intro k k' hk
    apply Fin.ext
    have hv := congrArg Fin.val hk
    dsimp [f] at hv
    omega

/-- The source and recipient labels in a block edge are disjoint.  [For the stated data and conditions](hyp:n,B,d,s,j,i,hj), [the stated conclusion holds](goal). -/
-- @node: blockEdge_source_iff
lemma blockEdge_source_iff (n B d : ℕ) (s : SourcePartition B d)
    (j i : Fin n) (hj : j.val < B * d) :
    blockEdge n B d s j i ↔ i ∈ recipientBlock n B d (s.1 ⟨j.val, hj⟩) := by
  constructor
  · rintro ⟨⟨_, ℓ, he, hi⟩, _⟩
    simpa only [he] using hi
  · intro hi
    refine ⟨⟨hj, _, rfl, hi⟩, ?_⟩
    have hb : B * d ≤ i.val := (Finset.mem_filter.mp hi).2.1.trans' (by omega)
    intro he
    subst i
    omega

/-- A source has exactly d outgoing edges; other labels have none.  [For the stated data and conditions](hyp:n,B,d,hfit,s,j), [the stated conclusion holds](goal). -/
-- @node: blockEdge_outgoing_card
lemma blockEdge_outgoing_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n)
    (s : SourcePartition B d) (j : Fin n) :
    (Finset.univ.filter (fun i => blockEdge n B d s j i)).card =
      if j.val < B * d then d else 0 := by
  by_cases hj : j.val < B * d
  · rw [if_pos hj]
    have he : Finset.univ.filter (fun i => blockEdge n B d s j i) =
        recipientBlock n B d (s.1 ⟨j.val, hj⟩) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        blockEdge_source_iff n B d s j i hj]
    rw [he]
    exact recipientBlock_card n B d hfit _
  · rw [if_neg hj]
    have he : Finset.univ.filter (fun i => blockEdge n B d s j i) = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro i hi
      exact hj (Finset.mem_filter.mp hi).2.1.choose
    rw [he, Finset.card_empty]

/-- There are B*d source labels in a fitting block layout.  [For the stated data and conditions](hyp:n,B,d,hfit), [the stated conclusion holds](goal). -/
-- @node: block_source_card
lemma block_source_card (n B d : ℕ) (hfit : 2 * (B * d) ≤ n) :
    (Finset.univ.filter (fun j : Fin n => j.val < B * d)).card = B * d := by
  by_cases hm : B * d = 0
  · simp [hm]
  · have hmn : B * d < n := by omega
    have he : Finset.univ.filter (fun j : Fin n => j.val < B * d) =
        Finset.Iio (⟨B * d, hmn⟩ : Fin n) := by
      ext j
      simp [Fin.lt_def]
    rw [he, Fin.card_Iio]

/-- Every recipient in a block has exactly d incoming source labels.  [For the stated data and conditions](hyp:n,B,d,hd,hfit,σ,h,ξ,i,ℓ,hi), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_inNbhd_card
lemma blockSchedule_inNbhd_card (n B d : ℕ) (hd : 1 ≤ d)
    (hfit : 2 * (B * d) ≤ n) (σ : Bool) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) (i : Fin n) (ℓ : Fin B)
    (hi : i ∈ recipientBlock n B d ℓ) :
    (inNbhd (blockSchedule n B d σ h ξ) i).card = d := by
  let f : Fin (B * d) → Fin n := fun j => ⟨j.val, by have hj := j.isLt; omega⟩
  have he : inNbhd (blockSchedule n B d σ h ξ) i =
      (Finset.univ.filter (fun j => ξ.1.1 j = ℓ)).image f := by
    ext j
    change (j ∈ Finset.univ.filter (fun j => blockEdge n B d ξ.1 j i)) ↔ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hj
      obtain ⟨⟨hjm, k, hjk, hik⟩, _⟩ := hj
      have hkl := recipientBlock_unique n B d i k ℓ hik hi
      refine ⟨⟨j.val, hjm⟩, ?_, ?_⟩
      · exact hjk.trans hkl
      · rfl
    · rintro ⟨k, hk, rfl⟩
      apply (blockEdge_source_iff n B d ξ.1 (f k) i k.isLt).mpr
      simpa only [f, hk] using hi
  rw [he, Finset.card_image_of_injective]
  · exact ξ.1.2 ℓ
  · intro j k hjk
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hjk)

/-- Labels outside all recipient blocks have no incoming edges.  [For the stated data and conditions](hyp:n,B,d,σ,h,ξ,i,hi), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_inNbhd_empty
lemma blockSchedule_inNbhd_empty (n B d : ℕ) (σ : Bool) (h : ℝ)
    (ξ : SourcePartition B d × (Fin B → ℝ)) (i : Fin n)
    (hi : ∀ ℓ, i ∉ recipientBlock n B d ℓ) :
    inNbhd (blockSchedule n B d σ h ξ) i = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro j hj
  obtain ⟨⟨_, ℓ, _, hiℓ⟩, _⟩ := (Finset.mem_filter.mp hj).2
  exact hi ℓ hiℓ

/-- Baselines in the support interval give the required coefficient-mass and degree bounds.  [For the stated data and conditions](hyp:n,B,d,σ,h,hd,hfit,hh,ξ,hξ), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_mem_class
lemma blockSchedule_mem_class (n B d : ℕ) (σ : Bool) (h : ℝ)
    (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hh : h ∈ Set.Icc 0 (1 / 4))
    (ξ : SourcePartition B d × (Fin B → ℝ)) (hξ : ∀ ℓ, |ξ.2 ℓ| ≤ 1 / 4) :
    ScheduleClass (blockSchedule n B d σ h ξ) d := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have habs : |signOf σ * h / d| = h / d := by
    rw [abs_div, abs_mul, show |signOf σ| = 1 by cases σ <;> norm_num [signOf],
      abs_of_nonneg hh.1, abs_of_nonneg (Nat.cast_nonneg d), one_mul]
  constructor
  · intro i
    by_cases hi : ∃ ℓ, i ∈ recipientBlock n B d ℓ
    · obtain ⟨ℓ, hi⟩ := hi
      exact (blockSchedule_inNbhd_card n B d hd hfit σ h ξ i ℓ hi).le
    · rw [blockSchedule_inNbhd_empty n B d σ h ξ i (not_exists.mp hi)]
      simp
  · intro j
    have he : (Finset.univ.filter (fun i => j ∈ inNbhd (blockSchedule n B d σ h ξ) i)) =
        Finset.univ.filter (fun i => blockEdge n B d ξ.1 j i) := by
      ext i
      change (i ∈ Finset.univ.filter (fun i => j ∈
        Finset.univ.filter (fun j => blockEdge n B d ξ.1 j i))) ↔ _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [he, blockEdge_outgoing_card n B d hfit]
    split <;> omega
  · intro i
    by_cases hi : ∃ ℓ, i ∈ recipientBlock n B d ℓ
    · obtain ⟨ℓ, hi⟩ := hi
      have ha : (blockSchedule n B d σ h ξ).a i = ξ.2 ℓ - signOf σ * h / 2 := by
        change (∑ k : Fin B, if i ∈ recipientBlock n B d k then
          ξ.2 k - signOf σ * h / 2 else 0) = _
        rw [Finset.sum_eq_single ℓ]
        · simp [hi]
        · intro k _ hk
          rw [if_neg]
          exact fun hik => hk (recipientBlock_unique n B d i k ℓ hik hi)
        · simp
      change |(blockSchedule n B d σ h ξ).a i| + |(0 : ℝ)| +
        (∑ j ∈ inNbhd (blockSchedule n B d σ h ξ) i, |signOf σ * h / d|) ≤ 1
      rw [ha]
      simp only [abs_zero, add_zero, habs, Finset.sum_const, nsmul_eq_mul,
        blockSchedule_inNbhd_card n B d hd hfit σ h ξ i ℓ hi]
      have he : (d : ℝ) * (h / d) = h := by field_simp
      rw [he]
      have hs : |signOf σ * h / 2| = h / 2 := by
        rw [abs_div, abs_mul, show |signOf σ| = 1 by cases σ <;> norm_num [signOf],
          abs_of_nonneg hh.1, abs_of_pos (by norm_num : (0 : ℝ) < 2), one_mul]
      have hb := abs_sub (ξ.2 ℓ) (signOf σ * h / 2)
      rw [hs] at hb
      linarith [hξ ℓ, hh.2]
    · have hn := not_exists.mp hi
      have ha : (blockSchedule n B d σ h ξ).a i = 0 := by
        change (∑ k : Fin B, if i ∈ recipientBlock n B d k then _ else 0) = 0
        simp [hn]
      change |(blockSchedule n B d σ h ξ).a i| + |(0 : ℝ)| +
        (∑ j ∈ inNbhd (blockSchedule n B d σ h ξ) i, |signOf σ * h / d|) ≤ 1
      rw [ha, blockSchedule_inNbhd_empty n B d σ h ξ i hn]
      norm_num

/-- Summing the outgoing degree counts gives the block prior's constant causal target.  [For the stated data and conditions](hyp:n,B,d,σ,h,hd,hfit,ξ), [the stated conclusion holds](goal). -/
-- @node: blockSchedule_tte
lemma blockSchedule_tte (n B d : ℕ) (σ : Bool) (h : ℝ)
    (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n)
    (ξ : SourcePartition B d × (Fin B → ℝ)) :
    tte (blockSchedule n B d σ h ξ) = signOf σ * (B * d : ℕ) * h / n := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  simp only [tte, potentialOutcome, blockSchedule, treatment, ite_true,
    Bool.false_eq_true, ite_false, mul_one, mul_zero, Finset.sum_const_zero,
    add_zero, add_sub_cancel_left, Fintype.card_fin]
  simp only [inNbhd, Finset.sum_filter]
  rw [Finset.sum_comm]
  have hrow (j : Fin n) :
      (∑ i : Fin n, if blockEdge n B d ξ.1 j i then signOf σ * h / d else 0) =
        if j.val < B * d then signOf σ * h else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul,
      blockEdge_outgoing_card n B d hfit]
    split
    · field_simp
    · simp
  simp_rw [hrow]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, block_source_card n B d hfit]
  ring

/-- The compact baseline density gives zero mass outside its declared support.  [the stated conclusion holds](goal). -/
-- @node: cosSqDensity_ae_support
lemma cosSqDensity_ae_support :
    ∀ᵐ w ∂(volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w))),
      |w| ≤ (1 / 4 : ℝ) := by
  have hm : Measurable (fun w => ENNReal.ofReal (cosSqDensity w)) := by
    apply Measurable.ennreal_ofReal
    unfold cosSqDensity
    apply Measurable.ite (measurableSet_le (by fun_prop) measurable_const)
    · fun_prop
    · fun_prop
  apply (ae_withDensity_iff hm).mpr
  filter_upwards [] with w hw
  by_contra h
  exact hw (by rw [cosSqDensity, if_neg h, ENNReal.ofReal_zero])

/-- All coordinates of the independent baseline draw lie in the support interval.  [For the stated data and conditions](hyp:B), [the stated conclusion holds](goal). -/
-- @node: blockBaselineLaw_ae_support
lemma blockBaselineLaw_ae_support (B : ℕ) :
    ∀ᵐ u ∂(blockBaselineLaw B), ∀ ℓ, |u ℓ| ≤ (1 / 4 : ℝ) := by
  unfold blockBaselineLaw
  exact Filter.eventually_all.mpr (fun ℓ =>
    (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin B => volume.withDensity (fun w => ENNReal.ofReal (cosSqDensity w)))
      (i := ℓ)).eventually cosSqDensity_ae_support)

/-- Almost every prior schedule belongs to the model class and has the stated constant signed
target.  [For the stated data and conditions](hyp:n,B,d,σ,h,hB,hd,hfit,hh), [the stated conclusion holds](goal). -/
-- @node: block_support
lemma block_support (n B d : ℕ) (σ : Bool) (h : ℝ)
    (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hh : h ∈ Set.Icc 0 (1 / 4)) :
    ∀ᵐ ξ ∂(blockParamLaw B d), ScheduleClass (blockSchedule n B d σ h ξ) d ∧
      tte (blockSchedule n B d σ h ξ) = signOf σ * (B * d : ℕ) * h / n := by
  have hb : ∀ᵐ ξ ∂(blockParamLaw B d), ∀ ℓ, |ξ.2 ℓ| ≤ (1 / 4 : ℝ) := by
    have : SigmaFinite (blockBaselineLaw B) := by unfold blockBaselineLaw; infer_instance
    exact Measure.quasiMeasurePreserving_snd.ae (blockBaselineLaw_ae_support B)
  filter_upwards [hb] with ξ hξ
  exact ⟨blockSchedule_mem_class n B d σ h hd hfit hh ξ hξ,
    blockSchedule_tte n B d σ h hd hfit ξ⟩

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
