module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-! Joint evaluation supplies a countable separating family for the public schedule space. -/
public section

open Set MeasureTheory
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- A measurable product event depends on countably many measurable first-coordinate sets. [Under the stated conditions](hyp:hB). [This is the stated conclusion](goal). -/
-- @node: schedule_product_countable_sections
lemma schedule_product_countable_sections {S D : Type*} [MeasurableSpace S]
    [MeasurableSpace D] (B : Set (S × D)) (hB : MeasurableSet B) :
    ∃ C : Set (Set S), C.Countable ∧ (∀ c ∈ C, MeasurableSet c) ∧
      ∀ s t, (∀ c ∈ C, s ∈ c ↔ t ∈ c) → ∀ a, (s, a) ∈ B ↔ (t, a) ∈ B := by
  rw [← generateFrom_prod] at hB
  induction B, hB using MeasurableSpace.generateFrom_induction with
  | hC B hB hmeas =>
    obtain ⟨c, hc, d, hd, rfl⟩ := hB
    refine ⟨{c}, countable_singleton c, ?_, ?_⟩
    · intro b hb
      simpa only [mem_singleton_iff.mp hb, mem_ofPred_eq] using hc
    · intro s t h a
      exact and_congr (h c (mem_singleton c)) Iff.rfl
  | empty =>
    exact ⟨∅, countable_empty, by simp, by simp⟩
  | compl B hB ih =>
    obtain ⟨C, hC, hm, hs⟩ := ih
    exact ⟨C, hC, hm, fun s t h a => not_congr (hs s t h a)⟩
  | iUnion B hB ih =>
    choose C hC hm hs using ih
    refine ⟨⋃ n, C n, countable_iUnion hC, ?_, ?_⟩
    · intro c hc
      obtain ⟨n, hn⟩ := mem_iUnion.mp hc
      exact hm n c hn
    · intro s t h a
      simp only [mem_iUnion]
      exact exists_congr fun n =>
        hs n s t (fun c hc => h c (mem_iUnion.mpr ⟨n, hc⟩)) a

/-- Jointly measurable, extensional evaluation supplies countable separation of schedules. [This is the stated conclusion](goal). -/
-- @node: pathSpace_countablySeparated
lemma pathSpace_countablySeparated {S : Type*} [MeasurableSpace S] (E : PathSpace S) :
    MeasurableSpace.CountablySeparated S := by
  classical
  have hq (q : ℚ) : MeasurableSet {p : S × Dose | E.eval p.1 p.2 < (q : ℝ)} :=
    measurableSet_lt E.measurable_eval measurable_const
  choose C hC hm hs using fun q : ℚ =>
    schedule_product_countable_sections _ (hq q)
  refine ⟨⟨⋃ q, C q, countable_iUnion hC, ?_, ?_⟩⟩
  · intro c hc
    obtain ⟨q, hq⟩ := mem_iUnion.mp hc
    exact hm q c hq
  · intro s _ t _ h
    apply E.eval_injective
    funext a
    have he (q : ℚ) : E.eval s a < (q : ℝ) ↔ E.eval t a < (q : ℝ) :=
      hs q s t (fun c hc => h c (mem_iUnion.mpr ⟨q, hc⟩)) a
    apply le_antisymm
    · by_contra hn
      obtain ⟨q, htq, hqs⟩ := exists_rat_btwn (lt_of_not_ge hn)
      exact (not_lt_of_ge hqs.le) ((he q).mpr htq)
    · by_contra hn
      obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn (lt_of_not_ge hn)
      exact (not_lt_of_ge hqt.le) ((he q).mp hsq)

end CausalSmith.Stat.NoisydoseWeakdesignTransition
