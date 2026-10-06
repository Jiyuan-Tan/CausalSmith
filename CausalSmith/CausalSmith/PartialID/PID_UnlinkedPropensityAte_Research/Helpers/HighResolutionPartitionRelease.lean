module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.KLabelRateLower

/-! Equivalence between measurable finite score partitions and releases. -/

@[expose] public section

open MeasureTheory Set

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- For [the specified mathematical inputs](hyp:ε,K,B,hB,e), [this definition](goal) introduces the corresponding object. -/
def intervalPartitionRelease {ε : ℝ} {K : ℕ}
    (B : Fin K → Set ℝ)
    (hB : IsIntervalPartition ε (1 - ε) K B)
    (e : ScoreSpace ε) : LabelSpace K := by
  have he : (e : ℝ) ∈ ⋃ r, B r := by
    rw [hB.2.2]
    exact e.property
  exact Classical.choose (Set.mem_iUnion.mp he)
/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,B,hB,e), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalPartitionRelease_mem {ε : ℝ} {K : ℕ}
    (B : Fin K → Set ℝ)
    (hB : IsIntervalPartition ε (1 - ε) K B)
    (e : ScoreSpace ε) :
    (e : ℝ) ∈ B (intervalPartitionRelease B hB e) := by
  unfold intervalPartitionRelease
  exact Classical.choose_spec (Set.mem_iUnion.mp (by
    rw [hB.2.2]
    exact e.property))

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,B,hB,e,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalPartitionRelease_eq_iff {ε : ℝ} {K : ℕ}
    (B : Fin K → Set ℝ)
    (hB : IsIntervalPartition ε (1 - ε) K B)
    (e : ScoreSpace ε) (r : LabelSpace K) :
    intervalPartitionRelease B hB e = r ↔ (e : ℝ) ∈ B r := by
  constructor
  · intro h
    simpa [h] using intervalPartitionRelease_mem B hB e
  · intro her
    by_contra hne
    have hdis := hB.2.1 (intervalPartitionRelease B hB e) r hne
    exact Set.disjoint_left.mp hdis
      (intervalPartitionRelease_mem B hB e) her

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,B,hB), this result [establishes the stated mathematical conclusion](goal). -/
lemma intervalPartitionRelease_measurable {ε : ℝ} {K : ℕ}
    (B : Fin K → Set ℝ)
    (hB : IsIntervalPartition ε (1 - ε) K B) :
    Measurable (intervalPartitionRelease B hB) := by
  apply measurable_to_countable'
  intro r
  have hpre : intervalPartitionRelease B hB ⁻¹' {r} =
      (Subtype.val : ScoreSpace ε → ℝ) ⁻¹' B r := by
    ext e
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact intervalPartitionRelease_eq_iff B hB e r
  rw [hpre]
  exact (hB.1 r).preimage measurable_subtype_coe

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,B,hB,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma realScoreCell_intervalPartitionRelease {ε : ℝ} {K : ℕ}
    (B : Fin K → Set ℝ)
    (hB : IsIntervalPartition ε (1 - ε) K B)
    (r : LabelSpace K) :
    realScoreCell (intervalPartitionRelease B hB) r = B r := by
  ext x
  constructor
  · rintro ⟨e, he, rfl⟩
    exact (intervalPartitionRelease_eq_iff B hB e r).mp he
  · intro hx
    have hxUnion : x ∈ ⋃ j, B j := Set.mem_iUnion_of_mem r hx
    have hxIcc : x ∈ Set.Icc ε (1 - ε) := by
      rw [← hB.2.2]
      exact hxUnion
    let e : ScoreSpace ε := ⟨x, hxIcc⟩
    refine ⟨e, ?_, rfl⟩
    exact (intervalPartitionRelease_eq_iff B hB e r).mpr hx

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,K,g,hg), this result [establishes the stated mathematical conclusion](goal). -/
lemma measurableRelease_intervalPartition {ε : ℝ} {K : ℕ}
    (g : ScoreSpace ε → LabelSpace K) (hg : Measurable g) :
    IsIntervalPartition ε (1 - ε) K (realScoreCell g) :=
  realScoreCell_intervalPartition g hg

end
end CausalSmith.PartialID.UnlinkedPropensityAte
