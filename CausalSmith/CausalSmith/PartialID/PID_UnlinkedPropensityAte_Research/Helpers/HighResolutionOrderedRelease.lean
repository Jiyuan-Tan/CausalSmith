module
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionPartitionRelease
public import CausalSmith.PartialID.PID_UnlinkedPropensityAte_Research.Helpers.HighResolutionCost

/-! The measurable ordered release induced by the paired companding cells. -/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace CausalSmith.PartialID.UnlinkedPropensityAte

noncomputable section

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfcont,hfpos,k,hk), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionCompandingCell_partition {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) :
    IsIntervalPartition ε (1 - ε) k
      (pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f)) := by
  let boundary : ℕ → ℝ := fun j =>
    pairedBoundary ε (1 - ε) 2 k j (highResolutionBeta f)
  have hab : ε < 1 - ε := by linarith [hOverlap.2]
  have hmono : ∀ i j, i ≤ j → j ≤ k → boundary i ≤ boundary j := by
    intro i j hij hj
    exact pairedBoundary_mono ε (1 - ε) hab.le 2 k i j hk hij hj
      (highResolutionBeta f)
  have hpart := orderedIntervalCells_partition boundary k hk hmono
  have hzero : boundary 0 = ε :=
    pairedBoundary_zero ε (1 - ε) hab.le 2 k (highResolutionBeta f)
  have hlast : boundary k = 1 - ε :=
    pairedBoundary_last ε (1 - ε) hab 2 k (by norm_num) hk
      (highResolutionBeta f)
      (highResolutionBeta_continuousOn hOverlap f hfcont)
      (highResolutionBeta_pos hOverlap f hfpos)
  rw [hzero, hlast] at hpart
  exact hpart

/-- For [the specified mathematical inputs](hyp:ε,hOverlap,f,hfcont,hfpos,k,hk), [this definition](goal) introduces the corresponding object. -/
def highResolutionOrderedRelease {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) : ScoreSpace ε → LabelSpace k :=
  intervalPartitionRelease
    (pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f))
    (highResolutionCompandingCell_partition hOverlap f hfcont hfpos k hk)

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfcont,hfpos,k,hk), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionOrderedRelease_measurable {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) :
    Measurable (highResolutionOrderedRelease hOverlap f hfcont hfpos k hk) := by
  unfold highResolutionOrderedRelease
  exact intervalPartitionRelease_measurable _ _

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfcont,hfpos,k,hk,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionOrderedRelease_realScoreCell {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) (r : LabelSpace k) :
    realScoreCell
        (highResolutionOrderedRelease hOverlap f hfcont hfpos k hk) r =
      pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f) r := by
  unfold highResolutionOrderedRelease
  exact realScoreCell_intervalPartitionRelease _ _ r

/-- Given [the stated mathematical inputs and assumptions](hyp:ε,hOverlap,f,hfcont,hfpos,k,hk,r), this result [establishes the stated mathematical conclusion](goal). -/
lemma highResolutionOrderedRelease_cell_ordConnected {ε : ℝ}
    (hOverlap : Overlap ε) (f : ScoreSpace ε → ℝ)
    (hfcont : Continuous f) (hfpos : ∀ e, 0 < f e)
    (k : ℕ) (hk : 0 < k) (r : LabelSpace k) :
    (cell (highResolutionOrderedRelease hOverlap f hfcont hfpos k hk) r).OrdConnected := by
  let B := pairedCompandingCell ε (1 - ε) 2 k (highResolutionBeta f)
  let hB := highResolutionCompandingCell_partition hOverlap f hfcont hfpos k hk
  have hBorder : (B r).OrdConnected := by
    dsimp [B, pairedCompandingCell]
    split_ifs
    · exact ordConnected_Icc
    · exact ordConnected_Ico
  rw [ordConnected_iff]
  intro x hx y hy hxy z hz
  change highResolutionOrderedRelease hOverlap f hfcont hfpos k hk z = r
  have hxB : (x : ℝ) ∈ B r := by
    exact (intervalPartitionRelease_eq_iff B hB x r).mp hx
  have hyB : (y : ℝ) ∈ B r := by
    exact (intervalPartitionRelease_eq_iff B hB y r).mp hy
  apply (intervalPartitionRelease_eq_iff B hB z r).mpr
  rw [ordConnected_iff] at hBorder
  exact hBorder (x : ℝ) hxB (y : ℝ) hyB hxy ⟨hz.1, hz.2⟩

end
end CausalSmith.PartialID.UnlinkedPropensityAte
