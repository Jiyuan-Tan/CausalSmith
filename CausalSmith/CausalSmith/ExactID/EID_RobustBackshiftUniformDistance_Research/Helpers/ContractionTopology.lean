import CausalSmith.ExactID.EID_RobustBackshiftUniformDistance_Research.Helpers.ContractionUniformExclusion
import Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine.Definitions

/-! # Closed matrix constraints used by contraction compactness -/

namespace CausalSmith.ExactID.RobustBackshiftUniformDistance

open Set
open scoped Matrix Matrix.Norms.L2Operator
open Causalean.Discovery.LinearDisentanglement.Quantitative.PairwiseAffine

/-- Positive semidefiniteness is closed in finite-dimensional real matrix space. [This is the asserted conclusion](goal). -/
lemma isClosed_posSemidef_realMatrix (p : ℕ) :
    IsClosed {A : RealMatrix p | A.PosSemidef} := by
  change IsClosed ({A : RealMatrix p | A.IsHermitian ∧
    ∀ x : Fin p →₀ ℝ,
      0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj})
  rw [show {A : RealMatrix p | A.IsHermitian ∧
      ∀ x : Fin p →₀ ℝ,
        0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj} =
      {A | A.IsHermitian} ∩ ⋂ x : Fin p →₀ ℝ,
        {A | 0 ≤ x.sum fun i xi ↦ x.sum fun j xj ↦ star xi * A i j * xj} by
    ext A; simp]
  apply IsClosed.inter
  · exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    change Continuous (fun A : RealMatrix p =>
      ∑ i ∈ x.support, ∑ j ∈ x.support, star (x i) * A i j * x j)
    fun_prop

/-- Largest affine determinant over triples from a fixed retained set. -/
def maxPairAffineDet {p m : ℕ} (S : Finset (Environment m)) [Nonempty {e // e ∈ S}]
    (s : ContractionShifts p m) (i j : Fin p) : ℝ :=
  (Finset.univ : Finset ({e // e ∈ S} × {e // e ∈ S} × {e // e ∈ S})).sup'
    Finset.univ_nonempty (fun q ↦ |pairAffineDet (fun e : {e // e ∈ S} ↦ s e.1)
      i j q.1 q.2.1 q.2.2|)

/-- For a fixed retained set and coordinate pair, [the largest absolute affine determinant varies continuously with the shift array](goal). -/
lemma continuous_maxPairAffineDet {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (i j : Fin p) :
    Continuous (fun s : ContractionShifts p m ↦ maxPairAffineDet S s i j) := by
  unfold maxPairAffineDet
  let f := fun q : {e // e ∈ S} × {e // e ∈ S} × {e // e ∈ S} =>
    fun s : ContractionShifts p m =>
      |pairAffineDet (fun e : {e // e ∈ S} ↦ s e.1) i j q.1 q.2.1 q.2.2|
  have hf : ∀ q, Continuous (f q) := by
    intro q
    dsimp [f]
    apply Continuous.abs
    unfold pairAffineDet
    fun_prop
  have h := Continuous.finset_sup' (s := Finset.univ) Finset.univ_nonempty
    (fun q _ => hf q)
  convert h using 1
  funext s
  exact (Finset.sup'_apply Finset.univ_nonempty f s).symm

/-- Uniform lower bounds on all fixed-set pairwise affine maxima form a closed set. [This is the asserted conclusion](goal). -/
lemma isClosed_pairwiseAffineMaxSeparated {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (γ : ℝ) :
    IsClosed {s : ContractionShifts p m |
      ∀ i j : Fin p, i ≠ j → γ ≤ maxPairAffineDet S s i j} := by
  simp only [show {s : ContractionShifts p m |
      ∀ i j : Fin p, i ≠ j → γ ≤ maxPairAffineDet S s i j} =
      ⋂ i, ⋂ j, ⋂ (_h : i ≠ j), {s | γ ≤ maxPairAffineDet S s i j} by
        ext s
        simp]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _h
  exact isClosed_le continuous_const (continuous_maxPairAffineDet S i j)

/-- The closed maximum formulation implies the existential pairwise-separation predicate. [Under the stated hypotheses](hyp:h) [this conclusion](goal) applies. -/
lemma pairwiseAffineSeparated_of_max {p m : ℕ} (S : Finset (Environment m))
    [Nonempty {e // e ∈ S}] (s : ContractionShifts p m) (γ : ℝ)
    (h : ∀ i j : Fin p, i ≠ j → γ ≤ maxPairAffineDet S s i j) :
    PairwiseAffineSeparated (fun e : {e // e ∈ S} ↦ s e.1) γ := by
  intro i j hij
  have hle := h i j hij
  unfold maxPairAffineDet at hle
  rw [Finset.le_sup'_iff] at hle
  obtain ⟨q, _, hq⟩ := hle
  exact ⟨q.1, q.2.1, q.2.2, hq⟩

end CausalSmith.ExactID.RobustBackshiftUniformDistance
