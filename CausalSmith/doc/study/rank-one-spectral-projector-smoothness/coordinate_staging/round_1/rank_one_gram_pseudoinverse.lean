import Causalean.Mathlib.Analysis.TwoByTwoSpectralProjector
import Mathlib.Analysis.Matrix.PosDef

/-!
# Rank-one truncation and pseudoinverse from a two-row Gram matrix

This module identifies eigenvector-based rank-one truncation and pseudoinverse formulas with a choice-free algebraic construction from the left Gram matrix.  It proves the Moore--Penrose identities and local continuous differentiability on the isolated-positive-root region.
-/

open Matrix
open scoped Matrix.Norms.Elementwise

namespace Causalean.Mathlib.Analysis

variable {E : Type*} [Fintype E]

private theorem contDiffAt_matrix_mul
    {X m n p : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] [Fintype p]
    {f : X → Matrix m n ℝ} {g : X → Matrix n p ℝ} {x : X}
    (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) :
    ContDiffAt ℝ 1 (fun y => f y * g y) x := by
  apply contDiffAt_pi'
  intro i
  apply contDiffAt_pi'
  intro j
  simp only [Matrix.mul_apply]
  apply ContDiffAt.sum
  intro k _
  exact ((contDiffAt_pi.mp (contDiffAt_pi.mp hf i) k).mul
    (contDiffAt_pi.mp (contDiffAt_pi.mp hg k) j))

private theorem contDiffAt_matrix_transpose
    {X m n : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [Fintype m] [Fintype n] {f : X → Matrix m n ℝ} {x : X}
    (hf : ContDiffAt ℝ 1 f x) :
    ContDiffAt ℝ 1 (fun y => (f y).transpose) x := by
  apply contDiffAt_pi'
  intro j
  apply contDiffAt_pi'
  intro i
  exact contDiffAt_pi.mp (contDiffAt_pi.mp hf i) j

/-- Given [a real matrix with two rows](hyp:H), [its left Gram matrix](goal) records all pairwise inner products of those rows. -/
def leftGram (H : Matrix (Fin 2) E ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  H * H.transpose

/-- For [a real matrix with two rows](hyp:H), [its left Gram matrix is symmetric](goal). -/
theorem leftGram_isHermitian (H : Matrix (Fin 2) E ℝ) :
    (leftGram H).IsHermitian := by
  simpa [leftGram, conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_mul_conjTranspose_self H

/-- Given [a real two-vector](hyp:u) and [a real matrix with two rows](hyp:H), [the eigenvector-selected rank-one truncation](goal) projects the rows of the matrix onto that vector before reconstruction. -/
def eigenvectorRankOneTruncation (u : Fin 2 → ℝ) (H : Matrix (Fin 2) E ℝ) :
    Matrix (Fin 2) E ℝ :=
  outerProjector u * H

/-- Given [a real two-vector](hyp:u) and [a real matrix with two rows](hyp:H), [the eigenvector-selected rank-one pseudoinverse formula](goal) transposes the projected matrix and divides by its upper Gram root. -/
noncomputable def eigenvectorRankOnePseudoInverse (u : Fin 2 → ℝ) (H : Matrix (Fin 2) E ℝ) :
    Matrix E (Fin 2) ℝ :=
  (lambda₁ (leftGram H))⁻¹ • (H.transpose * outerProjector u)

/-- Given [a real matrix with two rows](hyp:H), [the choice-free algebraic rank-one truncation](goal) applies the algebraic upper projector of its left Gram matrix. -/
noncomputable def algebraicRankOneTruncation (H : Matrix (Fin 2) E ℝ) :
    Matrix (Fin 2) E ℝ :=
  topProjector (leftGram H) * H

/-- Given [a real matrix with two rows](hyp:H), [the choice-free algebraic rank-one pseudoinverse](goal) transposes the algebraically projected matrix and divides by the upper Gram root. -/
noncomputable def algebraicRankOnePseudoInverse (H : Matrix (Fin 2) E ℝ) :
    Matrix E (Fin 2) ℝ :=
  (lambda₁ (leftGram H))⁻¹ • (H.transpose * topProjector (leftGram H))

/-- Given [a real two-row matrix](hyp:H) with [a strict left-Gram root gap](hyp:hgap) and [a unit upper left-Gram eigenvector](hyp:u,hu_unit,hu_eig), [the eigenvector-selected and algebraic rank-one truncations agree](goal). -/
theorem eigenvectorRankOneTruncation_eq_algebraic {H : Matrix (Fin 2) E ℝ}
    (hgap : leftGram H ∈ strictGapSet) {u : Fin 2 → ℝ}
    (hu_unit : dotProduct u u = 1)
    (hu_eig : (leftGram H).mulVec u = lambda₁ (leftGram H) • u) :
    eigenvectorRankOneTruncation u H = algebraicRankOneTruncation H := by
  rw [eigenvectorRankOneTruncation, algebraicRankOneTruncation,
    topProjector_eq_outerProjector (leftGram_isHermitian H) hgap hu_unit hu_eig]

/-- Given [a real two-row matrix](hyp:H) with [a strict positive upper left-Gram root](hyp:hgap,hpos) and [a unit upper left-Gram eigenvector](hyp:u,hu_unit,hu_eig), [the eigenvector-selected and algebraic rank-one pseudoinverse formulas agree](goal). -/
theorem eigenvectorRankOnePseudoInverse_eq_algebraic {H : Matrix (Fin 2) E ℝ}
    (hgap : leftGram H ∈ strictGapSet) (hpos : 0 < lambda₁ (leftGram H))
    {u : Fin 2 → ℝ} (hu_unit : dotProduct u u = 1)
    (hu_eig : (leftGram H).mulVec u = lambda₁ (leftGram H) • u) :
    eigenvectorRankOnePseudoInverse u H = algebraicRankOnePseudoInverse H := by
  have _hlambda_ne : lambda₁ (leftGram H) ≠ 0 := ne_of_gt hpos
  rw [eigenvectorRankOnePseudoInverse, algebraicRankOnePseudoInverse,
    topProjector_eq_outerProjector (leftGram_isHermitian H) hgap hu_unit hu_eig]

/-- Given [a real two-row matrix](hyp:H) with [a strict positive upper left-Gram root](hyp:hgap,hpos), [the algebraic rank-one pseudoinverse satisfies all four Moore--Penrose equations for the algebraic rank-one truncation](goal). -/
theorem algebraicRankOnePseudoInverse_isMoorePenrose {H : Matrix (Fin 2) E ℝ}
    (hgap : leftGram H ∈ strictGapSet) (hpos : 0 < lambda₁ (leftGram H)) :
    let A := algebraicRankOneTruncation H
    let Aplus := algebraicRankOnePseudoInverse H
    A * Aplus * A = A ∧
      Aplus * A * Aplus = Aplus ∧
      (A * Aplus).IsHermitian ∧
      (Aplus * A).IsHermitian := by
  let G := leftGram H
  let P := topProjector G
  let l := lambda₁ G
  have hG : G.IsHermitian := leftGram_isHermitian H
  have hP : P.IsHermitian := topProjector_isHermitian hG
  have hPP : P * P = P := topProjector_mul_self hG hgap
  have hl : l ≠ 0 := ne_of_gt hpos
  have hdecomp : G = (lambda₁ G - lambda₂ G) • P + lambda₂ G • 1 := by
    have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
    ext i j
    simp [P, topProjector]
    field_simp [hne]
    ring
  have hPG : P * G = l • P := by
    rw [hdecomp, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
      hPP, Matrix.mul_one]
    ext i j
    simp [l]
    ring
  have hAAplus :
      algebraicRankOneTruncation H * algebraicRankOnePseudoInverse H = P := by
    rw [algebraicRankOneTruncation, algebraicRankOnePseudoInverse,
      Matrix.mul_smul]
    change (lambda₁ G)⁻¹ • ((P * H) * (H.transpose * P)) = P
    rw [← Matrix.mul_assoc (P * H) H.transpose P,
      Matrix.mul_assoc P H H.transpose]
    change (lambda₁ G)⁻¹ • (P * G * P) = P
    rw [hPG, Matrix.smul_mul, hPP]
    simp [l, hl]
  have hAplusP : algebraicRankOnePseudoInverse H * P =
      algebraicRankOnePseudoInverse H := by
    rw [algebraicRankOnePseudoInverse, Matrix.smul_mul, Matrix.mul_assoc, hPP]
  have hAplusA :
      algebraicRankOnePseudoInverse H * algebraicRankOneTruncation H =
        l⁻¹ • (H.transpose * P * H) := by
    rw [algebraicRankOnePseudoInverse, algebraicRankOneTruncation,
      Matrix.smul_mul]
    change (lambda₁ G)⁻¹ • ((H.transpose * P) * (P * H)) =
      (lambda₁ G)⁻¹ • (H.transpose * P * H)
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P P H, hPP]
    rw [Matrix.mul_assoc]
  dsimp only
  refine ⟨?_, ?_, hAAplus ▸ hP, ?_⟩
  · rw [hAAplus]
    change P * (P * H) = P * H
    rw [← Matrix.mul_assoc, hPP]
  · rw [Matrix.mul_assoc, hAAplus, hAplusP]
  · rw [hAplusA]
    apply (Matrix.isHermitian_conjTranspose_mul_mul H hP).smul
    simp [isSelfAdjoint_iff]

/-- Given [a real two-row matrix](hyp:H) whose [left Gram matrix has distinct roots](hyp:hgap), [the algebraic rank-one truncation varies continuously differentiably near that matrix](goal). -/
theorem contDiffAt_algebraicRankOneTruncation {H : Matrix (Fin 2) E ℝ}
    (hgap : leftGram H ∈ strictGapSet) :
    ContDiffAt ℝ 1 algebraicRankOneTruncation H := by
  have hgram : ContDiffAt ℝ 1 leftGram H := by
    unfold leftGram
    exact contDiffAt_matrix_mul contDiffAt_id
      (contDiffAt_matrix_transpose contDiffAt_id)
  have hprojector : ContDiffAt ℝ 1 (fun X => topProjector (leftGram X)) H :=
    (contDiffAt_topProjector hgap).comp H hgram
  unfold algebraicRankOneTruncation
  exact contDiffAt_matrix_mul hprojector contDiffAt_id

/-- Given [a real two-row matrix](hyp:H) whose [left Gram matrix has a strict positive upper root](hyp:hgap,hpos), [the algebraic rank-one pseudoinverse varies continuously differentiably near that matrix](goal). -/
theorem contDiffAt_algebraicRankOnePseudoInverse {H : Matrix (Fin 2) E ℝ}
    (hgap : leftGram H ∈ strictGapSet) (hpos : 0 < lambda₁ (leftGram H)) :
    ContDiffAt ℝ 1 algebraicRankOnePseudoInverse H := by
  have hgram : ContDiffAt ℝ 1 leftGram H := by
    unfold leftGram
    exact contDiffAt_matrix_mul contDiffAt_id
      (contDiffAt_matrix_transpose contDiffAt_id)
  have hlambda : ContDiffAt ℝ 1 (fun X => lambda₁ (leftGram X)) H :=
    (contDiffAt_lambda₁ hgap).comp H hgram
  have hinv : ContDiffAt ℝ 1 (fun X => (lambda₁ (leftGram X))⁻¹) H :=
    hlambda.inv (ne_of_gt hpos)
  have hprojector : ContDiffAt ℝ 1 (fun X => topProjector (leftGram X)) H :=
    (contDiffAt_topProjector hgap).comp H hgram
  unfold algebraicRankOnePseudoInverse
  exact hinv.smul (contDiffAt_matrix_mul
    (contDiffAt_matrix_transpose contDiffAt_id) hprojector)

end Causalean.Mathlib.Analysis
