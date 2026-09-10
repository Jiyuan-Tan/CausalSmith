import Causalean.Mathlib.Analysis.TwoByTwoSpectralRoots
import Mathlib.Data.Matrix.Mul

/-!
# Choice-free top spectral projector in dimension two

This module turns the two explicit roots into an algebraic projector onto the upper eigenspace of a real symmetric two-by-two matrix.  The formula is independent of any sign or basis choice for an eigenvector and is continuously differentiable on the strict-gap region.
-/

open Matrix
open scoped Matrix.Norms.Elementwise

namespace Causalean.Mathlib.Analysis

/-- Given [a real two-vector](hyp:v), [its rank-one outer-product matrix](goal) maps a vector to its component in the direction of that two-vector, before normalization. -/
def outerProjector (v : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i j => v i * v j

/-- Given [a real two-by-two matrix](hyp:G), [the algebraic upper spectral-projector candidate](goal) is its lower-root-shifted matrix divided by the gap between its explicit roots. -/
noncomputable def topProjector (G : Matrix (Fin 2) (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (lambda₁ G - lambda₂ G)⁻¹ •
    (G - lambda₂ G • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- Given [a real two-by-two matrix](hyp:G) and [a candidate matrix](hyp:P), [the property of being the orthogonal projector onto the upper-root eigenspace](goal) means that the candidate is symmetric, idempotent, and fixes exactly the upper-root eigenvectors. -/
def IsOrthogonalProjectorOntoTop (G P : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  P.IsHermitian ∧ P * P = P ∧
    ∀ x : Fin 2 → ℝ, P.mulVec x = x ↔ G.mulVec x = lambda₁ G • x

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG) with [distinct explicit roots](hyp:hgap) and [a two-vector](hyp:x), [the algebraic projector fixes that vector exactly when it is an upper-root eigenvector](goal). -/
theorem topProjector_mulVec_eq_iff {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) (x : Fin 2 → ℝ) :
    (topProjector G).mulVec x = x ↔ G.mulVec x = lambda₁ G • x := by
  have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  constructor <;> intro h <;> funext i
  · have hi := congrFun h i
    fin_cases i
    all_goals
    simp [topProjector, Matrix.mulVec] at hi ⊢
    field_simp [hne] at hi
    linarith
  · have hi := congrFun h i
    fin_cases i
    all_goals
    simp [topProjector, Matrix.mulVec] at hi ⊢
    field_simp [hne]
    linarith

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG) with [distinct explicit roots](hyp:hgap) and [a two-vector](hyp:x), [the algebraic projector sends that vector to zero exactly when it is a lower-root eigenvector](goal). -/
theorem topProjector_mulVec_eq_zero_iff {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) (x : Fin 2 → ℝ) :
    (topProjector G).mulVec x = 0 ↔ G.mulVec x = lambda₂ G • x := by
  have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  constructor <;> intro h <;> funext i
  · have hi := congrFun h i
    fin_cases i
    all_goals
      simp [topProjector, Matrix.mulVec] at hi ⊢
      field_simp [hne] at hi
      linarith
  · have hi := congrFun h i
    fin_cases i
    all_goals
      simp [topProjector, Matrix.mulVec] at hi ⊢
      field_simp [hne]
      linarith

/-- Given [a real two-by-two matrix](hyp:G) that [is symmetric](hyp:hG), [its algebraic upper projector is symmetric](goal). -/
theorem topProjector_isHermitian {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) : (topProjector G).IsHermitian := by
  unfold topProjector
  apply (hG.sub (Matrix.isHermitian_one.smul ?_)).smul
  · simp [isSelfAdjoint_iff]
  · simp [isSelfAdjoint_iff]

/-- Given [a real two-by-two matrix](hyp:G) that [is symmetric](hyp:hG) and [has distinct explicit roots](hyp:hgap), [its algebraic upper projector is idempotent](goal). -/
theorem topProjector_mul_self {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) :
    topProjector G * topProjector G = topProjector G := by
  have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  have hsym : G 1 0 = G 0 1 := by simpa using hG.apply 0 1
  have hsum := lambda₁_add_lambda₂ G
  have hprod := lambda₁_mul_lambda₂ hG
  rw [Matrix.det_fin_two, hsym] at hprod
  have ha : lambda₁ G = G 0 0 + G 1 1 - lambda₂ G := by
    linarith [hsum]
  have hb : lambda₂ G ^ 2 - (G 0 0 + G 1 1) * lambda₂ G +
      (G 0 0 * G 1 1 - G 0 1 * G 0 1) = 0 := by
    rw [← hprod, ← hsum]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topProjector, Matrix.mul_apply] <;>
    field_simp [hne] <;>
    (try rw [hsym]) <;>
    rw [ha] <;>
    nlinarith [hb]

/-- Given [a real two-by-two matrix](hyp:G) that [is symmetric](hyp:hG) and [has distinct explicit roots](hyp:hgap), [its algebraic quotient is the orthogonal projector onto the upper-root eigenspace](goal). -/
theorem topProjector_isOrthogonalProjectorOntoTop {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) :
    IsOrthogonalProjectorOntoTop G (topProjector G) := by
  exact ⟨topProjector_isHermitian hG, topProjector_mul_self hG hgap,
    topProjector_mulVec_eq_iff hG hgap⟩

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG) with [distinct explicit roots](hyp:hgap) and [a unit upper-root eigenvector](hyp:v,hv_unit,hv_eig), [the algebraic upper projector equals that vector's outer-product projector](goal). -/
theorem topProjector_eq_outerProjector {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) {v : Fin 2 → ℝ}
    (hv_unit : dotProduct v v = 1) (hv_eig : G.mulVec v = lambda₁ G • v) :
    topProjector G = outerProjector v := by
  have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  have hsym : G 1 0 = G 0 1 := by simpa using hG.apply 0 1
  have hsum := lambda₁_add_lambda₂ G
  have ha : lambda₁ G = G 0 0 + G 1 1 - lambda₂ G := by
    linarith [hsum]
  have h0 := congrFun hv_eig 0
  have h1 := congrFun hv_eig 1
  simp [Matrix.mulVec] at h0 h1
  rw [hsym, ha] at h1
  rw [ha] at h0
  simp [dotProduct] at hv_unit
  have hr0 : G 0 1 * v 1 = (G 1 1 - lambda₂ G) * v 0 := by
    linarith [h0]
  have hr1 : G 0 1 * v 0 = (G 0 0 - lambda₂ G) * v 1 := by
    linarith [h1]
  have h00 : G 0 0 - lambda₂ G =
      (lambda₁ G - lambda₂ G) * (v 0 * v 0) := by
    calc
      G 0 0 - lambda₂ G =
          (G 0 0 - lambda₂ G) * (v 0 * v 0 + v 1 * v 1) := by
            rw [hv_unit]
            ring
      _ = (G 0 0 - lambda₂ G) * (v 0 * v 0) +
          (G 0 1 * v 0) * v 1 := by rw [hr1]; ring
      _ = (G 0 0 - lambda₂ G) * (v 0 * v 0) +
          (G 0 1 * v 1) * v 0 := by ring
      _ = (G 0 0 + G 1 1 - 2 * lambda₂ G) * (v 0 * v 0) := by
            rw [hr0]
            ring
      _ = (lambda₁ G - lambda₂ G) * (v 0 * v 0) := by rw [ha]; ring
  have h11 : G 1 1 - lambda₂ G =
      (lambda₁ G - lambda₂ G) * (v 1 * v 1) := by
    calc
      G 1 1 - lambda₂ G =
          (G 1 1 - lambda₂ G) * (v 0 * v 0 + v 1 * v 1) := by
            rw [hv_unit]
            ring
      _ = (G 0 1 * v 1) * v 0 +
          (G 1 1 - lambda₂ G) * (v 1 * v 1) := by rw [hr0]; ring
      _ = (G 0 1 * v 0) * v 1 +
          (G 1 1 - lambda₂ G) * (v 1 * v 1) := by ring
      _ = (G 0 0 + G 1 1 - 2 * lambda₂ G) * (v 1 * v 1) := by
            rw [hr1]
            ring
      _ = (lambda₁ G - lambda₂ G) * (v 1 * v 1) := by rw [ha]; ring
  have h01 : G 0 1 = (lambda₁ G - lambda₂ G) * (v 0 * v 1) := by
    calc
      G 0 1 = G 0 1 * (v 0 * v 0 + v 1 * v 1) := by
        rw [hv_unit]
        ring
      _ = (G 0 1 * v 0) * v 0 + (G 0 1 * v 1) * v 1 := by ring
      _ = (G 0 0 + G 1 1 - 2 * lambda₂ G) * (v 0 * v 1) := by
        rw [hr0, hr1]
        ring
      _ = (lambda₁ G - lambda₂ G) * (v 0 * v 1) := by rw [ha]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [topProjector, outerProjector] <;>
    field_simp [hne] <;>
    (try rw [hsym]) <;>
    nlinarith [h00, h01, h11]

/-- Given [a real symmetric two-by-two matrix](hyp:G,hG) with [distinct explicit roots](hyp:hgap) and [two unit upper-root eigenvectors](hyp:v,w,hv_unit,hv_eig,hw_unit,hw_eig), [their outer-product projectors coincide](goal). -/
theorem outerProjector_eq_of_topEigenvectors {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hG : G.IsHermitian) (hgap : G ∈ strictGapSet) {v w : Fin 2 → ℝ}
    (hv_unit : dotProduct v v = 1) (hv_eig : G.mulVec v = lambda₁ G • v)
    (hw_unit : dotProduct w w = 1) (hw_eig : G.mulVec w = lambda₁ G • w) :
    outerProjector v = outerProjector w := by
  rw [← topProjector_eq_outerProjector hG hgap hv_unit hv_eig,
    ← topProjector_eq_outerProjector hG hgap hw_unit hw_eig]

/-- Given [a real two-vector](hyp:v), [negating it leaves its outer-product projector unchanged](goal). -/
theorem outerProjector_neg (v : Fin 2 → ℝ) :
    outerProjector (-v) = outerProjector v := by
  ext i j
  simp [outerProjector]

/-- Given [a real two-by-two matrix](hyp:G) with [distinct explicit roots](hyp:hgap), [its algebraic upper projector varies continuously differentiably near that matrix](goal). -/
theorem contDiffAt_topProjector {G : Matrix (Fin 2) (Fin 2) ℝ}
    (hgap : G ∈ strictGapSet) : ContDiffAt ℝ 1 topProjector G := by
  have hne : lambda₁ G - lambda₂ G ≠ 0 := ne_of_gt (sub_pos.mpr hgap)
  have hscalar : ContDiffAt ℝ 1 (fun A => (lambda₁ A - lambda₂ A)⁻¹) G :=
    ((contDiffAt_lambda₁ hgap).sub (contDiffAt_lambda₂ hgap)).inv hne
  have hmatrix : ContDiffAt ℝ 1
      (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
        A - lambda₂ A • (1 : Matrix (Fin 2) (Fin 2) ℝ)) G :=
    contDiffAt_id.sub ((contDiffAt_lambda₂ hgap).smul_const 1)
  change ContDiffAt ℝ 1
    (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (lambda₁ A - lambda₂ A)⁻¹ •
        (A - lambda₂ A • (1 : Matrix (Fin 2) (Fin 2) ℝ))) G
  exact hscalar.smul hmatrix

/-- [The algebraic upper projector is continuously differentiable throughout the strict-gap region](goal). -/
theorem contDiffOn_topProjector : ContDiffOn ℝ 1 topProjector strictGapSet := by
  intro G hgap
  exact (contDiffAt_topProjector hgap).contDiffWithinAt

end Causalean.Mathlib.Analysis
