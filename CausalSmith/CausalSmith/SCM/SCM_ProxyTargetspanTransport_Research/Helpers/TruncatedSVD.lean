import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Causalean.Mathlib.Analysis.RankOneWaldSmoothness

set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! A finite Gram-spectral construction of the rank-truncated matrix and pseudoinverse. -/

open scoped BigOperators
open Matrix
open scoped Matrix.Norms.Elementwise

namespace CausalSmith.SCM.ProxyTargetspanTransport

variable {E W : Type*} [Fintype E] [Fintype W] [DecidableEq E] [DecidableEq W]

/-- The paper's positive rank indices, bounded by the smaller matrix dimension. -/
def RankIndex (E W : Type*) [Fintype E] [Fintype W] :=
  {r0 : ℕ // 1 ≤ r0 ∧ r0 ≤ min (Fintype.card W) (Fintype.card E)}
-- @realizes r_0(1 <= r0 <= min(card W, card E))

/-- [The matrix](hyp:H) determine [the left Gram matrix formed by multiplying a matrix by its transpose](goal). -/
noncomputable def gramMatrix (H : Matrix W E ℝ) : Matrix W W ℝ := H * H.transpose

omit [Fintype W] [DecidableEq E] [DecidableEq W] in
private lemma gramMatrix_isHermitian (H : Matrix W E ℝ) : (gramMatrix H).IsHermitian := by
  unfold Matrix.IsHermitian gramMatrix
  ext i j
  simp [Matrix.mul_apply, mul_comm]

private noncomputable def spectralEquiv (W : Type*) [Fintype W] :
    Fin (Fintype.card W) ≃ W :=
  Fintype.equivOfCardEq (Fintype.card_fin _)

private noncomputable def spectralIndex (w : W) : Fin (Fintype.card W) :=
  (spectralEquiv W).symm w

/-- [The rank index and matrix](hyp:r0,H) determine [the leading-eigenspace selector](goal) by
[choosing a unitary Gram eigenbasis](step:1) and [retaining exactly its first requested
coordinates](step:2). -/
noncomputable def topEigenSelect (r0 : ℕ) (H : Matrix W E ℝ) : Matrix W W ℝ :=
  let Umat : Matrix W W ℝ := gramMatrix_isHermitian H |>.eigenvectorUnitary
  Umat * diagonal (fun w => if (spectralIndex w).val < r0 then (1 : ℝ) else 0)

/-- [The rank index and matrix](hyp:r0,H) determine [the leading Gram-eigenspace
projector](goal) by [choosing a unitary Gram eigenbasis](step:1) and [conjugating the leading
coordinate selector by that basis](step:2). -/
noncomputable def topProjection (r0 : ℕ) (H : Matrix W E ℝ) : Matrix W W ℝ :=
  let Umat : Matrix W W ℝ := gramMatrix_isHermitian H |>.eigenvectorUnitary
  topEigenSelect r0 H * Umat.transpose

/-- [The rank index and matrix](hyp:r0,H) determine [the rank-truncated pseudoinverse](goal):
the construction [forms the Gram decomposition](step:1), [chooses its unitary eigenbasis](step:2),
[inverts only the selected eigenvalues](step:3), and [transports that inverse back through the
matrix transpose and eigenbasis](step:4). -/
noncomputable def truncatedPseudoInverse (r0 : ℕ) (H : Matrix W E ℝ) : Matrix E W ℝ :=
  let hG := gramMatrix_isHermitian H
  let Umat : Matrix W W ℝ := hG.eigenvectorUnitary
  let invEig : Matrix W W ℝ := diagonal (fun w =>
    if (spectralIndex w).val < r0 then (hG.eigenvalues w)⁻¹ else 0)
  H.transpose * Umat * invEig * Umat.transpose

/-- [The rank index, matrix](hyp:r0,H) determine [the requested singular value, totalized to zero at rank index zero](goal). -/
noncomputable def sigmaAt (r0 : ℕ) (H : Matrix W E ℝ) : ℝ :=
  if 1 ≤ r0 then (Matrix.toEuclideanLin H).singularValues (r0 - 1) else 0
-- @realizes \sigma_{r_0}(r0-th ordered singular value)

omit [DecidableEq W] in
/-- [at a positive successor rank, the totalized singular-value selector returns the corresponding zero-based singular value](goal). -/
lemma sigmaAt_succ (j : ℕ) (H : Matrix W E ℝ) :
    sigmaAt (j + 1) H = (Matrix.toEuclideanLin H).singularValues j := by
  simp [sigmaAt]

-- @node: def:regular-wald-functional
/-- [The rank index, matrix, outcome vector, target proxy vector](hyp:r0,H,z,bvec) determine [the rank-truncated Wald functional obtained by pairing the outcome vector with the truncated-pseudoinverse balancing weights](goal). -/
noncomputable def regularWaldFunctional (r0 : RankIndex E W) (H : Matrix W E ℝ)
    (z : E → ℝ) (bvec : W → ℝ) : ℝ :=
  dotProduct z ((truncatedPseudoInverse r0.val H).mulVec bvec)
-- @realizes \phi_{r_0}(z^T H_r0^dagger b) @realizes H(generic matrix)
-- @realizes z(generic outcome vector) @realizes r_0(retained rank index)

private noncomputable def spectralLabel (i : Fin 2) : Fin 2 :=
  spectralEquiv (Fin 2) i

private lemma spectralIndex_spectralLabel (i : Fin 2) :
    spectralIndex (spectralLabel i) = i := by
  unfold spectralIndex spectralLabel
  exact (spectralEquiv (Fin 2)).symm_apply_apply i

private lemma orderedTopEigenvalue_eq_lambda₁
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsHermitian)
    (hgap : G ∈ Causalean.Mathlib.Analysis.strictGapSet) :
    hG.eigenvalues (spectralLabel 0) = Causalean.Mathlib.Analysis.lambda₁ G := by
  let u0 : Fin 2 → ℝ := ⇑(hG.eigenvectorBasis (spectralLabel 0))
  let u1 : Fin 2 → ℝ := ⇑(hG.eigenvectorBasis (spectralLabel 1))
  have hu0norm : ‖hG.eigenvectorBasis (spectralLabel 0)‖ = 1 :=
    hG.eigenvectorBasis.orthonormal.1 (spectralLabel 0)
  have hu1norm : ‖hG.eigenvectorBasis (spectralLabel 1)‖ = 1 :=
    hG.eigenvectorBasis.orthonormal.1 (spectralLabel 1)
  have hu0 : u0 ≠ 0 := by
    intro hz
    apply hG.eigenvectorBasis.orthonormal.ne_zero (spectralLabel 0)
    apply PiLp.ext
    intro i
    simpa [u0] using congrFun hz i
  have hu1 : u1 ≠ 0 := by
    intro hz
    apply hG.eigenvectorBasis.orthonormal.ne_zero (spectralLabel 1)
    apply PiLp.ext
    intro i
    simpa [u1] using congrFun hz i
  have he0 := Causalean.Mathlib.Analysis.eigenvalue_eq_lambda₁_or_lambda₂ hG hu0
    (hG.mulVec_eigenvectorBasis (spectralLabel 0))
  have he1 := Causalean.Mathlib.Analysis.eigenvalue_eq_lambda₁_or_lambda₂ hG hu1
    (hG.mulVec_eigenvectorBasis (spectralLabel 1))
  have hmono : hG.eigenvalues (spectralLabel 1) ≤ hG.eigenvalues (spectralLabel 0) := by
    unfold Matrix.IsHermitian.eigenvalues
    change hG.eigenvalues₀ (spectralIndex (spectralLabel 1)) ≤
      hG.eigenvalues₀ (spectralIndex (spectralLabel 0))
    rw [spectralIndex_spectralLabel, spectralIndex_spectralLabel]
    exact hG.eigenvalues₀_antitone (by decide)
  rcases he0 with he0 | he0
  · exact he0
  · exfalso
    have he1' : hG.eigenvalues (spectralLabel 1) =
        Causalean.Mathlib.Analysis.lambda₂ G := by
      rcases he1 with he1 | he1
      · exfalso
        rw [he0, he1] at hmono
        exact (not_le_of_gt hgap) hmono
      · exact he1
    have htrace := hG.trace_eq_sum_eigenvalues
    change G.trace = ∑ i, hG.eigenvalues i at htrace
    have hroots := Causalean.Mathlib.Analysis.lambda₁_add_lambda₂ G
    have hlabels :
        (∑ i : Fin 2, hG.eigenvalues i) =
          hG.eigenvalues (spectralLabel 0) + hG.eigenvalues (spectralLabel 1) := by
      rw [← Equiv.sum_comp (spectralEquiv (Fin 2))]
      change (∑ i : Fin 2, hG.eigenvalues (spectralEquiv (Fin 2) i)) = _
      rw [Fin.sum_univ_two]
      rfl
    rw [hlabels, he0, he1'] at htrace
    simp only [Matrix.trace, Fin.sum_univ_two] at htrace
    change G 0 0 + G 1 1 = _ at htrace
    change Causalean.Mathlib.Analysis.lambda₂ G <
      Causalean.Mathlib.Analysis.lambda₁ G at hgap
    linarith

private lemma spectralIndex_lt_one_iff (w : Fin 2) :
    (spectralIndex w).val < 1 ↔ w = spectralLabel 0 := by
  constructor
  · intro h
    have hi : spectralIndex w = (0 : Fin 2) := by
      apply Fin.ext
      exact Nat.lt_one_iff.mp h
    calc
      w = spectralLabel (spectralIndex w) := by
        unfold spectralIndex spectralLabel
        exact ((spectralEquiv (Fin 2)).apply_symm_apply w).symm
      _ = spectralLabel 0 := congrArg spectralLabel hi
  · rintro rfl
    rw [spectralIndex_spectralLabel]
    decide

private lemma topProjection_eq_outerProjector
    (H : Matrix (Fin 2) E ℝ) :
    topProjection 1 H = Causalean.Mathlib.Analysis.outerProjector
      (⇑((gramMatrix_isHermitian H).eigenvectorBasis (spectralLabel 0))) := by
  let hG := gramMatrix_isHermitian H
  let Umat : Matrix (Fin 2) (Fin 2) ℝ := hG.eigenvectorUnitary
  let u : Fin 2 → ℝ := ⇑(hG.eigenvectorBasis (spectralLabel 0))
  have hselect (i j : Fin 2) :
      topEigenSelect 1 H i j = if j = spectralLabel 0 then Umat i j else 0 := by
    simp only [topEigenSelect, Umat, Matrix.mul_apply, Matrix.diagonal]
    simp_rw [spectralIndex_lt_one_iff]
    simp [hG]
  ext i j
  simp only [topProjection, Matrix.mul_apply]
  simp_rw [hselect]
  simp [Umat, u, Causalean.Mathlib.Analysis.outerProjector,
    Matrix.vecMulVec, Matrix.transpose_apply]

/-- Given [the strict spectral-gap condition, the required strict positivity condition](hyp:hgap,hpos), [on the positive rank-one regular region, the ordered spectral pseudoinverse agrees with the choice-free algebraic pseudoinverse](goal). -/
theorem truncatedPseudoInverse_one_eq_algebraic {H : Matrix (Fin 2) E ℝ}
    (hgap : Causalean.Mathlib.Analysis.leftGram H ∈
      Causalean.Mathlib.Analysis.strictGapSet)
    (hpos : 0 < Causalean.Mathlib.Analysis.lambda₁
      (Causalean.Mathlib.Analysis.leftGram H)) :
    truncatedPseudoInverse 1 H =
      Causalean.Mathlib.Analysis.algebraicRankOnePseudoInverse H := by
  let G := gramMatrix H
  let hG := gramMatrix_isHermitian H
  let Umat : Matrix (Fin 2) (Fin 2) ℝ := hG.eigenvectorUnitary
  let u : Fin 2 → ℝ := ⇑(hG.eigenvectorBasis (spectralLabel 0))
  have hleft : Causalean.Mathlib.Analysis.leftGram H = G := rfl
  have hgap' : G ∈ Causalean.Mathlib.Analysis.strictGapSet := by
    rw [← hleft]
    exact hgap
  have hpos' : 0 < Causalean.Mathlib.Analysis.lambda₁ G := by
    rw [← hleft]
    exact hpos
  have heigval : hG.eigenvalues (spectralLabel 0) =
      Causalean.Mathlib.Analysis.lambda₁ G :=
    orderedTopEigenvalue_eq_lambda₁ G hG hgap'
  have huunit : dotProduct u u = 1 := by
    have hi := (orthonormal_iff_ite.mp hG.eigenvectorBasis.orthonormal)
      (spectralLabel 0) (spectralLabel 0)
    have hi' : inner ℝ (hG.eigenvectorBasis (spectralLabel 0))
        (hG.eigenvectorBasis (spectralLabel 0)) = 1 := by simpa using hi
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hi'
    simpa [u] using hi'
  have hueig : G.mulVec u = Causalean.Mathlib.Analysis.lambda₁ G • u := by
    simpa [u, heigval] using hG.mulVec_eigenvectorBasis (spectralLabel 0)
  have hchoice := Causalean.Mathlib.Analysis.eigenvectorRankOnePseudoInverse_eq_algebraic
    hgap' hpos' huunit hueig
  have hinvDiag :
      diagonal (fun w : Fin 2 =>
        if (spectralIndex w).val < 1 then (hG.eigenvalues w)⁻¹ else 0) =
      (Causalean.Mathlib.Analysis.lambda₁ G)⁻¹ •
        diagonal (fun w : Fin 2 => if (spectralIndex w).val < 1 then 1 else 0) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : (spectralIndex i).val < 1
      · have hilabel := (spectralIndex_lt_one_iff i).mp hi
        subst i
        simp [hi, heigval]
      · have hne : spectralIndex i ≠ 0 := by
          intro hz
          apply hi
          rw [hz]
          decide
        simp [hi, hne]
    · simp [Matrix.diagonal, hij]
  rw [truncatedPseudoInverse]
  change H.transpose * Umat *
      diagonal (fun w : Fin 2 => if (spectralIndex w).val < 1 then (hG.eigenvalues w)⁻¹ else 0) *
        Umat.transpose = _
  rw [hinvDiag, Matrix.mul_smul, Matrix.smul_mul]
  change (Causalean.Mathlib.Analysis.lambda₁ G)⁻¹ •
      (H.transpose * Umat *
        diagonal (fun w : Fin 2 => if (spectralIndex w).val < 1 then 1 else 0) *
          Umat.transpose) = _
  rw [Matrix.mul_assoc H.transpose Umat,
    Matrix.mul_assoc H.transpose (Umat * diagonal _) Umat.transpose]
  change (Causalean.Mathlib.Analysis.lambda₁ G)⁻¹ •
      (H.transpose * topProjection 1 H) = _
  rw [topProjection_eq_outerProjector]
  exact hchoice

/-- Given [the hr0 condition, the strict spectral-gap condition, the required strict positivity condition](hyp:hr0,hgap,hpos), [on the positive rank-one regular region, the spectral Wald functional agrees with the choice-free algebraic Wald functional](goal). -/
theorem regularWaldFunctional_one_eq_algebraic (r0 : RankIndex E (Fin 2))
    (hr0 : r0.val = 1) {H : Matrix (Fin 2) E ℝ}
    (hgap : Causalean.Mathlib.Analysis.leftGram H ∈
      Causalean.Mathlib.Analysis.strictGapSet)
    (hpos : 0 < Causalean.Mathlib.Analysis.lambda₁
      (Causalean.Mathlib.Analysis.leftGram H)) (z : E → ℝ) (b : Fin 2 → ℝ) :
    regularWaldFunctional r0 H z b =
      Causalean.Mathlib.Analysis.algebraicWaldFunctional (H, z, b) := by
  simp only [regularWaldFunctional,
    Causalean.Mathlib.Analysis.algebraicWaldFunctional]
  rw [hr0]
  rw [truncatedPseudoInverse_one_eq_algebraic hgap hpos]

/-- Given [the hr0 condition, the hx condition](hyp:hr0,hx), [the rank-one Wald functional is continuously differentiable at every input with a positive leading singular value and nonzero treatment columns](goal). -/
theorem contDiffAt_regularWaldFunctional_one (r0 : RankIndex E (Fin 2))
    (hr0 : r0.val = 1) {x : Causalean.Mathlib.Analysis.WaldInput E}
    (hx : x ∈ Causalean.Mathlib.Analysis.waldRegularSet) :
    ContDiffAt ℝ 1
      (fun y : Causalean.Mathlib.Analysis.WaldInput E =>
        regularWaldFunctional r0 y.1 y.2.1 y.2.2) x := by
  apply (Causalean.Mathlib.Analysis.contDiffAt_algebraicWaldFunctional hx).congr_of_eventuallyEq
  filter_upwards [Causalean.Mathlib.Analysis.isOpen_waldRegularSet.eventually_mem hx] with y hy
  exact regularWaldFunctional_one_eq_algebraic r0 hr0 hy.1 hy.2 y.2.1 y.2.2

end CausalSmith.SCM.ProxyTargetspanTransport
