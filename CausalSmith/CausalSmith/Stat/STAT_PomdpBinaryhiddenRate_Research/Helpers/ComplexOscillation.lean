module
public import CausalSmith.Stat.STAT_PomdpBinaryhiddenRate_Research.Basic
public import Causalean.Mathlib.Probability.FiniteMarkovOscillation
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly

/-!
# Complex oscillation contraction

Real TV duality applied to rotated real parts controls the diameter of complex
functions. This yields the transient eigenvalue bound without an eigenbasis.
-/

public section

namespace CausalSmith.Stat.PomdpBinaryhiddenRate

open scoped BigOperators
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
open Causalean.Mathlib.Probability.FiniteMarkovOscillation

/-- Every pair of rows is within the Dobrushin TV coefficient. [the stated conclusion holds](goal).-/
-- @node: row_tv_le_dobrushin
lemma row_tv_le_dobrushin (P : FourMatrix) (i j : JointState 2 2) :
    (1 / 2 : ℝ) * ∑ s, |P i s - P j s| ≤ dobrushin P := by
  have hj : (1 / 2 : ℝ) * ∑ s, |P i s - P j s| ≤
      ⨆ j : JointState 2 2, (1 / 2 : ℝ) * ∑ s, |P i s - P j s| :=
    le_ciSup (f := fun j : JointState 2 2 => (1 / 2 : ℝ) * ∑ s, |P i s - P j s|)
      (Finite.bddAbove_range _) j
  exact hj.trans (le_ciSup
    (f := fun i : JointState 2 2 => ⨆ j : JointState 2 2,
      (1 / 2 : ℝ) * ∑ s, |P i s - P j s|) (Finite.bddAbove_range _) i)

/-- A stochastic Dobrushin contraction contracts complex diameters in one step. [Under the listed formal conditions](hyp:hP,hδ,hf), [the stated conclusion holds](goal).-/
-- @node: dobrushin_complex_diameter_contraction
lemma dobrushin_complex_diameter_contraction (P : FourMatrix)
    (hP : IsStochasticMatrix P) {alpha B : ℝ} (hδ : dobrushin P ≤ alpha)
    (f : JointState 2 2 → ℂ) (hf : ∀ i j, ‖f i - f j‖ ≤ B)
    (i j : JointState 2 2) :
    ‖Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f i -
      Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f j‖ ≤ alpha * B := by
  have hB : 0 ≤ B := by simpa using hf i i
  have h := probability_complex_mean_tv_diameter
    (p := P i) (q := P j) ⟨hP.1 i, hP.2 i⟩ ⟨hP.1 j, hP.2 j⟩ hf
  have heq : Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f i -
      Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f j =
      ∑ s, ((P i s - P j s : ℝ) : ℂ) * f s := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply,
      ← Finset.sum_sub_distrib, Complex.ofReal_sub, sub_mul]
    rfl
  rw [heq]
  exact h.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left ((row_tv_le_dobrushin P i j).trans hδ) hB)

/-- A stochastic matrix fixes complex constant vectors. [Under the listed formal conditions](hyp:hP), [the stated conclusion holds](goal).-/
-- @node: stochastic_complex_constant
lemma stochastic_complex_constant (P : FourMatrix) (hP : IsStochasticMatrix P)
    (c : ℂ) : Matrix.mulVec (P.map (algebraMap ℝ ℂ)) (fun _ => c) = fun _ => c := by
  ext i
  change (∑ j, (P i j : ℂ) * c) = c
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, hP.2 i]
  simp

/-- A nonstationary complex eigenvector cannot be constant. [Under the listed formal conditions](hyp:hP,hz,hf0,hfe), [the stated conclusion holds](goal).-/
-- @node: stochastic_complex_eigenvector_nonconstant
lemma stochastic_complex_eigenvector_nonconstant (P : FourMatrix)
    (hP : IsStochasticMatrix P) {z : ℂ} (hz : z ≠ 1)
    {f : JointState 2 2 → ℂ} (hf0 : f ≠ 0)
    (hfe : Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f = z • f) :
    ∃ i j, f i ≠ f j := by
  classical
  by_contra hc
  have hc : ∀ i j, f i = f j := by simpa using hc
  let i : JointState 2 2 := (0, 0)
  have hconst : f = fun _ => f i := funext fun j => hc j i
  have hfi : f i ≠ 0 := by
    intro h
    apply hf0
    simpa [h, Pi.zero_def] using hconst
  have he : f i = z * f i := by
    have h := congrFun hfe i
    rw [hconst, stochastic_complex_constant P hP] at h
    simpa using h
  apply hz
  exact (mul_right_cancel₀ hfi (by simpa using he.symm : z * f i = 1 * f i))

/-- Nonconstant modes of a stochastic matrix lie in its Dobrushin disk. [Under the listed formal conditions](hyp:hP,hδ,hz,hf0,hfe), [the stated conclusion holds](goal).-/
-- @node: dobrushin_complex_eigenvector_norm_le
lemma dobrushin_complex_eigenvector_norm_le (P : FourMatrix)
    (hP : IsStochasticMatrix P) {alpha : ℝ} (hδ : dobrushin P ≤ alpha)
    {z : ℂ} (hz : z ≠ 1) {f : JointState 2 2 → ℂ} (hf0 : f ≠ 0)
    (hfe : Matrix.mulVec (P.map (algebraMap ℝ ℂ)) f = z • f) :
    ‖z‖ ≤ alpha := by
  obtain ⟨ij, hmax⟩ := Finite.exists_max
    (fun ij : JointState 2 2 × JointState 2 2 => ‖f ij.1 - f ij.2‖)
  have hdiam : ∀ i j, ‖f i - f j‖ ≤ ‖f ij.1 - f ij.2‖ := fun i j => hmax (i, j)
  obtain ⟨i, j, hij⟩ := stochastic_complex_eigenvector_nonconstant P hP hz hf0 hfe
  have hpos : 0 < ‖f ij.1 - f ij.2‖ :=
    (norm_pos_iff.mpr (sub_ne_zero.mpr hij)).trans_le (hdiam i j)
  have h := dobrushin_complex_diameter_contraction P hP hδ f hdiam ij.1 ij.2
  rw [hfe] at h
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_sub, norm_mul] at h
  exact le_of_mul_le_mul_right h hpos

/-- Every characteristic root other than one obeys the Dobrushin bound. [Under the listed formal conditions](hyp:hP,hδ,hz,hroot), [the stated conclusion holds](goal).-/
-- @node: dobrushin_complex_charpoly_root_norm_le
lemma dobrushin_complex_charpoly_root_norm_le (P : FourMatrix)
    (hP : IsStochasticMatrix P) {alpha : ℝ} (hδ : dobrushin P ≤ alpha)
    {z : ℂ} (hz : z ≠ 1)
    (hroot : Polynomial.IsRoot ((Matrix.charpoly P).map (algebraMap ℝ ℂ)) z) :
    ‖z‖ ≤ alpha := by
  have heig : Module.End.HasEigenvalue
      (P.map (algebraMap ℝ ℂ)).mulVecLin z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_mulVecLin,
      Matrix.charpoly_map]
    exact hroot
  obtain ⟨f, hf⟩ := heig.exists_hasEigenvector
  exact dobrushin_complex_eigenvector_norm_le P hP hδ hz hf.2 hf.apply_eq_smul

end CausalSmith.Stat.PomdpBinaryhiddenRate
