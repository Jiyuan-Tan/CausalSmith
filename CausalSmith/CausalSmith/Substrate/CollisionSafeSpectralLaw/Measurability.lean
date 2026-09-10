import CausalSmith.Substrate.CollisionSafeSpectralLaw.MoorePenrose
import Causalean.Mathlib.Analysis.SingularValueWeyl
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Instances.Matrix

/-!
# Borel prerequisites for finite-dimensional spectral algorithms

This module contains topology and measurability facts that do not depend on the proxy model or
on a particular statistical construction.
-/

namespace CausalSmith.Substrate.CollisionSafeSpectralLaw

open scoped Matrix.Norms.L2Operator

noncomputable local instance {rows cols : ℕ} : MeasurableSpace (RectMatrix rows cols) :=
  borel _

local instance {rows cols : ℕ} : BorelSpace (RectMatrix rows cols) := ⟨rfl⟩

/-- Converting a finite real matrix to its Euclidean continuous linear map is continuous. -/
@[fun_prop] lemma matrixCLM_continuous {rows cols : ℕ} :
    Continuous (@matrixCLM rows cols) := by
  let f : RectMatrix rows cols →ₗ[ℝ] (Euc cols →L[ℝ] Euc rows) :=
    { toFun := matrixCLM
      map_add' := by
        intro A B
        ext x i
        simp [matrixCLM, Matrix.toEuclideanLin_apply]
      map_smul' := by
        intro c A
        ext x i
        simp [matrixCLM, Matrix.toEuclideanLin_apply] }
  exact f.continuous_of_finiteDimensional

/-- Every fixed singular-value coordinate is continuous on the continuous-linear-map space. -/
lemma continuous_singularValues_apply {rows cols j : ℕ} :
    Continuous (fun T : Euc cols →L[ℝ] Euc rows => T.toLinearMap.singularValues j) := by
  rw [continuous_iff_continuousAt]
  intro T
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro S hST
  rw [Real.dist_eq]
  have hw :=
    Causalean.Mathlib.Analysis.abs_singularValues_add_sub_singularValues_le_opNorm
      T.toLinearMap (S - T).toLinearMap j
  have hadd : T + (S - T) = S := by abel
  rw [show T.toLinearMap + (S - T).toLinearMap = S.toLinearMap by
    simpa only [ContinuousLinearMap.coe_add, ContinuousLinearMap.coe_sub] using
      congrArg ContinuousLinearMap.toLinearMap hadd] at hw
  have hclm : LinearMap.toContinuousLinearMap (S - T).toLinearMap = S - T := by
    ext x
    rfl
  rw [hclm] at hw
  exact lt_of_le_of_lt hw (by simpa [dist_eq_norm] using hST)

/-- Every fixed singular value of a finite real rectangular matrix is continuous, hence Borel
measurable. -/
lemma singularValue_continuous {rows cols j : ℕ} :
    Continuous (fun A : RectMatrix rows cols => singularValue A j) := by
  have h := (continuous_singularValues_apply (rows := rows) (cols := cols) (j := j)).comp
    (matrixCLM_continuous (rows := rows) (cols := cols))
  convert h using 1
  funext A
  rfl

lemma singularValue_measurable {rows cols j : ℕ} :
    Measurable (fun A : RectMatrix rows cols => singularValue A j) :=
  singularValue_continuous.measurable

/-- The finite mask of singular directions retained by a hard threshold. -/
noncomputable def singularThresholdMask {rows cols : ℕ} (threshold : ℝ)
    (A : RectMatrix rows cols) : Finset (Fin cols) :=
  Finset.univ.filter fun j => threshold ≤ singularValue A j

/-- Every fixed hard-threshold mask is a Borel stratum.  Thus the discontinuity at equality is
still Borel; the convention `threshold ≤ σ` is represented by a closed inequality. -/
lemma measurableSet_singularThresholdMask_eq {rows cols : ℕ} (threshold : ℝ)
    (mask : Finset (Fin cols)) :
    MeasurableSet {A : RectMatrix rows cols | singularThresholdMask threshold A = mask} := by
  classical
  have hset : {A : RectMatrix rows cols | singularThresholdMask threshold A = mask} =
      ⋂ j : Fin cols, if j ∈ mask then {A | threshold ≤ singularValue A j}
        else {A | singularValue A j < threshold} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_iInter, singularThresholdMask,
      Finset.ext_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h j
      specialize h j
      by_cases hj : j ∈ mask
      · simp only [hj, if_pos, Set.mem_setOf_eq]
        exact h.mpr hj
      · simp only [hj, if_neg, Set.mem_setOf_eq]
        exact lt_of_not_ge fun hle => hj (h.mp hle)
    · intro h j
      specialize h j
      by_cases hj : j ∈ mask
      · simp only [hj, if_pos, Set.mem_setOf_eq] at h
        exact ⟨fun _ => hj, fun _ => h⟩
      · simp only [hj, if_neg, Set.mem_setOf_eq] at h
        exact ⟨fun hle => (not_le_of_gt h) hle |>.elim, fun hmem => (hj hmem).elim⟩
  rw [hset]
  apply MeasurableSet.iInter
  intro j
  split_ifs
  · simpa only [Set.preimage, Set.mem_Ici] using
      (singularValue_measurable (rows := rows) (cols := cols) (j := j)) measurableSet_Ici
  · simpa only [Set.preimage, Set.mem_Iio] using
      (singularValue_measurable (rows := rows) (cols := cols) (j := j)) measurableSet_Iio

/-- A rational approximation to the hard-thresholded inverse.  The index `m` represents the
positive exponent `m + 1`; this convention avoids a special zeroth term in the approximating
sequence. -/
noncomputable def rationalThresholdApprox {rows cols : ℕ} (threshold : ℝ) (m : ℕ)
    (A : RectMatrix rows cols) : RectMatrix cols rows :=
  let G := A.transpose * A
  let q := m + 1
  let a := threshold ^ (2 * q) / (q : ℝ)
  G ^ m * (G ^ q + a • (1 : RectMatrix cols cols))⁻¹ * A.transpose

private lemma rationalThresholdDenominator_posDef {rows cols : ℕ} {threshold : ℝ}
    (hthreshold : 0 < threshold) (m : ℕ) (A : RectMatrix rows cols) :
    let G := A.transpose * A
    let q := m + 1
    let a := threshold ^ (2 * q) / (q : ℝ)
    (G ^ q + a • (1 : RectMatrix cols cols)).PosDef := by
  dsimp only
  have hG : (A.transpose * A).PosSemidef := by
    have heq : A.conjTranspose = A.transpose := by
      ext i j
      simp [Matrix.conjTranspose_apply]
    rw [← heq]
    exact Matrix.posSemidef_conjTranspose_mul_self A
  have ha : 0 < threshold ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ) := by positivity
  exact Matrix.PosDef.posSemidef_add (hG.pow (m + 1)) (Matrix.PosDef.one.smul ha)

/-- Every rational approximant is continuous.  Positivity of the regularization makes the
matrix denominator invertible for every input matrix. -/
lemma rationalThresholdApprox_continuous {rows cols : ℕ} {threshold : ℝ}
    (hthreshold : 0 < threshold) (m : ℕ) :
    Continuous (rationalThresholdApprox (rows := rows) (cols := cols) threshold m) := by
  rw [continuous_iff_continuousAt]
  intro A
  let G : RectMatrix cols cols := A.transpose * A
  let q := m + 1
  let a := threshold ^ (2 * q) / (q : ℝ)
  let D : RectMatrix cols cols := G ^ q + a • 1
  have hD : D.PosDef := by
    simpa only [G, q, a, D] using rationalThresholdDenominator_posDef hthreshold m A
  have hdet : D.det ≠ 0 := by
    exact ((Matrix.isUnit_iff_isUnit_det D).mp hD.isUnit).ne_zero
  have hDcont : ContinuousAt
      (fun B : RectMatrix rows cols =>
        (B.transpose * B) ^ (m + 1) +
          (threshold ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)) • 1) A := by
    fun_prop
  have hinv : ContinuousAt
      (fun B : RectMatrix rows cols =>
        ((B.transpose * B) ^ (m + 1) +
          (threshold ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)) • 1)⁻¹) A := by
    apply (continuousAt_matrix_inv D (by simpa using continuousAt_inv₀ hdet)).comp
    simpa only [D, G, q, a] using hDcont
  unfold rationalThresholdApprox
  have hpow : ContinuousAt
      (fun B : RectMatrix rows cols => (B.transpose * B) ^ m) A := by
    fun_prop
  have hleft : ContinuousAt
      (fun B : RectMatrix rows cols =>
        (B.transpose * B) ^ m *
          ((B.transpose * B) ^ (m + 1) +
            (threshold ^ (2 * (m + 1)) / ((m + 1 : ℕ) : ℝ)) • 1)⁻¹) A :=
    hpow.mul hinv
  have htranspose : ContinuousAt (fun B : RectMatrix rows cols => B.transpose) A := by
    fun_prop
  have hmul : Continuous
      (fun p : RectMatrix cols cols × RectMatrix cols rows => p.1 * p.2) :=
    continuous_fst.matrix_mul continuous_snd
  exact hmul.continuousAt.comp (hleft.prodMk htranspose)

lemma rationalThresholdApprox_measurable {rows cols : ℕ} {threshold : ℝ}
    (hthreshold : 0 < threshold) (m : ℕ) :
    Measurable (rationalThresholdApprox (rows := rows) (cols := cols) threshold m) :=
  (rationalThresholdApprox_continuous hthreshold m).measurable

/-- Any pointwise limit of the canonical rational hard-threshold approximants is Borel
measurable.  This is the reusable analytic interface: a concrete SVD implementation need only
identify itself as that pointwise limit. -/
lemma measurable_of_rationalThresholdApprox_tendsto {rows cols : ℕ} {threshold : ℝ}
    (hthreshold : 0 < threshold) {f : RectMatrix rows cols → RectMatrix cols rows}
    (hlim : ∀ A, Filter.Tendsto (fun m => rationalThresholdApprox threshold m A)
      Filter.atTop (nhds (f A))) :
    Measurable f := by
  apply measurable_of_tendsto_metrizable
    (fun m => rationalThresholdApprox_measurable hthreshold m)
  rw [tendsto_pi_nhds]
  exact hlim

end CausalSmith.Substrate.CollisionSafeSpectralLaw
