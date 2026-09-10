import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Helpers.Certificate
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Causalean.Mathlib.StandardGaussian

set_option linter.defProp false

/-! # Positive-noise completion

The explicit matrix data used to complete an ordered certificate to a legal
Gaussian covariance-shift SCM.
-/

open scoped BigOperators MatrixOrder
open scoped Matrix.Norms.L2Operator
open Matrix MeasureTheory

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

variable {d E r : ℕ}

/-- The positive-definiteness witness retained by a certificate. -/
noncomputable def certificatePosDef {θ : CovarianceTuple d E} {T : Finset (Fin d)}
    {t : Fin r → Fin d} (h : Cert θ T t) :
    (orderedPrincipalBlock (aggregateShift θ) t).PosDef :=
  Classical.choose h.2

/-- Aggregate range-reconstruction matrix. -/
noncomputable def completionW (θ : CovarianceTuple d E) (t : Fin r → Fin d) :
    Matrix (Fin d) (Fin r) ℝ :=
  aggregateShift θ * (selectionMatrix t).transpose *
    (orderedPrincipalBlock (aggregateShift θ) t)⁻¹
  -- @realizes Wt(Wt = Q Pt^T Qtt⁻¹)

/-- Recovered changed columns. -/
noncomputable def completionA (θ : CovarianceTuple d E) (t : Fin r → Fin d)
    (h : Cert θ T t) : Matrix (Fin d) (Fin r) ℝ :=
  completionW θ t * LDL.lower (certificatePosDef h)
  -- @realizes At(At = Wt Lt)

/-- Completion with recovered target columns and identity off the target. -/
noncomputable def completionU (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) : RealMatrix d :=
  fun i j => if hj : j ∈ T then
      completionA θ t h i (Classical.choose (by
        have hord := h.1
        rw [← hord.2] at hj
        simpa using hj))
    else if i = j then 1 else 0
  -- @realizes Ut(unit-lower completion after placing t first)

/-- Completed acyclic structural matrix. -/
noncomputable def completionB (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) : RealMatrix d :=
  1 - (completionU θ T t h)⁻¹
  -- @realizes Bt(Bt = Id - Ut⁻¹)

/-- Minimum baseline eigenvalue used in the completion slack. -/
noncomputable def baselineMinimumEigenvalue (θ : CovarianceTuple d E) : ℝ :=
  sInf (Set.range (θ.symmetric 0).eigenvalues)

/-- Euclidean operator norm of the completed total-effect matrix. -/
noncomputable def completionOperatorNorm (θ : CovarianceTuple d E)
    (T : Finset (Fin d)) (t : Fin r → Fin d) (h : Cert θ T t) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (completionU θ T t h))‖

/-- Small positive structural and measurement-noise slack.  The baseline
positivity premise is part of the construction because it makes this choice
strictly positive. -/
noncomputable def completionSlack (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (_hBase : BaselinePositive θ) : ℝ :=
  baselineMinimumEigenvalue θ /
    (4 * (completionOperatorNorm θ T t h ^ 2 + 1))
  -- @realizes tau(positive scalar below the minimum-eigenvalue bound)

/-- The slack is positive and satisfies the paper's strict operator-norm bound. -/
lemma completionSlack_spec (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (hd : AdmissibleDimension d)
    (hBase : BaselinePositive θ) :
    0 < completionSlack θ T t h hBase ∧
      completionSlack θ T t h hBase <
        baselineMinimumEigenvalue θ /
          (2 * (completionOperatorNorm θ T t h ^ 2 + 1)) := by
  have hd0 : d ≠ 0 := by
    exact Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  let _ : NeZero d := ⟨hd0⟩
  have hmin : 0 < baselineMinimumEigenvalue θ := by
    rw [baselineMinimumEigenvalue, sInf_range]
    obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite
      (f := (θ.symmetric 0).eigenvalues)
    rw [← hi]
    exact hBase.eigenvalues_pos i
  have hop : 0 < completionOperatorNorm θ T t h ^ 2 + 1 := by
    positivity
  constructor
  · simp only [completionSlack]
    positivity
  · simp only [completionSlack]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    nlinarith

/-- Baseline covariance remainder after allocating positive primitive noises. -/
noncomputable def completionRzero (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (hBase : BaselinePositive θ) : RealMatrix d :=
  let τ := completionSlack θ T t h hBase
  θ.cov 0 - τ • (completionU θ T t h * (completionU θ T t h).transpose) - τ • 1
  -- @realizes Rzero(R0 = Sigma0 - tau Ut Ut^T - tau Id)

-- @node: baselineMinimumEigenvalue_smul_one_le
lemma baselineMinimumEigenvalue_smul_one_le (θ : CovarianceTuple d E)
    (hd : AdmissibleDimension d) (hBase : BaselinePositive θ) :
    baselineMinimumEigenvalue θ • (1 : RealMatrix d) ≤ θ.cov 0 := by
  have hd0 : d ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)
  let _ : NeZero d := ⟨hd0⟩
  let a := baselineMinimumEigenvalue θ
  change a • (1 : RealMatrix d) ≤ θ.cov 0
  rw [Matrix.le_iff]
  let U : RealMatrix d := (θ.symmetric 0).eigenvectorUnitary
  let D : RealMatrix d := Matrix.diagonal ((θ.symmetric 0).eigenvalues)
  have hspec : θ.cov 0 = U * D * star U := by
    simpa [U, D, Unitary.conjStarAlgAut_apply] using (θ.symmetric 0).spectral_theorem
  rw [hspec]
  have hmin (i : Fin d) : a ≤ (θ.symmetric 0).eigenvalues i := by
    simp only [a, baselineMinimumEigenvalue]
    exact csInf_le (Set.finite_range _).bddBelow ⟨i, rfl⟩
  simp only [sub_eq_add_neg, Matrix.smul_one_eq_diagonal] at *
  have hneg : -Matrix.diagonal (fun _ : Fin d => a) =
      Matrix.diagonal (fun _ : Fin d => -a) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  rw [hneg]
  have hconst : Matrix.diagonal (fun _ : Fin d => -a) =
      U * Matrix.diagonal (fun _ : Fin d => -a) * star U := by
    rw [show Matrix.diagonal (fun _ : Fin d => -a) = (-a) • (1 : RealMatrix d) by
      simp [Matrix.smul_one_eq_diagonal]]
    simp [U]
  rw [hconst]
  rw [show U * D * star U + U * Matrix.diagonal (fun _ : Fin d => -a) * star U =
      U * (D + Matrix.diagonal (fun _ : Fin d => -a)) * star U by noncomm_ring]
  have hU : IsUnit U := by
    dsimp [U]
    exact Unitary.isUnit_coe
  apply hU.posSemidef_star_right_conjugate_iff.mpr
  simp only [D, Matrix.diagonal_add, Matrix.posSemidef_diagonal_iff]
  intro i
  simpa [a] using hmin i

-- @node: mul_transpose_le_operatorNorm_sq_smul_one
lemma mul_transpose_le_operatorNorm_sq_smul_one (U : RealMatrix d) :
    U * U.transpose ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)‖ ^ 2 •
      (1 : RealMatrix d) := by
  rw [Matrix.le_iff]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (Matrix.isHermitian_one.smul (by rw [isSelfAdjoint_iff]; rfl)).sub (by
      simpa using Matrix.isHermitian_mul_conjTranspose_self U)
  intro x
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul]
  simp only [star_trivial]
  have hquad : x ⬝ᵥ ((U * U.transpose) *ᵥ x) =
      (U.transpose *ᵥ x) ⬝ᵥ (U.transpose *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec x U U.transpose, Matrix.dotProduct_mulVec]
    rw [show x ᵥ* U = U.transpose *ᵥ x by
      simpa using Matrix.vecMul_transpose U.transpose x]
  rw [hquad]
  have hop := Matrix.l2_opNorm_mulVec U.transpose
    ((EuclideanSpace.equiv (Fin d) ℝ).symm x)
  rw [show ‖U.transpose‖ = ‖U‖ by
    simpa using Matrix.l2_opNorm_conjTranspose U] at hop
  have hop2 :
      ‖((EuclideanSpace.equiv (Fin d) ℝ).symm
        (U.transpose *ᵥ ((EuclideanSpace.equiv (Fin d) ℝ).symm x).ofLp))‖ ^ 2 ≤
      (‖U‖ * ‖((EuclideanSpace.equiv (Fin d) ℝ).symm x)‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hop
  have hxnorm : ‖((EuclideanSpace.equiv (Fin d) ℝ).symm x)‖ ^ 2 = x ⬝ᵥ x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, x i ^ 2) = ∑ i, x i * x i
    simp only [pow_two]
  have hutnorm :
      ‖((EuclideanSpace.equiv (Fin d) ℝ).symm
        (U.transpose *ᵥ ((EuclideanSpace.equiv (Fin d) ℝ).symm x).ofLp))‖ ^ 2 =
        (U.transpose *ᵥ x) ⬝ᵥ (U.transpose *ᵥ x) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ i, (U.transpose *ᵥ x) i ^ 2) =
      ∑ i, (U.transpose *ᵥ x) i * (U.transpose *ᵥ x) i
    simp only [pow_two]
  rw [hutnorm, mul_pow, hxnorm] at hop2
  change 0 ≤ ‖U‖ ^ 2 * (x ⬝ᵥ x) -
    (U.transpose *ᵥ x) ⬝ᵥ (U.transpose *ᵥ x)
  exact sub_nonneg.mpr hop2

/-- The baseline remainder is positive semidefinite under the specified slack bound. -/
-- @node: completionRzero_posSemidef
lemma completionRzero_posSemidef (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (hd : AdmissibleDimension d)
    (hBase : BaselinePositive θ) :
    (completionRzero θ T t h hBase).PosSemidef := by
  let τ := completionSlack θ T t h hBase
  let U := completionU θ T t h
  let N := completionOperatorNorm θ T t h
  let a := baselineMinimumEigenvalue θ
  have hτ := completionSlack_spec θ T t h hd hBase
  have hp : 0 < N ^ 2 + 1 := by positivity
  have hsmall : τ * (N ^ 2 + 1) < a / 2 := by
    calc
      τ * (N ^ 2 + 1) < (a / (2 * (N ^ 2 + 1))) * (N ^ 2 + 1) :=
        mul_lt_mul_of_pos_right hτ.2 hp
      _ = a / 2 := by field_simp
  have ha : 0 < a := by
    have hq : 0 < a / (2 * (N ^ 2 + 1)) := lt_trans hτ.1 hτ.2
    rcases (div_pos_iff.mp hq) with hpos | hneg
    · exact hpos.1
    · exfalso
      exact (not_lt_of_ge (by positivity : 0 ≤ 2 * (N ^ 2 + 1))) hneg.2
  have hcoeff : τ * (N ^ 2 + 1) ≤ a := by nlinarith
  have hU : U * U.transpose ≤ N ^ 2 • (1 : RealMatrix d) := by
    simpa [U, N, completionOperatorNorm] using
      mul_transpose_le_operatorNorm_sq_smul_one U
  have hτU : τ • (U * U.transpose) ≤ τ • (N ^ 2 • (1 : RealMatrix d)) :=
    smul_le_smul_of_nonneg_left hU hτ.1.le
  have hsum : τ • (U * U.transpose) + τ • (1 : RealMatrix d) ≤ a • 1 := by
    calc
      τ • (U * U.transpose) + τ • (1 : RealMatrix d) ≤
          τ • (N ^ 2 • (1 : RealMatrix d)) + τ • (1 : RealMatrix d) :=
        add_le_add hτU (le_refl _)
      _ = (τ * (N ^ 2 + 1)) • (1 : RealMatrix d) := by
        ext i j
        by_cases hij : i = j <;> simp [smul_smul, Matrix.one_apply, hij] <;> ring
      _ ≤ a • (1 : RealMatrix d) := by
        rw [Matrix.le_iff]
        simp only [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub,
          Matrix.posSemidef_diagonal_iff]
        intro i
        simpa using hcoeff
  have hbase := baselineMinimumEigenvalue_smul_one_le θ hd hBase
  have htotal : τ • (U * U.transpose) + τ • (1 : RealMatrix d) ≤ θ.cov 0 :=
    le_trans hsum hbase
  rw [Matrix.le_iff] at htotal
  simpa [completionRzero, τ, U, sub_sub] using htotal

/-- Latent loading obtained from the positive-semidefinite square root of the remainder. -/
noncomputable def completionC (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (hBase : BaselinePositive θ) : RealMatrix d :=
  (completionU θ T t h)⁻¹ * CFC.sqrt (completionRzero θ T t h hBase)
  -- @realizes Ct(Ct = Ut⁻¹ Rzero^{1/2})

/-- All explicit algebraic data of the positive-noise completion. -/
structure PositiveNoiseCompletionData (d E r : ℕ) where
  target : Finset (Fin d)
  ordering : Fin r → Fin d
  W : Matrix (Fin d) (Fin r) ℝ
  A : Matrix (Fin d) (Fin r) ℝ
  U : RealMatrix d
  B : RealMatrix d
  covariance : CovarianceTuple d E
  operatorNorm : ℝ
  τ : ℝ
  τ_pos : 0 < τ
  τ_operator_bound : τ < baselineMinimumEigenvalue (d := d) covariance /
    (2 * (operatorNorm ^ 2 + 1))
  R0 : RealMatrix d
  R0_posSemidef : R0.PosSemidef
  C : RealMatrix d
  latentLaw : Environment E → Measure (EuclideanSpace ℝ (Fin d))
  latentGaussian : ∀ e, ProbabilityTheory.IsGaussian (latentLaw e)
  latentMeanZero : ∀ e, ∫ x, x ∂latentLaw e = 0
  latentCovarianceIdentity : ∀ e u v,
    ProbabilityTheory.covarianceBilin (latentLaw e) u v = inner ℝ u v
  baselineStructuralCovariance : RealMatrix d
  baselineMeasurementCovariance : RealMatrix d
  increments : Environment E → Fin d → ℝ

-- @node: def:positive-noise-completion
noncomputable def positiveNoiseCompletion (θ : CovarianceTuple d E) (T : Finset (Fin d))
    (t : Fin r → Fin d) (h : Cert θ T t) (hd : AdmissibleDimension d)
    (hBase : BaselinePositive θ) :
    PositiveNoiseCompletionData d E r where
  target := T
  ordering := t
  W := completionW θ t
  A := completionA θ t h
  U := completionU θ T t h
  B := completionB θ T t h
  τ := completionSlack θ T t h hBase
  τ_pos := (completionSlack_spec θ T t h hd hBase).1
  covariance := θ
  operatorNorm := completionOperatorNorm θ T t h
  τ_operator_bound := (completionSlack_spec θ T t h hd hBase).2
  R0 := completionRzero θ T t h hBase
  R0_posSemidef := completionRzero_posSemidef θ T t h hd hBase
  C := completionC θ T t h hBase
  latentLaw _ := Causalean.Mathlib.stdGaussian (EuclideanSpace ℝ (Fin d))
  latentGaussian _ := inferInstance
  latentMeanZero _ := Causalean.Mathlib.stdGaussian_mean
  latentCovarianceIdentity _ := Causalean.Mathlib.covarianceBilin_stdGaussian
  baselineStructuralCovariance := completionSlack θ T t h hBase • (1 : RealMatrix d)
  baselineMeasurementCovariance := completionSlack θ T t h hBase • (1 : RealMatrix d)
  increments e j := if hj : j ∈ T then
    transformedTargetBlock θ t (certificatePosDef h) e
      (Classical.choose (by simpa [← h.1.2] using hj))
      (Classical.choose (by simpa [← h.1.2] using hj))
    else 0

/-- A raw SCM realizes the matrices and positive primitive-noise allocation of a completion. -/
def CompletionRealizes (D : PositiveNoiseCompletionData d E r)
    (M : CovShiftModel d E r) : Prop :=
  M.target = D.target ∧ M.B = D.B ∧ M.C = D.C ∧
    Matrix.diagonal M.ω0 = D.baselineStructuralCovariance ∧
    M.Ωη = D.baselineMeasurementCovariance ∧
      M.shiftVariance = D.increments

end CausalSmith.ExactID.CovshiftProfilequotientTargets
