import CausalSmith.ExactID.EID_CovshiftProfilequotientTargets_Research.Basic
import Mathlib.Analysis.Matrix.LDL
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Causalean.Mathlib.LinearAlgebra.Cholesky

set_option linter.style.longLine false

/-! # Ordered LDL certificates and target fibers

This file defines the observable covariance algebra, its ordered certificate,
and the causal and algebraic target fibers.
-/

open scoped BigOperators
open Matrix

namespace CausalSmith.ExactID.CovshiftProfilequotientTargets

-- @env: S2
variable {d E r : ℕ}

/-- A tuple of symmetric population covariance matrices. -/
structure CovarianceTuple (d E : ℕ) where
  cov : Environment E → RealMatrix d -- @realizes theta(carrier (S^d)^{E+1}) @realizes Sigma(component carrier S^d)
  symmetric : ∀ e, (cov e).IsHermitian -- @realizes theta(symmetric components) @realizes Sigma(symmetric range)

/-- Covariance difference from the baseline environment. -/
def covarianceShift (θ : CovarianceTuple d E) (e : Environment E) : RealMatrix d :=
  θ.cov e - θ.cov 0 -- @realizes Delta(Delta_e = Sigma_e - Sigma_0; Delta_0 = 0)

/-- Sum of all nonbaseline covariance differences. -/
def aggregateShift (θ : CovarianceTuple d E) : RealMatrix d :=
  ∑ e : Fin E, covarianceShift θ e.succ -- @realizes Q(Qbar = sum nonbaseline Delta_e)

/-- An ordered tuple contains each member of `T` exactly once. -/
def Orders (t : Fin r → Fin d) (T : Finset (Fin d)) : Prop :=
  Function.Injective t ∧ Finset.univ.image t = T
  -- @realizes t(ordering of T with distinct labels)

/-- Coordinate-selection matrix associated with an ordering. -/
def selectionMatrix (t : Fin r → Fin d) : Matrix (Fin r) (Fin d) ℝ :=
  fun i j => if t i = j then 1 else 0
  -- @realizes Pt(selection matrix in {0,1}^{r×d})

/-- Ordered principal block of a square matrix. -/
def orderedPrincipalBlock (A : RealMatrix d) (t : Fin r → Fin d) : RealMatrix r :=
  selectionMatrix t * A * (selectionMatrix t).transpose
  -- @realizes Qtt(Qtt = Pt Q Pt^T)

/-- A matrix is diagonal. -/
def IsDiagonal (A : RealMatrix r) : Prop :=
  ∀ i j, i ≠ j → A i j = 0

/-- A matrix is entrywise nonnegative. -/
def EntrywiseNonnegative (A : RealMatrix r) : Prop :=
  ∀ i j, 0 ≤ A i j

/-- The transformed environment-specific target block. -/
noncomputable def transformedTargetBlock (θ : CovarianceTuple d E) (t : Fin r → Fin d)
    (hQ : (orderedPrincipalBlock (aggregateShift θ) t).PosDef)
    (e : Environment E) : RealMatrix r :=
  let L := LDL.lower hQ
  L⁻¹ * selectionMatrix t * covarianceShift θ e * (selectionMatrix t).transpose * (L⁻¹).transpose
  -- @realizes Lambdat(Lambda_e,t = Lt⁻¹ Pt Delta_e Pt^T Lt⁻T)

-- @node: ass:baseline-positive
def BaselinePositive (θ : CovarianceTuple d E) : Prop :=
  (θ.cov 0).PosDef -- @realizes SPDd(baseline covariance positive definite)

-- @node: ass:reference-exact-rank
def AggregateExactRank (θ : CovarianceTuple d E) (r : ℕ) : Prop :=
  (aggregateShift θ).rank = r

-- @node: ass:common-shift-range
def CommonShiftRange (θ : CovarianceTuple d E) : Prop :=
  ∀ e : Fin E,
    LinearMap.range (Matrix.mulVecLin (covarianceShift θ e.succ)) ≤
      LinearMap.range (Matrix.mulVecLin (aggregateShift θ))

-- @node: def:ordered-ldl-certificate
def Cert (θ : CovarianceTuple d E) (T : Finset (Fin d)) (t : Fin r → Fin d) : Prop :=
  Orders t T ∧
    ∃ hQ : (orderedPrincipalBlock (aggregateShift θ) t).PosDef,
      let L := LDL.lower hQ -- @realizes Lt(canonical unit-lower LDL factor)
      let D := LDL.diag hQ -- @realizes Dt(canonical positive diagonal LDL factor)
      orderedPrincipalBlock (aggregateShift θ) t = L * D * L.transpose ∧
      (∀ i, L i i = 1) ∧
      (∀ i j, i < j → L i j = 0) ∧
      (∀ i, 0 < D i i) ∧
      IsDiagonal D ∧
      ∀ e : Fin E,
        IsDiagonal (transformedTargetBlock θ t hQ e.succ) ∧
          EntrywiseNonnegative (transformedTargetBlock θ t hQ e.succ)
  -- @realizes Cert(ordered positive LDL certificate)

-- @node: def:causal-target-fiber
def causalTargetFiber (θ : CovarianceTuple d E) (r : ℕ) : Set (Finset (Fin d)) :=
  {T | T.card = r ∧
    ∃ M : CovShiftModel d E r, LegalCovShiftModel M ∧ M.target = T ∧
      ∀ e, M.covOf e = θ.cov e}
  -- @realizes Fcausal(target sets realized by a legal model)

-- @node: def:algebraic-target-fiber
def algebraicTargetFiber (θ : CovarianceTuple d E) (r : ℕ) : Set (Finset (Fin d)) :=
  {T | T.card = r ∧ ∃ t : Fin r → Fin d, Orders t T ∧ Cert θ T t}
  -- @realizes Falg(size-r sets admitting an ordered certificate)

/-- Labels appearing in every algebraically compatible target. -/
noncomputable def compulsoryLabels (θ : CovarianceTuple d E) (r : ℕ) : Finset (Fin d) :=
  by classical exact Finset.univ.filter fun j => ∀ T, T ∈ algebraicTargetFiber θ r → j ∈ T
  -- @realizes Comp(intersection of all algebraic targets)

/-- Labels appearing in at least one algebraically compatible target. -/
noncomputable def possibleLabels (θ : CovarianceTuple d E) (r : ℕ) : Finset (Fin d) :=
  by classical exact Finset.univ.filter fun j => ∃ T, T ∈ algebraicTargetFiber θ r ∧ j ∈ T
  -- @realizes Poss(union of all algebraic targets)

-- @node: def:complete-classification
noncomputable def completeClassification (θ : CovarianceTuple d E) (r : ℕ) :
    Finset (Fin d) × Finset (Fin d) :=
  (compulsoryLabels θ r, possibleLabels θ r)
  -- @realizes h(h(theta) = (Comp(theta), Poss(theta)))

-- @node: lem:range-reconstruction
lemma range_reconstruction (θ : CovarianceTuple d E) (r : ℕ)
    (hRank : AggregateExactRank θ r)
    (t : Fin r → Fin d)
    (hUnit : IsUnit (orderedPrincipalBlock (aggregateShift θ) t))
    (N : RealMatrix d) -- @realizes Nmat(generic symmetric matrix)
    (hNsymm : N.IsHermitian)
    (hNrange : LinearMap.range (Matrix.mulVecLin N) ≤
      LinearMap.range (Matrix.mulVecLin (aggregateShift θ)))
    (W : Matrix (Fin d) (Fin r) ℝ)
    (hW : W = aggregateShift θ * (selectionMatrix t).transpose *
      (orderedPrincipalBlock (aggregateShift θ) t)⁻¹) :
    N = W * (selectionMatrix t * N * (selectionMatrix t).transpose) * W.transpose := by
  let Q := aggregateShift θ
  let P := selectionMatrix t
  let K := Q * P.transpose
  have hKrange : LinearMap.range K.mulVecLin ≤ LinearMap.range Q.mulVecLin := by
    dsimp [K]
    rw [Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range (Matrix.mulVecLin P.transpose) (Matrix.mulVecLin Q)
  have hRankK : K.rank = r := by
    have hlo : r ≤ K.rank := by
      calc
        r = (orderedPrincipalBlock Q t).rank := by
          rw [Matrix.rank_of_isUnit _ hUnit]
          simp
        _ = (P * K).rank := by simp [orderedPrincipalBlock, Q, P, K, Matrix.mul_assoc]
        _ ≤ K.rank := Matrix.rank_mul_le_right P K
    have hhi : K.rank ≤ r := by
      calc
        K.rank ≤ Q.rank := Matrix.rank_mul_le_left Q P.transpose
        _ = r := hRank
    omega
  have hRangeEq : LinearMap.range K.mulVecLin = LinearMap.range Q.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_le hKrange
    change Q.rank ≤ K.rank
    rw [hRankK]
    simpa [Q, AggregateExactRank] using hRank.le
  letI := hUnit.invertible
  have hW' : W = K * (orderedPrincipalBlock Q t)⁻¹ := by
    simpa [K, Q, P] using hW
  have hPK : P * K = orderedPrincipalBlock Q t := by
    simp [P, K, Q, orderedPrincipalBlock, Matrix.mul_assoc]
  have hAction (x : Fin d → ℝ) (hx : x ∈ LinearMap.range Q.mulVecLin) :
      W *ᵥ (P *ᵥ x) = x := by
    rw [← hRangeEq] at hx
    rcases hx with ⟨y, rfl⟩
    rw [hW']
    simp only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    simp [hPK]
  have hLeft : W * (P * N) = N := by
    ext i j
    have hv := hAction (N *ᵥ Pi.single j 1) (hNrange ⟨Pi.single j 1, rfl⟩)
    have hv' : (W * (P * N)) *ᵥ Pi.single j 1 = N *ᵥ Pi.single j 1 := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact hv
    simpa [Matrix.mulVec_single] using congrFun hv' i
  have hRight : N * P.transpose * W.transpose = N := by
    have ht := congrArg Matrix.transpose hLeft
    have hNt : N.transpose = N := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
      exact hNsymm
    simpa [Matrix.transpose_mul, hNt, ← Matrix.mul_assoc] using ht
  calc
    N = W * (P * N) := hLeft.symm
    _ = W * (P * (N * P.transpose * W.transpose)) := by rw [hRight]
    _ = W * (P * N * P.transpose) * W.transpose := by simp [Matrix.mul_assoc]
    _ = W * (selectionMatrix t * N * (selectionMatrix t).transpose) * W.transpose := by
      rfl
  -- @realizes Wt(Wt = Q Pt^T Qtt⁻¹ and reconstructs N)

end CausalSmith.ExactID.CovshiftProfilequotientTargets
