import Causalean.Mathlib.Analysis.RectangularSignalSingularValues
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite tensors, contractions, and quantitative norms

This module fixes paper-independent array models for finite real tensors and factor matrices.
It defines rank-one tensor powers, degree lifts, Frobenius norms, contraction against a family
of probes, and the exact contracted factorization used by tensor-pencil arguments.
-/

namespace Causalean.Mathlib.Analysis.SymmetricTensorPencil

open scoped BigOperators

/-- A finite real vector with `p` coordinates. With [its explicit inputs](hyp:p), [the defined object](goal) is [given by the displayed formula](step:1). -/
abbrev Vec (p : ℕ) := Fin p → ℝ

/-- A real matrix whose `n` columns are vectors with `p` coordinates. With [its explicit inputs](hyp:p,n), [the defined object](goal) is [given by the displayed formula](step:1). -/
abbrev FactorMatrix (p n : ℕ) := Matrix (Fin p) (Fin n) ℝ

/-- An order-`r` real tensor on a `p`-dimensional coordinate space, represented as an array. With [its explicit inputs](hyp:p,r), [the defined object](goal) is [given by the displayed formula](step:1). -/
abbrev Tensor (p r : ℕ) := (Fin r → Fin p) → ℝ

/-- The ordered multi-index space used for a degree-`d` tensor-power lift. With [its explicit inputs](hyp:p,d), [the defined object](goal) is [given by the displayed formula](step:1). -/
abbrev LiftIndex (p d : ℕ) := Fin d → Fin p

/-- The Euclidean/Frobenius norm of a finite real array. With [its explicit inputs](hyp:x), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def finiteFrobeniusNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, (x i) ^ 2)

/-- The Frobenius norm of a finite real matrix. With [its explicit inputs](hyp:A), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def matrixFrobeniusNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : ℝ :=
  finiteFrobeniusNorm (fun x : ι × κ => A x.1 x.2)

/-- The Euclidean operator norm of a finite real square matrix. With [its explicit inputs](hyp:A), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def squareOperatorNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)) A‖

/-- The last domain-indexed singular value of a finite real matrix. With [its explicit inputs](hyp:A), [the defined object](goal) is [given by the displayed formula](step:1). -/
noncomputable def leastColumnSingularValue {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (A : Matrix ι κ ℝ) : ℝ :=
  A.toEuclideanLin.singularValues (Fintype.card κ - 1)

/-- The Euclidean dot product of two finite real vectors. With [its explicit inputs](hyp:x,y), [the defined object](goal) is [given by the displayed formula](step:1). -/
def dot {p : ℕ} (x y : Vec p) : ℝ := ∑ i, x i * y i

/-- The order-`r` rank-one tensor power of a vector. With [its explicit inputs](hyp:r,c), [the defined object](goal) is [given by the displayed formula](step:1). -/
def rankOneTensor (r : ℕ) {p : ℕ} (c : Vec p) : Tensor p r :=
  fun I => ∏ k, c (I k)

/-- The symmetric tensor represented by weighted rank-one tensor powers of the columns. With [its explicit inputs](hyp:r,C,lam), [the defined object](goal) is [given by the displayed formula](step:1). -/
def decompositionTensor {p n : ℕ} (r : ℕ) (C : FactorMatrix p n)
    (lam : Fin n → ℝ) : Tensor p r :=
  fun I => ∑ j, lam j * rankOneTensor r (C.col j) I

/-- The matrix whose columns are the ordered degree-`d` tensor powers of the factor columns. With [its explicit inputs](hyp:d,C), [the defined object](goal) is [given by the displayed formula](step:1). -/
def liftedDirections {p n : ℕ} (d : ℕ) (C : FactorMatrix p n) :
    Matrix (LiftIndex p d) (Fin n) ℝ :=
  fun I j => ∏ k, C (I k) j

/-- Concatenate two degree-`d` indices and one degree-`q` index into an order-`d+d+q` index. With [its explicit inputs](hyp:I,J,K), [the defined object](goal) is [given by the displayed formula](step:1). -/
def blockIndex {p d q : ℕ} (I J : LiftIndex p d) (K : Fin q → Fin p) :
    Fin (d + d + q) → Fin p :=
  Fin.addCases (Fin.addCases I J) K

/-- Contract the final `q` modes of an order-`d+d+q` tensor against a family of `q` probes. With [its explicit inputs](hyp:T,probes), [the defined object](goal) is [given by the displayed formula](step:1). -/
def contractLast {p d q : ℕ} (T : Tensor p (d + d + q))
    (probes : Fin q → Vec p) : Matrix (LiftIndex p d) (LiftIndex p d) ℝ :=
  fun I J => ∑ K : Fin q → Fin p,
    T (blockIndex I J K) * ∏ a, probes a (K a)

/-- The probe family containing `q-1` copies of `u` followed by one copy of `w`. With [its explicit inputs](hyp:u,w), [the defined object](goal) is [given by the displayed formula](step:1). -/
def pencilProbes {p q : ℕ} (u w : Vec p) : Fin q → Vec p :=
  fun a => if a.1 + 1 = q then w else u

/-- Splitting a finite function at an additive boundary is an equivalence. -/
private def finFunctionAddEquiv (a b : ℕ) (γ : Type*) :
    ((Fin a → γ) × (Fin b → γ)) ≃ (Fin (a + b) → γ) where
  toFun x := Fin.addCases x.1 x.2
  invFun x := (fun i => x (Fin.castAdd b i), fun j => x (Fin.natAdd a j))
  left_inv x := by ext i <;> simp
  right_inv x := by
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp
    · intro j
      simp

/-- The three blocks used by `blockIndex` enumerate every full tensor index exactly once. -/
private def blockIndexEquiv (p d q : ℕ) :
    (((Fin d → Fin p) × (Fin d → Fin p)) × (Fin q → Fin p)) ≃
      (Fin (d + d + q) → Fin p) :=
  (Equiv.prodCongr (finFunctionAddEquiv d d (Fin p)) (Equiv.refl _)).trans
    (finFunctionAddEquiv (d + d) q (Fin p))

/-- The Euclidean operator norm of a finite real square matrix is at most its entrywise
Frobenius norm. [The stated conclusion follows](goal). -/
theorem squareOperatorNorm_le_matrixFrobenius {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : squareOperatorNorm A ≤ matrixFrobeniusNorm A := by
  rw [squareOperatorNorm]
  calc
    _ ≤ @norm (Matrix ι ι ℝ) Matrix.frobeniusNormedAddCommGroup.toNorm A := by
      open scoped Matrix.Norms.Frobenius in
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
        have hmul := Matrix.frobenius_norm_mul A
          (Matrix.replicateCol Unit (WithLp.ofLp x))
        have heq :
            A * Matrix.replicateCol Unit (WithLp.ofLp x) =
              Matrix.replicateCol Unit (Matrix.mulVec A (WithLp.ofLp x)) := by
          ext i u
          simp [Matrix.mul_apply, Matrix.mulVec, Matrix.replicateCol, dotProduct]
        rw [heq, Matrix.frobenius_norm_replicateCol] at hmul
        rw [← Matrix.toEuclideanCLM_toLp A (WithLp.ofLp x), WithLp.toLp_ofLp] at hmul
        simpa using hmul
    _ = matrixFrobeniusNorm A := by
      rw [Matrix.frobenius_norm_def, matrixFrobeniusNorm, finiteFrobeniusNorm,
        Real.sqrt_eq_rpow, Fintype.sum_prod_type]
      simp only [Real.rpow_two, Real.norm_eq_abs, sq_abs]

/-- Contracting a finite tensor against probes of norm at most one cannot increase its
Frobenius norm. Under [the listed assumptions](hyp:hprobes), [the stated conclusion follows](goal). -/
-- Proof route: identify each contraction as an inner product in the product probe index,
-- apply finite Cauchy--Schwarz, and sum the squared bounds over the two free index blocks.
theorem contractLast_frobeniusNorm_le {p d q : ℕ} (T : Tensor p (d + d + q))
    (probes : Fin q → Vec p)
    (hprobes : ∀ a, finiteFrobeniusNorm (probes a) ≤ 1) :
    matrixFrobeniusNorm (contractLast T probes) ≤ finiteFrobeniusNorm T := by
  have hsingle (a : Fin q) : ∑ i, probes a i ^ 2 ≤ 1 := by
    have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num)).2 (hprobes a)
    simpa [finiteFrobeniusNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using hsq
  have henergy :
      ∑ K : Fin q → Fin p, (∏ a, probes a (K a)) ^ 2 ≤ 1 := by
    calc
      _ = ∏ a, ∑ i, probes a i ^ 2 := by
        calc
          _ = ∑ K : Fin q → Fin p, ∏ a, probes a (K a) ^ 2 := by
            apply Finset.sum_congr rfl
            intro K _
            rw [Finset.prod_pow]
          _ = _ := (Fintype.prod_sum
            (fun a : Fin q => fun i : Fin p => probes a i ^ 2)).symm
      _ ≤ 1 := Finset.prod_le_one
        (fun a _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
        (fun a _ => hsingle a)
  have hpoint (I J : LiftIndex p d) :
      (contractLast T probes I J) ^ 2 ≤
        ∑ K : Fin q → Fin p, T (blockIndex I J K) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q → Fin p))
      (fun K => T (blockIndex I J K)) (fun K => ∏ a, probes a (K a))
    have hrow : 0 ≤ ∑ K : Fin q → Fin p, T (blockIndex I J K) ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      _ ≤ (∑ K : Fin q → Fin p, T (blockIndex I J K) ^ 2) *
          (∑ K : Fin q → Fin p, (∏ a, probes a (K a)) ^ 2) := by
        simpa [contractLast] using hcs
      _ ≤ (∑ K : Fin q → Fin p, T (blockIndex I J K) ^ 2) * 1 :=
        mul_le_mul_of_nonneg_left henergy hrow
      _ = _ := mul_one _
  rw [matrixFrobeniusNorm, finiteFrobeniusNorm, finiteFrobeniusNorm]
  apply Real.sqrt_le_sqrt
  change (∑ x : LiftIndex p d × LiftIndex p d,
      (contractLast T probes x.1 x.2) ^ 2) ≤ ∑ L, T L ^ 2
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ I, ∑ J, ∑ K : Fin q → Fin p, T (blockIndex I J K) ^ 2 := by
      exact Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun J _ => hpoint I J
    _ = ∑ x : (LiftIndex p d × LiftIndex p d) × (Fin q → Fin p),
        T (blockIndex x.1.1 x.1.2 x.2) ^ 2 := by
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    _ = _ := (blockIndexEquiv p d q).sum_comp (fun L => T L ^ 2)

/-- The operator norm of a contracted tensor is bounded by the original tensor's Frobenius
norm when every contraction probe has norm at most one. Under [the listed assumptions](hyp:hprobes), [the stated conclusion follows](goal). -/
-- Proof route: first bound the square-matrix operator norm by its Frobenius norm, then invoke
-- `contractLast_frobeniusNorm_le`.
theorem contractLast_operatorNorm_le {p d q : ℕ} (T : Tensor p (d + d + q))
    (probes : Fin q → Vec p)
    (hprobes : ∀ a, finiteFrobeniusNorm (probes a) ≤ 1) :
    squareOperatorNorm (contractLast T probes) ≤ finiteFrobeniusNorm T := by
  exact (squareOperatorNorm_le_matrixFrobenius (contractLast T probes)).trans
    (contractLast_frobeniusNorm_le T probes hprobes)

/-- Contracting a weighted symmetric rank-one decomposition against `q-1` copies of `u` and
one copy of `w` gives the lifted factor matrix times the corresponding diagonal loadings times
its transpose. Under [the listed assumptions](hyp:hq), [the stated conclusion follows](goal). -/
-- Proof route: ext the two free multi-indices, unfold both matrix products and the tensor sum,
-- swap finite sums, and factor each probe sum into a dot product.
theorem contractLast_decompositionTensor {p n d q : ℕ} (hq : 0 < q)
    (C : FactorMatrix p n) (lam : Fin n → ℝ) (u w : Vec p) :
    contractLast (decompositionTensor (d + d + q) C lam) (pencilProbes u w) =
      liftedDirections d C * Matrix.diagonal (fun j =>
        lam j * dot u (C.col j) ^ (q - 1) * dot w (C.col j)) *
          (liftedDirections d C).transpose := by
  classical
  ext I J
  rw [Matrix.mul_apply]
  simp_rw [Matrix.mul_diagonal, Matrix.transpose_apply]
  rw [contractLast]
  simp_rw [decompositionTensor, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hrank (K : Fin q → Fin p) :
      rankOneTensor (d + d + q) (C.col j) (blockIndex I J K) =
        liftedDirections d C I j * liftedDirections d C J j * ∏ a, C (K a) j := by
    rw [rankOneTensor, Fin.prod_univ_add, Fin.prod_univ_add]
    simp only [Matrix.col_apply]
    congr 1
    · congr 1
      · apply Finset.prod_congr rfl
        intro i _
        simp [blockIndex]
      · apply Finset.prod_congr rfl
        intro i _
        simp only [blockIndex, Fin.addCases_left]
        rw [Fin.addCases_right]
    · apply Finset.prod_congr rfl
      intro i _
      simp [blockIndex]
  simp_rw [hrank]
  have hprobe :
      (∑ K : Fin q → Fin p, (∏ a, C (K a) j) *
          ∏ a, pencilProbes u w a (K a)) =
        dot u (C.col j) ^ (q - 1) * dot w (C.col j) := by
    calc
      _ = ∑ K : Fin q → Fin p, ∏ a,
          (C (K a) j * pencilProbes u w a (K a)) := by
        apply Finset.sum_congr rfl
        intro K _
        rw [Finset.prod_mul_distrib]
      _ = ∏ a, ∑ i, C i j * pencilProbes u w a i := (Fintype.prod_sum
        (fun a : Fin q => fun i : Fin p => C i j * pencilProbes u w a i)).symm
      _ = _ := by
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
        rw [Fin.prod_univ_castSucc]
        simp only [pencilProbes]
        have hcast (a : Fin r) : ¬(a.castSucc.1 + 1 = r + 1) := by
          change ¬(a.1 + 1 = r + 1)
          have ha := a.isLt
          omega
        simp_rw [hcast, if_false]
        simp only [Fin.val_last, if_true]
        simp [dot, Finset.prod_const, mul_comm]
  calc
    _ = (lam j * liftedDirections d C I j * liftedDirections d C J j) *
        (∑ K : Fin q → Fin p, (∏ a, C (K a) j) *
          ∏ a, pencilProbes u w a (K a)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro K _
      ring
    _ = _ := by rw [hprobe]; ring

/-- Unit columns have unit degree-`d` tensor lifts for every positive lifting degree. Under [the listed assumptions](hyp:hd,hunit), [the stated conclusion follows](goal). -/
-- Proof route: square the norm, factor the sum over functions `Fin d → Fin p` as a product of
-- coordinate sums, and use the unit-column hypothesis in every factor.
theorem finiteFrobeniusNorm_liftedColumn_eq_one {p n d : ℕ} (hd : 0 < d)
    (C : FactorMatrix p n) (hunit : ∀ j, finiteFrobeniusNorm (C.col j) = 1) (j : Fin n) :
    finiteFrobeniusNorm ((liftedDirections d C).col j) = 1 := by
  have hs : (∑ i, C i j ^ 2) = 1 := by
    have h := congrArg (fun z : ℝ => z ^ 2) (hunit j)
    simpa [finiteFrobeniusNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
  rw [finiteFrobeniusNorm]
  have hp := show (∑ I : Fin d → Fin p, (∏ k, C (I k) j) ^ 2) =
      (∑ i, C i j ^ 2) ^ d by
    calc
      _ = ∑ I : Fin d → Fin p, ∏ k, C (I k) j ^ 2 := by
        apply Finset.sum_congr rfl
        intro I _
        rw [Finset.prod_pow]
      _ = ∏ _k : Fin d, ∑ i, C i j ^ 2 := (Fintype.prod_sum
        (fun _k : Fin d => fun i : Fin p => C i j ^ 2)).symm
      _ = _ := by simp
  change Real.sqrt (∑ I : Fin d → Fin p, (∏ k, C (I k) j) ^ 2) = 1
  rw [hp, hs]
  simp

/-- The Frobenius norm of a lifted factor matrix with unit original columns is the square root
of the number of columns. Under [the listed assumptions](hyp:hd,hunit), [the stated conclusion follows](goal). -/
-- Proof route: regroup the matrix sum by columns and use
-- `finiteFrobeniusNorm_liftedColumn_eq_one`.
theorem matrixFrobeniusNorm_liftedDirections {p n d : ℕ} (hd : 0 < d)
    (C : FactorMatrix p n) (hunit : ∀ j, finiteFrobeniusNorm (C.col j) = 1) :
    matrixFrobeniusNorm (liftedDirections d C) = Real.sqrt n := by
  have hcol (j : Fin n) :
      ∑ I : LiftIndex p d, (liftedDirections d C I j) ^ 2 = 1 := by
    have h := congrArg (fun z : ℝ => z ^ 2)
      (finiteFrobeniusNorm_liftedColumn_eq_one hd C hunit j)
    simpa [finiteFrobeniusNorm,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
  rw [matrixFrobeniusNorm, finiteFrobeniusNorm]
  congr 1
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hcol]
  simp

end Causalean.Mathlib.Analysis.SymmetricTensorPencil
