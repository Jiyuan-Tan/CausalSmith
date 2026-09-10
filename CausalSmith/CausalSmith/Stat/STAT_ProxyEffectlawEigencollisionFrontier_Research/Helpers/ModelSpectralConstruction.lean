import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Helpers.ModelRealDiagonalization

/-!
Ambient real diagonalizations and uniform finite-dimensional conditioning bounds built from
the model's thin target-feature singular-value factorization.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open CausalSmith.Substrate.CollisionSafeSpectralLaw
open scoped Matrix.Norms.L2Operator

-- @node: modelRealDiagonalization_AmbientExtension
structure AmbientExtension {dx k : ℕ} (V : SignalBasis dx k) where
  basis : OrthonormalBasis (Fin dx) ℝ (Euc dx)
  signalIndex : Fin k ↪ Fin dx
  basis_signal : ∀ j, basis (signalIndex j) = WithLp.toLp 2 (fun i => V.V i j)

-- @node: modelRealDiagonalization_ambientExtension
noncomputable def SignalBasis.ambientExtension {dx k : ℕ} (V : SignalBasis dx k) :
    AmbientExtension V := by
  let b := Classical.choose V.exists_fin_ambient_orthonormalBasis
  let he := Classical.choose_spec V.exists_fin_ambient_orthonormalBasis
  let e := Classical.choose he
  exact ⟨b, e, Classical.choose_spec he⟩

-- @node: modelRealDiagonalization_ambientEigenvalue
noncomputable def ambientEigenvalue {dx k : ℕ} [Nonempty (Fin k)] (V : SignalBasis dx k)
    (tau : Fin k → ℝ) (i : Fin dx) : ℝ :=
  if _h : i ∈ Set.range V.ambientExtension.signalIndex then
    tau (Function.invFun V.ambientExtension.signalIndex i) else 0

-- @node: modelRealDiagonalization_ambientEigenvalue_signal
lemma ambientEigenvalue_signal {dx k : ℕ} [Nonempty (Fin k)] (V : SignalBasis dx k)
    (tau : Fin k → ℝ) (j : Fin k) :
    ambientEigenvalue V tau (V.ambientExtension.signalIndex j) = tau j := by
  rw [ambientEigenvalue, dif_pos ⟨j, rfl⟩,
    Function.leftInverse_invFun V.ambientExtension.signalIndex.injective j]

-- @node: modelRealDiagonalization_ambientEigenvalue_nonsignal
lemma ambientEigenvalue_nonsignal {dx k : ℕ} [Nonempty (Fin k)] (V : SignalBasis dx k)
    (tau : Fin k → ℝ) (i : Fin dx)
    (hi : i ∉ Set.range V.ambientExtension.signalIndex) :
    ambientEigenvalue V tau i = 0 := by
  simp [ambientEigenvalue, hi]

-- @node: modelRealDiagonalization_eigenbasis
noncomputable def ThinSignalFactorization.eigenbasis {dx k : ℕ}
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) :
    Module.Basis (Fin dx) ℝ (Euc dx) :=
  F.V.ambientExtension.basis.toBasis.map F.linearEquiv

-- @node: modelRealDiagonalization_forward_signal
lemma forward_signal {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) (j : Fin k) :
    Matrix.toEuclideanLin F.forward
      (WithLp.toLp 2 (fun i => F.V.V i j)) =
      WithLp.toLp 2 (fun i => (F.V.V * F.coordInv.transpose) i j) := by
  have hgram := F.V.transpose_mul_self
  have hmat : F.forward * F.V.V = F.V.V * F.coordInv.transpose := by
    unfold ThinSignalFactorization.forward
    rw [Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
    rw [hgram, Matrix.mul_one, Matrix.mul_one, sub_self, add_zero]
  apply PiLp.ext
  intro i
  have hi := congrArg (fun M : RectMatrix dx k => M i j) hmat
  simpa [Matrix.toEuclideanLin_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi

-- @node: modelRealDiagonalization_factorOperator
noncomputable def ThinSignalFactorization.factorOperator {dx k : ℕ}
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) (tau : Fin k → ℝ) :
    RectMatrix dx dx :=
  F.V.V * F.coordInv.transpose * Matrix.diagonal tau * F.coord.transpose * F.V.V.transpose

-- @node: modelRealDiagonalization_factorOperator_mul_signalEigenvectors
lemma factorOperator_mul_signalEigenvectors {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) (tau : Fin k → ℝ) :
    F.factorOperator tau * (F.V.V * F.coordInv.transpose) =
      (F.V.V * F.coordInv.transpose) * Matrix.diagonal tau := by
  have hgram := F.V.transpose_mul_self
  have hci : F.coord.transpose * F.coordInv.transpose = (1 : RectMatrix k k) := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose F.inv_mul_coord
  unfold ThinSignalFactorization.factorOperator
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.V.V.transpose F.V.V F.coordInv.transpose,
    hgram, Matrix.one_mul,
    hci, Matrix.mul_one]

-- @node: modelRealDiagonalization_transpose_mul_ambientBasis_nonsignal
lemma transpose_mul_ambientBasis_nonsignal {dx k : ℕ} (V : SignalBasis dx k)
    (i : Fin dx) (hi : i ∉ Set.range V.ambientExtension.signalIndex) :
    Matrix.mulVec V.V.transpose (V.ambientExtension.basis i).ofLp = 0 := by
  ext j
  have hne : V.ambientExtension.signalIndex j ≠ i := fun h => hi ⟨j, h⟩
  have horth := V.ambientExtension.basis.orthonormal
  rw [orthonormal_iff_ite] at horth
  have horth := horth (V.ambientExtension.signalIndex j) i
  rw [if_neg hne] at horth
  rw [V.ambientExtension.basis_signal j] at horth
  simpa [Matrix.mulVec, dotProduct, PiLp.inner_apply, RCLike.inner_apply,
    conj_trivial, mul_comm] using horth

-- @node: modelRealDiagonalization_forward_ambientBasis_nonsignal
lemma forward_ambientBasis_nonsignal {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) (i : Fin dx)
    (hi : i ∉ Set.range F.V.ambientExtension.signalIndex) :
    Matrix.toEuclideanLin F.forward (F.V.ambientExtension.basis i) =
      F.V.ambientExtension.basis i := by
  have hzero := transpose_mul_ambientBasis_nonsignal F.V i hi
  apply PiLp.ext
  intro a
  simp only [ThinSignalFactorization.forward, Matrix.toEuclideanLin_apply]
  change Matrix.mulVec
      (F.V.V * F.coordInv.transpose * F.V.V.transpose +
        (1 - F.V.V * F.V.V.transpose))
      (F.V.ambientExtension.basis i).ofLp a = _
  have hp : Matrix.mulVec (F.V.V * F.V.V.transpose)
      (F.V.ambientExtension.basis i).ofLp = 0 := by
    rw [← Matrix.mulVec_mulVec, hzero]
    simp
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hzero, hp]
  simp

-- @node: modelRealDiagonalization_factorOperator_eigenbasis
lemma factorOperator_eigenbasis {dx k : ℕ} [Nonempty (Fin k)]
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) (tau : Fin k → ℝ) :
    ∀ i, Matrix.toEuclideanLin (F.factorOperator tau) (F.eigenbasis i) =
      ambientEigenvalue F.V tau i • F.eigenbasis i := by
  intro i
  by_cases hi : i ∈ Set.range F.V.ambientExtension.signalIndex
  · obtain ⟨j, rfl⟩ := hi
    rw [ambientEigenvalue_signal]
    change Matrix.toEuclideanLin (F.factorOperator tau)
        (F.linearEquiv (F.V.ambientExtension.basis.toBasis
          (F.V.ambientExtension.signalIndex j))) =
      tau j • F.linearEquiv (F.V.ambientExtension.basis.toBasis
        (F.V.ambientExtension.signalIndex j))
    rw [show F.V.ambientExtension.basis.toBasis
      (F.V.ambientExtension.signalIndex j) =
        WithLp.toLp 2 (fun i => F.V.V i j) by
          exact F.V.ambientExtension.basis_signal j]
    change Matrix.toEuclideanLin (F.factorOperator tau)
        (Matrix.toEuclideanLin F.forward
          (WithLp.toLp 2 (fun i => F.V.V i j))) =
      tau j • Matrix.toEuclideanLin F.forward
        (WithLp.toLp 2 (fun i => F.V.V i j))
    rw [forward_signal]
    apply PiLp.ext
    intro a
    have hmat := factorOperator_mul_signalEigenvectors F tau
    have ha := congrArg (fun M : RectMatrix dx k => M a j) hmat
    simpa [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Matrix.diagonal_apply, mul_comm] using ha
  · rw [ambientEigenvalue_nonsignal F.V tau i hi, zero_smul]
    change Matrix.toEuclideanLin (F.factorOperator tau)
        (F.linearEquiv (F.V.ambientExtension.basis.toBasis i)) = 0
    change Matrix.toEuclideanLin (F.factorOperator tau)
        (Matrix.toEuclideanLin F.forward (F.V.ambientExtension.basis i)) = 0
    rw [forward_ambientBasis_nonsignal F i hi]
    have hzero := transpose_mul_ambientBasis_nonsignal F.V i hi
    apply PiLp.ext
    intro a
    simp only [ThinSignalFactorization.factorOperator, Matrix.toEuclideanLin_apply]
    simp only [← Matrix.mulVec_mulVec]
    rw [hzero]
    simp

-- @node: modelRealDiagonalization_realDiagonalization
noncomputable def ThinSignalFactorization.realDiagonalization {dx k : ℕ}
    [Nonempty (Fin k)] {B : RectMatrix dx k} (F : ThinSignalFactorization B)
    (tau : Fin k → ℝ) : RealDiagonalization (F.factorOperator tau) :=
  realDiagonalizationOfEigenbasis (F.factorOperator tau) F.eigenbasis
    (ambientEigenvalue F.V tau) (factorOperator_eigenbasis F tau)

-- @node: modelRealDiagonalization_ambientEigenvalue_comp
lemma ambientEigenvalue_comp {dx k : ℕ} [Nonempty (Fin k)]
    (V : SignalBasis dx k) (tau : Fin k → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 0) (i : Fin dx) :
    ambientEigenvalue V (f ∘ tau) i = f (ambientEigenvalue V tau i) := by
  by_cases hi : i ∈ Set.range V.ambientExtension.signalIndex
  · obtain ⟨j, rfl⟩ := hi
    simp [ambientEigenvalue_signal, Function.comp_apply]
  · rw [ambientEigenvalue_nonsignal V (f ∘ tau) i hi,
      ambientEigenvalue_nonsignal V tau i hi, hf0]

-- @node: modelRealDiagonalization_applyFunction
lemma realDiagonalization_applyFunction {dx k : ℕ} [Nonempty (Fin k)]
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) (tau : Fin k → ℝ)
    (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    (F.realDiagonalization tau).applyFunction f = F.factorOperator (f ∘ tau) := by
  apply realDiagonalizationOfEigenbasis_applyFunction_eq_of_apply_basis
  intro i
  rw [← ambientEigenvalue_comp F.V tau f hf0 i]
  exact factorOperator_eigenbasis F (f ∘ tau) i

-- @node: modelRealDiagonalization_moorePenroseInverse_thinSignalFactorization
lemma moorePenroseInverse_thinSignalFactorization {dx k : ℕ}
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) :
    moorePenroseInverse B = F.coordInv * F.V.V.transpose := by
  apply isMoorePenroseInverse_unique (moorePenroseInverse_spec B)
  have hgram := F.V.transpose_mul_self
  have hprojSymm : (F.V.V * F.V.V.transpose).transpose =
      F.V.V * F.V.V.transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hBG : B * (F.coordInv * F.V.V.transpose) = F.V.V * F.V.V.transpose := by
    calc
      B * (F.coordInv * F.V.V.transpose) =
          (F.V.V * F.coord) * (F.coordInv * F.V.V.transpose) :=
        congrArg (fun X : RectMatrix dx k => X * (F.coordInv * F.V.V.transpose)) F.factor
      _ = F.V.V * (F.coord * F.coordInv) * F.V.V.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [F.coord_mul_inv, Matrix.mul_one]
  have hGB : (F.coordInv * F.V.V.transpose) * B = 1 := by
    calc
      (F.coordInv * F.V.V.transpose) * B =
          (F.coordInv * F.V.V.transpose) * (F.V.V * F.coord) :=
        congrArg (fun X : RectMatrix dx k => (F.coordInv * F.V.V.transpose) * X) F.factor
      _ = F.coordInv * (F.V.V.transpose * F.V.V) * F.coord := by
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgram, Matrix.mul_one, F.inv_mul_coord]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hBG]
    calc
      (F.V.V * F.V.V.transpose) * B =
          (F.V.V * F.V.V.transpose) * (F.V.V * F.coord) :=
        congrArg (fun X : RectMatrix dx k => (F.V.V * F.V.V.transpose) * X) F.factor
      _ = F.V.V * (F.V.V.transpose * F.V.V) * F.coord := by
        simp only [Matrix.mul_assoc]
      _ = B := by rw [hgram, Matrix.mul_one]; exact F.factor.symm
  · rw [hGB, Matrix.one_mul]
  · rw [hBG, hprojSymm]
  · rw [hGB, Matrix.transpose_one]

-- @node: modelRealDiagonalization_factorOperator_eq_moorePenrose
lemma factorOperator_eq_moorePenrose {dx k : ℕ}
    {B : RectMatrix dx k} (F : ThinSignalFactorization B) (tau : Fin k → ℝ) :
    F.factorOperator tau =
      (moorePenroseInverse B).transpose * Matrix.diagonal tau * B.transpose := by
  calc
    F.factorOperator tau =
        (F.coordInv * F.V.V.transpose).transpose * Matrix.diagonal tau *
          (F.V.V * F.coord).transpose := by
            simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
              ThinSignalFactorization.factorOperator, Matrix.mul_assoc]
    _ = (moorePenroseInverse B).transpose * Matrix.diagonal tau * B.transpose := by
      rw [moorePenroseInverse_thinSignalFactorization F]
      exact congrArg
        (fun X : RectMatrix dx k =>
          (F.coordInv * F.V.V.transpose).transpose * Matrix.diagonal tau * X.transpose)
        F.factor.symm

-- @node: modelRealDiagonalization_applyFunction_moorePenrose
lemma realDiagonalization_applyFunction_moorePenrose {dx k : ℕ}
    [Nonempty (Fin k)] {B : RectMatrix dx k} (F : ThinSignalFactorization B)
    (tau : Fin k → ℝ) (f : ℝ → ℝ) (hf0 : f 0 = 0) :
    (F.realDiagonalization tau).applyFunction f =
      (moorePenroseInverse B).transpose * Matrix.diagonal (f ∘ tau) * B.transpose := by
  rw [realDiagonalization_applyFunction F tau f hf0,
    factorOperator_eq_moorePenrose]

-- @node: modelRealDiagonalization_eucNorm_le_card_mul_bound
lemma eucNorm_le_card_mul_bound {n : ℕ} (x : Euc n) (M : ℝ)
    (_hM : 0 ≤ M) (hx : ∀ i, |x.ofLp i| ≤ M) :
    ‖x‖ ≤ (n : ℝ) * M := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hsum := b.sum_repr x
  rw [← hsum]
  calc
    ‖∑ i, b.repr x i • b i‖ ≤ ∑ i, ‖b.repr x i • b i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, M := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, b.orthonormal.1 i, mul_one]
      simp only [Real.norm_eq_abs, b, EuclideanSpace.basisFun_repr]
      exact hx i
    _ = (n : ℝ) * M := by simp

-- @node: modelRealDiagonalization_entryNormConstant
noncomputable def entryNormConstant (rows cols : ℕ) : ℝ :=
  (cols : ℝ) *
    ‖((EuclideanSpace.basisFun (Fin cols) ℝ).toBasis.equivFunL :
      Euc cols →L[ℝ] (Fin cols → ℝ))‖ * (rows : ℝ)

-- @node: modelRealDiagonalization_entryNormConstant_nonneg
lemma entryNormConstant_nonneg (rows cols : ℕ) : 0 ≤ entryNormConstant rows cols := by
  unfold entryNormConstant
  positivity

-- @node: modelRealDiagonalization_matrixNorm_le_entryBound
lemma matrixNorm_le_entryBound {rows cols : ℕ}
    (A : RectMatrix rows cols) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ i j, |A i j| ≤ M) :
    ‖A‖ ≤ entryNormConstant rows cols * M := by
  rw [Matrix.l2_opNorm_def]
  have hb := (EuclideanSpace.basisFun (Fin cols) ℝ).toBasis.opNorm_le
    (u := (Matrix.toEuclideanLin ≪≫ₗ LinearMap.toContinuousLinearMap) A)
    (M := (rows : ℝ) * M) (by positivity) (by
      intro j
      apply eucNorm_le_card_mul_bound _ M hM
      intro i
      simpa [Matrix.toEuclideanLin_apply] using hA i j)
  simpa [entryNormConstant, nsmul_eq_mul, mul_assoc] using hb

-- @node: modelRealDiagonalization_orthonormalBasis_entry_abs_le_one
lemma orthonormalBasis_entry_abs_le_one {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (Euc n)) (i j : Fin n) :
    |(b j).ofLp i| ≤ 1 := by
  have hi := PiLp.norm_apply_le (b j) i
  rw [b.orthonormal.1 j] at hi
  simpa [Real.norm_eq_abs] using hi

-- @node: modelRealDiagonalization_signalBasis_entry_abs_le_one
lemma SignalBasis.entry_abs_le_one {dx k : ℕ} (V : SignalBasis dx k)
    (i : Fin dx) (j : Fin k) : |V.V i j| ≤ 1 := by
  let v : Euc dx := WithLp.toLp 2 (fun a => V.V a j)
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hj := V.orthonormal j j
    rw [if_pos rfl] at hj
    rw [show (∑ x, ‖v.ofLp x‖ ^ 2) = 1 by
      simpa [v, Real.norm_eq_abs, sq_abs, pow_two] using hj, Real.sqrt_one]
  have hi := PiLp.norm_apply_le v i
  rw [hv] at hi
  simpa [v, Real.norm_eq_abs] using hi

-- @node: modelRealDiagonalization_coord_entry_bound
lemma ThinSignalFactorization.coord_entry_bound {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ i j, |B i j| ≤ L) (r j : Fin k) :
    |F.coord r j| ≤ (dx : ℝ) * L := by
  have hcoord : F.coord = F.V.V.transpose * B := by
    calc
      F.coord = 1 * F.coord := by rw [Matrix.one_mul]
      _ = (F.V.V.transpose * F.V.V) * F.coord := by rw [F.V.transpose_mul_self]
      _ = F.V.V.transpose * (F.V.V * F.coord) := by rw [Matrix.mul_assoc]
      _ = F.V.V.transpose * B := by rw [← F.factor]
  rw [hcoord, Matrix.mul_apply]
  calc
    |∑ i, F.V.V i r * B i j| ≤ ∑ i, |F.V.V i r * B i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin dx, L := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      calc
        |F.V.V i r| * |B i j| ≤ 1 * L :=
          mul_le_mul (F.V.entry_abs_le_one i r) (hB i j) (abs_nonneg _) (by norm_num)
        _ = L := one_mul L
    _ = (dx : ℝ) * L := by simp

-- @node: modelRealDiagonalization_forward_norm_bound
lemma ThinSignalFactorization.forward_norm_bound {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) {J : ℝ} (hJ : 0 ≤ J)
    (hCi : ∀ i j, |F.coordInv i j| ≤ J) (hdx : 0 < dx) :
    ‖F.forward‖ ≤
      entryNormConstant dx k * entryNormConstant k k * entryNormConstant k dx * J +
        (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx) := by
  have hCdxk := entryNormConstant_nonneg dx k
  have hCkk := entryNormConstant_nonneg k k
  have hCkdx := entryNormConstant_nonneg k dx
  have hV := matrixNorm_le_entryBound F.V.V 1 (by norm_num) F.V.entry_abs_le_one
  have hVt := matrixNorm_le_entryBound F.V.V.transpose 1 (by norm_num)
    (fun i j => by simpa using F.V.entry_abs_le_one j i)
  have hCit := matrixNorm_le_entryBound F.coordInv.transpose J hJ
    (fun i j => by simpa using hCi j i)
  have hone := matrixNorm_le_entryBound (1 : RectMatrix dx dx) 1 (by norm_num)
    (fun i j => by simp [Matrix.one_apply]; split <;> norm_num)
  have htriple : ‖F.V.V * F.coordInv.transpose * F.V.V.transpose‖ ≤
      (entryNormConstant dx k * 1) * (entryNormConstant k k * J) *
        (entryNormConstant k dx * 1) := by
    calc
      _ ≤ (‖F.V.V‖ * ‖F.coordInv.transpose‖) * ‖F.V.V.transpose‖ :=
        (Matrix.l2_opNorm_mul _ _).trans <|
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ _ := by gcongr
  have hproj : ‖F.V.V * F.V.V.transpose‖ ≤
      (entryNormConstant dx k * 1) * (entryNormConstant k dx * 1) :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hV hVt (norm_nonneg _) (mul_nonneg hCdxk (by norm_num)))
  unfold ThinSignalFactorization.forward
  calc
    ‖F.V.V * F.coordInv.transpose * F.V.V.transpose +
        (1 - F.V.V * F.V.V.transpose)‖ ≤
        ‖F.V.V * F.coordInv.transpose * F.V.V.transpose‖ +
          ‖1 - F.V.V * F.V.V.transpose‖ := norm_add_le _ _
    _ ≤ (entryNormConstant dx k * 1 * (entryNormConstant k k * J)) *
          (entryNormConstant k dx * 1) +
        (entryNormConstant dx dx * 1 +
          (entryNormConstant dx k * 1) * (entryNormConstant k dx * 1)) :=
      add_le_add htriple ((norm_sub_le _ _).trans (add_le_add hone hproj))
    _ = _ := by ring

-- @node: modelRealDiagonalization_backward_norm_bound
lemma ThinSignalFactorization.backward_norm_bound {dx k : ℕ} {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) {L : ℝ} (hL : 0 ≤ L)
    (hB : ∀ i j, |B i j| ≤ L) (hdx : 0 < dx) :
    ‖F.backward‖ ≤
      entryNormConstant dx k * entryNormConstant k k * entryNormConstant k dx *
          ((dx : ℝ) * L) +
        (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx) := by
  have hCdxk := entryNormConstant_nonneg dx k
  have hCkk := entryNormConstant_nonneg k k
  have hCkdx := entryNormConstant_nonneg k dx
  have hV := matrixNorm_le_entryBound F.V.V 1 (by norm_num) F.V.entry_abs_le_one
  have hVt := matrixNorm_le_entryBound F.V.V.transpose 1 (by norm_num)
    (fun i j => by simpa using F.V.entry_abs_le_one j i)
  have hCt := matrixNorm_le_entryBound F.coord.transpose ((dx : ℝ) * L) (by positivity)
    (fun i j => by simpa using F.coord_entry_bound hL hB j i)
  have hone := matrixNorm_le_entryBound (1 : RectMatrix dx dx) 1 (by norm_num)
    (fun i j => by simp [Matrix.one_apply]; split <;> norm_num)
  have htriple : ‖F.V.V * F.coord.transpose * F.V.V.transpose‖ ≤
      (entryNormConstant dx k * 1) *
        (entryNormConstant k k * ((dx : ℝ) * L)) *
        (entryNormConstant k dx * 1) := by
    calc
      _ ≤ (‖F.V.V‖ * ‖F.coord.transpose‖) * ‖F.V.V.transpose‖ :=
        (Matrix.l2_opNorm_mul _ _).trans <|
          mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ ≤ _ := by gcongr
  have hproj : ‖F.V.V * F.V.V.transpose‖ ≤
      (entryNormConstant dx k * 1) * (entryNormConstant k dx * 1) :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_mul hV hVt (norm_nonneg _) (mul_nonneg hCdxk (by norm_num)))
  unfold ThinSignalFactorization.backward
  calc
    ‖F.V.V * F.coord.transpose * F.V.V.transpose +
        (1 - F.V.V * F.V.V.transpose)‖ ≤
        ‖F.V.V * F.coord.transpose * F.V.V.transpose‖ +
          ‖1 - F.V.V * F.V.V.transpose‖ := norm_add_le _ _
    _ ≤ (entryNormConstant dx k * 1 *
          (entryNormConstant k k * ((dx : ℝ) * L))) *
          (entryNormConstant k dx * 1) +
        (entryNormConstant dx dx * 1 +
          (entryNormConstant dx k * 1) * (entryNormConstant k dx * 1)) :=
      add_le_add htriple ((norm_sub_le _ _).trans (add_le_add hone hproj))
    _ = _ := by ring

-- @node: modelRealDiagonalization_conditionBound
noncomputable def conditionBound (dx k : ℕ) (L sigma0 : ℝ) : ℝ :=
  let Kf := entryNormConstant dx k * entryNormConstant k k *
      entryNormConstant k dx * sigma0⁻¹ +
    (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx)
  let Kb := entryNormConstant dx k * entryNormConstant k k *
      entryNormConstant k dx * ((dx : ℝ) * L) +
    (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx)
  entryNormConstant dx dx ^ 2 * Kf * Kb

-- @node: modelRealDiagonalization_conditionBound_nonneg
lemma conditionBound_nonneg (dx k : ℕ) {L sigma0 : ℝ}
    (hL : 0 ≤ L) (hsigma : 0 < sigma0) :
    0 ≤ conditionBound dx k L sigma0 := by
  unfold conditionBound
  have hdxk := entryNormConstant_nonneg dx k
  have hkk := entryNormConstant_nonneg k k
  have hkdx := entryNormConstant_nonneg k dx
  have hdxdx := entryNormConstant_nonneg dx dx
  positivity

-- @node: modelRealDiagonalization_conditionNumber_le
lemma ThinSignalFactorization.diagonalization_conditionNumber_le
    {dx k : ℕ} [Nonempty (Fin k)] {B : RectMatrix dx k}
    (F : ThinSignalFactorization B) (tau : Fin k → ℝ) {L sigma0 : ℝ}
    (hL : 0 ≤ L) (hsigma : 0 < sigma0)
    (hB : ∀ i j, |B i j| ≤ L)
    (hCi : ∀ i j, |F.coordInv i j| ≤ sigma0⁻¹) (hdx : 0 < dx) :
    (F.realDiagonalization tau).conditionNumber ≤
      conditionBound dx k L sigma0 := by
  let Kf := entryNormConstant dx k * entryNormConstant k k *
      entryNormConstant k dx * sigma0⁻¹ +
    (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx)
  let Kb := entryNormConstant dx k * entryNormConstant k k *
      entryNormConstant k dx * ((dx : ℝ) * L) +
    (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx)
  have hKf0 : 0 ≤ Kf := by
    dsimp [Kf]
    have := entryNormConstant_nonneg dx k
    have := entryNormConstant_nonneg k k
    have := entryNormConstant_nonneg k dx
    have := entryNormConstant_nonneg dx dx
    positivity
  have hKb0 : 0 ≤ Kb := by
    dsimp [Kb]
    have := entryNormConstant_nonneg dx k
    have := entryNormConstant_nonneg k k
    have := entryNormConstant_nonneg k dx
    have := entryNormConstant_nonneg dx dx
    positivity
  have hFwd : ‖F.forward‖ ≤ Kf := F.forward_norm_bound (inv_nonneg.mpr hsigma.le) hCi hdx
  have hBwd : ‖F.backward‖ ≤ Kb := F.backward_norm_bound hL hB hdx
  have hBasisEntry (i j : Fin dx) :
      |(F.realDiagonalization tau).basis i j| ≤ Kf := by
    change |(F.eigenbasis j).ofLp i| ≤ Kf
    rw [ThinSignalFactorization.eigenbasis, Module.Basis.map_apply]
    change |(Matrix.toEuclideanLin F.forward (F.V.ambientExtension.basis j)).ofLp i| ≤ Kf
    calc
      _ ≤ ‖Matrix.toEuclideanLin F.forward (F.V.ambientExtension.basis j)‖ := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le (Matrix.toEuclideanLin F.forward
            (F.V.ambientExtension.basis j)) i
      _ ≤ ‖F.forward‖ * ‖F.V.ambientExtension.basis j‖ := by
        simpa [Matrix.toEuclideanLin_apply] using
          Matrix.l2_opNorm_mulVec F.forward (F.V.ambientExtension.basis j)
      _ = ‖F.forward‖ := by rw [F.V.ambientExtension.basis.orthonormal.1 j, mul_one]
      _ ≤ Kf := hFwd
  have hBasis : ‖(F.realDiagonalization tau).basis‖ ≤
      entryNormConstant dx dx * Kf :=
    matrixNorm_le_entryBound _ Kf hKf0 hBasisEntry
  have hInvEntry (i j : Fin dx) :
      |(F.realDiagonalization tau).basisInv i j| ≤ Kb := by
    change |F.eigenbasis.repr (EuclideanSpace.single j (1 : ℝ)) i| ≤ Kb
    rw [ThinSignalFactorization.eigenbasis, Module.Basis.map_repr]
    change |F.V.ambientExtension.basis.toBasis.repr
      (F.linearEquiv.symm (EuclideanSpace.single j (1 : ℝ))) i| ≤ Kb
    change |F.V.ambientExtension.basis.toBasis.repr
      (Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ))) i| ≤ Kb
    rw [F.V.ambientExtension.basis.coe_toBasis_repr_apply]
    have hre := F.V.ambientExtension.basis.repr_apply_apply
      (Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ))) i
    change |(F.V.ambientExtension.basis.repr
      (Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ)))).ofLp i| ≤ Kb
    rw [hre]
    calc
      |inner ℝ (F.V.ambientExtension.basis i)
          (Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ)))| ≤
          ‖F.V.ambientExtension.basis i‖ *
            ‖Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ))‖ :=
        abs_real_inner_le_norm _ _
      _ = ‖Matrix.toEuclideanLin F.backward (EuclideanSpace.single j (1 : ℝ))‖ := by
        rw [F.V.ambientExtension.basis.orthonormal.1 i, one_mul]
      _ ≤ ‖F.backward‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := by
        simpa [Matrix.toEuclideanLin_apply] using
          Matrix.l2_opNorm_mulVec F.backward (EuclideanSpace.single j (1 : ℝ))
      _ = ‖F.backward‖ := by rw [EuclideanSpace.norm_single, norm_one, mul_one]
      _ ≤ Kb := hBwd
  have hInv : ‖(F.realDiagonalization tau).basisInv‖ ≤
      entryNormConstant dx dx * Kb :=
    matrixNorm_le_entryBound _ Kb hKb0 hInvEntry
  unfold RealDiagonalization.conditionNumber conditionBound
  dsimp [Kf, Kb] at hBasis hInv ⊢
  calc
    ‖(F.realDiagonalization tau).basis‖ * ‖(F.realDiagonalization tau).basisInv‖ ≤
        (entryNormConstant dx dx *
          (entryNormConstant dx k * entryNormConstant k k * entryNormConstant k dx * sigma0⁻¹ +
            (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx))) *
        (entryNormConstant dx dx *
          (entryNormConstant dx k * entryNormConstant k k * entryNormConstant k dx * (↑dx * L) +
            (entryNormConstant dx dx + entryNormConstant dx k * entryNormConstant k dx))) :=
      mul_le_mul hBasis hInv (norm_nonneg _)
        (mul_nonneg (entryNormConstant_nonneg dx dx) hKf0)
    _ = _ := by ring

-- @node: modelRealDiagonalization_singularSystem_right_entry_abs_le_one
lemma singularSystem_right_entry_abs_le_one {rows cols : ℕ} (B : RectMatrix rows cols)
    (r j : Fin cols) : |(singularSystem B).right r j| ≤ 1 := by
  let v : Euc cols := WithLp.toLp 2 ((singularSystem B).right r)
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hr := (singularSystem B).right_orthonormal r r
    rw [if_pos rfl] at hr
    rw [show (∑ x, ‖v.ofLp x‖ ^ 2) = 1 by
      simpa [v, Real.norm_eq_abs, sq_abs, pow_two] using hr, Real.sqrt_one]
  have hj := PiLp.norm_apply_le v j
  rw [hv] at hj
  simpa [v, Real.norm_eq_abs] using hj

-- @node: modelRealDiagonalization_constructed_coordInv_entry_bound
lemma thinSignalFactorization_coordInv_entry_bound {dx k : ℕ}
    (B : RectMatrix dx k) (hpos : ∀ r : Fin k, 0 < (singularSystem B).sigma r)
    {sigma0 : ℝ} (hsigma : 0 < sigma0)
    (hsle : ∀ r, sigma0 ≤ (singularSystem B).sigma r) (i j : Fin k) :
    |(thinSignalFactorization B hpos).coordInv i j| ≤ sigma0⁻¹ := by
  simp only [thinSignalFactorization]
  change |(singularSystem B).right j i * ((singularSystem B).sigma j)⁻¹| ≤ sigma0⁻¹
  rw [abs_mul, abs_inv, abs_of_pos (hpos j)]
  have hinv : ((singularSystem B).sigma j)⁻¹ ≤ sigma0⁻¹ := inv_anti₀ hsigma (hsle j)
  calc
    |(singularSystem B).right j i| * ((singularSystem B).sigma j)⁻¹ ≤
        1 * sigma0⁻¹ := mul_le_mul (singularSystem_right_entry_abs_le_one B j i)
          hinv (inv_nonneg.mpr (hpos j).le) (by norm_num)
    _ = sigma0⁻¹ := one_mul _

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
