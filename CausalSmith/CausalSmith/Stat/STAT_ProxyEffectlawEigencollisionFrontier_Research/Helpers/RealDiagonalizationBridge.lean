import CausalSmith.Substrate.CollisionSafeSpectralLaw.FunctionalCalculus
import CausalSmith.Stat.STAT_ProxyEffectlawEigencollisionFrontier_Research.Basic

/-!
Paper-local conversion of a real eigenbasis into the matrix certificate used by the
collision-safe functional-calculus substrate.
-/

namespace CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier

open CausalSmith.Substrate.CollisionSafeSpectralLaw

/-- The orthonormal target-signal frame extends to an ambient orthonormal basis.  This is the
paper-local complement construction needed to add the zero eigenspace without choosing an
eigengap or a basis inside any repeated signal eigenspace. -/
-- @node: realDiagonalizationBridge_signalBasis_extension
lemma SignalBasis.exists_ambient_orthonormalBasis {dx k : ℕ} (V : SignalBasis dx k) :
    ∃ (u : Finset (Euc dx)) (b : OrthonormalBasis u ℝ (Euc dx)),
      Set.range (fun j : Fin k => WithLp.toLp 2 (fun i => V.V i j)) ⊆ u ∧
      ⇑b = ((↑) : u → Euc dx) := by
  have horth : Orthonormal ℝ
      (fun j : Fin k => (WithLp.toLp 2 (fun i => V.V i j) : Euc dx)) := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm,
      mul_comm] using V.orthonormal i j
  let f : Fin k → Euc dx :=
    fun j => WithLp.toLp 2 (fun i => V.V i j)
  have hf : Function.Injective f := horth.linearIndependent.injective
  have hrange : Orthonormal ℝ ((↑) : Set.range f → Euc dx) := by
    rwa [orthonormal_subtype_range hf]
  simpa [f] using hrange.exists_orthonormalBasis_extension

/-- The ambient orthonormal extension may be indexed by the standard ambient coordinates,
with an explicit embedding recording which coordinates are the signal columns. -/
-- @node: realDiagonalizationBridge_signalBasis_fin_extension
lemma SignalBasis.exists_fin_ambient_orthonormalBasis {dx k : ℕ} (V : SignalBasis dx k) :
    ∃ (b : OrthonormalBasis (Fin dx) ℝ (Euc dx)) (e : Fin k ↪ Fin dx),
      ∀ j, b (e j) = WithLp.toLp 2 (fun i => V.V i j) := by
  obtain ⟨u, b, hu, hb⟩ := V.exists_ambient_orthonormalBasis
  let f : Fin k → Euc dx := fun j => WithLp.toLp 2 (fun i => V.V i j)
  have hforth : Orthonormal ℝ f := by
    rw [orthonormal_iff_ite]
    intro i j
    simpa only [f, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, eq_comm,
      mul_comm] using V.orthonormal i j
  have hf : Function.Injective f := hforth.linearIndependent.injective
  have hcard : Fintype.card u = Fintype.card (Fin dx) := by
    rw [← Module.finrank_eq_card_basis b.toBasis]
    simp
  let eu : u ≃ Fin dx := Fintype.equivOfCardEq hcard
  let e : Fin k ↪ Fin dx :=
    ⟨fun j => eu ⟨f j, hu ⟨j, rfl⟩⟩, fun a b h => by
      apply hf
      exact congrArg Subtype.val (eu.injective h)⟩
  refine ⟨b.reindex eu, e, ?_⟩
  intro j
  rw [OrthonormalBasis.reindex_apply]
  change b (eu.symm (eu ⟨f j, hu ⟨j, rfl⟩⟩)) = f j
  simp only [Equiv.symm_apply_apply]
  simpa [f] using congrFun hb ⟨f j, hu ⟨j, rfl⟩⟩

/-- The matrix whose columns are the vectors of a Euclidean basis. -/
-- @node: realDiagonalizationBridge_basisMatrix
noncomputable def basisMatrix {n : ℕ} (b : Module.Basis (Fin n) ℝ (Euc n)) :
    RectMatrix n n :=
  fun i j => (b j).ofLp i

/-- The inverse coordinate matrix of a Euclidean basis. -/
-- @node: realDiagonalizationBridge_basisInvMatrix
noncomputable def basisInvMatrix {n : ℕ} (b : Module.Basis (Fin n) ℝ (Euc n)) :
    RectMatrix n n :=
  fun i j => b.repr (EuclideanSpace.single j (1 : ℝ)) i

/-- A basis matrix followed by its coordinate matrix is the identity. -/
-- @node: realDiagonalizationBridge_basisMatrix_mul_inv
lemma basisMatrix_mul_inv {n : ℕ} (b : Module.Basis (Fin n) ℝ (Euc n)) :
    basisMatrix b * basisInvMatrix b = 1 := by
  ext i j
  have h := congrArg (fun x : Euc n => x.ofLp i)
    (b.sum_repr (EuclideanSpace.single j (1 : ℝ)))
  have coord_sum (f : Fin n → Euc n) :
      (∑ x, f x).ofLp i = ∑ x, (f x).ofLp i := by
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => simp [ha, ih]
  rw [coord_sum] at h
  change ∑ x, (b x).ofLp i * b.repr (EuclideanSpace.single j (1 : ℝ)) x = _
  rw [show (∑ x, (b x).ofLp i * b.repr (EuclideanSpace.single j (1 : ℝ)) x) =
      ∑ x, b.repr (EuclideanSpace.single j (1 : ℝ)) x * (b x).ofLp i by
    apply Finset.sum_congr rfl
    intro x _
    ring]
  simpa only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul,
    PiLp.single_apply, one_mul, Matrix.one_apply] using h

/-- The coordinate matrix followed by its basis matrix is the identity. -/
-- @node: realDiagonalizationBridge_basisInvMatrix_mul_basis
lemma basisInvMatrix_mul_basis {n : ℕ} (b : Module.Basis (Fin n) ℝ (Euc n)) :
    basisInvMatrix b * basisMatrix b = 1 := by
  ext i j
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  have h0 : ∑ x, (b j).ofLp x • e x = b j := by
    simpa [e, EuclideanSpace.basisFun_repr] using e.sum_repr (b j)
  have h1 := congrArg b.repr h0
  simp only [map_sum, map_smul] at h1
  have h := congrArg (fun f : Fin n →₀ ℝ => f i) h1
  change ∑ x, b.repr (EuclideanSpace.single x (1 : ℝ)) i * (b j).ofLp x = _
  rw [show b.repr (b j) = Finsupp.single j 1 from b.repr_self j] at h
  rw [Finsupp.single_apply] at h
  simpa [e, mul_comm, Matrix.one_apply, eq_comm] using h

/-- A full real eigenbasis yields the substrate's two-sided real diagonalization certificate. -/
-- @node: realDiagonalizationBridge_ofEigenbasis
noncomputable def realDiagonalizationOfEigenbasis {n : ℕ} (A : RectMatrix n n)
    (b : Module.Basis (Fin n) ℝ (Euc n)) (lam : Fin n → ℝ)
    (heig : ∀ j, Matrix.toEuclideanLin A (b j) = lam j • b j) :
    RealDiagonalization A := by
  let S := basisMatrix b
  let T := basisInvMatrix b
  exact {
    basis := S
    basisInv := T
    eigenvalue := lam
    basis_mul_inv := basisMatrix_mul_inv b
    inv_mul_basis := basisInvMatrix_mul_basis b
    reconstruct := by
      have hAS : A * S = S * Matrix.diagonal lam := by
        ext i j
        have h := congrArg (fun x : Euc n => x.ofLp i) (heig j)
        simpa [S, basisMatrix, Matrix.toEuclideanLin_apply,
          Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, mul_comm] using h
      calc
        A = A * 1 := by rw [Matrix.mul_one]
        _ = A * (S * T) := by rw [basisMatrix_mul_inv b]
        _ = (A * S) * T := by rw [Matrix.mul_assoc]
        _ = (S * Matrix.diagonal lam) * T := by rw [hAS] }

/-- The functional calculus of the eigenbasis certificate is the expected conjugation formula. -/
-- @node: realDiagonalizationBridge_applyFunction
lemma realDiagonalizationOfEigenbasis_applyFunction {n : ℕ} (A : RectMatrix n n)
    (b : Module.Basis (Fin n) ℝ (Euc n)) (lam : Fin n → ℝ)
    (heig : ∀ j, Matrix.toEuclideanLin A (b j) = lam j • b j) (f : ℝ → ℝ) :
    (realDiagonalizationOfEigenbasis A b lam heig).applyFunction f =
      basisMatrix b * Matrix.diagonal (f ∘ lam) * basisInvMatrix b := by
  rfl

/-- A matrix agreeing with the scalar functional calculus on every vector of the eigenbasis
is exactly the functional-calculus matrix. -/
-- @node: realDiagonalizationBridge_applyFunction_eq_of_apply_basis
lemma realDiagonalizationOfEigenbasis_applyFunction_eq_of_apply_basis {n : ℕ}
    (A F : RectMatrix n n) (b : Module.Basis (Fin n) ℝ (Euc n))
    (lam : Fin n → ℝ) (heig : ∀ j, Matrix.toEuclideanLin A (b j) = lam j • b j)
    (f : ℝ → ℝ) (hF : ∀ j, Matrix.toEuclideanLin F (b j) = f (lam j) • b j) :
    (realDiagonalizationOfEigenbasis A b lam heig).applyFunction f = F := by
  rw [realDiagonalizationOfEigenbasis_applyFunction]
  let S := basisMatrix b
  let T := basisInvMatrix b
  have hFS : F * S = S * Matrix.diagonal (f ∘ lam) := by
    ext i j
    have h := congrArg (fun x : Euc n => x.ofLp i) (hF j)
    simpa [S, basisMatrix, Matrix.toEuclideanLin_apply, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.diagonal_apply, Function.comp_apply, mul_comm] using h
  calc
    basisMatrix b * Matrix.diagonal (f ∘ lam) * basisInvMatrix b =
        (F * S) * T := by rw [hFS]
    _ = F * (S * T) := by rw [Matrix.mul_assoc]
    _ = F := by rw [basisMatrix_mul_inv b, Matrix.mul_one]

end CausalSmith.Stat.ProxyEffectlawEigencollisionFrontier
