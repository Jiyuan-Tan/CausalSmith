import Causalean.Mathlib.Analysis.SingularValueWeyl
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Rectangular signal singular values

This module provides reusable singular-value tools for rectangular full-rank products,
orthonormal compression to a signal subspace, and vertical stacks.  The product bound works on
the rank-sized signal subspace rather than wrongly treating an ambient adjoint as injective; the
other results preserve or improve the entire zero-extended singular-value sequence.
-/

open Module
open scoped InnerProductSpace

namespace Causalean.Mathlib.Analysis

/- Proof route: obtain Mathlib's tail subspace from
`exists_large_subspace_norm_le_singularValues`; its intersection with the proposed expanding
subspace is nonzero by the finrank inequality.  The least-value lemmas can then be proved in an
ordered eigenbasis of `T†T`.  For the product, apply the subspace lemma to `range B` and chain the
three least-value estimates; only the middle estimate for `B†` is restricted to `range B`. -/

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- Given [a finite-dimensional real linear map](hyp:T), [a selected signal subspace](hyp:S),
[a nonnegative expansion factor](hyp:c,hc), [an index smaller than the subspace dimension](hyp:j,hdim),
and [a lower norm bound on that subspace](hyp:hbound), [the indexed singular value is at least
that factor](goal).

This is the lower-bound half of the singular-value min--max principle, stated so that a map may
have a nontrivial kernel outside the specified subspace. -/
theorem le_singularValues_of_subspace
    (T : E →ₗ[ℝ] F) (S : Submodule ℝ E) {j : ℕ} {c : ℝ}
    (hc : 0 ≤ c) (hdim : j < finrank ℝ S)
    (hbound : ∀ x : E, x ∈ S → c * ‖x‖ ≤ ‖T x‖) :
    c ≤ T.singularValues j := by
  have hj : j < finrank ℝ E :=
    lt_of_lt_of_le hdim (Submodule.finrank_le S)
  obtain ⟨L, hdimL, hTL⟩ :=
    Causalean.Mathlib.Analysis.exists_large_subspace_norm_le_singularValues T hj
  have hinfne : S ⊓ L ≠ ⊥ := by
    intro hinf
    have hformula := S.finrank_sup_add_finrank_inf_eq L
    have hsup := Submodule.finrank_le (S ⊔ L)
    rw [hinf, finrank_bot, add_zero] at hformula
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinfne
  have hlower := hbound x hx.1
  have hupper := hTL x hx.2
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  nlinarith

/-- Given [an injective finite-dimensional real linear map](hyp:T,hT) on [a nontrivial domain](hyp:E)
and [a domain vector](hyp:x), [the map expands that vector by at least its last domain-indexed
singular value](goal). -/
theorem least_singularValue_mul_norm_le
    [Nontrivial E] (T : E →ₗ[ℝ] F) (hT : Function.Injective T) (x : E) :
    T.singularValues (finrank ℝ E - 1) * ‖x‖ ≤ ‖T x‖ := by
  let hself := T.isSymmetric_adjoint_comp_self
  let b := hself.eigenvectorBasis rfl
  have hdimpos : 0 < finrank ℝ E := Module.finrank_pos
  have hj : finrank ℝ E - 1 < finrank ℝ E := by omega
  have hof (r : ℝ) : (RCLike.ofReal r : ℝ) = r := by
    calc
      (RCLike.ofReal r : ℝ) = RCLike.re (RCLike.ofReal r : ℝ) :=
        (RCLike.re_to_real).symm
      _ = r := RCLike.ofReal_re r
  have hnorm_sq :
      ‖T x‖ ^ 2 =
        ∑ i : Fin (finrank ℝ E),
          hself.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
    calc
      ‖T x‖ ^ 2 = inner ℝ (T x) (T x) := (real_inner_self_eq_norm_sq _).symm
      _ = inner ℝ x ((T.adjoint ∘ₗ T) x) := by
        exact (T.adjoint_inner_right x (T x)).symm
      _ = ∑ i, inner ℝ x (b i) * inner ℝ (b i) ((T.adjoint ∘ₗ T) x) :=
        (b.sum_inner_mul_inner x ((T.adjoint ∘ₗ T) x)).symm
      _ = ∑ i, hself.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hself (b i) x, hself.apply_eigenvectorBasis]
        simp only [real_inner_smul_left, hof]
        rw [real_inner_comm x (b i)]
        simp only [Real.norm_eq_abs, sq_abs]
        ring
  have hlam (i : Fin (finrank ℝ E)) :
      T.singularValues (finrank ℝ E - 1) ^ 2 ≤ hself.eigenvalues rfl i := by
    rw [T.sq_singularValues_fin rfl ⟨finrank ℝ E - 1, hj⟩]
    exact hself.eigenvalues_antitone rfl (by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.le_sub_one_of_lt i.isLt)
  apply
    (sq_le_sq₀
      (mul_nonneg (T.singularValues_nonneg _) (norm_nonneg _))
      (norm_nonneg _)).mp
  rw [mul_pow, hnorm_sq, ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg _)

/-- Given [a full-column-rank finite-dimensional real map](hyp:B,hB), [a vector in its column
space](hyp:y,hy), and [a nontrivial signal domain](hyp:K), [the adjoint expands that vector by at
least the map's least signal singular value](goal).

No claim is made on the whole ambient codomain, where the adjoint can have a nontrivial kernel. -/
theorem least_singularValue_mul_norm_le_adjoint_on_range
    [Nontrivial K] (B : K →ₗ[ℝ] E) (hB : Function.Injective B)
    (y : E) (hy : y ∈ B.range) :
    B.singularValues (finrank ℝ K - 1) * ‖y‖ ≤ ‖B.adjoint y‖ := by
  rcases hy with ⟨z, rfl⟩
  by_cases hz : z = 0
  · simp [hz]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hleast := least_singularValue_mul_norm_le B hB z
  have hcs := real_inner_le_norm z (B.adjoint (B z))
  have hadj : inner ℝ z (B.adjoint (B z)) = ‖B z‖ ^ 2 := by
    calc
      inner ℝ z (B.adjoint (B z)) = inner ℝ (B z) (B z) :=
        B.adjoint_inner_right z (B z)
      _ = ‖B z‖ ^ 2 := real_inner_self_eq_norm_sq _
  rw [hadj] at hcs
  have hsv := B.singularValues_nonneg (finrank ℝ K - 1)
  have hBnorm := norm_nonneg (B z)
  have hadjnorm := norm_nonneg (B.adjoint (B z))
  nlinarith

/-- Given [full-column-rank rectangular factors and an injective square core](hyp:A,D,B,hA,hD,hB)
on [a nontrivial signal space](hyp:K), [the last signal singular value of their adjoint product
is at least the product of the three least signal singular values](goal).

The product is a map on the ambient domain of `B†`, but the proof uses only the rank-sized signal
subspace `range B`; in particular, it does not pretend that `B†` is ambiently injective. -/
theorem singularValues_product_adjoint_lower_bound
    [Nontrivial K]
    (A : K →ₗ[ℝ] F) (D : K →ₗ[ℝ] K) (B : K →ₗ[ℝ] E)
    (hA : Function.Injective A) (hD : Function.Injective D)
    (hB : Function.Injective B) :
    A.singularValues (finrank ℝ K - 1) *
          D.singularValues (finrank ℝ K - 1) *
          B.singularValues (finrank ℝ K - 1) ≤
      (A ∘ₗ D ∘ₗ B.adjoint).singularValues (finrank ℝ K - 1) := by
  apply le_singularValues_of_subspace (A ∘ₗ D ∘ₗ B.adjoint) B.range
  · exact mul_nonneg
      (mul_nonneg (A.singularValues_nonneg _) (D.singularValues_nonneg _))
      (B.singularValues_nonneg _)
  · rw [B.finrank_range_of_inj hB]
    exact Nat.sub_lt (Module.finrank_pos) (by omega)
  · intro y hy
    have hBadj := least_singularValue_mul_norm_le_adjoint_on_range B hB y hy
    have hDleast := least_singularValue_mul_norm_le D hD (B.adjoint y)
    have hAleast := least_singularValue_mul_norm_le A hA (D (B.adjoint y))
    calc
      (A.singularValues (finrank ℝ K - 1) *
          D.singularValues (finrank ℝ K - 1) *
          B.singularValues (finrank ℝ K - 1)) * ‖y‖ =
          (A.singularValues (finrank ℝ K - 1) *
            D.singularValues (finrank ℝ K - 1)) *
            (B.singularValues (finrank ℝ K - 1) * ‖y‖) := by ring
      _ ≤ (A.singularValues (finrank ℝ K - 1) *
            D.singularValues (finrank ℝ K - 1)) * ‖B.adjoint y‖ :=
        mul_le_mul_of_nonneg_left hBadj (mul_nonneg (A.singularValues_nonneg _)
          (D.singularValues_nonneg _))
      _ = A.singularValues (finrank ℝ K - 1) *
            (D.singularValues (finrank ℝ K - 1) * ‖B.adjoint y‖) := by ring
      _ ≤ A.singularValues (finrank ℝ K - 1) * ‖D (B.adjoint y)‖ :=
        mul_le_mul_of_nonneg_left hDleast (A.singularValues_nonneg _)
      _ ≤ ‖A (D (B.adjoint y))‖ := hAleast
      _ = ‖(A ∘ₗ D ∘ₗ B.adjoint) y‖ := rfl

/-- Given [finite real matrices with full column rank and an injective square core](hyp:A,D,B,hA,hD,hB),
[the last signal singular value of their product with the right factor transposed is at least the
product of the three least signal singular values](goal). -/
theorem Matrix.singularValues_mul_mul_transpose_lower_bound
    {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] [Nonempty k]
    (A : Matrix m k ℝ) (D : Matrix k k ℝ) (B : Matrix n k ℝ)
    (hA : Function.Injective A.toEuclideanLin)
    (hD : Function.Injective D.toEuclideanLin)
    (hB : Function.Injective B.toEuclideanLin) :
    A.toEuclideanLin.singularValues (Fintype.card k - 1) *
          D.toEuclideanLin.singularValues (Fintype.card k - 1) *
          B.toEuclideanLin.singularValues (Fintype.card k - 1) ≤
      (A * D * B.transpose).toEuclideanLin.singularValues (Fintype.card k - 1) := by
  have htrans : B.transpose = B.conjTranspose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hlin :
      (A * D * B.transpose).toEuclideanLin =
        A.toEuclideanLin ∘ₗ D.toEuclideanLin ∘ₗ B.toEuclideanLin.adjoint := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint B, ← htrans]
    apply LinearMap.ext
    intro x
    apply PiLp.ext
    intro i
    simp only [LinearMap.comp_apply, Matrix.ofLp_toEuclideanLin_apply,
      Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc]
  have h := singularValues_product_adjoint_lower_bound
    A.toEuclideanLin D.toEuclideanLin B.toEuclideanLin hA hD hB
  simpa only [finrank_euclideanSpace, ← hlin] using h

end Causalean.Mathlib.Analysis

namespace Causalean.Mathlib.Analysis

variable {E F₀ F₁ : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F₀] [InnerProductSpace ℝ F₀] [FiniteDimensional ℝ F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁]

/-- The vertical stack combines two real linear maps with [a common domain](hyp:M₀,M₁) into one
map whose output records both component outputs in their Hilbert direct sum. -/
def verticalStack (M₀ : E →ₗ[ℝ] F₀) (M₁ : E →ₗ[ℝ] F₁) :
    E →ₗ[ℝ] WithLp 2 (F₀ × F₁) :=
  (WithLp.linearEquiv 2 ℝ (F₀ × F₁)).symm.comp (M₀.prod M₁)

/-- Given [two finite-dimensional real maps with a common domain](hyp:M₀,M₁), [the Gram
operator of their vertical stack is the sum of their two Gram operators](goal). -/
theorem verticalStack_adjoint_comp_self
    (M₀ : E →ₗ[ℝ] F₀) (M₁ : E →ₗ[ℝ] F₁) :
    (verticalStack M₀ M₁).adjoint ∘ₗ verticalStack M₀ M₁ =
      (M₀.adjoint ∘ₗ M₀) + (M₁.adjoint ∘ₗ M₁) := by
  ext x
  apply ext_inner_right ℝ
  intro y
  simp only [LinearMap.comp_apply, LinearMap.add_apply]
  rw [(verticalStack M₀ M₁).adjoint_inner_left, inner_add_left,
    M₀.adjoint_inner_left, M₁.adjoint_inner_left]
  rfl

private theorem singularValues_le_of_gram_sub_isPositive
    {F G : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    (A : E →ₗ[ℝ] F) (B : E →ₗ[ℝ] G)
    (hpos : ((B.adjoint ∘ₗ B) - (A.adjoint ∘ₗ A)).IsPositive) (j : ℕ) :
    A.singularValues j ≤ B.singularValues j := by
  by_cases hj : j < finrank ℝ E
  · obtain ⟨S, hdim, hB⟩ :=
      Causalean.Mathlib.Analysis.exists_large_subspace_norm_le_singularValues B hj
    apply Causalean.Mathlib.Analysis.singularValues_le_of_large_subspace A hj S hdim
    intro x hx
    have hnorm : ‖A x‖ ≤ ‖B x‖ := by
      rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)]
      calc
        ‖A x‖ ^ 2 = inner ℝ ((A.adjoint ∘ₗ A) x) x := by
          rw [LinearMap.comp_apply, A.adjoint_inner_left, real_inner_self_eq_norm_sq]
        _ ≤ inner ℝ ((B.adjoint ∘ₗ B) x) x := by
          have h := hpos.inner_nonneg_left x
          simp only [LinearMap.sub_apply, inner_sub_left] at h
          linarith
        _ = ‖B x‖ ^ 2 := by
          rw [LinearMap.comp_apply, B.adjoint_inner_left, real_inner_self_eq_norm_sq]
    exact hnorm.trans (hB x hx)
  · have hdim : finrank ℝ E ≤ j := Nat.le_of_not_gt hj
    rw [A.singularValues_of_finrank_le hdim, B.singularValues_of_finrank_le hdim]

/-- Given [two finite-dimensional real maps with a common domain](hyp:M₀,M₁) and [a singular-value
index](hyp:j), [every zero-extended indexed singular value of their vertical stack is at least
the corresponding singular value of the first component](goal). -/
theorem singularValues_le_verticalStack_left
    (M₀ : E →ₗ[ℝ] F₀) (M₁ : E →ₗ[ℝ] F₁) (j : ℕ) :
    M₀.singularValues j ≤ (verticalStack M₀ M₁).singularValues j := by
  apply singularValues_le_of_gram_sub_isPositive M₀ (verticalStack M₀ M₁)
  rw [verticalStack_adjoint_comp_self]
  simpa using M₁.isPositive_adjoint_comp_self

/-- Given [two finite-dimensional real maps with a common domain](hyp:M₀,M₁) and [a singular-value
index](hyp:j), [every zero-extended indexed singular value of their vertical stack is at least
the corresponding singular value of the second component](goal). -/
theorem singularValues_le_verticalStack_right
    (M₀ : E →ₗ[ℝ] F₀) (M₁ : E →ₗ[ℝ] F₁) (j : ℕ) :
    M₁.singularValues j ≤ (verticalStack M₀ M₁).singularValues j := by
  apply singularValues_le_of_gram_sub_isPositive M₁ (verticalStack M₀ M₁)
  rw [verticalStack_adjoint_comp_self]
  simpa [add_comm] using M₀.isPositive_adjoint_comp_self

end Causalean.Mathlib.Analysis

namespace Causalean.Mathlib.Analysis

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]

/-- Given [a finite-dimensional real map](hyp:M), [an isometric parametrization](hyp:V), [whose
range is exactly the map's adjoint range](hyp:hrange), and [a singular-value index](hyp:j),
[compressing to those orthonormal signal coordinates preserves the indexed singular value](goal).

The equality includes Mathlib's zero-extended tail. -/
theorem singularValues_comp_linearIsometry_of_range_eq_adjoint_range
    (M : E →ₗ[ℝ] F) (V : K →ₗᵢ[ℝ] E)
    (hrange : V.toLinearMap.range = M.adjoint.range) (j : ℕ) :
    (M ∘ₗ V.toLinearMap).singularValues j = M.singularValues j := by
  let A := M ∘ₗ V.toLinearMap
  have hfin : finrank ℝ K = finrank ℝ M.range := by
    calc
      finrank ℝ K = finrank ℝ V.toLinearMap.range := V.equivRange.toLinearEquiv.finrank_eq
      _ = finrank ℝ M.adjoint.range := by rw [hrange]
      _ = finrank ℝ M.range := M.finrank_range_adjoint
  have hrangeA : A.range = M.range := by
    change (M ∘ₗ V.toLinearMap).range = M.range
    rw [LinearMap.range_comp, hrange, ← LinearMap.range_comp]
    exact M.range_self_comp_adjoint
  by_cases hj : j < finrank ℝ M.range
  · have hjK : j < finrank ℝ K := by omega
    apply le_antisymm
    · obtain ⟨S, hdimS, hboundS⟩ :=
        Causalean.Mathlib.Analysis.exists_large_subspace_norm_le_singularValues M
          (hj.trans_le (LinearMap.finrank_range_le M))
      let T : Submodule ℝ K := S.comap V.toLinearMap
      have hmapT : T.map V.toLinearMap = V.toLinearMap.range ⊓ S := by
        simpa [T, inf_comm] using Submodule.map_comap_eq V.toLinearMap S
      have hdim_map (U : Submodule ℝ K) :
          finrank ℝ (U.map V.toLinearMap) = finrank ℝ U := by
        let f : U →ₗ[ℝ] E := V.toLinearMap.comp U.subtype
        have hf : Function.Injective f := V.injective.comp U.injective_subtype
        have hfrange : f.range = U.map V.toLinearMap := by
          simp [f, LinearMap.range_comp]
        rw [← hfrange, f.finrank_range_of_inj hf]
      have hdimT : finrank ℝ K ≤ finrank ℝ T + j := by
        have hsum :=
          Submodule.finrank_sup_add_finrank_inf_eq V.toLinearMap.range S
        have hsup := Submodule.finrank_le (V.toLinearMap.range ⊔ S)
        have hfinV : finrank ℝ V.toLinearMap.range = finrank ℝ K := by
          simpa using V.equivRange.toLinearEquiv.finrank_eq.symm
        rw [← hmapT, hdim_map, hfinV] at hsum
        omega
      apply
        Causalean.Mathlib.Analysis.singularValues_le_of_large_subspace A hjK T hdimT
      intro x hx
      simpa [A] using hboundS (V x) hx
    · obtain ⟨T, hdimT, hboundT⟩ :=
        Causalean.Mathlib.Analysis.exists_large_subspace_norm_le_singularValues A hjK
      let U : Submodule ℝ E := T.map V.toLinearMap
      let S : Submodule ℝ E := U ⊔ M.ker
      have hUorth : U ≤ M.kerᗮ := by
        rw [M.orthogonal_ker, ← hrange]
        exact LinearMap.map_le_range
      have hdisjoint : Disjoint U M.ker :=
        M.ker.orthogonal_disjoint.symm.mono hUorth le_rfl
      have hdimU : finrank ℝ U = finrank ℝ T := by
        let f : T →ₗ[ℝ] E := V.toLinearMap.comp T.subtype
        have hf : Function.Injective f := V.injective.comp T.injective_subtype
        have hfrange : f.range = U := by
          simp [f, U, LinearMap.range_comp]
        rw [← hfrange, f.finrank_range_of_inj hf]
      have hdimS : finrank ℝ E ≤ finrank ℝ S + j := by
        have hsum := Submodule.finrank_sup_add_finrank_inf_eq U M.ker
        rw [hdisjoint.eq_bot, finrank_bot, add_zero, hdimU] at hsum
        have hranknull := M.finrank_range_add_finrank_ker
        dsimp [S]
        omega
      apply
        Causalean.Mathlib.Analysis.singularValues_le_of_large_subspace M
          (hj.trans_le (LinearMap.finrank_range_le M)) S hdimS
      intro x hx
      rcases Submodule.mem_sup.mp hx with ⟨u, hu, k, hk, rfl⟩
      rcases hu with ⟨t, ht, rfl⟩
      have hvorth : V t ∈ M.kerᗮ := hUorth (by exact ⟨t, ht, rfl⟩)
      have hinter : inner ℝ (V t) k = 0 :=
        (M.ker.mem_orthogonal' (V t)).mp hvorth k hk
      have hnormsq : ‖V t + k‖ ^ 2 = ‖V t‖ ^ 2 + ‖k‖ ^ 2 :=
        by simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (V t) k hinter
      have hnormle : ‖t‖ ≤ ‖V t + k‖ := by
        rw [V.norm_map] at hnormsq
        nlinarith [sq_nonneg ‖k‖, norm_nonneg (V t + k), norm_nonneg t]
      calc
        ‖M (V t + k)‖ = ‖A t‖ := by
          simp [A, LinearMap.mem_ker.mp hk]
        _ ≤ A.singularValues j * ‖t‖ := hboundT t ht
        _ ≤ A.singularValues j * ‖V t + k‖ :=
          mul_le_mul_of_nonneg_left hnormle (A.singularValues_nonneg j)
  · have hle : finrank ℝ M.range ≤ j := Nat.le_of_not_gt hj
    have hleA : finrank ℝ A.range ≤ j := by rwa [hrangeA]
    rw [A.singularValues_eq_zero_iff_le_finrank_range.mpr hleA,
      M.singularValues_eq_zero_iff_le_finrank_range.mpr hle]

/-- Given [a finite-dimensional real map](hyp:M), [an isometric signal parametrization](hyp:V),
and [the equality between its range and the adjoint range](hyp:hrange), [the compressed map and
the original map have the same last coordinate-indexed singular value](goal). -/
theorem singularValues_comp_linearIsometry_last
    (M : E →ₗ[ℝ] F) (V : K →ₗᵢ[ℝ] E)
    (hrange : V.toLinearMap.range = M.adjoint.range) :
    (M ∘ₗ V.toLinearMap).singularValues (finrank ℝ K - 1) =
      M.singularValues (finrank ℝ K - 1) := by
  exact singularValues_comp_linearIsometry_of_range_eq_adjoint_range M V hrange _

end Causalean.Mathlib.Analysis
