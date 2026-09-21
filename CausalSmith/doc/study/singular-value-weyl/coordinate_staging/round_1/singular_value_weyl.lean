import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Weyl perturbation inequality for singular values

This module proves the indexed Weyl--Mirsky perturbation inequality for singular values of
finite-dimensional real linear maps.  Its support lemmas express the two halves of the singular
value min--max argument using subspaces, and the main result shows that each singular value is
1-Lipschitz in the operator norm, including Mathlib's zero-extended indices.
-/

open Module
open scoped InnerProductSpace

namespace Causalean.Mathlib.Analysis

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]

/-- Given [a linear map](hyp:A), [an in-range singular-value index](hyp:j,hj), and [a subspace
whose codimension is at most that index](hyp:S,hdim), if [the map is bounded by a scalar multiple
of the norm on that subspace](hyp:c,hbound), then [the indexed singular value is at most that
scalar](goal).

This is the comparison half of the singular-value min--max principle.  It does not require the
map to be injective or the singular value to be positive. -/
theorem singularValues_le_of_large_subspace
    (A : V →ₗ[ℝ] W) {j : ℕ} (hj : j < finrank ℝ V)
    (S : Submodule ℝ V) (hdim : finrank ℝ V ≤ finrank ℝ S + j)
    {c : ℝ} (hbound : ∀ x : V, x ∈ S → ‖A x‖ ≤ c * ‖x‖) :
    A.singularValues j ≤ c := by
  let e : Fin (j + 1) → Fin (finrank ℝ V) :=
    fun i => Fin.castLE (Nat.succ_le_iff.mpr hj) i
  let v : Fin (j + 1) → V :=
    fun i => A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl (e i)
  let lam : Fin (j + 1) → ℝ :=
    fun i => A.isSymmetric_adjoint_comp_self.eigenvalues rfl (e i)
  have hv : Orthonormal ℝ v :=
    A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl |>.orthonormal.comp e
      (Fin.castLE_injective _)
  let U : Submodule ℝ V := Submodule.span ℝ (Set.range v)
  have hU : finrank ℝ U = j + 1 := by
    simpa [U] using finrank_span_eq_card hv.linearIndependent
  have hinfpos : 0 < finrank ℝ (U ⊓ S : Submodule ℝ V) := by
    have hformula := U.finrank_sup_add_finrank_inf_eq S
    have hsup := Submodule.finrank_le (U ⊔ S)
    rw [hU] at hformula
    omega
  have hinfne : U ⊓ S ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hinfpos
    omega
  obtain ⟨x, hxUS, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hinfne
  have hxU : x ∈ U := hxUS.1
  have hxS : x ∈ S := hxUS.2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hxU
  have hx : (∑ i, a i • v i) = x := ha
  have hxnorm : ‖x‖ ^ 2 = ∑ i, (a i) ^ 2 := by
    rw [← hx, @norm_sq_eq_re_inner ℝ V]
    simpa [pow_two] using hv.inner_sum a a Finset.univ
  have hAe (i : Fin (j + 1)) :
      A.adjoint (A (v i)) = lam i • v i := by
    change (A.adjoint ∘ₗ A) _ = _
    exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl _
  have hTx :
      A.adjoint (A (∑ i, a i • v i)) = ∑ i, (lam i * a i) • v i := by
    simp [map_sum, map_smul, hAe, smul_smul, mul_comm]
  have hAxnorm : ‖A x‖ ^ 2 = ∑ i, lam i * (a i) ^ 2 := by
    rw [← hx, @norm_sq_eq_re_inner ℝ W, ← A.adjoint_inner_left, hTx]
    simpa [mul_assoc, mul_left_comm, mul_comm, pow_two] using
      hv.inner_sum (fun i => lam i * a i) a Finset.univ
  have hlam (i : Fin (j + 1)) : A.singularValues j ^ 2 ≤ lam i := by
    rw [A.sq_singularValues_fin rfl ⟨j, hj⟩]
    exact A.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl
      (show e i ≤ (⟨j, hj⟩ : Fin (finrank ℝ V)) from
        Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ i.isLt))
  have hsq : (A.singularValues j * ‖x‖) ^ 2 ≤ ‖A x‖ ^ 2 := by
    rw [mul_pow, hxnorm, hAxnorm, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hlam i) (sq_nonneg (a i))
  have hlower : A.singularValues j * ‖x‖ ≤ ‖A x‖ := by
    exact (sq_le_sq₀
      (mul_nonneg (A.singularValues_nonneg j) (norm_nonneg x))
      (norm_nonneg (A x))).mp hsq
  have hupper := hbound x hxS
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  nlinarith

/-- Given [a linear map](hyp:A) and [an in-range singular-value index](hyp:j,hj), [there is a
subspace whose codimension is at most that index and on which the map is bounded by the indexed
singular value](goal).

This is the constructive half of the singular-value min--max principle for rectangular maps. -/
theorem exists_large_subspace_norm_le_singularValues
    (A : V →ₗ[ℝ] W) {j : ℕ} (hj : j < finrank ℝ V) :
    ∃ S : Submodule ℝ V,
      finrank ℝ V ≤ finrank ℝ S + j ∧
      ∀ x : V, x ∈ S → ‖A x‖ ≤ A.singularValues j * ‖x‖ := by
  classical
  let hT := A.isSymmetric_adjoint_comp_self
  let b := hT.eigenvectorBasis rfl
  let I := {i : Fin (finrank ℝ V) // j ≤ i.1}
  let S := Submodule.span ℝ (Set.range (fun i : I ↦ b i.1))
  refine ⟨S, ?_, ?_⟩
  · have hli : LinearIndependent ℝ (fun i : I ↦ b i.1) :=
      b.orthonormal.linearIndependent.comp _ Subtype.val_injective
    have hdim : finrank ℝ S = Fintype.card I := finrank_span_eq_card hli
    have hhead :
        Fintype.card {i : Fin (finrank ℝ V) // ¬j ≤ i.1} = j := by
      simpa only [not_le, Fintype.card_fin] using
        (Fintype.card_congr
          (Fin.castLEOrderIso (Nat.le_of_lt hj)).symm.toEquiv)
    have hsplit :=
      Fintype.card_subtype_compl (fun i : Fin (finrank ℝ V) ↦ j ≤ i.1)
    rw [hdim]
    dsimp [I]
    have hsplit' :
        j = finrank ℝ V - Fintype.card {i : Fin (finrank ℝ V) // j ≤ i.1} :=
      hhead.symm.trans (by simpa only [Fintype.card_fin] using hsplit)
    omega
  · intro x hx
    have hcoord {i : Fin (finrank ℝ V)} (hi : i.1 < j) :
        ⟪b i, x⟫_ℝ = 0 := by
      rcases (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx with ⟨c, hc⟩
      rw [← hc]
      simp only [inner_sum, real_inner_smul_right]
      apply Finset.sum_eq_zero
      intro k _
      have hik : i ≠ k.1 := by
        intro h
        subst i
        omega
      rw [b.orthonormal.2 hik]
      simp
    have hof (r : ℝ) : (RCLike.ofReal r : ℝ) = r := by
      calc
        (RCLike.ofReal r : ℝ) = RCLike.re (RCLike.ofReal r : ℝ) :=
          (RCLike.re_to_real).symm
        _ = r := RCLike.ofReal_re r
    have hnorm_sq :
        ‖A x‖ ^ 2 =
          ∑ i : Fin (finrank ℝ V),
            hT.eigenvalues rfl i * ‖⟪b i, x⟫_ℝ‖ ^ 2 := by
      calc
        ‖A x‖ ^ 2 = inner ℝ (A x) (A x) := (real_inner_self_eq_norm_sq _).symm
        _ = inner ℝ x ((A.adjoint ∘ₗ A) x) := by
          change inner ℝ (A x) (A x) = inner ℝ x (A.adjoint (A x))
          exact (A.adjoint_inner_right x (A x)).symm
        _ = ∑ i, inner ℝ x (b i) * inner ℝ (b i) ((A.adjoint ∘ₗ A) x) :=
          (b.sum_inner_mul_inner x ((A.adjoint ∘ₗ A) x)).symm
        _ = ∑ i, hT.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hT (b i) x, hT.apply_eigenvectorBasis]
          simp only [real_inner_smul_left, hof]
          rw [real_inner_comm x (b i)]
          simp only [Real.norm_eq_abs, sq_abs]
          ring
    apply
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (A.singularValues_nonneg j) (norm_nonneg _))).mp
    rw [mul_pow]
    calc
      ‖A x‖ ^ 2 =
          ∑ i : Fin (finrank ℝ V),
            hT.eigenvalues rfl i * ‖inner ℝ (b i) x‖ ^ 2 := hnorm_sq
      _ ≤ ∑ i : Fin (finrank ℝ V),
          A.singularValues j ^ 2 * ‖inner ℝ (b i) x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : j ≤ i.1
        · rw [A.sq_singularValues_fin rfl ⟨j, hj⟩]
          exact mul_le_mul_of_nonneg_right
            (hT.eigenvalues_antitone rfl hi) (sq_nonneg _)
        · have hc := hcoord (Nat.lt_of_not_ge hi)
          rw [hc, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, mul_zero]
      _ = A.singularValues j ^ 2 *
          ∑ i : Fin (finrank ℝ V), ‖inner ℝ (b i) x‖ ^ 2 := by
        rw [Finset.mul_sum]
      _ = A.singularValues j ^ 2 * ‖x‖ ^ 2 := by
        rw [b.sum_sq_norm_inner_right]

/-- Given [a baseline linear map](hyp:A), [an additive perturbation](hyp:D), and [a singular-value
index](hyp:j), [the perturbation can increase that indexed singular value by no more than its
operator norm](goal).

The statement includes indices at which Mathlib extends the singular-value sequence by zero. -/
theorem singularValues_add_le_add_opNorm
    (A D : V →ₗ[ℝ] W) (j : ℕ) :
    (A + D).singularValues j ≤ A.singularValues j + ‖D.toContinuousLinearMap‖ := by
  by_cases hj : j < finrank ℝ V
  · obtain ⟨S, hdim, hA⟩ := exists_large_subspace_norm_le_singularValues A hj
    apply singularValues_le_of_large_subspace (A + D) hj S hdim
    intro x hx
    calc
      ‖(A + D) x‖ ≤ ‖A x‖ + ‖D x‖ := by
        simpa only [LinearMap.add_apply] using norm_add_le (A x) (D x)
      _ ≤ A.singularValues j * ‖x‖ + ‖D.toContinuousLinearMap‖ * ‖x‖ :=
        add_le_add (hA x hx) (D.toContinuousLinearMap.le_opNorm x)
      _ = (A.singularValues j + ‖D.toContinuousLinearMap‖) * ‖x‖ := by ring
  · have hdim : finrank ℝ V ≤ j := Nat.le_of_not_gt hj
    simp only [LinearMap.singularValues_of_finrank_le _ hdim, zero_add]
    exact norm_nonneg _

/-- Given [a baseline linear map](hyp:A), [an additive perturbation](hyp:D), and [a singular-value
index](hyp:j), [the absolute change in the indexed singular value is at most the perturbation's
operator norm](goal).

The norm is written on the associated continuous linear map because plain linear maps do not carry
a norm instance. -/
theorem abs_singularValues_add_sub_singularValues_le_opNorm
    (A D : V →ₗ[ℝ] W) (j : ℕ) :
    |(A + D).singularValues j - A.singularValues j| ≤ ‖D.toContinuousLinearMap‖ := by
  rw [abs_le]
  constructor
  · have h := singularValues_add_le_add_opNorm (A + D) (-D) j
    have hnorm : ‖(-D).toContinuousLinearMap‖ = ‖D.toContinuousLinearMap‖ := by simp
    have hcancel : A + D + -D = A := by abel
    rw [hcancel, hnorm] at h
    linarith
  · have h := singularValues_add_le_add_opNorm A D j
    linarith

/-- Given [a baseline continuous linear map](hyp:A), [an additive continuous perturbation](hyp:D),
and [a singular-value index](hyp:j), [the absolute change in the indexed singular value is at most
the perturbation's operator norm](goal). -/
theorem ContinuousLinearMap.abs_singularValues_add_sub_singularValues_le
    (A D : V →L[ℝ] W) (j : ℕ) :
    |(A + D).toLinearMap.singularValues j - A.toLinearMap.singularValues j| ≤ ‖D‖ := by
  have hD : D.toLinearMap.toContinuousLinearMap = D := by ext x; rfl
  simpa [hD] using
    abs_singularValues_add_sub_singularValues_le_opNorm A.toLinearMap D.toLinearMap j

end Causalean.Mathlib.Analysis
