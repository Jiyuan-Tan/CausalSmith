module
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Tactic.Abel

/-! # Local continuous solutions of full-row-rank linear systems

This file gives an anchored local solver for a continuous family of finite real
linear systems. A right inverse chosen at the base parameter keeps the square
correction matrix nonsingular nearby, so the solver remains continuous while
preserving the prescribed base solution.
-/

@[expose] public section

open scoped Matrix

namespace Causalean.Mathlib.LinearAlgebra

variable {X : Type*} {k n : ℕ}

/-- Given a [coefficient family](hyp:A), [right-hand-side family](hyp:b),
[fixed correction matrix](hyp:R₀), [prescribed base vector](hyp:y₀), and
[parameter](hyp:x), the [anchored solution](goal) is [the base vector plus the
inverse-based correction at that parameter](step:1). -/
noncomputable def anchoredSolution
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (y₀ : Fin n → ℝ) (x : X) : Fin n → ℝ :=
  y₀ + R₀ *ᵥ ((A x * R₀)⁻¹ *ᵥ (b x - A x *ᵥ y₀))

/-- A [coefficient family](hyp:A), [right-hand-side family](hyp:b), [fixed
correction matrix](hyp:R₀), [base vector](hyp:y₀), and [parameter](hyp:x),
under [a nonzero determinant of the correction matrix](hyp:hx), have [an
anchored solution that solves the linear system at that parameter](goal). -/
theorem anchoredSolution_eq_of_det_ne_zero
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (y₀ : Fin n → ℝ) (x : X)
    (hx : (A x * R₀).det ≠ 0) :
    A x *ᵥ anchoredSolution A b R₀ y₀ x = b x := by
  unfold anchoredSolution
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hx), Matrix.one_mulVec]
  abel

/-- A [coefficient family](hyp:A), [right-hand-side family](hyp:b), [fixed
correction matrix](hyp:R₀), [prescribed base solution](hyp:y₀), and [base
parameter](hyp:x₀), with [a right-inverse identity at the base](hyp:hR) and
[a solved base system](hyp:hy), have [an anchored solution equal to the
prescribed base solution at the base parameter](goal). -/
theorem anchoredSolution_at_base
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (y₀ : Fin n → ℝ) (x₀ : X)
    (hR : A x₀ * R₀ = 1) (hy : A x₀ *ᵥ y₀ = b x₀) :
    anchoredSolution A b R₀ y₀ x₀ = y₀ := by
  simp [anchoredSolution, hy, hR]

/-- A [coefficient family](hyp:A), [right-hand-side family](hyp:b), [fixed
correction matrix](hyp:R₀), [base vector](hyp:y₀), and [parameter](hyp:x),
with [continuous coefficients](hyp:hA), [a continuous right-hand side](hyp:hb),
and [a nonsingular correction matrix at that parameter](hyp:hx), have [an
anchored solution continuous at that parameter](goal). -/
theorem continuousAt_anchoredSolution
    [TopologicalSpace X]
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (y₀ : Fin n → ℝ) (x : X)
    (hA : Continuous A) (hb : Continuous b)
    (hx : (A x * R₀).det ≠ 0) :
    ContinuousAt (anchoredSolution A b R₀ y₀) x := by
  have hM : Continuous (fun z => A z * R₀) :=
    hA.matrix_mul continuous_const
  have hInv : ContinuousAt (fun z => (A z * R₀)⁻¹) x := by
    have hringInv : ContinuousAt Ring.inverse (A x * R₀).det := by
      rw [show (Ring.inverse : ℝ → ℝ) = Inv.inv from funext Ring.inverse_eq_inv]
      exact continuousAt_inv₀ hx
    exact ContinuousAt.comp' (f := fun z => A z * R₀)
      (continuousAt_matrix_inv (A x * R₀) hringInv) hM.continuousAt
  have hResidual : Continuous (fun z => b z - A z *ᵥ y₀) :=
    hb.sub (hA.matrix_mulVec continuous_const)
  have hInner : ContinuousAt
      (fun z => (A z * R₀)⁻¹ *ᵥ (b z - A z *ᵥ y₀)) x :=
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt.comp
      (hInv.prodMk hResidual.continuousAt)
  have hCorrection : ContinuousAt
      (fun z => R₀ *ᵥ ((A z * R₀)⁻¹ *ᵥ (b z - A z *ᵥ y₀))) x :=
    (continuous_const.matrix_mulVec continuous_id).continuousAt.comp hInner
  change ContinuousAt
    (fun z => y₀ + R₀ *ᵥ ((A z * R₀)⁻¹ *ᵥ (b z - A z *ᵥ y₀))) x
  exact continuousAt_const.add hCorrection

/-- A [coefficient family](hyp:A) and [fixed correction matrix](hyp:R₀), with
[continuous coefficients](hyp:hA), have [an open set of parameters where the
correction matrix is nonsingular](goal). -/
theorem isOpen_nonSingular_set
    [TopologicalSpace X]
    (A : X → Matrix (Fin k) (Fin n) ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (hA : Continuous A) :
    IsOpen {x : X | (A x * R₀).det ≠ 0} := by
  have hdet : Continuous (fun x => (A x * R₀).det) :=
    (hA.matrix_mul continuous_const).matrix_det
  simpa only [Set.preimage_ofPred_eq] using
    (isOpen_ne (x := (0 : ℝ))).preimage hdet

variable [TopologicalSpace X]

/-- A [coefficient family](hyp:A), [right-hand-side family](hyp:b), [fixed
correction matrix](hyp:R₀), [base parameter](hyp:x₀), and [prescribed base
solution](hyp:y₀), with [continuous coefficients](hyp:hA), [a continuous
right-hand side](hyp:hb), [a right inverse at the base](hyp:hR), and [a solved
base system](hyp:hy), have [an open neighborhood carrying a continuous anchored
solution that agrees at the base and solves every system in the neighborhood](goal). -/
theorem exists_local_anchoredSolution_of_rightInverse
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (R₀ : Matrix (Fin n) (Fin k) ℝ) (x₀ : X) (y₀ : Fin n → ℝ)
    (hA : Continuous A) (hb : Continuous b)
    (hR : A x₀ * R₀ = 1) (hy : A x₀ *ᵥ y₀ = b x₀) :
    ∃ s : Set X, IsOpen s ∧ x₀ ∈ s ∧
      ContinuousOn (anchoredSolution A b R₀ y₀) s ∧
      anchoredSolution A b R₀ y₀ x₀ = y₀ ∧
      ∀ x ∈ s, A x *ᵥ anchoredSolution A b R₀ y₀ x = b x := by
  refine ⟨{x | (A x * R₀).det ≠ 0}, isOpen_nonSingular_set A R₀ hA,
    ?_, ?_, anchoredSolution_at_base A b R₀ y₀ x₀ hR hy, ?_⟩
  · change (A x₀ * R₀).det ≠ 0
    rw [hR]
    simp
  · exact continuousOn_of_forall_continuousAt fun x hx =>
      continuousAt_anchoredSolution A b R₀ y₀ x hA hb hx
  · intro x hx
    exact anchoredSolution_eq_of_det_ne_zero A b R₀ y₀ x hx

/-- A [coefficient family](hyp:A), [right-hand-side family](hyp:b), [base
parameter](hyp:x₀), and [prescribed base solution](hyp:y₀), with [continuous
coefficients](hyp:hA), [a continuous right-hand side](hyp:hb), [full row rank
at the base](hyp:hfull), and [a solved base system](hyp:hy), have [an open
neighborhood with a continuous solution through the prescribed base solution](goal). -/
theorem exists_local_anchoredSolution_of_surjective
    (A : X → Matrix (Fin k) (Fin n) ℝ) (b : X → Fin k → ℝ)
    (x₀ : X) (y₀ : Fin n → ℝ)
    (hA : Continuous A) (hb : Continuous b)
    (hfull : Function.Surjective (A x₀).mulVec)
    (hy : A x₀ *ᵥ y₀ = b x₀) :
    ∃ (s : Set X) (y : X → Fin n → ℝ),
      IsOpen s ∧ x₀ ∈ s ∧ ContinuousOn y s ∧
      y x₀ = y₀ ∧ ∀ x ∈ s, A x *ᵥ y x = b x := by
  obtain ⟨R₀, hR⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hfull
  obtain ⟨s, hsOpen, hx₀, hContinuous, hy₀, hSolution⟩ :=
    exists_local_anchoredSolution_of_rightInverse A b R₀ x₀ y₀ hA hb hR hy
  exact ⟨s, anchoredSolution A b R₀ y₀, hsOpen, hx₀, hContinuous, hy₀, hSolution⟩

end Causalean.Mathlib.LinearAlgebra
