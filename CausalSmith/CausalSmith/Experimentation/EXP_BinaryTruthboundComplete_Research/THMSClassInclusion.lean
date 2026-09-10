import CausalSmith.Experimentation.EXP_BinaryTruthboundComplete_Research.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Inclusion, and strict inclusion, of design-compatible homogeneous quadratic bounds. -/

open Finset Set

namespace CausalSmith.Experimentation.BinaryTruthbound

/-- Maximum of the true variance over the finite binary cube. -/
noncomputable def cubeMax (E : Setup) : ℝ :=
  (Finset.univ.image (trueVarianceFn E)).max' (by simp)

/-- Published homogeneous-quadratic observability restrictions. -/
def HMSCompatible (E : Setup) (H : Matrix (Fin E.K) (Fin E.K) ℝ) : Prop :=
  H.IsSymm ∧
  (∀ i, (∀ z, i ∉ E.O z) → H i i = 0) ∧
  (∀ i k, i ≠ k → (∀ z, ¬ ({i, k} : Finset (Fin E.K)) ⊆ E.O z) → H i k = 0)

/-- For [an experiment](hyp:E), [every compatible homogeneous quadratic is observable through degrees two and three and is conservative when its matrix dominates the variance matrix, while a constant conservative degree-two bound lies outside the homogeneous quadratic class](goal). -/
-- @node: prop:hms-class-inclusion
theorem hms_quadratic_mem_observableSpan_strict (E : Setup) :
    (∀ H : Matrix (Fin E.K) (Fin E.K) ℝ, HMSCompatible E H →
      hQuad E H ∈ observableSpan E 2 ∧ hQuad E H ∈ observableSpan E 3 ∧
      ((H - varianceMatrixAsMatrix E).PosSemidef →
        hQuad E H ∈ conservativeCone E 2)) ∧
    (fun _ : Theta E => 1 + cubeMax E) ∈ conservativeCone E 2 ∧
    (∀ H : Matrix (Fin E.K) (Fin E.K) ℝ,
      (fun _ : Theta E => 1 + cubeMax E) ≠ hQuad E H) := by
  classical
  have hnonempty : Nonempty E.Omega := by
    by_contra h
    letI : IsEmpty E.Omega := not_nonempty_iff.mp h
    simpa using E.design.p_sum
  have hempty : ∅ ∈ observableComplex E := by
    rcases hnonempty with ⟨z⟩
    unfold observableComplex
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, z, Finset.empty_subset _⟩
  have hmono (S : Finset (Fin E.K)) (hS : S ∈ observableComplex E)
      (r : WithTop ℕ) (hr : (S.card : WithTop ℕ) ≤ r) :
      monomial E S ∈ observableSpan E r := by
    unfold observableSpan
    exact Submodule.subset_span ⟨S, hS, hr, rfl⟩
  constructor
  · intro H hH
    have hterm (i k : Fin E.K) :
        (fun θ : Theta E => H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)) ∈
          observableSpan E 2 := by
      by_cases hik : i = k
      · subst k
        by_cases hzero : H i i = 0
        · rw [show (fun θ : Theta E =>
                H i i * ((θ i : ℕ) : ℝ) * ((θ i : ℕ) : ℝ)) = 0 by
              funext θ
              simp [hzero]]
          exact (observableSpan E 2).zero_mem
        · have hiobs : {i} ∈ observableComplex E := by
            simp only [observableComplex, Finset.mem_filter, Finset.mem_powerset]
            refine ⟨by simp, ?_⟩
            obtain ⟨z, hiz⟩ := not_forall.mp (mt (hH.2.1 i) hzero)
            exact ⟨z, by simpa using hiz⟩
          rw [show (fun θ : Theta E =>
                H i i * ((θ i : ℕ) : ℝ) * ((θ i : ℕ) : ℝ)) =
              H i i • monomial E {i} by
            funext θ
            have hbit : θ i = 0 ∨ θ i = 1 := by omega
            rcases hbit with hbit | hbit <;> simp [monomial, hbit]]
          exact Submodule.smul_mem _ _ (hmono {i} hiobs 2 (by simp))
      · by_cases hzero : H i k = 0
        · rw [show (fun θ : Theta E =>
                H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)) = 0 by
              funext θ
              simp [hzero]]
          exact (observableSpan E 2).zero_mem
        · have hpobs : {i, k} ∈ observableComplex E := by
            simp only [observableComplex, Finset.mem_filter, Finset.mem_powerset]
            refine ⟨by simp, ?_⟩
            obtain ⟨z, hz⟩ := not_forall.mp (mt (hH.2.2 i k hik) hzero)
            exact ⟨z, by simpa using hz⟩
          rw [show (fun θ : Theta E =>
                H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)) =
              H i k • monomial E {i, k} by
            funext θ
            simp [monomial, hik]
            ring]
          exact Submodule.smul_mem _ _
            (hmono {i, k} hpobs 2 (by rw [Finset.card_pair hik]; norm_num))
    have htwo : hQuad E H ∈ observableSpan E 2 := by
      rw [show hQuad E H = ∑ i, ∑ k,
          (fun θ : Theta E => H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ)) by
        funext θ
        simp only [hQuad, Finset.sum_apply]]
      exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => hterm i k
    refine ⟨htwo, ?_, ?_⟩
    · unfold observableSpan at *
      refine Submodule.span_mono ?_ htwo
      rintro u ⟨S, hS, hcard, rfl⟩
      exact ⟨S, hS, hcard.trans (by norm_num), rfl⟩
    · intro hpsd
      refine ⟨htwo, ?_⟩
      intro θ
      let x : Fin E.K → ℝ := fun i => ((θ i : ℕ) : ℝ)
      let y : Fin E.K →₀ ℝ := Finsupp.equivFunOnFinite.symm x
      have hy : ∀ i, y i = x i := fun i => by simp [y]
      have hnonneg := hpsd.2 y
      rw [Finsupp.sum_fintype y _ (by simp)] at hnonneg
      simp only [star_trivial, hy, Matrix.sub_apply] at hnonneg
      have hinner (i : Fin E.K) :
          y.sum (fun j xj => x i *
            (H i j - varianceMatrixAsMatrix E i j) * xj) =
          ∑ j, x i * (H i j - varianceMatrixAsMatrix E i j) * y j := by
        exact Finsupp.sum_fintype y _ (by simp)
      simp_rw [hinner] at hnonneg
      simp only [hy] at hnonneg
      unfold hQuad trueVarianceFn
      dsimp [x] at hnonneg ⊢
      simp only [varianceMatrixAsMatrix] at hnonneg
      have hreorder (i k : Fin E.K) :
          ((θ i : ℕ) : ℝ) * (H i k - varianceMatrix E i k) * ((θ k : ℕ) : ℝ) =
            H i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ) -
            varianceMatrix E i k * ((θ i : ℕ) : ℝ) * ((θ k : ℕ) : ℝ) := by
        ring
      simp_rw [hreorder, Finset.sum_sub_distrib] at hnonneg
      linarith
  · constructor
    · constructor
      · rw [show (fun _ : Theta E => 1 + cubeMax E) =
            (1 + cubeMax E) • monomial E ∅ by
              funext θ
              simp [monomial]]
        exact Submodule.smul_mem _ _ (hmono ∅ hempty 2 (by simp))
      · intro θ
        have hmax : trueVarianceFn E θ ≤ cubeMax E := by
          unfold cubeMax
          apply Finset.le_max'
          simp
        linarith
    · intro H heq
      have hzero : hQuad E H (fun _ => 0) = 0 := by simp [hQuad]
      have hvarnonneg : 0 ≤ trueVarianceFn E (fun _ => 0) := by
        rw [designVarianceFn_eq_Var]
        unfold Causalean.Experimentation.DesignBased.FiniteDesign.Var
          Causalean.Experimentation.DesignBased.FiniteDesign.E
        exact Finset.sum_nonneg fun z _ => mul_nonneg (E.design.p_nonneg z) (sq_nonneg _)
      have hmax : trueVarianceFn E (fun _ => 0) ≤ cubeMax E := by
        unfold cubeMax
        apply Finset.le_max'
        simp
      have hone : 0 < 1 + cubeMax E := by linarith
      have := congrFun heq (fun _ => 0)
      simp [hzero] at this
      linarith

end CausalSmith.Experimentation.BinaryTruthbound
