module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.TCompatibilityCompletion

/-! Full-cover normalization to known-label population identification. -/

@[expose] public section

open MeasureTheory Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: acyclic_mechanism_totalEffect_unit_det
lemma acyclic_mechanism_totalEffect_unit_det {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : AcyclicMechanism A) :
    IsUnit (totalEffect A).det := by
  classical
  have hdiag : ∀ i, (1 - A) i i = 1 := by
    intro i
    simp [hA.1 i]
  have hacyc : ∀ i, ¬ Relation.TransGen
      (fun j k => j ≠ k ∧ (1 - A) k j ≠ 0) i i := by
    intro i hi
    exact hA.2 i (hi.lift id (by
      intro j k hjk
      have hkj : k ≠ j := Ne.symm hjk.1
      change A k j ≠ 0
      simpa [Matrix.sub_apply, hkj] using hjk.2))
  have hu := acyclic_unit_matrix_invertible (1 - A) hdiag hacyc
  exact Matrix.isUnit_nonsing_inv_det_iff.mpr hu

/-- Stack normalized observable shifts in supplied target columns. -/
noncomputable def normalizedStack {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p p Ω μ)
    (ht : Function.Bijective 𝔐.t) :
    Matrix (Fin p) (Fin p) ℝ :=
  let σ := Equiv.ofBijective 𝔐.t ht
  Matrix.of (fun i j =>
    obsShift μ 𝔐 (σ.symm j) i / obsShift μ 𝔐 (σ.symm j) j)

-- @node: prop:full-cover-reduction
theorem full_cover_reduction {p q : ℕ} (v : Fin q → Fin p → ℝ)
    (hq : q = p) (hcompat : (assignmentFiber v).Nonempty) :
    (∃! f : Fin q ↪ Fin p, f ∈ assignmentFiber v) ∧
    (∃! B : Matrix (Fin p) (Fin p) ℝ, B ∈ completionFiber v) ∧
    (∀ (Ω : Type) (ms : MeasurableSpace Ω)
      (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∀ 𝔐 : AtomicCountModel p p Ω μ,
      ∀ ht : Function.Bijective 𝔐.t,
      (∀ m, obsShift μ 𝔐 m (𝔐.t m) ≠ 0 ∧
        ∀ i, obsShift μ 𝔐 m i / obsShift μ 𝔐 m (𝔐.t m) =
          totalEffect 𝔐.A i (𝔐.t m)) ∧
      𝔐.A = 1 - (normalizedStack μ 𝔐 ht)⁻¹ ∧
      ∀ m m', ProjSim (obsShift μ 𝔐) m m' ↔ m = m') := by
  subst q
  refine ⟨full_cover_assignment_unique v hcompat,
    full_cover_completion_unique v hcompat, ?_⟩
  intro Ω ms μ
  letI : MeasurableSpace Ω := ms
  intro 𝔐 ht
  have hshift := ((compatibility_completion 𝔐.p_pos).1 p Ω ms μ 𝔐).1
  have hB := acyclic_mechanism_totalEffect_unit_det 𝔐.A 𝔐.acyclic
  have hdiag := acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic
  have hBunit : IsUnit (totalEffect 𝔐.A) :=
    (Matrix.isUnit_iff_isUnit_det (A := totalEffect 𝔐.A)).2 hB
  have hproj : ∀ m m', ProjSim (obsShift μ 𝔐) m m' ↔ 𝔐.t m = 𝔐.t m' := by
    intro m m'
    constructor
    · rintro ⟨b, hb, hsim⟩
      have heq : 𝔐.α m • Pi.single (𝔐.t m) (1 : ℝ) =
          b • (𝔐.α m' • Pi.single (𝔐.t m') (1 : ℝ)) := by
        apply Matrix.mulVec_injective_of_isUnit hBunit
        rw [hshift m, hshift m', 𝔐.atomic m, 𝔐.atomic m'] at hsim
        simpa only [Matrix.mulVec_smul] using hsim
      by_contra hne
      have hi := congrFun heq (𝔐.t m)
      simp [hne] at hi
      exact 𝔐.nonvanishing m hi
    · intro htarget
      refine ⟨𝔐.α m / 𝔐.α m', div_ne_zero (𝔐.nonvanishing m)
        (𝔐.nonvanishing m'), ?_⟩
      rw [hshift m, hshift m', 𝔐.atomic m, 𝔐.atomic m', htarget]
      rw [← Matrix.mulVec_smul, smul_smul]
      congr 1
      rw [div_mul_cancel₀ (𝔐.α m) (𝔐.nonvanishing m')]
  have hcol (m : Fin p) (i : Fin p) :
      obsShift μ 𝔐 m i = 𝔐.α m * totalEffect 𝔐.A i (𝔐.t m) := by
    rw [hshift m, 𝔐.atomic m]
    simp [Matrix.mulVec_smul, Matrix.mulVec_single]
  have hnorm (m : Fin p) :
      obsShift μ 𝔐 m (𝔐.t m) ≠ 0 ∧
      ∀ i, obsShift μ 𝔐 m i / obsShift μ 𝔐 m (𝔐.t m) =
        totalEffect 𝔐.A i (𝔐.t m) := by
    constructor
    · simpa [hcol m, hdiag] using 𝔐.nonvanishing m
    · intro i
      rw [hcol m i, hcol m (𝔐.t m), hdiag]
      simp [𝔐.nonvanishing m]
  have hstack : normalizedStack μ 𝔐 ht = totalEffect 𝔐.A := by
    let σ := Equiv.ofBijective 𝔐.t ht
    apply Matrix.ext
    intro i j
    let m := σ.symm j
    have hm : 𝔐.t m = j := σ.apply_symm_apply j
    change obsShift μ 𝔐 m i / obsShift μ 𝔐 m j = _
    rw [← hm]
    exact (hnorm m).2 i
  refine ⟨hnorm, ?_, ?_⟩
  · rw [hstack]
    simp only [totalEffect]
    have hC : IsUnit (1 - 𝔐.A).det := Matrix.isUnit_nonsing_inv_det_iff.mp hB
    rw [Matrix.nonsing_inv_nonsing_inv _ hC]
    simp
  · intro m m'
    rw [hproj m m']
    exact ht.1.eq_iff

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
