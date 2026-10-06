module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.SameLawCompletionRealization

/-! Fiber consequences of same-law structural completion. -/

public section
noncomputable section
open MeasureTheory Matrix
namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

-- @node: generatedDirections_totalEffect_mem_completionFiber
lemma generatedDirections_totalEffect_mem_completionFiber {p q M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (v : Fin q → Fin p → ℝ) (hgen : GeneratesDirections μ 𝔐 v) :
    totalEffect 𝔐.A ∈ completionFiber v := by
  classical
  obtain ⟨r, hrq, e, he⟩ := hgen
  have hshift (m : Fin M) : obsShift μ 𝔐 m =
      𝔐.α m • (totalEffect 𝔐.A).col (𝔐.t m) := by
    rw [show obsShift μ 𝔐 m = totalEffect 𝔐.A *ᵥ
        (fun i => 𝔐.η m.succ i - 𝔐.η 0 i) by
      funext j
      rw [obsShift, obsMean_eq_structural_mean μ 𝔐 m.succ,
        obsMean_eq_structural_mean μ 𝔐 0]
      exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
        (𝔐.η m.succ) (𝔐.η 0)) j).symm,
      𝔐.atomic m, Matrix.mulVec_smul, Matrix.mulVec_single]
    simp [MulOpposite.op_one]
  have hrep (g : Fin q) : ∃ m : Fin M, r.κ m = e.symm g := by
    have : Fin r.q = Fin q := congrArg Fin hrq
    exact r.κ_surj (e.symm g)
  let m : Fin q → Fin M := fun g => Classical.choose (hrep g)
  have hm (g : Fin q) : r.κ (m g) = e.symm g := Classical.choose_spec (hrep g)
  let f0 : Fin q → Fin p := fun g => 𝔐.t (m g)
  have hf0 : Function.Injective f0 := by
    intro g h hgh
    by_contra hne
    have hpj : ProjSim (obsShift μ 𝔐) (m g) (m h) := by
      refine ⟨𝔐.α (m g) / 𝔐.α (m h),
        div_ne_zero (𝔐.nonvanishing _) (𝔐.nonvanishing _), ?_⟩
      rw [hshift, hshift]
      change 𝔐.t (m g) = 𝔐.t (m h) at hgh
      rw [hgh, smul_smul, div_mul_cancel₀ _ (𝔐.nonvanishing _)]
    have hk := (r.classes (m g) (m h)).mpr hpj
    rw [hm, hm] at hk
    exact hne (e.symm.injective hk)
  let f : Fin q ↪ Fin p := ⟨f0, hf0⟩
  have hsupport (g : Fin q) : f g ∈ support v g := by
    have hd := r.decomp (m g)
    rw [hm g, he (e.symm g), e.apply_symm_apply, hshift] at hd
    have hv : v g (f g) ≠ 0 := by
      intro hz
      have := congrFun hd (f g)
      change 𝔐.α (m g) * totalEffect 𝔐.A (f g) (f g) =
        r.c (m g) * v g (f g) at this
      rw [acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic, hz,
        mul_one, mul_zero] at this
      exact 𝔐.nonvanishing _ this
    simpa [support] using hv
  have hac : ∀ i, ¬ Relation.TransGen (Hf v f) i i := by
    intro i hc
    apply acyclic_mechanism_totalEffect_acyclic 𝔐.A 𝔐.acyclic i
    apply hc.lift id
    rintro a b ⟨g, rfl, hb, hne⟩
    have hd := r.decomp (m g)
    rw [hm g, he (e.symm g), e.apply_symm_apply, hshift] at hd
    have hvb : v g b ≠ 0 := by simpa [support] using hb
    refine ⟨hne.symm, ?_⟩
    intro hz
    have := congrFun hd b
    change 𝔐.α (m g) * totalEffect 𝔐.A b (f g) = r.c (m g) * v g b at this
    have hz' : totalEffect 𝔐.A b (f g) = 0 := by simpa using hz
    rw [hz', mul_zero] at this
    exact hvb (mul_eq_zero.mp this.symm |>.resolve_left (r.c_ne _))
  have hf : f ∈ assignmentFiber v := ⟨hsupport, hac⟩
  simp only [completionFiber, Set.mem_iUnion]
  refine ⟨f, hf, ?_, acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic,
    acyclic_mechanism_totalEffect_acyclic 𝔐.A 𝔐.acyclic⟩
  intro g i
  have hd := r.decomp (m g)
  rw [hm g, he (e.symm g), e.apply_symm_apply, hshift] at hd
  have ht := congrFun hd (f g)
  have hi := congrFun hd i
  change 𝔐.α (m g) * totalEffect 𝔐.A (f g) (f g) =
      r.c (m g) * v g (f g) at ht
  rw [acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic, mul_one] at ht
  change 𝔐.α (m g) * totalEffect 𝔐.A i (f g) = r.c (m g) * v g i at hi
  rw [ht] at hi
  have hc := r.c_ne (m g)
  have hv := by simpa [support] using hsupport g
  apply (eq_div_iff hv).2
  rw [mul_assoc] at hi
  have hcancel := mul_left_cancel₀ hc hi
  nlinarith


open ProbabilityTheory
-- @node: atomicCountModel_count_full_support
lemma atomicCountModel_count_full_support {p M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (𝔐 : AtomicCountModel p M Ω μ)
    (m : Fin (M + 1)) (x : Fin p → ℕ) : 0 < μ {ω | 𝔐.X m ω = x} := by
  letI : IsProbabilityMeasure μ := (𝔐.gaussian m).2.isProbabilityMeasure
  let Z := latentState 𝔐.A 𝔐.η 𝔐.ξ m
  let F : Ω → ((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℕ) :=
    fun ω => ((𝔐.S m ω, Z ω), 𝔐.X m ω)
  let A : Set (((Fin p → ℝ) × (Fin p → ℝ)) × (Fin p → ℕ)) := {y | y.2 = x}
  have hA : MeasurableSet A := by measurability
  have hF := (𝔐.poisson m ()).2.2.1
  have hpre : F ⁻¹' A = {ω | 𝔐.X m ω = x} := rfl
  rw [← hpre, ← Measure.map_apply_of_aemeasurable hF hA]
  rw [(𝔐.poisson m ()).2.2.2]
  rw [Measure.bind_apply hA poissonCountLaw_attach_measurable_general.aemeasurable]
  have heval (sz : (Fin p → ℝ) × (Fin p → ℝ)) :
      ((poissonCountLaw sz.1 sz.2).map (fun y => (sz, y))) A =
        poissonCountLaw sz.1 sz.2 {x} := by
    rw [Measure.map_apply (by fun_prop) hA]
    congr 1
  simp_rw [heval]
  have hmeas : Measurable (fun sz : (Fin p → ℝ) × (Fin p → ℝ) =>
      poissonCountLaw sz.1 sz.2 {x}) := by
    exact (Measure.measurable_coe (MeasurableSet.singleton x)).comp
      poissonCountLaw_parameter_measurable
  rw [lintegral_pos_iff_support hmeas]
  have hpos : ∀ᵐ ω ∂μ, 0 < poissonCountLaw (𝔐.S m ω) (Z ω) {x} := by
    filter_upwards [(𝔐.poisson m ()).1] with ω hs
    rw [poissonCountLaw, Measure.pi_singleton]
    rw [pos_iff_ne_zero]
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    have hrate : Real.toNNReal
        (𝔐.S m ω j * Real.exp (Z ω j)) ≠ 0 := by
      exact ne_of_gt (Real.toNNReal_pos.mpr (mul_pos (hs j) (Real.exp_pos _)))
    rw [poissonMeasure_singleton]
    positivity
  have hmap := (𝔐.poisson m ()).2.1
  rw [Measure.map_apply_of_aemeasurable hmap (measurableSet_support hmeas)]
  have hs : (fun ω => (𝔐.S m ω, Z ω)) ⁻¹'
      Function.support (fun sz => poissonCountLaw sz.1 sz.2 {x}) =ᵐ[μ]
      Set.univ := by
    filter_upwards [hpos] with ω hω
    change ((poissonCountLaw (𝔐.S m ω) (Z ω) {x} ≠ 0) = True)
    apply propext
    simp [ne_of_gt hω]
  rw [measure_congr hs, measure_univ]
  simp


-- @node: sameLawCompletion_fiber_exactness
lemma sameLawCompletion_fiber_exactness {p q M : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (v : Fin q → Fin p → ℝ)
    (𝔐 : AtomicCountModel p M Ω μ) (hgen : GeneratesDirections μ 𝔐 v) :
    ({B : Matrix (Fin p) (Fin p) ℝ |
      ∃ 𝔐' : AtomicCountModel p M Ω μ,
        GeneratesDirections μ 𝔐' v ∧
        (∀ m, obsLaw μ 𝔐' m = obsLaw μ 𝔐 m) ∧
        totalEffect 𝔐'.A = B} = completionFiber v) ∧
    ({A : Matrix (Fin p) (Fin p) ℝ |
      ∃ 𝔐' : AtomicCountModel p M Ω μ,
        GeneratesDirections μ 𝔐' v ∧
        (∀ m, obsLaw μ 𝔐' m = obsLaw μ 𝔐 m) ∧
        𝔐'.A = A} = coefficientFiber v) ∧
    ∀ (B' : Matrix (Fin p) (Fin p) ℝ) (hB' : B' ∈ completionFiber v),
      ∃ 𝔐' : AtomicCountModel p M Ω μ,
        𝔐'.A = 1 - B'⁻¹ ∧
        (∀ m, (𝔐'.Ωc m).PosDef ∧
          obsLaw μ 𝔐' m = obsLaw μ 𝔐 m ∧
          ∀ x : Fin p → ℕ, 0 < μ {ω | 𝔐'.X m ω = x}) ∧
        (∀ m, 𝔐'.η m = (sameLawCompletion μ v 𝔐 B' hB').2.1 m ∧
          𝔐'.Ωc m = (sameLawCompletion μ v 𝔐 B' hB').2.2.1 m ∧
          𝔐'.ξ m = (sameLawCompletion μ v 𝔐 B' hB').2.2.2.1 m) ∧
        (sameLawCompletion μ v 𝔐 B' hB').2.2.2.2 = poissonCountLaw ∧
        𝔐'.S = 𝔐.S ∧ 𝔐'.X = 𝔐.X := by
  classical
  have hreal (B' : Matrix (Fin p) (Fin p) ℝ) (hB' : B' ∈ completionFiber v) :=
    sameLawCompletion_model μ v 𝔐 hgen B' hB'
  have hrecover (N : AtomicCountModel p M Ω μ) :
      1 - (totalEffect N.A)⁻¹ = N.A := by
    have hdiag : ∀ i, (1 - N.A) i i = 1 := by
      intro i
      simp [Matrix.sub_apply, N.acyclic.1 i]
    have hac : ∀ i, ¬ Relation.TransGen
        (fun j k => j ≠ k ∧ (1 - N.A) k j ≠ 0) i i := by
      intro i hc
      apply N.acyclic.2 i
      apply hc.lift id
      intro j k h
      have hjk : k ≠ j := h.1.symm
      have : (1 - N.A) k j = -N.A k j := by simp [Matrix.sub_apply, hjk]
      exact fun hz => h.2 (this.trans (neg_eq_zero.mpr hz))
    have hu := acyclic_unit_matrix_invertible (1 - N.A) hdiag hac
    unfold totalEffect
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    abel
  have hcompletion : ({B : Matrix (Fin p) (Fin p) ℝ |
      ∃ N : AtomicCountModel p M Ω μ, GeneratesDirections μ N v ∧
        (∀ m, obsLaw μ N m = obsLaw μ 𝔐 m) ∧ totalEffect N.A = B} =
      completionFiber v) := by
    ext B
    constructor
    · rintro ⟨N, hN, _, rfl⟩
      exact generatedDirections_totalEffect_mem_completionFiber μ N v hN
    · intro hB
      obtain ⟨N, hN, hA, _, _, hS, hX⟩ := hreal B hB
      refine ⟨N, hN, ?_, ?_⟩
      · intro m
        unfold obsLaw
        rw [hS, hX]
      · rw [hA]
        simp only [completionFiber, Set.mem_iUnion] at hB
        obtain ⟨f, hf, hs⟩ := hB
        exact (acyclic_completion_to_mechanism B hs.2.1 hs.2.2).2
  refine ⟨hcompletion, ?_, ?_⟩
  · ext A
    constructor
    · rintro ⟨N, hN, _, rfl⟩
      refine ⟨totalEffect N.A,
        generatedDirections_totalEffect_mem_completionFiber μ N v hN, ?_⟩
      exact hrecover N
    · rintro ⟨B, hB, rfl⟩
      obtain ⟨N, hN, hA, _, _, hS, hX⟩ := hreal B hB
      refine ⟨N, hN, ?_, hA⟩
      intro m
      unfold obsLaw
      rw [hS, hX]
  · intro B' hB'
    obtain ⟨N, hN, hA, hparams, hk, hS, hX⟩ := hreal B' hB'
    refine ⟨N, hA, ?_, hparams, hk, hS, hX⟩
    intro m
    refine ⟨(N.gaussian m).1, ?_, ?_⟩
    · unfold obsLaw
      rw [hS, hX]
    · intro x
      exact atomicCountModel_count_full_support μ N m x

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
