module

public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.StructuralMean
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.Matching
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.Triangular
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.CompatibleModelRealization
public import CausalSmith.ExactID.EID_CountshiftUnlabeledMatching_Research.Helpers.SameLawCompletionFibers

/-! Compatibility and sharp completion of unlabeled count shifts. -/

public section

open MeasureTheory Matrix

namespace CausalSmith.ExactID.EIDCountshiftUnlabeledMatching

/-- Observable expectations agree when the count-offset laws agree. -/
-- @node: obsLaw_integral_congr
lemma obsLaw_integral_congr {p M : ℕ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (μ' : Measure Ω')
    (𝔐 : AtomicCountModel p M Ω μ) (𝔐' : AtomicCountModel p M Ω' μ')
    (m : Fin (M + 1))
    (hobs : AEMeasurable (fun ω => (𝔐.S m ω, 𝔐.X m ω)) μ)
    (hobs' : AEMeasurable (fun ω => (𝔐'.S m ω, 𝔐'.X m ω)) μ')
    (hlaw : obsLaw μ 𝔐 m = obsLaw μ' 𝔐' m)
    (F : ((Fin p → ℝ) × (Fin p → ℕ)) → ℝ) (hF : Measurable F) :
    (∫ ω, F (𝔐.S m ω, 𝔐.X m ω) ∂μ) =
      ∫ ω, F (𝔐'.S m ω, 𝔐'.X m ω) ∂μ' := by
  have hleft := integral_map hobs hF.aestronglyMeasurable
  have hright := integral_map hobs' hF.aestronglyMeasurable
  change (∫ y, F y ∂obsLaw μ 𝔐 m) = _ at hleft
  change (∫ y, F y ∂obsLaw μ' 𝔐' m) = _ at hright
  rw [hlaw] at hleft
  exact hleft.symm.trans hright

/-- Observable shifts and their law-indexed fiber, followed by the exact
compatibility and completion characterization for an arbitrary direction family. -/
-- @node: thm:compatibility-completion
theorem compatibility_completion {p : ℕ} (hp : 0 < p)
    :
    (∀ (M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω)
      (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∀ 𝔐 : AtomicCountModel p M Ω μ,
        (∀ m, obsShift μ 𝔐 m =
          totalEffect 𝔐.A *ᵥ
            (fun i => 𝔐.η m.succ i - 𝔐.η 0 i)) ∧
        ∀ m, obsShift μ 𝔐 m ≠ 0) ∧
    (∀ (M : ℕ) (Ω Ω' : Type)
      (ms : MeasurableSpace Ω) (ms' : MeasurableSpace Ω')
      (μ : Measure Ω) (μ' : Measure Ω'),
      letI : MeasurableSpace Ω := ms
      letI : MeasurableSpace Ω' := ms'
      ∀ (𝔐 : AtomicCountModel p M Ω μ)
        (𝔐' : AtomicCountModel p M Ω' μ'),
        (∀ m, obsLaw μ 𝔐 m = obsLaw μ' 𝔐' m) →
        ∀ r : ProjectiveReduction (obsShift μ 𝔐),
          ∃ r' : ProjectiveReduction (obsShift μ' 𝔐'),
            lawIndexedFiber μ 𝔐 r = lawIndexedFiber μ' 𝔐' r') ∧
    (∀ (q' : ℕ) (v : Fin q' → Fin p → ℝ) (scale : Fin q' → ℝ),
      (∀ g, scale g ≠ 0) →
      assignmentFiber (fun g => scale g • v g) = assignmentFiber v ∧
      completionFiber (fun g => scale g • v g) = completionFiber v ∧
      coefficientFiber (fun g => scale g • v g) = coefficientFiber v) ∧
    (∀ (q : ℕ) (hq : 0 < q) (v : Fin q → Fin p → ℝ),
      (∀ g, v g ≠ 0) →
      (∀ g h, g ≠ h → ¬ ProjSim v g h) →
    ((∃ (M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω)
        (μ : Measure Ω),
        letI : MeasurableSpace Ω := ms
        ∃ 𝔐 : AtomicCountModel p M Ω μ,
          GeneratesDirections μ 𝔐 v) ↔
      (assignmentFiber v).Nonempty) ∧
    ((assignmentFiber v).Nonempty ↔
      ∃ f : Fin q ↪ Fin p,
        (∀ g, f g ∈ support v g) ∧
        ∀ e : Fin q ↪ Fin p,
          (∀ g, e g ∈ support v g ∧ e g ∈ Set.range f) → e = f) ∧
    ((assignmentFiber v).Nonempty ↔
      peelsAll (fun g => support v g)) ∧
    (∀ (M : ℕ) (Ω : Type) (ms : MeasurableSpace Ω)
      (μ : Measure Ω),
      letI : MeasurableSpace Ω := ms
      ∀ 𝔐 : AtomicCountModel p M Ω μ,
      GeneratesDirections μ 𝔐 v →
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
            ∀ x : Fin p → ℕ,
              0 < μ {ω | 𝔐'.X m ω = x}) ∧
          (∀ m, 𝔐'.η m = (sameLawCompletion μ v 𝔐 B' hB').2.1 m ∧
            𝔐'.Ωc m = (sameLawCompletion μ v 𝔐 B' hB').2.2.1 m ∧
            𝔐'.ξ m = (sameLawCompletion μ v 𝔐 B' hB').2.2.2.1 m) ∧
          (sameLawCompletion μ v 𝔐 B' hB').2.2.2.2 =
            poissonCountLaw ∧
      𝔐'.S = 𝔐.S ∧ 𝔐'.X = 𝔐.X)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M Ω ms μ
    letI : MeasurableSpace Ω := ms
    intro 𝔐
    have hshift (m : Fin M) : obsShift μ 𝔐 m =
        totalEffect 𝔐.A *ᵥ (fun i => 𝔐.η m.succ i - 𝔐.η 0 i) := by
      funext j
      rw [obsShift, obsMean_eq_structural_mean μ 𝔐 m.succ,
        obsMean_eq_structural_mean μ 𝔐 0]
      exact (congrFun (Matrix.mulVec_sub (totalEffect 𝔐.A)
        (𝔐.η m.succ) (𝔐.η 0)) j).symm
    refine ⟨hshift, ?_⟩
    intro m hzero
    have hdiag := acyclic_mechanism_totalEffect_diagonal 𝔐.A 𝔐.acyclic
    have hval := congrFun hzero (𝔐.t m)
    rw [hshift m, 𝔐.atomic m] at hval
    simp [Matrix.mulVec_smul, Matrix.mulVec_single, hdiag] at hval
    exact 𝔐.nonvanishing m hval
  · intro M Ω Ω' ms ms' μ μ'
    letI : MeasurableSpace Ω := ms
    letI : MeasurableSpace Ω' := ms'
    intro 𝔐 𝔐' hlaw r
    have hobs (m : Fin (M + 1)) :
        AEMeasurable (fun ω => (𝔐.S m ω, 𝔐.X m ω)) μ :=
      PoissonMeasurement.obs_aemeasurable μ 𝔐.poisson m ()
    have hobs' (m : Fin (M + 1)) :
        AEMeasurable (fun ω => (𝔐'.S m ω, 𝔐'.X m ω)) μ' :=
      PoissonMeasurement.obs_aemeasurable μ' 𝔐'.poisson m ()
    have hfirst (m : Fin (M + 1)) (j : Fin p) :
        (∫ ω, firstFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) =
          ∫ ω, firstFactorial (𝔐'.X m ω) (𝔐'.S m ω) j ∂μ' := by
      let F : ((Fin p → ℝ) × (Fin p → ℕ)) → ℝ :=
        fun sx => firstFactorial sx.2 sx.1 j
      have hF : Measurable F := by
        dsimp [F, firstFactorial]
        fun_prop
      exact obsLaw_integral_congr μ μ' 𝔐 𝔐' m (hobs m) (hobs' m)
        (hlaw m) F hF
    have hsecond (m : Fin (M + 1)) (j : Fin p) :
        (∫ ω, secondFactorial (𝔐.X m ω) (𝔐.S m ω) j ∂μ) =
          ∫ ω, secondFactorial (𝔐'.X m ω) (𝔐'.S m ω) j ∂μ' := by
      let F : ((Fin p → ℝ) × (Fin p → ℕ)) → ℝ :=
        fun sx => secondFactorial sx.2 sx.1 j
      have hF : Measurable F := by
        dsimp [F, secondFactorial]
        fun_prop
      exact obsLaw_integral_congr μ μ' 𝔐 𝔐' m (hobs m) (hobs' m)
        (hlaw m) F hF
    have hmean (m : Fin (M + 1)) : obsMean μ 𝔐 m = obsMean μ' 𝔐' m := by
      funext j
      simp only [obsMean, hfirst, hsecond]
    have hshift : obsShift μ 𝔐 = obsShift μ' 𝔐' := by
      funext m j
      simp only [obsShift, congrFun (hmean m.succ) j, congrFun (hmean 0) j]
    have htransport (d d' : Fin M → Fin p → ℝ) (h : d = d')
        (r : ProjectiveReduction d) :
        ∃ r' : ProjectiveReduction d',
          (⟨r.q, structuralFiber r.v⟩ :
            Σ q : ℕ, Set (Fin q ↪ Fin p) ×
              Set (Matrix (Fin p) (Fin p) ℝ) ×
              Set (Matrix (Fin p) (Fin p) ℝ)) =
          ⟨r'.q, structuralFiber r'.v⟩ := by
      subst d'
      exact ⟨r, rfl⟩
    simpa only [lawIndexedFiber] using htransport _ _ hshift r
  · intro q v scale hscale
    let w : Fin q → Fin p → ℝ := fun g => scale g • v g
    have hsupp (g : Fin q) : support w g = support v g := by
      ext i
      simp [support, w, Pi.smul_apply, smul_eq_mul, hscale g]
    have hgraph (f : Fin q ↪ Fin p) (i j : Fin p) :
        Hf w f i j ↔ Hf v f i j := by
      simp only [Hf, hsupp]
    have hassign : assignmentFiber w = assignmentFiber v := by
      ext f
      simp only [assignmentFiber, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hmem, hac⟩
        exact ⟨fun g => hsupp g ▸ hmem g,
          fun i hc => hac i (hc.lift id (fun _ _ h => (hgraph f _ _).mpr h))⟩
      · rintro ⟨hmem, hac⟩
        exact ⟨fun g => (hsupp g).symm ▸ hmem g,
          fun i hc => hac i (hc.lift id (fun _ _ h => (hgraph f _ _).mp h))⟩
    have hslice (f : Fin q ↪ Fin p) : completionFiberAt w f = completionFiberAt v f := by
      ext B
      have hratio (g : Fin q) (i : Fin p) :
          w g i / w g (f g) = v g i / v g (f g) := by
        simp [w, Pi.smul_apply, smul_eq_mul, mul_div_mul_left, hscale g]
      simp only [completionFiberAt, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hcol, hdiag, hac⟩
        exact ⟨fun g i => (hcol g i).trans (hratio g i), hdiag, hac⟩
      · rintro ⟨hcol, hdiag, hac⟩
        exact ⟨fun g i => (hcol g i).trans (hratio g i).symm, hdiag, hac⟩
    have hcompletion : completionFiber w = completionFiber v := by
      simp only [completionFiber, hassign, hslice]
    refine ⟨hassign, hcompletion, ?_⟩
    change coefficientFiber w = coefficientFiber v
    rw [coefficientFiber, coefficientFiber, hcompletion]
  · intro q hq v hvne hvdistinct
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact compatible_model_exists_iff_assignment_nonempty hp hq v hvne hvdistinct
    · constructor
      · rintro ⟨f, hf⟩
        exact ⟨f, (assignment_iff_unique_induced_matching v f).mp hf⟩
      · rintro ⟨f, hf⟩
        exact ⟨f, (assignment_iff_unique_induced_matching v f).mpr hf⟩
    · exact assignment_nonempty_iff_peelsAll v
    · intro M Ω ms μ
      letI : MeasurableSpace Ω := ms
      intro 𝔐 hgen
      exact sameLawCompletion_fiber_exactness μ v 𝔐 hgen

end CausalSmith.ExactID.EIDCountshiftUnlabeledMatching
