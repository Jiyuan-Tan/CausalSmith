import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSharpRegretFormula

/-! Perfect-reference sanity reduction. -/

open MeasureTheory

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def PerfectReferenceConclusion (M : ImperfectReferenceModel)
    (ν : Bool → Measure ℝ) (Q : CompatibleCompletion M) : Prop :=
  prevalence M = obsMass M true ∧
  ν true = obsMeasure M true ∧ ν false = 0 ∧
  (∀ t, massLower M (referSet t) = massUpper M (referSet t)) ∧
  jointCurveSet M = {fun t : Cutoff M =>
    (stratumMass M true (referSet t.1) / obsMass M true,
     stratumMass M false (referSet t.1) / obsMass M false,
     M.b * stratumMass M true (referSet t.1) -
       M.c * stratumMass M false (referSet t.1))} ∧
  (∀ t : Cutoff M, regretAt M t =
    sSup {x : ℝ | ∃ u : Cutoff M,
      x = netValueAt M Q u.1 - netValueAt M Q t.1})

-- @node: prop:perfect-reference-reduction
theorem perfect_reference_reduction (M : ImperfectReferenceModel)
    (Q : Measure (ℝ × Bool × Bool)) (hQ : CompatibleLaw M Q)
    (ν : Bool → Measure ℝ) (hν : DominatedAllocation M ν)
    (hperfect : M.alpha = 1 ∧ M.beta = 1) :
    PerfectReferenceConclusion M ν ⟨Q, hQ⟩ := by
  have hprev : prevalence M = obsMass M true := by
    simp [prevalence, youden, hperfect.1, hperfect.2]
  have ha_true : diseaseMass M true = obsMass M true := by
    simp [diseaseMass, hperfect.1, hprev]
  have ha_false : diseaseMass M false = 0 := by
    simp [diseaseMass, hperfect.1]
  have hnu_true : ν true = obsMeasure M true := by
    letI : IsFiniteMeasure (ν true) :=
      isFiniteMeasure_of_le (obsMeasure M true) (hν.domination true)
    apply Measure.eq_of_le_of_measure_univ_eq (hν.domination true)
    apply (ENNReal.toReal_eq_toReal_iff'
      (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (ν true).real Set.univ = (obsMeasure M true).real Set.univ
    calc
      _ = diseaseMass M true := hν.mass true
      _ = obsMass M true := ha_true
      _ = _ := rfl
  have hnu_false : ν false = 0 := by
    letI : IsFiniteMeasure (ν false) :=
      isFiniteMeasure_of_le (obsMeasure M false) (hν.domination false)
    rw [← Measure.measure_univ_eq_zero, ← measureReal_eq_zero_iff]
    simpa [ha_false] using hν.mass false
  have allocation_unique (ξ : Bool → Measure ℝ)
      (hξ : DominatedAllocation M ξ) : ξ = ν := by
    have hξ_true : ξ true = obsMeasure M true := by
      letI : IsFiniteMeasure (ξ true) :=
        isFiniteMeasure_of_le (obsMeasure M true) (hξ.domination true)
      apply Measure.eq_of_le_of_measure_univ_eq (hξ.domination true)
      apply (ENNReal.toReal_eq_toReal_iff'
        (measure_ne_top _ _) (measure_ne_top _ _)).mp
      change (ξ true).real Set.univ = (obsMeasure M true).real Set.univ
      calc
        _ = diseaseMass M true := hξ.mass true
        _ = obsMass M true := ha_true
        _ = _ := rfl
    have hξ_false : ξ false = 0 := by
      letI : IsFiniteMeasure (ξ false) :=
        isFiniteMeasure_of_le (obsMeasure M false) (hξ.domination false)
      rw [← Measure.measure_univ_eq_zero, ← measureReal_eq_zero_iff]
      simpa [ha_false] using hξ.mass false
    funext r
    cases r <;> simp [hξ_false, hnu_false, hξ_true, hnu_true]
  refine ⟨hprev, hnu_true, hnu_false, ?_, ?_, ?_⟩
  · intro t
    simp only [massLower, massUpper, massEndpoints, Fintype.sum_bool,
      diseaseMass, hperfect.1, hprev]
    have htrue : stratumMass M true (referSet t) ≤ obsMass M true :=
      measureReal_mono (Set.subset_univ _)
    have htrue0 : 0 ≤ stratumMass M true (referSet t) := measureReal_nonneg
    have hfalse : 0 ≤ stratumMass M false (referSet t) := measureReal_nonneg
    have hfalse_le : stratumMass M false (referSet t) ≤ obsMass M false :=
      measureReal_mono (Set.subset_univ _)
    simp [htrue, htrue0, hfalse, hfalse_le]
  · have hq : 1 - obsMass M true = obsMass M false := by
      linarith [obsMass_false_add_true M]
    have hcurve : allocationCurve M ν = fun t : Cutoff M =>
        (stratumMass M true (referSet t.1) / obsMass M true,
         stratumMass M false (referSet t.1) / obsMass M false,
         M.b * stratumMass M true (referSet t.1) -
           M.c * stratumMass M false (referSet t.1)) := by
      funext t
      simp [allocationCurve, hnu_true, hnu_false, hprev, hq,
        Fintype.sum_bool, stratumMass]
      ring
    rw [(submeasure_bijection M hQ.informative hQ.interior Q hQ).2.2]
    ext curve
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨ξ, hξ, rfl⟩
      have hξν := allocation_unique ξ hξ
      simpa [hξν] using hcurve
    · intro hcurve'
      refine ⟨ν, hν, ?_⟩
      exact hcurve.trans hcurve'.symm
  · intro t
    apply congrArg sSup
    ext x
    constructor
    · rintro ⟨Q', u, rfl⟩
      have hbij := (submeasure_bijection M hQ.informative hQ.interior Q hQ).1
      have hallocQ' := hbij.mapsTo Q'.2
      have hallocQ := hbij.mapsTo hQ
      have hQQ : Q'.1 = Q := hbij.injOn Q'.2 hQ
        ((allocation_unique _ hallocQ').trans (allocation_unique _ hallocQ).symm)
      have hQc : Q ∈ compatibleLaws M := hQ
      have hQQsub : Q' = (⟨Q, hQc⟩ : CompatibleCompletion M) := Subtype.ext hQQ
      exact ⟨u, by rw [hQQsub]⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨Q, hQ⟩, u, rfl⟩

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
