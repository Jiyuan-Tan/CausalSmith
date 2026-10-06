module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.FourthDerivative

/-! # Assembly of the observable marked-density reduction

Combines the observable channel identities with explicit coordinate derivative bounds.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

-- @node: lem:observable-marked-reduction
/-- Given [the supplied inputs](hyp:c_f,C_f,L,P,n,hf,hF,hL,hP), [the stated result about observable marked reduction holds](goal). -/
lemma observable_marked_reduction (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hf : 0 < c_f ∧ c_f < 1) (hF : 1 < C_f) (hL : 1 < L)
    (hP : ModelClass c_f C_f L P n) :
    (∀ i : Fin 7, ∀ B : Set ℝ, MeasurableSet B → B ⊆ covariateSpace →
      (∫ x in B, markedDensityVector c_f C_f L P n hP x i) =
        if i.val = 0 then (targetXLaw P B).toReal else
          ∫ o in {o | o.1 ∈ B}, coordinateMark i o ∂sourceObsLaw P) ∧
    (∀ x ∈ covariateSpace,
      c_f / 4 ≤ markedDensityVector c_f C_f L P n hP x 1 ∧
      c_f / 4 ≤ markedDensityVector c_f C_f L P n hP x 2) ∧
    (∀ A : Bool, transportedForm P A =
      ∫ x in (0 : ℝ)..1, Phi A (markedDensityVector c_f C_f L P n hP x)) ∧
    (∀ A : Bool, ∀ v : Fin 7 → ℝ,
      clippingRectangle c_f C_f v →
      ∀ k : Fin 5, ∀ dirs : Fin k.val → Fin 7,
        |iteratedFDeriv ℝ k.val (Phi A) v
          (fun j => coordinateBasis (dirs j))| ≤
          fourthDerivativeEnvelope c_f C_f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i B hB hsub
    by_cases hi : i.val = 0
    · have hi0 : i = 0 := Fin.ext hi
      subst i
      simp only [markedDensityVector, Matrix.cons_val_zero]
      have hcont : ContinuousOn P.fT covariateSpace := by
        have hcd := hP.targetHolder.2.1.continuousOn
        have hmap : ContinuousOn (fun x : ℝ => ![x]) covariateSpace := by fun_prop
        have hmaps : MapsTo (fun x : ℝ => ![x]) covariateSpace
            {v : Fin 1 → ℝ | v 0 ∈ covariateSpace} := by
          intro x hx
          simpa using hx
        simpa [Function.comp_def, Matrix.cons_val_zero] using hcd.comp hmap hmaps
      have hae : AEMeasurable (fun x : ℝ => ENNReal.ofReal (P.fT x))
          ((volume.restrict covariateSpace).restrict B) :=
        (hcont.aemeasurable measurableSet_Icc).ennreal_ofReal.restrict
      have hfinite : ∀ᵐ x ∂(volume.restrict covariateSpace).restrict B,
          ENNReal.ofReal (P.fT x) < ⊤ := by filter_upwards [] with x; simp
      have hden := setIntegral_withDensity_eq_setIntegral_toReal_smul₀
        (f := fun x : ℝ => ENNReal.ofReal (P.fT x))
        (s := B) hae hfinite (fun _ => (1 : ℝ)) hB
      have hmass :
          ((targetXLaw P) B).toReal = ∫ x in B, P.fT x := by
        rw [hP.targetBounds.1]
        calc
          (((volume.restrict covariateSpace).withDensity
            (fun x => ENNReal.ofReal (P.fT x))) B).toReal =
              ∫ x in B, (1 : ℝ) ∂(volume.restrict covariateSpace).withDensity
                (fun x => ENNReal.ofReal (P.fT x)) := by simp [Measure.real]
          _ = ∫ x in B, (ENNReal.ofReal (P.fT x)).toReal • (1 : ℝ)
                ∂volume := by
              simpa only [Measure.restrict_restrict_of_subset hsub] using hden
          _ = ∫ x in B, P.fT x := by
            apply setIntegral_congr_fun hB
            intro x hx
            simp [ENNReal.toReal_ofReal
              (le_trans hf.1.le (hP.targetBounds.2.1 x (hsub hx)).1)]
      simpa using hmass.symm
    · fin_cases i
      · simp at hi
      · simpa [markedDensityVector, coordinateMark, boolReal, assignmentMass] using
          (source_assignment_density c_f C_f L P n hP false B hB hsub).trans
            (source_assignment_mark_integral P false B hB).symm
      · simpa [markedDensityVector, coordinateMark, boolReal, assignmentMass] using
          (source_assignment_density c_f C_f L P n hP true B hB hsub).trans
            (source_assignment_mark_integral P true B hB).symm
      · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass,
          boolReal] using source_marked_arm_density c_f C_f L P n hP true false B hB hsub
      · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass,
          boolReal] using source_marked_arm_density c_f C_f L P n hP true true B hB hsub
      · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass,
          boolReal] using source_marked_arm_density c_f C_f L P n hP false false B hB hsub
      · simpa [markedDensityVector, coordinateMark, armValue, assignmentMass,
          boolReal] using source_marked_arm_density c_f C_f L P n hP false true B hB hsub
  · intro x hx
    exact markedDensityVector_assignment_lower_bounds c_f C_f L P n hP x hx
  · intro A
    exact transportedForm_eq_integral_Phi_markedDensityVector c_f C_f L P n hP A
  · intro A v hv k dirs
    by_cases hk : k.val = 0
    · have hk0 : k = 0 := Fin.ext hk
      subst k
      simpa [iteratedFDeriv_zero_apply] using
        Phi_value_abs_le_fourthDerivativeEnvelope c_f C_f hf hF A v hv
    · by_cases hk1 : k.val = 1
      · have hkone : k = 1 := Fin.ext hk1
        subst k
        change Fin 1 → Fin 7 at dirs
        change |iteratedFDeriv ℝ 1 (Phi A) v (fun j => coordinateBasis (dirs j))| ≤ _
        have hdirs : (fun j => coordinateBasis (dirs j)) = ![coordinateBasis (dirs 0)] := by
          funext j
          fin_cases j
          rfl
        rw [hdirs]
        exact Phi_first_derivative_abs_le_fourthDerivativeEnvelope c_f C_f hf hF A v hv (dirs 0)
      · by_cases hk2 : k.val = 2
        · have hktwo : k = 2 := Fin.ext hk2
          subst k
          change Fin 2 → Fin 7 at dirs
          change |iteratedFDeriv ℝ 2 (Phi A) v (fun j => coordinateBasis (dirs j))| ≤ _
          have hdirs : (fun j => coordinateBasis (dirs j)) =
              ![basis (dirs 0), basis (dirs 1)] := by
            funext j
            fin_cases j <;> rfl
          rw [hdirs]
          exact dPhi2_abs_le c_f C_f hf hF A v hv (dirs 0) (dirs 1)
        · by_cases hk3 : k.val = 3
          · have hkthree : k = 3 := Fin.ext hk3
            subst k
            change Fin 3 → Fin 7 at dirs
            change |iteratedFDeriv ℝ 3 (Phi A) v (fun j => coordinateBasis (dirs j))| ≤ _
            have hdirs : (fun j => coordinateBasis (dirs j)) =
                ![basis (dirs 0), basis (dirs 1), basis (dirs 2)] := by
              funext j
              fin_cases j <;> rfl
            rw [hdirs]
            exact dPhi3_abs_le c_f C_f hf hF A v hv (dirs 0) (dirs 1) (dirs 2)
          · -- The only remaining derivative order is four.
            have hk4 : k.val = 4 := by omega
            have hkfour : k = 4 := Fin.ext hk4
            subst k
            change Fin 4 → Fin 7 at dirs
            change |iteratedFDeriv ℝ 4 (Phi A) v (fun j => coordinateBasis (dirs j))| ≤ _
            have hdirs : (fun j => coordinateBasis (dirs j)) =
                ![basis (dirs 0), basis (dirs 1), basis (dirs 2), basis (dirs 3)] := by
              funext j
              fin_cases j <;> rfl
            rw [hdirs]
            exact dPhi4_abs_le c_f C_f hf hF A v hv (dirs 0) (dirs 1) (dirs 2) (dirs 3)

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
