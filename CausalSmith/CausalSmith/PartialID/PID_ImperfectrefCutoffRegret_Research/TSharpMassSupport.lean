import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.Helpers.Capacities
import CausalSmith.PartialID.PID_ImperfectrefCutoffRegret_Research.TSubmeasureBijection

/-! Sharp interval and support function for dominated fixed-mass allocations. -/

open MeasureTheory
open scoped BigOperators Pointwise

namespace CausalSmith.PartialID.ImperfectrefCutoffRegret

noncomputable section

def allocationMass (I : BorelScoreSet) (ν : Bool → Measure ℝ) : ℝ :=
  ∑ r : Bool, (ν r).real I

abbrev BoundedBorelFunction :=
  {f : ℝ → ℝ // Measurable f ∧ ∃ C : ℝ, ∀ x, |f x| ≤ C}

def allocationSupport (f : Bool → BoundedBorelFunction)
    (ν : Bool → Measure ℝ) : ℝ :=
  ∑ r : Bool, ∫ s, (f r).1 s ∂(ν r)
  -- @realizes \(f_r\)(bounded Borel stratum objective carrier)

def allocationDual (M : ImperfectReferenceModel)
    (f : Bool → BoundedBorelFunction) : ℝ :=
  ∑ r : Bool, sInf {x : ℝ | ∃ l : ℝ,
    x = diseaseMass M r * l +
      ∫ s, max ((f r).1 s - l) 0 ∂(obsMeasure M r)}
  -- @realizes \(\lambda_r\)(outer real dual multiplier)

def SharpMassSupportConclusion (M : ImperfectReferenceModel) (I : BorelScoreSet)
    (f : Bool → BoundedBorelFunction) : Prop :=
  Causalean.PartialID.IdentifiedInterval (allocationMass I)
      (DominatedAllocation M) = Set.Icc (massLower M I) (massUpper M I) ∧
    (∃ ν, DominatedAllocation M ν ∧ allocationMass I ν = massLower M I) ∧
    (∃ ν, DominatedAllocation M ν ∧ allocationMass I ν = massUpper M I) ∧
    sSup {x : ℝ | ∃ ν, DominatedAllocation M ν ∧ x = allocationSupport f ν} =
      allocationDual M f

-- @node: thm:sharp-mass-support
theorem sharp_mass_support (M : ImperfectReferenceModel)
    (hg : InformativeReference M) (hπ : InteriorPrevalence M)
    (I : BorelScoreSet) (f : Bool → BoundedBorelFunction) :
    SharpMassSupportConclusion M I f := by
  have hinterval := dominatedAllocation_image_eq_Icc M hg hπ I
  have hlower : massLower M I ≤ massUpper M I := by
    have hstratum (r : Bool) : stratumLower M r I ≤ stratumUpper M r I := by
      have ha := diseaseMass_nonneg_le_obsMass M hg hπ r
      have hp0 : 0 ≤ stratumMass M r I := measureReal_nonneg
      have hpq : stratumMass M r I ≤ obsMass M r :=
        measureReal_mono (Set.subset_univ (I : Set ℝ))
      apply max_le
      · exact le_min ha.1 hp0
      · exact le_min (by linarith) (by linarith)
    simpa only [massLower, massUpper, massEndpoints, stratumLower, stratumUpper,
      Fintype.sum_bool] using add_le_add (hstratum true) (hstratum false)
  have hattain (y : ℝ) (hy : y ∈ Set.Icc (massLower M I) (massUpper M I)) :
      ∃ ν, DominatedAllocation M ν ∧ allocationMass I ν = y := by
    simpa [allocationMass] using mem_dominatedAllocation_image M hg hπ I hy
  refine ⟨?_, hattain _ ⟨le_rfl, hlower⟩,
    hattain _ ⟨hlower, le_rfl⟩, ?_⟩
  · change Causalean.PartialID.IdentifiedInterval
        (fun ν : Bool → Measure ℝ => ∑ r : Bool, (ν r).real I)
        (DominatedAllocation M) = Set.Icc (massLower M I) (massUpper M I)
    exact hinterval
  · let S : Bool → Set ℝ := fun r =>
      {x | ∃ ν : Measure ℝ, ν ≤ obsMeasure M r ∧
        ν.real Set.univ = diseaseMass M r ∧ x = allocationIntegral ν (f r).1}
    have hfeasible : ∃ ν, DominatedAllocation M ν := by
      obtain ⟨ν, hν, _⟩ := hattain (massLower M I) ⟨le_rfl, hlower⟩
      exact ⟨ν, hν⟩
    have hSne (r : Bool) : (S r).Nonempty := by
      obtain ⟨ν, hν⟩ := hfeasible
      exact ⟨allocationIntegral (ν r) (f r).1, ν r, hν.domination r,
        hν.mass r, rfl⟩
    have hSbdd (r : Bool) : BddAbove (S r) := by
      obtain ⟨C, hC⟩ := (f r).2.2
      refine ⟨C * diseaseMass M r, ?_⟩
      intro z hz
      rcases hz with ⟨ν, hνle, hνmass, rfl⟩
      letI : IsFiniteMeasure ν :=
        isFiniteMeasure_of_le (obsMeasure M r) hνle
      have habs : |allocationIntegral ν (f r).1| ≤ C * diseaseMass M r := by
        rw [← hνmass]
        simpa [allocationIntegral, Real.norm_eq_abs] using
          (norm_integral_le_of_norm_le_const (μ := ν) (f := (f r).1) (C := C)
            (Filter.Eventually.of_forall fun x => by
              simpa [Real.norm_eq_abs] using hC x))
      exact (le_abs_self _).trans habs
    have hsupportSet :
        {x : ℝ | ∃ ν, DominatedAllocation M ν ∧ x = allocationSupport f ν} =
          S true + S false := by
      ext z
      rw [Set.mem_add]
      constructor
      · rintro ⟨ν, hν, rfl⟩
        refine ⟨allocationIntegral (ν true) (f true).1, ?_,
          allocationIntegral (ν false) (f false).1, ?_, ?_⟩
        · exact ⟨ν true, hν.domination true, hν.mass true, rfl⟩
        · exact ⟨ν false, hν.domination false, hν.mass false, rfl⟩
        · simp [allocationSupport, allocationIntegral, Fintype.sum_bool]
      · rintro ⟨x₁, ⟨ν₁, hν₁le, hν₁mass, rfl⟩,
          x₀, ⟨ν₀, hν₀le, hν₀mass, rfl⟩, hsum⟩
        let ν : Bool → Measure ℝ := fun r => if r then ν₁ else ν₀
        refine ⟨ν, ?_, ?_⟩
        · constructor
          · intro r
            cases r <;> simp [ν, hν₀le, hν₁le]
          · intro r
            cases r <;> simp [ν, hν₀mass, hν₁mass]
        · simpa [allocationSupport, allocationIntegral, Fintype.sum_bool, ν] using
            hsum.symm
    rw [hsupportSet, csSup_add (hSne true) (hSbdd true) (hSne false) (hSbdd false)]
    have htrue := support_dual_stratum (obsMeasure M true)
      (diseaseMass M true) (f true).1 (f true).2.1 (f true).2.2
    have hfalse := support_dual_stratum (obsMeasure M false)
      (diseaseMass M false) (f false).1 (f false).2.1 (f false).2.2
    simpa [S, allocationDual, cappedDualValue, Fintype.sum_bool] using
      congrArg₂ (· + ·) htrue hfalse

end
end CausalSmith.PartialID.ImperfectrefCutoffRegret
