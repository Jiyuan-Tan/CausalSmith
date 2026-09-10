import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.Statements
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.TieConstruction
import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.TFiniteSampleSimultaneousBand

/-! # Tie-inclusive rectangular-band impossibility -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory Set Filter
open scoped Topology

/-- Uniform tie-inclusive coverage forces nonshrinking endpoint projections at
CDF contacts; every rectangular directional handle inherits the obstruction.  For the specified model objects, [the stated conditions](hyp:hPos,hAlpha,hRect,hBandMeas,hCoverage), [the stated mathematical relationship holds](goal).
-/
-- @node: thm:tie-inclusive-band-impossibility
theorem tie_inclusive_band_impossibility
    (e alpha : ℝ) (hPos : StrictPositivity e) (hAlpha : alpha ∈ Set.Ioo 0 (1 / 2))
    (band : FiniteSampleBand)
    (hRect : DirectionalHandle band)
    (hBandMeas : ∀ n y z, MeasurableSet {S | z ∈ band n S y})
    (localClass : Set (Measure (Bool × ℝ) × Measure ℝ))
    (hCoverage : UniformAsymptoticLocalCoverage alpha e hPos band localClass) :
    (∀ (atOne : Bool) (a : Bool) (y₀ : ℝ) (P₀ : Measure ℝ)
      (Pn : ℕ → Measure ℝ) (delta : ℕ → ℝ)
      (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)),
      TieContactScenario atOne a e y₀ P₀ Pn delta nu₀ nun →
      (nu₀, P₀) ∈ localClass → (∀ᶠ n in atTop, (nun n, Pn n) ∈ localClass) →
      (∀ n, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n nu₀) nu₀) →
      (∀ᶠ n in atTop, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n (nun n)) (nun n)) →
      AsymptoticAtLeast (1 - 2 * alpha)
        (fun n => ProjectionDiameterProbability atOne nu₀ band n y₀ (1 - e))) ∧
    (∀ (atOne : Bool) (a : Bool) (y₀ : ℝ) (delta : ℕ → ℝ),
      (∀ n, 0 < delta n) →
      Tendsto (fun n : ℕ => (n : ℝ) * delta n) atTop (nhds 0) →
      ∃ (P₀ : Measure ℝ) (Pn : ℕ → Measure ℝ)
        (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)),
        TieContactScenario atOne a e y₀ P₀ Pn delta nu₀ nun ∧
        (∀ n, IidObservationalSampling n (sampleCoordinate n)
          (iidProductLaw n nu₀) nu₀) ∧
        (∀ᶠ n in atTop, IidObservationalSampling n (sampleCoordinate n)
          (iidProductLaw n (nun n)) (nun n))) ∧
    (∀ (atOne : Bool) (a : Bool) (y₀ : ℝ) (P₀ : Measure ℝ)
      (Pn : ℕ → Measure ℝ) (delta : ℕ → ℝ)
      (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)),
      TieContactScenario atOne a e y₀ P₀ Pn delta nu₀ nun →
      (nu₀, P₀) ∈ localClass →
      (∀ᶠ n in atTop, (nun n, Pn n) ∈ localClass) →
      ¬ UniformlyShrinkingAtContacts band localClass) ∧
    HonestBandFallback := by
  have hfirst : ∀ (atOne : Bool) (a : Bool) (y₀ : ℝ) (P₀ : Measure ℝ)
      (Pn : ℕ → Measure ℝ) (delta : ℕ → ℝ)
      (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)),
      TieContactScenario atOne a e y₀ P₀ Pn delta nu₀ nun →
      (nu₀, P₀) ∈ localClass → (∀ᶠ n in atTop, (nun n, Pn n) ∈ localClass) →
      (∀ n, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n nu₀) nu₀) →
      (∀ᶠ n in atTop, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n (nun n)) (nun n)) →
      AsymptoticAtLeast (1 - 2 * alpha)
        (fun n => ProjectionDiameterProbability atOne nu₀ band n y₀ (1 - e)) := by
    intro atOne a y₀ P₀ Pn delta nu₀ nun hscenario hmem hmemn _hiid0 _hiidn
    rcases hscenario with ⟨hbow0, hbown, hcdf0, hcdfn, hdelta, hrate, htv⟩
    obtain ⟨rho, hrho, hcov⟩ := hCoverage
    let tv : ℕ → ℝ := fun n => sSup {d : ℝ | ∃ C : Set (ObservedSample n),
      d = |(iidProductLaw n (nun n) C).toReal -
        (iidProductLaw n nu₀ C).toReal|}
    have htv0 : Tendsto tv atTop (nhds 0) := htv
    have hdelta0 : Tendsto delta atTop (nhds 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
      · filter_upwards [] with n
        exact (hdelta n).le
      · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
        have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith [hdelta n]
    have hdlt : ∀ᶠ n in atTop, delta n < 1 :=
      (tendsto_order.1 hdelta0).2 1 zero_lt_one
    have coverage_lower (n : ℕ) (nu : Measure (Bool × ℝ)) (P : Measure ℝ)
        [IsProbabilityMeasure nu] [IsProbabilityMeasure P]
        (hclass : (nu, P) ∈ localClass)
        (hn : 1 - alpha - rho n ≤ sInf {r : ℝ | ∃ nu' P',
          ∃ _hnu : IsProbabilityMeasure nu', ∃ hP : IsProbabilityMeasure P',
          (nu', P') ∈ localClass ∧
          r = (iidProductLaw n nu' {S | ∀ y : ℝ,
            cdfEndpoints (endpointPropensity e (Or.inl hPos))
              (@cdfProbability P' hP y) ∈ band n S y}).toReal}) :
        1 - alpha - rho n ≤
          (iidProductLaw n nu {S | ∀ y : ℝ,
            cdfEndpoints (endpointPropensity e (Or.inl hPos))
              (cdfProbability P y) ∈ band n S y}).toReal := by
      apply hn.trans
      apply csInf_le
      · refine ⟨0, ?_⟩
        intro r hr
        obtain ⟨nu', P', hnu', hP', _, rfl⟩ := hr
        exact ENNReal.toReal_nonneg
      · exact ⟨nu, P, inferInstance, inferInstance, hclass, rfl⟩
    let r : ℕ → ℝ := fun n => 2 * rho n + tv n
    refine ⟨r, ?_, ?_⟩
    · simpa [r] using (hrho.const_mul 2).add htv0
    · filter_upwards [hcov, hbown, hmemn, hcdfn, hdlt] with n hcovn hbownn hmemnn hcdfnn hdltn
      letI : IsProbabilityMeasure nu₀ := hbow0.2.1
      letI : IsProbabilityMeasure P₀ := hbow0.1
      letI : IsProbabilityMeasure (nun n) := hbownn.2.1
      letI : IsProbabilityMeasure (Pn n) := hbownn.1
      letI : ∀ _ : Fin n, IsProbabilityMeasure nu₀ := fun _ => inferInstance
      letI : ∀ _ : Fin n, IsProbabilityMeasure (nun n) := fun _ => inferInstance
      letI : IsProbabilityMeasure (iidProductLaw n nu₀) :=
        Measure.pi.instIsProbabilityMeasure _
      letI : IsProbabilityMeasure (iidProductLaw n (nun n)) :=
        Measure.pi.instIsProbabilityMeasure _
      let z0 := cdfEndpoints (endpointPropensity e (Or.inl hPos))
        (cdfProbability P₀ y₀)
      let z1 := cdfEndpoints (endpointPropensity e (Or.inl hPos))
        (cdfProbability (Pn n) y₀)
      let A : Set (ObservedSample n) := {S | z0 ∈ band n S y₀}
      let B : Set (ObservedSample n) := {S | z1 ∈ band n S y₀}
      have hAmeas : MeasurableSet A := hBandMeas n y₀ z0
      have hBmeas : MeasurableSet B := hBandMeas n y₀ z1
      have hcov0 : 1 - alpha - rho n ≤ (iidProductLaw n nu₀ A).toReal := by
        apply (coverage_lower n nu₀ P₀ hmem hcovn).trans
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply measure_mono
        intro S hS
        exact hS y₀
      have hcov1 : 1 - alpha - rho n ≤ (iidProductLaw n (nun n) B).toReal := by
        apply (coverage_lower n (nun n) (Pn n) hmemnn hcovn).trans
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply measure_mono
        intro S hS
        exact hS y₀
      have htvB : |(iidProductLaw n (nun n) B).toReal -
          (iidProductLaw n nu₀ B).toReal| ≤ tv n := by
        apply le_csSup
        · refine ⟨1, ?_⟩
          intro d hd
          obtain ⟨C, rfl⟩ := hd
          have hx : (iidProductLaw n (nun n) C).toReal ≤ 1 :=
            ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
          have hy : (iidProductLaw n nu₀ C).toReal ≤ 1 :=
            ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
          have hx0 : 0 ≤ (iidProductLaw n (nun n) C).toReal := ENNReal.toReal_nonneg
          have hy0 : 0 ≤ (iidProductLaw n nu₀ C).toReal := ENNReal.toReal_nonneg
          rw [abs_le]
          constructor <;> linarith
        · exact ⟨B, rfl⟩
      have hcovB0 : 1 - alpha - rho n - tv n ≤
          (iidProductLaw n nu₀ B).toReal := by
        rw [abs_le] at htvB
        linarith
      have hinter : 1 - 2 * alpha - (2 * rho n + tv n) ≤
          (iidProductLaw n nu₀ (A ∩ B)).toReal := by
        have hunion := measureReal_union_add_inter (μ := iidProductLaw n nu₀) (s := A) (t := B)
          hBmeas (measure_ne_top _ _) (measure_ne_top _ _)
        change (iidProductLaw n nu₀ (A ∪ B)).toReal +
            (iidProductLaw n nu₀ (A ∩ B)).toReal =
            (iidProductLaw n nu₀ A).toReal +
            (iidProductLaw n nu₀ B).toReal at hunion
        have hunionle : (iidProductLaw n nu₀ (A ∪ B)).toReal ≤ 1 :=
          ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one
        linarith
      apply hinter.trans
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono
      intro S hS
      rcases hS with ⟨hSz0, hSz1⟩
      refine ⟨z0, z1, hSz0, hSz1, ?_⟩
      change (cdfProbability P₀ y₀ : ℝ) = (if atOne then 1 else 0) at hcdf0
      change (cdfProbability (Pn n) y₀ : ℝ) =
        (if atOne then 1 - delta n else delta n) at hcdfnn
      have hdne : delta n ≠ 0 := ne_of_gt (hdelta n)
      have honene : 1 - delta n ≠ 0 := ne_of_gt (sub_pos.mpr hdltn)
      cases atOne
      · simp only [Bool.false_eq_true, ↓reduceIte] at hcdf0 hcdfnn
        simp [z0, z1, hcdf0, hcdfnn, cdfEndpoints, endpointPropensity,
          hdne, honene, hdelta n, hdltn]
        rw [abs_of_nonpos]
        · nlinarith [hPos.1, hPos.2, hdelta n]
        · nlinarith [hPos.1, hPos.2, hdelta n]
      · simp only [↓reduceIte] at hcdf0 hcdfnn
        simp [z0, z1, hcdf0, hcdfnn, cdfEndpoints, endpointPropensity,
          hdne, honene, hdelta n, hdltn]
        rw [abs_of_nonneg]
        · nlinarith [hPos.1, hPos.2, hdelta n]
        · nlinarith [hPos.1, hPos.2, hdelta n]
  refine ⟨hfirst, ?_, ?_, ?_⟩
  · intro atOne a y₀ delta hdelta hrate
    obtain ⟨P₀, Pn, nu₀, nun, hscenario⟩ :=
      exists_tieContactScenario e hPos atOne a y₀ delta hdelta hrate
    refine ⟨P₀, Pn, nu₀, nun, hscenario, ?_, ?_⟩
    · intro n
      letI : IsProbabilityMeasure nu₀ := hscenario.1.2.1
      exact iidObservationalSampling_iidProductLaw n nu₀
    · filter_upwards [hscenario.2.1] with n hn
      letI : IsProbabilityMeasure (nun n) := hn.2.1
      exact iidObservationalSampling_iidProductLaw n (nun n)
  · intro atOne a y₀ P₀ Pn delta nu₀ nun hscenario hmem hmemn hshrink
    have hlower := hfirst atOne a y₀ P₀ Pn delta nu₀ nun hscenario hmem hmemn
    have hiid0 : ∀ n, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n nu₀) nu₀ := by
      intro n
      letI : IsProbabilityMeasure nu₀ := hscenario.1.2.1
      exact iidObservationalSampling_iidProductLaw n nu₀
    have hiidn : ∀ᶠ n in atTop, IidObservationalSampling n (sampleCoordinate n)
        (iidProductLaw n (nun n)) (nun n) := by
      filter_upwards [hscenario.2.1] with n hn
      letI : IsProbabilityMeasure (nun n) := hn.2.1
      exact iidObservationalSampling_iidProductLaw n (nun n)
    obtain ⟨r, hr0, hr⟩ := hlower hiid0 hiidn
    have hnu0 : IsProbabilityMeasure nu₀ := hscenario.1.2.1
    have hP0 : IsProbabilityMeasure P₀ := hscenario.1.1
    have hdiam0 := hshrink nu₀ P₀ hmem hnu0 hP0 y₀ atOne hscenario.2.2.1
      (1 - e) (sub_pos.mpr hPos.2)
    have hsum0 : Tendsto (fun n =>
        ProjectionDiameterProbability atOne nu₀ band n y₀ (1 - e) + r n)
        atTop (nhds 0) := by simpa using hdiam0.add hr0
    have hev : ∀ᶠ n in atTop, 1 - 2 * alpha ≤
        ProjectionDiameterProbability atOne nu₀ band n y₀ (1 - e) + r n := by
      filter_upwards [hr] with n hn
      linarith
    have htpos : 0 < 1 - 2 * alpha := by linarith [hAlpha.2]
    have hevsmall : ∀ᶠ n in atTop,
        ProjectionDiameterProbability atOne nu₀ band n y₀ (1 - e) + r n <
          1 - 2 * alpha := (tendsto_order.1 hsum0).2 _ htpos
    obtain ⟨n, hn, hn'⟩ := (hev.and hevsmall).exists
    exact (not_lt_of_ge hn) hn'
  · constructor
    · intro n a alpha S y
      simp only [honestFiniteSampleBand, honestBand]
      have hsamp : (fun i : Fin n => sampleCoordinate n (i : ℕ) S) = S := by
        funext i
        simp [sampleCoordinate, i.isLt]
      rw [hsamp]
      by_cases h : armCount S a = 0
      · rw [if_pos h]
        exact ⟨0, 1, 0, 1, rfl⟩
      · rw [if_neg h]
        exact ⟨_, _, _, _, rfl⟩
    · intro hHoeffding hDkw n a alpha e nu P hP hPos hIID hFactor hAlpha
      letI : IsProbabilityMeasure P := hP
      letI : IsProbabilityMeasure (iidProductLaw n nu) := hIID.1
      simpa [honestFiniteSampleBand] using
        honestBand_simultaneous_coverage (iidProductLaw n nu) n a alpha e nu P
          (sampleCoordinate n) hIID hFactor hHoeffding hDkw hPos hAlpha

end CausalSmith.SCM.PropensityLvSharpnessFrontier
