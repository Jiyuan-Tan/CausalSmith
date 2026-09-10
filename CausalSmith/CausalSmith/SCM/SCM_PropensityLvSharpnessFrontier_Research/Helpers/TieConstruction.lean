import CausalSmith.SCM.SCM_PropensityLvSharpnessFrontier_Research.Helpers.ProductPerturbation

/-! # Explicit two-point alternatives at CDF contacts -/

namespace CausalSmith.SCM.PropensityLvSharpnessFrontier

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

/-- Given [strictly positive propensity and a shrinking local perturbation](hyp:hPos,hdelta,hrate), [there exists a tie-contact observational scenario](goal). -/
lemma exists_tieContactScenario (e : ℝ) (hPos : StrictPositivity e)
    (atOne a : Bool) (y₀ : ℝ)
    (delta : ℕ → ℝ) (hdelta : ∀ n, 0 < delta n)
    (hrate : Tendsto (fun n : ℕ => (n : ℝ) * delta n) atTop (nhds 0)) :
    ∃ (P₀ : Measure ℝ) (Pn : ℕ → Measure ℝ)
      (nu₀ : Measure (Bool × ℝ)) (nun : ℕ → Measure (Bool × ℝ)),
      TieContactScenario atOne a e y₀ P₀ Pn delta nu₀ nun := by
  let p : ℕ → ℝ := fun n => min (delta n) (1 / 2)
  have hp (n : ℕ) : p n ∈ Set.Icc 0 1 := by
    dsimp [p]
    exact ⟨le_of_lt (lt_min (hdelta n) (by norm_num)),
      (min_le_right _ _).trans (by norm_num)⟩
  have hprate : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
    · filter_upwards [] with n
      exact mul_nonneg (Nat.cast_nonneg _) (hp n).1
    · filter_upwards [] with n
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)
  have hd0 : Tendsto delta atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hrate
    · filter_upwards [] with n
      exact (hdelta n).le
    · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
      have hnreal : 1 ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [hdelta n]
  have hp_eq : ∀ᶠ n in atTop, p n = delta n := by
    have hev : ∀ᶠ n in atTop, delta n < 1 / 2 :=
      (tendsto_order.1 hd0).2 (1 / 2) (by norm_num)
    filter_upwards [hev] with n hn
    exact min_eq_left (le_of_lt hn)
  let z₀ : ℝ := if atOne then y₀ else y₀ + 1
  let z₁ : ℝ := if atOne then y₀ + 1 else y₀
  let P₀ : Measure ℝ := Measure.dirac z₀
  let P₁ : Measure ℝ := Measure.dirac z₁
  let Pn : ℕ → Measure ℝ := fun n =>
    ENNReal.ofReal (1 - p n) • P₀ + ENNReal.ofReal (p n) • P₁
  have hP0 : IsProbabilityMeasure P₀ := inferInstance
  have hP1 : IsProbabilityMeasure P₁ := inferInstance
  letI : IsProbabilityMeasure P₀ := hP0
  letI : IsProbabilityMeasure P₁ := hP1
  have hPn (n : ℕ) : IsProbabilityMeasure (Pn n) := by
    rw [isProbabilityMeasure_iff]
    simp only [Pn, Measure.add_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr (hp n).2) (hp n).1]
    simp
  let nu₀ := canonicalObservedMeasure a e P₀
  let nun : ℕ → Measure (Bool × ℝ) := fun n => canonicalObservedMeasure a e (Pn n)
  refine ⟨P₀, Pn, nu₀, nun, ?_⟩
  have bow (P : Measure ℝ) [IsProbabilityMeasure P] :
      BowObservedLawAt a e P (canonicalObservedMeasure a e P) := by
    let w := canonicalBowWitness a e P P hPos.1.le hPos.2.le
    refine ⟨inferInstance, canonicalObservedMeasure_isProbabilityMeasure a e P
      hPos.1.le hPos.2.le, w, ?_, ?_, ?_, ?_, ?_⟩
    · exact w.probability
    · exact canonicalBowWitness_consistency a e P P hPos.1.le hPos.2.le
    · exact canonicalBowWitness_propensity a e P P hPos.1.le hPos.2.le
    · exact canonicalBowWitness_armLaw a e P P hPos.1 hPos.2.le
    · exact observedLaw_canonicalBowWitness_self a e P hPos.1.le hPos.2.le
  refine ⟨bow P₀, ?_, ?_, ?_, hdelta, hrate, ?_⟩
  · filter_upwards [] with n
    letI : IsProbabilityMeasure (Pn n) := hPn n
    exact bow (Pn n)
  · cases atOne <;>
      simp [P₀, z₀, ProbabilityTheory.cdf_eq_real, Measure.real,
        Measure.dirac_apply' _ measurableSet_Iic]
  · filter_upwards [hp_eq] with n hn
    letI : IsProbabilityMeasure (Pn n) := hPn n
    rw [ProbabilityTheory.cdf_eq_real]
    have hdnonneg : 0 ≤ delta n := (hdelta n).le
    cases atOne <;>
      simp [Pn, P₀, P₁, z₀, z₁, Measure.real, hn, hdnonneg,
        (show delta n ≤ 1 by rw [← hn]; exact hp n |>.2)]
  · simpa [nu₀, nun, Pn] using
      productTVLocal_of_canonical_mixture a e P₀ P₁ p hp hPos.1.le hPos.2.le hprate

/-- [The independent observational sample](goal) has the stated product-law sampling representation. -/
lemma iidObservationalSampling_iidProductLaw (n : ℕ)
    (nu : Measure (Bool × ℝ)) [IsProbabilityMeasure nu] :
    IidObservationalSampling n (sampleCoordinate n) (iidProductLaw n nu) nu := by
  letI : ∀ _ : Fin n, IsProbabilityMeasure nu := fun _ => inferInstance
  letI hprod : IsProbabilityMeasure (iidProductLaw n nu) := by
    exact Measure.pi.instIsProbabilityMeasure _
  unfold IidObservationalSampling
  refine ⟨hprod, inferInstance, ?_, ?_, ?_⟩
  · intro i
    rw [show sampleCoordinate n (i : ℕ) = fun S => S i by
      funext S
      simp [sampleCoordinate, i.isLt]]
    fun_prop
  · rw [iIndepFun_iff_map_fun_eq_pi_map]
    · rw [show (fun (S : ObservedSample n) (i : Fin n) =>
          sampleCoordinate n (i : ℕ) S) = id by
        funext S i
        simp [sampleCoordinate, i.isLt]]
      simp only [Measure.map_id]
      have hm : ∀ i : Fin n,
          Measure.map (sampleCoordinate n (i : ℕ)) (iidProductLaw n nu) = nu := by
        intro i
        rw [show sampleCoordinate n (i : ℕ) = fun S => S i by
          funext S
          simp [sampleCoordinate, i.isLt]]
        exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq
      simp_rw [hm]
      rfl
    · intro i
      rw [show sampleCoordinate n (i : ℕ) = fun S => S i by
        funext S
        simp [sampleCoordinate, i.isLt]]
      exact (measurable_pi_apply i).aemeasurable
  · intro i
    rw [show sampleCoordinate n (i : ℕ) = fun S => S i by
      funext S
      simp [sampleCoordinate, i.isLt]]
    exact (measurePreserving_eval (fun _ : Fin n => nu) i).map_eq

end CausalSmith.SCM.PropensityLvSharpnessFrontier
