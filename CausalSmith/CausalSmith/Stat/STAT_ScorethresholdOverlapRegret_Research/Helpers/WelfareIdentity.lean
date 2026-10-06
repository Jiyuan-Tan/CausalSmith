module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.Estimator
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Score-threshold overlap regret — welfare and regularization

The concrete potential-outcome law uses Mathlib measures.
The abstract POSystem and strict-overlap ATE model have different scope.
Product experiments match the paper sampling model; lower-pair proofs
reuse Causalean chi-square and total variation lemmas.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped BigOperators ENNReal

lemma fullRow_X_measurable : Measurable (fun o : FullRow => o.X) := by
  have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) := comap_measurable _
  exact (by fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.1)).comp hfull

lemma logger_aemeasurable (P : RowLaw) (hwf : WellFormed P) :
    AEMeasurable P.logger P.PX := by
  have hXfull : ∀ᵐ o ∂P.full, o.X ∈ Set.Icc (0 : ℝ) 1 := ae_iff.mpr hwf.2.1
  have hXPX : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2 hXfull
  have hr : AEMeasurable P.logger (P.PX.restrict (Set.Icc (0 : ℝ) 1)) :=
    aemeasurable_restrict_of_measurable_subtype measurableSet_Icc hwf.2.2.2.1
  rwa [Measure.restrict_eq_self_of_ae_mem hXPX] at hr

/-- The tested propensity clause extends from sets to measurable treatment-arm weights. -/
lemma tested_arm_weighted (P : RowLaw) (hwf : WellFormed P)
    (hloggerSpace : ∀ x ∈ Set.Icc (0:ℝ) 1, P.logger x ∈ Set.Ioo (0:ℝ) 1)
    (a : Bool) (f : ℝ → ℝ) (hf : AEStronglyMeasurable f P.PX) :
    ∫ o, (if o.A = a then f o.X else 0) ∂P.full =
      ∫ x, (if a then P.logger x else 1-P.logger x) * f x ∂P.PX := by
  letI : IsProbabilityMeasure P.full := hwf.1
  letI : IsFiniteMeasure P.PX := ⟨by
    rw [RowLaw.PX, Measure.map_apply fullRow_X_measurable MeasurableSet.univ]
    simp⟩
  have hXfull : ∀ᵐ o ∂P.full, o.X ∈ Set.Icc (0 : ℝ) 1 := ae_iff.mpr hwf.2.1
  have hXPX : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0 : ℝ) 1 :=
    (ae_map_iff fullRow_X_measurable.aemeasurable measurableSet_Icc).2 hXfull
  have hemeas := logger_aemeasurable P hwf
  let q : ℝ → ℝ := fun x => if a then P.logger x else 1-P.logger x
  have hqmeas : AEMeasurable q P.PX := by
    dsimp [q]
    split <;> fun_prop
  have hqbounds : ∀ᵐ x ∂P.PX, 0 ≤ q x ∧ q x ≤ 1 := by
    filter_upwards [hXPX] with x hx
    have he := hloggerSpace x hx
    cases a <;> simp [q] at * <;> constructor <;> linarith
  have hqint : Integrable q P.PX := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hqmeas.aestronglyMeasurable ?_
    filter_upwards [hqbounds] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2
  letI : IsFiniteMeasure (P.PX.withDensity (fun x => ENNReal.ofReal (q x))) :=
    isFiniteMeasure_withDensity_ofReal hqint.hasFiniteIntegral
  let ν : Measure ℝ := P.PX.withDensity (fun x => ENNReal.ofReal (q x))
  let μa : Measure ℝ := Measure.map (fun o : FullRow => o.X)
    (P.full.restrict {o | o.A = a})
  have hμaν : μa = ν := by
    apply Measure.ext
    intro B hB
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change μa.real B = ν.real B
    have harm :
        ∫ o in {o : FullRow | o.X ∈ B}, (if o.A = a then (1 : ℝ) else 0) ∂P.full =
          ∫ x in B, q x ∂P.PX := by
      cases a with
      | false =>
        have ht := hwf.2.2.2.2.2.1 B hB
        have hPXreal : P.PX.real B = P.full.real {o : FullRow | o.X ∈ B} := by
          rw [measureReal_def, measureReal_def, RowLaw.PX,
            Measure.map_apply fullRow_X_measurable hB]
          rfl
        have heint : Integrable P.logger P.PX := by
          convert (integrable_const (1 : ℝ)).sub hqint using 1
          ext x
          simp [q]
        have hleft :
            ∫ o in {o : FullRow | o.X ∈ B}, (if o.A = false then (1 : ℝ) else 0) ∂P.full =
              ∫ o in {o : FullRow | o.X ∈ B}, 1 - (if o.A then (1 : ℝ) else 0) ∂P.full := by
          apply integral_congr_ae
          filter_upwards with o
          cases o.A <;> simp
        rw [hleft, integral_sub]
        · rw [setIntegral_one_eq_measureReal, ht]
          dsimp [q]
          rw [integral_sub]
          · rw [setIntegral_one_eq_measureReal, hPXreal]
          · exact integrableOn_const
          · exact heint.integrableOn
        · exact integrableOn_const
        · exact (Integrable.mono' (integrable_const (1 : ℝ)) (by
            have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
              comap_measurable _
            have hAm : Measurable (fun o : FullRow => o.A) := (by
              fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp hfull
            exact (Measurable.ite (hAm (measurableSet_singleton true))
              (measurable_const : Measurable (fun _ : FullRow => (1 : ℝ)))
              measurable_const).aestronglyMeasurable) (by
            filter_upwards with o
            cases o.A <;> simp)).integrableOn
      | true => simpa [q] using hwf.2.2.2.2.2.1 B hB
    simp only [measureReal_def, μa]
    rw [Measure.map_apply fullRow_X_measurable hB,
      Measure.restrict_apply (fullRow_X_measurable hB)]
    simp only [ν]
    rw [withDensity_apply _ hB]
    rw [← integral_toReal hqmeas.ennreal_ofReal.restrict
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    have htoReal :
        ∫ x in B, (ENNReal.ofReal (q x)).toReal ∂P.PX = ∫ x in B, q x ∂P.PX := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hqbounds] with x hx
      exact ENNReal.toReal_ofReal hx.1
    rw [htoReal]
    have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
      comap_measurable _
    have hAm : Measurable (fun o : FullRow => o.A) := (by
      fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp hfull
    have hAset : MeasurableSet {o : FullRow | o.A = a} := hAm (measurableSet_singleton a)
    have hlhs :
        ∫ o in {o : FullRow | o.X ∈ B}, (if o.A = a then (1 : ℝ) else 0) ∂P.full =
          P.full.real ((fun o : FullRow => o.X) ⁻¹' B ∩ {o | o.A = a}) := by
      change (∫ o in (fun o : FullRow => o.X) ⁻¹' B,
        (if o.A = a then (1 : ℝ) else 0) ∂P.full) = _
      rw [← integral_indicator (fullRow_X_measurable hB),
        ← integral_indicator_one ((fullRow_X_measurable hB).inter hAset)]
      apply integral_congr_ae
      filter_upwards with o
      by_cases hoX : o.X ∈ B <;> by_cases hoA : o.A = a <;> simp [hoX, hoA]
    rw [← measureReal_def, ← hlhs]
    exact harm
  have hfull : Measurable (fun o : FullRow => (o.X,o.A,o.Y,o.Y0,o.Y1)) :=
    comap_measurable _
  have hAm : Measurable (fun o : FullRow => o.A) := (by
    fun_prop : Measurable (fun t : ℝ × Bool × ℝ × ℝ × ℝ => t.2.1)).comp hfull
  have hAset : MeasurableSet {o : FullRow | o.A = a} := hAm (measurableSet_singleton a)
  have hfν : AEStronglyMeasurable f ν :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  have hfμa : AEStronglyMeasurable f μa := by rw [hμaν]; exact hfν
  have hmap : ∫ x, f x ∂μa = ∫ o, f o.X ∂P.full.restrict {o | o.A = a} :=
    integral_map fullRow_X_measurable.aemeasurable hfμa
  calc
    ∫ o, (if o.A = a then f o.X else 0) ∂P.full =
        ∫ o in {o | o.A = a}, f o.X ∂P.full := by
          rw [← integral_indicator hAset]
          apply integral_congr_ae
          filter_upwards with o
          by_cases ho : o.A = a <;> simp [Set.indicator, ho]
    _ = ∫ x, f x ∂μa := hmap.symm
    _ = ∫ x, f x ∂ν := by rw [hμaν]
    _ = ∫ x, (ENNReal.ofReal (q x)).toReal • f x ∂P.PX := by
      exact integral_withDensity_eq_integral_toReal_smul₀ hqmeas.ennreal_ofReal
        (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f
    _ = ∫ x, q x * f x ∂P.PX := by
      apply integral_congr_ae
      filter_upwards [hqbounds] with x hx
      simp [ENNReal.toReal_ofReal hx.1]
    _ = ∫ x, (if a then P.logger x else 1-P.logger x) * f x ∂P.PX := rfl

-- @node: lem:welfare-identity
/-- Regret is the effect-weighted disagreement integral for measurable binary policies. -/
lemma regret_eq_effect_disagreement (α γ θ : ℝ) (n : ℕ)
    (P : RowLaw) (e : ℝ → ℝ) (hClass : LawClass α γ θ n P e)
    (φ : ℝ → Bool) (hφ : φ ∈ binaryPolicyClass) :
    regret (P.toWellFormedLaw hClass.wf hClass.bounded) ⟨φ, hφ⟩ =
      ∫ x, effectMagnitude P x *
      (if φ x = canonicalPolicy P x then (0:ℝ) else 1) ∂P.PX := by
  have hbounded : BoundedPotentials P := hClass.bounded
  have hcanonical : CanonicalThreshold P := hClass.canonical
  have : IsProbabilityMeasure P.PX := hClass.score.1
  have hsupport : ∀ᵐ x ∂P.PX, x ∈ Set.Icc (0:ℝ) 1 :=
    ae_iff.mpr hClass.score.2
  have ht : AEMeasurable P.tau P.PX := by
    have hr := aemeasurable_restrict_of_measurable_subtype (μ := P.PX)
      measurableSet_Icc hClass.wf.2.2.2.2.1
    rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at hr
  have hIntStar : Integrable
      (fun x => (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x) P.PX := by
    have hm : AEStronglyMeasurable
        (fun x => (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x) P.PX := by
      have hi : AEMeasurable (fun x => max (P.tau x) 0) P.PX := by fun_prop
      convert hi.aestronglyMeasurable using 1
      ext x
      by_cases h : 0 ≤ P.tau x
      · simp [canonicalPolicy, h]
      · simp [canonicalPolicy, h, max_eq_right (le_of_not_ge h)]
    refine Integrable.mono' (integrable_const (2:ℝ)) hm ?_
    filter_upwards [hClass.effectBound] with x hx
    cases canonicalPolicy P x <;> simp_all
  have hIntPhi : Integrable
      (fun x => (if φ x then (1:ℝ) else 0) * P.tau x) P.PX := by
    have hi : Measurable (fun x : Set.Icc (0:ℝ) 1 => if φ x then (1:ℝ) else 0) := by
      have hp : Measurable (fun x : Set.Icc (0:ℝ) 1 => φ x) := hφ
      exact Measurable.ite (hp (measurableSet_singleton true))
        measurable_const measurable_const
    have hm : AEMeasurable (fun x => if φ x then (1:ℝ) else 0) P.PX := by
      have hr := aemeasurable_restrict_of_measurable_subtype
        (f := fun x => if φ x then (1:ℝ) else 0) (μ := P.PX)
        measurableSet_Icc hi
      rwa [Measure.restrict_eq_self_of_ae_mem hsupport] at hr
    refine Integrable.mono' (integrable_const (2:ℝ))
      (hm.mul ht).aestronglyMeasurable ?_
    filter_upwards [hClass.effectBound] with x hx
    cases φ x <;> simp_all
  have hpoint (x : ℝ) :
      ((if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x) -
        ((if φ x then (1:ℝ) else 0) * P.tau x) =
      effectMagnitude P x * (if φ x = canonicalPolicy P x then (0:ℝ) else 1) := by
    by_cases ht : 0 ≤ P.tau x
    · cases φ x <;> simp [canonicalPolicy, effectMagnitude, ht, abs_of_nonneg ht]
    · have hneg : P.tau x < 0 := lt_of_not_ge ht
      cases φ x <;> simp [canonicalPolicy, effectMagnitude, ht, abs_of_neg hneg]
  change (∫ x, (if canonicalPolicy P x then (1:ℝ) else 0) * P.tau x ∂P.PX) -
      (∫ x, (if φ x then (1:ℝ) else 0) * P.tau x ∂P.PX) = _
  rw [← integral_sub hIntStar hIntPhi]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)


end CausalSmith.Stat.ScorethresholdOverlapRegret
