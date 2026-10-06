module
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationOutcomeEntries
public import CausalSmith.Stat.STAT_TwosamplePointcateAnnotationFrontier_Research.Helpers.PopulationOutcomeMoments

/-! # Localized causal response entries
The observed outcome moments are transported to the designated admissible
versions and substituted into the population rectangular response formula.
-/

public section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
noncomputable section
set_option linter.unusedVariables false
namespace CausalSmith.Stat.TwosamplePointcateAnnotationFrontier

/-- Localization transports both observed response moments to designated causal versions.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input f](hyp:f), [the specified input hf](hyp:hf), [the specified input B](hyp:B), [the specified input hB](hyp:hB), [the specified input hfB](hyp:hfB), [the population localized causal moments conclusion](goal) holds. -/
lemma population_localized_causal_moments {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (f : Cov d → ℝ) (hf : Measurable f) (B : ℝ) (hB : 0 ≤ B)
    (hfB : ∀ x ∈ locCube d h, ‖f x‖ ≤ B) :
    ((∫ w, locWeight h w.1 * (f w.1 * bit w.2.1 * bit w.2.2) ∂obsLaw P) =
      ∫ x, f x * designatedPropensity P hP x * designatedTreated P hP x ∂locLaw d h) ∧
    ((∫ w, locWeight h w.1 * (f w.1 * bit w.2.2) ∂obsLaw P) =
      ∫ x, f x * (designatedControl P hP x + designatedPropensity P hP x * tau P hP x)
        ∂locLaw d h) := by
  have hs := canonicalLaw_spec P hP
  have hobs : obsLaw P = obsLaw (canonicalLaw P hP) := by unfold obsLaw; rw [hs.1]
  let F := fun x => locWeight h x * f x
  have hF : Measurable F := by fun_prop
  have hFB := locWeight_mul_norm_bound h hh f B hB hfB
  have hFs : ∀ x, x ∉ cube d → F x = 0 := by
    intro x hx
    have hl : x ∉ locCube d h := fun hl => hx (locCube_subset_cube d h hh' hl)
    simp [F, locWeight, hl]
  have hB' : 0 ≤ h^(-(d:ℝ))*B := by positivity
  have ht := population_treated_outcome_moment (canonicalLaw P hP)
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2.2.2
    F hF _ hB' hFB hFs
  have hy := population_outcome_moment (canonicalLaw P hP)
    hs.2.1 hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2.2
    F hF _ hB' hFB hFs
  dsimp [F] at ht hy
  simp only [mul_assoc] at ht hy
  rw [uniformLaw_localization_integral d h hh hh'] at ht hy
  constructor
  · simp only [mul_assoc]
    rw [hobs, ht]
    unfold locLaw
    apply integral_congr_ae
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (isClosed_locCube d h).measurableSet] with x hx
    simp [designatedPropensity, designatedTreated, locCube_subset_cube d h hh' hx, mul_assoc]
  · rw [hobs, hy]
    unfold locLaw
    apply integral_congr_ae
    apply Measure.ae_smul_measure
    filter_upwards [ae_restrict_mem (isClosed_locCube d h).measurableSet] with x hx
    simp [designatedPropensity, designatedControl, designatedTreated, tau,
      locCube_subset_cube d h hh' hx]

/-- The population response vector uses the causal response mean in its projection correction.  Given [the specified input d](hyp:d), [the specified input alpha](hyp:alpha), [the specified input beta](hyp:beta), [the specified input gamma](hyp:gamma), [the specified input L](hyp:L), [the overlap level eps](hyp:eps), [the specified input P](hyp:P), [the specified input hP](hyp:hP), [the specified input n](hyp:n), [the specified input m](hyp:m), [the specified input hn](hyp:hn), [the specified input h](hyp:h), [the specified input hh](hyp:hh), [the specified input hh'](hyp:hh'), [the specified input J](hyp:J), [the specified input hJ](hyp:hJ), [the specified input u](hyp:u), [the population response causal entries conclusion](goal) holds. -/
lemma population_response_causal_entries {d : ℕ} {alpha beta gamma L eps : ℝ}
    (P : PrimitiveLaw d) (hP : PrimitiveClass alpha beta gamma L eps P)
    (n m : ℕ) (hn : 2 ≤ n) (h : ℝ) (hh : 0 < h) (hh' : h ≤ 1/2)
    (J : ℕ) (hJ : 1 ≤ J) (u : PolyIdx d) :
    rBar P n m h J u =
      (∫ x, coarseBasis h x u * designatedPropensity P hP x * designatedTreated P hP x ∂locLaw d h) -
      ∑ z : FineIdx d J,
        (∫ x, fineBasis h J x z * (designatedPropensity P hP x * coarseBasis h x u) ∂locLaw d h) *
        (∫ x, fineBasis h J x z *
          (designatedControl P hP x + designatedPropensity P hP x * tau P hP x) ∂locLaw d h) := by
  rw [population_response_observed_entries P hP n m hn h hh hh' J hJ u,
    (population_localized_causal_moments P hP h hh hh'
      (fun x => coarseBasis h x u) (by fun_prop) ((4:ℝ)^d) (by positivity)
      (by intro x hx; simpa only [Real.norm_eq_abs] using coarseBasis_abs_bound d h hh x hx u)).1]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  rw [(population_localized_causal_moments P hP h hh hh'
    (fun x => fineBasis h J x z) (by fun_prop) (Real.sqrt ((J:ℝ)^d)*(4:ℝ)^d) (by positivity)
    (by intro x hx; simpa only [Real.norm_eq_abs] using fineBasis_abs_bound d h J hh hJ x z)).2]

end CausalSmith.Stat.TwosamplePointcateAnnotationFrontier
