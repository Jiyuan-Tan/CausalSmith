module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.MarkedIdentification

/-! Identification of latent measures, continuous potential means, and the causal target. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- Observational equivalence identifies both latent measures, every continuous mean value, and the causal target via local-mass limits. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa,hsigma,hP,hP',hobs). -/
-- @node: prop:identification
theorem identification (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P P' : ProbabilityMeasure (StructSpace S))
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma (P : Measure (StructSpace S)))
    (hP' : NoisyDoseModelClass E K beta kappa sigma (P' : Measure (StructSpace S)))
    (hobs : obsLaw sigma (P : Measure (StructSpace S)) = obsLaw sigma (P' : Measure (StructSpace S))) :
    (∀ x, strataProb (P : Measure (StructSpace S)) x = strataProb (P' : Measure (StructSpace S)) x ∧
      latentDoseLaw (P : Measure (StructSpace S)) x = latentDoseLaw (P' : Measure (StructSpace S)) x ∧
      latentMeanMeasure E (P : Measure (StructSpace S)) x = latentMeanMeasure E (P' : Measure (StructSpace S)) x ∧
      (∀ a ∈ Icc (0 : ℝ) 1, condPotMean E (P : Measure (StructSpace S)) x a = condPotMean E (P' : Measure (StructSpace S)) x a) ∧
      (∀ j : ℕ, 0 < (latentDoseLaw (P : Measure (StructSpace S)) x).real (Ioo (-1 / ((j : ℝ)+3)) (1 / ((j : ℝ)+3)))) ∧
      Tendsto (latentLocalRatio E (P : Measure (StructSpace S)) x) atTop
        (𝓝 (condPotMean E (P : Measure (StructSpace S)) x a0))) ∧
    causalTarget E (P : Measure (StructSpace S)) =
      ∑ x : Bool, strataProb (P : Measure (StructSpace S)) x * condPotMean E (P : Measure (StructSpace S)) x a0 ∧
    causalTarget E (P : Measure (StructSpace S)) = causalTarget E (P' : Measure (StructSpace S)) := by
  -- Equations (5)--(7): deconvolution recovers both latent measures.
  have hlatent : ∀ x : Bool,
      latentDoseLaw (P : Measure (StructSpace S)) x =
        latentDoseLaw (P' : Measure (StructSpace S)) x ∧
      latentMeanMeasure E (P : Measure (StructSpace S)) x =
        latentMeanMeasure E (P' : Measure (StructSpace S)) x := by
    intro x
    refine ⟨latentDoseLaw_eq_of_obsLaw_eq sigma kappa hsigma _ _
      hP.strataPos hP'.strataPos hP.weakDesign hP'.weakDesign
      hP.errorIndependence hP'.errorIndependence hP.gaussianChannel hP'.gaussianChannel hobs x, ?_⟩
    exact latentMeanMeasure_eq_of_obsLaw_eq E beta kappa sigma hbeta hkappa hsigma
      _ _ hP hP' hobs x
  have hbetaPos : 0 < beta := hbeta.1
  have hmass (x : Bool) (j : ℕ) :
      0 < (latentDoseLaw (P : Measure (StructSpace S)) x).real
        (Ioo (-1 / ((j : ℝ)+3)) (1 / ((j : ℝ)+3))) := by
    have heps : 0 < 1 / ((j : ℝ)+3) := by positivity
    have hhalf : 1 / ((j : ℝ)+3) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity : 0 < (j : ℝ)+3)).mpr
      have := Nat.cast_nonneg (α := ℝ) j
      linarith
    simpa only [neg_div] using latentDoseLaw_local_mass_pos
      (P : Measure (StructSpace S)) kappa hP.strataPos hP.weakDesign x
      (1 / ((j : ℝ)+3)) heps hhalf
  have hlimit (x : Bool) := latentLocalRatio_tendsto E (P : Measure (StructSpace S))
    beta kappa hbetaPos hP.strataPos hP.weakDesign hP.holderMean hP.meanRange x
  have hp (x : Bool) := strataProb_eq_of_obsLaw_eq sigma
    (P : Measure (StructSpace S)) (P' : Measure (StructSpace S)) hobs x
  have hm (x : Bool) : EqOn (condPotMean E (P : Measure (StructSpace S)) x)
      (condPotMean E (P' : Measure (StructSpace S)) x) (Icc (0 : ℝ) 1) :=
    condPotMean_eqOn_of_latent_measures_eq E _ _ beta kappa hbetaPos
      hP.strataPos hP'.strataPos hP.weakDesign hP'.weakDesign
      hP.holderMean hP'.holderMean hP.meanRange hP'.meanRange x
      (hlatent x).1 (hlatent x).2
  have ht := causalTarget_eq_stratum_sum E (P : Measure (StructSpace S))
    hP.strataPos hP.boundedPO
  refine ⟨?_, ht, ?_⟩
  · intro x
    exact ⟨hp x, (hlatent x).1, (hlatent x).2, hm x,
      hmass x, hlimit x⟩
  · rw [ht, causalTarget_eq_stratum_sum E (P' : Measure (StructSpace S))
      hP'.strataPos hP'.boundedPO]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hp x, hm x (by norm_num [a0])]

end CausalSmith.Stat.NoisydoseWeakdesignTransition
