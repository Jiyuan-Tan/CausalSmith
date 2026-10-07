module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.LegalMixture.ChannelLaws

/-! # Target covariate and conditioning identities -/

public section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength
/-- Given [the supplied inputs](hyp:s,mass,hm), [the stated result about primitive kernel measurable of holds](goal). -/

lemma primitiveKernel_measurable_of (s : Bool)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) :
    Measurable fun x => primitiveKernel s x mass := by
  classical
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp only [primitiveKernel, Measure.finsetSum_apply]
  apply Finset.measurable_fun_sum
  intro d0 hd0
  apply Finset.measurable_fun_sum
  intro d1 hd1
  apply Finset.measurable_fun_sum
  intro y0 hy0
  apply Finset.measurable_fun_sum
  intro y1 hy1
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hA]
  exact (hm d0 d1 y0 y1).ennreal_ofReal.mul
    (measurable_one.indicator (hA.preimage (by fun_prop)))
/-- Given [the supplied inputs](hyp:s,x,mass,hm0,hsum), [the stated result about primitive kernel univ holds](goal). -/

lemma primitiveKernel_univ (s : Bool) (x : ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm0 : ∀ d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1) :
    primitiveKernel s x mass Set.univ = 1 := by
  simp only [primitiveKernel, Measure.finsetSum_apply, Measure.smul_apply,
    smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, mul_one]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun y1 _ => hm0 _ _ _ y1)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun y0 _ =>
    Finset.sum_nonneg fun y1 _ => hm0 _ _ y0 y1)]
  simp_rw [← ENNReal.ofReal_sum_of_nonneg (fun d1 _ =>
    Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hm0 _ d1 y0 y1)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun d0 _ => Finset.sum_nonneg fun d1 _ =>
    Finset.sum_nonneg fun y0 _ => Finset.sum_nonneg fun y1 _ => hm0 d0 d1 y0 y1)]
  rw [hsum]
  simp
/-- Given [the supplied inputs](hyp:s,density,mass,hdensity,hm,hm0,hsum), [the stated result about map covariate primitive population holds](goal). -/

lemma map_covariate_primitivePopulation (s : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hdensity : Measurable density)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1)
    (hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1)
    (hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1) :
    Measure.map covariate (primitivePopulation s density mass) =
      (volume.restrict covariateSpace).withDensity
        (fun x => ENNReal.ofReal (density x)) := by
  have hcov : Measurable covariate := by unfold covariate; fun_prop
  have hk := primitiveKernel_measurable_of s mass hm
  ext A hA
  rw [Measure.map_apply hcov hA]
  unfold primitivePopulation
  rw [Measure.bind_apply (hA.preimage hcov) hk.aemeasurable]
  rw [← lintegral_indicator_one hA]
  apply lintegral_congr
  intro x
  classical
  by_cases hx : x ∈ A
  · simpa [primitiveKernel, covariate, Set.indicator, hx] using
      primitiveKernel_univ s x mass (hm0 x) (hsum x)
  · simp [primitiveKernel, covariate, Set.indicator, hx]
/-- Given [the supplied inputs](hyp:s,t,density,mass,hm), [the stated result about primitive population population event holds](goal). -/

lemma primitivePopulation_population_event (s t : Bool) (density : ℝ → ℝ)
    (mass : ℝ → Bool → Bool → Bool → Bool → ℝ)
    (hm : ∀ d0 d1 y0 y1, Measurable fun x => mass x d0 d1 y0 y1) :
    primitivePopulation s density mass {o | population o = t} =
      if s = t then (primitivePopulation s density mass) Set.univ else 0 := by
  have hk := primitiveKernel_measurable_of s mass hm
  have hpop : MeasurableSet {o : FullData | population o = t} := by
    unfold population
    measurability
  unfold primitivePopulation
  rw [Measure.bind_apply hpop hk.aemeasurable,
    Measure.bind_apply MeasurableSet.univ hk.aemeasurable]
  split_ifs with hst
  · subst t
    apply lintegral_congr
    intro x
    simp [primitiveKernel, population]
  · apply lintegral_eq_zero_of_ae_eq_zero
    apply Filter.Eventually.of_forall
    intro x
    simp [primitiveKernel, population, hst]
/-- Given [the supplied inputs](hyp:source,target,hsource,htarget,htarget_univ), [the stated result about cond half supported mixture holds](goal). -/

lemma cond_half_supported_mixture (source target : Measure FullData)
    (hsource : source {o | population o = false} = 0)
    (htarget : target {o | population o = false} = 1)
    (htarget_univ : target Set.univ = 1) :
    ProbabilityTheory.cond
        ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target)
        {o | population o = false} = target := by
  let S : Set FullData := {o | population o = false}
  have hS : MeasurableSet S := by
    unfold S population
    measurability
  have hfullS : ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target) S = 1 / 2 := by
    simp [Measure.add_apply, Measure.smul_apply, hsource, htarget, S]
  have hrs : source.restrict S = 0 := Measure.restrict_eq_zero.mpr hsource
  have hrt : target.restrict S = target := by
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    change target (Sᶜ) = 0
    rw [measure_compl hS (by rw [htarget]; simp)]
    rw [htarget_univ, show target S = 1 by simpa [S] using htarget]
    simp
  unfold ProbabilityTheory.cond
  rw [hfullS]
  change (1 / 2 : ℝ≥0∞)⁻¹ •
      (((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target).restrict S) = target
  rw [Measure.restrict_add, Measure.restrict_smul, Measure.restrict_smul,
    hrs, hrt]
  simp only [smul_zero, zero_add]
  rw [← mul_smul]
  rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  exact one_smul _ _
/-- Given [the supplied inputs](hyp:cStar,n,sgn,hn,hu0), [the stated result about target density univ holds](goal). -/

lemma targetDensity_univ (cStar : ℝ) (n : ℕ)
    (sgn : Fin (lowerCells n) → Bool) (hn : 0 < n)
    (hu0 : ∀ x, 0 ≤ 1 + tiledPerturbation cStar n sgn x) :
    ((volume.restrict covariateSpace).withDensity
      (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x))) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  have hu := tiledPerturbation_integrable_and_integral_zero cStar n sgn hn
  letI : IsFiniteMeasure (volume.restrict covariateSpace) := by
    change IsFiniteMeasure (volume.restrict (Icc (0 : ℝ) 1))
    infer_instance
  have hi : Integrable (fun x => 1 + tiledPerturbation cStar n sgn x)
      (volume.restrict covariateSpace) := by
    exact (integrable_const 1).add hu.1
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall hu0)]
  rw [integral_add (integrable_const 1) hu.1, hu.2]
  simp [covariateSpace]
/-- Given [the supplied inputs](hyp:a,n,cStar,sgn,hb,hAdm,hn,hτ), [the stated result about legal target law eq density holds](goal). -/

lemma legalTargetLaw_eq_density (a : ℝ) (n : ℕ) (cStar τ : ℝ)
    (sgn : Fin (lowerCells n) → Bool)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4)
    (hAdm : LowerAdmissible n a cStar) (hτ : τ ∈ Icc (-1 : ℝ) 1)
    (hn : 0 < n) :
    (ProbabilityTheory.cond
      ((1 / 2 : ℝ≥0∞) •
          primitivePopulation true (fun _ => 1) (lowerMass a n cStar τ sgn) +
        (1 / 2 : ℝ≥0∞) •
          primitivePopulation false
            (fun x => 1 + tiledPerturbation cStar n sgn x)
            (lowerMass a n cStar τ sgn))
      {o | population o = false}).map covariate =
      (volume.restrict covariateSpace).withDensity
        (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x)) := by
  let source := primitivePopulation true (fun _ => 1) (lowerMass a n cStar τ sgn)
  let target := primitivePopulation false
    (fun x => 1 + tiledPerturbation cStar n sgn x) (lowerMass a n cStar τ sgn)
  have hm0 := lowerMass_nonneg a n cStar τ sgn hb hAdm hτ
  have hu_sq (x : ℝ) : tiledPerturbation cStar n sgn x ^ 2 ≠ 1 / 4 := by
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have hu' : |tiledPerturbation cStar n sgn x| ≤ 3 / 16 := le_trans hu hAdm.2.1
    intro heq
    have : |tiledPerturbation cStar n sgn x| = 1 / 2 := by
      nlinarith [sq_abs (tiledPerturbation cStar n sgn x),
        abs_nonneg (tiledPerturbation cStar n sgn x)]
    linarith
  have hsum (x : ℝ) := primitiveMass_sum (actualStrength a n)
    (tiledPerturbation cStar n sgn x)
    (coupledPerturbation cStar τ n sgn x) (ne_of_gt hb.1) (hu_sq x)
  have hmap : Measure.map covariate target =
      (volume.restrict covariateSpace).withDensity
        (fun x => ENNReal.ofReal (1 + tiledPerturbation cStar n sgn x)) := by
    apply map_covariate_primitivePopulation
    · exact measurable_const.add (tiledPerturbation_measurable cStar n sgn)
    · exact lowerMass_measurable a n cStar τ sgn
    · exact hm0
    · exact hsum
  have hu0 (x : ℝ) : 0 ≤ 1 + tiledPerturbation cStar n sgn x := by
    have hu := tiledPerturbation_abs_le_lowerHeight cStar n sgn x hAdm.1.le
    have hu' : |tiledPerturbation cStar n sgn x| ≤ 3 / 16 := le_trans hu hAdm.2.1
    linarith [neg_abs_le (tiledPerturbation cStar n sgn x)]
  have htuniv : target Set.univ = 1 := by
    have hmapped := congrArg (fun μ : Measure ℝ => μ Set.univ) hmap
    rw [Measure.map_apply (by unfold covariate; fun_prop) MeasurableSet.univ] at hmapped
    simpa [target] using hmapped.trans
      (targetDensity_univ cStar n sgn hn hu0)
  have hs0 : source {o | population o = false} = 0 := by
    simpa [source] using primitivePopulation_population_event true false
      (fun _ => 1) (lowerMass a n cStar τ sgn)
      (lowerMass_measurable a n cStar τ sgn)
  have ht1 : target {o | population o = false} = 1 := by
    rw [primitivePopulation_population_event false false
      (fun x => 1 + tiledPerturbation cStar n sgn x)
      (lowerMass a n cStar τ sgn)
      (lowerMass_measurable a n cStar τ sgn)]
    simpa [target] using htuniv
  rw [show ProbabilityTheory.cond
      ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target)
        {o | population o = false} = target from
      cond_half_supported_mixture source target hs0 ht1 htuniv]
  exact hmap
/-- Given [the supplied inputs](hyp:a,n,hb), [the stated result about center target law eq volume holds](goal). -/

lemma centerTargetLaw_eq_volume (a : ℝ) (n : ℕ)
    (hb : 0 < actualStrength a n ∧ actualStrength a n ≤ 1 / 4) :
    (ProbabilityTheory.cond
      ((1 / 2 : ℝ≥0∞) • primitivePopulation true (fun _ => 1)
          (fun _ => primitiveMass (actualStrength a n) 0 0) +
        (1 / 2 : ℝ≥0∞) • primitivePopulation false (fun _ => 1)
          (fun _ => primitiveMass (actualStrength a n) 0 0))
      {o | population o = false}).map covariate =
      volume.restrict covariateSpace := by
  let mass : ℝ → Bool → Bool → Bool → Bool → ℝ :=
    fun _ => primitiveMass (actualStrength a n) 0 0
  let source := primitivePopulation true (fun _ => 1) mass
  let target := primitivePopulation false (fun _ => 1) mass
  have hm0 : ∀ x d0 d1 y0 y1, 0 ≤ mass x d0 d1 y0 y1 := by
    intro x d0 d1 y0 y1
    exact primitiveMass_nonneg_of_bounds (actualStrength a n) 0 0 hb
      (by norm_num) (by norm_num) (by nlinarith [hb.1]) d0 d1 y0 y1
  have hsum : ∀ x, ∑ d0 : Bool, ∑ d1 : Bool, ∑ y0 : Bool, ∑ y1 : Bool,
      mass x d0 d1 y0 y1 = 1 := by
    intro x
    exact primitiveMass_sum (actualStrength a n) 0 0 (ne_of_gt hb.1) (by norm_num)
  have hmap : Measure.map covariate target = volume.restrict covariateSpace := by
    have h := map_covariate_primitivePopulation false (fun _ => 1) mass
      measurable_const (fun _ _ _ _ => measurable_const) hm0 hsum
    simpa [target] using h
  have htuniv : target Set.univ = 1 := by
    have hmapped := congrArg (fun μ : Measure ℝ => μ Set.univ) hmap
    rw [Measure.map_apply (by unfold covariate; fun_prop) MeasurableSet.univ] at hmapped
    simpa [covariateSpace] using hmapped
  have hs0 : source {o | population o = false} = 0 := by
    simpa [source] using primitivePopulation_population_event true false
      (fun _ => 1) mass (fun _ _ _ _ => measurable_const)
  have ht1 : target {o | population o = false} = 1 := by
    rw [primitivePopulation_population_event false false
      (fun _ => 1) mass (fun _ _ _ _ => measurable_const)]
    simpa [target] using htuniv
  rw [show ProbabilityTheory.cond
      ((1 / 2 : ℝ≥0∞) • source + (1 / 2 : ℝ≥0∞) • target)
        {o | population o = false} = target from
      cond_half_supported_mixture source target hs0 ht1 htuniv]
  exact hmap

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
