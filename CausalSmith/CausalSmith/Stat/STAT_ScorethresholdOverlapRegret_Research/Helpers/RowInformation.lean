module
public import CausalSmith.Stat.STAT_ScorethresholdOverlapRegret_Research.Helpers.RowLikelihood

/-! # Observable-row information

The observable sign-change density identifies absolute continuity and the real
Radon–Nikodym derivative. Integrating its squared deviation gives the rare-block
chi-square formula and the regularity needed for product tensorization.
-/

public section

namespace CausalSmith.Stat.ScorethresholdOverlapRegret

open MeasureTheory
open scoped ENNReal

attribute [local instance] Classical.propDecidable

/-- Either sign's observable block experiment is a probability measure. -/
-- @node: blockPair_obsLaw_probability
lemma blockPair_obsLaw_probability (m q h : ℝ) (σ : Bool) :
    IsProbabilityMeasure (blockPair m q h σ).obsLaw := by
  haveI := uniformRandomizer_probability
  haveI : IsProbabilityMeasure fourUniform := by unfold fourUniform; infer_instance
  rw [blockPair_obsLaw_map]
  exact Measure.isProbabilityMeasure_map (blockObservationMap_measurable m q h σ).aemeasurable

/-- The observable positive experiment is absolutely continuous relative to the negative one. -/
-- @node: blockPair_obsLaw_sign_absolutelyContinuous
lemma blockPair_obsLaw_sign_absolutelyContinuous (m q h : ℝ)
    (hh : -1 < h) (hh1 : h < 1) :
    (blockPair m q h true).obsLaw ≪ (blockPair m q h false).obsLaw := by
  rw [← blockPair_obsLaw_sign_withDensity m q h hh hh1]
  exact withDensity_absolutelyContinuous _ _

/-- The real observable Radon–Nikodym derivative equals the explicit row likelihood. -/
-- @node: blockPair_obsLaw_sign_rnDeriv
lemma blockPair_obsLaw_sign_rnDeriv (m q h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    (fun o => (((blockPair m q h true).obsLaw).rnDeriv
      (blockPair m q h false).obsLaw o).toReal) =ᵐ[(blockPair m q h false).obsLaw]
      blockObservationLikelihood m h := by
  haveI := blockPair_obsLaw_probability m q h false
  have hd : Measurable (fun o => ENNReal.ofReal (blockObservationLikelihood m h o)) := by
    fun_prop
  have hr := Measure.rnDeriv_withDensity (blockPair m q h false).obsLaw hd
  rw [blockPair_obsLaw_sign_withDensity m q h hh hh1] at hr
  filter_upwards [hr] with o ho
  rw [ho, ENNReal.toReal_ofReal (blockObservationLikelihood_positive m h hh hh1 o).le]

/-- The squared observable likelihood deviation is integrable by its finite range. -/
-- @node: blockPair_obsLaw_likelihood_sq_integrable
lemma blockPair_obsLaw_likelihood_sq_integrable (m q h : ℝ) :
    Integrable (fun o => (blockObservationLikelihood m h o - 1)^2)
      (blockPair m q h false).obsLaw := by
  haveI := blockPair_obsLaw_probability m q h false
  have hd : Measurable (fun o => (blockObservationLikelihood m h o - 1)^2) := by fun_prop
  apply Integrable.of_bound hd.aestronglyMeasurable
    (max (((1+h)/(1-h)-1)^2) (((1-h)/(1+h)-1)^2))
  filter_upwards with o
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  unfold blockObservationLikelihood binarySignLikelihood
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _
  · simpa using (sq_nonneg ((1+h)/(1-h)-1)).trans (le_max_left _ _)

/-- Tensorization regularity follows from the bounded explicit observable density. -/
-- @node: blockPair_obsLaw_sign_sq_integrable
lemma blockPair_obsLaw_sign_sq_integrable (m q h : ℝ) (hh : -1 < h) (hh1 : h < 1) :
    Integrable (fun o => ((((blockPair m q h true).obsLaw).rnDeriv
      (blockPair m q h false).obsLaw o).toReal - 1)^2)
      (blockPair m q h false).obsLaw := by
  apply (blockPair_obsLaw_likelihood_sq_integrable m q h).congr
  filter_upwards [blockPair_obsLaw_sign_rnDeriv m q h hh hh1] with o ho
  rw [ho]

/-- The actual observable-row chi-square is the channel divergence times the rare-event mass. -/
-- @node: blockPair_obsLaw_sign_chiSqDiv
lemma blockPair_obsLaw_sign_chiSqDiv (m q h : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hh : -1 < h) (hh1 : h < 1) :
    Causalean.Stat.chiSqDiv (blockPair m q h true).obsLaw
      (blockPair m q h false).obsLaw = m*q*(4*h^2/(1-h^2)) := by
  haveI := uniformRandomizer_probability
  unfold Causalean.Stat.chiSqDiv
  calc
    _ = ∫ o, (blockObservationLikelihood m h o - 1)^2
        ∂(blockPair m q h false).obsLaw := by
      apply integral_congr_ae
      filter_upwards [blockPair_obsLaw_sign_rnDeriv m q h hh hh1] with o ho
      rw [ho]
    _ = ∫ v, (blockObservationLikelihood m h (blockObservationMap m q h false v)-1)^2
        ∂fourUniform := by
      rw [blockPair_obsLaw_map, integral_map
        (blockObservationMap_measurable m q h false).aemeasurable (by fun_prop)]
    _ = ∫ v : (((ℝ × ℝ) × ℝ) × ℝ),
        ((if v.1.1.1 ≤ m then (1:ℝ) else 0) *
          (if v.1.1.2 ≤ q then (1:ℝ) else 0)) *
        (binarySignLikelihood h (binaryOutcome (-h) v.2)-1)^2 ∂fourUniform := by
      apply integral_congr_ae
      filter_upwards with v
      by_cases hx : v.1.1.1 ≤ m <;> by_cases ha : v.1.1.2 ≤ q <;>
        simp [blockObservationLikelihood, blockObservationMap, blockLogger, blockMeanOne, hx, ha]
    _ = _ := by
      unfold fourUniform
      rw [integral_prod_mul
        (fun v : (ℝ × ℝ) × ℝ => (if v.1.1 ≤ m then (1:ℝ) else 0) *
          (if v.1.2 ≤ q then (1:ℝ) else 0))
        (fun u => (binarySignLikelihood h (binaryOutcome (-h) u)-1)^2),
        integral_fun_fst (fun v : ℝ × ℝ => (if v.1 ≤ m then (1:ℝ) else 0) *
          (if v.2 ≤ q then (1:ℝ) else 0)),
        integral_prod_mul (fun x => if x ≤ m then (1:ℝ) else 0)
          (fun u => if u ≤ q then (1:ℝ) else 0),
        uniformRandomizer_coin_integral m hm hm1,
        uniformRandomizer_coin_integral q hq hq1,
        binaryOutcome_sign_chi_integral h hh hh1]
      simp

/-- The observable row satisfies the paper's rare-block chi-square bound. -/
-- @node: blockPair_obsLaw_sign_chiSqDiv_bound
lemma blockPair_obsLaw_sign_chiSqDiv_bound (m q h : ℝ)
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1/2) :
    Causalean.Stat.chiSqDiv (blockPair m q h true).obsLaw
      (blockPair m q h false).obsLaw ≤ 8*m*q*h^2 := by
  rw [blockPair_obsLaw_sign_chiSqDiv m q h hm hm1 hq hq1 (by linarith) (by linarith)]
  have hb := binaryOutcome_sign_chi_bound h hh hh1
  rw [binaryOutcome_sign_chi_integral h (by linarith) (by linarith)] at hb
  calc
    _ ≤ m*q*(8*h^2) := mul_le_mul_of_nonneg_left hb (mul_nonneg hm hq)
    _ = _ := by ring

end CausalSmith.Stat.ScorethresholdOverlapRegret
