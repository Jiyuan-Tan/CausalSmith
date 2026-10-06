module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DirectPerturbation
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.IdentificationBasics
public import Causalean.Stat.Minimax.ChiSquared

/-! Target separation (16), (22) and observed-product distance assembly (49)--(51). -/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- The independent uniform threshold rank makes the causal target exactly the profile at the public dose. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hk). -/
-- @node: lowerWitness_causalTarget
lemma lowerWitness_causalTarget (E : PathSpace S) (kappa : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (mu : ThresholdProfile) :
    causalTarget E (lowerWitnessLaw E kappa mu) =
      (mu (Set.projIcc 0 1 zero_le_one a0) : ℝ) := by
  let := lowerWitnessLaw_probability E kappa hk mu
  rw [causalTarget_eq_stratum_sum E _ (lowerWitness_stratumPositive E kappa hk.1 mu)
    (lowerWitness_boundedPotentialOutcomes E kappa mu)]
  simp_rw [lowerWitness_condPotMean E kappa hk.1 mu _ a0 (by norm_num [a0])]
  have hm (x : Bool) : strataProb (lowerWitnessLaw E kappa mu) x = 1/2 := by
    rw [strataProb, measureReal_def, lowerWitness_stratum_mass E kappa hk.1 mu x]
    norm_num
  simp_rw [hm]
  simp

/-- Symmetric profiles have causal-target difference twice the perturbation at zero, on the fixed public path space. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hk,hformula). -/
-- @node: lower_profile_target_difference
lemma lower_profile_target_difference (E : PathSpace S) (kappa : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (muPlus muMinus : ThresholdProfile) (delta : ℝ → ℝ)
    (hformula : ∀ a : Dose, (muPlus a : ℝ) = 1/2 + delta ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - delta ((a : ℝ)-a0)) :
    causalTarget E (lowerWitnessLaw E kappa muPlus) -
      causalTarget E (lowerWitnessLaw E kappa muMinus) = 2*delta 0 := by
  rw [lowerWitness_causalTarget E kappa hk muPlus,
    lowerWitness_causalTarget E kappa hk muMinus]
  have ha : a0 ∈ Icc (0 : ℝ) 1 := by norm_num [a0]
  have hf := hformula (Set.projIcc 0 1 zero_le_one a0)
  rw [Set.projIcc_of_mem zero_le_one ha, sub_self] at hf
  rw [Set.projIcc_of_mem zero_le_one ha, hf.1, hf.2]
  ring

/-- Equation (16) is the exact absolute separation of the direct threshold witnesses. [Under the stated conditions](hyp:h,he,hh,hk,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_target_separation
lemma direct_profile_target_separation (E : PathSpace S) (beta kappa epsilon h : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (he : 0 ≤ epsilon) (hh : 0 < h)
    (muPlus muMinus : ThresholdProfile)
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon h ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon h ((a : ℝ)-a0)) :
    |causalTarget E (lowerWitnessLaw E kappa muPlus) -
      causalTarget E (lowerWitnessLaw E kappa muMinus)| = 2*epsilon*h^beta := by
  rw [lower_profile_target_difference E kappa hk muPlus muMinus _ hformula,
    directPerturbation_zero beta epsilon h hh, abs_of_nonneg (by positivity)]
  ring

/-- Equation (22) uses the same normalized packet as the moment cancellations. [Under the stated conditions](hyp:h,hp,he,hh,hk,hformula). [This is the stated conclusion](goal). -/
-- @node: inverse_profile_target_separation
lemma inverse_profile_target_separation (E : PathSpace S) (beta kappa epsilon h ell C c : ℝ)
    (m : ℕ) (hk : kappa ∈ Icc (0 : ℝ) 2) (hp : PacketBounds kappa C c m)
    (he : 0 ≤ epsilon) (hh : 0 ≤ h) (muPlus muMinus : ThresholdProfile)
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + epsilon*h^beta*packetPsi kappa m (((a : ℝ)-a0)/ell) ∧
      (muMinus a : ℝ) = 1/2 - epsilon*h^beta*packetPsi kappa m (((a : ℝ)-a0)/ell)) :
    |causalTarget E (lowerWitnessLaw E kappa muPlus) -
      causalTarget E (lowerWitnessLaw E kappa muMinus)| = 2*epsilon*h^beta := by
  rw [lower_profile_target_difference E kappa hk muPlus muMinus
    (fun t => epsilon*h^beta*packetPsi kappa m (t/ell)) hformula]
  rw [zero_div, hp.2.2.2.2.1, mul_one, abs_of_nonneg (by positivity)]
  ring

/-- The direct frontier branch agrees exactly with the separation amplitude. [Under the stated conditions](hyp:he,hh,hs,hk,hformula). [This is the stated conclusion](goal). -/
-- @node: direct_profile_frontier_separation
lemma direct_profile_frontier_separation (E : PathSpace S) (beta kappa epsilon sigma : ℝ)
    (n : ℕ) (hk : kappa ∈ Icc (0 : ℝ) 2) (he : 0 ≤ epsilon)
    (hh : 0 < directScale beta kappa n) (hs : sigma ≤ directScale beta kappa n)
    (muPlus muMinus : ThresholdProfile)
    (hformula : ∀ a : Dose,
      (muPlus a : ℝ) = 1/2 + directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0) ∧
      (muMinus a : ℝ) = 1/2 - directPerturbation beta epsilon (directScale beta kappa n) ((a : ℝ)-a0)) :
    |causalTarget E (lowerWitnessLaw E kappa muPlus) -
      causalTarget E (lowerWitnessLaw E kappa muMinus)| =
        (2*epsilon)*frontierRate beta kappa sigma n := by
  rw [direct_profile_target_separation E beta kappa epsilon _ hk he hh muPlus muMinus hformula]
  simp only [frontierRate, frontierScale, if_pos hs]

/-- Tensorization (49), the exponential bound, and Cauchy--Schwarz (50) convert a single-record budget to product TV. [Under the stated conditions](hyp:hac,hi,hbudget). [This is the stated conclusion](goal). -/
-- @node: lower_iid_tv_le_half_sqrt_exp
lemma lower_iid_tv_le_half_sqrt_exp {Ω : Type*} [MeasurableSpace Ω]
    (Q Qstar : Measure Ω) [IsProbabilityMeasure Q] [IsProbabilityMeasure Qstar]
    (hac : Q ≪ Qstar)
    (hi : Integrable (fun x => ((Q.rnDeriv Qstar x).toReal - 1) ^ 2) Qstar)
    (n : ℕ) (budget : ℝ) (hbudget : (n : ℝ) * Causalean.Stat.chiSqDiv Q Qstar ≤ budget) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Q))
      (Measure.pi (fun _ : Fin n => Qstar)) ≤ (1/2)*Real.sqrt (Real.exp budget - 1) := by
  have hp := Causalean.Stat.one_add_chiSqDiv_pi_iid_general Q Qstar hac hi n
  have hnonneg : 0 ≤ Causalean.Stat.chiSqDiv Q Qstar := Causalean.Stat.chiSqDiv_nonneg
  have hexp : (1 + Causalean.Stat.chiSqDiv Q Qstar)^n ≤ Real.exp budget := by
    calc
      _ ≤ (Real.exp (Causalean.Stat.chiSqDiv Q Qstar))^n :=
        pow_le_pow_left₀ (by linarith)
          (by linarith [Real.add_one_le_exp (Causalean.Stat.chiSqDiv Q Qstar)]) n
      _ = Real.exp ((n : ℝ) * Causalean.Stat.chiSqDiv Q Qstar) := by
        rw [Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr hbudget
  have hchi : Causalean.Stat.chiSqDiv (Measure.pi (fun _ : Fin n => Q))
      (Measure.pi (fun _ : Fin n => Qstar)) ≤ Real.exp budget - 1 := by
    linarith
  exact (Causalean.Stat.tvDist_le_half_sqrt_chiSqDiv _ _
    (Causalean.Mathlib.Probability.ProductAbsolutelyContinuous.pi_iid_absolutelyContinuous Q Qstar hac n)
    (Causalean.Stat.pi_iid_integrable_sq_dev Q Qstar hac hi n)).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hchi) (by norm_num))

/-- A common reference and the logarithmic budget log(1+τ²) give the paper's pairwise product-TV bound (51) at level τ. [Under the stated conditions](hyp:hp,hm,hip,him,hbp,hbm,htau). [This is the stated conclusion](goal). -/
-- @node: lower_pair_iid_tv_le
lemma lower_pair_iid_tv_le {Ω : Type*} [MeasurableSpace Ω]
    (Qplus Qminus Qstar : Measure Ω) [IsProbabilityMeasure Qplus]
    [IsProbabilityMeasure Qminus] [IsProbabilityMeasure Qstar]
    (hp : Qplus ≪ Qstar) (hm : Qminus ≪ Qstar)
    (hip : Integrable (fun x => ((Qplus.rnDeriv Qstar x).toReal - 1) ^ 2) Qstar)
    (him : Integrable (fun x => ((Qminus.rnDeriv Qstar x).toReal - 1) ^ 2) Qstar)
    (n : ℕ) (tau : ℝ) (htau : 0 ≤ tau)
    (hbp : (n : ℝ) * Causalean.Stat.chiSqDiv Qplus Qstar ≤ Real.log (1 + tau^2))
    (hbm : (n : ℝ) * Causalean.Stat.chiSqDiv Qminus Qstar ≤ Real.log (1 + tau^2)) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Qplus))
      (Measure.pi (fun _ : Fin n => Qminus)) ≤ tau := by
  have hsqrt : Real.sqrt (Real.exp (Real.log (1 + tau^2)) - 1) = tau := by
    rw [Real.exp_log (by positivity), add_sub_cancel_left]
    exact Real.sqrt_sq htau
  have hplus := lower_iid_tv_le_half_sqrt_exp Qplus Qstar hp hip n _ hbp
  have hminus := lower_iid_tv_le_half_sqrt_exp Qminus Qstar hm him n _ hbm
  rw [hsqrt] at hplus hminus
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  intro A
  calc
    _ ≤ |(Measure.pi (fun _ : Fin n => Qplus)).real A.1 -
        (Measure.pi (fun _ : Fin n => Qstar)).real A.1| +
        |(Measure.pi (fun _ : Fin n => Qstar)).real A.1 -
        (Measure.pi (fun _ : Fin n => Qminus)).real A.1| := abs_sub_le _ _ _
    _ ≤ Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Qplus))
        (Measure.pi (fun _ : Fin n => Qstar)) +
        Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Qminus))
        (Measure.pi (fun _ : Fin n => Qstar)) := by
      rw [abs_sub_comm ((Measure.pi (fun _ : Fin n => Qstar)).real A.1)]
      exact add_le_add (Causalean.Stat.abs_measureReal_sub_le_tvDist A.2)
        (Causalean.Stat.abs_measureReal_sub_le_tvDist A.2)
    _ ≤ tau := by linarith

/-- Applied to actual observed marginals, the common-reference budget log(1+τ²) controls the declared experiment's total variation by τ at every noise scale, including zero. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hk,hp,hm,hip,him,hbp,hbm,htau). -/
-- @node: lower_observed_experiment_tv_le
lemma lower_observed_experiment_tv_le (E : PathSpace S) (kappa sigma : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (muPlus muMinus : ThresholdProfile) (n : ℕ)
    (tau : ℝ) (htau : 0 ≤ tau)
    (hp : obsLaw sigma (lowerWitnessLaw E kappa muPlus) ≪
      obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    (hm : obsLaw sigma (lowerWitnessLaw E kappa muMinus) ≪
      obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    (hip : Integrable (fun o =>
      (((obsLaw sigma (lowerWitnessLaw E kappa muPlus)).rnDeriv
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal - 1) ^ 2)
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)))
    (him : Integrable (fun o =>
      (((obsLaw sigma (lowerWitnessLaw E kappa muMinus)).rnDeriv
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal - 1) ^ 2)
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)))
    (hbp : (n : ℝ) * Causalean.Stat.chiSqDiv
      (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ Real.log (1 + tau^2))
    (hbm : (n : ℝ) * Causalean.Stat.chiSqDiv
      (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ Real.log (1 + tau^2)) :
    Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
      (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ tau := by
  have hobs : Measurable (obsMap (S := S) sigma) := by
    unfold obsMap contaminatedDose
    fun_prop
  have hprob (mu : ThresholdProfile) : IsProbabilityMeasure
      (obsLaw sigma (lowerWitnessLaw E kappa mu)) := by
    let := lowerWitnessLaw_probability E kappa hk mu
    exact Measure.isProbabilityMeasure_map hobs.aemeasurable
  let := hprob muPlus
  let := hprob muMinus
  let := hprob referenceProfile
  exact lower_pair_iid_tv_le _ _ _ hp hm hip him n tau htau hbp hbm

/-- [Two laws absolutely continuous](hyp:hp,hm) with respect to a common reference, [with square-integrable likelihood-ratio deviations](hyp:hip,him) and [chi-square divergences from it, times the sample size, at most log(26/25)](hyp:hbp,hbm), [have n-fold product laws within total variation one fifth of each other](goal); this is the paper's pairwise bound (51), the level-one-fifth instance of the general product-TV bound. -/
-- @node: lower_pair_iid_tv_le_one_fifth
lemma lower_pair_iid_tv_le_one_fifth {Ω : Type*} [MeasurableSpace Ω]
    (Qplus Qminus Qstar : Measure Ω) [IsProbabilityMeasure Qplus]
    [IsProbabilityMeasure Qminus] [IsProbabilityMeasure Qstar]
    (hp : Qplus ≪ Qstar) (hm : Qminus ≪ Qstar)
    (hip : Integrable (fun x => ((Qplus.rnDeriv Qstar x).toReal - 1) ^ 2) Qstar)
    (him : Integrable (fun x => ((Qminus.rnDeriv Qstar x).toReal - 1) ^ 2) Qstar)
    (n : ℕ)
    (hbp : (n : ℝ) * Causalean.Stat.chiSqDiv Qplus Qstar ≤ Real.log (26 / 25))
    (hbm : (n : ℝ) * Causalean.Stat.chiSqDiv Qminus Qstar ≤ Real.log (26 / 25)) :
    Causalean.Stat.tvDist (Measure.pi (fun _ : Fin n => Qplus))
      (Measure.pi (fun _ : Fin n => Qminus)) ≤ 1/5 := by
  have h : Real.log (26 / 25) = Real.log (1 + (1/5 : ℝ)^2) := by norm_num
  rw [h] at hbp hbm
  exact lower_pair_iid_tv_le Qplus Qminus Qstar hp hm hip him n (1/5) (by norm_num) hbp hbm

/-- [For a design exponent between zero and two](hyp:hk), when [the observed witness marginals are absolutely continuous](hyp:hp,hm) with respect to the reference witness marginal, [with square-integrable likelihood-ratio deviations](hyp:hip,him) and [chi-square divergences, times the sample size, at most log(26/25)](hyp:hbp,hbm), [the two declared observed experiments are within total variation one fifth](goal) at every noise scale, including zero; this is the level-one-fifth instance of the general observed-experiment bound. -/
-- @node: lower_observed_experiment_tv_le_one_fifth
lemma lower_observed_experiment_tv_le_one_fifth (E : PathSpace S) (kappa sigma : ℝ)
    (hk : kappa ∈ Icc (0 : ℝ) 2) (muPlus muMinus : ThresholdProfile) (n : ℕ)
    (hp : obsLaw sigma (lowerWitnessLaw E kappa muPlus) ≪
      obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    (hm : obsLaw sigma (lowerWitnessLaw E kappa muMinus) ≪
      obsLaw sigma (lowerWitnessLaw E kappa referenceProfile))
    (hip : Integrable (fun o =>
      (((obsLaw sigma (lowerWitnessLaw E kappa muPlus)).rnDeriv
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal - 1) ^ 2)
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)))
    (him : Integrable (fun o =>
      (((obsLaw sigma (lowerWitnessLaw E kappa muMinus)).rnDeriv
        (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) o).toReal - 1) ^ 2)
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)))
    (hbp : (n : ℝ) * Causalean.Stat.chiSqDiv
      (obsLaw sigma (lowerWitnessLaw E kappa muPlus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ Real.log (26 / 25))
    (hbm : (n : ℝ) * Causalean.Stat.chiSqDiv
      (obsLaw sigma (lowerWitnessLaw E kappa muMinus))
      (obsLaw sigma (lowerWitnessLaw E kappa referenceProfile)) ≤ Real.log (26 / 25)) :
    Causalean.Stat.tvDist (experiment n sigma (lowerWitnessLaw E kappa muPlus))
      (experiment n sigma (lowerWitnessLaw E kappa muMinus)) ≤ 1/5 := by
  have h : Real.log (26 / 25) = Real.log (1 + (1/5 : ℝ)^2) := by norm_num
  rw [h] at hbp hbm
  exact lower_observed_experiment_tv_le E kappa sigma hk muPlus muMinus n (1/5) (by norm_num)
    hp hm hip him hbp hbm

end CausalSmith.Stat.NoisydoseWeakdesignTransition
