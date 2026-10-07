module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.CausalPriorDecision
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.ConverseResources
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.ProductPriorConcentration
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TwoPoint
public import Causalean.Mathlib.Analysis.Duality.MomentPrior.Basic

/-!
# Helpers/Frontier/Lower

Finite original-record private value frontiers: Helpers/Frontier/Lower.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


/-- [The paper's indexed infimum agrees with the library's best uniform error](goal). -/
-- @node: bestAbsApproxError_eq_library
lemma bestAbsApproxError_eq_library (K : ℕ) :
    bestAbsApproxError K =
      Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs K := by
  unfold bestAbsApproxError
    Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs
  change sInf (Set.range (fun p : {p : Polynomial ℝ // p.natDegree ≤ K} =>
    sSup ((fun x : ℝ => abs (p.1.eval x - abs x)) '' Set.Icc (-1) 1))) = _
  congr 1
  ext e
  constructor
  · rintro ⟨p, rfl⟩
    refine ⟨p.1, p.2, ?_⟩
    simp only [Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs,
      Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.symmUnitInterval, abs_sub_comm]
  · rintro ⟨p, hp, rfl⟩
    refine ⟨⟨p, hp⟩, ?_⟩
    simp only [Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.uniformApproxErrorAbs,
      Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.symmUnitInterval, abs_sub_comm]

/-- [Increasing the degree enlarges the candidate space and decreases the best error](goal). -/
-- @node: bestAbsApproxError_antitone
lemma bestAbsApproxError_antitone : Antitone bestAbsApproxError := by
  intro K L hKL
  rw [bestAbsApproxError_eq_library, bestAbsApproxError_eq_library]
  exact Causalean.Mathlib.Analysis.AbsoluteValueMomentPriorDuality.bestUniformApproxErrorAbs_antitone hKL

/-- Assume [the Bernstein absolute-approximation limit](hyp:hBernstein_of_gate). [Positive universal absolute-approximation scale, including each finite even degree](goal). -/
-- @node: bernstein_uniform_positive_of_gate
lemma bernstein_uniform_positive_of_gate (hBernstein_of_gate :
  BernsteinAbsoluteApproximationLimit) :
    ∃ bStar : ℝ, 0 < bStar ∧ ∀ K : ℕ, 0 < K → Even K → bStar/K ≤ bestAbsApproxError K := by
  obtain ⟨betaStar, hbeta, _hupper, hlimit⟩ := hBernstein_of_gate
  have htail : ∀ᶠ k : ℕ in Filter.atTop,
      (1/10 : ℝ) ≤ (2*k : ℝ) * bestAbsApproxError (2*k) :=
    hlimit.eventually_const_le (by linarith)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp htail
  let N := max N0 1
  have hN : 0 < N := by dsimp [N]; omega
  have hcut := hN0 N (by dsimp [N]; omega)
  have hcutpos : 0 < bestAbsApproxError (2*N) := by
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    by_contra h
    have hmul : (2*N : ℝ) * bestAbsApproxError (2*N) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt h)
    linarith
  refine ⟨min (1/10) (bestAbsApproxError (2*N)), lt_min (by norm_num) hcutpos, ?_⟩
  intro K hK hEven
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  rw [div_le_iff₀ hKreal]
  obtain ⟨k, hk⟩ := hEven
  have hKk : K = 2*k := by omega
  by_cases hlarge : N ≤ k
  · have hbound := hN0 k (by dsimp [N] at hlarge; omega)
    rw [hKk]
    exact (min_le_left _ _).trans (by simpa [mul_comm] using hbound)
  · have hdegree : K ≤ 2*N := by omega
    have hmono := bestAbsApproxError_antitone hdegree
    have herrpos : 0 < bestAbsApproxError K := hcutpos.trans_le hmono
    have hKone : (1 : ℝ) ≤ K := by exact_mod_cast hK
    calc
      min (1/10) (bestAbsApproxError (2*N)) ≤ bestAbsApproxError (2*N) := min_le_right _ _
      _ ≤ bestAbsApproxError K := hmono
      _ ≤ bestAbsApproxError K * K := le_mul_of_one_le_right herrpos.le hKone
/-- Assume [the stated hxi condition](hyp:hxi) and [the stated ha condition](hyp:ha). [Positive scaling transports a unit-interval probability to the amplitude interval](goal). -/
-- @node: amplitudePrior_map_scale
lemma amplitudePrior_map_scale (xi : Measure ℝ) [IsProbabilityMeasure xi]
    (hxi : xi (Set.Icc (-1 : ℝ) 1)ᶜ = 0) (a : ℝ) (ha : 0 < a) :
    AmplitudePrior a (xi.map (fun x => a*x)) := by
  have hscale : Measurable (fun x : ℝ => a*x) := by fun_prop
  constructor
  · exact Measure.isProbabilityMeasure_map hscale.aemeasurable
  · rw [Measure.map_apply hscale (isClosed_Icc.measurableSet.compl)]
    apply measure_mono_null _ hxi
    intro x hx
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_Icc] at hx ⊢
    intro hunit
    apply hx
    constructor <;> nlinarith [hunit.1, hunit.2]

/-- [Pushforward scaling multiplies the q-th raw moment by the q-th power of the scale](goal). -/
-- @node: integral_pow_map_scale
lemma integral_pow_map_scale (xi : Measure ℝ) (a : ℝ) (q : ℕ) :
    (∫ x, x^q ∂xi.map (fun x => a*x)) = a^q * ∫ x, x^q ∂xi := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [mul_pow]
  exact integral_const_mul _ _

/-- Assume [nonnegative amplitude](hyp:ha). [Positive pushforward scaling multiplies the absolute moment by the scale](goal). -/
-- @node: integral_abs_map_scale
lemma integral_abs_map_scale (xi : Measure ℝ) (a : ℝ) (ha : 0 ≤ a) :
    (∫ x, |x| ∂xi.map (fun x => a*x)) = a * ∫ x, |x| ∂xi := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, abs_of_nonneg ha]
  exact integral_const_mul _ _

/-- Assume [the Cai–Low moment-duality theorem](hyp:hDual_of_gate), [the stated privacy condition for the protocol](hyp:hK), [the stated even condition](hyp:hEven), and [the stated ha condition](hyp:ha). [Scaled symmetric duality priors retain exact moment matching and target separation](goal). -/
-- @node: scaled_dual_priors_of_gate
lemma scaled_dual_priors_of_gate (hDual_of_gate : CaiLowMomentDuality)
    (K : ℕ) (hK : 0 < K) (hEven : Even K) (a : ℝ) (ha : 0 < a) :
    ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
      MatchingMoments (K+1) nu0 nu1 ∧
      (∫ u, |u| ∂nu1) - (∫ u, |u| ∂nu0) = 2*a*bestAbsApproxError K := by
  obtain ⟨xi0, xi1, hprob0, hprob1, hsupp0, hsupp1, _hsym0, _hsym1, hmom, hgap⟩ :=
    hDual_of_gate K hK hEven
  let := hprob0
  let := hprob1
  refine ⟨xi0.map (fun x => a*x), xi1.map (fun x => a*x),
    amplitudePrior_map_scale xi0 hsupp0 a ha,
    amplitudePrior_map_scale xi1 hsupp1 a ha, ?_, ?_⟩
  · intro q hq
    rw [integral_pow_map_scale, integral_pow_map_scale, hmom q (by omega)]
  · rw [integral_abs_map_scale xi1 a ha.le, integral_abs_map_scale xi0 a ha.le,
      ← mul_sub, hgap]
    ring
/-- Assume [the Cai–Low moment-duality theorem](hyp:hDual) and [the Bernstein absolute-approximation limit](hyp:hBernstein). [The scaled dual priors have separated half-norm means and both targets concentrate within one eighth of their actual mean gap. The escape bound is uniform in amplitude, as required before choosing the dimension cutoff](goal). -/
-- @node: dual_product_priors_target_concentration_of_gate
lemma dual_product_priors_target_concentration_of_gate
    (hDual : CaiLowMomentDuality) (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∀ (d K : ℕ), 0 < d → 0 < K → Even K →
      ∀ a : ℝ, 0 < a →
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (K+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ b*a/K ≤ gap ∧
          (∫ theta, signedNorm theta/2 ∂productPrior d nu1) -
            (∫ theta, signedNorm theta/2 ∂productPrior d nu0) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            (productPrior d nu) {theta | gap/8 ≤
              |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} ≤
                ENNReal.ofReal (16*(K : ℝ)^2/(b^2*d))) := by
  obtain ⟨b, hb, happrox⟩ := bernstein_uniform_positive_of_gate hBernstein
  refine ⟨b, hb, ?_⟩
  intro d K hd hK hEven a ha
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, hgap⟩ :=
    scaled_dual_priors_of_gate hDual K hK hEven a ha
  let gap := a * bestAbsApproxError K
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlower : b*a/K ≤ gap := by
    dsimp [gap]
    have h := mul_le_mul_of_nonneg_left (happrox K hK hEven) ha.le
    calc
      b*a/K = a*(b/K) := by ring
      _ ≤ a * bestAbsApproxError K := h
  have hpos : 0 < gap := (by positivity : (0 : ℝ) < b*a/K).trans_le hlower
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hpos, hlower, ?_, ?_⟩
  · rw [productPrior_halfNorm_mean d hd a nu1 hnu1,
      productPrior_halfNorm_mean d hd a nu0 hnu0]
    have h := hgap
    dsimp [gap]
    linarith
  · intro nu hnu
    have hamp : AmplitudePrior a nu := by
      rcases hnu with rfl | hnu
      · exact hnu0
      · have heq : nu = nu1 := Set.mem_singleton_iff.mp hnu
        simpa [heq] using hnu1
    refine (productPrior_halfNorm_gap_escape d hd a nu hamp gap hpos).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have hmul : b*a ≤ gap*K := (div_le_iff₀ hKR).mp hlower
    have hsq : (b*a)^2 ≤ (gap*K)^2 :=
      pow_le_pow_left₀ (by positivity) hmul 2
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < d*gap^2)
      (by positivity : (0 : ℝ) < b^2*d)).mpr
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 16*d)
    nlinarith

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Mapping a supported coordinate prior to symmetric causal laws shifts its half-norm mean by the common baseline one half](goal). -/
-- @node: symmetricLaw_productPrior_value_mean
lemma symmetricLaw_productPrior_value_mean (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : a ≤ (1/2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (∫ P, value P ∂(productPrior d nu).map symmetricLaw) =
      1/2 + (∫ u, |u| ∂nu)/2 := by
  letI := hnu.1
  haveI : IsProbabilityMeasure (productPrior d nu) := by
    unfold productPrior
    infer_instance
  have hint : Integrable (fun theta : Fin d → ℝ => signedNorm theta/2)
      (productPrior d nu) := by
    unfold signedNorm
    apply Integrable.div_const
    apply Integrable.const_mul
    apply integrable_finsetSum
    intro j hj
    exact ((amplitudePrior_abs_memLp a nu hnu).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin d => nu) j)).integrable
      (by norm_num)
  rw [integral_map measurable_symmetricLaw_parameter.aemeasurable
    measurable_causal_value.aestronglyMeasurable]
  calc
    _ = ∫ theta, (1/2 : ℝ) + signedNorm theta/2 ∂productPrior d nu := by
      apply integral_congr_ae
      filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
      exact symmetricLaw_value theta htheta hd
    _ = 1/2 + (∫ theta, signedNorm theta/2 ∂productPrior d nu) := by
      rw [integral_add (integrable_const _) hint, integral_const]
      simp
    _ = _ := by rw [productPrior_halfNorm_mean d hd a nu hnu]

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [A common baseline shift preserves target-neighborhood escape probabilities when the coordinate prior is pushed to full-data causal laws](goal). -/
-- @node: symmetricLaw_productPrior_value_escape
lemma symmetricLaw_productPrior_value_escape (d : ℕ) (hd : 0 < d)
    (a : ℝ) (ha : a ≤ (1/2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu)
    (radius center : ℝ) :
    ((productPrior d nu).map symmetricLaw)
      {P | radius < |value P - (1/2 + center)|} =
      (productPrior d nu) {theta | radius < |signedNorm theta/2 - center|} := by
  have hE : MeasurableSet {P : Measure (FullRecord d) |
      radius < |value P - (1/2 + center)|} := by
    apply measurableSet_lt measurable_const
    fun_prop
  rw [Measure.map_apply measurable_symmetricLaw_parameter hE]
  apply measure_congr
  filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
  change (radius < |value (symmetricLaw theta) - (1/2 + center)|) =
    (radius < |signedNorm theta/2 - center|)
  rw [symmetricLaw_value theta htheta hd]
  congr 2
  ring

/-- Assume [the Cai–Low moment-duality theorem](hyp:hDual) and [the Bernstein absolute-approximation limit](hyp:hBernstein). [Moment-dual coordinate priors produce a positive gap between actual welfare means and the same quantitative escape bound on causal law space](goal). -/
-- @node: causal_dual_product_priors_target_concentration_of_gate
lemma causal_dual_product_priors_target_concentration_of_gate
    (hDual : CaiLowMomentDuality) (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∀ (d K : ℕ), 0 < d → 0 < K → Even K →
      ∀ a : ℝ, 0 < a → a ≤ (1/2 : ℝ) →
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (K+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ b*a/K ≤ gap ∧
          (∫ P, value P ∂(productPrior d nu1).map symmetricLaw) -
            (∫ P, value P ∂(productPrior d nu0).map symmetricLaw) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            ((productPrior d nu).map symmetricLaw).real
              {P | gap/8 < |value P - (1/2 + (∫ u, |u| ∂nu)/2)|} ≤
                16*(K : ℝ)^2/(b^2*d)) := by
  obtain ⟨b, hb, hpriors⟩ :=
    dual_product_priors_target_concentration_of_gate hDual hBernstein
  refine ⟨b, hb, ?_⟩
  intro d K hd hK hEven a ha haHalf
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower, hmean, hescape⟩ :=
    hpriors d K hd hK hEven a ha
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower, ?_, ?_⟩
  · rw [symmetricLaw_productPrior_value_mean d hd a haHalf nu1 hnu1,
      symmetricLaw_productPrior_value_mean d hd a haHalf nu0 hnu0]
    rw [productPrior_halfNorm_mean d hd a nu1 hnu1,
      productPrior_halfNorm_mean d hd a nu0 hnu0] at hmean
    linarith
  · intro nu hnu
    have hamp : AmplitudePrior a nu := by
      rcases hnu with rfl | hnu
      · exact hnu0
      · have heq : nu = nu1 := Set.mem_singleton_iff.mp hnu
        simpa [heq] using hnu1
    have hstrict : (productPrior d nu)
        {theta | gap/8 < |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} ≤
        ENNReal.ofReal (16*(K : ℝ)^2/(b^2*d)) :=
      (measure_mono (show
        {theta : Fin d → ℝ | gap/8 < |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} ⊆
          {theta | gap/8 ≤ |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} from by
            intro theta ht
            change gap/8 < |signedNorm theta/2 - (∫ u, |u| ∂nu)/2| at ht
            change gap/8 ≤ |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|
            exact ht.le)).trans (hescape nu hnu)
    unfold Measure.real
    rw [symmetricLaw_productPrior_value_escape d hd a haHalf nu hamp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hstrict).trans_eq
      (ENNReal.toReal_ofReal (by positivity))

/-- Assume [the Cai–Low moment-duality theorem](hyp:hDual) and [the Bernstein absolute-approximation limit](hyp:hBernstein). [At the prescribed resource amplitude and moment order, causal law-space priors have a frontier-sized welfare gap and escape probability at most one hundredth above a universal dimension cutoff](goal). -/
-- @node: causal_concentrated_resource_priors_of_gate
lemma causal_concentrated_resource_priors_of_gate
    (hDual : CaiLowMomentDuality) (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∃ D : ℕ, 2 ≤ D ∧
      ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D < d →
      let a := (frontierResources n d eps).converseAmp
      let q := (frontierResources n d eps).converseDegree - 1
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (q+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ (b/3400)*rateH .SI n d eps ≤ gap ∧
          (∫ P, value P ∂(productPrior d nu1).map symmetricLaw) -
            (∫ P, value P ∂(productPrior d nu0).map symmetricLaw) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            ((productPrior d nu).map symmetricLaw).real
              {P | gap/8 < |value P - (1/2 + (∫ u, |u| ∂nu)/2)|} ≤ (1/100 : ℝ)) := by
  obtain ⟨b, hb, hpriors⟩ :=
    causal_dual_product_priors_target_concentration_of_gate hDual hBernstein
  obtain ⟨D, hD, hcutoff⟩ := frontier_converse_concentration_cutoff b hb
  refine ⟨b, hb, D, hD, ?_⟩
  intro n d eps hAllowed hdim
  obtain ⟨hq, heven⟩ := frontier_converse_degree_domain n d eps hAllowed
  obtain ⟨ha, haHalf⟩ := frontier_converse_amplitude_domain n d eps hAllowed
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower, hmean, hescape⟩ :=
    hpriors d _ (by have := hAllowed.2.1; omega) hq heven _ ha haHalf
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, ?_, hmean, ?_⟩
  · calc
      (b/3400)*rateH .SI n d eps = b*((1/3400)*rateH .SI n d eps) := by ring
      _ ≤ b*((frontierResources n d eps).converseAmp /
          (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left (frontier_converse_gap_rate n d eps hAllowed) hb.le
      _ = b*(frontierResources n d eps).converseAmp /
          (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ) := by ring
      _ ≤ gap := hlower
  · intro nu hnu
    exact (hescape nu hnu).trans (hcutoff n d eps hAllowed hdim)

/-- Assume [polynomial degree at least two](hyp:hD), [dimension no larger than the polynomial degree](hyp:hdD), and [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [Below any fixed dimension cutoff, the frontier is controlled by the two-point rate](goal). -/
-- @node: bounded_dimension_frontier_comparisons
lemma bounded_dimension_frontier_comparisons (D n d : ℕ) (eps : ℝ)
    (hD : 2 ≤ D) (hdD : d ≤ D) (hAllowed : Allowed n d eps) :
    rateR .SI n d eps ≤ 4*(D : ℝ)^2 * min 1 (1/(n*eps^2)) ∧
    rateH .SI n d eps ≤ 4*(D : ℝ)^2 * min 1 (1/(Real.sqrt n*eps)) := by
  have hDR : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hdR : (0 : ℝ) ≤ d := by positivity
  have hdDR : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := hAllowed.1; omega)
  have ht : 0 < (n : ℝ)*eps^2 := mul_pos hnR (sq_pos_of_pos hAllowed.2.2.1)
  have hfactor : 1 ≤ (D : ℝ)^2 := by nlinarith
  have hbound : min 1 ((d : ℝ)^2/(n*eps^2)) ≤
      (D : ℝ)^2 * min 1 (1/(n*eps^2)) := by
    by_cases hsmall : (n : ℝ)*eps^2 ≤ 1
    · rw [show min 1 (1/(n*eps^2)) = 1 from min_eq_left ((le_div_iff₀ ht).mpr (by simpa using hsmall))]
      simpa only [mul_one] using (min_le_left 1 ((d : ℝ)^2/(n*eps^2))).trans hfactor
    · rw [show min 1 (1/(n*eps^2)) = 1/(n*eps^2) from min_eq_right ((div_le_iff₀ ht).mpr (by linarith))]
      refine (min_le_right _ _).trans ?_
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by nlinarith) ht.le
  have hr : rateR .SI n d eps ≤ 4*(D : ℝ)^2 * min 1 (1/(n*eps^2)) := by
    exact (rho_elementary_comparisons n d eps hAllowed).2.1.trans (by nlinarith [hbound])
  refine ⟨hr, ?_⟩
  have hs : 0 < Real.sqrt n*eps := mul_pos (Real.sqrt_pos.mpr hnR) hAllowed.2.2.1
  have hsq := min_one_reciprocal_sq (Real.sqrt n*eps) hs
  rw [mul_pow, Real.sq_sqrt hnR.le] at hsq
  have hm : 0 ≤ min 1 (1/(Real.sqrt n*eps)) := by positivity
  have hr0 : 0 ≤ rateR .SI n d eps :=
    (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
      (rho_elementary_comparisons n d eps hAllowed).1
  have hroot := Real.sq_sqrt hr0
  have hroot0 := Real.sqrt_nonneg (rateR .SI n d eps)
  have hrootle : Real.sqrt (rateR .SI n d eps) ≤
      2*(D : ℝ)*min 1 (1/(Real.sqrt n*eps)) := by
    have hsqbound : (Real.sqrt (rateR .SI n d eps))^2 ≤
        (2*(D : ℝ)*min 1 (1/(Real.sqrt n*eps)))^2 := by
      rw [hroot]
      calc
        _ ≤ 4*(D : ℝ)^2 * min 1 (1/(n*eps^2)) := hr
        _ = _ := by rw [← hsq]; ring
    nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 2*(D : ℝ)) hm]
  exact hrootle.trans (by nlinarith)

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [polynomial degree at least two](hyp:hD), [dimension no larger than the polynomial degree](hyp:hdD), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [sequential local privacy of the protocol](hyp:hQ). [A fixed dimension cutoff gives both per-decision frontier converses with one constant](goal). -/
-- @node: bounded_dimension_frontier_lower
lemma bounded_dimension_frontier_lower (hRN : MeasurableKernelRadonNikodym)
    (D n d : ℕ) (eps : ℝ) (hD : 2 ≤ D) (hdD : d ≤ D) (hAllowed : Allowed n d eps)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hQ : SequentialClass Q eps) :
    (∀ T : Estimator Q, ENNReal.ofReal ((1/(32768*(D : ℝ)^2))*rateR .SI n d eps) ≤
      ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
        squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
    (∀ I : IntervalDecision Q (1/4) (3/4),
      (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
      ENNReal.ofReal ((1/(32768*(D : ℝ)^2))*rateH .SI n d eps) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I) := by
  obtain ⟨hr, hh⟩ := bounded_dimension_frontier_comparisons D n d eps hD hdD hAllowed
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hscale : (1/(32768*(D : ℝ)^2))*(4*(D : ℝ)^2) = 1/8192 := by
    field_simp
    <;> ring
  have hscaledR := mul_le_mul_of_nonneg_left hr
    (by positivity : (0 : ℝ) ≤ 1/(32768*(D : ℝ)^2))
  have hscaledH := mul_le_mul_of_nonneg_left hh
    (by positivity : (0 : ℝ) ≤ 1/(32768*(D : ℝ)^2))
  rw [← mul_assoc, hscale] at hscaledR hscaledH
  have hdec := dimension_free_private_two_point_decisions hRN n d eps hAllowed S hIID hRandom Q hQ
  exact ⟨fun T => (ENNReal.ofReal_le_ofReal hscaledR).trans (hdec.1 T),
    fun I hCov => (ENNReal.ofReal_le_ofReal hscaledH).trans (hdec.2 I hCov)⟩

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate), [the Cai–Low moment-duality theorem](hyp:hDual_of_gate), and [the Bernstein absolute-approximation limit](hyp:hBernstein_of_gate). [Per-protocol and per-decision causal lower bounds, including connected honest intervals](goal). -/
-- @node: frontier_lower_of_gate
lemma frontier_lower_of_gate (hRN_of_gate : MeasurableKernelRadonNikodym)
    (hDual_of_gate : CaiLowMomentDuality) (hBernstein_of_gate :
      BernsteinAbsoluteApproximationLimit) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
      ∀ Q : LocalProtocol n (ObsRecord d), SequentialClass Q eps →
        (∀ T : Estimator Q, ENNReal.ofReal (c*rateR .SI n d eps) ≤
          ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
            squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
        (∀ I : IntervalDecision Q (1/4) (3/4),
          (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
          ENNReal.ofReal (c*rateH .SI n d eps) ≤
            ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
              expectedLength (decisionLaw S Q P.1) I) := by
  -- Concentrated product priors give the converse above a universal cutoff.
  have hLarge :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ c : ℝ, 0 < c ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D < d →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
      ∀ Q : LocalProtocol n (ObsRecord d), SequentialClass Q eps →
        (∀ T : Estimator Q, ENNReal.ofReal (c*rateR .SI n d eps) ≤
          ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
            squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
        (∀ I : IntervalDecision Q (1/4) (3/4),
          (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
          ENNReal.ofReal (c*rateH .SI n d eps) ≤
            ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
              expectedLength (decisionLaw S Q P.1) I) := by
    obtain ⟨b, hb, D, hD, hpriors⟩ :=
      causal_concentrated_resource_priors_of_gate hDual_of_gate hBernstein_of_gate
    let scale : ℝ := b/3400
    have hs : 0 < scale := by dsimp [scale]; positivity
    refine ⟨D, hD, min (scale^2/100) (scale/100),
      lt_min (by positivity) (by positivity), ?_⟩
    intro n d eps hAllowed hdim S hIID hRandom Q hQ
    obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap,
      hlower, hmean, hescape⟩ :=
      hpriors n d eps hAllowed hdim
    letI := hnu0.1
    letI := hnu1.1
    haveI : IsProbabilityMeasure (productPrior d nu0) := by unfold productPrior; infer_instance
    haveI : IsProbabilityMeasure (productPrior d nu1) := by unfold productPrior; infer_instance
    haveI : IsProbabilityMeasure ((productPrior d nu0).map symmetricLaw) :=
      Measure.isProbabilityMeasure_map measurable_symmetricLaw_parameter.aemeasurable
    haveI : IsProbabilityMeasure ((productPrior d nu1).map symmetricLaw) :=
      Measure.isProbabilityMeasure_map measurable_symmetricLaw_parameter.aemeasurable
    have hd : 0 < d := by have := hAllowed.2.1; omega
    have ha := (frontier_converse_amplitude_domain n d eps hAllowed).2
    have hdegree : (frontierResources n d eps).converseDegree - 1 + 1 =
        (frontierResources n d eps).converseDegree := by
      have := frontier_converse_degree_domain n d eps hAllowed
      omega
    rw [hdegree] at hmatch
    let v0 : ℝ := 1/2 + (∫ u, |u| ∂nu0)/2
    let v1 : ℝ := 1/2 + (∫ u, |u| ∂nu1)/2
    have hcenters : v1-v0 = gap := by
      rw [symmetricLaw_productPrior_value_mean d hd _ ha nu1 hnu1,
        symmetricLaw_productPrior_value_mean d hd _ ha nu0 hnu0] at hmean
      exact hmean
    have hTV := causal_lawspace_resource_contraction hRN_of_gate Q eps hQ hAllowed
      nu0 nu1 hnu0 hnu1 hmatch
    have hdec := causal_separated_lawspace_decisions S hIID hRandom Q
      ((productPrior d nu0).map symmetricLaw) ((productPrior d nu1).map symmetricLaw)
      (symmetricLaw_productPrior_support hd _ ha nu0 hnu0)
      (symmetricLaw_productPrior_support hd _ ha nu1 hnu1)
      v0 v1 (1/100) (1/100) (by linarith)
      (by simpa only [hcenters] using hescape nu0 (by simp))
      (by simpa only [hcenters] using hescape nu1 (by simp)) hTV
    rw [hcenters] at hdec
    have htest : max (0 : ℝ) (1-1/100-2*(1/100)) = 97/100 := by norm_num
    have hlength : max (0 : ℝ) ((0.80 : ℝ)-2*(1/100)-1/100) = 77/100 := by norm_num
    rw [htest, hlength] at hdec
    have hr0 : 0 ≤ rateR .SI n d eps :=
      (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
        (rho_elementary_comparisons n d eps hAllowed).1
    have hh0 : 0 ≤ rateH .SI n d eps := Real.sqrt_nonneg _
    have hsq : (rateH .SI n d eps)^2 = rateR .SI n d eps :=
      Real.sq_sqrt hr0
    have hlower' : scale * rateH .SI n d eps ≤ gap := hlower
    have hgapSq : scale^2 * rateR .SI n d eps ≤ gap^2 := by
      have h := mul_self_le_mul_self (mul_nonneg hs.le hh0) hlower'
      simpa only [← pow_two, mul_pow, hsq] using h
    have hr : min (scale^2/100) (scale/100) * rateR .SI n d eps ≤
        9*gap^2/128 * (97/100) := by
      have h := mul_le_mul_of_nonneg_right
        (min_le_left (scale^2/100) (scale/100)) hr0
      nlinarith [sq_nonneg gap]
    have hh : min (scale^2/100) (scale/100) * rateH .SI n d eps ≤
        3*gap/4 * (77/100) := by
      have h := mul_le_mul_of_nonneg_right
        (min_le_right (scale^2/100) (scale/100)) hh0
      nlinarith
    exact ⟨fun T => (ENNReal.ofReal_le_ofReal hr).trans (hdec.1 T),
      fun J hCov => (ENNReal.ofReal_le_ofReal hh).trans (hdec.2 J hCov)⟩
  obtain ⟨D, hD, cLarge, hcLarge, hLarge⟩ := hLarge
  let cSmall : ℝ := 1/(32768*(D : ℝ)^2)
  have hDpos : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hcSmall : 0 < cSmall := by dsimp [cSmall]; positivity
  refine ⟨min cLarge cSmall, lt_min hcLarge hcSmall, ?_⟩
  intro n d eps hAllowed S hIID hRandom Q hQ
  have hr0 : 0 ≤ rateR .SI n d eps :=
    (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
      (rho_elementary_comparisons n d eps hAllowed).1
  have hh0 : 0 ≤ rateH .SI n d eps := Real.sqrt_nonneg _
  by_cases hdD : d ≤ D
  · have hSmall := bounded_dimension_frontier_lower hRN_of_gate D n d eps hD hdD
      hAllowed S hIID hRandom Q hQ
    constructor
    · intro T
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_right cLarge cSmall) hr0)).trans (hSmall.1 T)
    · intro I hCov
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_right cLarge cSmall) hh0)).trans (hSmall.2 I hCov)
  · have hBig := hLarge n d eps hAllowed (by omega) S hIID hRandom Q hQ
    constructor
    · intro T
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLarge cSmall) hr0)).trans (hBig.1 T)
    · intro I hCov
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLarge cSmall) hh0)).trans (hBig.2 I hCov)



end CausalSmith.Stat.LdpOptvalueUniformFrontier
