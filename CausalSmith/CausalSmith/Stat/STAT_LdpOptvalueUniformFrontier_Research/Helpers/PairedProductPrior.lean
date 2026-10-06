module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.ContractionCalibration
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedTwoPoint

/-!
# Paired product-prior experiments

Signed preprocessing identifies the paired product-prior transcript experiment
with the causal symmetric experiment. Moment duality, target concentration and
adaptive contraction then supply the three ingredients for the paired converse.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier
variable {n d : ℕ}

/-- The paired finite law [depends measurably on its contrast coordinates](goal). -/
-- @node: measurable_pairedLaw_parameter
@[fun_prop] lemma measurable_pairedLaw_parameter :
    Measurable (pairedLaw : (Fin d → ℝ) → Measure (PairedSymbol d)) := by
  unfold pairedLaw
  first
  | fun_prop
  | apply measurable_atomLaw_weights
    intro v
    fun_prop

/-- The finite total-variation target is [measurable on the space of input laws](goal). -/
-- @node: measurable_tvFromUniform
@[fun_prop] lemma measurable_tvFromUniform :
    Measurable (tvFromUniform : Measure (PairedSymbol d) → ℝ) := by
  unfold tvFromUniform
  first
  | fun_prop
  | apply Measurable.const_mul
    apply Finset.measurable_sum
    intro v _
    exact continuous_abs.measurable.comp
      ((Measure.measurable_coe (measurableSet_singleton v)).ennreal_toReal.sub measurable_const)

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Pushing the product prior to paired laws preserves its scalar TV center](goal). -/
-- @node: pairedLaw_prior_target_mean
lemma pairedLaw_prior_target_mean (hd : 0 < d) (a : ℝ) (ha : a ≤ (1/2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (∫ p, tvFromUniform p ∂(productPrior d nu).map pairedLaw) =
      (∫ u, |u| ∂nu)/2 := by
  rw [integral_map measurable_pairedLaw_parameter.aemeasurable
    measurable_tvFromUniform.aestronglyMeasurable]
  calc
    _ = ∫ theta, signedNorm theta/2 ∂productPrior d nu := by
      apply integral_congr_ae
      filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
      exact tvFromUniform_pairedLaw theta htheta hd
    _ = _ := productPrior_halfNorm_mean d hd a nu hnu

/-- [Escape probabilities transfer to law-space priors with the same radius and center](goal). -/
-- @node: pairedLaw_prior_target_escape
lemma pairedLaw_prior_target_escape (nu : Measure ℝ) (r v : ℝ) :
    ((productPrior d nu).map pairedLaw) {p | r < |tvFromUniform p-v|} =
      (productPrior d nu) {theta | r < |tvFromUniform (pairedLaw theta)-v|} := by
  apply Measure.map_apply measurable_pairedLaw_parameter
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_tvFromUniform.sub measurable_const))

/-- Assume [dimension at least two](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [Averaging signed preprocessing over a supported product prior preserves the joint public-seed and transcript law, including sequential histories](goal). -/
-- @node: paired_productPrior_transcript_eq
lemma paired_productPrior_transcript_eq
    (K : LocalProtocol n (PairedSymbol d)) (hd : 2 ≤ d)
    (a : ℝ) (ha : a ≤ (1 / 2 : ℝ)) (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (productPrior d nu).bind (fun theta =>
      canonicalSeedTranscriptLaw K (pairedLaw theta)) =
      mixtureLaw (canonicalScheme n d) (pulledProtocol K) nu := by
  unfold mixtureLaw
  apply Measure.bind_congr_right
  filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
  have h := pulledProtocol_decisionLaw (canonicalScheme n d) canonicalScheme_iidPeople
    canonicalScheme_independentRandomness hd K theta htheta
  simp only [canonicalSeedTranscriptLaw, seedTranscriptLaw, h]
  rfl

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hK), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [amplitude between zero and one half](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), and [the stated hmatch condition](hyp:hmatch). [Arbitrary paired sequential protocols obey the same higher-order product-prior contraction and exact above-sample moment cancellation as the causal experiment](goal). -/
-- @node: paired_productPrior_contraction
lemma paired_productPrior_contraction (hRN : MeasurableKernelRadonNikodym)
    (K : LocalProtocol n (PairedSymbol d)) (eps : ℝ)
    (hK : SequentialClass K eps) (hAllowed : Allowed n d eps)
    (a : ℝ) (ha : a ∈ Set.Ioc 0 (1 / 2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hmatch : MatchingMoments k nu0 nu1) :
    (k ≤ n → Causalean.Stat.tvDist
      ((productPrior d nu0).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
      ((productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
        min 1 (d * a^k * Real.sqrt (Nat.choose n k) * (derivativeScale d eps)^k)) ∧
    (n < k →
      (productPrior d nu0).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) =
      (productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  rw [paired_productPrior_transcript_eq K hAllowed.2.1 a ha.2 nu0 hnu0,
    paired_productPrior_transcript_eq K hAllowed.2.1 a ha.2 nu1 hnu1]
  have h := (adaptive_moment_contraction hRN (canonicalScheme n d) canonicalScheme_iidPeople
    canonicalScheme_independentRandomness (pulledProtocol K) eps
    ((signed_protocol_classes eps).2 K |>.1 hK) hAllowed).2
      a ha nu0 nu1 hnu0 hnu1 k hk hmatch
  exact ⟨h.1, h.2.1⟩

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hK), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [amplitude between zero and one half](hyp:ha), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), [the stated hk condition](hyp:hk), and [the stated hmatch condition](hyp:hmatch). [The paired adaptive contraction has the geometric resource form of equation (15), for every matching order. Orders beyond the sample size use exact mixture cancellation rather than an artificial binomial estimate](goal). -/
-- @node: paired_productPrior_geometric_contraction
lemma paired_productPrior_geometric_contraction (hRN : MeasurableKernelRadonNikodym)
    (K : LocalProtocol n (PairedSymbol d)) (eps : ℝ)
    (hK : SequentialClass K eps) (hAllowed : Allowed n d eps)
    (a : ℝ) (ha : a ∈ Set.Ioc 0 (1/2 : ℝ))
    (nu0 nu1 : Measure ℝ) (hnu0 : AmplitudePrior a nu0) (hnu1 : AmplitudePrior a nu1)
    (k : ℕ) (hk : 1 ≤ k) (hmatch : MatchingMoments k nu0 nu1) :
    Causalean.Stat.tvDist
      ((productPrior d nu0).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
      ((productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
        min 1 ((d : ℝ)*(a*Real.sqrt (Real.exp 1*n/k)*(eps/d))^k) := by
  have hcontract := paired_productPrior_contraction hRN K eps hK hAllowed
    a ha nu0 nu1 hnu0 hnu1 k hk hmatch
  by_cases hkn : k ≤ n
  · exact (hcontract.1 hkn).trans (min_le_min_left 1
      (contraction_coefficient_geometric_le n d k
        (by have := hAllowed.2.1; omega) (by omega) eps a hAllowed.2.2 ha.1.le))
  · rw [hcontract.2 (by omega)]
    have hzero : Causalean.Stat.tvDist
        ((productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
        ((productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) = 0 := by
      simp [Causalean.Stat.tvDist]
    rw [hzero]
    apply le_min (by norm_num)
    exact mul_nonneg (Nat.cast_nonneg d) (pow_nonneg
      (mul_nonneg (mul_nonneg ha.1.le (Real.sqrt_nonneg _))
        (div_nonneg hAllowed.2.2.1.le (Nat.cast_nonneg d))) k)

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [sequential local privacy of the protocol](hyp:hK), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [the stated hnu0 condition](hyp:hnu0), [the stated hnu1 condition](hyp:hnu1), and [the stated hmatch condition](hyp:hmatch). [At the prescribed frontier amplitude and matching degree, every paired sequential protocol has product-prior transcript TV at most one hundredth. Matching beyond the sample horizon uses exact cancellation](goal). -/
-- @node: paired_productPrior_resource_contraction
lemma paired_productPrior_resource_contraction (hRN : MeasurableKernelRadonNikodym)
    (K : LocalProtocol n (PairedSymbol d)) (eps : ℝ)
    (hK : SequentialClass K eps) (hAllowed : Allowed n d eps)
    (nu0 nu1 : Measure ℝ)
    (hnu0 : AmplitudePrior (frontierResources n d eps).converseAmp nu0)
    (hnu1 : AmplitudePrior (frontierResources n d eps).converseAmp nu1)
    (hmatch : MatchingMoments (frontierResources n d eps).converseDegree nu0 nu1) :
    Causalean.Stat.tvDist
      ((productPrior d nu0).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
      ((productPrior d nu1).bind (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
        (1/100 : ℝ) := by
  have hk : 1 ≤ (frontierResources n d eps).converseDegree := by
    have h := (frontier_converse_degree_domain n d eps hAllowed).1
    omega
  have hgeo := paired_productPrior_geometric_contraction hRN K eps hK hAllowed
    _ (frontier_converse_amplitude_domain n d eps hAllowed) nu0 nu1 hnu0 hnu1
    _ hk hmatch
  exact hgeo.trans ((min_le_right _ _).trans
    (frontier_converse_geometric_small n d eps hAllowed))

/-- Assume [positive dimension](hyp:hd), [the stated ha condition](hyp:ha), and [the stated hnu condition](hyp:hnu). [The paired TV prior center is half the scalar absolute moment](goal). -/
-- @node: productPrior_paired_tv_mean
lemma productPrior_paired_tv_mean (hd : 0 < d) (a : ℝ) (ha : a ≤ (1 / 2 : ℝ))
    (nu : Measure ℝ) (hnu : AmplitudePrior a nu) :
    (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu) =
      (∫ u, |u| ∂nu) / 2 := by
  calc
    _ = ∫ theta, signedNorm theta / 2 ∂productPrior d nu := by
      apply integral_congr_ae
      filter_upwards [amplitude_productPrior_ae_cube a ha nu hnu] with theta htheta
      exact tvFromUniform_pairedLaw theta htheta hd
    _ = _ := productPrior_halfNorm_mean d hd a nu hnu

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [The dual product priors simultaneously separate and concentrate the paired TV target and contract its private transcript experiment. This leaves the public amplitude, degree and dimension-cutoff calculations to the frontier assembly](goal). -/
-- @node: paired_dual_product_priors_of_gate
lemma paired_dual_product_priors_of_gate
    (hRN : MeasurableKernelRadonNikodym) (hDual : CaiLowMomentDuality)
    (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∀ (n d Kdeg : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
      0 < Kdeg → Even Kdeg → ∀ a : ℝ, a ∈ Set.Ioc 0 (1 / 2 : ℝ) →
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (Kdeg+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ b*a/Kdeg ≤ gap ∧
          (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu1) -
            (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu0) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            (productPrior d nu) {theta | gap/8 ≤
              |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} ≤
                ENNReal.ofReal (16*(Kdeg : ℝ)^2/(b^2*d))) ∧
          (Kdeg+1 ≤ n → Causalean.Stat.tvDist
            ((productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
            ((productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
              min 1 (d * a^(Kdeg+1) * Real.sqrt (Nat.choose n (Kdeg+1)) *
                (derivativeScale d eps)^(Kdeg+1))) ∧
          (n < Kdeg+1 →
            (productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) =
            (productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  obtain ⟨b, hb, hpriors⟩ := dual_product_priors_target_concentration_of_gate hDual hBernstein
  refine ⟨b, hb, ?_⟩
  intro n d Kdeg eps hAllowed K hK hdegree heven a ha
  have hd : 0 < d := by have := hAllowed.2.1; omega
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower, hmean, hescape⟩ :=
    hpriors d Kdeg hd hdegree heven a ha.1
  have hmeanTV :
      (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu1) -
        (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu0) = gap := by
    rw [productPrior_halfNorm_mean d hd a nu1 hnu1,
      productPrior_halfNorm_mean d hd a nu0 hnu0] at hmean
    rw [productPrior_paired_tv_mean hd a ha.2 nu1 hnu1,
      productPrior_paired_tv_mean hd a ha.2 nu0 hnu0]
    exact hmean
  have hcontract := paired_productPrior_contraction hRN K eps hK hAllowed
    a ha nu0 nu1 hnu0 hnu1 (Kdeg+1) (by omega) hmatch
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower, hmeanTV, ?_,
    hcontract.1, hcontract.2⟩
  intro nu hnu
  have hamp : AmplitudePrior a nu := by
    rcases hnu with rfl | hnu
    · exact hnu0
    · have heq : nu = nu1 := Set.mem_singleton_iff.mp hnu
      simpa [heq] using hnu1
  have heq : (productPrior d nu) {theta | gap/8 ≤
      |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} =
      (productPrior d nu) {theta | gap/8 ≤
        |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|} := by
    apply measure_congr
    filter_upwards [amplitude_productPrior_ae_cube a ha.2 nu hamp] with theta htheta
    change (gap/8 ≤ |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|) =
      (gap/8 ≤ |signedNorm theta/2 - (∫ u, |u| ∂nu)/2|)
    rw [tvFromUniform_pairedLaw theta htheta hd]
  rw [heq]
  exact hescape nu hnu

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [At the exact public resource choices, dual priors have a positive paired TV center gap at least a universal multiple of the square-root rate. Their concentration and transcript-contraction bounds retain the explicit degree, so subsequent dimension-cutoff calculations use the same priors](goal). -/
-- @node: paired_resource_product_priors_of_gate
lemma paired_resource_product_priors_of_gate
    (hRN : MeasurableKernelRadonNikodym) (hDual : CaiLowMomentDuality)
    (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
      let a := (frontierResources n d eps).converseAmp
      let q := (frontierResources n d eps).converseDegree - 1
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (q+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ (b/3400)*rateH .SI n d eps ≤ gap ∧
          (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu1) -
            (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu0) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            (productPrior d nu) {theta | gap/8 ≤
              |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} ≤
                ENNReal.ofReal (16*(q : ℝ)^2/(b^2*d))) ∧
          (q+1 ≤ n → Causalean.Stat.tvDist
            ((productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
            ((productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
              min 1 (d * a^(q+1) * Real.sqrt (Nat.choose n (q+1)) *
                (derivativeScale d eps)^(q+1))) ∧
          (n < q+1 →
            (productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) =
            (productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  obtain ⟨b, hb, hpriors⟩ := paired_dual_product_priors_of_gate hRN hDual hBernstein
  refine ⟨b, hb, ?_⟩
  intro n d eps hAllowed K hK
  obtain ⟨hq, heven⟩ := frontier_converse_degree_domain n d eps hAllowed
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hgaplower, hmean,
      hescape, hcontract, hcancel⟩ :=
    hpriors n d _ eps hAllowed K hK hq heven _
      (frontier_converse_amplitude_domain n d eps hAllowed)
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, ?_, hmean,
    hescape, hcontract, hcancel⟩
  calc
    (b/3400)*rateH .SI n d eps = b*((1/3400)*rateH .SI n d eps) := by ring
    _ ≤ b*((frontierResources n d eps).converseAmp /
        (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (frontier_converse_gap_rate n d eps hAllowed) hb.le
    _ = b*(frontierResources n d eps).converseAmp /
        (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ) := by ring
    _ ≤ gap := hgaplower

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [The prescribed paired priors simultaneously achieve the frontier gap, matching moments, adaptive transcript contraction and escape probability at most one hundredth above one universal dimension cutoff](goal). -/
-- @node: paired_concentrated_resource_priors_of_gate
lemma paired_concentrated_resource_priors_of_gate
    (hRN : MeasurableKernelRadonNikodym) (hDual : CaiLowMomentDuality)
    (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D < d →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
      let a := (frontierResources n d eps).converseAmp
      let q := (frontierResources n d eps).converseDegree - 1
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (q+1) nu0 nu1 ∧
        ∃ gap : ℝ, 0 < gap ∧ (b/3400)*rateH .SI n d eps ≤ gap ∧
          (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu1) -
            (∫ theta, tvFromUniform (pairedLaw theta) ∂productPrior d nu0) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            (productPrior d nu) {theta | gap/8 ≤
              |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} ≤
                ENNReal.ofReal (1/100 : ℝ)) ∧
          (q+1 ≤ n → Causalean.Stat.tvDist
            ((productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
            ((productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
              min 1 (d * a^(q+1) * Real.sqrt (Nat.choose n (q+1)) *
                (derivativeScale d eps)^(q+1))) ∧
          (n < q+1 →
            (productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) =
            (productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  obtain ⟨b, hb, hpriors⟩ := paired_resource_product_priors_of_gate hRN hDual hBernstein
  obtain ⟨D, hD, hcutoff⟩ := frontier_converse_concentration_cutoff b hb
  refine ⟨b, hb, D, hD, ?_⟩
  intro n d eps hAllowed hdim K hK
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hgaplower,
      hmean, hescape, hcontract, hcancel⟩ := hpriors n d eps hAllowed K hK
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hgaplower,
    hmean, ?_, hcontract, hcancel⟩
  intro nu hnu
  exact (hescape nu hnu).trans
    (ENNReal.ofReal_le_ofReal (hcutoff n d eps hAllowed hdim))

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [The prescribed concentrated priors, pushed to paired input laws, have the same center gap and the strict real escape bounds used by the decision reduction. The underlying scalar priors are retained for transcript contraction](goal). -/
-- @node: paired_lawspace_resource_priors_of_gate
lemma paired_lawspace_resource_priors_of_gate
    (hRN : MeasurableKernelRadonNikodym) (hDual : CaiLowMomentDuality)
    (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ b : ℝ, 0 < b ∧ ∃ D : ℕ, 2 ≤ D ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D < d →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
      let a := (frontierResources n d eps).converseAmp
      let q := (frontierResources n d eps).converseDegree - 1
      ∃ nu0 nu1 : Measure ℝ, AmplitudePrior a nu0 ∧ AmplitudePrior a nu1 ∧
        MatchingMoments (q+1) nu0 nu1 ∧
        let pi0 := (productPrior d nu0).map pairedLaw
        let pi1 := (productPrior d nu1).map pairedLaw
        IsProbabilityMeasure pi0 ∧ IsProbabilityMeasure pi1 ∧
        ∃ gap : ℝ, 0 < gap ∧ (b/3400)*rateH .SI n d eps ≤ gap ∧
          (∫ p, tvFromUniform p ∂pi1) - (∫ p, tvFromUniform p ∂pi0) = gap ∧
          (∀ nu ∈ ({nu0, nu1} : Set (Measure ℝ)),
            ((productPrior d nu).map pairedLaw).real
              {p | gap/8 < |tvFromUniform p - (∫ u, |u| ∂nu)/2|} ≤ (1/100 : ℝ)) ∧
          (q+1 ≤ n → Causalean.Stat.tvDist
            ((productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)))
            ((productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) ≤
              min 1 (d * a^(q+1) * Real.sqrt (Nat.choose n (q+1)) *
                (derivativeScale d eps)^(q+1))) ∧
          (n < q+1 →
            (productPrior d nu0).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta)) =
            (productPrior d nu1).bind
              (fun theta => canonicalSeedTranscriptLaw K (pairedLaw theta))) := by
  obtain ⟨b, hb, D, hD, hpriors⟩ :=
    paired_concentrated_resource_priors_of_gate hRN hDual hBernstein
  refine ⟨b, hb, D, hD, ?_⟩
  intro n d eps hAllowed hdim K hK
  obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, gap, hgap, hlower,
      hmean, hescape, hcontract, hcancel⟩ := hpriors n d eps hAllowed hdim K hK
  have ha := (frontier_converse_amplitude_domain n d eps hAllowed).2
  have hd : 0 < d := by have := hAllowed.2.1; omega
  letI := hnu0.1
  letI := hnu1.1
  haveI : IsProbabilityMeasure (productPrior d nu0) := by unfold productPrior; infer_instance
  haveI : IsProbabilityMeasure (productPrior d nu1) := by unfold productPrior; infer_instance
  refine ⟨nu0, nu1, hnu0, hnu1, hmatch,
    Measure.isProbabilityMeasure_map measurable_pairedLaw_parameter.aemeasurable,
    Measure.isProbabilityMeasure_map measurable_pairedLaw_parameter.aemeasurable,
    gap, hgap, hlower, ?_, ?_, hcontract, hcancel⟩
  · rw [pairedLaw_prior_target_mean hd _ ha nu1 hnu1,
      pairedLaw_prior_target_mean hd _ ha nu0 hnu0]
    rw [productPrior_paired_tv_mean hd _ ha nu1 hnu1,
      productPrior_paired_tv_mean hd _ ha nu0 hnu0] at hmean
    exact hmean
  · intro nu hnu
    have hstrict : (productPrior d nu)
        {theta | gap/8 < |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} ≤
        ENNReal.ofReal (1/100 : ℝ) :=
      (measure_mono (show
        {theta : Fin d → ℝ | gap/8 < |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|} ⊆
          {theta | gap/8 ≤ |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|}
        from by
          intro theta ht
          change gap/8 < |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2| at ht
          change gap/8 ≤ |tvFromUniform (pairedLaw theta) - (∫ u, |u| ∂nu)/2|
          exact ht.le)).trans (hescape nu hnu)
    unfold Measure.real
    rw [pairedLaw_prior_target_escape]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hstrict).trans_eq
      (ENNReal.toReal_ofReal (by norm_num))

end CausalSmith.Stat.LdpOptvalueUniformFrontier
