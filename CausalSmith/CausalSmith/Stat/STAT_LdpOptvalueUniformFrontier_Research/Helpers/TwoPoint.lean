module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Mixture
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.SeparatedMixtures

/-!
# Helpers/TwoPoint

Finite original-record private value frontiers: Helpers/TwoPoint.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


variable {n d : ℕ}

/-- [A degenerate coordinate prior fixes the entire parameter vector](goal). -/
-- @node: productPrior_dirac_ae
lemma productPrior_dirac_ae (u : ℝ) :
    ∀ᵐ theta ∂productPrior d (Measure.dirac u), theta = fun _ => u := by
  have hall : ∀ᵐ theta ∂productPrior d (Measure.dirac u), ∀ j, theta j = u :=
    Filter.eventually_all.mpr (fun j =>
      (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin d => Measure.dirac u) (i := j)).eventually
      (show ∀ᵐ x ∂Measure.dirac u, x = u by simp))
  filter_upwards [hall] with theta htheta
  exact funext htheta

/-- [A point coordinate prior gives the corresponding unmixed experiment](goal). -/
-- @node: mixtureLaw_dirac
lemma mixtureLaw_dirac (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (u : ℝ) : mixtureLaw S Q (Measure.dirac u) =
      seedTranscriptLaw S Q (symmetricLaw (fun _ => u)) := by
  unfold mixtureLaw
  have h := productPrior_dirac_ae (d := d) u
  have heq : (fun theta => seedTranscriptLaw S Q (symmetricLaw theta)) =ᵐ[
      productPrior d (Measure.dirac u)]
      (fun _ => seedTranscriptLaw S Q (symmetricLaw (fun _ => u))) :=
    h.mono (fun theta htheta => by rw [htheta])
  rw [Measure.bind_congr_right heq]
  haveI : IsProbabilityMeasure (productPrior d (Measure.dirac u)) := by
    unfold productPrior; infer_instance
  simp

/-- [Finite population measures are separated by their measurable atom masses](goal). -/
-- @node: measurableSingleton_fullRecordMeasure
instance measurableSingleton_fullRecordMeasure :
    MeasurableSingletonClass (Measure (FullRecord d)) where
  measurableSet_singleton P := by
    have heq : ({P} : Set (Measure (FullRecord d))) =
        ⋂ x : FullRecord d, {μ | μ {x} = P {x}} := by
      ext μ
      simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      exact ⟨fun h x => by rw [h], fun h => Measure.ext_of_singleton h⟩
    rw [heq]
    exact MeasurableSet.iInter (fun x => measurableSet_eq_fun
      (Measure.measurable_coe (measurableSet_singleton x)) measurable_const)

/-- [A law prior at a single population has no mixing effect](goal). -/
-- @node: causal_dirac_bind
lemma causal_dirac_bind (S : SamplingScheme n d) (Q : LocalProtocol n (ObsRecord d))
    (P : Measure (FullRecord d)) :
    (Measure.dirac P).bind (decisionLaw S Q) = decisionLaw S Q P := by
  rw [Measure.bind_congr_right (ae_eq_dirac (decisionLaw S Q))]
  change (Measure.dirac P).bind (fun _ => decisionLaw S Q P) = _
  simp

/-- Assume [positive dimension](hyp:hd). [The constant contrast has its absolute value as its averaged signed norm](goal). -/
-- @node: signedNorm_constant
lemma signedNorm_constant (u : ℝ) (hd : 0 < d) :
    signedNorm (fun _ : Fin d => u) = |u| := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
  simp [signedNorm, hdR]

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [sequential local privacy of the protocol](hyp:hQ), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), and [amplitude between zero and one half](hyp:ha). [The first moment-matching contraction controls the two constant-contrast experiments](goal). -/
-- @node: constant_contrast_tv_bound
lemma constant_contrast_tv_bound (hRN : MeasurableKernelRadonNikodym)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (eps a : ℝ) (hQ : SequentialClass Q eps)
    (hAllowed : Allowed n d eps) (ha : a ∈ Set.Ioc 0 (1/2 : ℝ)) :
    Causalean.Stat.tvDist (seedTranscriptLaw S Q (symmetricLaw (fun _ => 0)))
      (seedTranscriptLaw S Q (symmetricLaw (fun _ => a))) ≤
      a * Real.sqrt n * eps := by
  have hprior (u : ℝ) (hu : u ∈ Set.Icc (-a) a) :
      AmplitudePrior a (Measure.dirac u) := by
    refine ⟨inferInstance, ?_⟩
    simp [Measure.dirac_apply', hu]
  have hmatch : MatchingMoments 1 (Measure.dirac (0 : ℝ)) (Measure.dirac a) := by
    intro q hq
    have hq0 : q = 0 := by omega
    subst q
    simp
  have htv := ((adaptive_moment_contraction hRN S hIID hRandom Q eps hQ hAllowed).2
    a ha (Measure.dirac 0) (Measure.dirac a)
    (hprior 0 ⟨by linarith [ha.1], ha.1.le⟩)
    (hprior a ⟨by linarith [ha.1], le_rfl⟩) 1 le_rfl hmatch).1 (by
      have := hAllowed.1; omega)
  rw [mixtureLaw_dirac, mixtureLaw_dirac] at htv
  have hexp : Real.exp eps - 1 ≤ 2*eps := by
    have h := Real.abs_exp_sub_one_le (show |eps| ≤ 1 by
      rw [abs_of_pos hAllowed.2.2.1]; exact hAllowed.2.2.2)
    rw [abs_of_pos hAllowed.2.2.1] at h
    exact (le_abs_self _).trans h
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by
    have := hAllowed.2.1; omega)
  have heq : (d : ℝ) * a^1 * Real.sqrt (Nat.choose n 1) *
      (derivativeScale d eps)^1 = a * Real.sqrt n * (Real.exp eps - 1)/2 := by
    simp only [pow_one, Nat.choose_one_right, derivativeScale]
    field_simp
  refine (htv.trans (min_le_right _ _)).trans ?_
  rw [heq]
  have hmul := mul_le_mul_of_nonneg_left hexp
    (mul_nonneg ha.1.le (Real.sqrt_nonneg (n : ℝ)))
  nlinarith

/-- Assume [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), [amplitude between zero and one half](hyp:ha), [positive dimension](hyp:hd), and [the stated total-variation bound](hyp:hTV). [Point priors turn transcript closeness into both per-decision lower bounds](goal). -/
-- @node: constant_contrast_decision_lower
lemma constant_contrast_decision_lower
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (a : ℝ) (ha : a ∈ Set.Ioc 0 (1/2 : ℝ))
    (hd : 0 < d)
    (hTV : Causalean.Stat.tvDist
      (seedTranscriptLaw S Q (symmetricLaw (fun _ => 0)))
      (seedTranscriptLaw S Q (symmetricLaw (fun _ => a))) ≤ 1/8) :
    (∀ T : Estimator Q, ENNReal.ofReal (63*a^2/4096) ≤
      ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
        squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
    (∀ I : IntervalDecision Q (1/4) (3/4),
      (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
      ENNReal.ofReal (81*a/320) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I) := by
  have hcube0 : (fun _ : Fin d => (0 : ℝ)) ∈ parameterCube d := by
    intro j; constructor <;> norm_num
  have hcubea : (fun _ : Fin d => a) ∈ parameterCube d := by
    intro j; exact ⟨by linarith [ha.1], ha.2⟩
  haveI := symmetricLaw_probability _ hcube0 hd
  haveI := symmetricLaw_probability _ hcubea hd
  have hmodel0 := symmetricLaw_causalModel _ hcube0 hd
  have hmodela := symmetricLaw_causalModel _ hcubea hd
  have hmem0 : symmetricLaw (fun _ : Fin d => (0 : ℝ)) ∈ causalClass d :=
    ⟨inferInstance, hmodel0⟩
  have hmema : symmetricLaw (fun _ : Fin d => a) ∈ causalClass d :=
    ⟨inferInstance, hmodela⟩
  have hv0 : value (symmetricLaw (fun _ : Fin d => (0 : ℝ))) = 1/2 := by
    rw [symmetricLaw_value _ hcube0 hd, signedNorm_constant _ hd]
    norm_num
  have hva : value (symmetricLaw (fun _ : Fin d => a)) = 1/2+a/2 := by
    rw [symmetricLaw_value _ hcubea hd, signedNorm_constant _ hd, abs_of_pos ha.1]
  have hsupport0 : (Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ))))
      (causalClass d)ᶜ = 0 := by simp [hmem0]
  have hsupporta : (Measure.dirac (symmetricLaw (fun _ : Fin d => a)))
      (causalClass d)ᶜ = 0 := by simp [hmema]
  have hprob0 : IsProbabilityMeasure
      ((Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ)))).bind (decisionLaw S Q)) := by
    rw [causal_dirac_bind]
    exact sampling_decisionLaw_probability S hIID hRandom Q _ hmodel0
  have hproba : IsProbabilityMeasure
      ((Measure.dirac (symmetricLaw (fun _ : Fin d => a))).bind (decisionLaw S Q)) := by
    rw [causal_dirac_bind]
    exact sampling_decisionLaw_probability S hIID hRandom Q _ hmodela
  have hescape0 : (Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ)))).real
      {P | ((1/2+a/2)-1/2)/8 < |value P - 1/2|} ≤ 0 := by
    have hnot : symmetricLaw (fun _ : Fin d => (0 : ℝ)) ∉
        {P | ((1/2+a/2)-1/2)/8 < |value P - 1/2|} := by
      simp only [Set.mem_ofPred_eq, hv0, sub_self, abs_zero]
      linarith [ha.1]
    simp only [Measure.real, Measure.dirac_apply, Set.indicator_of_notMem hnot,
      ENNReal.toReal_zero, le_refl]
  have hescapea : (Measure.dirac (symmetricLaw (fun _ : Fin d => a))).real
      {P | ((1/2+a/2)-1/2)/8 < |value P - (1/2+a/2)|} ≤ 0 := by
    have hnot : symmetricLaw (fun _ : Fin d => a) ∉
        {P | ((1/2+a/2)-1/2)/8 < |value P - (1/2+a/2)|} := by
      simp only [Set.mem_ofPred_eq, hva, sub_self, abs_zero]
      linarith [ha.1]
    simp only [Measure.real, Measure.dirac_apply, Set.indicator_of_notMem hnot,
      ENNReal.toReal_zero, le_refl]
  have htv : Causalean.Stat.tvDist
      (((Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ)))).bind
        (decisionLaw S Q)).map (fun w => (w.2.1,w.1)))
      (((Measure.dirac (symmetricLaw (fun _ : Fin d => a))).bind
        (decisionLaw S Q)).map (fun w => (w.2.1,w.1))) ≤ 1/8 := by
    simpa only [causal_dirac_bind, seedTranscriptLaw] using hTV
  have hsep := separated_value_mixtures S hIID hRandom Q
    (Measure.dirac (symmetricLaw (fun _ : Fin d => (0 : ℝ))))
    (Measure.dirac (symmetricLaw (fun _ : Fin d => a)))
    hsupport0 hsupporta hprob0 hproba (1/2) (1/2+a/2) 0 (1/8)
    (by linarith [ha.1]) hescape0 hescapea htv
  have hr : 9*((1/2+a/2)-1/2)^2/128 * max 0 (1-(1/8 : ℝ)-2*0) =
      63*a^2/4096 := by norm_num; ring
  have hl : 3*((1/2+a/2)-1/2)/4 * max 0 ((0.80 : ℝ)-2*0-1/8) =
      81*a/320 := by norm_num; ring
  simpa only [hr, hl] using hsep

/-- Assume [the stated hs condition](hyp:hs). [Squaring the truncated reciprocal gives the truncated inverse information](goal). -/
-- @node: min_one_reciprocal_sq
lemma min_one_reciprocal_sq (s : ℝ) (hs : 0 < s) :
    (min 1 (1/s))^2 = min 1 (1/s^2) := by
  by_cases h : s ≤ 1
  · have hi : 1 ≤ 1/s := (le_div_iff₀ hs).mpr (by linarith)
    have hi2 : 1 ≤ 1/s^2 := (le_div_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith)
    rw [min_eq_left hi, min_eq_left hi2]
    norm_num
  · have hi : 1/s ≤ 1 := (div_le_iff₀ hs).mpr (by linarith)
    have hi2 : 1/s^2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hs)).mpr (by nlinarith)
    rw [min_eq_right hi, min_eq_right hi2, div_pow, one_pow]

/-- Assume [the stated hn condition](hyp:hn) and [a positive privacy budget](hyp:heps). [The roadmap's amplitude obeys its support, privacy, and rate calibration requirements](goal). -/
-- @node: two_point_amplitude_calibration
lemma two_point_amplitude_calibration (n : ℕ) (eps : ℝ) (hn : 0 < n) (heps : 0 < eps) :
    let a := min 1 (1/(Real.sqrt n*eps))/8
    a ∈ Set.Ioc 0 (1/2 : ℝ) ∧ a*Real.sqrt n*eps ≤ 1/8 ∧
    (1/8192 : ℝ)*min 1 (1/(n*eps^2)) ≤ 63*a^2/4096 ∧
    (1/8192 : ℝ)*min 1 (1/(Real.sqrt n*eps)) ≤ 81*a/320 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n*eps := mul_pos (Real.sqrt_pos.mpr hnR) heps
  have hmin : 0 < min 1 (1/(Real.sqrt n*eps)) := lt_min (by norm_num) (by positivity)
  have hinfo : (Real.sqrt n*eps)^2 = n*eps^2 := by
    rw [mul_pow, Real.sq_sqrt hnR.le]
  have hsq := min_one_reciprocal_sq (Real.sqrt n*eps) hs
  rw [hinfo] at hsq
  dsimp only
  refine ⟨⟨by positivity, by linarith [min_le_left 1 (1/(Real.sqrt n*eps))]⟩, ?_, ?_, ?_⟩
  · have hprod := mul_le_mul_of_nonneg_right
      (min_le_right 1 (1/(Real.sqrt n*eps))) hs.le
    rw [one_div_mul_cancel hs.ne'] at hprod
    nlinarith
  · have hnonneg : 0 ≤ min 1 (1/(n*eps^2)) := by positivity
    nlinarith [hsq]
  · nlinarith

/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [an admissible sample size, dimension, and privacy budget](hyp:hAllowed), [independent and identically distributed participant records](hyp:hIID), [independent protocol randomness](hyp:hRandom), and [sequential local privacy of the protocol](hyp:hQ). [The two-point converse holds before taking either minimax infimum](goal). -/
-- @node: dimension_free_private_two_point_decisions
lemma dimension_free_private_two_point_decisions (hRN : MeasurableKernelRadonNikodym)
    (n d : ℕ) (eps : ℝ) (hAllowed : Allowed n d eps)
    (S : SamplingScheme n d) (hIID : IidPeople S) (hRandom : IndependentRandomness S)
    (Q : LocalProtocol n (ObsRecord d)) (hQ : SequentialClass Q eps) :
    (∀ T : Estimator Q, ENNReal.ofReal ((1/8192 : ℝ)*min 1 (1/(n*eps^2))) ≤
      ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
        squaredRisk (decisionLaw S Q P.1) T (value P.1)) ∧
    (∀ I : IntervalDecision Q (1/4) (3/4),
      (∀ P ∈ causalClass d, (0.90 : ℝ) ≤ coverage (decisionLaw S Q P) I (value P)) →
      ENNReal.ofReal ((1/8192 : ℝ)*min 1 (1/(Real.sqrt n*eps))) ≤
        ⨆ P : {P : Measure (FullRecord d) // P ∈ causalClass d},
          expectedLength (decisionLaw S Q P.1) I) := by
  let a := min 1 (1/(Real.sqrt n*eps))/8
  obtain ⟨ha, hsmall, hr, hl⟩ := two_point_amplitude_calibration n eps
    (by have := hAllowed.1; omega) hAllowed.2.2.1
  have hd : 0 < d := by have := hAllowed.2.1; omega
  have hTV := (constant_contrast_tv_bound hRN S hIID hRandom Q eps a
      hQ hAllowed ha).trans hsmall
  have hsep := constant_contrast_decision_lower S hIID hRandom Q a ha hd hTV
  exact ⟨fun T => (ENNReal.ofReal_le_ofReal hr).trans (hsep.1 T),
      fun I hCov => (ENNReal.ofReal_le_ofReal hl).trans (hsep.2 I hCov)⟩

-- @node: lem:dimension-free-private-two-point
/-- Assuming [measurable kernel Radon--Nikodym derivatives](hyp:hRN_of_gate), universal private
two-point alternatives give [lower bounds for both minimax decision values](goal). -/
lemma dimension_free_private_two_point (hRN_of_gate : MeasurableKernelRadonNikodym) :
    ∃ c1 : ℝ, 0 < c1 ∧ ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ (S : SamplingScheme n d), IidPeople S → IndependentRandomness S →
      ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c1 * min 1 (1/(n*eps^2))) ≤ minimaxRisk S C eps ∧
        ENNReal.ofReal (c1 * min 1 (1/(Real.sqrt n*eps))) ≤ honestLength S C eps := by
  refine ⟨1/8192, by norm_num, ?_⟩
  intro n d eps hAllowed S hIID hRandom C
  have hdec (Q : LocalProtocol n (ObsRecord d)) (hQ : protocolClass C Q eps) :=
    dimension_free_private_two_point_decisions hRN_of_gate n d eps hAllowed S hIID hRandom Q
      (by cases C with
          | NI => exact NoninteractiveClass.toSequentialClass Q eps hQ
          | SI => exact hQ)
  constructor
  · unfold minimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hdec e.1.1 e.1.2).1 e.2
  · unfold honestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hdec e.1.1 e.1.2).2 e.2.1 e.2.2


end CausalSmith.Stat.LdpOptvalueUniformFrontier
