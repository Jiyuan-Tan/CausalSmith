module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.PairedDecisionCompletion
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.TVUpper
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.TUniformPrivateValueFrontiers

/-!
# TPairedUniformTvFrontier

Finite original-record private value frontiers: TPairedUniformTvFrontier.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace CausalSmith.Stat.LdpOptvalueUniformFrontier


/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN_of_gate), [the Cai–Low moment-duality theorem](hyp:hDual_of_gate), and [the Bernstein absolute-approximation limit](hyp:hBernstein_of_gate). [Per-decision paired converse for reuse under model inclusion](goal). -/
-- @node: paired_converse_of_gate
lemma paired_converse_of_gate (hRN_of_gate : MeasurableKernelRadonNikodym)
    (hDual_of_gate : CaiLowMomentDuality) (hBernstein_of_gate :
      BernsteinAbsoluteApproximationLimit) :
    ∃ c : ℝ, 0 < c ∧ -- @realizes c(universal positive lower constant)
      ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
        (∀ T : Estimator K, ENNReal.ofReal (c*rateR .SI n d eps) ≤
          ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
            squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
        (∀ J : IntervalDecision K 0 1,
          (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
            (tvFromUniform p)) →
          ENNReal.ofReal (c*rateH .SI n d eps) ≤
            ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
              expectedLength (canonicalDecisionLaw K p.1) J) := by
  -- Concentrated product priors give the converse above a universal dimension cutoff.
  have hLarge :
    ∃ D : ℕ, 2 ≤ D ∧ ∃ c : ℝ, 0 < c ∧ -- @realizes c(universal positive lower constant)
      ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → D < d →
      ∀ K : LocalProtocol n (PairedSymbol d), SequentialClass K eps →
        (∀ T : Estimator K, ENNReal.ofReal (c*rateR .SI n d eps) ≤
          ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
            squaredRisk (canonicalDecisionLaw K p.1) T (tvFromUniform p.1)) ∧
        (∀ J : IntervalDecision K 0 1,
          (∀ p ∈ pairedFamily d, (0.90 : ℝ) ≤ coverage (canonicalDecisionLaw K p) J
            (tvFromUniform p)) →
          ENNReal.ofReal (c*rateH .SI n d eps) ≤
            ⨆ p : {p : Measure (PairedSymbol d) // p ∈ pairedFamily d},
              expectedLength (canonicalDecisionLaw K p.1) J) := by
    obtain ⟨b, hb, D, hD, hpriors⟩ :=
      paired_lawspace_resource_priors_of_gate hRN_of_gate hDual_of_gate hBernstein_of_gate
    let scale : ℝ := b/3400
    have hs : 0 < scale := by dsimp [scale]; positivity
    refine ⟨D, hD, min (scale^2/100) (scale/100),
      lt_min (by positivity) (by positivity), ?_⟩
    intro n d eps hAllowed hdim K hK
    obtain ⟨nu0, nu1, hnu0, hnu1, hmatch, hp0, hp1, gap, hgap,
      hlower, hmean, hescape, _hcontract, _hcancel⟩ :=
      hpriors n d eps hAllowed hdim K hK
    letI := hp0
    letI := hp1
    have hd : 0 < d := by have := hAllowed.2.1; omega
    have ha := (frontier_converse_amplitude_domain n d eps hAllowed).2
    have hdegree : (frontierResources n d eps).converseDegree - 1 + 1 =
        (frontierResources n d eps).converseDegree := by
      have := frontier_converse_degree_domain n d eps hAllowed
      omega
    rw [hdegree] at hmatch
    let v0 : ℝ := (∫ u, |u| ∂nu0)/2
    let v1 : ℝ := (∫ u, |u| ∂nu1)/2
    have hcenters : v1-v0 = gap := by
      rw [pairedLaw_prior_target_mean hd _ ha nu1 hnu1,
        pairedLaw_prior_target_mean hd _ ha nu0 hnu0] at hmean
      exact hmean
    have hTV := paired_lawspace_resource_contraction hRN_of_gate K eps hK hAllowed
      nu0 nu1 hnu0 hnu1 hmatch
    have hdec := paired_separated_lawspace_decisions K hAllowed.2.1
      ((productPrior d nu0).map pairedLaw) ((productPrior d nu1).map pairedLaw)
      (pairedLaw_productPrior_support hd _ ha nu0 hnu0)
      (pairedLaw_productPrior_support hd _ ha nu1 hnu1)
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
  intro n d eps hAllowed K hK
  have hr0 : 0 ≤ rateR .SI n d eps :=
    (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
      (rho_elementary_comparisons n d eps hAllowed).1
  have hh0 : 0 ≤ rateH .SI n d eps := Real.sqrt_nonneg _
  by_cases hdD : d ≤ D
  · have hSmall := paired_bounded_dimension_frontier_lower hRN_of_gate D n d eps hD hdD
      hAllowed K hK
    constructor
    · intro T
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_right cLarge cSmall) hr0)).trans (hSmall.1 T)
    · intro J hCov
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_right cLarge cSmall) hh0)).trans (hSmall.2 J hCov)
  · have hBig := hLarge n d eps hAllowed (by omega) K hK
    constructor
    · intro T
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLarge cSmall) hr0)).trans (hBig.1 T)
    · intro J hCov
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLarge cSmall) hh0)).trans (hBig.2 J hCov)


/-- Assume [measurable Radon–Nikodym densities for dominated kernels](hyp:hRN), [the Cai–Low moment-duality theorem](hyp:hDual), and [the Bernstein absolute-approximation limit](hyp:hBernstein). [The paired per-decision converse survives both minimax infima](goal). -/
-- @node: paired_minimax_lower_of_gate
lemma paired_minimax_lower_of_gate (hRN : MeasurableKernelRadonNikodym)
    (hDual : CaiLowMomentDuality) (hBernstein : BernsteinAbsoluteApproximationLimit) :
    ∃ c : ℝ, 0 < c ∧ ∀ n d eps, Allowed n d eps → ∀ C : ProtocolClassLabel,
      ENNReal.ofReal (c*rateR C n d eps) ≤ tvMinimaxRisk C (pairedFamily d) n eps ∧
      ENNReal.ofReal (c*rateH C n d eps) ≤ tvHonestLength C (pairedFamily d) n eps := by
  obtain ⟨c, hc, hLower⟩ := paired_converse_of_gate hRN hDual hBernstein
  refine ⟨c, hc, ?_⟩
  intro n d eps hAllowed C
  have hSeq : ∀ K : LocalProtocol n (PairedSymbol d), protocolClass C K eps →
      SequentialClass K eps := by
    intro K hK
    cases C with
    | NI => exact NoninteractiveClass.toSequentialClass K eps hK
    | SI => exact hK
  constructor
  · unfold tvMinimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hLower n d eps hAllowed e.1.1 (hSeq _ e.1.2)).1 e.2
  · unfold tvHonestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    exact (hLower n d eps hAllowed e.1.1 (hSeq _ e.1.2)).2 e.2.1 e.2.2

/-- Assume [the stated attain condition](hyp:hAttain). [Finite paired attainment bounds both private decision values; the same interval endpoints also define a legal interval in the larger range [0,1]](goal). -/
-- @node: tvAttainment_minimax_upper
lemma tvAttainment_minimax_upper (n d : ℕ) (eps r h C0 : ℝ)
    (hAttain : TvAttainment n d eps r h C0) (C : ProtocolClassLabel) :
    tvMinimaxRisk C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*r) ∧
    tvHonestLength C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*h) := by
  obtain ⟨K, hNI, _hFinite, T, J, _hTranscript, hBounds⟩ := hAttain
  have hK : protocolClass C K eps := by
    cases C with
    | NI => exact hNI
    | SI => exact NoninteractiveClass.toSequentialClass K eps hNI
  let J' : IntervalDecision K 0 1 :=
    { lo := J.lo, hi := J.hi, measurable_lo := J.measurable_lo,
      measurable_hi := J.measurable_hi, ordered := J.ordered,
      range_lo := fun w => ⟨(J.range_lo w).1, (J.range_lo w).2.trans (by norm_num)⟩,
      range_hi := fun w => ⟨(J.range_hi w).1, (J.range_hi w).2.trans (by norm_num)⟩ }
  constructor
  · unfold tvMinimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply iInf_le_of_le ⟨⟨K, hK⟩, T⟩
    apply iSup_le
    intro p
    exact (hBounds p.1 p.2).1
  · unfold tvHonestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply iInf_le_of_le ⟨⟨K, hK⟩, ⟨J', fun p hp => (hBounds p hp).2.1⟩⟩
    apply iSup_le
    intro p
    exact (hBounds p.1 p.2).2.2

/-- [Paired NI optimization is over a smaller protocol class than SI optimization](goal). -/
-- @node: tv_ni_si_values
lemma tv_ni_si_values (n d : ℕ) (eps : ℝ) :
    tvMinimaxRisk .SI (pairedFamily d) n eps ≤ tvMinimaxRisk .NI (pairedFamily d) n eps ∧
    tvHonestLength .SI (pairedFamily d) n eps ≤ tvHonestLength .NI (pairedFamily d) n eps := by
  constructor
  · unfold tvMinimaxRisk riskValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    let q : {K : LocalProtocol n (PairedSymbol d) // protocolClass .SI K eps} :=
      ⟨e.1.1, NoninteractiveClass.toSequentialClass e.1.1 eps e.1.2⟩
    exact iInf_le_of_le ⟨q, e.2⟩ le_rfl
  · unfold tvHonestLength lengthValue Causalean.Stat.minimaxValueENNReal
    apply le_iInf
    intro e
    let q : {K : LocalProtocol n (PairedSymbol d) // protocolClass .SI K eps} :=
      ⟨e.1.1, NoninteractiveClass.toSequentialClass e.1.1 eps e.1.2⟩
    exact iInf_le_of_le ⟨q, e.2⟩ le_rfl

-- @node: thm:paired-uniform-tv-frontier
/-- Given the [Bernstein absolute-approximation limit](hyp:hBernstein_of_gate), the paired experiment
satisfies the [complete TV frontier,
finite sign-vector attainment, and resource conclusions](goal). -/
theorem paired_uniform_tv_frontier
    (hBernstein_of_gate : BernsteinAbsoluteApproximationLimit) :
    (∀ d : ℕ, 2 ≤ d → ∀ theta ∈ parameterCube d,
      tvFromUniform (pairedLaw theta) = Causalean.Stat.tvDist (pairedLaw theta) (pairedUniform d) ∧
      tvFromUniform (pairedLaw theta) = signedNorm theta/2) ∧
    (∃ c C0 : ℝ, 0 < c ∧ c ≤ C0 ∧
      -- @realizes c(universal positive lower constant); @realizes C_0(universal finite upper constant)
      ∀ (n d : ℕ) (eps : ℝ), Allowed n d eps → ∀ C : ProtocolClassLabel,
        ENNReal.ofReal (c*rateR C n d eps) ≤ tvMinimaxRisk C (pairedFamily d) n eps ∧
        tvMinimaxRisk C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*rateR C n d eps) ∧
        ENNReal.ofReal (c*rateH C n d eps) ≤ tvHonestLength C (pairedFamily d) n eps ∧
        tvHonestLength C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*rateH C n d eps) ∧
        TvAttainment n d eps (rateR C n d eps) (rateH C n d eps) C0 ∧
        ConcreteTvAttainment n d eps C0 ∧
        (1 : ℝ≥0∞) ≤ tvMinimaxRisk .NI (pairedFamily d) n eps / tvMinimaxRisk .SI (pairedFamily
          d) n eps ∧
        tvMinimaxRisk .NI (pairedFamily d) n eps / tvMinimaxRisk .SI (pairedFamily d) n eps ≤
          ENNReal.ofReal (C0/c) ∧
        (1 : ℝ≥0∞) ≤ tvHonestLength .NI (pairedFamily d) n eps / tvHonestLength .SI
          (pairedFamily d) n eps ∧
        tvHonestLength .NI (pairedFamily d) n eps / tvHonestLength .SI (pairedFamily d) n eps ≤
          ENNReal.ofReal (C0/c)) ∧
    RateResourceConclusions ∧
    (∀ C : ProtocolClassLabel, ValueSequenceConclusions
      (fun n d eps => (tvMinimaxRisk C (pairedFamily d) n eps).toReal)
      (fun n d eps => (tvHonestLength C (pairedFamily d) n eps).toReal)) := by
  obtain ⟨cLower, hcLower, hLower⟩ :=
    paired_minimax_lower_of_gate measurableKernelRadonNikodym_proved
      caiLowMomentDuality_proved hBernstein_of_gate
  let c := min cLower 1
  let C0 : ℝ := (10 : ℝ)^16
  have hc : 0 < c := lt_min hcLower (by norm_num)
  have hC0 : 0 < C0 := by norm_num [C0]
  have hcC : c ≤ C0 := (min_le_right cLower 1).trans (by norm_num [C0])
  have hBase : ∀ n d eps, Allowed n d eps → ∀ C : ProtocolClassLabel,
      ENNReal.ofReal (c*rateR C n d eps) ≤ tvMinimaxRisk C (pairedFamily d) n eps ∧
      tvMinimaxRisk C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*rateR C n d eps) ∧
      ENNReal.ofReal (c*rateH C n d eps) ≤ tvHonestLength C (pairedFamily d) n eps ∧
      tvHonestLength C (pairedFamily d) n eps ≤ ENNReal.ofReal (C0*rateH C n d eps) := by
    intro n d eps hAllowed C
    have hr : 0 ≤ rateR C n d eps :=
      (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
        (rho_elementary_comparisons n d eps hAllowed).1
    have hh : 0 ≤ rateH C n d eps := Real.sqrt_nonneg _
    obtain ⟨hRl, hHl⟩ := hLower n d eps hAllowed C
    obtain ⟨hRu, hHu⟩ := tvAttainment_minimax_upper n d eps _ _ C0
      (tvFrontier_attainment boundedMeanConcentration_proved
        caiLowChebyshevApproximation_proved n d eps hAllowed) C
    exact ⟨(ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLower 1) hr)).trans hRl, hRu,
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cLower 1) hh)).trans hHl, hHu⟩
  refine ⟨?_, ⟨c, C0, hc, hcC, ?_⟩, rate_resource_conclusions, ?_⟩
  · intro d hd theta htheta
    have hp : IsProbabilityMeasure (pairedLaw theta) := pairedFamily_subset_simplex
      (by omega) (Set.mem_image_of_mem pairedLaw htheta)
    letI := hp
    exact ⟨tvFromUniform_eq_tvDist _ (by omega), tvFromUniform_pairedLaw theta htheta (by omega)⟩
  · intro n d eps hAllowed C
    obtain ⟨hRl, hRu, hHl, hHu⟩ := hBase n d eps hAllowed C
    have hn : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by have := hAllowed.1; omega)
    have ht : 0 < (n : ℝ)*eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
    have hr : 0 < rateR .NI n d eps :=
      (by positivity : (0 : ℝ) < min 1 (1/(n*eps^2))).trans_le
        (rho_elementary_comparisons n d eps hAllowed).1
    have hh : 0 < rateH .NI n d eps := Real.sqrt_pos.mpr hr
    have hInclusion := tv_ni_si_values n d eps
    have hRiskRatio := frontier_ratio_comparison c C0 (rateR .NI n d eps) hc hC0 hr
      (tvMinimaxRisk .NI (pairedFamily d) n eps) (tvMinimaxRisk .SI (pairedFamily d) n eps)
      hInclusion.1 (hBase n d eps hAllowed .SI).1 (hBase n d eps hAllowed .NI).2.1
    have hLengthRatio := frontier_ratio_comparison c C0 (rateH .NI n d eps) hc hC0 hh
      (tvHonestLength .NI (pairedFamily d) n eps) (tvHonestLength .SI (pairedFamily d) n eps)
      hInclusion.2 (hBase n d eps hAllowed .SI).2.2.1 (hBase n d eps hAllowed .NI).2.2.2
    exact ⟨hRl, hRu, hHl, hHu,
      tvFrontier_attainment boundedMeanConcentration_proved
        caiLowChebyshevApproximation_proved n d eps hAllowed,
      tvFrontier_concrete_attainment boundedMeanConcentration_proved
        caiLowChebyshevApproximation_proved n d eps hAllowed,
      hRiskRatio.1, hRiskRatio.2, hLengthRatio.1, hLengthRatio.2⟩
  · intro C
    apply value_sequence_conclusions_of_bounds _ _ c C0 hc hcC
    intro n d eps hAllowed
    obtain ⟨hRlo, hRhi, hHlo, hHhi⟩ := hBase n d eps hAllowed C
    have hRfin : tvMinimaxRisk C (pairedFamily d) n eps ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hRhi
    have hHfin : tvHonestLength C (pairedFamily d) n eps ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hHhi
    have hrho : 0 ≤ rho (n*eps^2) d :=
      (by positivity : (0 : ℝ) ≤ min 1 (1/(n*eps^2))).trans
        (rho_elementary_comparisons n d eps hAllowed).1
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [rateR, ENNReal.toReal_ofReal (mul_nonneg hc.le hrho)] using
        ENNReal.toReal_mono hRfin hRlo
    · simpa only [rateR, ENNReal.toReal_ofReal (mul_nonneg hC0.le hrho)] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hRhi
    · simpa only [rateH, rateR,
        ENNReal.toReal_ofReal (mul_nonneg hc.le (Real.sqrt_nonneg _))] using
        ENNReal.toReal_mono hHfin hHlo
    · simpa only [rateH, rateR,
        ENNReal.toReal_ofReal (mul_nonneg hC0.le (Real.sqrt_nonneg _))] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hHhi


end CausalSmith.Stat.LdpOptvalueUniformFrontier
