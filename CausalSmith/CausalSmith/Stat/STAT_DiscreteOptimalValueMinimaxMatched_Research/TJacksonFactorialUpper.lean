import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.UpperRiskAggregation
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.EmpiricalRatioRisk
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TEqualPropensityL1Reduction

set_option linter.style.longLine false

/-! Uniform upper risk bound for the explicit Jackson--factorial estimator. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

-- @node: thm:jackson-factorial-upper
/-- If [the product experiment has the stated independent-sampling law](hyp:h_iid), then [the stated jackson factorial upper relation holds](goal). -/
theorem jackson_factorial_upper
    (h_iid : ∀ {d n : ℕ} (P : DiscreteLaw d), IidSampling P (productLaw P n)) :
    ∃ tuning : JacksonTuning, 2 < tuning.boundedAlphabetCutoff ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ Cepsilon : ℝ, 0 < Cepsilon ∧ ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
        ∀ P : DiscreteLaw d, ∀ hP : ObservedModelClass epsilon P,
          Causalean.Stat.sqRisk (productLaw P n) (jacksonFactorialEstimator tuning epsilon)
            (observedOptimalValue P hP) ≤
          Cepsilon * min 1 (d / (n * logAlphabet d)) := by
  obtain ⟨tuning, htuning, hpilot⟩ := centered_factorial_pilot_control h_iid
  subst tuning
  refine ⟨canonicalJacksonTuning, canonicalJacksonTuning_cutoff, ?_⟩
  intro epsilon hepsilon hepsilonHalf
  obtain ⟨C, hC, hcontrols⟩ := hpilot epsilon hepsilon hepsilonHalf
  let Cepsilon : ℝ :=
    20000000 * (1 + C + C ^ 2) +
      2000 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) + 10
  have hCe : 0 < Cepsilon := by
    dsimp [Cepsilon]
    have hsq : 0 ≤ C ^ 2 := sq_nonneg C
    have hie : 0 ≤ epsilon⁻¹ := inv_nonneg.mpr (le_of_lt hepsilon)
    have hiesq : 0 ≤ epsilon⁻¹ ^ 2 := sq_nonneg _
    nlinarith
  refine ⟨Cepsilon, hCe, ?_⟩
  intro n d hn hd P hP
  have hnpos : 0 < n := by omega
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hdR : 0 < (d : ℝ) := by positivity
  have hL : 0 < logAlphabet d := by
    rw [logAlphabet]
    apply Real.log_pos
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
    exact he.trans_le (by
      simpa using mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
  have hLle : logAlphabet d ≤ d := by
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR), Real.log_exp]
    have hlog := Real.log_le_sub_one_of_pos hdR
    linarith
  have htheta := observedOptimalValue_mem_unitInterval P hP
  have htarget : observedOptimalValue P hP =
      ∑ x : Fin d, globalCellValue epsilon (cellVector P x) := by
    rw [observedOptimalValue, observedOptimalValueRaw]
    apply Finset.sum_congr rfl
    intro x hx
    exact (globalCellValue_cellVector P hP x).symm
  by_cases hcut : d < canonicalJacksonTuning.boundedAlphabetCutoff
  · have hd2 : d = 2 := by
      norm_num [canonicalJacksonTuning] at hcut
      omega
    subst d
    have hest : jacksonFactorialEstimator (n := n) (d := 2)
        canonicalJacksonTuning epsilon = empiricalRatioEstimator := by
      funext sample
      simp [jacksonFactorialEstimator, hcut]
    rw [hest]
    by_cases hn4 : 4 ≤ n
    · have hrisk := empiricalRatio_sqRisk_two_le P hP hn4
      have hL2 : logAlphabet 2 ≤ 2 := hLle
      have hratio : (2 : ℝ) / (n * logAlphabet 2) ≤ 1 := by
        rw [div_le_one (mul_pos hnR hL)]
        have hLone : 1 ≤ logAlphabet 2 := by
          rw [logAlphabet]
          calc
            1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
            _ ≤ Real.log (Real.exp 1 * 2) :=
              Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
                (mul_pos (Real.exp_pos 1) (by norm_num))
                (by nlinarith [Real.exp_pos 1])
        have hn4R : (4 : ℝ) ≤ n := by exact_mod_cast hn4
        nlinarith
      norm_num only [Nat.cast_ofNat] at ⊢
      rw [min_eq_right hratio]
      calc
        _ ≤ 1600 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := hrisk
        _ ≤ Cepsilon * (2 / (n * logAlphabet 2)) := by
          have hbase : 0 ≤ 1 + epsilon⁻¹ + epsilon⁻¹ ^ 2 := by positivity
          have hpart : 1600 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) ≤
              Cepsilon * (2 / logAlphabet 2) := by
            have hcoef : 1600 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) ≤ Cepsilon := by
              dsimp [Cepsilon]
              nlinarith [sq_nonneg C, inv_nonneg.mpr (le_of_lt hepsilon),
                sq_nonneg epsilon⁻¹]
            have htwo : 1 ≤ 2 / logAlphabet 2 := by
              rw [le_div_iff₀ hL]
              simpa using hL2
            nlinarith [mul_le_mul_of_nonneg_left htwo (le_of_lt hCe)]
          field_simp [ne_of_gt hnR, ne_of_gt hL] at hpart ⊢
          nlinarith
    · have hnle : n ≤ 3 := by omega
      have her := empiricalRatioEstimator_mem_unitInterval
        (n := n) (d := 2)
      have hrisk : Causalean.Stat.sqRisk (productLaw P n) empiricalRatioEstimator
          (observedOptimalValue P hP) ≤ 1 := by
        unfold Causalean.Stat.sqRisk
        calc
          _ ≤ ∫ _z : Fin n → Obs 2, (1 : ℝ) ∂productLaw P n := by
            apply MeasureTheory.integral_mono MeasureTheory.Integrable.of_finite
              (MeasureTheory.integrable_const 1)
            intro z
            have hz := her z hnpos
            have habs : |empiricalRatioEstimator z - observedOptimalValue P hP| ≤ 1 :=
              abs_le.mpr ⟨by linarith [hz.1, htheta.2], by linarith [hz.2, htheta.1]⟩
            simpa only [sq_abs, one_pow] using
              (pow_le_pow_left₀ (abs_nonneg _) habs 2)
          _ = 1 := by simp
      have hratioLower : (1 / 3 : ℝ) ≤ 2 / (n * logAlphabet 2) := by
        rw [le_div_iff₀ (mul_pos hnR hL)]
        have hn3 : (n : ℝ) ≤ 3 := by exact_mod_cast hnle
        have hprod : (n : ℝ) * logAlphabet 2 ≤ 3 * 2 :=
          mul_le_mul hn3 hLle (le_of_lt hL) (by norm_num)
        nlinarith
      have hminLower : (1 / 3 : ℝ) ≤ min 1 (2 / (n * logAlphabet 2)) := by
        rw [le_min_iff]
        exact ⟨by norm_num, hratioLower⟩
      calc
        _ ≤ 1 := hrisk
        _ ≤ Cepsilon * min 1 (2 / (n * logAlphabet 2)) := by
          have hCe3 : 3 ≤ Cepsilon := by
            dsimp [Cepsilon]
            nlinarith [sq_nonneg C, inv_nonneg.mpr (le_of_lt hepsilon),
              sq_nonneg epsilon⁻¹]
          nlinarith [mul_le_mul_of_nonneg_left hminLower (le_of_lt hCe)]
  · by_cases hscale : (n : ℝ) < d / logAlphabet d
    · have hest : jacksonFactorialEstimator (n := n) (d := d)
          canonicalJacksonTuning epsilon = fun _ => (1 / 2 : ℝ) := by
        funext sample
        simp [jacksonFactorialEstimator, hcut, hscale]
      rw [hest]
      have hrisk : Causalean.Stat.sqRisk (productLaw P n) (fun _ => (1 / 2 : ℝ))
          (observedOptimalValue P hP) ≤ 1 := by
        unfold Causalean.Stat.sqRisk
        calc
          _ ≤ ∫ _z : Fin n → Obs d, (1 : ℝ) ∂productLaw P n := by
            apply MeasureTheory.integral_mono (MeasureTheory.integrable_const _)
              (MeasureTheory.integrable_const _)
            intro z
            nlinarith [htheta.1, htheta.2]
          _ = 1 := by simp
      have hr : 1 < d / (n * logAlphabet d) := by
        rw [lt_div_iff₀ hL] at hscale
        rw [one_lt_div (mul_pos hnR hL)]
        nlinarith
      rw [min_eq_left (le_of_lt hr)]
      have hCeOne : 1 ≤ Cepsilon := by
        dsimp [Cepsilon]
        nlinarith [sq_nonneg C, inv_nonneg.mpr (le_of_lt hepsilon),
          sq_nonneg epsilon⁻¹]
      exact hrisk.trans (by simpa using hCeOne)
    · obtain ⟨_hcount, _htable, _hcell, _hfactorial, hcellControl⟩ :=
        hcontrols n d P hnpos hP
      have huncapped := sqRisk_jacksonUncapped_le_rate P epsilon
        (observedOptimalValue P hP) C hnpos hd hepsilon hC htheta htarget
        (le_of_not_gt hscale) (fun x => (hcellControl x).1)
        (fun x => (hcellControl x).2.1)
      have houter := sqRisk_jacksonFactorialEstimator_le_marked P
        canonicalJacksonTuning epsilon
        (observedOptimalValue P hP) hnpos hcut hscale
      have hcap := sqRisk_marked_raoBlackwell_jackson_le P canonicalJacksonTuning epsilon
        (observedOptimalValue P hP) hnpos htheta
      have htail :=
        Causalean.Stat.Concentration.PoissonSelfNormalized.poisson_quarter_overflow_le_inv
          n hnpos
      have hr0 : 0 ≤ d / (n * logAlphabet d) := by positivity
      have htailRate : 8 / (n : ℝ) ≤ 8 * (d / (n * logAlphabet d)) := by
        have hone : 1 ≤ d / logAlphabet d := by
          rw [le_div_iff₀ hL]
          simpa using hLle
        field_simp [ne_of_gt hnR, ne_of_gt hL] at hone ⊢
        nlinarith
      have hrisk : Causalean.Stat.sqRisk (productLaw P n)
          (jacksonFactorialEstimator canonicalJacksonTuning epsilon)
            (observedOptimalValue P hP) ≤
          (10000000 * (1 + C + C ^ 2) + 8) *
            (d / (n * logAlphabet d)) := by
        calc
          _ ≤ Causalean.Stat.sqRisk
              (MeasureTheory.Measure.pi
                (fun _ : Fin n => (obsLaw P).prod uncappedFairMarkLaw))
              (Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
                (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hnpos) 0)
              (observedOptimalValue P hP) := houter
          _ ≤ Causalean.Stat.sqRisk
              (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
                ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4)))
              (jacksonUncappedStatistic canonicalJacksonTuning epsilon n hnpos)
              (observedOptimalValue P hP) +
              (ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4))).real
                (Set.Ioi n) := hcap
          _ ≤ 10000000 * (1 + C + C ^ 2) * (d / (n * logAlphabet d)) +
              8 * (d / (n * logAlphabet d)) := by
            have htail' :
                (ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4))).real
                    (Set.Ioi n) ≤ 8 / (n : ℝ) := by
              have hmean : Real.toNNReal ((n : ℝ) / 4) = (n : NNReal) / 4 := by
                apply NNReal.eq
                simp [Real.toNNReal_of_nonneg (by positivity : 0 ≤ (n : ℝ) / 4)]
              rw [hmean]
              exact htail
            linarith
          _ = _ := by ring
      have hrle : d / (n * logAlphabet d) ≤ 1 := by
        rw [div_le_one (mul_pos hnR hL)]
        have hscalele : (d : ℝ) / logAlphabet d ≤ n := le_of_not_gt hscale
        rw [div_le_iff₀ hL] at hscalele
        exact hscalele
      rw [min_eq_right hrle]
      calc
        _ ≤ (10000000 * (1 + C + C ^ 2) + 8) *
            (d / (n * logAlphabet d)) := hrisk
        _ ≤ Cepsilon * (d / (n * logAlphabet d)) := by
          apply mul_le_mul_of_nonneg_right _ hr0
          dsimp [Cepsilon]
          nlinarith [sq_nonneg C, inv_nonneg.mpr (le_of_lt hepsilon),
            sq_nonneg epsilon⁻¹]

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
