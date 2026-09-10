import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TAllEstimatorLower
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TJacksonFactorialUpper
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TCausalOptimalValueCorollary

set_option linter.style.longLine false

/-! Matched minimax frontier and its causal transfer. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

/-- For [the specified tuning rule, sample size, alphabet size, overlap level](hyp:tuning,n,d,epsilon), the [Jackson worst-case risk is the supremum squared-error risk of the Jackson factorial estimator over the observed model class](goal). -/
noncomputable def jacksonWorstCaseRisk (tuning : JacksonTuning) (n d : ℕ) (epsilon : ℝ) : ℝ :=
  ⨆ P : ModelLaw d epsilon,
    Causalean.Stat.sqRisk (productLaw P.1 n) (jacksonFactorialEstimator tuning epsilon)
      (observedOptimalValue P.1 P.2)

-- @node: thm:matched-minimax-frontier
/-- If [the Cai--Low moment-matching prior result is available](hyp:h_cai_low_of_gate), and [the Jiao--Han--Weissman Poisson L1 lower bound is available](hyp:h_jhw_of_gate), then [the observed minimax risk is bounded above and below by positive constants times the minimum of one and $d/(nlog(ed))$, with the stated causal and fallback comparisons](goal). -/
theorem matched_minimax_frontier
    (h_cai_low_of_gate : CaiLowAbsoluteMomentPriors)
    (h_jhw_of_gate : JhwPoissonL1Lower) :
    ∃ tuning : JacksonTuning, 2 < tuning.boundedAlphabetCutoff ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ cepsilon Cepsilon : ℝ,
        0 < cepsilon ∧ -- @realizes \(c_\epsilon\)(positive lower comparison constant)
        cepsilon ≤ Cepsilon ∧ -- @realizes \(C_\epsilon\)(positive upper constant, since cepsilon is positive)
        ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
          cepsilon * min 1 (d / (n * logAlphabet d)) ≤ minimaxRisk n d epsilon ∧
          minimaxRisk n d epsilon ≤ jacksonWorstCaseRisk tuning n d epsilon ∧
          jacksonWorstCaseRisk tuning n d epsilon ≤
            Cepsilon * min 1 (d / (n * logAlphabet d)) ∧
          causalMinimaxRisk n d epsilon = minimaxRisk n d epsilon := by
  obtain ⟨tuning, htuning, hupper⟩ := jackson_factorial_upper
    (fun _P => rfl)
  refine ⟨tuning, htuning, ?_⟩
  intro epsilon hepsilon hepsilon'
  obtain ⟨C, hC, hupper⟩ := hupper epsilon hepsilon hepsilon'
  obtain ⟨c, hc, hlower⟩ :=
    all_estimator_lower (fun _P => rfl) h_cai_low_of_gate h_jhw_of_gate
      epsilon hepsilon hepsilon'
  refine ⟨c, C + c, hc, by linarith, ?_⟩
  intro n d hn hd
  have hlog_pos : 0 < logAlphabet d := by
    rw [logAlphabet]
    exact Real.log_pos (by
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      nlinarith [show (2 : ℝ) ≤ d by exact_mod_cast hd])
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hscale : 0 ≤ min 1 ((d : ℝ) / (n * logAlphabet d)) := by
    rw [le_min_iff]
    exact ⟨by norm_num, by positivity⟩
  let jf : Estimator n d := ⟨jacksonFactorialEstimator tuning epsilon, by fun_prop⟩
  refine ⟨hlower n d hn hd, ?_, ?_, ?_⟩
  · unfold minimaxRisk jacksonWorstCaseRisk
    exact Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
      (risk := observedRisk n (d := d) (epsilon := epsilon))
      (by intro est P; unfold observedRisk Causalean.Stat.sqRisk; positivity)
      jf
  · unfold jacksonWorstCaseRisk
    change Causalean.Stat.worstCaseRisk
      (observedRisk n (d := d) (epsilon := epsilon))
      jf ≤ _
    cases isEmpty_or_nonempty (ModelLaw d epsilon) with
    | inl _ =>
      rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
      positivity
    | inr _ =>
      apply Causalean.Stat.worstCaseRisk_le
      intro P
      change Causalean.Stat.sqRisk (productLaw P.1 n)
        (jacksonFactorialEstimator tuning epsilon)
        (observedOptimalValue P.1 P.2) ≤ _
      calc
        Causalean.Stat.sqRisk (productLaw P.1 n)
            (jacksonFactorialEstimator tuning epsilon)
            (observedOptimalValue P.1 P.2) ≤
            C * min 1 (d / (n * logAlphabet d)) := hupper n d hn hd P.1 P.2
        _ ≤ (C + c) * min 1 (d / (n * logAlphabet d)) := by
          nlinarith
  · unfold causalMinimaxRisk minimaxRisk Causalean.Stat.minimaxValue
    congr 1
    funext est
    rw [Causalean.Stat.worstCaseRisk_eq_sSup_range,
      Causalean.Stat.worstCaseRisk_eq_sSup_range]
    congr 1
    ext r
    constructor
    · rintro ⟨Q, rfl⟩
      refine ⟨⟨observedMarginal Q.1, Q.2.observedModel⟩, ?_⟩
      unfold causalRisk observedRisk
      rw [causal_optimal_value_corollary Q.1 Q.2]
    · rintro ⟨P, rfl⟩
      obtain ⟨_hcone, _hvalue, _hbound, _hlip, hcompletion, _hconverse⟩ :=
        identification_and_extension P.1 hd ⟨hepsilon, hepsilon'⟩ P.2
      obtain ⟨Q, hQ, hconstruction⟩ := hcompletion
      refine ⟨⟨Q, hQ⟩, ?_⟩
      unfold causalRisk observedRisk
      rw [causal_optimal_value_corollary Q hQ]
      simpa [hconstruction.1]

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
