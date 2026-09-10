import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TMatchedMinimaxFrontier

/-! Deterministic comparison with the predecessor rates and bounded-alphabet branch. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

/-- Eventual two-sided parametric risk bounds along a bounded alphabet sequence. -/
def EventualParametricRisk (epsilon : ℝ) (dseq : ℕ → ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
    ∀ᶠ n in Filter.atTop,
      c / n ≤ minimaxRisk n (dseq n) epsilon ∧
        minimaxRisk n (dseq n) epsilon ≤ C / n

-- @node: prop:parent-reduction
/-- If [the Cai--Low moment-matching prior result is available](hyp:h_cai_low_of_gate), and [the Jiao--Han--Weissman Poisson L1 lower bound is available](hyp:h_jhw_of_gate), then [the parent observed and causal minimax problems inherit the matched frontier, bounded-alphabet equivalence, and fallback comparisons](goal). -/
theorem parent_reduction
    (h_cai_low_of_gate : CaiLowAbsoluteMomentPriors)
    (h_jhw_of_gate : JhwPoissonL1Lower) :
    ∃ tuning : JacksonTuning,
      2 < tuning.boundedAlphabetCutoff ∧
      (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
          c * min 1 (Real.sqrt d / n + d / (n * Real.log (Real.exp 1 * n))) ≤
            minimaxRisk n d epsilon ∧
          minimaxRisk n d epsilon ≤ C * (d / n)) ∧
      (∀ n d : ℕ, 2 ≤ d → d < tuning.boundedAlphabetCutoff →
        ∀ epsilon sample, jacksonFactorialEstimator (n := n) (d := d) tuning epsilon sample =
          empiricalRatioEstimator sample) ∧
      (∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
        ∀ dseq : ℕ → ℕ, (∀ n, 2 ≤ dseq n) →
          (∃ dmax : ℕ, ∀ n, dseq n ≤ dmax) → EventualParametricRisk epsilon dseq) := by
  obtain ⟨tuning, htuning, hfrontier⟩ :=
    matched_minimax_frontier h_cai_low_of_gate h_jhw_of_gate
  refine ⟨tuning, htuning, ?_, ?_, ?_⟩
  · intro epsilon hepsilon hepsilon'
    obtain ⟨c, C, hc, hcC, hbounds⟩ := hfrontier epsilon hepsilon hepsilon'
    refine ⟨c / 4, C, by positivity, by nlinarith, ?_⟩
    intro n d hn hd
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hdR : 0 < (d : ℝ) := by positivity
    have hlogd : 0 < logAlphabet d := by
      rw [logAlphabet]
      apply Real.log_pos
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
      exact lt_of_lt_of_le he (by
        calc
          Real.exp 1 = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * d := mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
    have hlogn : 0 < Real.log (Real.exp 1 * n) := by
      apply Real.log_pos
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact lt_of_lt_of_le he (by
        calc
          Real.exp 1 = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * n := mul_le_mul_of_nonneg_left hn1 (Real.exp_nonneg 1))
    have hlog_sqrt : logAlphabet d ≤ 2 * Real.sqrt d := by
      have hsqrtpos : 0 < Real.sqrt d := Real.sqrt_pos.2 hdR
      have hlog_le := Real.log_le_sub_one_of_pos hsqrtpos
      have hlog_sqrt_eq := Real.log_sqrt (le_of_lt hdR)
      rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdR),
        Real.log_exp] at ⊢
      nlinarith
    have hsqrt_term : Real.sqrt d / n ≤
        2 * (d / (n * logAlphabet d)) := by
      rw [div_le_iff₀ hnR]
      have hsqrt_nonneg : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
      have hsqrt_sq : Real.sqrt d * Real.sqrt d = d := Real.mul_self_sqrt (le_of_lt hdR)
      have hcancel : 2 * (d / (n * logAlphabet d)) * n =
          2 * d / logAlphabet d := by
        field_simp
      calc
        Real.sqrt d ≤ 2 * d / logAlphabet d := by
          rw [le_div_iff₀ hlogd]
          nlinarith
        _ = 2 * (d / (n * logAlphabet d)) * n := hcancel.symm
    have hparent_scale :
        min 1 (Real.sqrt d / n + d / (n * Real.log (Real.exp 1 * n))) ≤
          4 * min 1 (d / (n * logAlphabet d)) := by
      by_cases ha : 1 ≤ d / (n * logAlphabet d)
      · rw [min_eq_left ha]
        exact le_trans (min_le_left _ _) (by norm_num)
      · have ha' : d / (n * logAlphabet d) < 1 := lt_of_not_ge ha
        rw [min_eq_right (le_of_lt ha')]
        have hlogs : logAlphabet d ≤ 2 * Real.log (Real.exp 1 * n) := by
          by_cases hnd : d ≤ n
          · have hmul : Real.exp 1 * (d : ℝ) ≤ Real.exp 1 * n :=
              mul_le_mul_of_nonneg_left (by exact_mod_cast hnd) (Real.exp_nonneg 1)
            have hmono : logAlphabet d ≤ Real.log (Real.exp 1 * n) := by
              rw [logAlphabet]
              exact Real.strictMonoOn_log.monotoneOn
                (mul_pos (Real.exp_pos 1) hdR) (mul_pos (Real.exp_pos 1) hnR) hmul
            nlinarith [hlogn]
          · have hdn : (n : ℝ) < d := by exact_mod_cast (lt_of_not_ge hnd)
            let t : ℝ := d / n
            have ht : 1 < t := (one_lt_div hnR).2 hdn
            have hsplit : logAlphabet d = Real.log (Real.exp 1 * n) + Real.log t := by
              dsimp [t]
              rw [logAlphabet, ← Real.log_mul (by positivity : Real.exp 1 * (n : ℝ) ≠ 0)
                (by positivity : (d : ℝ) / n ≠ 0)]
              congr 1
              field_simp
            have hlogt : Real.log t ≤ t / 2 := by
              have hsqrtpos : 0 < Real.sqrt t := Real.sqrt_pos.2 (lt_trans (by norm_num) ht)
              have hbase := Real.log_le_sub_one_of_pos hsqrtpos
              have hroot := Real.log_sqrt (le_of_lt (lt_trans (by norm_num) ht))
              have hsquare := Real.sq_sqrt (le_of_lt (lt_trans (by norm_num) ht))
              nlinarith [sq_nonneg (Real.sqrt t - 2)]
            have ht_bound : t ≤ 2 * Real.log (Real.exp 1 * n) := by
              have hat : t / logAlphabet d < 1 := by
                dsimp [t]
                simpa [div_div] using ha'
              rw [div_lt_one hlogd] at hat
              rw [hsplit] at hat
              nlinarith
            rw [hsplit]
            nlinarith
        have hsecond : d / (n * Real.log (Real.exp 1 * n)) ≤
            2 * (d / (n * logAlphabet d)) := by
          calc
            d / (n * Real.log (Real.exp 1 * n)) ≤ d / (n * (logAlphabet d / 2)) := by
              apply div_le_div_of_nonneg_left (le_of_lt hdR)
                (mul_pos hnR (div_pos hlogd (by norm_num)))
              exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hnR)
            _ = 2 * (d / (n * logAlphabet d)) := by field_simp
        have hmin := min_le_right (1 : ℝ)
          (Real.sqrt d / n + d / (n * Real.log (Real.exp 1 * n)))
        nlinarith [hsqrt_term, hsecond, hmin]
    obtain ⟨hlower, _hmiddle, hupper, _hcausal⟩ := hbounds n d hn hd
    constructor
    · calc
        c / 4 * min 1 (Real.sqrt d / n + d / (n * Real.log (Real.exp 1 * n))) ≤
            c * min 1 (d / (n * logAlphabet d)) := by
              nlinarith [mul_le_mul_of_nonneg_left hparent_scale (le_of_lt hc)]
        _ ≤ minimaxRisk n d epsilon := hlower
    · calc
        minimaxRisk n d epsilon ≤ C * min 1 (d / (n * logAlphabet d)) :=
          _hmiddle.trans hupper
        _ ≤ C * (d / n) := by
          have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
          apply mul_le_mul_of_nonneg_left _ hC
          refine le_trans (min_le_right _ _) ?_
          have hlog_one : 1 ≤ logAlphabet d := by
            rw [logAlphabet]
            have hmul : Real.exp 1 ≤ Real.exp 1 * (d : ℝ) := by
              have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
              calc
                Real.exp 1 = Real.exp 1 * 1 := by ring
                _ ≤ Real.exp 1 * d := mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)
            calc
              1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
              _ ≤ Real.log (Real.exp 1 * d) := Real.strictMonoOn_log.monotoneOn
                (Real.exp_pos 1) (mul_pos (Real.exp_pos 1) hdR) hmul
          apply div_le_div_of_nonneg_left (le_of_lt hdR) hnR
          simpa using mul_le_mul_of_nonneg_left hlog_one (le_of_lt hnR)
  · intro n d hd hdcut epsilon sample
    simp [jacksonFactorialEstimator, hdcut]
  · intro epsilon hepsilon hepsilon' dseq hdseq
    rintro ⟨dmax, hdmax⟩
    obtain ⟨c, C, hc, hcC, hbounds⟩ := hfrontier epsilon hepsilon hepsilon'
    have hdmax2 : 2 ≤ dmax := le_trans (hdseq 0) (hdmax 0)
    have hdmaxR : (2 : ℝ) ≤ dmax := by exact_mod_cast hdmax2
    have hlogmax : 0 < Real.log (Real.exp 1 * dmax) := Real.log_pos (by
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      have hdmax1 : (1 : ℝ) ≤ dmax := le_trans (by norm_num) hdmaxR
      exact lt_of_lt_of_le he (by
        calc
          Real.exp 1 = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * dmax :=
            mul_le_mul_of_nonneg_left hdmax1 (Real.exp_nonneg 1)))
    have hlogmax_one : 1 ≤ Real.log (Real.exp 1 * dmax) := by
      have hmul : Real.exp 1 ≤ Real.exp 1 * (dmax : ℝ) := by
        calc
          Real.exp 1 = Real.exp 1 * 1 := by ring
          _ ≤ Real.exp 1 * dmax :=
            mul_le_mul_of_nonneg_left (le_trans (by norm_num) hdmaxR) (Real.exp_nonneg 1)
      calc
        1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ ≤ Real.log (Real.exp 1 * dmax) := Real.strictMonoOn_log.monotoneOn
          (Real.exp_pos 1)
            (mul_pos (Real.exp_pos 1) (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hdmax2))) hmul
    refine ⟨c * (2 / Real.log (Real.exp 1 * dmax)), C * dmax, ?_, ?_, ?_⟩
    · positivity
    · have hratio : 2 / Real.log (Real.exp 1 * dmax) ≤ (dmax : ℝ) := by
        rw [div_le_iff₀ hlogmax]
        calc
          2 ≤ (dmax : ℝ) * 1 := by simpa using hdmaxR
          _ ≤ (dmax : ℝ) * Real.log (Real.exp 1 * dmax) :=
            mul_le_mul_of_nonneg_left hlogmax_one (Nat.cast_nonneg dmax)
      calc
        c * (2 / Real.log (Real.exp 1 * dmax)) ≤ c * dmax :=
          mul_le_mul_of_nonneg_left hratio (le_of_lt hc)
        _ ≤ C * dmax := mul_le_mul_of_nonneg_right hcC (Nat.cast_nonneg dmax)
    · filter_upwards [Filter.eventually_ge_atTop dmax] with n hnmax
      have hn : 1 ≤ n := le_trans (by omega : 1 ≤ dmax) hnmax
      have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
      have hd := hdseq n
      have hdR : 0 < (dseq n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
      have hdn := hdmax n
      have hlogd : 0 < logAlphabet (dseq n) := by
        rw [logAlphabet]
        apply Real.log_pos
        have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
        have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
        exact lt_of_lt_of_le he (by
          calc
            Real.exp 1 = Real.exp 1 * 1 := by ring
            _ ≤ Real.exp 1 * dseq n :=
              mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1))
      have hlogd_one : 1 ≤ logAlphabet (dseq n) := by
        rw [logAlphabet]
        have hmul : Real.exp 1 ≤ Real.exp 1 * (dseq n : ℝ) := by
          have hd1 : (1 : ℝ) ≤ dseq n := by exact_mod_cast (le_trans (by omega : 1 ≤ 2) hd)
          calc
            Real.exp 1 = Real.exp 1 * 1 := by ring
            _ ≤ Real.exp 1 * dseq n :=
              mul_le_mul_of_nonneg_left hd1 (Real.exp_nonneg 1)
        calc
          1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
          _ ≤ Real.log (Real.exp 1 * dseq n) := Real.strictMonoOn_log.monotoneOn
            (Real.exp_pos 1) (mul_pos (Real.exp_pos 1) hdR) hmul
      have hlog_le_max : logAlphabet (dseq n) ≤ Real.log (Real.exp 1 * dmax) := by
        rw [logAlphabet]
        apply Real.strictMonoOn_log.monotoneOn
          (mul_pos (Real.exp_pos 1) hdR)
          (mul_pos (Real.exp_pos 1)
            (by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hdmax2)))
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdn) (Real.exp_nonneg 1)
      have hscale : (dseq n : ℝ) / (n * logAlphabet (dseq n)) ≤ 1 := by
        rw [div_le_one (mul_pos hnR hlogd)]
        have hcast : (dseq n : ℝ) ≤ n := by exact_mod_cast (hdn.trans hnmax)
        exact hcast.trans (by
          simpa using mul_le_mul_of_nonneg_left hlogd_one (le_of_lt hnR))
      obtain ⟨hlower, hmiddle, hupper, _hcausal⟩ := hbounds n (dseq n) hn hd
      rw [min_eq_right hscale] at hlower hupper
      constructor
      · have hratio : 2 / Real.log (Real.exp 1 * dmax) ≤
            (dseq n : ℝ) / logAlphabet (dseq n) := by
          rw [div_le_div_iff₀ hlogmax hlogd]
          calc
            2 * logAlphabet (dseq n) ≤ 2 * Real.log (Real.exp 1 * dmax) := by gcongr
            _ ≤ (dseq n : ℝ) * Real.log (Real.exp 1 * dmax) := by
              gcongr
              exact_mod_cast hd
        calc
          c * (2 / Real.log (Real.exp 1 * dmax)) / n ≤
              c * ((dseq n : ℝ) / logAlphabet (dseq n)) / n := by gcongr
          _ = c * ((dseq n : ℝ) / (n * logAlphabet (dseq n))) := by field_simp
          _ ≤ minimaxRisk n (dseq n) epsilon := hlower
      · calc
          minimaxRisk n (dseq n) epsilon ≤
              C * ((dseq n : ℝ) / (n * logAlphabet (dseq n))) := hmiddle.trans hupper
          _ ≤ C * ((dseq n : ℝ) / n) := by
            have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
            apply mul_le_mul_of_nonneg_left _ hC
            apply div_le_div_of_nonneg_left (le_of_lt hdR) hnR
            simpa using mul_le_mul_of_nonneg_left hlogd_one (le_of_lt hnR)
          _ ≤ C * dmax / n := by
            have hC : 0 ≤ C := le_trans (le_of_lt hc) hcC
            rw [← mul_div_assoc]
            rw [div_le_div_iff₀ hnR hnR]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (by exact_mod_cast hdn) hC) (le_of_lt hnR)

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
