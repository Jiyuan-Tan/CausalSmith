import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.LowerSplice
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TEqualPropensityL1Reduction

/-! Conditional minimax lower bound over all measurable estimators. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

-- @node: thm:all-estimator-lower
/-- If [the product experiment has the stated independent-sampling law](hyp:h_iid), and [the Cai--Low moment-matching prior result is available](hyp:h_cai_low), and [the Jiao--Han--Weissman Poisson L1 lower bound is available](hyp:h_jhw), then [there is a positive constant, depending only on overlap, for which every estimator has risk at least that constant times the minimum of one and $d/(nlog(ed))$](goal). -/
theorem all_estimator_lower
    (h_iid : ∀ {d n : ℕ} (P : DiscreteLaw d), IidSampling P (productLaw P n))
    (h_cai_low : CaiLowAbsoluteMomentPriors)
    (h_jhw : JhwPoissonL1Lower) :
    ∀ epsilon : ℝ, 0 < epsilon → epsilon < 1 / 2 →
      ∃ cepsilon : ℝ, 0 < cepsilon ∧ ∀ n d : ℕ, 1 ≤ n → 2 ≤ d →
        cepsilon * min 1 (d / (n * logAlphabet d)) ≤ minimaxRisk n d epsilon := by
  obtain ⟨Ddense, hDdense, hdense⟩ := dense_moment_matching_lower h_iid h_cai_low
  obtain ⟨cJ, hcJ, hJ⟩ :=
    jhw_fixedL1_lower_sub_expTail h_jhw (1 / 4) 2 (by norm_num) (by norm_num)
  obtain ⟨Dlog, hDlog⟩ := eventually_logAlphabet_le_half
  obtain ⟨Ntail, hNtail2, htail⟩ := pairedTail_cutoff cJ hcJ
  let D := max Ddense Dlog
  let M := max D Ntail
  intro epsilon hepsilon hepsilonHalf
  obtain ⟨cDense, hcDense, hDense⟩ := hdense epsilon hepsilon hepsilonHalf
  let c : ℝ := min cDense (min (cJ / 64) (1 / (100 * (M : ℝ))))
  have hM2 : 2 ≤ M := le_trans hNtail2 (Nat.le_max_right _ _)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro n d hn hd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hdR : (0 : ℝ) < d := by positivity
  have hLd : 0 < logAlphabet d := logAlphabet_pos d (by omega)
  have hscale_nonneg : 0 ≤ (d : ℝ) / (n * logAlphabet d) := by positivity
  have hregular := regular_parametric_lower ⟨hepsilon, hepsilonHalf⟩ n d hn hd
  by_cases hnsmall : n < Ntail
  · have hnM : n ≤ M := le_trans (Nat.le_of_lt hnsmall) (Nat.le_max_right _ _)
    have hcM : c ≤ 1 / (100 * (M : ℝ)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have htarget : c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
        1 / (100 * (n : ℝ)) := by
      have hmin : min 1 ((d : ℝ) / (n * logAlphabet d)) ≤ 1 := min_le_left _ _
      have hnM' : (n : ℝ) ≤ M := by exact_mod_cast hnM
      have hMpos : (0 : ℝ) < M := by positivity
      calc
        c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤ c := by
          nlinarith [mul_le_mul_of_nonneg_left hmin hc.le]
        _ ≤ 1 / (100 * (M : ℝ)) := hcM
        _ ≤ 1 / (100 * (n : ℝ)) := by
          apply one_div_le_one_div_of_le <;> nlinarith
    exact htarget.trans hregular
  have hnlarge : Ntail ≤ n := Nat.le_of_not_gt hnsmall
  by_cases hdsmall : d < D
  · have hdM : d ≤ M := le_trans (Nat.le_of_lt hdsmall) (Nat.le_max_left _ _)
    have hcM : c ≤ 1 / (100 * (M : ℝ)) :=
      le_trans (min_le_right _ _) (min_le_right _ _)
    have hdM' : (d : ℝ) ≤ M := by exact_mod_cast hdM
    have htarget : c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
        1 / (100 * (n : ℝ)) := by
      calc
        c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
            c * ((d : ℝ) / (n * logAlphabet d)) := by
          gcongr
          exact min_le_right _ _
        _ ≤ (1 / (100 * (M : ℝ))) * ((d : ℝ) / (n * logAlphabet d)) := by
          gcongr
        _ ≤ 1 / (100 * (n : ℝ)) := by
          have hLone := logAlphabet_one_le d (by omega)
          have hMpos : (0 : ℝ) < M := by positivity
          field_simp [ne_of_gt hnR, ne_of_gt hLd, ne_of_gt hMpos]
          nlinarith
    exact htarget.trans hregular
  have hdD : D ≤ d := Nat.le_of_not_gt hdsmall
  by_cases hdenseRegime : d ^ 2 < n
  · have hcert := hDense d n (le_trans (Nat.le_max_left _ _) hdD) hdenseRegime
    rcases hcert with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hfinal⟩
    have hcDense' : c ≤ cDense := min_le_left _ _
    have hcmp : c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
        cDense * d / (n * logAlphabet d) := by
      calc
        c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
            c * ((d : ℝ) / (n * logAlphabet d)) := by gcongr; exact min_le_right _ _
        _ ≤ cDense * d / (n * logAlphabet d) := by
          have := mul_le_mul_of_nonneg_right hcDense' hscale_nonneg
          simpa [mul_div_assoc] using this
    exact hcmp.trans hfinal
  have hn_dsq : n ≤ d ^ 2 := Nat.le_of_not_gt hdenseRegime
  have hlogHalf : logAlphabet d ≤ (d : ℝ) / 2 :=
    hDlog d (le_trans (Nat.le_max_right _ _) hdD)
  let Ln := Real.log (Real.exp 1 * (n : ℝ))
  have hLn : 0 < Ln := by
    dsimp [Ln]
    exact logAlphabet_pos n hn
  have hlogCompare : Ln ≤ 2 * logAlphabet d := by
    have hncast : (n : ℝ) ≤ (d : ℝ) ^ 2 := by exact_mod_cast hn_dsq
    have harg : Real.exp 1 * (n : ℝ) ≤ Real.exp 1 * (d : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left hncast (Real.exp_nonneg 1)
    have hmono := Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.exp 1 * (n : ℝ) by positivity)
      (show 0 < Real.exp 1 * (d : ℝ) ^ 2 by positivity) harg
    dsimp [Ln]
    rw [Real.log_mul (Real.exp_ne_zero 1) (by positivity : (d : ℝ) ^ 2 ≠ 0),
      Real.log_exp, Real.log_pow] at hmono
    rw [logAlphabet, Real.log_mul (Real.exp_ne_zero 1) (by positivity : (d : ℝ) ≠ 0),
      Real.log_exp]
    have hlogd0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ d))
    calc
      Real.log (Real.exp 1 * (n : ℝ)) ≤ 1 + 2 * Real.log (d : ℝ) := by
        simpa using hmono
      _ ≤ 2 * (1 + Real.log (d : ℝ)) := by linarith
  by_cases hsaturated : (n : ℝ) < (1 / 4 : ℝ) * d / logAlphabet d
  · let s := saturatedAlphabet n
    obtain ⟨hs2, hsd, hgate, hlogs, hratio⟩ :=
      saturatedAlphabet_properties n d (le_trans hNtail2 hnlarge) hd hsaturated
    let P0 := simplexPointMass s (by omega)
    have hraw := hJ s n hs2 hgate hlogs P0 P0
    have htail' := (htail n hnlarge).2
    have hfixed : cJ / 2 ≤ fixedL1MinimaxRisk n s := by
      have hmin : min 1 ((s : ℝ) / (n * Ln)) = 1 := min_eq_left hratio
      change cJ * min 1 ((s : ℝ) / (n * Ln)) -
        8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤ fixedL1MinimaxRisk n s at hraw
      rw [hmin] at hraw
      linarith
    have hpad := fixedL1MinimaxRisk_mono_alphabet (n := n) (s := s) (d := d)
      (by omega) hsd
    let Pd := simplexPointMass d (by omega)
    have htransfer := l1_minimax_transfer (n := n) hd
      ⟨hepsilon, hepsilonHalf⟩ Pd Pd
    have hobs : cJ / 32 ≤ minimaxRisk n d epsilon := by
      linarith [hfixed.trans hpad, htransfer]
    have hscaleOne : min 1 ((d : ℝ) / (n * logAlphabet d)) = 1 := by
      apply min_eq_left
      have : 4 < (d : ℝ) / (n * logAlphabet d) := by
        apply (lt_div_iff₀ (mul_pos hnR hLd)).2
        apply (lt_div_iff₀ hLd).mp at hsaturated
        nlinarith
      linarith
    rw [hscaleOne]
    have hcJ' : c ≤ cJ / 64 := le_trans (min_le_right _ _) (min_le_left _ _)
    nlinarith
  · have hgate : (1 / 4 : ℝ) * d / logAlphabet d ≤ n := le_of_not_gt hsaturated
    let P0 := simplexPointMass d (by omega)
    have hraw := hJ d n hd hgate hlogCompare P0 P0
    have htail' := (htail n hnlarge).1
    have hLn_le_d : Ln ≤ d := hlogCompare.trans (by linarith)
    have hinv : 1 / (n : ℝ) ≤ min 1 ((d : ℝ) / (n * Ln)) := by
      apply le_min
      · apply (div_le_iff₀ hnR).2
        simpa only [one_mul] using (show (1 : ℝ) ≤ n by exact_mod_cast hn)
      · apply (div_le_div_iff₀ hnR (mul_pos hnR hLn)).2
        nlinarith
    have hfixed : cJ / 2 * min 1 ((d : ℝ) / (n * Ln)) ≤
        fixedL1MinimaxRisk n d := by
      change cJ * min 1 ((d : ℝ) / (n * Ln)) -
        8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤ fixedL1MinimaxRisk n d at hraw
      have htailBound : 8 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤
          cJ / 2 * min 1 ((d : ℝ) / (n * Ln)) := by
        calc
          _ ≤ cJ / (2 * n) := htail'
          _ = cJ / 2 * (1 / n) := by ring
          _ ≤ _ := by gcongr
      linarith
    have hratioCompare : (d : ℝ) / (n * logAlphabet d) ≤
        2 * (d / (n * Ln)) := by
      rw [show 2 * ((d : ℝ) / (n * Ln)) = (2 * d) / (n * Ln) by ring]
      apply (div_le_div_iff₀ (mul_pos hnR hLd) (mul_pos hnR hLn)).2
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hlogCompare hnR.le) hdR.le
      nlinarith [hmul]
    have hminCompare : min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
        2 * min 1 ((d : ℝ) / (n * Ln)) := by
      by_cases hbig : 1 ≤ (d : ℝ) / (n * Ln)
      · rw [min_eq_left hbig]
        exact (min_le_left _ _).trans (by norm_num)
      · rw [min_eq_right (le_of_not_ge hbig)]
        exact (min_le_right _ _).trans hratioCompare
    have htransfer := l1_minimax_transfer (n := n) hd
      ⟨hepsilon, hepsilonHalf⟩ P0 P0
    have hcJ' : c ≤ cJ / 64 := le_trans (min_le_right _ _) (min_le_left _ _)
    calc
      c * min 1 ((d : ℝ) / (n * logAlphabet d)) ≤
          cJ / 64 * (2 * min 1 ((d : ℝ) / (n * Ln))) := by gcongr
      _ ≤ fixedL1MinimaxRisk n d / 16 := by nlinarith [hfixed]
      _ ≤ minimaxRisk n d epsilon := htransfer

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
