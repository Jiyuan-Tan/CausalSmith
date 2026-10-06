module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_FiniteBandwidth
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_LowerPairMembership
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.T_UnknownTailAdaptation
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.TwoLawRisk
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.BandwidthRate
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.MinimaxLower

/-! # Sharp global-tail minimax rate -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

-- @node: fixed_bandwidth_rate_bound
/-- The expectation bound at the rounded balancing bandwidth attains the sharp
rate uniformly over the law class, as in roadmap equation (S7). -/
lemma fixed_bandwidth_rate_bound (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ∀ P : Law d, LawClass d β γ C L M P →
        lawRisk P
          (fun sample : Fin n → Obs d => balancedEstimator sample (fixedLevel d n β γ) β M)
          P.mu1 ≤ ENNReal.ofReal (K * rate d n β γ) := by
  obtain ⟨B₀, K₀, c₀, hB₀, hK₀, hc₀, hfinite⟩ :=
    finite_bandwidth d β γ C L M hparam
  rcases hparam with ⟨hd, hβ, hγ, hC, hL, hM⟩
  refine ⟨K₀ * (L + (2 : ℝ) ^ (effectiveDimension d γ / 2) * M), by positivity, ?_⟩
  intro n hn P hP
  apply ((hfinite n (fixedLevel d n β γ) 1 hn le_rfl).2 P hP).trans
  apply ENNReal.ofReal_le_ofReal
  have hb := rateBandwidth_bias_le hd hn hβ hγ
  have hv := rateBandwidth_stochastic_le hd hn hβ hγ
  change (rateBandwidth d n β γ) ^ β ≤ rate d n β γ at hb
  change K₀ * (L * (rateBandwidth d n β γ) ^ β +
    M / Real.sqrt ((n : ℝ) * (rateBandwidth d n β γ) ^ (effectiveDimension d γ))) ≤ _
  have hvM := mul_le_mul_of_nonneg_left hv hM.le
  have hbL := mul_le_mul_of_nonneg_left hb hL.le
  calc
    _ ≤ K₀ * (L * rate d n β γ +
        M * ((2 : ℝ) ^ (effectiveDimension d γ / 2) * rate d n β γ)) := by
      apply mul_le_mul_of_nonneg_left _ hK₀.le
      simp only [div_eq_mul_inv, one_mul] at hvM ⊢
      exact add_le_add hbL hvM
    _ = _ := by ring

-- @node: minimaxRisk_le_of_admissible
/-- A measurable candidate with a uniform class risk bound gives the same
minimax upper bound, by roadmap (S9). -/
lemma minimaxRisk_le_of_admissible {d n : ℕ} {β γ C L M : ℝ}
    (f : (Fin n → Obs d) → (Fin d → ℝ) → ℝ)
    (hf : AdmissibleEstimator d n β γ C L M f) (B : ENNReal)
    (hbound : ∀ P : Law d, LawClass d β γ C L M P → lawRisk P f P.mu1 ≤ B) :
    minimaxRisk d n β γ C L M ≤ B := by
  unfold minimaxRisk
  apply iInf_le_of_le f
  apply iInf_le_of_le hf
  exact iSup_le fun P => iSup_le fun hP => hbound P hP

-- @node: thm:sharp-minimax
/-- Uniform class constants sandwich the minimax risk. The dyadic
fixed-bandwidth fit attains the upper bound, and one parameter-free selector
adapts separately to each finite tail class. The balanced fit's pointwise and
loss measurability are explicit regularity bookkeeping for the total sample
map asserted measurable just before roadmap (S9). -/
theorem sharp_minimax (d : ℕ) (β γ C L M : ℝ)
    (hparam : ParameterDomain d β γ C L M)
    (hfit_meas : ∀ n : ℕ, 1 ≤ n →
      AdmissibleEstimator d n β γ C L M
        (fun sample : Fin n → Obs d =>
          balancedEstimator sample (fixedLevel d n β γ) β M)) :
    (∃ c K : ℝ, 0 < c ∧ c < K ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n →
        ENNReal.ofReal (c * rate d n β γ) ≤ minimaxRisk d n β γ C L M ∧
        minimaxRisk d n β γ C L M ≤ ENNReal.ofReal (K * rate d n β γ) ∧
        (∀ P : Law d, LawClass d β γ C L M P →
          lawRisk P
            (fun sample : Fin n → Obs d => balancedEstimator sample (fixedLevel d n β γ) β M)
            P.mu1 ≤ ENNReal.ofReal (K * rate d n β γ))) ∧
    (∀ γ' C' : ℝ, 1 < γ' → 1 ≤ C' →
      ∃ K' : ℝ, 0 < K' ∧ ∃ N' : ℕ, ∀ n : ℕ, N' ≤ n →
        ∀ P : Law d, LawClass d β γ' C' L M P →
          lawRisk P (fun sample : Fin n → Obs d => selectorHandle sample β M) P.mu1 ≤
            ENNReal.ofReal (K' * rate d n β γ')) := by
  constructor
  · obtain ⟨Kfixed, hKfixed, hfixed⟩ :=
      fixed_bandwidth_rate_bound d β γ C L M hparam
    suffices hminimax : ∃ c K : ℝ, 0 < c ∧ c < K ∧ Kfixed ≤ K ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          ENNReal.ofReal (c * rate d n β γ) ≤ minimaxRisk d n β γ C L M ∧
          minimaxRisk d n β γ C L M ≤ ENNReal.ofReal (K * rate d n β γ) by
      obtain ⟨c, K, hc, hcK, hKK, N₀, hbounds⟩ := hminimax
      refine ⟨c, K, hc, hcK, max N₀ 1, ?_⟩
      intro n hn
      have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
      have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
      refine ⟨(hbounds n hn₀).1, (hbounds n hn₀).2, ?_⟩
      intro P hP
      apply (hfixed n hn1 P hP).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right hKK (by unfold rate; positivity)
    obtain ⟨c, hc, hlower⟩ := minimax_lower_rate d β γ C L M hparam
    refine ⟨c, max Kfixed (c + 1), hc, ?_, le_max_left _ _, 1, ?_⟩
    · exact (by linarith : c < c + 1).trans_le (le_max_right _ _)
    · intro n hn
      refine ⟨hlower n hn, ?_⟩
      apply minimaxRisk_le_of_admissible
        (fun sample : Fin n → Obs d =>
          balancedEstimator sample (fixedLevel d n β γ) β M) (hfit_meas n hn)
      intro P hP
      apply (hfixed n hn P hP).trans
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_right (le_max_left _ _)
        (by unfold rate; positivity)
  · exact unknown_tail_adaptation d β L M hparam.1 hparam.2.1
      hparam.2.2.2.2.1 hparam.2.2.2.2.2

end CausalSmith.Stat.GlobalTailDesignRobustCate
