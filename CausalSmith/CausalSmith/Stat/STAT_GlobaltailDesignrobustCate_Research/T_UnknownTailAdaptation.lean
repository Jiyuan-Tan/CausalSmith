module
public import CausalSmith.Stat.STAT_GlobaltailDesignrobustCate_Research.Helpers.AdaptationTail

/-! # Selection without the tail parameters -/
public section
namespace CausalSmith.Stat.GlobalTailDesignRobustCate

open MeasureTheory
open scoped ENNReal

-- @node: thm:unknown-tail-adaptation
/-- The fixed count-based selector uses only `d`, `β`, and `M`. For each
fixed global-tail class it eventually reaches the corresponding log-free rate. -/
theorem unknown_tail_adaptation (d : ℕ) (β L M : ℝ)
    (hd : 1 ≤ d) (hβ : 0 < β) (hL : 0 < L) (hM : 0 < M) :
    ∀ (γ C : ℝ), 1 < γ → 1 ≤ C →
      ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ∀ P : Law d, LawClass d β γ C L M P →
          lawRisk P (fun sample : Fin n → Obs d => selectorHandle sample β M) P.mu1 ≤
            ENNReal.ofReal (K * rate d n β γ) := by
  -- Roadmap (6) and (10), with the deterministic analysis-scale multiplier
  -- absorbed into the constants and the exponential remainder bounded by the rate.
  suffices hselected : ∀ (γ C : ℝ), 1 < γ → 1 ≤ C →
      ∃ B K c Kbad : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧ 0 < Kbad ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → 1 ≤ n →
          ∀ P : Law d, LawClass d β γ C L M P →
            AEMeasurable
              (fun sample : Fin n → Obs d => supLoss (selectorHandle sample β M) P.mu1)
              (P.sample n) ∧
            ∃ A : Set (Fin n → Obs d), MeasurableSet A ∧
              (P.sample n).real Aᶜ ≤ Kbad * rate d n β γ ∧
              ∀ u : ℝ, 1 ≤ u → u * (M * rate d n β γ) ≤ 2 * M →
                (P.sample n).real
                  {sample | sample ∈ A ∧
                    ENNReal.ofReal (B * L * rate d n β γ +
                      u * (M * rate d n β γ)) <
                        supLoss (selectorHandle sample β M) P.mu1} ≤
                  K * Real.exp (-c * u ^ 2) by
    intro γ C hγ hC
    obtain ⟨B, K, c, Kbad, hB, hK, hc, hKbad, N₀, hselected⟩ :=
      hselected γ C hγ hC
    let G : ℝ := (1 + K) * Real.exp c / c
    refine ⟨G * (B * L + M) + 2 * M * Kbad, by dsimp [G]; positivity,
      max N₀ 1, ?_⟩
    intro n hn P hP
    have hn₀ : N₀ ≤ n := (le_max_left _ _).trans hn
    have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
    obtain ⟨hmeas, A, hA, hbad, htail⟩ := hselected n hn₀ hn1 P hP
    let : IsProbabilityMeasure (P.sample n) :=
      sample_isProbabilityMeasure P hP.iid hP.consistency (by omega)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hr : 0 < rate d n β γ := by unfold rate; positivity
    have hmoment := gaussianTail_goodEvent_lintegral_le (P.sample n)
      (fun sample : Fin n → Obs d => supLoss (selectorHandle sample β M) P.mu1)
      A hA hmeas (B * L * rate d n β γ) (M * rate d n β γ) K c (2 * M)
      (by positivity) (by positivity) hK hc (by positivity)
      (fun sample => selectorHandle_supLoss_le_two_mul sample β γ C L M P hP) htail
    apply hmoment.trans
    apply ENNReal.ofReal_le_ofReal
    change G * (B * L * rate d n β γ + M * rate d n β γ) +
      2 * M * (P.sample n).real Aᶜ ≤ _
    calc
      _ ≤ G * (B * L * rate d n β γ + M * rate d n β γ) +
          2 * M * (Kbad * rate d n β γ) := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_left hbad (by positivity)
      _ = _ := by ring
  intro γ C hγ hC
  obtain ⟨A, Kbad, hA, hKbad, Nscale, hscale⟩ :=
    selector_analysisScale_failure_rate d β γ C L M ⟨hd, hβ, hγ, hC, hL, hM⟩
  -- Count failure and adaptive-loss measurability are closed. Only the
  -- good-event outcome deviation is needed at the analysis scale.
  suffices hgood : ∃ B K c : ℝ, 0 < B ∧ 0 < K ∧ 0 < c ∧
      ∃ Nnoise : ℕ, ∀ n : ℕ, Nnoise ≤ n → 1 ≤ n →
        ∀ j : ℕ, j ≤ selectorMaxLevel d n β →
          A * rateWidth d n β γ ≤ dyadicWidth j →
          dyadicWidth j < 2 * A * rateWidth d n β γ →
          ∀ P : Law d, LawClass d β γ C L M P →
            ∀ u : ℝ, 1 ≤ u → u * (M * rate d n β γ) ≤ 2 * M →
              (P.sample n).real
                {sample | selectorAdmissible sample j β ∧
                  ENNReal.ofReal (B * L * rate d n β γ +
                    u * (M * rate d n β γ)) <
                      supLoss (selectorHandle sample β M) P.mu1} ≤
                K * Real.exp (-c * u ^ 2) by
    obtain ⟨B, K, c, hB, hK, hc, Nnoise, hgood⟩ := hgood
    refine ⟨B, K, c, Kbad, hB, hK, hc, hKbad, max Nscale Nnoise, ?_⟩
    intro n hn hn1 P hP
    obtain ⟨j, hgrid, hlo, hhi, hmeasEvent, hbad⟩ :=
      hscale n ((le_max_left _ _).trans hn) hn1
    have htail :=
      hgood n ((le_max_right _ _).trans hn) hn1 j hgrid hlo hhi P hP
    refine ⟨(selectorHandle_supLoss_measurable β M P.mu1
      (holderOnCube_continuousOn hβ hP.treatedHolder)).aemeasurable,
      {sample | selectorAdmissible sample j β}, hmeasEvent, ?_, htail⟩
    exact hbad P hP
  obtain ⟨B, K, c, hB, hK, hc, htail⟩ := selectorHandle_goodEvent_gaussianTail
    d β γ C L M ⟨hd, hβ, hγ, hC, hL, hM⟩
  let F : ℝ := (2 * A) ^ β
  have hApos : 0 < A := by linarith
  have hF : 0 < F := by dsimp [F]; positivity
  refine ⟨B * F, K + Real.exp c, c / F ^ 2,
    by positivity, by positivity, by positivity, 0, ?_⟩
  intro n _ hn1 j hgrid hlo hhi P hP u hu hcut
  have hn : 0 < n := by omega
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hw : 0 < rateWidth d n β γ := by unfold rateWidth; positivity
  have hr : 0 < rate d n β γ := by unfold rate; positivity
  have hh : 0 < dyadicWidth j := by unfold dyadicWidth; positivity
  have hD := effectiveDimension_pos hd hγ
  have hden : 0 < 2 * β + effectiveDimension d γ := by linarith
  have hwide : rateWidth d n β γ ≤ dyadicWidth j := by
    apply le_trans _ hlo
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hw.le
  have hbalance : 1 ≤ (n : ℝ) * (dyadicWidth j) ^
      (effectiveDimension d γ + 2 * β) := by
    have heq := rateWidth_sample_balance hn1 hden.ne'
    rw [add_comm (2 * β)] at heq
    rw [← heq]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hw.le hwide (by linarith)) hn'.le
  have hbias : (dyadicWidth j) ^ β ≤ F * rate d n β γ := by
    calc
      _ ≤ (2 * A * rateWidth d n β γ) ^ β :=
        Real.rpow_le_rpow hh.le hhi.le hβ.le
      _ = _ := by rw [Real.mul_rpow (by positivity) hw.le, rateWidth_bias_eq hn1]
  let : IsProbabilityMeasure (P.sample n) :=
    sample_isProbabilityMeasure P hP.iid hP.consistency hn
  by_cases huF : F ≤ u
  · have hv : 1 ≤ u / F := (le_div_iff₀ hF).mpr (by simpa using huF)
    have ht : u / F * M * (dyadicWidth j) ^ β ≤ u * (M * rate d n β γ) := by
      have h := mul_le_mul_of_nonneg_left hbias
        (show 0 ≤ u / F * M by positivity)
      have heq : u / F * M * (F * rate d n β γ) = u * (M * rate d n β γ) := by
        field_simp
      exact h.trans_eq heq
    have hevent :
        {sample : Fin n → Obs d | selectorAdmissible sample j β ∧
          ENNReal.ofReal (B * F * L * rate d n β γ + u * (M * rate d n β γ)) <
            supLoss (selectorHandle sample β M) P.mu1} ⊆
        {sample : Fin n → Obs d | selectorAdmissible sample j β ∧
          ENNReal.ofReal (B * L * (dyadicWidth j) ^ β +
            u / F * M * (dyadicWidth j) ^ β) <
              supLoss (selectorHandle sample β M) P.mu1} := by
      intro sample hs
      refine ⟨hs.1, lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hs.2⟩
      have h := mul_le_mul_of_nonneg_left hbias (show 0 ≤ B * L by positivity)
      nlinarith only [h, ht]
    apply (measureReal_mono hevent (measure_ne_top _ _)).trans
    apply (htail n j P hP hn hgrid hbalance (u / F) hv (ht.trans hcut)).trans
    have heq : -c * (u / F) ^ 2 = -(c / F ^ 2) * u ^ 2 := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_nonneg c))
      (Real.exp_nonneg _)
  · have hu0 : 0 ≤ u := by linarith
    have hu2 : u ^ 2 ≤ F ^ 2 := by nlinarith
    have hexp : 1 ≤ Real.exp c * Real.exp (-(c / F ^ 2) * u ^ 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have h := mul_le_mul_of_nonneg_left hu2 (show 0 ≤ c / F ^ 2 by positivity)
      have heq : c / F ^ 2 * F ^ 2 = c := div_mul_cancel₀ c (ne_of_gt (sq_pos_of_pos hF))
      rw [heq] at h
      linarith
    apply (measureReal_le_one (μ := P.sample n)).trans
    apply hexp.trans
    exact mul_le_mul_of_nonneg_right (by linarith : Real.exp c ≤ K + Real.exp c)
      (Real.exp_nonneg _)


end CausalSmith.Stat.GlobalTailDesignRobustCate
