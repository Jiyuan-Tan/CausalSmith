module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SelectorExpectationRates

/-! # Uniform frontier bound for the observable block selector -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- A nonempty block converts inverse length into the list-size coordinate using the universal
logarithmic block-count constant in equation (17). For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the time horizon assumption](hyp:hT),
[the candidate-policy count assumption](hyp:hM), and [the sample size assumption](hyp:hn), this
establishes [the selector inv block len bound list coordinate result](goal). -/
-- @node: selector_inv_blockLen_le_list_coordinate
lemma selector_inv_blockLen_le_list_coordinate (T M : Nat) (hT : 0 < T)
    (hM : 2 ≤ M) (hn : 1 ≤ blockLen T M) :
    1 / (blockLen T M : ℝ) ≤
      (2 * (2 + 4 / Real.log 2)) * (Real.log (M : ℝ) / T) := by
  have hhalf := selector_blockLen_ge_half_ratio T M hn
  have hB := (selector_numBlocks_log_bounds M hM).2
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hnR : (0 : ℝ) < blockLen T M := by exact_mod_cast (by omega : 0 < blockLen T M)
  have hBR : (0 : ℝ) < numBlocks M := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (selector_numBlocks_ge_three M))
  have hprod := (div_le_iff₀ (by positivity : 0 < 2 * (numBlocks M : ℝ))).mp hhalf
  apply (div_le_iff₀ hnR).mpr
  have hratio : (T : ℝ) ≤
      (2 * (2 + 4 / Real.log 2) * Real.log (M : ℝ)) * (blockLen T M : ℝ) := by
    nlinarith
  have hd := (div_le_div_of_nonneg_right hratio hTR.le)
  have hid : ((2 * (2 + 4 / Real.log 2) * Real.log (M : ℝ)) *
      (blockLen T M : ℝ)) / T =
      (2 * (2 + 4 / Real.log 2) * (Real.log (M : ℝ) / T)) * (blockLen T M : ℝ) := by ring
  simpa only [div_self hTR.ne', hid] using hd

/-- Both block-rate coordinates transfer to log(M)/T with one universal factor; the exponent
lies between zero and one. For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the time horizon assumption](hyp:hT),
[the candidate-policy count assumption](hyp:hM), and [the sample size assumption](hyp:hn), this
establishes [the selector block rate bound list rate result](goal). -/
-- @node: selector_block_rate_le_list_rate
lemma selector_block_rate_le_list_rate (T M : Nat) (t0 zeta C : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (hT : 0 < T) (hM : 2 ≤ M) (hn : 1 ≤ blockLen T M) :
    Real.sqrt (1 / (blockLen T M : ℝ)) +
        overlapRadius C ^ (1 - rateExponent t0 zeta) *
          (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2)) ≤
      (2 * (2 + 4 / Real.log 2)) *
        (Real.sqrt (Real.log (M : ℝ) / T) +
          overlapRadius C ^ (1 - rateExponent t0 zeta) *
            (Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) := by
  let H := 2 * (2 + 4 / Real.log 2)
  let u := Real.log (M : ℝ) / T
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hH : 1 ≤ H := by
    have hx : 0 ≤ 4 / Real.log (2 : ℝ) := by positivity
    dsimp [H]
    linarith
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hq : 0 ≤ overlapRadius C := by unfold overlapRadius; apply div_nonneg <;> linarith
  have hβ0 : 0 ≤ rateExponent t0 zeta / 2 := by unfold rateExponent; positivity
  have hβ1 : rateExponent t0 zeta / 2 ≤ 1 := by
    unfold rateExponent
    have hden : 0 < 2 + t0 * zeta := by positivity
    have hb : (2 : ℝ) / (2 + t0 * zeta) ≤ 1 :=
      (div_le_one hden).mpr (by nlinarith [mul_pos ht0 hzeta])
    linarith
  have hinv := selector_inv_blockLen_le_list_coordinate T M hT hM hn
  change 1 / (blockLen T M : ℝ) ≤ H * u at hinv
  have hs : Real.sqrt (1 / (blockLen T M : ℝ)) ≤ H * Real.sqrt u := by
    calc
      _ ≤ Real.sqrt (H * u) := Real.sqrt_le_sqrt hinv
      _ = Real.sqrt H * Real.sqrt u := Real.sqrt_mul (by positivity) u
      _ ≤ H * Real.sqrt u := mul_le_mul_of_nonneg_right
        (Real.sqrt_le_self_iff.mpr (Or.inr hH)) (Real.sqrt_nonneg _)
  have hp : (blockLen T M : ℝ) ^ (-(rateExponent t0 zeta / 2)) ≤
      H * u ^ (rateExponent t0 zeta / 2) := by
    rw [Real.rpow_neg_eq_inv_rpow, ← one_div]
    calc
      _ ≤ (H * u) ^ (rateExponent t0 zeta / 2) := Real.rpow_le_rpow (by positivity) hinv hβ0
      _ = H ^ (rateExponent t0 zeta / 2) * u ^ (rateExponent t0 zeta / 2) :=
        Real.mul_rpow (by positivity) hu
      _ ≤ H * u ^ (rateExponent t0 zeta / 2) := mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hβ1)
        (Real.rpow_nonneg hu _)
  have hp' := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hq (1 - rateExponent t0 zeta))
  change _ ≤ H * (Real.sqrt u + overlapRadius C ^ (1 - rateExponent t0 zeta) * u ^ (rateExponent t0 zeta / 2))
  nlinarith

/-- Short blocks force log(M)/T above a regime-only positive threshold. This is the small-block
case after equation (18). For [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the n0](hyp:n0), [the time horizon assumption](hyp:hT),
[the candidate-policy count assumption](hyp:hM), [the n0 assumption](hyp:hn0), and
[the sample size assumption](hyp:hn), this establishes
[the selector small block coordinate lower result](goal). -/
-- @node: selector_small_block_coordinate_lower
lemma selector_small_block_coordinate_lower (T M n0 : Nat) (hT : 0 < T)
    (hM : 2 ≤ M) (hn0 : 0 < n0) (hn : blockLen T M < n0) :
    1 / ((2 + 4 / Real.log 2) * (n0 : ℝ)) ≤ Real.log (M : ℝ) / T := by
  have hratio := selector_blockLen_ratio_lt T M
  have hnR : (blockLen T M : ℝ) + 1 ≤ n0 := by exact_mod_cast (by omega : blockLen T M + 1 ≤ n0)
  have hBR : (0 : ℝ) < numBlocks M := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 3) (selector_numBlocks_ge_three M))
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hn0R : (0 : ℝ) < n0 := by exact_mod_cast hn0
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hB := (selector_numBlocks_log_bounds M hM).2
  have hprod := (div_lt_iff₀ hBR).mp (hratio.trans_le hnR)
  apply (div_le_div_iff₀ (by positivity) hTR).mpr
  nlinarith

-- @node: thm:observable-selector-upper
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the observable selector upper result](goal). -/
theorem observable_selector_upper (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ (Ku : ℝ) (Tu : Nat), 0 < Ku ∧
      ∀ (T M : Nat) (C : ℝ), (hT : max 1 Tu ≤ T) → (hM : 2 ≤ M) → (hC : 1 ≤ C) →
        Causalean.Stat.worstCaseRiskReal
          (fun (sel : ObservableSelector T M)
            (m : {m : ModelIndex T M // PolicyListClass t0 zeta C m}) ↦
            expectedRegret sel m.1)
          (blockSelector T M (by omega) t0 zeta C) ≤
            Ku * (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) := by
  classical
  obtain ⟨K, n0, hK, hn0, hrate⟩ := selector_expectedRegret_block_rate t0 zeta ht0 hzeta
  let cB := 2 + 4 / Real.log 2
  let δ := min 1 (Real.sqrt (1 / (cB * (n0 : ℝ))))
  let Ku := K * (2 * cB) + δ⁻¹ + 1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hn0R : (0 : ℝ) < n0 := by exact_mod_cast (by omega : 0 < n0)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKu : 0 < Ku := by dsimp [Ku]; positivity
  have hKlarge : K * (2 * cB) ≤ Ku := by
    have : 0 < δ⁻¹ := inv_pos.mpr hδ
    dsimp [Ku]
    linarith
  have hKsmall : δ⁻¹ ≤ Ku := by
    have : 0 < K * (2 * cB) := by positivity
    dsimp [Ku]
    linarith
  have hKu1 : 1 ≤ Ku := by
    have : 0 < K * (2 * cB) + δ⁻¹ := by positivity
    dsimp [Ku]
    linarith
  refine ⟨Ku, 1, hKu, ?_⟩
  intro T M C hT hM hC
  have hTpos : 0 < T := by omega
  have hq : 0 ≤ overlapRadius C := by unfold overlapRadius; apply div_nonneg <;> linarith
  let f := Real.sqrt (Real.log (M : ℝ) / T) +
    overlapRadius C ^ (1 - rateExponent t0 zeta) *
      (Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hF : 0 ≤ (regretFrontier T M t0 zeta C ht0 hzeta hC (by omega) hM) := by
    change 0 ≤ min 1 f
    exact le_min (by norm_num) hf
  rcases isEmpty_or_nonempty {m : ModelIndex T M // PolicyListClass t0 zeta C m} with h | h
  · letI := h
    rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
    exact mul_nonneg hKu.le hF
  · letI := h
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    have hunit := (selector_expectedRegret_unit t0 zeta C
      (blockSelector T M (by omega) t0 zeta C) m.1 m.2).2
    change expectedRegret _ m.1 ≤ Ku * min 1 f
    by_cases hf1 : 1 ≤ f
    · rw [min_eq_left hf1]
      simpa only [mul_one] using hunit.trans hKu1
    · rw [min_eq_right (le_of_not_ge hf1)]
      by_cases hn : n0 ≤ blockLen T M
      · have hr := hrate C m.1 m.2 hn
        have hcomp := selector_block_rate_le_list_rate T M t0 zeta C ht0 hzeta hC
          hTpos hM (by omega)
        change _ ≤ (2 * cB) * f at hcomp
        calc
          _ ≤ _ := hr
          _ ≤ K * ((2 * cB) * f) := mul_le_mul_of_nonneg_left hcomp hK.le
          _ = (K * (2 * cB)) * f := by ring
          _ ≤ Ku * f := mul_le_mul_of_nonneg_right hKlarge hf
      · have hlower := selector_small_block_coordinate_lower T M n0 hTpos hM
          (by omega) (by omega)
        change 1 / (cB * (n0 : ℝ)) ≤ Real.log (M : ℝ) / T at hlower
        have hδf : δ ≤ f := by
          calc
            δ ≤ Real.sqrt (1 / (cB * (n0 : ℝ))) := min_le_right _ _
            _ ≤ Real.sqrt (Real.log (M : ℝ) / T) := Real.sqrt_le_sqrt hlower
            _ ≤ f := by
              dsimp [f]
              exact le_add_of_nonneg_right (by positivity)
        have hone : 1 ≤ δ⁻¹ * f := by
          have hh := mul_le_mul_of_nonneg_left hδf (inv_nonneg.mpr hδ.le)
          simpa only [inv_mul_cancel₀ hδ.ne'] using hh
        exact hunit.trans (hone.trans (mul_le_mul_of_nonneg_right hKsmall hf))

end CausalSmith.Stat.PomdpPolicyclassRegret
