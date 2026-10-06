module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.BoundedRoughCalibration

/-! Activity calibration for the moment-normalized tail copula converse. -/
public section
set_option maxRecDepth 2000
noncomputable section
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The tail amplitude coefficient is at most two to the power minus forty-eight. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: tail_copula_amplitude_product
lemma tail_copula_amplitude_product (v : Params) (hv : v.Valid) (K : ℕ) (hK : 0 < K) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ (2:ℝ)^(-48:ℤ) ∧
      (legalityA v K)^4*(1/16:ℝ)^4*(legalityRarity v K)^2 =
        c*(K:ℝ)^(-(4*v.α+2*v.β/qExp v)) := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  refine ⟨(16:ℝ)^(-8:ℤ)*(16:ℝ)^(-2/qExp v), by positivity, ?_, ?_⟩
  · have hex : -2/qExp v ≤ -4 := (div_le_iff₀ hq).mpr (by linarith)
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 16) hex
    norm_num at hh ⊢
    linarith
  · unfold legalityA legalityRarity legalityB
    have ht : (16:ℝ)*((K:ℝ)^(-v.β)/256) = (16:ℝ)^(-1:ℝ)*(K:ℝ)^(-v.β) := by norm_num; ring
    rw [ht, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16), ← Real.rpow_mul hk.le]
    simp only [div_pow, mul_pow]
    rw [← Real.rpow_natCast ((K:ℝ)^(-v.α)), ← Real.rpow_mul hk.le,
      ← Real.rpow_natCast ((16:ℝ)^((-1:ℝ)*(1/qExp v))),
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 16),
      ← Real.rpow_natCast ((K:ℝ)^(-v.β*(1/qExp v))), ← Real.rpow_mul hk.le]
    norm_num only [Nat.cast_ofNat]
    have hr : (K:ℝ)^(-v.α*4)*(K:ℝ)^(-v.β*(1/qExp v)*2) =
        (K:ℝ)^(-(4*v.α+2*v.β/qExp v)) := by
      rw [← Real.rpow_add hk]; congr 1; ring
    have hc : (16:ℝ)^((-1:ℝ)*(1/qExp v)*2) = (16:ℝ)^(-2/qExp v) := by
      congr 1; ring
    rw [hc]
    calc
      _ = (16:ℝ)^(-8:ℤ)*(16:ℝ)^(-2/qExp v)*
          ((K:ℝ)^(-v.α*4)*(K:ℝ)^(-v.β*(1/qExp v)*2)) := by norm_num; ring
      _ = _ := by rw [hr]; norm_num

/-- The first tail activity exponent dominates the rough denominator. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: tail_rough_denominator_bound
lemma tail_rough_denominator_bound (v : Params) (hv : v.Valid) :
    Dp v ≤ 1+(4*v.α+2*v.β/qExp v) := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hb : 2*v.β ≤ v.β/qExp v := (le_div_iff₀ hq).mpr (by nlinarith [hv.2.2.1.1])
  have hs : sumReg v/(2*v.γ) ≤ 2*sumReg v :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [hv.2.2.2.1])
  unfold Dp sumReg at *
  simp only [mul_div_assoc] at *
  linarith

/-- Both full-record activities fit the small fixed budgets for the tail tuning. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: tail_rough_activity_budgets
lemma tail_rough_activity_budgets (v : Params) (hv : v.Valid)
    (hf : Fphase v < 1) (n : ℕ) (hn : 2 ≤ n)
    (hlarge : Nlow v ≤ n) :
    activityBudgetA n (roughK n v) (legalityA v (roughK n v))
      (1/16) (legalityRarity v (roughK n v)) ≤ (2:ℝ)^(-10:ℤ)/Hfine ∧
    activityBudgetB n (roughK n v) (roughM n v) (legalityA v (roughK n v))
      (1/16) (legalityRarity v (roughK n v)) ≤ 2^13/Hfine^2 := by
  let K := roughK n v
  let M := roughM n v
  have hr := rough_rank_legality v hv hf n hn hlarge
  have hK : 0 < K := by have := hr.1.2.2.1; have := hr.1.2.2.2.1; dsimp [K]; omega
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hm : (0:ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hr.1.2.2.2.1)
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hp := rough_sample_power_budget v hv hf n hn
  obtain ⟨c, hc0, hc, hprod⟩ := tail_copula_amplitude_product v hv K hK
  have hA : activityBudgetA n K (legalityA v K) (1/16) (legalityRarity v K) =
      (2:ℝ)^38*c*(n:ℝ)^2*(K:ℝ)^(-(1+(4*v.α+2*v.β/qExp v))) := by
    unfold activityBudgetA
    rw [show (2:ℝ)^38*legalityA v K^4*(1/16)^4*(legalityRarity v K)^2 =
      (2:ℝ)^38*(legalityA v K^4*(1/16)^4*(legalityRarity v K)^2) by ring, hprod]
    have hid : (K:ℝ)^(-(4*v.α+2*v.β/qExp v))/(K:ℝ) = (K:ℝ)^(-(1+(4*v.α+2*v.β/qExp v))) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hk]
      congr 1; ring
    calc
      _ = (2:ℝ)^38*c*(n:ℝ)^2*((K:ℝ)^(-(4*v.α+2*v.β/qExp v))/(K:ℝ)) := by norm_num; ring
      _ = _ := by rw [hid]
  have hB : activityBudgetB n K M (legalityA v K) (1/16) (legalityRarity v K) =
      (2:ℝ)^56*c*(n:ℝ)^4*(K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v)))/(M:ℝ) := by
    unfold activityBudgetB
    rw [show (2:ℝ)^56*legalityA v K^4*(1/16)^4*(legalityRarity v K)^2 =
      (2:ℝ)^56*(legalityA v K^4*(1/16)^4*(legalityRarity v K)^2) by ring, hprod]
    have hid : (K:ℝ)^(-(4*v.α+2*v.β/qExp v))/(K:ℝ)^2 = (K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v))) := by
      rw [← Real.rpow_two, ← Real.rpow_sub hk]
      congr 1; ring
    calc
      _ = (2:ℝ)^56*c*(n:ℝ)^4*((K:ℝ)^(-(4*v.α+2*v.β/qExp v))/(K:ℝ)^2)/(M:ℝ) := by norm_num; ring
      _ = _ := by rw [hid]
  constructor
  · rw [hA]
    have hex := tail_rough_denominator_bound v hv
    have hpow : (K:ℝ)^(-(1+(4*v.α+2*v.β/qExp v))) ≤ (K:ℝ)^(-Dp v) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (neg_le_neg hex)
    calc
      _ ≤ (2:ℝ)^(-10:ℤ)*(n:ℝ)^2*(K:ℝ)^(-(1+(4*v.α+2*v.β/qExp v))) := by
        gcongr
        norm_num at hc ⊢
        linarith
      _ ≤ (2:ℝ)^(-10:ℤ)*((n:ℝ)^2*(K:ℝ)^(-Dp v)) := by
        rw [← mul_assoc]; gcongr
      _ ≤ (2:ℝ)^(-10:ℤ)*(1/Hfine) := mul_le_mul_of_nonneg_left hp.1 (by positivity)
      _ = _ := by ring
  · rw [hB]
    have hl : (0:ℝ) < (K:ℝ)^(sumReg v/v.γ)/32 := by positivity
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ (2:ℝ)^56*c*(n:ℝ)^4*(K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v)))) hl hr.2
    have hid : (2:ℝ)^56*c*(n:ℝ)^4*(K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v))) /
        ((K:ℝ)^(sumReg v/v.γ)/32) =
        (2:ℝ)^61*c*((n:ℝ)^4*(K:ℝ)^(-(2*Dp v))) := by
      have hex : -(2+(4*v.α+2*v.β/qExp v)) + -(sumReg v/v.γ) = -(2*Dp v) := by
        unfold Dp
        ring
      have hrat : (K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v)))/(K:ℝ)^(sumReg v/v.γ) =
          (K:ℝ)^(-(2*Dp v)) := by
        rw [← Real.rpow_sub hk]
        rw [sub_eq_add_neg, hex]
      calc
        _ = (2:ℝ)^61*c*(n:ℝ)^4*((K:ℝ)^(-(2+(4*v.α+2*v.β/qExp v)))/(K:ℝ)^(sumReg v/v.γ)) := by
          norm_num; ring
        _ = _ := by rw [hrat]; ring
    calc
      _ ≤ _ := hdiv
      _ = _ := hid
      _ ≤ (2:ℝ)^13*((n:ℝ)^4*(K:ℝ)^(-(2*Dp v))) := by
        gcongr
        norm_num at hc ⊢
        linarith
      _ ≤ (2:ℝ)^13*(1/Hfine^2) := mul_le_mul_of_nonneg_left hp.2 (by positivity)
      _ = _ := by ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma
