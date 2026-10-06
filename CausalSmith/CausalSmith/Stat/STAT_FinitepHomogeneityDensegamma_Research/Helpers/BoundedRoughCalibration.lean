module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ComponentOccupancy
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.RoughRanks

/-! Activity calibration for the separate bounded copula converse. -/
public section
noncomputable section
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Raising the fine target to the rough denominator controls both sample powers. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: rough_sample_power_budget
lemma rough_sample_power_budget (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    (n:ℝ)^2*(roughK n v:ℝ)^(-Dp v) ≤ 1/Hfine ∧
    (n:ℝ)^4*(roughK n v:ℝ)^(-(2*Dp v)) ≤ 1/Hfine^2 := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hKpos : (0:ℝ) < roughK n v := by
    have := (rough_fine_rank_bounds v hv hf n hn).2.2
    exact_mod_cast (by omega : 0 < roughK n v)
  have hD : 1 ≤ Dp v := by
    unfold Dp
    have ha := hv.2.1.1
    have hb := hv.2.2.1.1
    have h1 : 0 ≤ v.β/qExp v := by positivity
    have h2 : 0 ≤ sumReg v/(2*v.γ) := by positivity
    linarith
  have hH : 1 ≤ Hfine := by norm_num [Hfine]
  have hHpos : 0 < Hfine := by norm_num [Hfine]
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ Hfine*(n:ℝ)^(2/Dp v))
    (rough_fine_rank_bounds v hv hf n hn).1 hd.le
  rw [Real.mul_rpow hHpos.le (by positivity), ← Real.rpow_mul hnpos.le,
    div_mul_cancel₀ _ hd.ne', Real.rpow_two] at hpow
  have hh : Hfine ≤ Hfine^Dp v := by
    simpa using Real.rpow_le_rpow_of_exponent_le hH hD
  have hmain : Hfine*(n:ℝ)^2 ≤ (roughK n v:ℝ)^Dp v :=
    (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans hpow
  have hfirst : (n:ℝ)^2*(roughK n v:ℝ)^(-Dp v) ≤ 1/Hfine := by
    rw [Real.rpow_neg hKpos.le, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (by positivity) hHpos).mpr
    simpa [mul_comm] using hmain
  refine ⟨hfirst, ?_⟩
  have hsq := mul_self_le_mul_self (by positivity : 0 ≤ (n:ℝ)^2*(roughK n v:ℝ)^(-Dp v)) hfirst
  have hid : ((n:ℝ)^2*(roughK n v:ℝ)^(-Dp v))^2 =
      (n:ℝ)^4*(roughK n v:ℝ)^(-(2*Dp v)) := by
    rw [mul_pow, ← Real.rpow_natCast ((roughK n v:ℝ)^(-Dp v)), ← Real.rpow_mul hKpos.le]
    congr 1
    · ring
    · congr 1; ring
  simpa only [← sq, hid, div_pow, one_pow] using hsq

/-- The bounded amplitudes have the fourth-moment product specified by the roadmap. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: bounded_copula_amplitude_product
lemma bounded_copula_amplitude_product (v : Params) (K : ℕ) (hK : 0 < K) :
    (legalityA v K)^4*(2*legalityB v K)^4*(1/2:ℝ)^2 =
      (2:ℝ)^(-46:ℤ)*(K:ℝ)^(-4*sumReg v) := by
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  unfold legalityA legalityB
  simp only [div_pow, mul_pow]
  rw [← Real.rpow_natCast ((K:ℝ)^(-v.α)), ← Real.rpow_mul hk.le,
    ← Real.rpow_natCast ((K:ℝ)^(-v.β)), ← Real.rpow_mul hk.le]
  norm_num only [Nat.cast_ofNat]
  have hid : (K:ℝ)^(-v.α*4)*(K:ℝ)^(-v.β*4) = (K:ℝ)^(-4*sumReg v) := by
    rw [← Real.rpow_add hk]
    congr 1
    dsimp [sumReg]; ring
  calc
    _ = (2:ℝ)^(-46:ℤ)*((K:ℝ)^(-v.α*4)*(K:ℝ)^(-v.β*4)) := by norm_num; ring
    _ = _ := by rw [hid]; norm_num

/-- Dense effect smoothness makes the bounded first activity exponent at least the rough denominator. This statement assumes [the hw condition](hyp:hw). [This is the stated conclusion](goal). -/
-- @node: bounded_rough_denominator_bounds
lemma bounded_rough_denominator_bounds (w : Smooth3) (hw : w.Valid) :
    Dp (Params.ofBounded w) = 1+2*sumReg (Params.ofBounded w)+
      sumReg (Params.ofBounded w)/(2*w.γ) ∧
    Dp (Params.ofBounded w) ≤ 1+4*sumReg (Params.ofBounded w) := by
  have hg : 0 < w.γ := by linarith [hw.2.2.1]
  have hS : 0 < sumReg (Params.ofBounded w) := add_pos hw.1.1 hw.2.1.1
  have hid : Dp (Params.ofBounded w) = 1+2*sumReg (Params.ofBounded w)+
      sumReg (Params.ofBounded w)/(2*w.γ) := by
    norm_num [Dp, qExp, Params.ofBounded, sumReg]
    ring
  refine ⟨hid, ?_⟩
  rw [hid]
  have hdiv : sumReg (Params.ofBounded w)/(2*w.γ) ≤ 2*sumReg (Params.ofBounded w) :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith [hw.2.2.1])
  linarith

/-- Both full-record activities fit the small fixed budgets for the bounded tuning. This statement assumes [the hw condition](hyp:hw), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: bounded_rough_activity_budgets
lemma bounded_rough_activity_budgets (w : Smooth3) (hw : w.Valid)
    (hf : Fphase (Params.ofBounded w) < 1) (n : ℕ) (hn : 2 ≤ n)
    (hlarge : Nlow (Params.ofBounded w) ≤ n) :
    let v := Params.ofBounded w
    activityBudgetA n (roughK n v) (legalityA v (roughK n v))
      (2*legalityB v (roughK n v)) (1/2) ≤ (2:ℝ)^(-8:ℤ)/Hfine ∧
    activityBudgetB n (roughK n v) (roughM n v) (legalityA v (roughK n v))
      (2*legalityB v (roughK n v)) (1/2) ≤ 2^15/Hfine^2 := by
  dsimp only
  let v := Params.ofBounded w
  have hv : v.Valid := ⟨by norm_num [v, Params.ofBounded], hw⟩
  let K := roughK n v
  let M := roughM n v
  have hr := rough_rank_legality v hv hf n hn hlarge
  have hK : 0 < K := by have := hr.1.2.2.1; have := hr.1.2.2.2.1; dsimp [K]; omega
  have hk : (0:ℝ) < K := by exact_mod_cast hK
  have hm : (0:ℝ) < M := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hr.1.2.2.2.1)
  have hK1 : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hp := rough_sample_power_budget v hv hf n hn
  have hprod := bounded_copula_amplitude_product v K hK
  have hA : activityBudgetA n K (legalityA v K) (2*legalityB v K) (1/2) =
      (2:ℝ)^(-8:ℤ)*(n:ℝ)^2*(K:ℝ)^(-(1+4*sumReg v)) := by
    unfold activityBudgetA
    rw [show (2:ℝ)^38*legalityA v K^4*(2*legalityB v K)^4*(1/2)^2 =
      (2:ℝ)^38*(legalityA v K^4*(2*legalityB v K)^4*(1/2)^2) by ring, hprod]
    have hid : (K:ℝ)^(-4*sumReg v)/(K:ℝ) = (K:ℝ)^(-(1+4*sumReg v)) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add hk]
      congr 1; ring
    calc
      _ = (2:ℝ)^(-8:ℤ)*(n:ℝ)^2*((K:ℝ)^(-4*sumReg v)/(K:ℝ)) := by norm_num; ring
      _ = _ := by rw [hid]
  have hB : activityBudgetB n K M (legalityA v K) (2*legalityB v K) (1/2) =
      (2:ℝ)^10*(n:ℝ)^4*(K:ℝ)^(-(2+4*sumReg v))/(M:ℝ) := by
    unfold activityBudgetB
    rw [show (2:ℝ)^56*legalityA v K^4*(2*legalityB v K)^4*(1/2)^2 =
      (2:ℝ)^56*(legalityA v K^4*(2*legalityB v K)^4*(1/2)^2) by ring, hprod]
    have hid : (K:ℝ)^(-4*sumReg v)/(K:ℝ)^2 = (K:ℝ)^(-(2+4*sumReg v)) := by
      rw [← Real.rpow_two, ← Real.rpow_sub hk]
      congr 1; ring
    calc
      _ = (2:ℝ)^10*(n:ℝ)^4*((K:ℝ)^(-4*sumReg v)/(K:ℝ)^2)/(M:ℝ) := by norm_num; ring
      _ = _ := by rw [hid]
  constructor
  · rw [hA]
    have hex := (bounded_rough_denominator_bounds w hw).2
    have hpow : (K:ℝ)^(-(1+4*sumReg v)) ≤ (K:ℝ)^(-Dp v) :=
      Real.rpow_le_rpow_of_exponent_le hK1 (neg_le_neg hex)
    calc
      _ ≤ (2:ℝ)^(-8:ℤ)*((n:ℝ)^2*(K:ℝ)^(-Dp v)) := by
        rw [← mul_assoc]; gcongr
      _ ≤ (2:ℝ)^(-8:ℤ)*(1/Hfine) := mul_le_mul_of_nonneg_left hp.1 (by positivity)
      _ = _ := by ring
  · rw [hB]
    have hl : (0:ℝ) < (K:ℝ)^(sumReg v/v.γ)/32 := by positivity
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : 0 ≤ (2:ℝ)^10*(n:ℝ)^4*(K:ℝ)^(-(2+4*sumReg v))) hl hr.2
    have hid : (2:ℝ)^10*(n:ℝ)^4*(K:ℝ)^(-(2+4*sumReg v)) /
        ((K:ℝ)^(sumReg v/v.γ)/32) =
        (2:ℝ)^15*((n:ℝ)^4*(K:ℝ)^(-(2*Dp v))) := by
      have hex : -(2+4*sumReg v) + -(sumReg v/v.γ) = -(2*Dp v) := by
        rw [(bounded_rough_denominator_bounds w hw).1]
        change -(2+4*sumReg v) + -(sumReg v/w.γ) = _
        ring
      have hrat : (K:ℝ)^(-(2+4*sumReg v))/(K:ℝ)^(sumReg v/v.γ) =
          (K:ℝ)^(-(2*Dp v)) := by
        rw [← Real.rpow_sub hk]
        rw [sub_eq_add_neg, hex]
      calc
        _ = (2:ℝ)^15*(n:ℝ)^4*((K:ℝ)^(-(2+4*sumReg v))/(K:ℝ)^(sumReg v/v.γ)) := by
          norm_num; ring
        _ = _ := by rw [hrat]; ring
    calc
      _ ≤ _ := hdiv
      _ = _ := hid
      _ ≤ (2:ℝ)^15*(1/Hfine^2) := mul_le_mul_of_nonneg_left hp.2 (by positivity)
      _ = _ := by ring

end CausalSmith.Stat.FinitepHomogeneityDensegamma

