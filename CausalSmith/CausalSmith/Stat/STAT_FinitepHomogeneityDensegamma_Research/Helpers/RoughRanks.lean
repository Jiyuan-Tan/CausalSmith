module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ConversePriors
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaAlternativeLegality
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerTuning

/-! Dyadic ranks and separation calibration for the rough full-record converse. -/
public section
noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The rough denominator is below two, so the fine resolution grows at least linearly. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: rough_denominator_lt_two
lemma rough_denominator_lt_two (v : Params) (hv : v.Valid) (hf : Fphase v < 1) :
    Dp v < 2 := by
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have ha : 2*v.α ≤ 2*v.α/(v.p-1) :=
    (le_div_iff₀ hm).mpr (by nlinarith [hv.1.2, hv.2.1.1])
  dsimp [Dp, Fphase] at *
  linarith

/-- Fine dyadic rounding retains the specified target within a factor two. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: rough_fine_rank_bounds
lemma rough_fine_rank_bounds (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    Hfine*(n:ℝ)^(2/Dp v) ≤ roughK n v ∧
    (roughK n v:ℝ) ≤ 2*Hfine*(n:ℝ)^(2/Dp v) ∧ 2^40*n ≤ roughK n v := by
  have hd := (phase_denominators v hv).2.2.2.2.2.2.2
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hex : 1 ≤ 2/Dp v := (le_div_iff₀ hd).mpr (by simpa using (rough_denominator_lt_two v hv hf).le)
  have hp : (n:ℝ) ≤ (n:ℝ)^(2/Dp v) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hn1 hex
  have ht : 1 ≤ Hfine*(n:ℝ)^(2/Dp v) := by
    have hH : 1 ≤ Hfine := by norm_num [Hfine]
    nlinarith [hn1.trans hp]
  have he := leastPow2Ge_eq_dyadUp ht
  have hlo := le_dyadUp (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) ht)
  have hup := (ledger_dyadUp_bounds ht).2
  rw [← he] at hlo hup
  refine ⟨hlo, by simpa [roughK, mul_assoc] using hup, ?_⟩
  have hlinear := (mul_le_mul_of_nonneg_left hp (by norm_num [Hfine] : 0 ≤ Hfine)).trans hlo
  change Hfine*(n:ℝ) ≤ (roughK n v:ℝ) at hlinear
  norm_num [Hfine] at hlinear
  exact_mod_cast hlinear

/-- Downward dyadic rounding lies between one half of a target and that target. This statement assumes [the hx condition](hyp:hx). [This is the stated conclusion](goal). -/
-- @node: rough_dyadic_floor_bounds
lemma rough_dyadic_floor_bounds (x : ℝ) (hx : 2 ≤ x) :
    x/2 ≤ (2:ℝ)^Nat.floor (Real.logb 2 x) ∧
    (2:ℝ)^Nat.floor (Real.logb 2 x) ≤ x ∧
    2 ≤ (2:ℕ)^Nat.floor (Real.logb 2 x) := by
  have hlog : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) (by linarith)
  have hf := Nat.floor_le hlog
  have hl := (Nat.lt_floor_add_one (Real.logb 2 x)).le
  have he := Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    (by linarith : 0 < x)
  constructor
  · have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hl
    rw [he, Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at hp
    linarith
  constructor
  · rw [← Real.rpow_natCast]
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num) hf).trans_eq he
  · have hlog1 : 1 ≤ Real.logb 2 x := by
      simpa using Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
        (by norm_num : (0:ℝ) < 2) hx
    have hfloor : 1 ≤ Nat.floor (Real.logb 2 x) := (Nat.le_floor_iff hlog).mpr (by simpa using hlog1)
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hfloor

/-- The public threshold makes the coarse target at least thirty-two. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: rough_coarse_target_ge
lemma rough_coarse_target_ge (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) (hlarge : Nlow v ≤ n) :
    32 ≤ (roughK n v:ℝ)^(sumReg v/v.γ) := by
  obtain ⟨hp, hm, hg, hS, hq, hqh, he, hd⟩ := phase_denominators v hv
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ht : (32:ℝ)^(Dp v*v.γ/(2*sumReg v)) ≤ (n:ℝ) := by
    exact (le_max_right _ _).trans ((Nat.le_ceil _).trans (by exact_mod_cast hlarge))
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (32:ℝ)^(Dp v*v.γ/(2*sumReg v)))
    ht (show 0 ≤ (2/Dp v)*(sumReg v/v.γ) by positivity)
  rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 32),
    show (Dp v*v.γ/(2*sumReg v))*((2/Dp v)*(sumReg v/v.γ)) = 1 by
      field_simp, Real.rpow_one] at hpow
  have hK := (rough_fine_rank_bounds v hv hf n hn).1
  have hbase : (n:ℝ)^(2/Dp v) ≤ (roughK n v:ℝ) := by
    have hH : 1 ≤ Hfine := by norm_num [Hfine]
    exact (le_mul_of_one_le_left (by positivity) hH).trans hK
  have hmono := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)^(2/Dp v)) hbase
    (show 0 ≤ sumReg v/v.γ by positivity)
  rw [← Real.rpow_mul hnpos.le] at hmono
  exact hpow.trans hmono

/-- Both dyadic ranks obey all legality constraints and the coarse lower rounding bound. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn), [the hlarge condition](hyp:hlarge). [This is the stated conclusion](goal). -/
-- @node: rough_rank_legality
lemma rough_rank_legality (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) (hlarge : Nlow v ≤ n) :
    LegalityRanks v (roughK n v) (roughM n v) ∧
    (roughK n v:ℝ)^(sumReg v/v.γ)/32 ≤ roughM n v := by
  have hk := rough_fine_rank_bounds v hv hf n hn
  have hK : (1:ℝ) ≤ roughK n v := by
    have : 1 ≤ roughK n v := by have := hk.2.2; omega
    exact_mod_cast this
  have ht := rough_coarse_target_ge v hv hf n hn hlarge
  have hr := rough_dyadic_floor_bounds ((roughK n v:ℝ)^(sumReg v/v.γ)/16) (by linarith)
  have hM : (roughM n v:ℝ) ≤ (roughK n v:ℝ)^(sumReg v/v.γ)/16 := by
    simpa [roughM, Nat.cast_pow, Nat.cast_ofNat] using hr.2.1
  have hreg : (roughK n v:ℝ)^(sumReg v/v.γ) ≤ roughK n v := by
    have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
    have hex : sumReg v/v.γ ≤ 1 := (div_le_one hg).mpr (legality_rough_regularity v hv hf).1.le
    simpa using Real.rpow_le_rpow_of_exponent_le hK hex
  refine ⟨⟨?_, ⟨_, rfl⟩, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨_, rfl⟩
  · have hh : (16:ℝ)*roughM n v ≤ roughK n v := by linarith
    exact_mod_cast hh
  · simpa [roughM] using hr.2.2
  · linarith
  · have hh := hr.1
    norm_num [roughM, Nat.cast_pow, div_div] at hh ⊢
    exact hh

/-- The fine-rank upper rounding bound preserves the claimed rough separation multiplier. This statement assumes [the hv condition](hyp:hv), [the hf condition](hyp:hf), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: rough_rank_separation
lemma rough_rank_separation (v : Params) (hv : v.Valid) (hf : Fphase v < 1)
    (n : ℕ) (hn : 2 ≤ n) :
    cLower v*(n:ℝ)^(-E4 v) ≤ (2:ℝ)^(-17:ℤ)*(roughK n v:ℝ)^(-sumReg v) := by
  have hS : 0 < sumReg v := add_pos hv.2.1.1 hv.2.2.1.1
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hK : (0:ℝ) < roughK n v := by
    have := (rough_fine_rank_bounds v hv hf n hn).2.2
    exact_mod_cast (by omega : 0 < roughK n v)
  have hup := (rough_fine_rank_bounds v hv hf n hn).2.1
  have hpow := Real.rpow_le_rpow_of_nonpos hK hup (neg_nonpos.mpr hS.le)
  rw [Real.mul_rpow (by norm_num [Hfine]) (by positivity), ← Real.rpow_mul hnpos.le,
    show (2/Dp v)*(-sumReg v) = -E4 v by unfold E4; ring] at hpow
  have hc : cLower v ≤ (2:ℝ)^(-17:ℤ)*(2*Hfine)^(-sumReg v) := by
    simp only [cLower, if_neg (not_le.mpr hf)]
    exact min_le_left _ _
  exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans
    (by simpa only [mul_assoc] using (mul_le_mul_of_nonneg_left hpow
      (by positivity : 0 ≤ (2:ℝ)^(-17:ℤ))))

end CausalSmith.Stat.FinitepHomogeneityDensegamma
