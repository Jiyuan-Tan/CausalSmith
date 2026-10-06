module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperHandle

/-! Finite-moment point-CATE frontier: Helpers/PhaseAlgebra. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Clearing the positive denominators gives the phase comparison identity. -/
-- @node: phase_exponent_difference
lemma phase_exponent_difference (κ : Params) (hκ : κ.Valid) (b : ℝ) (hb : 0 < b) :
    let D := 1 + (b + κ.β) / κ.γ + 2*b + κ.β / qExp κ
    2*(b + κ.β)/D - rOracle κ =
      κ.γ*qExp κ/(D*(κ.γ + qExp κ)) *
        ((b + κ.β)/κ.γ + 2*b/(κ.p-1) + κ.β/qExp κ - 1):= by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hp1 : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp1 hp
  have hg := hκ.2.2.2.1
  have hβ := hκ.2.2.1.1
  have hD : 0 < 1 + (b + κ.β) / κ.γ + 2*b + κ.β / qExp κ := by positivity
  dsimp only
  unfold rOracle qExp at *
  field_simp
  ring

/-- The sign of the exponent difference is the sign of the public phase expression. -/
-- @node: phase_exponent_comparison
lemma phase_exponent_comparison (κ : Params) (hκ : κ.Valid) (b : ℝ) (hb : 0 < b) :
    let D := 1 + (b + κ.β) / κ.γ + 2*b + κ.β / qExp κ
    (2*(b + κ.β)/D ≤ rOracle κ ↔
      (b + κ.β)/κ.γ + 2*b/(κ.p-1) + κ.β/qExp κ ≤ 1) ∧
    (rOracle κ < 2*(b + κ.β)/D ↔
      1 < (b + κ.β)/κ.γ + 2*b/(κ.p-1) + κ.β/qExp κ):= by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hp1 : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp1 hp
  have hg := hκ.2.2.2.1
  have hβ := hκ.2.2.1.1
  have hD : 0 < 1 + (b + κ.β) / κ.γ + 2*b + κ.β / qExp κ := by positivity
  have hc : 0 < κ.γ*qExp κ /
      ((1 + (b + κ.β)/κ.γ + 2*b + κ.β/qExp κ)*(κ.γ + qExp κ)) := by positivity
  have hid := phase_exponent_difference κ hκ b hb
  dsimp only at hid ⊢
  constructor
  · rw [← sub_nonpos, hid, mul_nonpos_iff, sub_nonpos]
    simp only [hc.le, not_le.mpr hc, true_and, false_and, or_false]
  · rw [← sub_pos, hid, mul_pos_iff_of_pos_left hc, sub_pos]

/-- The effective tuning and public exponents have the same slowest power. -/
-- @node: phase_algebra
lemma phase_algebra (κ : Params) (hκ : κ.Valid) :
  min (rOracle κ) (effectiveR κ) = min (rOracle κ) (rInter κ) ∧
  (rInter κ ≤ rOracle κ ↔ boundary κ ≤ 1) ∧
  0 < effectiveA κ ∧ 0 < effectiveD κ ∧
  0 < constantA κ ∧ 0 < constantE κ ∧ 0 < constantF κ := by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hp1 : 0 < κ.p-1 := sub_pos.mpr hκ.1.1
  have hq : 0 < qExp κ := div_pos hp1 hp
  have hα := hκ.2.1.1
  have hβ := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have ha : 0 < effectiveA κ := lt_min hα (by positivity)
  have hacap : effectiveA κ ≤ (κ.p-1)/2 := min_le_right _ _
  have hd : 0 < effectiveD κ := by
    unfold effectiveD qExp
    have hprod := mul_le_mul_of_nonneg_right hacap (show 0 ≤ 2-κ.p by linarith [hκ.1.2])
    have heq : (κ.p-1)/κ.p - effectiveA κ*(2-κ.p)/κ.p =
        (κ.p-1-effectiveA κ*(2-κ.p))/κ.p := by ring
    rw [heq]
    exact div_pos (by nlinarith) hp
  have hb : boundary κ = sumReg κ/κ.γ + 2*κ.α/(κ.p-1) + κ.β/qExp κ := by
    unfold boundary qExp
    field_simp
    ring
  have hphase := phase_exponent_comparison κ hκ κ.α hα
  have hmin : min (rOracle κ) (effectiveR κ) = min (rOracle κ) (rInter κ) := by
    by_cases hcap : κ.α ≤ (κ.p-1)/2
    · have hea : effectiveA κ = κ.α := min_eq_left hcap
      simp only [effectiveR, effectiveS, hea, rInter, sumReg]
    · have hea : effectiveA κ = (κ.p-1)/2 := min_eq_right (le_of_not_ge hcap)
      have hapos : 0 < (κ.p-1)/2 := by positivity
      have hephase := phase_exponent_comparison κ hκ ((κ.p-1)/2) hapos
      have hcancel : 2*((κ.p-1)/2)/(κ.p-1) = 1 := by field_simp
      have hegt : rOracle κ < effectiveR κ := by
        unfold effectiveR effectiveS
        rw [hea]
        apply hephase.2.mpr
        rw [hcancel]
        have h1 : 0 < ((κ.p-1)/2+κ.β)/κ.γ := by positivity
        have h2 : 0 < κ.β/qExp κ := by positivity
        linarith
      have higt : rOracle κ < rInter κ := by
        unfold rInter sumReg
        apply hphase.2.mpr
        have h1 : 0 < (κ.α+κ.β)/κ.γ := by positivity
        have h2 : 0 < κ.β/qExp κ := by positivity
        have h3 : 1 < 2*κ.α/(κ.p-1) := (lt_div_iff₀ hp1).2 (by linarith)
        linarith
      rw [min_eq_left hegt.le, min_eq_left higt.le]
  refine ⟨hmin, ?_, ha, hd, ?_, ?_, ?_⟩
  · rw [hb]
    exact hphase.1
  · unfold constantA
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  · unfold constantE
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  · unfold constantF
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))

/-- The public benchmark is a positive power with exponent equal to the slower rate. -/
-- @node: upper_rate_power
lemma upper_rate_power (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    0 < min (rOracle κ) (rInter κ) ∧
      rate κ n = (n : ℝ) ^ (-min (rOracle κ) (rInter κ)) := by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hg := hκ.2.2.2.1
  have ha := hκ.2.1.1
  have hb := hκ.2.2.1.1
  have ho : 0 < rOracle κ := by unfold rOracle; positivity
  have hi : 0 < rInter κ := by unfold rInter sumReg; positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  refine ⟨lt_min ho hi, ?_⟩
  unfold rate
  by_cases h : rOracle κ ≤ rInter κ
  · rw [min_eq_left h, max_eq_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg h))]
  · have h' := le_of_not_ge h
    rw [min_eq_right h', max_eq_right
      (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg h'))]

/-- The oracle comparison certifies localization, effective sample size and both powers. -/
-- @node: upper_bandwidth_certificate
lemma upper_bandwidth_certificate (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (0 < upperH κ n ∧ upperH κ n ≤ 1) ∧
    1 ≤ (n : ℝ) * upperH κ n ∧
    ((n : ℝ) * upperH κ n)^(-qExp κ) ≤ rate κ n ∧
    upperH κ n ^ κ.γ = rate κ n := by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hg := hκ.2.2.2.1
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  obtain ⟨hrpos, hrpow⟩ := upper_rate_power κ hκ n hn
  let r := min (rOracle κ) (rInter κ)
  have hrle : r ≤ rOracle κ := min_le_left _ _
  have horacle : rOracle κ < κ.γ := by
    unfold rOracle
    apply (div_lt_iff₀ (show 0 < κ.γ + qExp κ by positivity)).mpr
    nlinarith
  have hrγ : r / κ.γ ≤ 1 := (div_le_one hg).mpr (hrle.trans horacle.le)
  have hnoise : -(1-r/κ.γ)*qExp κ ≤ -r := by
    have he : r / κ.γ * κ.γ = r := div_mul_cancel₀ _ hg.ne'
    unfold rOracle at hrle
    have hh := (le_div_iff₀ (show 0 < κ.γ + qExp κ by positivity)).mp hrle
    nlinarith
  have hhpower : upperH κ n = (n : ℝ)^(-r/κ.γ) := by
    unfold upperH
    rw [hrpow, ← Real.rpow_mul hnpos.le]
    congr 1
    dsimp only [r]
    ring
  have hnh : (n : ℝ)*upperH κ n = (n : ℝ)^(1-r/κ.γ) := by
    rw [hhpower, neg_div, Real.rpow_sub hnpos, Real.rpow_one,
      Real.rpow_neg hnpos.le]
    simp only [div_eq_mul_inv]
  have hrnonneg : 0 ≤ r := hrpos.le
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hhpower]
    exact Real.rpow_pos_of_pos hnpos _
  · rw [hhpower]
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrnonneg) hg.le)
  · rw [hnh]
    exact Real.one_le_rpow hn1 (by linarith)
  · rw [hnh, ← Real.rpow_mul hnpos.le, hrpow]
    apply Real.rpow_le_rpow_of_exponent_le hn1
    dsimp only [r] at hnoise
    nlinarith
  · unfold upperH
    have hrpositive : 0 < rate κ n := by rw [hrpow]; positivity
    rw [← Real.rpow_mul hrpositive.le, one_div_mul_cancel hg.ne', Real.rpow_one]

/-- A nonnegative floor-rounded dyadic mesh lies within a factor two of its target;
positive resolutions also retain the target as a lower bound. -/
-- @node: dyadic_floor_certificate
lemma dyadic_floor_certificate (h t : ℝ) (hh : 0 < h) (ht : 0 < t) :
    let J := Int.toNat ⌊Real.logb 2 (h/t)⌋
    (0 < J → t ≤ cellLen h J) ∧ cellLen h J ≤ 2*t := by
  dsimp only
  by_cases hsmall : h ≤ t
  · have hlog : Real.logb 2 (h/t) ≤ 0 := by
      apply (Real.logb_le_iff_le_rpow (by norm_num) (div_pos hh ht)).mpr
      simpa using (div_le_one ht).mpr hsmall
    have hJ : Int.toNat ⌊Real.logb 2 (h/t)⌋ = 0 :=
      Int.toNat_eq_zero.mpr (Int.floor_le_iff.mpr (by simpa using (show Real.logb 2 (h/t) < 1 by linarith)))
    rw [hJ]
    simp only [cellLen, pow_zero, div_one]
    constructor
    · intro hzero
      omega
    · linarith
  · have hratio : 1 < h/t := (one_lt_div ht).mpr (lt_of_not_ge hsmall)
    have hlog : 0 ≤ Real.logb 2 (h/t) :=
      (Real.logb_pos (by norm_num) hratio).le
    have hcast : (Int.toNat ⌊Real.logb 2 (h/t)⌋ : ℝ) =
        (⌊Real.logb 2 (h/t)⌋ : ℤ) := by
      exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hlog)
    have hlo : (2 : ℝ)^Int.toNat ⌊Real.logb 2 (h/t)⌋ ≤ h/t := by
      rw [← Real.rpow_natCast, hcast]
      exact (Real.le_logb_iff_rpow_le (by norm_num) (div_pos hh ht)).mp
        (Int.floor_le _)
    have hhi : h/t < 2 * (2 : ℝ)^Int.toNat ⌊Real.logb 2 (h/t)⌋ := by
      have hx := (Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hh ht)).mp
        (Int.lt_floor_add_one (Real.logb 2 (h/t)))
      rw [← hcast, Real.rpow_add (by norm_num), Real.rpow_natCast, Real.rpow_one] at hx
      nlinarith
    have hp : 0 < (2 : ℝ)^Int.toNat ⌊Real.logb 2 (h/t)⌋ := by positivity
    constructor
    · intro _
      unfold cellLen
      apply (le_div_iff₀ hp).mpr
      have hx := (le_div_iff₀ ht).mp hlo
      nlinarith
    · unfold cellLen
      apply (div_le_iff₀ hp).mpr
      have hx := (div_lt_iff₀ ht).mp hhi
      nlinarith

/-- The rounded projection bias obeys the public constant-four certificate. -/
-- @node: upper_rounding_certificate
lemma upper_rounding_certificate (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    cellLen (upperH κ n) (upperJ κ n) ^ effectiveS κ ≤ 4*rate κ n := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hr : 0 < rate κ n := by rw [(upper_rate_power κ hκ n hn).2]; positivity
  have ha := (phase_algebra κ hκ).2.2.1
  have hb := hκ.2.2.1.1
  have hs : 0 < effectiveS κ := by unfold effectiveS; positivity
  have hs2 : effectiveS κ ≤ 2 := by
    have hcap : effectiveA κ ≤ (κ.p-1)/2 := min_le_right _ _
    unfold effectiveS
    linarith [hκ.1.2, hκ.2.2.1.2]
  have ht : 0 < rate κ n ^ (1/effectiveS κ) := by positivity
  have hmesh := (dyadic_floor_certificate (upperH κ n)
    (rate κ n ^ (1/effectiveS κ)) hh ht).2
  change cellLen (upperH κ n) (upperJ κ n) ≤ 2*rate κ n^(1/effectiveS κ) at hmesh
  calc
    cellLen (upperH κ n) (upperJ κ n) ^ effectiveS κ
        ≤ (2*rate κ n^(1/effectiveS κ))^effectiveS κ :=
      Real.rpow_le_rpow (by unfold cellLen; positivity) hmesh hs.le
    _ = (2 : ℝ)^effectiveS κ * rate κ n := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hr.le,
        one_div_mul_cancel hs.ne', Real.rpow_one]
    _ ≤ 4*rate κ n := by
      have htwo := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num) hs2
      norm_num at htwo
      exact mul_le_mul_of_nonneg_right htwo hr.le

/-- Dyadic cell lengths decrease with resolution. -/
-- @node: cellLen_antitone
lemma cellLen_antitone (h : ℝ) (hh : 0 ≤ h) : Antitone (cellLen h) := by
  intro j k hjk
  unfold cellLen
  gcongr
  norm_num

/-- The uncapped thresholds decrease with resolution. -/
-- @node: upper_uncapped_antitone
lemma upper_uncapped_antitone (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    Antitone (fun j : ℕ =>
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j^(1+2*effectiveA κ))^(1/κ.p)) := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have ha := (phase_algebra κ hκ).2.2.1
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  intro j k hjk
  apply Real.rpow_le_rpow (by unfold cellLen; positivity) _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (by unfold cellLen; positivity)
    (cellLen_antitone _ hh.le hjk) (by positivity)

/-- The finest positive resolution satisfies the effective interaction budget. -/
-- @node: upper_finest_budget
lemma upper_finest_budget (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (hJ : 0 < upperJ κ n) :
    1 ≤ (n : ℝ)^2*upperH κ n*
      cellLen (upperH κ n) (upperJ κ n)^(1+2*effectiveA κ+κ.β/qExp κ) := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1.1
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have ha := (phase_algebra κ hκ).2.2.1
  have hb := hκ.2.2.1.1
  have hg := hκ.2.2.2.1
  have hs : 0 < effectiveS κ := by unfold effectiveS; positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  obtain ⟨hrpos, hrpow⟩ := upper_rate_power κ hκ n hn
  have hr : 0 < rate κ n := by rw [hrpow]; positivity
  let r := min (rOracle κ) (rInter κ)
  let v := 1+2*effectiveA κ+κ.β/qExp κ
  let E := 1/κ.γ+v/effectiveS κ
  have hv : 0 < v := by dsimp [v]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hrc : r ≤ effectiveR κ := by
    dsimp only [r]
    rw [← (phase_algebra κ hκ).1]
    exact min_le_right _ _
  have hden : 0 < 1+effectiveS κ/κ.γ+2*effectiveA κ+κ.β/qExp κ := by positivity
  have hbudget : r*E ≤ 2 := by
    unfold effectiveR at hrc
    have hx := (le_div_iff₀ hden).mp hrc
    have hid : E*effectiveS κ =
        1+effectiveS κ/κ.γ+2*effectiveA κ+κ.β/qExp κ := by
      dsimp [E, v]
      field_simp
      ring
    nlinarith
  have htarget : 1 ≤ (n : ℝ)^2*upperH κ n*(rate κ n^(1/effectiveS κ))^v := by
    have hid : (n : ℝ)^2*upperH κ n*(rate κ n^(1/effectiveS κ))^v =
        (n : ℝ)^(2-r*E) := by
      unfold upperH
      rw [← Real.rpow_mul hr.le, mul_assoc, ← Real.rpow_add hr]
      have hsum : 1/κ.γ+1/effectiveS κ*v = E := by dsimp [E]; ring
      rw [hsum]
      rw [hrpow, ← Real.rpow_mul hnpos.le, ← Real.rpow_two, ← Real.rpow_add hnpos]
      congr 1
      dsimp only [r]
      ring
    rw [hid]
    exact Real.one_le_rpow hn1 (by linarith)
  have hmesh := (dyadic_floor_certificate (upperH κ n)
    (rate κ n^(1/effectiveS κ)) hh (by positivity)).1 hJ
  exact htarget.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hmesh hv.le) (by positivity))

/-- Every finite truncation level lies in the stipulated threshold domain. -/
-- @node: upper_threshold_positive
lemma upper_threshold_positive (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    ∀ j, 1 ≤ upperT κ n j := by
  have hh := (upper_bandwidth_certificate κ hκ n hn).1
  have hnh := (upper_bandwidth_certificate κ hκ n hn).2.1
  have hhpos := hh.1
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have ha := (phase_algebra κ hκ).2.2.1
  have hb := hκ.2.2.1.1
  have hcoarse : 1 ≤ ((n : ℝ)*upperH κ n)^(1/κ.p) :=
    Real.one_le_rpow hnh (by positivity)
  intro j
  unfold upperT
  split
  · exact hcoarse
  · rename_i hj
    apply le_min hcoarse
    have hJ : 0 < upperJ κ n := by omega
    have hd : 0 < cellLen (upperH κ n) (upperJ κ n) := by unfold cellLen; positivity
    have hd1 : cellLen (upperH κ n) (upperJ κ n) ≤ 1 := by
      have hx := cellLen_antitone _ hh.1.le (Nat.zero_le (upperJ κ n))
      simpa [cellLen] using hx.trans (by simpa [cellLen] using hh.2)
    have hexp : cellLen (upperH κ n) (upperJ κ n)^(1+2*effectiveA κ+κ.β/qExp κ) ≤
        cellLen (upperH κ n) (upperJ κ n)^(1+2*effectiveA κ) := by
      apply Real.rpow_le_rpow_of_exponent_ge hd hd1
      have hx : 0 ≤ κ.β/qExp κ := by positivity
      linarith
    have hfine : 1 ≤ (n : ℝ)^2*upperH κ n*
        cellLen (upperH κ n) (upperJ κ n)^(1+2*effectiveA κ) :=
      (upper_finest_budget κ hκ n hn hJ).trans
        (mul_le_mul_of_nonneg_left hexp (by positivity))
    have ht := Real.one_le_rpow hfine (show 0 ≤ 1/κ.p by positivity)
    exact ht.trans (upper_uncapped_antitone κ hκ n hn (by omega : j.val ≤ upperJ κ n))

/-- Capped positive levels form an initial segment, followed by the uncapped formula. -/
-- @node: upper_cap_certificate
lemma upper_cap_certificate (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    ∃ j0 : Fin (upperJ κ n+1), ∀ j : Fin (upperJ κ n+1),
      (j.val ≤ j0.val → upperT κ n j = upperT κ n 0) ∧
      (j0.val < j.val → upperT κ n j =
        ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val^(1+2*effectiveA κ))^(1/κ.p)) := by
  let coarse := ((n : ℝ)*upperH κ n)^(1/κ.p)
  let fine := fun j : ℕ =>
    ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j^(1+2*effectiveA κ))^(1/κ.p)
  have hanti : Antitone fine := upper_uncapped_antitone κ hκ n hn
  let capped : Finset (Fin (upperJ κ n+1)) :=
    Finset.univ.filter (fun j => j.val = 0 ∨ coarse ≤ fine j.val)
  have hnonempty : capped.Nonempty := by
    refine ⟨0, ?_⟩
    simp [capped]
  let j0 := capped.max' hnonempty
  have hj0mem : j0 ∈ capped := Finset.max'_mem capped hnonempty
  have hj0cap : j0.val = 0 ∨ coarse ≤ fine j0.val := by
    simpa only [capped, Finset.mem_filter, Finset.mem_univ, true_and] using hj0mem
  refine ⟨j0, ?_⟩
  intro j
  constructor
  · intro hjle
    by_cases hj : j.val = 0
    · simp [upperT, hj]
    · have hj0 : j0.val ≠ 0 := by omega
      have hcap : coarse ≤ fine j.val :=
        (hj0cap.resolve_left hj0).trans (hanti hjle)
      simpa only [upperT, hj, ↓reduceIte, Fin.val_zero] using min_eq_left hcap
  · intro hjgt
    have hj : j.val ≠ 0 := by omega
    have huncap : fine j.val ≤ coarse := by
      by_contra hnot
      have hmem : j ∈ capped := by
        simp only [capped, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr (le_of_lt (lt_of_not_ge hnot))
      have hle : j ≤ j0 := Finset.le_max' capped j hmem
      have hval : j.val ≤ j0.val := hle
      omega
    simpa only [upperT, hj, ↓reduceIte] using min_eq_right huncap

/-- Finite-sample bandwidth, floor rounding, threshold and cap certificates. -/
-- @node: upper_tuning
lemma upper_tuning (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
  (0 < upperH κ n ∧ upperH κ n ≤ 1) ∧
  1 ≤ (n : ℝ)*upperH κ n ∧
  ((n : ℝ)*upperH κ n)^(-qExp κ) ≤ rate κ n ∧
  upperH κ n ^ κ.γ = rate κ n ∧
  cellLen (upperH κ n) (upperJ κ n) ^ effectiveS κ ≤ 4*rate κ n ∧
  (∀ j, 1 ≤ upperT κ n j) ∧
  (∃ j0 : Fin (upperJ κ n+1), ∀ j : Fin (upperJ κ n+1),
    (j.val ≤ j0.val → upperT κ n j = upperT κ n 0) ∧
    (j0.val < j.val → upperT κ n j =
      ((n : ℝ)^2*upperH κ n*cellLen (upperH κ n) j.val^(1+2*effectiveA κ))^(1/κ.p))) := by
  obtain ⟨hh, hnh, hu, hpower⟩ := upper_bandwidth_certificate κ hκ n hn
  refine ⟨hh, hnh, hu, hpower, upper_rounding_certificate κ hκ n hn, upper_threshold_positive κ hκ n hn,
    upper_cap_certificate κ hκ n hn⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
