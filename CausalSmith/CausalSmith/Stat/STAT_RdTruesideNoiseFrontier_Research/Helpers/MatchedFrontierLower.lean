module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.MatchedFrontierUpper
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.DirectLowerAssembly
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.TDirectReduction

/-!
# Noise-adapted lower tuning for the matched frontier

This file rounds the scalar noisy resolution to the explicit cancellation
witness grid and transfers its information bound to the product experiment.
-/

public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- The noise-adapted support is monotone in the integer degree. Given [the displayed inputs and assumptions](hyp:σ,hσ,j,m,hjm), [the stated mathematical conclusion holds](goal). -/
lemma noiseSupport_mono {σ : ℝ} (hσ : 0 ≤ σ) {j m : ℕ} (hjm : j ≤ m) :
    noiseSupport σ j ≤ noiseSupport σ m := by
  unfold noiseSupport
  apply min_le_min_left
  gcongr

/-- Consecutive noise resolutions lose at most a factor four. Given [the displayed inputs and assumptions](hyp:σ,m,hσ,hm), [the stated mathematical conclusion holds](goal). -/
lemma noiseResolution_prev_le_four (σ : ℝ) (m : ℕ) (hσ : 0 ≤ σ) (hm : 2 ≤ m) :
    noiseResolution σ (m - 1) ≤ 4 * noiseResolution σ m := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hp : (m - 1 : ℕ) ≤ m := Nat.sub_le _ _
  have hs := noiseSupport_mono hσ hp
  have hm1 : (0 : ℝ) < (m - 1 : ℕ) := by exact_mod_cast (show 0 < m - 1 by omega)
  unfold noiseResolution
  rw [show 4 * (noiseSupport σ m / (m : ℝ)^2) =
    (4 * noiseSupport σ m) / (m : ℝ)^2 by ring]
  apply (div_le_div_iff₀ (sq_pos_of_pos hm1) (sq_pos_of_pos hmpos)).2
  have hsq : (m : ℝ)^2 ≤ 4 * ((m - 1 : ℕ) : ℝ)^2 := by
    have hmcast : (2 : ℝ) ≤ m := by exact_mod_cast hm
    rw [Nat.cast_sub (by omega : 1 ≤ m)]
    norm_num
    nlinarith
  calc
    noiseSupport σ (m - 1) * (m : ℝ)^2 ≤
        noiseSupport σ (m - 1) * (4 * ((m - 1 : ℕ) : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsq (by unfold noiseSupport; positivity)
    _ ≤ 4 * noiseSupport σ m * ((m - 1 : ℕ) : ℝ)^2 := by
      calc
        _ = (4 * noiseSupport σ (m - 1)) * ((m - 1 : ℕ) : ℝ)^2 := by ring
        _ ≤ (4 * noiseSupport σ m) * ((m - 1 : ℕ) : ℝ)^2 :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hs (by norm_num)) (sq_nonneg _)

/-- Every positive target scale is eventually crossed by the explicit
noise-resolution grid. Given [the displayed inputs and assumptions](hyp:σ,t,ht), [the stated mathematical conclusion holds](goal). -/
lemma exists_noiseResolution_le (σ t : ℝ) (ht : 0 < t) :
    ∃ m : ℕ, 2 ≤ m ∧ noiseResolution σ m ≤ t := by
  obtain ⟨m, hm⟩ := exists_nat_gt (Real.sqrt (1 / t) + 2)
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := lt_of_le_of_lt (by linarith [Real.sqrt_nonneg (1 / t)]) hm
    exact_mod_cast this.le
  have hmpos : (0 : ℝ) < m := by positivity
  have hmt : 1 / t < (m : ℝ)^2 := by
    have hs : Real.sqrt (1 / t) < (m : ℝ) := by linarith
    have harg : 0 ≤ 1 / t := by positivity
    nlinarith [Real.sq_sqrt harg,
      mul_self_lt_mul_self (Real.sqrt_nonneg (1 / t)) hs]
  refine ⟨m, hm2, ?_⟩
  unfold noiseResolution noiseSupport
  have hsupport : min 1 (σ * Real.sqrt m / 8) ≤ 1 := min_le_left _ _
  calc
    min 1 (σ * Real.sqrt m / 8) / (m : ℝ)^2 ≤ 1 / (m : ℝ)^2 :=
      div_le_div_of_nonneg_right hsupport (sq_nonneg _)
    _ ≤ t := by
      rw [div_le_iff₀ (sq_pos_of_pos hmpos)]
      have := (div_lt_iff₀ ht).mp hmt
      nlinarith

/-- Minimal grid crossing at `H/4096`; it lies within a factor four of the
requested scale once the scalar root is strictly below the noise level. Given [the displayed inputs and assumptions](hyp:σ,H,hσ,hH,hHσ), [the stated mathematical conclusion holds](goal). -/
lemma exists_noiseResolution_bracket (σ H : ℝ)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hH : 0 < H) (hHσ : H < σ) :
    ∃ m : ℕ, 3 ≤ m ∧
      H / 16384 < noiseResolution σ m ∧ noiseResolution σ m ≤ H / 4096 := by
  let p : ℕ → Prop := fun m => 2 ≤ m ∧ noiseResolution σ m ≤ H / 4096
  have hex : ∃ m, p m := exists_noiseResolution_le σ (H / 4096) (by positivity)
  let m := Nat.find hex
  have hmprop : p m := Nat.find_spec hex
  have htwo : H / 4096 < noiseResolution σ 2 := by
    have hsqrt : (1 : ℝ) ≤ Real.sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).2 (by norm_num)
    have hunsat : σ * Real.sqrt 2 / 8 < 1 := by
      have hsqrt2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      nlinarith [hσ.2]
    change H / 4096 < min 1 (σ * Real.sqrt (2 : ℝ) / 8) / (2 : ℝ)^2
    rw [min_eq_right hunsat.le]
    norm_num
    nlinarith
  have hm3 : 3 ≤ m := by
    by_contra h
    have hmle : m ≤ 2 := by omega
    have hm2 := hmprop.1
    have : m = 2 := by omega
    rw [this] at hmprop
    linarith [hmprop.2, htwo]
  have hprev : H / 4096 < noiseResolution σ (m - 1) := by
    by_contra h
    have hp : p (m - 1) := ⟨by omega, le_of_not_gt h⟩
    have hmin := Nat.find_min' hex hp
    omega
  have hratio := noiseResolution_prev_le_four σ m hσ.1.le (by omega)
  refine ⟨m, hm3, ?_, hmprop.2⟩
  nlinarith

/-- At the rounded cancellation scale, the likelihood exponential absorbs
the exact scalar root balance with a fixed numerical margin. Given [the displayed inputs and assumptions](hyp:β,σ,H,h,n,hβ,hn,hσ,hroot,hh,hhH,hHσ), [the stated mathematical conclusion holds](goal). -/
lemma rounded_noise_information_factor (β σ H h : ℝ) (n : ℕ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hn : 2 ≤ n)
    (hσ : σ ∈ Ioc (0 : ℝ) 1) (hroot : H = rateResolution β n σ)
    (hh : 0 < h) (hhH : h ≤ H / 4096) (hHσ : H < σ) :
    (n : ℝ) * h ^ (2 * β + 1) *
        Real.exp (-(1 + noiseCost h σ) / 32) ≤ Real.exp (-2) := by
  have hσclosed : σ ∈ Icc (0 : ℝ) 1 := ⟨hσ.1.le, hσ.2⟩
  have hr := unique_rate_root β n σ hβ hn hσclosed
  have hd := directResolution_pos_le_one β n hβ hn
  have hHpos : 0 < H := by rw [hroot]; exact hd.1.trans_le hr.1.1
  have hHle : H ≤ 1 := by rw [hroot]; exact hr.1.2
  have hhH' : h ≤ H := hhH.trans (by nlinarith [hHpos])
  have hcostH : 0 ≤ noiseCost H σ :=
    noiseCost_nonneg H σ ⟨hHpos, hHle⟩ hσclosed
  have hratio := (noise_cost_scaling.2.1 h H σ hh hhH' hHσ.le hσ.2).1
  have hquotient : (4096 : ℝ) ≤ H / h := by
    apply (le_div_iff₀ hh).2
    nlinarith
  have hsqrt : (64 : ℝ) ≤ (H / h) ^ (1 / 2 : ℝ) := by
    have hp := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 4096) hquotient
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
    norm_num at hp ⊢
    exact hp
  have hcostratio : 64 * (1 + noiseCost H σ) ≤ 1 + noiseCost h σ := by
    have hden : 0 < 1 + noiseCost H σ := by linarith
    have hq : (64 : ℝ) ≤ (1 + noiseCost h σ) / (1 + noiseCost H σ) :=
      hsqrt.trans hratio
    exact (le_div_iff₀ hden).mp hq
  have hexp : Real.exp (-(1 + noiseCost h σ) / 32) ≤
      Real.exp (-2 * (1 + noiseCost H σ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hν : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hpowers : h ^ (2 * β + 1) ≤ H ^ (2 * β + 1) :=
    Real.rpow_le_rpow hh.le hhH' hν.le
  have hnnonneg : (0 : ℝ) ≤ n := by positivity
  have hbalance := rateRoot_exp_balance β n σ hβ hn hσclosed
  rw [← hroot] at hbalance
  calc
    (n : ℝ) * h ^ (2 * β + 1) * Real.exp (-(1 + noiseCost h σ) / 32) ≤
        (n : ℝ) * H ^ (2 * β + 1) * Real.exp (-(1 + noiseCost h σ) / 32) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowers hnnonneg) (Real.exp_pos _).le
    _ ≤ (n : ℝ) * H ^ (2 * β + 1) *
        Real.exp (-2 * (1 + noiseCost H σ)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = Real.exp (-2 - noiseCost H σ) := by
      rw [← hbalance, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)

/-- A small one-observation extended chi-square bound gives the testing
constant required by `two_point_transfer` after `n` IID observations. Given [the displayed inputs and assumptions](hyp:P,Q,σ,δ,n,hδ,hnδ,hchi), [the stated mathematical conclusion holds](goal). -/
lemma sampleLaw_tv_le_one_fifth_of_chiSqExt (P Q : LatentLaw) (σ δ : ℝ) (n : ℕ)
    (hδ : 0 ≤ δ) (hnδ : (n : ℝ) * δ ≤ 1 / 100)
    (hchi : chiSqExt (Pobs P σ) (Pobs Q σ) ≤ ENNReal.ofReal δ) :
    tvDist (sampleLaw P σ n) (sampleLaw Q σ n) ≤ (1 / 5 : ℝ) := by
  let μ := Pobs P σ
  let ν := Pobs Q σ
  letI : IsProbabilityMeasure μ := empirical_Pobs_probability P σ
  letI : IsProbabilityMeasure ν := empirical_Pobs_probability Q σ
  have hfinite : chiSqExt μ ν ≠ ⊤ :=
    ne_of_lt (hchi.trans_lt ENNReal.ofReal_lt_top)
  obtain ⟨hac, hint⟩ := (chiSqExt_ne_top_iff μ ν).mp hfinite
  have heq := chiSqExt_eq_ofReal_chiSqDiv μ ν hac hint
  have hchiReal : Causalean.Stat.chiSqDiv μ ν ≤ δ := by
    rw [heq] at hchi
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp hchi
  have hχnonneg : 0 ≤ Causalean.Stat.chiSqDiv μ ν :=
    Causalean.Stat.chiSqDiv_nonneg
  have hnχ : (n : ℝ) * Causalean.Stat.chiSqDiv μ ν ≤ 1 / 100 :=
    (mul_le_mul_of_nonneg_left hchiReal (by positivity)).trans hnδ
  change tvDist (sampleLaw P σ n) (sampleLaw Q σ n) ≤ (1 / 5 : ℝ)
  change tvDist (Measure.pi (fun _ : Fin n => μ))
    (Measure.pi (fun _ : Fin n => ν)) ≤ (1 / 5 : ℝ)
  exact Causalean.Stat.iid_tv_le_one_fifth_of_chiSqDiv μ ν hac hint n hnχ

/-- In the genuinely noisy regime, cancellation alternatives attain a fixed
multiple of the scalar frontier for both minimax criteria. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,β,hβ), [the stated mathematical conclusion holds](goal). -/
lemma noisy_frontier_lower (legendre_of_gate : ClassicalLegendreFacts)
    (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    let c := (4 / 5 : ℝ) * kappa * (1 / 16384 : ℝ)^β
    0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Ioc (0 : ℝ) 1,
      rateResolution β n σ < σ →
      c * frontierRate β n σ ≤ risk β n σ ∧
      c * frontierRate β n σ ≤ lengthRisk β n σ := by
  dsimp only
  have hc : 0 < (4 / 5 : ℝ) * kappa * (1 / 16384 : ℝ)^β := by
    norm_num [kappa]
    positivity
  refine ⟨hc, ?_⟩
  intro n hn σ hσ hHσ
  let H := rateResolution β n σ
  obtain ⟨m, hm3, hh_lower, hh_upper⟩ :=
    exists_noiseResolution_bracket σ H hσ
      ((directResolution_pos_le_one β n hβ hn).1.trans_le
        (unique_rate_root β n σ hβ hn ⟨hσ.1.le, hσ.2⟩).1.1)
      hHσ
  let h := noiseResolution σ m
  let b := noiseSupport σ m
  have hm : 2 ≤ m := by omega
  have hb := noiseSupport_mem σ m hσ hm
  have hhpos : 0 < h := by
    have hmreal : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmreal
    have hsupp : 0 < noiseSupport σ m := by
      unfold noiseSupport
      exact lt_min (by norm_num) (div_pos (mul_pos hσ.1 hsqrt) (by norm_num))
    dsimp [h, noiseResolution]
    exact div_pos hsupp (sq_pos_of_pos hmreal)
  let δ : ℝ := (32 / 3 : ℝ) * kappa^2 * h^(2*β+1) *
    Real.exp (-(1 + noiseCost h σ)/32)
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hnfactor := rounded_noise_information_factor β σ H h n hβ hn hσ rfl
    hhpos hh_upper hHσ
  have hnδ : (n : ℝ) * δ ≤ 1 / 100 := by
    have hexple : Real.exp (-2 : ℝ) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr (by norm_num)
    dsimp [δ]
    have hcoef : (0 : ℝ) ≤ (32 / 3 : ℝ) * kappa^2 := by positivity
    calc
      (n : ℝ) * ((32 / 3 : ℝ) * kappa ^ 2 * h ^ (2 * β + 1) *
          Real.exp (-(1 + noiseCost h σ) / 32)) =
          ((32 / 3 : ℝ) * kappa^2) *
            ((n : ℝ) * h^(2*β+1) * Real.exp (-(1 + noiseCost h σ)/32)) := by ring
      _ ≤ ((32 / 3 : ℝ) * kappa^2) * Real.exp (-2) :=
        mul_le_mul_of_nonneg_left hnfactor hcoef
      _ ≤ ((32 / 3 : ℝ) * kappa^2) * 1 :=
        mul_le_mul_of_nonneg_left hexple hcoef
      _ ≤ 1 / 100 := by norm_num [kappa]
  let P := altLaw legendre_of_gate β b m true hβ hb hm
  let Q := altLaw legendre_of_gate β b m false hβ hb hm
  have hchi : chiSqExt (Pobs P σ) (Pobs Q σ) ≤ ENNReal.ofReal δ := by
    exact cancellation_information_envelope β σ m hβ hσ hm
  have htv := sampleLaw_tv_le_one_fifth_of_chiSqExt P Q σ δ n hδ hnδ hchi
  have hlower := two_point_transfer β b σ n m hβ hb hm hn
    ⟨hσ.1.le, hσ.2⟩ htv
  change (4/5 : ℝ) * kappa * h^β ≤ risk β n σ ∧
    (6/5 : ℝ) * kappa * h^β ≤ lengthRisk β n σ at hlower
  have hHpos : 0 < H :=
    (directResolution_pos_le_one β n hβ hn).1.trans_le
      (unique_rate_root β n σ hβ hn ⟨hσ.1.le, hσ.2⟩).1.1
  have hscale : (H / 16384)^β = (1 / 16384 : ℝ)^β * H^β := by
    rw [div_eq_mul_inv, Real.mul_rpow hHpos.le
      (by positivity : (0 : ℝ) ≤ (16384 : ℝ)⁻¹)]
    ring_nf
  have hhpow : (H / 16384)^β ≤ h^β :=
    Real.rpow_le_rpow (by positivity) hh_lower.le hβ.1.le
  have hcommon : ((4 / 5 : ℝ) * kappa * (1 / 16384 : ℝ)^β) * H^β ≤
      (4 / 5 : ℝ) * kappa * h^β := by
    rw [show ((4 / 5 : ℝ) * kappa * (1 / 16384 : ℝ)^β) * H^β =
      (4 / 5 : ℝ) * kappa * ((H / 16384)^β) by rw [hscale]; ring]
    exact mul_le_mul_of_nonneg_left hhpow (by norm_num [kappa])
  change _ * H^β ≤ risk β n σ ∧ _ * H^β ≤ lengthRisk β n σ
  exact ⟨hcommon.trans hlower.1,
    hcommon.trans (hlower.2.trans' (by
      have hhnonneg : 0 ≤ kappa * h^β := by
        exact mul_nonneg (by norm_num [kappa]) (Real.rpow_nonneg hhpos.le _)
      nlinarith))⟩

/-- Combining the ordinary direct witness below the direct resolution with
the cancellation witness above it gives a uniform scalar-frontier converse. Given [the displayed inputs and assumptions](hyp:legendre_of_gate,hermite_of_gate,β,hβ), [the stated mathematical conclusion holds](goal). -/
theorem frontierRate_lower_bounds
    (legendre_of_gate : ClassicalLegendreFacts)
    (hermite_of_gate : ClassicalHermiteFacts)
    (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      c * frontierRate β n σ ≤ risk β n σ ∧
      c * frontierRate β n σ ≤ lengthRisk β n σ := by
  obtain ⟨cd, Cd, hcd, hCd, hdirect⟩ := direct_reduction β hβ
  obtain ⟨hnc, hnoise⟩ := noisy_frontier_lower legendre_of_gate β hβ
  let cn : ℝ := (4 / 5 : ℝ) * kappa * (1 / 16384 : ℝ)^β
  let c := min cd cn
  have hcn : 0 < cn := by exact hnc
  have hc : 0 < c := lt_min hcd hcn
  refine ⟨c, hc, ?_⟩
  intro n hn σ hσ
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hdirectLower := (hdirect n hn).1 σ hσ
  by_cases hs : σ ≤ directResolution β n
  · have hres := rateResolution_eq_direct_of_le β n σ hβ hn hσ hs
    have hrate : frontierRate β n σ = (n : ℝ)^(-β/(2*β+1)) := by
      unfold frontierRate
      rw [hres]
      unfold directResolution
      calc
        ((n : ℝ) ^ (-1 / (2 * β + 1))) ^ β =
            (n : ℝ) ^ ((-1 / (2 * β + 1)) * β) :=
          (Real.rpow_mul hnpos.le _ _).symm
        _ = (n : ℝ)^(-β/(2*β+1)) := by congr 1 <;> ring
    rw [hrate]
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left cd cn)
      (Real.rpow_nonneg hnpos.le _)).trans hdirectLower.1,
      (mul_le_mul_of_nonneg_right (min_le_left cd cn)
        (Real.rpow_nonneg hnpos.le _)).trans hdirectLower.2⟩
  · have hnoisy : directResolution β n < σ := lt_of_not_ge hs
    have hσpos : 0 < σ :=
      (directResolution_pos_le_one β n hβ hn).1.trans hnoisy
    have hHσ := (noisy_rateResolution_interior β n σ hβ hn hσ hnoisy).2
    have hnLower := hnoise n hn σ ⟨hσpos, hσ.2⟩ hHσ
    have hrate : 0 ≤ frontierRate β n σ := by
      unfold frontierRate
      exact Real.rpow_nonneg
        ((directResolution_pos_le_one β n hβ hn).1.trans_le
          (unique_rate_root β n σ hβ hn hσ).1.1).le _
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right cd cn) hrate).trans hnLower.1,
      (mul_le_mul_of_nonneg_right (min_le_right cd cn) hrate).trans hnLower.2⟩

end CausalSmith.Stat.RdTruesideNoiseFrontier
