module
public import CausalSmith.Stat.STAT_RdTruesideNoiseFrontier_Research.Helpers.FrontierRoot

/-!
# True-side Gaussian measurement-error endpoint frontier

Helpers/Law-level constructions and the obligations specified by the typed core.
Cited logical facts are explicit inputs; bibliographic records have no logical consumers.
-/

@[expose] public section

set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology

namespace CausalSmith.Stat.RdTruesideNoiseFrontier

/-- Explicit eventually-in-size comparisons for shrinking and fixed noise, and exact direct sequences. Given [the displayed inputs and assumptions](hyp:β), [this definition specifies the stated object](goal). -/
def FrontierSequences (β : ℝ) : Prop :=
  (∀ a : ℝ, 0 < a → a < 1/(2*β+1) →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c * ((n : ℝ)^(-a*β) * (Real.log n)^(-3*β/2)) ≤ frontierRate β n ((n : ℝ)^(-a)) ∧
      frontierRate β n ((n : ℝ)^(-a)) ≤ C * ((n : ℝ)^(-a*β) * (Real.log n)^(-3*β/2))) ∧
  (∀ a : ℝ, 1/(2*β+1) ≤ a → ∀ n : ℕ, 2 ≤ n →
    rateResolution β n ((n : ℝ)^(-a)) = directResolution β n ∧
    frontierRate β n ((n : ℝ)^(-a)) = (n : ℝ)^(-β/(2*β+1))) ∧
  (∀ σ ∈ Ioc (0 : ℝ) 1,
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c * (Real.log (1 + Real.log n) / (1 + Real.log n))^(2*β) ≤ frontierRate β n σ ∧
      frontierRate β n σ ≤ C * (Real.log (1 + Real.log n) / (1 + Real.log n))^(2*β))
/-- The beta-one shrinking-noise specialization holds at every declared sample size. Given the displayed inputs, [this definition specifies the stated object](goal). -/
def BetaOneFrontier : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    let σ := (n : ℝ) ^ (-1/6 : ℝ)
    directResolution 1 n < σ ∧ IntermediateCondition 1 n σ ∧
    frontierRate 1 n σ = rateResolution 1 n σ ∧
    c * (σ / (1 + (1/2 : ℝ)*Real.log n)^(3/2 : ℝ)) ≤ frontierRate 1 n σ ∧
    frontierRate 1 n σ ≤ C * (σ / (1 + (1/2 : ℝ)*Real.log n)^(3/2 : ℝ))

private lemma eventually_shrinking_intermediate (β a : ℝ)
    (hβ : 0 < β) (ha : 0 < a) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      IntermediateCondition β n ((n : ℝ) ^ (-a)) := by
  let k := 1 - 4 * a * (2 * β + 1)
  let ε := 1 / (2 * (|k| + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hpowexp : 0 < 2 * a := by positivity
  have hsmall := (isLittleO_log_rpow_atTop hpowexp).bound hε
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hevsmall : ∀ᶠ n : ℕ in atTop,
      ‖Real.log (n : ℝ)‖ ≤ ε * ‖(n : ℝ) ^ (2 * a)‖ := hsmall.filter_mono hcast
  have hevpow : ∀ᶠ n : ℕ in atTop, 2 ≤ (n : ℝ) ^ (2 * a) :=
    ((tendsto_rpow_atTop hpowexp).comp hcast).eventually (eventually_ge_atTop 2)
  have hev : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ IntermediateCondition β n ((n : ℝ) ^ (-a)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hevsmall, hevpow] with n hn hs hp
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hnlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hpowpos : 0 < (n : ℝ) ^ (2 * a) := Real.rpow_pos_of_pos hnpos _
    have hs' : Real.log n ≤ ε * (n : ℝ) ^ (2 * a) := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hnlog, abs_of_pos hpowpos] using hs
    have hk : k * Real.log n ≤ ((n : ℝ) ^ (2 * a)) / 2 := by
      have hkle : k ≤ |k| := le_abs_self k
      have habs : |k| * ε ≤ 1 / 2 := by
        dsimp [ε]
        have hkden : 0 < |k| + 1 := by positivity
        have hkfrac : |k| / (|k| + 1) ≤ 1 :=
          (div_le_one hkden).2 (by linarith [abs_nonneg k])
        calc
          |k| * (1 / (2 * (|k| + 1))) = (1 / 2) * (|k| / (|k| + 1)) := by
            field_simp
          _ ≤ (1 / 2) * 1 := mul_le_mul_of_nonneg_left hkfrac (by norm_num)
          _ = 1 / 2 := by ring
      calc
        k * Real.log n ≤ |k| * Real.log n := mul_le_mul_of_nonneg_right hkle hnlog
        _ ≤ |k| * (ε * (n : ℝ) ^ (2 * a)) :=
          mul_le_mul_of_nonneg_left hs' (abs_nonneg k)
        _ ≤ (1 / 2) * (n : ℝ) ^ (2 * a) := by
          nlinarith [mul_le_mul_of_nonneg_right habs hpowpos.le]
        _ = (n : ℝ) ^ (2 * a) / 2 := by ring
    have hmain : k * Real.log n ≤ (n : ℝ) ^ (2 * a) - 1 := by nlinarith
    refine ⟨hn, ?_⟩
    unfold IntermediateCondition
    have hspos : 0 < (n : ℝ) ^ (-a) := Real.rpow_pos_of_pos hnpos _
    have hpowNoise : ((n : ℝ) ^ (-a)) ^ (4 * (2 * β + 1)) =
        (n : ℝ) ^ (-a * (4 * (2 * β + 1))) := by
      rw [← Real.rpow_mul hnpos.le]
    have hprod : (n : ℝ) * (n : ℝ) ^ (-a * (4 * (2 * β + 1))) =
        (n : ℝ) ^ k := by
      dsimp [k]
      calc
        (n : ℝ) * (n : ℝ) ^ (-a * (4 * (2 * β + 1))) =
            (n : ℝ) ^ (-a * (4 * (2 * β + 1))) * n := mul_comm _ _
        _ = (n : ℝ) ^ (-a * (4 * (2 * β + 1))) * (n : ℝ) ^ (1 : ℝ) := by
          rw [Real.rpow_one]
        _ = (n : ℝ) ^ (-a * (4 * (2 * β + 1)) + 1) :=
          (Real.rpow_add hnpos _ _).symm
        _ = (n : ℝ) ^ (1 - 4 * a * (2 * β + 1)) := by congr 1 <;> ring
    have hinv : ((n : ℝ) ^ (-a)) ^ (-2 : ℝ) = (n : ℝ) ^ (2 * a) := by
      rw [← Real.rpow_mul hnpos.le]
      congr 1
      ring
    rw [hpowNoise, hprod, hinv, Real.log_rpow hnpos]
    exact hmain
  rcases (show ∃ N, ∀ n ≥ N, 2 ≤ n ∧
      IntermediateCondition β n ((n : ℝ) ^ (-a)) by
        simpa only [eventually_atTop] using hev) with ⟨N, hN⟩
  refine ⟨max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  exact (hN n (le_trans (le_max_right 2 N) hn)).2

private lemma shrinking_intermediate_rate_bounds (β a c₀ C₀ : ℝ)
    (hβ : 0 < β) (ha : 0 < a) (ha' : a < 1 / (2 * β + 1))
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hbranches : ∀ n : ℕ, 2 ≤ n → ∀ σ ∈ Icc (0 : ℝ) 1,
      FrontierBranches β n σ c₀ C₀) :
    let d := 1 - a * (2 * β + 1)
    let K := d + 1 / Real.log 2
    ∀ n : ℕ, 2 ≤ n → IntermediateCondition β n ((n : ℝ) ^ (-a)) →
      (c₀ / K ^ (3 / 2 : ℝ)) ^ β *
          ((n : ℝ) ^ (-a * β) * (Real.log n) ^ (-3 * β / 2)) ≤
        frontierRate β n ((n : ℝ) ^ (-a)) ∧
      frontierRate β n ((n : ℝ) ^ (-a)) ≤
        (C₀ / d ^ (3 / 2 : ℝ)) ^ β *
          ((n : ℝ) ^ (-a * β) * (Real.log n) ^ (-3 * β / 2)) := by
  dsimp only
  let d := 1 - a * (2 * β + 1)
  let K := d + 1 / Real.log 2
  have hν : 0 < 2 * β + 1 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    have := (lt_div_iff₀ hν).mp ha'
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < K := by dsimp [K]; positivity
  intro n hn hinter
  let σ := (n : ℝ) ^ (-a)
  let L := Real.log n
  let S := 1 + Real.log ((n : ℝ) * σ ^ (2 * β + 1))
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnone : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hL2 : Real.log 2 ≤ L := by
    dsimp [L]
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) hnpos
      (by exact_mod_cast hn)
  have hL : 0 < L := hlog2.trans_le hL2
  have hspos : 0 < σ := Real.rpow_pos_of_pos hnpos _
  have hsone : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnone.le (by linarith)
  have hprodlog : Real.log ((n : ℝ) * σ ^ (2 * β + 1)) = d * L := by
    have hspow : σ ^ (2 * β + 1) = (n : ℝ) ^ (-a * (2 * β + 1)) := by
      dsimp [σ]
      rw [← Real.rpow_mul hnpos.le]
    rw [hspow, Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hnpos _).ne',
      Real.log_rpow hnpos]
    dsimp [d, L]
    ring
  have hS : S = 1 + d * L := by dsimp [S]; rw [hprodlog]
  have hdL : 0 < d * L := mul_pos hd hL
  have hlowS : d * L ≤ S := by rw [hS]; linarith
  have hone : 1 ≤ (1 / Real.log 2) * L := by
    have hx : 1 ≤ L / Real.log 2 := (le_div_iff₀ hlog2).2 (by simpa using hL2)
    simpa [div_eq_mul_inv, mul_comm] using hx
  have huppS : S ≤ K * L := by
    rw [hS]
    dsimp [K]
    nlinarith
  have hSpos : 0 < S := hdL.trans_le hlowS
  have hKL : 0 < K * L := mul_pos hK hL
  have hp : (0 : ℝ) < 3 / 2 := by norm_num
  have hpLow := Real.rpow_le_rpow hdL.le hlowS hp.le
  have hpUp := Real.rpow_le_rpow hSpos.le huppS hp.le
  have hbaseLow : (1 / K ^ (3 / 2 : ℝ)) *
      (σ * L ^ (-3 / 2 : ℝ)) ≤ σ / S ^ (3 / 2 : ℝ) := by
    rw [Real.mul_rpow hK.le hL.le] at hpUp
    rw [div_eq_mul_inv, show L ^ (-3 / 2 : ℝ) = (L ^ (3 / 2 : ℝ))⁻¹ by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hL.le]]
    have := div_le_div_of_nonneg_left hspos.le (Real.rpow_pos_of_pos hSpos _) hpUp
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hK _), ne_of_gt (Real.rpow_pos_of_pos hL _)] at this ⊢
    nlinarith
  have hbaseUp : σ / S ^ (3 / 2 : ℝ) ≤
      (1 / d ^ (3 / 2 : ℝ)) * (σ * L ^ (-3 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, show L ^ (-3 / 2 : ℝ) = (L ^ (3 / 2 : ℝ))⁻¹ by
      rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by norm_num, Real.rpow_neg hL.le]]
    have := div_le_div_of_nonneg_left hspos.le (Real.rpow_pos_of_pos hdL _) hpLow
    rw [Real.mul_rpow hd.le hL.le] at this
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hd _), ne_of_gt (Real.rpow_pos_of_pos hL _)] at this ⊢
    nlinarith
  have hb := hbranches n hn σ ⟨hspos.le, hsone⟩
  have hdirect : directResolution β n < σ := by
    unfold directResolution
    exact Real.rpow_lt_rpow_of_exponent_lt hnone (by simpa [neg_div] using neg_lt_neg ha')
  obtain ⟨_, _, _, hinterPart, _⟩ := hb.2.1 hdirect
  obtain ⟨z, hz1, hzup, hzeq, hres, hu, hlo, hhi⟩ := hinterPart hinter
  have hPpos : 0 < σ / S ^ (3 / 2 : ℝ) := div_pos hspos (Real.rpow_pos_of_pos hSpos _)
  have hHpos : 0 < rateResolution β n σ :=
    (mul_pos hc₀ hPpos).trans_le (by simpa [S] using hlo)
  have hpowers := Real.rpow_le_rpow
    (mul_nonneg hc₀.le hPpos.le) (by simpa [S] using hlo) hβ.le
  have hpowers' := Real.rpow_le_rpow hHpos.le (by simpa [S] using hhi) hβ.le
  have hscale : (σ * L ^ (-3 / 2 : ℝ)) ^ β =
      (n : ℝ) ^ (-a * β) * L ^ (-3 * β / 2) := by
    rw [Real.mul_rpow hspos.le (Real.rpow_nonneg hL.le _), ← Real.rpow_mul hnpos.le,
      ← Real.rpow_mul hL.le]
    congr 1 <;> ring
  unfold frontierRate
  constructor
  · calc
      (c₀ / K ^ (3 / 2 : ℝ)) ^ β *
          ((n : ℝ) ^ (-a * β) * L ^ (-3 * β / 2)) =
          (c₀ * ((1 / K ^ (3 / 2 : ℝ)) * (σ * L ^ (-3 / 2 : ℝ)))) ^ β := by
            rw [← hscale, ← Real.mul_rpow
              (by positivity : 0 ≤ c₀ / K ^ (3 / 2 : ℝ))
              (by positivity : 0 ≤ σ * L ^ (-3 / 2 : ℝ))]
            congr 1
            field_simp [ne_of_gt (Real.rpow_pos_of_pos hK _)]
      _ ≤ (c₀ * (σ / S ^ (3 / 2 : ℝ))) ^ β :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hbaseLow hc₀.le) hβ.le
      _ ≤ rateResolution β n σ ^ β := hpowers
  · calc
      rateResolution β n σ ^ β ≤ (C₀ * (σ / S ^ (3 / 2 : ℝ))) ^ β := hpowers'
      _ ≤ (C₀ * ((1 / d ^ (3 / 2 : ℝ)) * (σ * L ^ (-3 / 2 : ℝ)))) ^ β :=
        Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hbaseUp hC₀.le) hβ.le
      _ = (C₀ / d ^ (3 / 2 : ℝ)) ^ β *
          ((n : ℝ) ^ (-a * β) * L ^ (-3 * β / 2)) := by
            rw [← hscale, ← Real.mul_rpow
              (by positivity : 0 ≤ C₀ / d ^ (3 / 2 : ℝ))
              (by positivity : 0 ≤ σ * L ^ (-3 / 2 : ℝ))]
            congr 1
            field_simp [ne_of_gt (Real.rpow_pos_of_pos hd _)]

private lemma fixed_noise_rate_bounds (β σ c₀ C₀ : ℝ)
    (hβ : β ∈ Ioc (0 : ℝ) 1) (hσ : σ ∈ Ioc (0 : ℝ) 1)
    (hc₀ : 0 < c₀) (hC₀ : 0 < C₀)
    (hbranches : ∀ n : ℕ, 2 ≤ n → ∀ s ∈ Icc (0 : ℝ) 1,
      FrontierBranches β n s c₀ C₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      c * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β) ≤
          frontierRate β n σ ∧
      frontierRate β n σ ≤
        C * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β) := by
  let ℓσ := Real.log (σ ^ 2)
  let M := max 1 (max (-2 * ℓσ) |Real.log (Real.exp 1 + σ ^ 2)|)
  let K := 1 + |Real.log (Real.exp 1 + σ ^ 2)|
  let c := c₀ * (1 / 2 : ℝ) ^ (2 * β)
  let C := C₀ * K ^ (2 * β)
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < c := mul_pos hc₀ (Real.rpow_pos_of_pos (by norm_num) _)
  have hC : 0 < C := mul_pos hC₀ (Real.rpow_pos_of_pos hK _)
  have hν : 0 < 2 * β + 1 := by linarith [hβ.1]
  have hlogn : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hevM : ∀ᶠ n : ℕ in atTop, Real.exp M ≤ Real.log n :=
    (tendsto_atTop.1 hlogn) (Real.exp M)
  let T := σ ^ (-2 : ℝ) - 1 - 4 * (2 * β + 1) * Real.log σ
  have hevT : ∀ᶠ n : ℕ in atTop, T + 1 ≤ Real.log n :=
    (tendsto_atTop.1 hlogn) (T + 1)
  have hdirT : Tendsto (fun n : ℕ => (n : ℝ) ^ (-1 / (2 * β + 1)))
      atTop (nhds 0) := by
    have he : 0 < 1 / (2 * β + 1) := one_div_pos.mpr hν
    simpa [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop he).comp tendsto_natCast_atTop_atTop
  have hevDirect : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-1 / (2 * β + 1)) < σ :=
    hdirT.eventually_lt_const hσ.1
  have hev : ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ (c * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β) ≤
          frontierRate β n σ ∧ frontierRate β n σ ≤
        C * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β)) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ), hevM, hevT, hevDirect] with n hn hM hT hdirect
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hnlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    let B := 1 + Real.log n
    let L := Real.log B
    let D := Real.log (Real.exp 1 + σ ^ 2 * B)
    have hB : 1 < B := by dsimp [B]; linarith
    have hBpos : 0 < B := zero_lt_one.trans hB
    have hMone : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
    have hexpM : Real.exp M ≤ B := by
      have : Real.exp M < B := by dsimp [B]; linarith
      exact this.le
    have hLM : M ≤ L := by
      dsimp [L]
      rw [← Real.log_exp M]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos M) hBpos hexpM
    have hL : 0 < L := lt_of_lt_of_le (by norm_num) (hMone.trans hLM)
    have hℓlower : -2 * ℓσ ≤ L :=
      (le_max_left (-2 * ℓσ) |Real.log (Real.exp 1 + σ ^ 2)|).trans
        ((le_max_right 1 (max (-2 * ℓσ) |Real.log (Real.exp 1 + σ ^ 2)|)).trans hLM)
    have hconst : |Real.log (Real.exp 1 + σ ^ 2)| ≤ L :=
      (le_max_right (-2 * ℓσ) |Real.log (Real.exp 1 + σ ^ 2)|).trans
        ((le_max_right 1 (max (-2 * ℓσ) |Real.log (Real.exp 1 + σ ^ 2)|)).trans hLM)
    have hDpos : 0 < D := by
      dsimp [D]
      apply Real.log_pos
      have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      have hx : 0 ≤ σ ^ 2 * B := mul_nonneg (sq_nonneg σ) hBpos.le
      linarith
    have hDlow : (1 / 2 : ℝ) * L ≤ D := by
      have harg : σ ^ 2 * B ≤ Real.exp 1 + σ ^ 2 * B := by linarith [Real.exp_pos 1]
      have hlogarg := Real.strictMonoOn_log.monotoneOn
        (mul_pos (sq_pos_of_pos hσ.1) hBpos)
        (by positivity : 0 < Real.exp 1 + σ ^ 2 * B) harg
      have hlogprod : Real.log (σ ^ 2 * B) = ℓσ + L := by
        dsimp [ℓσ, L]
        rw [Real.log_mul (sq_pos_of_pos hσ.1).ne' hBpos.ne']
      rw [hlogprod] at hlogarg
      nlinarith
    have hDup : D ≤ K * L := by
      have harg : Real.exp 1 + σ ^ 2 * B ≤ (Real.exp 1 + σ ^ 2) * B := by
        nlinarith [hB.le, Real.exp_pos 1, sq_nonneg σ]
      have hlogarg := Real.strictMonoOn_log.monotoneOn
        (by positivity : 0 < Real.exp 1 + σ ^ 2 * B)
        (mul_pos (by positivity) hBpos) harg
      have hlogprod : Real.log ((Real.exp 1 + σ ^ 2) * B) =
          Real.log (Real.exp 1 + σ ^ 2) + L := by
        dsimp [L]
        rw [Real.log_mul (by positivity : Real.exp 1 + σ ^ 2 ≠ 0) hBpos.ne']
      dsimp [D, K] at hlogarg ⊢
      rw [hlogprod] at hlogarg
      have hcst := le_trans (le_abs_self (Real.log (Real.exp 1 + σ ^ 2))) hconst
      have hLone : 1 ≤ L := hMone.trans hLM
      have habsnonneg : 0 ≤ |Real.log (Real.exp 1 + σ ^ 2)| := abs_nonneg _
      have hmul : |Real.log (Real.exp 1 + σ ^ 2)| ≤
          |Real.log (Real.exp 1 + σ ^ 2)| * L := by nlinarith
      have hcst2 : Real.log (Real.exp 1 + σ ^ 2) ≤
          |Real.log (Real.exp 1 + σ ^ 2)| * L :=
        (le_abs_self _).trans hmul
      nlinarith
    have hnotInter : ¬ IntermediateCondition β n σ := by
      unfold IntermediateCondition
      intro hi
      have hlogprod : Real.log ((n : ℝ) * σ ^ (4 * (2 * β + 1))) =
          Real.log n + 4 * (2 * β + 1) * Real.log σ := by
        rw [Real.log_mul hnpos.ne' (Real.rpow_pos_of_pos hσ.1 _).ne',
          Real.log_rpow hσ.1]
      rw [hlogprod] at hi
      dsimp [T] at hT
      linarith
    have hb := hbranches n hn σ ⟨hσ.1.le, hσ.2⟩
    have hi := hb.2.1 (by simpa [directResolution] using hdirect)
    obtain ⟨τ, hτ, heq, hres, hu, htlo, hthi, hrlo, hrhi⟩ := hi.2.2.2.2 hnotInter
    have hratioLow : (1 / 2 : ℝ) * (L / B) ≤ D / B :=
      by simpa [mul_div_assoc] using (div_le_div_iff_of_pos_right hBpos).2 hDlow
    have hratioUp : D / B ≤ K * (L / B) := by
      apply (div_le_iff₀ hBpos).2
      calc
        D ≤ K * L := hDup
        _ = K * (L / B) * B := by field_simp
    have hpLow := Real.rpow_le_rpow
      (mul_nonneg (by norm_num) (div_nonneg hL.le hBpos.le)) hratioLow
        (by nlinarith [hβ.1] : 0 ≤ 2 * β)
    have hpUp := Real.rpow_le_rpow (div_nonneg hDpos.le hBpos.le) hratioUp
      (by nlinarith [hβ.1] : 0 ≤ 2 * β)
    refine ⟨hn, ?_, ?_⟩
    · calc
        c * (L / B) ^ (2 * β) = c₀ * (((1 / 2 : ℝ) * (L / B)) ^ (2 * β)) := by
          dsimp [c]
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2)
            (div_nonneg hL.le hBpos.le)]
          ring
        _ ≤ c₀ * (D / B) ^ (2 * β) := mul_le_mul_of_nonneg_left hpLow hc₀.le
        _ ≤ frontierRate β n σ := by simpa [D, B] using hrlo
    · calc
        frontierRate β n σ ≤ C₀ * (D / B) ^ (2 * β) := by simpa [D, B] using hrhi
        _ ≤ C₀ * ((K * (L / B)) ^ (2 * β)) :=
          mul_le_mul_of_nonneg_left hpUp hC₀.le
        _ = C * (L / B) ^ (2 * β) := by
          dsimp [C]
          rw [Real.mul_rpow hK.le (div_nonneg hL.le hBpos.le)]
          ring
  rcases (show ∃ N : ℕ, ∀ n : ℕ, n ≥ N → 2 ≤ n ∧
      (c * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β) ≤
          frontierRate β n σ ∧ frontierRate β n σ ≤
        C * (Real.log (1 + Real.log n) / (1 + Real.log n)) ^ (2 * β)) by
      simpa only [eventually_atTop] using hev) with ⟨N, hN⟩
  refine ⟨c, C, hc, hC, max 2 N, le_max_left _ _, ?_⟩
  intro n hn
  exact (hN n (le_trans (le_max_right 2 N) hn)).2

/-- The exact scalar formulas imply the shrinking-noise and fixed-noise asymptotic comparisons. Given [the displayed inputs and assumptions](hyp:β,hβ), [the stated mathematical conclusion holds](goal). -/
lemma frontier_sequences (β : ℝ) (hβ : β ∈ Ioc (0 : ℝ) 1) : FrontierSequences β := by
  obtain ⟨c₀, C₀, hc₀, hC₀, hbranches⟩ := frontier_branches β hβ
  unfold FrontierSequences
  refine ⟨?_, ?_, ?_⟩
  · intro a ha ha'
    let d := 1 - a * (2 * β + 1)
    let K := d + 1 / Real.log 2
    let c := (c₀ / K ^ (3 / 2 : ℝ)) ^ β
    let C := (C₀ / d ^ (3 / 2 : ℝ)) ^ β
    have hν : 0 < 2 * β + 1 := by linarith [hβ.1]
    have hd : 0 < d := by
      dsimp [d]
      nlinarith [(lt_div_iff₀ hν).mp ha']
    have hK : 0 < K := by
      dsimp [K]
      have : 0 < Real.log 2 := Real.log_pos (by norm_num)
      positivity
    have hc : 0 < c := Real.rpow_pos_of_pos (div_pos hc₀ (Real.rpow_pos_of_pos hK _)) _
    have hC : 0 < C := Real.rpow_pos_of_pos (div_pos hC₀ (Real.rpow_pos_of_pos hd _)) _
    obtain ⟨N, hN2, hN⟩ := eventually_shrinking_intermediate β a hβ.1 ha
    refine ⟨c, C, hc, hC, N, hN2, ?_⟩
    intro n hn
    have hbounds := shrinking_intermediate_rate_bounds β a c₀ C₀ hβ.1 ha ha'
      hc₀ hC₀ hbranches n (hN2.trans hn) (hN n hn)
    simpa [c, C, d, K] using hbounds
  · intro a ha n hn
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hnone : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hν : 0 < 2 * β + 1 := by linarith [hβ.1]
    let σ := (n : ℝ) ^ (-a)
    have hspos : 0 < σ := Real.rpow_pos_of_pos hnpos _
    have hsone : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnone.le (by
      have : 0 < 1 / (2 * β + 1) := one_div_pos.mpr hν
      linarith)
    have hsle : σ ≤ directResolution β n := by
      unfold directResolution
      exact Real.rpow_le_rpow_of_exponent_le hnone.le (by
        have := neg_le_neg ha
        simpa [neg_div] using this)
    have hb := hbranches n hn σ ⟨hspos.le, hsone⟩
    have hres := hb.1 hsle
    refine ⟨hres, ?_⟩
    unfold frontierRate
    rw [hres]
    unfold directResolution
    calc
      ((n : ℝ) ^ (-1 / (2 * β + 1))) ^ β =
          (n : ℝ) ^ ((-1 / (2 * β + 1)) * β) :=
        (Real.rpow_mul hnpos.le _ _).symm
      _ = (n : ℝ) ^ (-β / (2 * β + 1)) := by congr 1 <;> ring
  · intro σ hσ
    exact fixed_noise_rate_bounds β σ c₀ C₀ hβ hσ hc₀ hC₀ hbranches
/-- The beta-one example lies on the intermediate branch at every sample size. Given the displayed inputs, [the stated mathematical conclusion holds](goal). -/
lemma beta_one_frontier : BetaOneFrontier := by
  obtain ⟨c, C, hc, hC, hbranches⟩ :=
    frontier_branches 1 (by constructor <;> norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  intro n hn
  dsimp only
  let σ : ℝ := (n : ℝ) ^ (-1 / 6 : ℝ)
  change directResolution 1 n < σ ∧ IntermediateCondition 1 n σ ∧
    frontierRate 1 n σ = rateResolution 1 n σ ∧
    c * (σ / (1 + (1 / 2 : ℝ) * Real.log n) ^ (3 / 2 : ℝ)) ≤ frontierRate 1 n σ ∧
    frontierRate 1 n σ ≤ C * (σ / (1 + (1 / 2 : ℝ) * Real.log n) ^ (3 / 2 : ℝ))
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnone : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hspos : 0 < σ := Real.rpow_pos_of_pos hnpos _
  have hsone : σ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hnone.le (by norm_num)
  have hdirect : directResolution 1 n = (n : ℝ) ^ (-1 / 3 : ℝ) := by
    unfold directResolution
    norm_num
  have hnoisy : directResolution 1 n < σ := by
    rw [hdirect]
    dsimp [σ]
    exact Real.rpow_lt_rpow_of_exponent_lt hnone (by norm_num)
  have hs12 : σ ^ (12 : ℝ) = (n : ℝ) ^ (-2 : ℝ) := by
    dsimp [σ]
    rw [← Real.rpow_mul hnpos.le]
    norm_num
  have hs12nat : σ ^ (12 : ℕ) = (n : ℝ) ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast]
    exact hs12
  have hsInv2 : σ ^ (-2 : ℝ) = (n : ℝ) ^ (1 / 3 : ℝ) := by
    dsimp [σ]
    rw [← Real.rpow_mul hnpos.le]
    norm_num
  have hprod : (n : ℝ) * σ ^ (12 : ℝ) = (n : ℝ) ^ (-1 : ℝ) := by
    rw [hs12]
    convert (Real.rpow_add hnpos 1 (-2)).symm using 1 <;> norm_num
  have hprodNat : (n : ℝ) * σ ^ (12 : ℕ) = (n : ℝ) ^ (-1 : ℝ) := by
    rw [hs12nat]
    convert (Real.rpow_add hnpos 1 (-2)).symm using 1 <;> norm_num
  have hsInvNat : (σ ^ (2 : ℕ))⁻¹ = σ ^ (-2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg hspos.le]
    norm_num
  have hinter : IntermediateCondition 1 n σ := by
    unfold IntermediateCondition
    norm_num
    rw [hprodNat, hsInvNat, hsInv2, Real.log_rpow hnpos]
    have hpowone : 1 ≤ (n : ℝ) ^ (1 / 3 : ℝ) :=
      Real.one_le_rpow hnone.le (by norm_num)
    nlinarith [Real.log_pos hnone]
  have hb := hbranches n hn σ ⟨hspos.le, hsone⟩
  have hi := hb.2.1 hnoisy
  have hrate : frontierRate 1 n σ = rateResolution 1 n σ := by
    simp [frontierRate]
  have hprod3 : (n : ℝ) * σ ^ (3 : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) := by
    dsimp [σ]
    rw [← Real.rpow_mul hnpos.le]
    convert (Real.rpow_add hnpos 1 (-1 / 6 * 3)).symm using 1 <;> norm_num
  have hlog : Real.log ((n : ℝ) * σ ^ (3 : ℝ)) =
      (1 / 2 : ℝ) * Real.log n := by rw [hprod3, Real.log_rpow hnpos]
  obtain ⟨z, hz1, hzup, hzeq, hres, hu, hlo, hhi⟩ := hi.2.2.2.1 hinter
  norm_num at hlo hhi
  refine ⟨hnoisy, hinter, hrate, ?_, ?_⟩
  · rw [hrate, ← hlog]
    simpa using hlo
  · rw [hrate, ← hlog]
    simpa using hhi

end CausalSmith.Stat.RdTruesideNoiseFrontier
