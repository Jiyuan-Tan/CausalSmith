module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.FourierTuning

/-! Fourier dictionary tuning and comparison witness. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology FourierTransform
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The declared integer-power bandwidth is the usual decreasing dyadic sequence. [This is the stated conclusion](goal). -/
-- @node: dyadicBandwidth_eq_inv_pow
lemma dyadicBandwidth_eq_inv_pow (k : ℕ) :
    dyadicBandwidth k = ((2 : ℝ) ^ k)⁻¹ := by
  simp [dyadicBandwidth, zpow_neg]

/-- Rounding up to a dyadic bandwidth enlarges a positive scale by less than two. [Under the stated conditions](hyp:h,hh,hupper). [This is the stated conclusion](goal). -/
-- @node: dyadicBandwidth_round_up
lemma dyadicBandwidth_round_up (h : ℝ) (hh : 0 < h) (hupper : h ≤ 1) :
    ∃ k : ℕ, h ≤ dyadicBandwidth k ∧ dyadicBandwidth k < 2*h := by
  obtain ⟨k, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one hh hupper
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1 / 2 : ℝ) < 1)
  have he (j : ℕ) : (1 / 2 : ℝ)^j = dyadicBandwidth j := by
    rw [dyadicBandwidth_eq_inv_pow]
    simp [one_div, inv_pow]
  refine ⟨k, by simpa only [he] using hhi, ?_⟩
  rw [pow_succ, he] at hlo
  linarith

/-- Every dyadic bandwidth in the declared numerical window is a Fourier dictionary member.
The lower bandwidth cutoff also implies the finite index cutoff. [Under the stated conditions](hyp:hn,hhi,hlo). [This is the stated conclusion](goal). -/
-- @node: fourier_mem_weightDictionary_of_window
lemma fourier_mem_weightDictionary_of_window (n k : ℕ) (sigma : ℝ) (hn : 0 < n)
    (hlo : (n : ℝ) ^ (-2 : ℝ) ≤ dyadicBandwidth k)
    (hhi : dyadicBandwidth k ≤ 1/4) :
    DictTag.fourier k ∈ weightDictionary n sigma := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (2 : ℝ) ^ k ≤ (n : ℝ) ^ 2 := by
    rw [dyadicBandwidth_eq_inv_pow] at hlo
    rw [Real.rpow_neg hnR.le, Real.rpow_two] at hlo
    exact (inv_le_inv₀ (sq_pos_of_pos hnR) (by positivity)).mp hlo
  have hkpow : ∀ j : ℕ, (j : ℝ) ≤ (2 : ℝ) ^ j := by
    intro j
    induction j with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ, Nat.cast_add, Nat.cast_one]
      have hp : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
      linarith
  have hk : k < n^2+1 := by
    have : k ≤ n^2 := by exact_mod_cast (hkpow k).trans hpow
    omega
  simp only [weightDictionary, List.mem_toFinset, dictionaryList, List.mem_append,
    List.mem_singleton, List.mem_map, List.mem_filter, List.mem_range]
  exact Or.inl (Or.inr ⟨k, ⟨hk, by simpa using And.intro hlo hhi⟩, rfl⟩)

/-- A scale within the window can be rounded up to an available dictionary bandwidth. [Under the stated conditions](hyp:h,hn,hh,hhi,hlo). [This is the stated conclusion](goal). -/
-- @node: fourier_dictionary_round_up
lemma fourier_dictionary_round_up (n : ℕ) (sigma h : ℝ) (hn : 0 < n)
    (hh : 0 < h) (hlo : (n : ℝ) ^ (-2 : ℝ) ≤ h) (hhi : h ≤ 1 / 8) :
    ∃ k : ℕ, DictTag.fourier k ∈ weightDictionary n sigma ∧
      h ≤ dyadicBandwidth k ∧ dyadicBandwidth k < 2*h := by
  obtain ⟨k, hklo, hkhi⟩ := dyadicBandwidth_round_up h hh (by linarith)
  exact ⟨k, fourier_mem_weightDictionary_of_window n k sigma hn (hlo.trans hklo)
    (by linarith), hklo, hkhi⟩

/-- Enlarging the bandwidth decreases every factor in the stochastic S8 bound. [Under the stated conditions](hyp:h,H,hkappa,hsigma,hh,hhH). [This is the stated conclusion](goal). -/
-- @node: fourier_stochastic_antitone
lemma fourier_stochastic_antitone (kappa sigma : ℝ) (n : ℕ) (h H : ℝ)
    (hkappa : 0 ≤ kappa) (hsigma : 0 ≤ sigma) (hh : 0 < h) (hhH : h ≤ H) :
    Real.sqrt (H^(-kappa-1) * (1+sigma/H)^10 *
      Real.exp (36*(sigma/H)^2) / n) ≤
    Real.sqrt (h^(-kappa-1) * (1+sigma/h)^10 *
      Real.exp (36*(sigma/h)^2) / n) := by
  have hH : 0 < H := hh.trans_le hhH
  have hratio : sigma/H ≤ sigma/h := div_le_div_of_nonneg_left hsigma hh hhH
  have hbase : H^(-kappa-1) ≤ h^(-kappa-1) :=
    Real.rpow_le_rpow_of_nonpos hh hhH (by linarith)
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply mul_le_mul _ _ (by positivity) (by positivity)
  · exact mul_le_mul hbase (pow_le_pow_left₀ (by positivity) (by linarith) 10)
      (by positivity) (by positivity)
  · apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio 2)
      (by norm_num)

/-- The direct scale balances squared bias against inverse weighted sample size. [Under the stated conditions](hyp:hn,hd). [This is the stated conclusion](goal). -/
-- @node: directScale_power_balance
lemma directScale_power_balance (beta kappa : ℝ) (n : ℕ) (hn : 0 < n)
    (hd : 0 < effDim beta kappa) :
    directScale beta kappa n ^ effDim beta kappa = 1/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold directScale
  rw [← Real.rpow_mul hnR.le]
  rw [show (-1 / effDim beta kappa) * effDim beta kappa = -1 by
    field_simp, Real.rpow_neg_one]
  simp only [one_div]

/-- The exact S8 stochastic factor at the direct scale, before its bounded noise multiplier. [Under the stated conditions](hyp:hn,hd). [This is the stated conclusion](goal). -/
-- @node: directScale_variance_balance
lemma directScale_variance_balance (beta kappa : ℝ) (n : ℕ) (hn : 0 < n)
    (hd : 0 < effDim beta kappa) :
    directScale beta kappa n ^ (-kappa-1) / n =
      (directScale beta kappa n ^ beta)^2 := by
  have hh : 0 < directScale beta kappa n := by
    unfold directScale
    apply Real.rpow_pos_of_pos
    exact_mod_cast hn
  rw [div_eq_mul_inv, ← one_div (n : ℝ), ← directScale_power_balance beta kappa n hn hd,
    ← Real.rpow_add hh]
  rw [show -kappa-1+effDim beta kappa = beta*2 by unfold effDim; ring,
    Real.rpow_mul hh.le, Real.rpow_two]

/-- At the direct scale the unweighted sample-frequency term is smaller than the bias. [Under the stated conditions](hyp:hn,hbeta,hkappa). [This is the stated conclusion](goal). -/
-- @node: directScale_frequency_bound
lemma directScale_frequency_bound (beta kappa : ℝ) (n : ℕ) (hn : 0 < n)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    Real.sqrt (1/(n : ℝ)) ≤ directScale beta kappa n ^ beta := by
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hh : 0 < directScale beta kappa n := Real.rpow_pos_of_pos (by linarith) _
  have hh1 : directScale beta kappa n ≤ 1 := by
    unfold directScale
    exact Real.rpow_le_one_of_one_le_of_nonpos hnR (by exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le)
  have hpow : 1/(n : ℝ) ≤ (directScale beta kappa n ^ beta)^2 := by
    rw [← directScale_power_balance beta kappa n hn hd, ← Real.rpow_two,
      ← Real.rpow_mul hh.le]
    apply Real.rpow_le_rpow_of_exponent_ge hh hh1
    unfold effDim
    linarith [hkappa.1]
  exact (Real.sqrt_le_sqrt hpow).trans_eq (Real.sqrt_sq (by positivity))

/-- S8 at any rounded-up direct-regime bandwidth has the direct minimax rate. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qF_direct_certificate_bound
lemma qF_direct_certificate_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ h ∈ Ioc (0 : ℝ) (1 / 4),
      directScale beta kappa n ≤ h → h ≤ 2*directScale beta kappa n →
      ∀ sigma ∈ Icc (0 : ℝ) (1 / 4), sigma ≤ directScale beta kappa n →
      unitAq beta kappa n sigma ⟨qF h, ellF sigma h⟩ ≤
        C * directScale beta kappa n ^ beta := by
  obtain ⟨C, hC, hcert⟩ := qF_certificate_bound beta kappa hbeta hkappa
  let D : ℝ := Real.sqrt ((2 : ℝ) ^ 10 * Real.exp 36)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  refine ⟨C*(2^beta+D+1), by positivity, ?_⟩
  intro n hn h hh hlo hhi sigma hsigma hslo
  let h0 := directScale beta kappa n
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have hh0 : 0 < h0 := by
    dsimp [h0, directScale]
    apply Real.rpow_pos_of_pos
    exact_mod_cast hn
  have hb : h^beta ≤ 2^beta * h0^beta := by
    calc
      _ ≤ (2*h0)^beta := Real.rpow_le_rpow hh.1.le hhi (by linarith [hbeta.1])
      _ = _ := Real.mul_rpow (by norm_num) hh0.le
  have hr : sigma/h0 ≤ 1 := (div_le_one hh0).mpr hslo
  have hr0 : 0 ≤ sigma/h0 := div_nonneg hsigma.1 hh0.le
  have hm : (1+sigma/h0)^10 * Real.exp (36*(sigma/h0)^2) ≤
      (2 : ℝ) ^ 10 * Real.exp 36 := by
    apply mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) 10) _
      (by positivity) (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg (sigma/h0), mul_self_le_mul_self hr0 hr]
  have hs : Real.sqrt (h^(-kappa-1)*(1+sigma/h)^10*
      Real.exp (36*(sigma/h)^2)/n) ≤ D*h0^beta := by
    calc
      _ ≤ Real.sqrt (h0^(-kappa-1)*(1+sigma/h0)^10*
          Real.exp (36*(sigma/h0)^2)/n) :=
        fourier_stochastic_antitone kappa sigma n h0 h hkappa.1 hsigma.1 hh0 hlo
      _ ≤ Real.sqrt ((h0^beta)^2 * ((2 : ℝ) ^ 10 * Real.exp 36)) := by
        apply Real.sqrt_le_sqrt
        calc
          _ = (h0^(-kappa-1)/n)*((1+sigma/h0)^10*
              Real.exp (36*(sigma/h0)^2)) := by ring
          _ ≤ (h0^(-kappa-1)/n)*((2 : ℝ) ^ 10*Real.exp 36) :=
            mul_le_mul_of_nonneg_left hm (by positivity)
          _ = _ := by rw [directScale_variance_balance beta kappa n hn hd]
      _ = D*h0^beta := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
        dsimp [D]
        ring
  have hf := directScale_frequency_bound beta kappa n hn hbeta hkappa
  calc
    _ ≤ C*(h^beta + Real.sqrt (h^(-kappa-1)*(1+sigma/h)^10*
          Real.exp (36*(sigma/h)^2)/n) + Real.sqrt (1/(n : ℝ))) :=
      hcert n hn h hh sigma hsigma
    _ ≤ C*(2^beta*h0^beta + D*h0^beta + h0^beta) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hb hs) hf) hC.le
    _ = _ := by ring

/-- For large samples the direct scale fits the dyadic window, uniformly in the noise scale. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: directScale_dictionary_window
lemma directScale_dictionary_window (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0,
      0 < directScale beta kappa n ∧
      (n : ℝ) ^ (-2 : ℝ) ≤ directScale beta kappa n ∧
      directScale beta kappa n ≤ 1/8 := by
  have hd : 1 ≤ effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have hd0 : 0 < effDim beta kappa := by linarith
  have ht : Tendsto (directScale beta kappa) atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ) ^ (-1/effDim beta kappa)) atTop (𝓝 0)
    simpa only [Function.comp_def, neg_div] using
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hd0)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/8)))
  refine ⟨max N 1, by omega, ?_⟩
  intro n hn
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  refine ⟨Real.rpow_pos_of_pos (by linarith) _, ?_, (hN n (by omega)).le⟩
  unfold directScale
  apply Real.rpow_le_rpow_of_exponent_le hnR
  apply (le_div_iff₀ hd0).mpr
  nlinarith

/-- The first frontier regime has an actual Fourier dictionary witness at the stated rate. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: direct_fourier_dictionary_witness
lemma direct_fourier_dictionary_witness (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1 / 4),
      sigma ≤ directScale beta kappa n →
      ∃ k : ℕ, DictTag.fourier k ∈ weightDictionary n sigma ∧
        unitScore beta kappa n sigma (.fourier k) ≤
          C*frontierRate beta kappa sigma n := by
  obtain ⟨C, hC, hcert⟩ := qF_direct_certificate_bound beta kappa hbeta hkappa
  obtain ⟨n0, hn0, hwindow⟩ := directScale_dictionary_window beta kappa hbeta hkappa
  refine ⟨C, hC, n0, ?_⟩
  intro n hn sigma hsigma hslo
  have hnpos : 0 < n := hn0.trans_le hn
  obtain ⟨hh0, hlo, hhi⟩ := hwindow n hn
  obtain ⟨k, hmem, hklo, hkhi⟩ := fourier_dictionary_round_up n sigma
    (directScale beta kappa n) hnpos hh0 hlo hhi
  refine ⟨k, hmem, ?_⟩
  have hkh : dyadicBandwidth k ∈ Ioc (0 : ℝ) (1 / 4) :=
    ⟨hh0.trans_le hklo, by linarith⟩
  have hscore := hcert n hnpos (dyadicBandwidth k) hkh hklo hkhi.le sigma hsigma hslo
  simpa only [unitScore, pairOf, frontierRate, frontierScale, if_pos hslo] using hscore

/-- In the intermediate regime the effective Fourier sample size is at least one. [Under the stated conditions](hyp:hn,hd,hsigma). [This is the stated conclusion](goal). -/
-- @node: fourier_effective_sample_size_one_le
lemma fourier_effective_sample_size_one_le (beta kappa sigma : ℝ) (n : ℕ)
    (hn : 0 < n) (hd : 0 < effDim beta kappa)
    (hsigma : directScale beta kappa n ≤ sigma) :
    1 ≤ (n : ℝ)*sigma^effDim beta kappa := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 < directScale beta kappa n := Real.rpow_pos_of_pos hnR _
  have hp := Real.rpow_le_rpow h0.le hsigma hd.le
  rw [directScale_power_balance beta kappa n hn hd] at hp
  have hb := (div_le_iff₀ hnR).mp hp
  nlinarith

/-- S9 and the noise elbow place the tuned intermediate bandwidth in the dictionary
window for all sufficiently large samples, uniformly in the noise scale. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: fourierScale_dictionary_window
lemma fourierScale_dictionary_window (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ n0 : ℕ, 0 < n0 ∧ ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      directScale beta kappa n < sigma → sigma ≤ (logScale n)^(-1/2 : ℝ) →
      0 < 12*fourierScale beta kappa sigma n ∧
      (n : ℝ)^(-2 : ℝ) ≤ 12*fourierScale beta kappa sigma n ∧
      12*fourierScale beta kappa sigma n ≤ 1/8 := by
  obtain ⟨C, hC, hbound⟩ := fourierScale_inverse_power_bound beta kappa hbeta hkappa
  obtain ⟨M, hM⟩ := exists_nat_gt C
  have hL : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  have hE : Tendsto (fun n : ℕ => (logScale n)^(-1/2 : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
      hL using 1 <;> norm_num [Function.comp_def]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hE.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/96)))
  refine ⟨max (max M N) 1, by omega, ?_⟩
  intro n hn sigma hsigma hdirect helbow
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hCn : C < (n : ℝ) := hM.trans_le (by exact_mod_cast (show M ≤ n by omega))
  have hd : 1 ≤ effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have hd0 : 0 < effDim beta kappa := by linarith
  have h0 : 0 < directScale beta kappa n := Real.rpow_pos_of_pos hnR _
  have hs0 : 0 < sigma := h0.trans hdirect
  have hF : 0 < fourierScale beta kappa sigma n := fourierScale_pos beta kappa sigma n hs0
  have heff := fourier_effective_sample_size_one_le beta kappa sigma n hn0 hd0 hdirect.le
  have hb := hbound n hn0 sigma hs0 heff
  have hlo : (n : ℝ)^(-2 : ℝ) ≤ fourierScale beta kappa sigma n := by
    by_contra hnot
    have hf : fourierScale beta kappa sigma n ≤ (n : ℝ)^(-2 : ℝ) :=
      (lt_of_not_ge hnot).le
    have hi := Real.rpow_le_rpow_of_nonpos hF hf (neg_nonpos.mpr hd0.le)
    have hx : (n : ℝ)^(2*effDim beta kappa-1) ≤ C := by
      calc
        _ = ((n : ℝ)^(-2 : ℝ))^(-effDim beta kappa)/n := by
          rw [← Real.rpow_mul hnR.le, div_eq_mul_inv,
            ← Real.rpow_neg_one (n : ℝ), ← Real.rpow_add hnR]
          congr 1
          ring
        _ ≤ (fourierScale beta kappa sigma n)^(-effDim beta kappa)/n :=
          div_le_div_of_nonneg_right hi hnR.le
        _ ≤ C := hb
    have hnn : (n : ℝ) ≤ (n : ℝ)^(2*effDim beta kappa-1) := by
      calc
        _ = (n : ℝ)^(1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    linarith
  refine ⟨by positivity, hlo.trans (by linarith), ?_⟩
  have hsupper : sigma ≤ 1/96 := helbow.trans (hN n (by omega)).le
  have hfupper := fourierScale_le_sigma beta kappa sigma n hs0
  linarith

/-- The intermediate regime has a genuine Fourier dictionary witness at the frontier rate. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: intermediate_fourier_dictionary_witness
lemma intermediate_fourier_dictionary_witness (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      directScale beta kappa n < sigma → sigma ≤ (logScale n)^(-1/2 : ℝ) →
      ∃ k : ℕ, DictTag.fourier k ∈ weightDictionary n sigma ∧
        unitScore beta kappa n sigma (.fourier k) ≤ C*frontierRate beta kappa sigma n := by
  obtain ⟨C, hC, hcert⟩ := qF_intermediate_certificate_bound beta kappa hbeta hkappa
  obtain ⟨n0, hn0, hwindow⟩ := fourierScale_dictionary_window beta kappa hbeta hkappa
  refine ⟨C, hC, n0, ?_⟩
  intro n hn sigma hsigma hdirect helbow
  have hnpos : 0 < n := hn0.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have h0 : 0 < directScale beta kappa n := Real.rpow_pos_of_pos hnR _
  have hs0 : 0 < sigma := h0.trans hdirect
  have hd : 0 < effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have heff := fourier_effective_sample_size_one_le beta kappa sigma n hnpos hd hdirect.le
  obtain ⟨hh0, hlo, hhi⟩ := hwindow n hn sigma hsigma hdirect helbow
  obtain ⟨k, hmem, hklo, hkhi⟩ := fourier_dictionary_round_up n sigma
    (12*fourierScale beta kappa sigma n) hnpos hh0 hlo hhi
  refine ⟨k, hmem, ?_⟩
  have hkh : dyadicBandwidth k ∈ Ioc (0 : ℝ) (1/4) :=
    ⟨hh0.trans_le hklo, by linarith⟩
  have hscore := hcert n hnpos sigma ⟨hs0, hsigma.2⟩ heff
    (dyadicBandwidth k) hkh hklo (by linarith)
  simpa only [unitScore, pairOf, frontierRate, frontierScale,
    if_neg (not_le.mpr hdirect), if_pos helbow] using hscore

/-- This branch supplies a dictionary witness with score at most a fixed multiple of the frontier. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: fourier_dictionary_witness
lemma fourier_dictionary_witness (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ, ∀ n ≥ n0, ∀ sigma ∈ Icc (0 : ℝ) (1 / 4),
      sigma ≤ (logScale n)^(-1/2 : ℝ) →
      ∃ k : ℕ,
        DictTag.fourier k ∈ weightDictionary n sigma ∧
        unitScore beta kappa n sigma (.fourier k) ≤
          C*frontierRate beta kappa sigma n := by
  obtain ⟨C0, hC0, n0, hdirect⟩ := direct_fourier_dictionary_witness beta kappa hbeta hkappa
  obtain ⟨C1, hC1, n1, hintermediate⟩ :=
    intermediate_fourier_dictionary_witness beta kappa hbeta hkappa
  refine ⟨max C0 C1, lt_of_lt_of_le hC0 (le_max_left _ _), max n0 n1, ?_⟩
  intro n hn sigma hsigma helbow
  have hrate : 0 ≤ frontierRate beta kappa sigma n := by
    unfold frontierRate frontierScale
    rw [if_pos helbow]
    split_ifs with hslo
    · exact Real.rpow_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) _
    · exact Real.rpow_nonneg (div_nonneg hsigma.1 (Real.sqrt_nonneg _)) _
  by_cases hslo : sigma ≤ directScale beta kappa n
  · obtain ⟨k, hmem, hscore⟩ := hdirect n (le_max_left n0 n1 |>.trans hn) sigma hsigma hslo
    exact ⟨k, hmem, hscore.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hrate)⟩
  · obtain ⟨k, hmem, hscore⟩ := hintermediate n (le_max_right n0 n1 |>.trans hn)
      sigma hsigma (lt_of_not_ge hslo) helbow
    exact ⟨k, hmem, hscore.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate)⟩

end CausalSmith.Stat.NoisydoseWeakdesignTransition
