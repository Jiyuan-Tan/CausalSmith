module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.FixedNoise
public import Causalean.Mathlib.Analysis.RpowArith

/-! Scale comparisons throughout fixed-factor windows about either transition. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
open Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Multiplying a positive localization radius by at most K adds at most d log K
 to the logarithmic denominator. [Under the stated conditions](hyp:K,d,w,a,b,hK,hd,hw,ha,hb,hab). [This is the stated conclusion](goal). -/
-- @node: window_log_power_le
lemma window_log_power_le (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b) (hab : a ≤ K*b) :
    Real.log (Real.exp 1 + w*a^d) ≤
      d * Real.log K + Real.log (Real.exp 1 + w*b^d) := by
  exact Causalean.Mathlib.RpowArith.window_log_power_le K d w a b hK hd hw ha hb hab

/-- Throughout a factor-K window the positive logarithms differ by a bounded factor. [Under the stated conditions](hyp:K,d,w,a,b,hK,hd,hw,ha,hb,hab,hba). [This is the stated conclusion](goal). -/
-- @node: window_log_power_comparison
lemma window_log_power_comparison (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ K*b) (hba : b ≤ K*a) :
    Real.log (Real.exp 1 + w*a^d) ≤
      (1+d*Real.log K) * Real.log (Real.exp 1 + w*b^d) := by
  have _hba := hba
  exact Causalean.Mathlib.RpowArith.window_log_power_comparison K d w a b hK hd hw ha hb hab

/-- Square roots inherit the same (slightly enlarged) logarithmic factor. [Under the stated conditions](hyp:K,d,w,a,b,hK,hd,hw,ha,hb,hab,hba). [This is the stated conclusion](goal). -/
-- @node: window_sqrt_log_comparison
lemma window_sqrt_log_comparison (K d w a b : ℝ) (hK : 1 ≤ K) (hd : 0 ≤ d)
    (hw : 0 ≤ w) (ha : 0 < a) (hb : 0 < b)
    (hab : a ≤ K*b) (hba : b ≤ K*a) :
    Real.sqrt (Real.log (Real.exp 1 + w*a^d)) ≤
      (1+d*Real.log K) * Real.sqrt (Real.log (Real.exp 1 + w*b^d)) := by
  have _hba := hba
  exact Causalean.Mathlib.RpowArith.window_sqrt_log_comparison K d w a b hK hd hw ha hb hab

/-- The Fourier scale varies by a fixed multiplicative factor throughout a radius window. [Under the stated conditions](hyp:hK,hd,hb,hs). [This is the stated conclusion](goal). -/
-- @node: fourierScale_window_comparison
lemma fourierScale_window_comparison (beta kappa K b sigma : ℝ) (n : ℕ)
    (hK : 1 ≤ K) (hd : 0 ≤ effDim beta kappa) (hb : 0 < b)
    (hs : sigma ∈ Icc (b/K) (K*b)) :
    fourierScale beta kappa sigma n ≤
      (K*(1+effDim beta kappa*Real.log K)) * fourierScale beta kappa b n ∧
    fourierScale beta kappa b n ≤
      (K*(1+effDim beta kappa*Real.log K)) * fourierScale beta kappa sigma n := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hspos : 0 < sigma := (div_pos hb hKpos).trans_le hs.1
  have hbs : b ≤ K*sigma := by
    have := (div_le_iff₀ hKpos).mp hs.1
    linarith
  have rootpos (a : ℝ) (ha : 0 < a) :
      0 < Real.sqrt (Real.log (Real.exp 1 + (n:ℝ)*a^effDim beta kappa)) := by
    apply Real.sqrt_pos.mpr
    apply Real.log_pos
    have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    have : 0 ≤ (n:ℝ)*a^effDim beta kappa := by positivity
    linarith
  have hrs := rootpos sigma hspos
  have hrb := rootpos b hb
  have hsb := window_sqrt_log_comparison K (effDim beta kappa) n sigma b
    hK hd (Nat.cast_nonneg n) hspos hb hs.2 hbs
  have hbs' := window_sqrt_log_comparison K (effDim beta kappa) n b sigma
    hK hd (Nat.cast_nonneg n) hb hspos hbs hs.2
  have hc : 0 ≤ 1+effDim beta kappa*Real.log K := by
    have := mul_nonneg hd (Real.log_nonneg hK)
    linarith
  unfold fourierScale
  simp only [← mul_div_assoc]
  constructor
  · apply (div_le_div_iff₀ hrs hrb).mpr
    nlinarith [mul_le_mul_of_nonneg_left hbs' (mul_nonneg hKpos.le hb.le),
      mul_le_mul_of_nonneg_right hs.2 hrb.le]
  · apply (div_le_div_iff₀ hrb hrs).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsb (mul_nonneg hKpos.le hspos.le),
      mul_le_mul_of_nonneg_right hbs hrs.le]

/-- The polynomial scale also varies by a fixed factor in a radius window. [Under the stated conditions](hyp:hK,hb,hn,hs). [This is the stated conclusion](goal). -/
-- @node: polynomialScale_window_comparison
lemma polynomialScale_window_comparison (K b sigma : ℝ) (n : ℕ)
    (hK : 1 ≤ K) (hb : 0 < b) (hn : 1 ≤ n)
    (hs : sigma ∈ Icc (b/K) (K*b)) :
    polynomialScale sigma n ≤ (1+2*Real.log K) * polynomialScale b n ∧
    polynomialScale b n ≤ (1+2*Real.log K) * polynomialScale sigma n := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hspos : 0 < sigma := (div_pos hb hKpos).trans_le hs.1
  have hbs : b ≤ K*sigma := by
    have := (div_le_iff₀ hKpos).mp hs.1
    linarith
  have hL : 0 < logScale n := lt_of_lt_of_le zero_lt_one (logScale_one_le n hn)
  have hsb := window_log_power_comparison K 2 (logScale n) sigma b
    hK (by norm_num) hL.le hspos hb hs.2 hbs
  have hbs' := window_log_power_comparison K 2 (logScale n) b sigma
    hK (by norm_num) hL.le hb hspos hbs hs.2
  simp only [Real.rpow_two, mul_comm (logScale n)] at hsb hbs'
  unfold polynomialScale
  constructor
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith [hsb]) hL.le
  · rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by nlinarith [hbs']) hL.le

/-- At the direct elbow, the effective noisy sample size is exactly one. [Under the stated conditions](hyp:hd,hn). [This is the stated conclusion](goal). -/
-- @node: directScale_effective_sample
lemma directScale_effective_sample (beta kappa : ℝ) (n : ℕ)
    (hd : effDim beta kappa ≠ 0) (hn : 1 ≤ n) :
    (n : ℝ) * directScale beta kappa n ^ effDim beta kappa = 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold directScale
  rw [← Real.rpow_mul hnpos.le]
  have he : (-1 / effDim beta kappa) * effDim beta kappa = -1 := by
    field_simp
  rw [he, Real.rpow_neg_one, mul_inv_cancel₀ hnpos.ne']

/-- The Fourier scale at the direct elbow differs by a fixed public constant. [Under the stated conditions](hyp:hd,hn). [This is the stated conclusion](goal). -/
-- @node: fourierScale_at_directScale
lemma fourierScale_at_directScale (beta kappa : ℝ) (n : ℕ)
    (hd : effDim beta kappa ≠ 0) (hn : 1 ≤ n) :
    fourierScale beta kappa (directScale beta kappa n) n =
      directScale beta kappa n / Real.sqrt (Real.log (Real.exp 1 + 1)) := by
  unfold fourierScale
  rw [directScale_effective_sample beta kappa n hd hn]

/-- A constant dominating the two fixed ratios compares both scales at the first elbow. [Under the stated conditions](hyp:hd,hn,hC,hCinv). [This is the stated conclusion](goal). -/
-- @node: direct_fourier_elbow_comparison
lemma direct_fourier_elbow_comparison (beta kappa C : ℝ) (n : ℕ)
    (hd : effDim beta kappa ≠ 0) (hn : 1 ≤ n)
    (hC : Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C)
    (hCinv : 1 / Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C) :
    directScale beta kappa n ≤ C * fourierScale beta kappa (directScale beta kappa n) n ∧
      fourierScale beta kappa (directScale beta kappa n) n ≤ C * directScale beta kappa n := by
  have hroot : 0 < Real.sqrt (Real.log (Real.exp 1 + 1)) := by
    apply Real.sqrt_pos.mpr
    apply Real.log_pos
    linarith [Real.exp_pos (1 : ℝ)]
  have hb : 0 ≤ directScale beta kappa n := Real.rpow_nonneg (Nat.cast_nonneg n) _
  rw [fourierScale_at_directScale beta kappa n hd hn]
  constructor
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hroot).mpr
    exact (mul_le_mul_of_nonneg_left hC hb).trans_eq (mul_comm _ _)
  · calc
      directScale beta kappa n / Real.sqrt (Real.log (Real.exp 1 + 1)) =
          (1 / Real.sqrt (Real.log (Real.exp 1 + 1))) * directScale beta kappa n := by ring
      _ ≤ C * directScale beta kappa n := mul_le_mul_of_nonneg_right hCinv hb

/-- One constant and sample threshold compare the two scales on both full transition windows. [Under the stated conditions](hyp:hd,hK). [This is the stated conclusion](goal). -/
-- @node: frontier_transition_windows
lemma frontier_transition_windows (beta kappa : ℝ) (hd : 0 < effDim beta kappa)
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ CK : ℝ, 1 ≤ CK ∧ ∃ nK : ℕ, ∀ n ≥ nK,
      0 < directScale beta kappa n / K ∧ K * directScale beta kappa n ≤ 1/4 ∧
      0 < (logScale n)^(-1/2 : ℝ) / K ∧ K * (logScale n)^(-1/2 : ℝ) ≤ 1/4 ∧
      (∀ sigma ∈ Icc (directScale beta kappa n / K) (K * directScale beta kappa n),
        CK⁻¹ * directScale beta kappa n ≤ fourierScale beta kappa sigma n ∧
        fourierScale beta kappa sigma n ≤ CK * directScale beta kappa n) ∧
      (∀ sigma ∈ Icc ((logScale n)^(-1/2 : ℝ) / K) (K * (logScale n)^(-1/2 : ℝ)),
        CK⁻¹ * polynomialScale sigma n ≤ fourierScale beta kappa sigma n ∧
        fourierScale beta kappa sigma n ≤ CK * polynomialScale sigma n) := by
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  let A := K * (1 + effDim beta kappa * Real.log K)
  let B := 1 + 2 * Real.log K
  let E := max (Real.sqrt (Real.log (Real.exp 1 + 1)))
    (1 / Real.sqrt (Real.log (Real.exp 1 + 1)))
  have hA : 0 ≤ A := by
    dsimp [A]
    have := mul_nonneg hd.le (Real.log_nonneg hK)
    positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have := Real.log_nonneg hK
    positivity
  obtain ⟨CE, hCE, nE, hsecond⟩ := secondElbow_comparison beta kappa hd.le
  let CK := max 1 (max (A*E) (A*CE*B))
  have hCK1 : 1 ≤ CK := le_max_left _ _
  have hCK : 0 < CK := zero_lt_one.trans_le hCK1
  have hC1 : A*E ≤ CK := (le_max_left _ _).trans (le_max_right _ _)
  have hC2 : A*CE*B ≤ CK := (le_max_right _ _).trans (le_max_right _ _)
  have hD : Tendsto (fun n : ℕ => directScale beta kappa n) atTop (𝓝 0) := by
    simpa only [directScale, neg_div, Function.comp_def] using
      (tendsto_rpow_neg_atTop (one_div_pos.mpr hd)).comp tendsto_natCast_atTop_atTop
  have hL : Tendsto (fun n : ℕ => (logScale n)^(-1/2 : ℝ)) atTop (𝓝 0) := by
    convert (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
      logScale_tendsto_atTop using 1 <;> norm_num [Function.comp_def]
  have hDK : Tendsto (fun n : ℕ => K * directScale beta kappa n) atTop (𝓝 0) := by
    simpa only [mul_zero] using hD.const_mul K
  have hLK : Tendsto (fun n : ℕ => K * (logScale n)^(-1/2 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL.const_mul K
  obtain ⟨nW, hnW⟩ := eventually_atTop.1
    ((hDK.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))).and
      (hLK.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/4))))
  refine ⟨CK, hCK1, max 1 (max nW nE), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnWE := (le_max_right 1 (max nW nE)).trans hn
  have hnW' := (le_max_left nW nE).trans hnWE
  have hnE := (le_max_right nW nE).trans hnWE
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hDpos : 0 < directScale beta kappa n := Real.rpow_pos_of_pos hnpos _
  have hLpos : 0 < logScale n := zero_lt_one.trans_le (logScale_one_le n hn1)
  have hbpos : 0 < (logScale n)^(-1/2 : ℝ) := Real.rpow_pos_of_pos hLpos _
  obtain ⟨hwD, hwL⟩ := hnW n hnW'
  refine ⟨div_pos hDpos hKpos, hwD.le, div_pos hbpos hKpos, hwL.le, ?_, ?_⟩
  · intro sigma hs
    obtain ⟨hsD, hDs⟩ := fourierScale_window_comparison beta kappa K
      (directScale beta kappa n) sigma n hK hd.le hDpos hs
    change fourierScale beta kappa sigma n ≤ A * _ at hsD
    change fourierScale beta kappa (directScale beta kappa n) n ≤ A * _ at hDs
    obtain ⟨hDF, hFD⟩ := direct_fourier_elbow_comparison beta kappa E n hd.ne' hn1
      (le_max_left _ _) (le_max_right _ _)
    have hspos : 0 < sigma := (div_pos hDpos hKpos).trans_le hs.1
    have hFpos : 0 ≤ fourierScale beta kappa sigma n :=
      div_nonneg hspos.le (Real.sqrt_nonneg _)
    constructor
    · rw [inv_mul_eq_div]
      apply (div_le_iff₀ hCK).mpr
      calc
        directScale beta kappa n ≤ E * fourierScale beta kappa (directScale beta kappa n) n := hDF
        _ ≤ E * (A * fourierScale beta kappa sigma n) :=
          mul_le_mul_of_nonneg_left hDs (by dsimp [E]; positivity)
        _ = (A*E) * fourierScale beta kappa sigma n := by ring
        _ ≤ CK * fourierScale beta kappa sigma n := mul_le_mul_of_nonneg_right hC1 hFpos
        _ = _ := mul_comm _ _
    · calc
        fourierScale beta kappa sigma n ≤ A * fourierScale beta kappa (directScale beta kappa n) n := hsD
        _ ≤ A * (E * directScale beta kappa n) := mul_le_mul_of_nonneg_left hFD hA
        _ = (A*E) * directScale beta kappa n := by ring
        _ ≤ CK * directScale beta kappa n := mul_le_mul_of_nonneg_right hC1 hDpos.le
  · intro sigma hs
    obtain ⟨hsF, hFs⟩ := fourierScale_window_comparison beta kappa K
      ((logScale n)^(-1/2 : ℝ)) sigma n hK hd.le hbpos hs
    obtain ⟨hsP, hPs⟩ := polynomialScale_window_comparison K
      ((logScale n)^(-1/2 : ℝ)) sigma n hK hbpos hn1 hs
    change fourierScale beta kappa sigma n ≤ A * _ at hsF
    change fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤ A * _ at hFs
    change polynomialScale sigma n ≤ B * _ at hsP
    change polynomialScale ((logScale n)^(-1/2 : ℝ)) n ≤ B * _ at hPs
    obtain ⟨hFP, hPF⟩ := hsecond n hnE
    have hspos : 0 < sigma := (div_pos hbpos hKpos).trans_le hs.1
    have hFpos : 0 ≤ fourierScale beta kappa sigma n :=
      div_nonneg hspos.le (Real.sqrt_nonneg _)
    have hPpos : 0 ≤ polynomialScale sigma n := by
      apply div_nonneg _ hLpos.le
      apply Real.log_nonneg
      have := Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)
      have : 0 ≤ sigma^2 * logScale n := by positivity
      linarith
    constructor
    · rw [inv_mul_eq_div]
      apply (div_le_iff₀ hCK).mpr
      calc
        polynomialScale sigma n ≤ B * polynomialScale ((logScale n)^(-1/2 : ℝ)) n := hsP
        _ ≤ B * (CE * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n) :=
          mul_le_mul_of_nonneg_left hPF hB
        _ ≤ B * (CE * (A * fourierScale beta kappa sigma n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hFs hCE.le) hB
        _ = (A*CE*B) * fourierScale beta kappa sigma n := by ring
        _ ≤ CK * fourierScale beta kappa sigma n := mul_le_mul_of_nonneg_right hC2 hFpos
        _ = _ := mul_comm _ _
    · calc
        fourierScale beta kappa sigma n ≤ A * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n := hsF
        _ ≤ A * (CE * polynomialScale ((logScale n)^(-1/2 : ℝ)) n) :=
          mul_le_mul_of_nonneg_left hFP hA
        _ ≤ A * (CE * (B * polynomialScale sigma n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPs hCE.le) hA
        _ = (A*CE*B) * polynomialScale sigma n := by ring
        _ ≤ CK * polynomialScale sigma n := mul_le_mul_of_nonneg_right hC2 hPpos

end CausalSmith.Stat.NoisydoseWeakdesignTransition
