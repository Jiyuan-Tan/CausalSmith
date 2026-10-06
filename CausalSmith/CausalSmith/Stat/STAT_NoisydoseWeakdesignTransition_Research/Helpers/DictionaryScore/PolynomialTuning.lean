module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialEnvelope
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.DictionaryScore.PolynomialLocalization
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.FrontierElbows
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Compact-support dictionary tuning: the odd dyadic degree window (S14) and
quantitative control of the exponential inverse-heat variance factor (S15). -/
public section
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Rounding down a target degree at least four gives an available odd degree
between one quarter and the target. [Under the stated conditions](hyp:hM). [This is the stated conclusion](goal). -/
-- @node: polynomial_degree_round_down
lemma polynomial_degree_round_down (M : ℝ) (hM : 4 ≤ M) :
    ∃ j : ℕ, Odd (2^j+1) ∧ M/4 ≤ (2^j+1 : ℕ) ∧ (2^j+1 : ℕ) ≤ M := by
  obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near (show (1 : ℝ) ≤ M/2 by linarith)
    (by norm_num : (1 : ℝ) < 2)
  have hj : j ≠ 0 := by
    intro hj
    subst j
    norm_num at hhi
    linarith
  have heven : Even (2^j : ℕ) := (by decide : Even (2 : ℕ)).pow_of_ne_zero hj
  refine ⟨j, heven.add_odd (by decide), ?_, ?_⟩
  · push_cast
    rw [pow_succ] at hhi
    linarith
  · push_cast
    linarith

/-- The degree cutoff implies the finite polynomial index cutoff in the public dictionary. [Under the stated conditions](hyp:hdegree,hodd). [This is the stated conclusion](goal). -/
-- @node: polynomial_mem_weightDictionary_of_degree
lemma polynomial_mem_weightDictionary_of_degree (n j : ℕ) (sigma : ℝ)
    (hodd : Odd (2^j+1)) (hdegree : 2^j+1 ≤ n^2) :
    DictTag.poly j ∈ weightDictionary n sigma := by
  have hj : j < n^2+1 := by
    have hpow : ∀ k : ℕ, k ≤ 2^k := by
      intro k
      induction k with
      | zero => norm_num
      | succ j ih =>
        rw [pow_succ]
        have hp : 1 ≤ 2^j := Nat.one_le_pow j 2 (by omega)
        omega
    have := hpow j
    omega
  simp only [weightDictionary, List.mem_toFinset, dictionaryList, List.mem_append,
    List.mem_singleton, List.mem_map, List.mem_filter, List.mem_range]
  exact Or.inr ⟨j, ⟨hj, by simpa using And.intro hodd hdegree⟩, rfl⟩

/-- S14 rounding gives a dictionary element whenever the target is in the degree window. [Under the stated conditions](hyp:hM,hMn). [This is the stated conclusion](goal). -/
-- @node: polynomial_dictionary_round_down
lemma polynomial_dictionary_round_down (n : ℕ) (sigma M : ℝ)
    (hM : 4 ≤ M) (hMn : M ≤ (n : ℝ)^2) :
    ∃ j : ℕ, DictTag.poly j ∈ weightDictionary n sigma ∧ Odd (2^j+1) ∧
      M/4 ≤ (2^j+1 : ℕ) ∧ (2^j+1 : ℕ) ≤ M := by
  obtain ⟨j, hjodd, hjlo, hjhi⟩ := polynomial_degree_round_down M hM
  have hjn : 2^j+1 ≤ n^2 := by exact_mod_cast hjhi.trans hMn
  exact ⟨j, polynomial_mem_weightDictionary_of_degree n j sigma hjodd hjn,
    hjodd, hjlo, hjhi⟩

/-- The compact-support logarithmic denominator is at least one, uniformly in noise. [Under the stated conditions](hyp:hL). [This is the stated conclusion](goal). -/
-- @node: polynomial_log_denominator_one_le
lemma polynomial_log_denominator_one_le (L sigma : ℝ) (hL : 0 ≤ L) :
    1 ≤ Real.log (Real.exp 1 + sigma^2*L) := by
  simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1)
    (show Real.exp 1 ≤ Real.exp 1+sigma^2*L by
      exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg sigma) hL))

/-- A degree below L/(4096 B) makes the logarithm of the S13 square-root
variance factor at most L/16; the constants are public and independent of noise. [Under the stated conditions](hyp:hL,hm,hdegree). [This is the stated conclusion](goal). -/
-- @node: polynomial_inverseheat_log_bound
lemma polynomial_inverseheat_log_bound (L sigma : ℝ) (hL : 0 < L)
    (m : ℕ) (hm : 0 < m)
    (hdegree : (m : ℝ) ≤ L / (4096 * Real.log (Real.exp 1+sigma^2*L))) :
    (6*(m-1 : ℕ) : ℕ) * Real.log 15 +
      ((6*(m-1 : ℕ) : ℕ) : ℝ)/2 *
        Real.log (1+(6*(m-1 : ℕ) : ℕ)*sigma^2) ≤ L/16 := by
  let B := Real.log (Real.exp 1+sigma^2*L)
  let D := 6*(m-1 : ℕ)
  have hB : 1 ≤ B := polynomial_log_denominator_one_le L sigma hL.le
  have hBpos : 0 < B := by linarith
  have hD : (D : ℝ) ≤ 6*L/(4096*B) := by
    have hmle : ((m-1 : ℕ) : ℝ) ≤ m := by exact_mod_cast Nat.sub_le m 1
    dsimp [D]
    push_cast
    calc
      _ ≤ 6*(m : ℝ) := by gcongr
      _ ≤ 6*(L/(4096*B)) := mul_le_mul_of_nonneg_left hdegree (by norm_num)
      _ = _ := by ring
  have hDs : (D : ℝ)*sigma^2 ≤ 6*(sigma^2*L) := by
    have hDL : (D : ℝ) ≤ 6*L := hD.trans
      (div_le_self (by positivity) (by linarith : (1 : ℝ) ≤ 4096*B))
    nlinarith [sq_nonneg sigma]
  have harg : 1+(D : ℝ)*sigma^2 ≤ 6*(Real.exp 1+sigma^2*L) := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith
  have hlog : Real.log (1+(D : ℝ)*sigma^2) ≤ B+Real.log 6 := by
    calc
      _ ≤ Real.log (6*(Real.exp 1+sigma^2*L)) :=
        Real.log_le_log (by positivity) harg
      _ = B+Real.log 6 := by rw [Real.log_mul (by norm_num) (by positivity)]; ring
  have h15 : Real.log 15 ≤ 15 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have h6 : Real.log 6 ≤ 6 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hlog6 : Real.log (1+(D : ℝ)*sigma^2) ≤ B+6 := hlog.trans (by linarith)
  have hfirst : (D : ℝ)*Real.log 15 + (D : ℝ)/2*Real.log (1+(D : ℝ)*sigma^2) ≤
      (D : ℝ)*(15+(B+6)/2) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr h15),
      mul_nonneg (Nat.cast_nonneg D) (sub_nonneg.mpr hlog6)]
  calc
    _ ≤ (D : ℝ)*(15+(B+6)/2) := hfirst
    _ ≤ (6*L/(4096*B))*(15+(B+6)/2) :=
      mul_le_mul_of_nonneg_right hD (by linarith)
    _ ≤ L/16 := by
      -- Clear the positive logarithmic denominator in this numerical inequality.
      have heq : (6*L/(4096*B))*(15+(B+6)/2) =
          (6*L*(15+(B+6)/2))/(4096*B) := by ring
      rw [heq]
      apply (div_le_iff₀ (show 0 < 4096*B by positivity)).mpr
      nlinarith [mul_nonneg hL.le (sub_nonneg.mpr hB)]

/-- Exponentiating S15 gives the squared variance multiplier bound directly. [Under the stated conditions](hyp:hL,hm,hdegree). [This is the stated conclusion](goal). -/
-- @node: polynomial_inverseheat_multiplier_bound
lemma polynomial_inverseheat_multiplier_bound (L sigma : ℝ) (hL : 0 < L)
    (m : ℕ) (hm : 0 < m)
    (hdegree : (m : ℝ) ≤ L / (4096 * Real.log (Real.exp 1+sigma^2*L))) :
    (15 : ℝ)^(2*(6*(m-1))) * (1+(6*(m-1) : ℕ)*sigma^2)^(6*(m-1)) ≤
      Real.exp (L/8) := by
  have h := polynomial_inverseheat_log_bound L sigma hL m hm hdegree
  have hbase : 0 < 1+(6*(m-1) : ℕ)*sigma^2 := by positivity
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 15), ← Real.exp_nat_mul,
    ← Real.exp_log hbase, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast at h ⊢
  linarith

/-- The target degree L/(4096 B) eventually lies between four and n squared,
uniformly over the full public noise range (S14). [This is the stated conclusion](goal). -/
-- @node: polynomial_target_degree_window
lemma polynomial_target_degree_window :
    ∀ᶠ n : ℕ in atTop, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      4 ≤ logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n)) ∧
      logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n)) ≤ (n : ℝ)^2 := by
  have hLtop : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  have hshift : Tendsto (fun n : ℕ => Real.exp 1+logScale n) atTop atTop :=
    tendsto_const_nhds.add_atTop hLtop
  have hsmall := hshift.eventually (Real.isLittleO_log_id_atTop.def
    (by norm_num : (0 : ℝ) < 1/32768))
  filter_upwards [hsmall, hLtop.eventually_ge_atTop (Real.exp 1),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (Real.exp 1)]
    with n hnsmall hLn hnexp
  intro sigma hsigma
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hnpos : (0 : ℝ) < n := by linarith
  have hLpos : 0 < logScale n := by linarith
  let B := Real.log (Real.exp 1+sigma^2*logScale n)
  have hB : 1 ≤ B := polynomial_log_denominator_one_le _ _ hLpos.le
  have hBpos : 0 < B := by linarith
  have hsig : sigma^2 ≤ 1 := by nlinarith [hsigma.1, hsigma.2]
  have hBlog : B ≤ Real.log (Real.exp 1+logScale n) :=
    Real.log_le_log (by positivity)
      (add_le_add le_rfl (mul_le_of_le_one_left hLpos.le hsig))
  have hsmall' : Real.log (Real.exp 1+logScale n) ≤ logScale n/16384 := by
    simp only [id_eq, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ Real.exp 1+logScale n)] at hnsmall
    have := le_abs_self (Real.log (Real.exp 1+logScale n))
    linarith
  have hLbound : logScale n ≤ (n : ℝ)^2 := by
    have hlog := Real.log_le_sub_one_of_pos
      (mul_pos (Real.exp_pos 1) hnpos)
    have hmul := mul_le_mul_of_nonneg_right hnexp hnpos.le
    dsimp [logScale]
    nlinarith
  constructor
  · apply (le_div_iff₀ (show 0 < 4096*B by positivity)).mpr
    linarith [hBlog.trans hsmall']
  · exact (div_le_self hLpos.le (by linarith : (1 : ℝ) ≤ 4096*B)).trans hLbound

/-- S14 provides an actual odd polynomial dictionary element in the public tuning window. [This is the stated conclusion](goal). -/
-- @node: polynomial_tuned_dictionary_degree
lemma polynomial_tuned_dictionary_degree :
    ∀ᶠ n : ℕ in atTop, ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      ∃ j : ℕ, DictTag.poly j ∈ weightDictionary n sigma ∧ Odd (2^j+1) ∧
        logScale n / (16384*Real.log (Real.exp 1+sigma^2*logScale n)) ≤ (2^j+1 : ℕ) ∧
        (2^j+1 : ℕ) ≤ logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n)) := by
  filter_upwards [polynomial_target_degree_window] with n hn
  intro sigma hsigma
  obtain ⟨j, hjmem, hjodd, hjlo, hjhi⟩ := polynomial_dictionary_round_down n sigma
    _ (hn sigma hsigma).1 (hn sigma hsigma).2
  exact ⟨j, hjmem, hjodd, by convert hjlo using 1 <;> ring, hjhi⟩

/-- At logarithmic sample sizes at least two, the squared S15 multiplier is at most n^(1/4). [Under the stated conditions](hyp:hn,hL,hm,hdegree). [This is the stated conclusion](goal). -/
-- @node: polynomial_inverseheat_multiplier_sample_bound
lemma polynomial_inverseheat_multiplier_sample_bound (n m : ℕ) (sigma : ℝ)
    (hn : 0 < n) (hL : 2 ≤ logScale n) (hm : 0 < m)
    (hdegree : (m : ℝ) ≤ logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n))) :
    (15 : ℝ)^(2*(6*(m-1))) * (1+(6*(m-1) : ℕ)*sigma^2)^(6*(m-1)) ≤
      (n : ℝ)^(1/4 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hLn : logScale n = 1+Real.log n := by
    rw [logScale, Real.log_mul (Real.exp_ne_zero _) hnR.ne', Real.log_exp]
  apply (polynomial_inverseheat_multiplier_bound (logScale n) sigma (by linarith)
    m hm hdegree).trans
  rw [Real.rpow_def_of_pos hnR]
  apply Real.exp_le_exp.mpr
  rw [hLn] at hL ⊢
  linarith

/-- S13 and S15 give a finite public variance bounded by 16 n^(1/4),
with no analytic premise on the chosen degree. [Under the stated conditions](hyp:hkappa,hn,hL,hm,hdegree). [This is the stated conclusion](goal). -/
-- @node: ellM_Vq_tuned_sample_bound
lemma ellM_Vq_tuned_sample_bound (kappa sigma : ℝ) (hkappa : 0 ≤ kappa)
    (n m : ℕ) (hn : 0 < n) (hL : 2 ≤ logScale n) (hm : 0 < m)
    (hdegree : (m : ℝ) ≤ logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n))) :
    Vq kappa sigma (ellM sigma m) ≤ 16*(n : ℝ)^(1/4 : ℝ) := by
  apply (ellM_Vq_explicit_bound kappa sigma hkappa m hm).trans
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (polynomial_inverseheat_multiplier_sample_bound n m sigma hn hL hm hdegree) (by norm_num)

/-- The tuned Gaussian standard deviation is at most 4 n^(-3/8). [Under the stated conditions](hyp:hkappa,hn,hL,hm,hdegree). [This is the stated conclusion](goal). -/
-- @node: ellM_tuned_standard_deviation_bound
lemma ellM_tuned_standard_deviation_bound (kappa sigma : ℝ) (hkappa : 0 ≤ kappa)
    (n m : ℕ) (hn : 0 < n) (hL : 2 ≤ logScale n) (hm : 0 < m)
    (hdegree : (m : ℝ) ≤ logScale n / (4096*Real.log (Real.exp 1+sigma^2*logScale n))) :
    Real.sqrt (Vq kappa sigma (ellM sigma m)/n) ≤ 4*(n : ℝ)^(-3/8 : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (Real.sqrt_le_left (by positivity)).mpr
  calc
    _ ≤ 16*(n : ℝ)^(1/4 : ℝ)/n := div_le_div_of_nonneg_right
      (ellM_Vq_tuned_sample_bound kappa sigma hkappa n m hn hL hm hdegree) hnR.le
    _ = (4*(n : ℝ)^(-3/8 : ℝ))^2 := by
      rw [mul_pow, ← Real.rpow_two ((n : ℝ)^(-3/8 : ℝ)), ← Real.rpow_mul hnR.le]
      norm_num only [show (-3/8 : ℝ)*2 = -3/4 by norm_num, show (4 : ℝ)^2 = 16 by norm_num]
      rw [show (1/4 : ℝ) = 1+(-3/4) by norm_num, Real.rpow_add hnR, Real.rpow_one]
      field_simp

/-- Fixed logarithmic powers are eventually dominated by n^(3/8).
This is the uniform stochastic-to-bias comparison in S16. [This is the stated conclusion](goal). -/
-- @node: polynomial_logScale_power_absorption
lemma polynomial_logScale_power_absorption :
    ∀ᶠ n : ℕ in atTop, (logScale n)^4 ≤ (n : ℝ)^(3/8 : ℝ) := by
  let a : ℝ := (Real.exp 1)^(3/8 : ℝ)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsmall := (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1)).eventually
    ((isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 3/8)).def
      (inv_pos.mpr ha))
  filter_upwards [hsmall, eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hL : 0 ≤ logScale n := (logScale_one_le n hn1).trans' (by norm_num)
  have he : 0 < Real.exp 1*(n : ℝ) := mul_pos (Real.exp_pos 1) hnR
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hn
  rw [Real.mul_rpow (Real.exp_pos 1).le hnR.le] at hn
  rw [Real.rpow_ofNat] at hn
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hn
  have hn' : (logScale n)^4 ≤ a⁻¹*(a*(n : ℝ)^(3/8 : ℝ)) := hn
  simpa only [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] using hn'

/-- The S11 denominator lower bound controls the public ratio multiplier. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hkappa). -/
-- @node: qM_ratio_multiplier_bound
lemma qM_ratio_multiplier_bound (kappa : ℝ) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, Odd m → 0 < m →
      12 / unitbq kappa (qM m) ≤ C*(m : ℝ)^(kappa+1) := by
  obtain ⟨c, K, hc, hK, hden⟩ := qM_weightMoment_bounds kappa
    ⟨hkappa.1, by linarith [hkappa.2]⟩
  refine ⟨192/c, by positivity, ?_⟩
  intro m hm hmpos
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hl := (hden m hm hmpos).1
  have hp : 0 < ((m : ℝ)⁻¹)^(kappa+1) := by positivity
  calc
    _ = 192/weightMoment kappa (qM m) := by unfold unitbq; ring
    _ ≤ 192/(c*((m : ℝ)⁻¹)^(kappa+1)) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hc hp) hl
    _ = (192/c)*(m : ℝ)^(kappa+1) := by
      rw [Real.inv_rpow hmR.le]
      field_simp

/-- If the logarithmic degree is legal and the uniform logarithmic power is absorbed,
the stochastic rate n^(-3/8) m^(kappa+1) is at most the localization bias. [Under the stated conditions](hyp:hn,hm,hbeta,hkappa,hmL,habsorb). [This is the stated conclusion](goal). -/
-- @node: polynomial_stochastic_le_bias
lemma polynomial_stochastic_le_bias (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (n m : ℕ) (hn : 1 ≤ n) (hm : 0 < m) (hmL : (m : ℝ) ≤ logScale n)
    (habsorb : (logScale n)^4 ≤ (n : ℝ)^(3/8 : ℝ)) :
    (n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(kappa+1) ≤ ((m : ℝ)⁻¹)^beta := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by linarith
  have hexp : kappa+beta+1 ≤ 4 := by linarith [hbeta.2, hkappa.2]
  have hpow : (m : ℝ)^(kappa+beta+1) ≤ (n : ℝ)^(3/8 : ℝ) := by
    calc
      _ ≤ (m : ℝ)^(4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 hexp
      _ = (m : ℝ)^4 := Real.rpow_natCast _ _
      _ ≤ (logScale n)^4 := pow_le_pow_left₀ hmR.le hmL 4
      _ ≤ _ := habsorb
  have hb : (n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(kappa+beta+1) ≤ 1 := by
    calc
      _ ≤ (n : ℝ)^(-3/8 : ℝ)*(n : ℝ)^(3/8 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 1 := by rw [← Real.rpow_add hnR]; norm_num
  have hident : (n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(kappa+1) =
      ((m : ℝ)⁻¹)^beta*((n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(kappa+beta+1)) := by
    rw [Real.inv_rpow hmR.le, ← Real.rpow_neg hmR.le]
    calc
      _ = (n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(-beta+(kappa+beta+1)) := by congr 2; ring
      _ = _ := by rw [Real.rpow_add hmR]; ring
  rw [hident]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ ((m : ℝ)⁻¹)^beta)

/-- The rounded polynomial certificate has the inverse-degree bias rate (S16). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: qM_tuned_certificate_bound
lemma qM_tuned_certificate_bound (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ sigma : ℝ, ∀ m : ℕ,
      Odd m → 0 < m →
      (m : ℝ) ≤ logScale n/(4096*Real.log (Real.exp 1+sigma^2*logScale n)) →
      unitAq beta kappa n sigma ⟨qM m, ellM sigma m⟩ ≤ C*((m : ℝ)⁻¹)^beta := by
  obtain ⟨Cb, hCb, hb⟩ := qM_bias_bound beta kappa hbeta hkappa
  obtain ⟨Cr, hCr, hr⟩ := qM_ratio_multiplier_bound kappa hkappa
  refine ⟨Cb+4*Cr+2*Real.sqrt 3, by positivity, ?_⟩
  have hLtop : Tendsto (fun n : ℕ => logScale n) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (Real.exp_pos 1))
  filter_upwards [polynomial_logScale_power_absorption,
    hLtop.eventually_ge_atTop 2, eventually_ge_atTop 1] with n habsorb hL hn
  intro sigma m hm hmpos hmdegree
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : 0 < n := by omega
  have hnR0 : (0 : ℝ) < n := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hB := polynomial_log_denominator_one_le (logScale n) sigma (by linarith)
  have hmL : (m : ℝ) ≤ logScale n := hmdegree.trans
    (div_le_self (by linarith) (by linarith))
  have hstoch := polynomial_stochastic_le_bias beta kappa hbeta hkappa n m hn hmpos hmL habsorb
  have hrnonneg : 0 ≤ 12/unitbq kappa (qM m) := by
    exact div_nonneg (by norm_num) (div_nonneg
      (qM_weightMoment_pos kappa hkappa.1 m hm hmpos).le (by norm_num))
  have hnoise : 12/unitbq kappa (qM m)*Real.sqrt (Vq kappa sigma (ellM sigma m)/n) ≤
      4*Cr*((m : ℝ)⁻¹)^beta := by
    calc
      _ ≤ (Cr*(m : ℝ)^(kappa+1))*(4*(n : ℝ)^(-3/8 : ℝ)) :=
        mul_le_mul (hr m hm hmpos)
          (ellM_tuned_standard_deviation_bound kappa sigma hkappa.1 n m hn0 hL hmpos hmdegree)
          (Real.sqrt_nonneg _) (by positivity)
      _ = 4*Cr*((n : ℝ)^(-3/8 : ℝ)*(m : ℝ)^(kappa+1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hstoch (by positivity)
  have hfreq : Real.sqrt (3/(n : ℝ)) ≤ Real.sqrt 3*((m : ℝ)⁻¹)^beta := by
    have hfreqpow : (n : ℝ)^(-1/2 : ℝ) ≤ (n : ℝ)^(-3/8 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hnR (by norm_num)
    have hmone : 1 ≤ (m : ℝ)^(kappa+1) :=
      Real.one_le_rpow (by exact_mod_cast hmpos) (by linarith [hkappa.1])
    have hsmall : (n : ℝ)^(-1/2 : ℝ) ≤ ((m : ℝ)⁻¹)^beta :=
      (hfreqpow.trans (le_mul_of_one_le_right (by positivity) hmone)).trans hstoch
    have hsqrt : Real.sqrt (3/(n : ℝ)) = Real.sqrt 3*(n : ℝ)^(-1/2 : ℝ) := by
      rw [div_eq_mul_inv, Real.sqrt_mul (by norm_num), ← Real.rpow_neg_one,
        Real.sqrt_eq_rpow ((n : ℝ)^(-1 : ℝ)), ← Real.rpow_mul hnR0.le]
      norm_num
    rw [hsqrt]
    exact mul_le_mul_of_nonneg_left hsmall (Real.sqrt_nonneg _)
  unfold unitAq
  dsimp only
  calc
    _ ≤ Cb*((m : ℝ)⁻¹)^beta+4*Cr*((m : ℝ)⁻¹)^beta+
        2*(Real.sqrt 3*((m : ℝ)⁻¹)^beta) := by
      gcongr
      · exact hb m hm hmpos
    _ = _ := by ring

/-- The direct cutoff is eventually below the logarithmic cutoff, so high-noise
polynomial tuning selects the third branch of the public frontier. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: directScale_eventually_below_log_cutoff
lemma directScale_eventually_below_log_cutoff (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∀ᶠ n : ℕ in atTop, directScale beta kappa n ≤ (logScale n)^(-1/2 : ℝ) := by
  filter_upwards [polynomial_logScale_power_absorption, eventually_ge_atTop 1]
    with n habsorb hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL1 := logScale_one_le n hn
  have hL0 : 0 < logScale n := by linarith
  have hd0 : 0 < effDim beta kappa := by unfold effDim; linarith [hbeta.1, hkappa.1]
  have hd5 : effDim beta kappa ≤ 5 := by unfold effDim; linarith [hbeta.2, hkappa.2]
  have hLpower : (logScale n)^(effDim beta kappa/2) ≤ (n : ℝ) := by
    calc
      _ ≤ (logScale n)^(4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      _ = (logScale n)^4 := Real.rpow_ofNat _ _
      _ ≤ (n : ℝ)^(3/8 : ℝ) := habsorb
      _ ≤ (n : ℝ) := by
        convert Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (3/8 : ℝ) ≤ 1) using 1
        rw [Real.rpow_one]
  have hinv := Real.rpow_le_rpow_of_nonpos (by positivity :
    0 < (logScale n)^(effDim beta kappa/2)) hLpower
    (show -1/effDim beta kappa ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hd0.le)
  simpa only [directScale, ← Real.rpow_mul hL0.le,
    show (effDim beta kappa/2)*(-1/effDim beta kappa) = -1/2 by field_simp] using hinv

end CausalSmith.Stat.NoisydoseWeakdesignTransition
