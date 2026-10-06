module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LowerTuning

/-! Compact-support degree, bandwidth and cancellation estimates (38)--(45). -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
noncomputable section
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- The compact logarithm satisfies both deterministic comparisons in (38). [Under the stated conditions](hyp:ht). [This is the stated conclusion](goal). -/
-- @node: lower_compact_log_bounds
lemma lower_compact_log_bounds (tau : ℝ) (ht : 1 ≤ tau) :
    Real.log (Real.exp 1+tau) ≤ 2*Real.sqrt tau ∧
      Real.log (Real.exp 1+tau) ≤ Real.log tau+Real.log (Real.exp 1+1) := by
  have ht0 : 0 < tau := by linarith
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hproduct : Real.exp 1+tau ≤ (Real.exp 1+1)*tau := by nlinarith
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp 1+tau) hproduct
  rw [Real.log_mul (by positivity) ht0.ne'] at hlog
  have he2 : 2 < Real.exp 1 := by
    have := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hbase : Real.log (Real.exp 1+1) ≤ 2 := by
    have hexp : Real.exp 1+1 ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1+1 by norm_num, Real.exp_add]
      nlinarith
    have := Real.log_le_log (by positivity : 0 < Real.exp 1+1) hexp
    simpa using this
  have hs := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ht0)
  rw [Real.log_sqrt ht0.le] at hs
  exact ⟨by linarith, by linarith⟩

/-- The ceiling in (37) preserves the two-sided degree estimate (40). [Under the stated conditions](hyp:hCM,hB,hsize). [This is the stated conclusion](goal). -/
-- @node: lower_compact_degree_bounds
lemma lower_compact_degree_bounds (CM L B : ℝ) (hCM : 1 ≤ CM)
    (hB : 0 < B) (hsize : 1 ≤ L/B) :
    CM*L/B ≤ (Nat.ceil (CM*L/B) : ℝ) ∧
      (Nat.ceil (CM*L/B) : ℝ) ≤ 2*CM*L/B ∧
      1 ≤ Nat.ceil (CM*L/B) := by
  have hx : 1 ≤ CM*L/B := by
    rw [mul_div_assoc]
    exact one_le_mul_of_one_le_of_one_le hCM hsize
  have hlo := Nat.le_ceil (CM*L/B)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ CM*L/B by linarith)
  refine ⟨hlo, ?_, ?_⟩
  · calc
      _ ≤ CM*L/B+1 := hhi.le
      _ ≤ 2*CM*L/B := by
        rw [show 2*CM*L/B = 2*(CM*L/B) by ring]
        linarith
  · exact_mod_cast (hx.trans hlo)

/-- The rounded compact degree retains the fraction of the frontier in (47). [Under the stated conditions](hyp:hell,hCM,hB,hsize). [This is the stated conclusion](goal). -/
-- @node: lower_compact_bandwidth_comparison
lemma lower_compact_bandwidth_comparison (ell CM L B : ℝ)
    (hell : 0 ≤ ell) (hCM : 1 ≤ CM) (hB : 0 < B) (hsize : 1 ≤ L/B) :
    (ell/(2*CM))*(B/L) ≤ ell/(Nat.ceil (CM*L/B) : ℝ) := by
  obtain ⟨hlo, hhi, hm⟩ := lower_compact_degree_bounds CM L B hCM hB hsize
  have hL : 0 < L := by
    have : 0 < L/B := by linarith
    have := (lt_div_iff₀ hB).mp this
    simpa using this
  have hmR : (0 : ℝ) < Nat.ceil (CM*L/B) := by
    exact_mod_cast (show 0 < Nat.ceil (CM*L/B) by omega)
  calc
    _ = ell/(2*CM*L/B) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left hell hmR hhi

/-- Equation (44) follows from (38) and the explicit ratio lower bound (43). [Under the stated conditions](hyp:ht,hD,hR). [This is the stated conclusion](goal). -/
-- @node: lower_compact_log_ratio
lemma lower_compact_log_ratio (tau D R : ℝ) (ht : 1 ≤ tau)
    (hD : 2*Real.exp 1 ≤ D)
    (hR : D*tau/Real.log (Real.exp 1+tau) ≤ R) :
    Real.log (Real.exp 1+tau)/2 ≤ Real.log R := by
  have ht0 : 0 < tau := by linarith
  have hB : 0 < Real.log (Real.exp 1+tau) :=
    Real.log_pos (by linarith [Real.exp_pos 1])
  obtain ⟨hroot, hlog⟩ := lower_compact_log_bounds tau ht
  have hs0 := Real.sqrt_pos.2 ht0
  have hs2 := Real.sq_sqrt ht0.le
  have he := Real.exp_pos 1
  have hratio : Real.exp 1*Real.sqrt tau ≤ D*tau/Real.log (Real.exp 1+tau) := by
    apply (le_div_iff₀ hB).2
    have hmul := mul_le_mul_of_nonneg_left hroot (show 0 ≤ Real.exp 1*Real.sqrt tau by positivity)
    have hd := mul_le_mul_of_nonneg_right hD ht0.le
    nlinarith
  have hR0 : 0 < R := (mul_pos he hs0).trans_le (hratio.trans hR)
  have hmono := Real.log_le_log (mul_pos he hs0) (hratio.trans hR)
  rw [Real.log_mul he.ne' hs0.ne', Real.log_exp, Real.log_sqrt ht0.le] at hmono
  have hbase : Real.log (Real.exp 1+1) ≤ 2 := by
    simpa using (lower_compact_log_bounds 1 le_rfl).1
  linarith

/-- Equations (40)--(45) force the compact cancellation exponent to exceed four log-scales. [Under the stated conditions](hyp:hell,hg,hCM,hL,ht,hCMlarge,hsize,hm,hJ,hD). [This is the stated conclusion](goal). -/
-- @node: lower_compact_cancellation_decay
lemma lower_compact_cancellation_decay (ell gamma CM L tau : ℝ) (m J : ℕ)
    (hell : 0 < ell) (hg : 0 < gamma) (hCM : 1 ≤ CM) (hL : 0 < L)
    (ht : 1 ≤ tau)
    (hsize : 1 ≤ L/Real.log (Real.exp 1+tau))
    (hm : m = Nat.ceil (CM*L/Real.log (Real.exp 1+tau)))
    (hJ : gamma*m ≤ (J : ℝ))
    (hD : 2*Real.exp 1 ≤ gamma*CM/(Real.exp 1*ell^2))
    (hCMlarge : 8 ≤ gamma*CM) :
    4*L ≤ (J : ℝ)*Real.log ((J : ℝ)/(Real.exp 1*(ell^2*L/tau))) := by
  let B := Real.log (Real.exp 1+tau)
  have hB : 0 < B := Real.log_pos (by linarith [Real.exp_pos 1])
  have ht0 : 0 < tau := by linarith
  have hmlo : CM*L/B ≤ (m : ℝ) := by
    rw [hm]
    exact (lower_compact_degree_bounds CM L B hCM hB hsize).1
  have hJlo : gamma*CM*L/B ≤ (J : ℝ) := by
    have := mul_le_mul_of_nonneg_left hmlo hg.le
    calc
      _ = gamma*(CM*L/B) := by ring
      _ ≤ gamma*m := this
      _ ≤ _ := hJ
  have hden : 0 < Real.exp 1*(ell^2*L/tau) := by positivity
  have hratio : (gamma*CM/(Real.exp 1*ell^2))*tau/B ≤
      (J : ℝ)/(Real.exp 1*(ell^2*L/tau)) := by
    apply (le_div_iff₀ hden).2
    calc
      _ = gamma*CM*L/B := by field_simp
      _ ≤ _ := hJlo
  have hlog := lower_compact_log_ratio tau _ _ ht hD hratio
  have hJ0 : 0 ≤ (J : ℝ) := Nat.cast_nonneg J
  calc
    4*L ≤ gamma*CM*L/2 := by nlinarith
    _ = (gamma*CM*L/B)*(B/2) := by field_simp
    _ ≤ (J : ℝ)*(B/2) := mul_le_mul_of_nonneg_right hJlo (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlog hJ0

/-- Equations (43)--(45) follow uniformly from the compact degree lower bound and (41). [Under the stated conditions](hyp:ht,hL,hg,hell,hCM,hbudget,hlarge,horder). [This is the stated conclusion](goal). -/
-- @node: lower_compact_order_decay
lemma lower_compact_order_decay (tau L gamma CM ell : ℝ) (J : ℕ)
    (ht : 1 ≤ tau) (hL : 0 < L) (hg : 0 < gamma) (hell : 0 < ell)
    (hCM : 0 < CM) (hlarge : 2*Real.exp 1 ≤ gamma*CM/(Real.exp 1*ell^2))
    (hbudget : 8 ≤ gamma*CM)
    (horder : gamma*CM*L/Real.log (Real.exp 1+tau) ≤ (J : ℝ)) :
    0 < J ∧ 2*(ell^2*L/tau) ≤ (J : ℝ) ∧
      4*L ≤ (J : ℝ)*Real.log ((J : ℝ)/(Real.exp 1*(ell^2*L/tau))) := by
  let B := Real.log (Real.exp 1+tau)
  have ht0 : 0 < tau := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hB : 0 < B := Real.log_pos (by linarith)
  have hJ : (0 : ℝ) < J := (div_pos (by positivity) hB).trans_le horder
  have hroot : 1 ≤ Real.sqrt tau := by
    have := Real.sqrt_le_sqrt ht
    simpa using this
  obtain ⟨hBsqrt, hBlog⟩ := lower_compact_log_bounds tau ht
  have hbase : Real.log (Real.exp 1+1) ≤ 2 := by
    simpa using (lower_compact_log_bounds 1 le_rfl).1
  have hratio : Real.exp 1*Real.sqrt tau ≤
      (J : ℝ)/(Real.exp 1*(ell^2*L/tau)) := by
    apply (le_div_iff₀ (by positivity : 0 < Real.exp 1*(ell^2*L/tau))).2
    apply le_trans _ horder
    apply (le_div_iff₀ hB).2
    have h2 := (le_div_iff₀ (show 0 < Real.exp 1*ell^2 by positivity)).mp hlarge
    calc
      _ ≤ (Real.exp 1*Real.sqrt tau*(Real.exp 1*(ell^2*L/tau)))*(2*Real.sqrt tau) :=
        mul_le_mul_of_nonneg_left hBsqrt (by positivity)
      _ = (2*Real.exp 1*(Real.exp 1*ell^2))*L := by
        field_simp
        nlinarith [Real.sq_sqrt ht0.le]
      _ ≤ gamma*CM*L := mul_le_mul_of_nonneg_right h2 hL.le
  have hratio2 : 2 ≤ (J : ℝ)/(Real.exp 1*(ell^2*L/tau)) := by
    have := mul_le_mul_of_nonneg_left hroot (Real.exp_pos (1 : ℝ)).le
    linarith
  have hcut := (le_div_iff₀ (show 0 < Real.exp 1*(ell^2*L/tau) by positivity)).mp hratio2
  have hlog : B/2 ≤ Real.log ((J : ℝ)/(Real.exp 1*(ell^2*L/tau))) := by
    have hl := Real.log_le_log (show 0 < Real.exp 1*Real.sqrt tau by positivity) hratio
    rw [Real.log_mul (by positivity) (by positivity), Real.log_exp,
      Real.log_sqrt ht0.le] at hl
    dsimp [B]
    linarith
  have hprod := mul_le_mul horder hlog (by positivity : 0 ≤ B/2) hJ.le
  have hid : (gamma*CM*L/B)*(B/2) = gamma*CM*L/2 := by field_simp
  rw [hid] at hprod
  refine ⟨by exact_mod_cast hJ, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right he (show 0 ≤ ell^2*L/tau by positivity)
    nlinarith
  · have := mul_le_mul_of_nonneg_right hbudget hL.le
    linarith

/-- In the public compact regime, (38) gives a degree scale at least twice the square root of L. [Under the stated conditions](hyp:hL,ht,hs). [This is the stated conclusion](goal). -/
-- @node: lower_compact_scale_lower_bound
lemma lower_compact_scale_lower_bound (sigma L : ℝ)
    (hs : sigma ∈ Set.Ioc (0 : ℝ) (1/4)) (hL : 1 ≤ L) (ht : 1 ≤ sigma^2*L) :
    0 < Real.log (Real.exp 1+sigma^2*L) ∧
      2*Real.sqrt L ≤ L/Real.log (Real.exp 1+sigma^2*L) := by
  have hL0 : 0 < L := by linarith
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hB : 0 < Real.log (Real.exp 1+sigma^2*L) := Real.log_pos (by linarith)
  have hroot : Real.sqrt (sigma^2*L) ≤ Real.sqrt L/4 := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    have hsquare : sigma^2 ≤ 1/16 := by nlinarith [hs.1, hs.2]
    have := mul_le_mul_of_nonneg_right hsquare hL0.le
    nlinarith [Real.sq_sqrt hL0.le]
  have hBroot : Real.log (Real.exp 1+sigma^2*L) ≤ Real.sqrt L/2 := by
    have := (lower_compact_log_bounds (sigma^2*L) ht).1
    linarith
  refine ⟨hB, (le_div_iff₀ hB).2 ?_⟩
  have := mul_le_mul_of_nonneg_left hBroot (show 0 ≤ 2*Real.sqrt L by positivity)
  nlinarith [Real.sq_sqrt hL0.le]

/-- Equations (39)--(42): a single lower bound on L ensures any fixed degree threshold,
and the compact bandwidth is positive and below the noise scale. [Under the stated conditions](hyp:hL,ht,hCM,hM,hsize,hs,hell). [This is the stated conclusion](goal). -/
-- @node: lower_compact_degree_radius_bounds
lemma lower_compact_degree_radius_bounds (sigma L CM ell M : ℝ)
    (hs : sigma ∈ Set.Ioc (0 : ℝ) (1/4)) (hL : 1 ≤ L) (ht : 1 ≤ sigma^2*L)
    (hCM : 1 ≤ CM) (hell : ell ∈ Set.Ioc (0 : ℝ) (1/4))
    (hM : 0 ≤ M) (hsize : M^2 ≤ L) :
    let B := Real.log (Real.exp 1+sigma^2*L)
    let m := Nat.ceil (CM*L/B)
    M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2*CM*L/B ∧
      ell/(m : ℝ) ∈ Set.Ioc (0 : ℝ) (1/4) ∧ ell/(m : ℝ) ≤ sigma := by
  dsimp only
  have hs0 := hs.1
  have hell0 := hell.1
  obtain ⟨hB, hscale⟩ := lower_compact_scale_lower_bound sigma L hs hL ht
  have hroot1 : 1 ≤ Real.sqrt L := by
    have := Real.sqrt_le_sqrt hL
    simpa using this
  have hLB : 1 ≤ L/Real.log (Real.exp 1+sigma^2*L) := by linarith
  obtain ⟨hlo, hhi, hm⟩ := lower_compact_degree_bounds CM L _ hCM hB hLB
  have hCMscale : L/Real.log (Real.exp 1+sigma^2*L) ≤
      CM*L/Real.log (Real.exp 1+sigma^2*L) := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_left (by linarith) hCM
  have hmscale := hscale.trans (hCMscale.trans hlo)
  have hm0 : (0 : ℝ) < Nat.ceil (CM*L/Real.log (Real.exp 1+sigma^2*L)) := by
    exact_mod_cast (show 0 < Nat.ceil (CM*L/Real.log (Real.exp 1+sigma^2*L)) by omega)
  have hMroot : M ≤ Real.sqrt L := (Real.le_sqrt hM (by linarith)).2 hsize
  have hsroot : 1 ≤ sigma*Real.sqrt L := by
    have hnonneg : 0 ≤ sigma*Real.sqrt L := by positivity
    have hid : (sigma*Real.sqrt L)^2 = sigma^2*L := by
      rw [mul_pow, Real.sq_sqrt (by linarith : 0 ≤ L)]
    nlinarith
  refine ⟨by linarith, hhi, ⟨by positivity, ?_⟩, ?_⟩
  · exact (div_le_self hell.1.le (by exact_mod_cast hm)).trans hell.2
  · apply (div_le_iff₀ hm0).2
    have := mul_le_mul_of_nonneg_left hmscale hs.1.le
    nlinarith [hell.2]

/-- The concrete compact degree and its floor cancellation order satisfy (40), (42),
(45), (46), and (47), uniformly over the public compact noise range. [Under the stated conditions](hyp:hk,hd,hn,hL,ht,hCM,hc,hM,hthreshold,hsize,hs,hell,hlarge,hbudget). [This is the stated conclusion](goal). -/
-- @node: lower_compact_tuning
lemma lower_compact_tuning (beta kappa sigma CM ell cPacket M : ℝ) (n : ℕ)
    (hk : 0 ≤ kappa) (hd : 0 ≤ effDim beta kappa) (hn : 0 < n)
    (hs : sigma ∈ Set.Ioc (0 : ℝ) (1/4))
    (hL : 1 ≤ logScale n) (ht : 1 ≤ sigma^2*logScale n)
    (hCM : 1 ≤ CM) (hell : ell ∈ Set.Ioc (0 : ℝ) (1/4)) (hc : 0 < cPacket)
    (hM : 4 ≤ M) (hthreshold : 2 ≤ cPacket*M) (hsize : M^2 ≤ logScale n)
    (hlarge : 2*Real.exp 1 ≤ (cPacket/2)*CM/(Real.exp 1*ell^2))
    (hbudget : 8 ≤ (cPacket/2)*CM) :
    let B := Real.log (Real.exp 1+sigma^2*logScale n)
    let m := Nat.ceil (CM*logScale n/B)
    let J := Nat.floor (cPacket*m)
    4 ≤ m ∧ 1 ≤ J ∧
      ell/(m : ℝ) ∈ Set.Ioc (0 : ℝ) (1/4) ∧ ell/(m : ℝ) ≤ sigma ∧
      (ell/(2*CM))*(B/logScale n) ≤ ell/(m : ℝ) ∧
      (n : ℝ)*(sigma^(-kappa-1)*(ell/m)^(2*beta+2*kappa+2)*momentTail sigma ell J) ≤ 2 := by
  dsimp only
  let B := Real.log (Real.exp 1+sigma^2*logScale n)
  let m := Nat.ceil (CM*logScale n/B)
  let J := Nat.floor (cPacket*m)
  have hL0 : 0 < logScale n := by linarith
  have hs0 := hs.1
  have hell0 := hell.1
  obtain ⟨hB, hscale⟩ := lower_compact_scale_lower_bound sigma (logScale n) hs hL ht
  have hroot1 : 1 ≤ Real.sqrt (logScale n) := by
    have := Real.sqrt_le_sqrt hL
    simpa using this
  have hLB : 1 ≤ logScale n/B := by dsimp [B]; linarith
  obtain ⟨hmM, hmhi, hh, hhs⟩ := lower_compact_degree_radius_bounds sigma (logScale n)
    CM ell M hs hL ht hCM hell (by linarith) hsize
  have hm4 : 4 ≤ m := by
    have : (4 : ℝ) ≤ m := hM.trans hmM
    exact_mod_cast this
  have hthreshold' : 2 ≤ cPacket*m :=
    hthreshold.trans (mul_le_mul_of_nonneg_left hmM hc.le)
  obtain ⟨horder, hJ1⟩ := lower_packet_cancellation_order cPacket m hthreshold'
  have hlo := Nat.le_ceil (CM*logScale n/B)
  have horder' : (cPacket/2)*CM*logScale n/B ≤ (J : ℝ) := by
    have := mul_le_mul_of_nonneg_left hlo (show 0 ≤ cPacket/2 by positivity)
    calc
      _ = (cPacket/2)*(CM*logScale n/B) := by ring
      _ ≤ (cPacket/2)*m := this
      _ ≤ _ := horder
  obtain ⟨hJ, hcut, hdecay⟩ := lower_compact_order_decay (sigma^2*logScale n)
    (logScale n) (cPacket/2) CM ell J ht hL0 (by positivity) hell0
    (by linarith) hlarge hbudget horder'
  have hlambda : ell^2/sigma^2 = ell^2*logScale n/(sigma^2*logScale n) := by
    field_simp
  rw [← hlambda] at hcut hdecay
  refine ⟨hm4, hJ1, hh, hhs,
    lower_compact_bandwidth_comparison ell CM (logScale n) B hell0.le hCM hB hLB, ?_⟩
  exact lower_compact_gaussian_sample_budget beta kappa sigma (ell/m) ell n J hk hd
    ⟨hh.1, hh.2.trans (by norm_num)⟩ hhs hn hJ (by positivity) hcut hdecay

end CausalSmith.Stat.NoisydoseWeakdesignTransition
