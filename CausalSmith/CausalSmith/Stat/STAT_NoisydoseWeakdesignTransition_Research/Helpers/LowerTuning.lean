module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.ObservedPerturbationBounds

/-! Lower-bound tuning: cancellation, bandwidth and sample budgets, compatible constants
(19), (31), (41), (51), and uniform logarithmic size conditions. -/
public section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition

/-- Above threshold (19), cancellation order is positive and at least half its unrounded value. [Under the stated conditions](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: lower_packet_cancellation_order
lemma lower_packet_cancellation_order (cPacket : ℝ) (m : ℕ)
    (hm : 2 ≤ cPacket * m) :
    (cPacket / 2) * m ≤ (Nat.floor (cPacket * m) : ℝ) ∧
      1 ≤ Nat.floor (cPacket * m) := by
  have hfloor := Nat.lt_floor_add_one (cPacket * (m : ℝ))
  constructor
  · nlinarith
  · have hone : (1 : ℝ) ≤ (Nat.floor (cPacket * m) : ℝ) := by linarith
    exact_mod_cast hone

/-- Equation (29) factors the Gaussian prefactor into a bandwidth power and a noise ratio. [Under the stated conditions](hyp:h,hs,hh). [This is the stated conclusion](goal). -/
-- @node: lower_gaussian_prefactor_identity
lemma lower_gaussian_prefactor_identity (beta kappa sigma h : ℝ)
    (hs : 0 < sigma) (hh : 0 < h) :
    sigma^(-kappa-1)*h^(2*beta+2*kappa+2) =
      h^(effDim beta kappa)*(h/sigma)^(kappa+1) := by
  rw [Real.div_rpow hh.le hs.le]
  have he : 2*beta+2*kappa+2 = effDim beta kappa + (kappa+1) := by
    unfold effDim
    ring
  rw [he, Real.rpow_add hh]
  rw [show -kappa-1 = -(kappa+1) by ring, Real.rpow_neg hs.le]
  ring

/-- When the bandwidth is below the noise scale, the ratio factor in (29) is at most one. [Under the stated conditions](hyp:h,hk,hh,hhs). [This is the stated conclusion](goal). -/
-- @node: lower_gaussian_prefactor_le
lemma lower_gaussian_prefactor_le (beta kappa sigma h : ℝ)
    (hk : 0 ≤ kappa) (hh : 0 < h) (hhs : h ≤ sigma) :
    sigma^(-kappa-1)*h^(2*beta+2*kappa+2) ≤ h^(effDim beta kappa) := by
  have hs : 0 < sigma := hh.trans_le hhs
  rw [lower_gaussian_prefactor_identity beta kappa sigma h hs hh]
  have hratio : (h/sigma)^(kappa+1) ≤ 1 :=
    Real.rpow_le_one (div_nonneg hh.le hs.le) ((div_le_one hs).2 hhs) (by linarith)
  exact (mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hh.le _)).trans_eq (mul_one _)

/-- The direct scale has exactly the effective-dimensional sample power appearing in (18). [Under the stated conditions](hyp:hd,hn). [This is the stated conclusion](goal). -/
-- @node: lower_direct_scale_sample_identity
lemma lower_direct_scale_sample_identity (beta kappa : ℝ) (n : ℕ)
    (hd : 0 < effDim beta kappa) (hn : 0 < n) :
    (n : ℝ)*(directScale beta kappa n)^(effDim beta kappa) = 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [directScale, ← Real.rpow_mul hnR.le]
  rw [show (-1 / effDim beta kappa) * effDim beta kappa = -1 by
    field_simp, Real.rpow_neg_one]
  exact mul_inv_cancel₀ hnR.ne'

/-- The bandwidth cutoff in (13) is chosen from the fixed effective dimension,
so it is independent of the public noise scale. [Under the stated conditions](hyp:hd). [This is the stated conclusion](goal). -/
-- @node: lower_direct_scale_sample_cutoff
lemma lower_direct_scale_sample_cutoff (beta kappa : ℝ)
    (hd : 0 < effDim beta kappa) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0,
      directScale beta kappa n ∈ Ioc (0 : ℝ) (1/4) := by
  let n0 := max 2 (Nat.ceil ((4 : ℝ)^effDim beta kappa))
  refine ⟨n0, le_max_left _ _, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := (le_max_left _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hceil : Nat.ceil ((4 : ℝ)^effDim beta kappa) ≤ n :=
    (le_max_right _ _).trans hn
  have hlarge : (4 : ℝ)^effDim beta kappa ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  refine ⟨by unfold directScale; positivity, ?_⟩
  change (n : ℝ)^(-1/effDim beta kappa) ≤ 1/4
  calc
    _ ≤ ((4 : ℝ)^effDim beta kappa)^(-1/effDim beta kappa) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hlarge (div_nonpos_of_nonpos_of_nonneg (by norm_num) hd.le)
    _ = 1/4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
        show effDim beta kappa * (-1/effDim beta kappa) = -1 by field_simp,
        Real.rpow_neg_one]
      norm_num

/-- Multiplying direct quadratic energy by n removes bandwidth dependence, as in (18). [Under the stated conditions](hyp:hk,he,hd,hn). [This is the stated conclusion](goal). -/
-- @node: lower_direct_quadratic_sample_budget
lemma lower_direct_quadratic_sample_budget (beta kappa epsilon : ℝ) (n : ℕ)
    (hk : 0 ≤ kappa) (he : 0 ≤ epsilon)
    (hd : 0 < effDim beta kappa) (hn : 0 < n) :
    (n : ℝ)*(∫ t, witnessDesignDensity kappa t *
      (directPerturbation beta epsilon (directScale beta kappa n) t)^2) ≤
      2*(kappa+1)*2^kappa*epsilon^2 := by
  have hh : 0 < directScale beta kappa n := by
    unfold directScale
    positivity
  have hb := mul_le_mul_of_nonneg_left
    (directPerturbation_quadratic_energy_le beta kappa epsilon _ hk he hh)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hid := lower_direct_scale_sample_identity beta kappa n hd hn
  change (n : ℝ)*(directScale beta kappa n)^(2*beta+kappa+1) = 1 at hid
  calc
    _ ≤ (n : ℝ)*((2*(kappa+1)*2^kappa*epsilon^2)*
        (directScale beta kappa n)^(2*beta+kappa+1)) := hb
    _ = (2*(kappa+1)*2^kappa*epsilon^2)*
        ((n : ℝ)*(directScale beta kappa n)^(2*beta+kappa+1)) := by ring
    _ = _ := by rw [hid, mul_one]

/-- Factorial-series terms above the cancellation order have ratio at most one half, as in (28). [Under the stated conditions](hyp:hl,hJ). [This is the stated conclusion](goal). -/
-- @node: lower_factorial_tail_term_le
lemma lower_factorial_tail_term_le (lambda : ℝ) (J k : ℕ)
    (hl : 0 ≤ lambda) (hJ : 2 * lambda ≤ (J : ℝ)) :
    lambda^(k+J)/(Nat.factorial (k+J) : ℝ) ≤
      (lambda^J/(Nat.factorial J : ℝ))*(1/2 : ℝ)^k := by
  have hstep (i : ℕ) :
      lambda^(i+J+1)/(Nat.factorial (i+J+1) : ℝ) ≤
        (1/2 : ℝ)*(lambda^(i+J)/(Nat.factorial (i+J) : ℝ)) := by
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hf : (0 : ℝ) < (Nat.factorial (i+J) : ℝ) := by positivity
    have hi : (0 : ℝ) < (i+J : ℕ)+1 := by positivity
    apply (div_le_iff₀ (mul_pos hi hf)).2
    have hratio : lambda ≤ (1/2 : ℝ)*((i+J : ℕ)+1) := by
      push_cast
      have : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have hm := mul_le_mul_of_nonneg_left hratio (pow_nonneg hl (i+J))
    field_simp
    nlinarith
  have hgeom := le_geom (u := fun i => lambda^(i+J)/(Nat.factorial (i+J) : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1/2) k (fun i _ => by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep i)
  simpa [mul_comm] using hgeom

/-- Summing the geometric ratio estimate gives the first inequality in (28). [This is the stated conclusion](goal). [Under the stated conditions](hyp:hJ). -/
-- @node: lower_momentTail_geometric_le
lemma lower_momentTail_geometric_le (sigma ell : ℝ) (J : ℕ)
    (hJ : 2 * (ell ^ 2 / sigma ^ 2) ≤ (J : ℝ)) :
    momentTail sigma ell J ≤ 2*(ell^2/sigma^2)^J/(Nat.factorial J : ℝ) := by
  let lambda : ℝ := ell^2/sigma^2
  have hl : 0 ≤ lambda := by dsimp [lambda]; positivity
  have hf := momentTail_summable sigma ell J
  have hshift : momentTail sigma ell J =
      ∑' k : ℕ, lambda^(k+J)/(Nat.factorial (k+J) : ℝ) := by
    have he := hf.sum_add_tsum_nat_add J
    have hz : (∑ j ∈ Finset.range J,
        if J ≤ j then (ell^2/sigma^2)^j/(Nat.factorial j : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp [not_le.mpr (Finset.mem_range.mp hj)]
    rw [hz, zero_add] at he
    simpa [momentTail, lambda] using he.symm
  rw [hshift]
  have hg : Summable (fun k : ℕ =>
      (lambda^J/(Nat.factorial J : ℝ))*(1/2 : ℝ)^k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
      (by norm_num : (1/2 : ℝ) < 1)).mul_left _
  have hb := (Real.summable_pow_div_factorial lambda).comp_injective
    (show Function.Injective (fun k : ℕ => k+J) from fun _ _ h => Nat.add_right_cancel h)
  calc
    _ ≤ ∑' k : ℕ, (lambda^J/(Nat.factorial J : ℝ))*(1/2 : ℝ)^k :=
      hb.tsum_le_tsum (fun k => lower_factorial_tail_term_le lambda J k hl hJ) hg
    _ = _ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)]
      dsimp [lambda]
      ring

/-- The factorial estimate in (28) bounds the leading term by its Stirling-scale expression. [Under the stated conditions](hyp:hl,hJ). [This is the stated conclusion](goal). -/
-- @node: lower_factorial_term_exponential_le
lemma lower_factorial_term_exponential_le (lambda : ℝ) (J : ℕ)
    (hl : 0 ≤ lambda) (hJ : 0 < J) :
    lambda^J/(Nat.factorial J : ℝ) ≤ (Real.exp 1*lambda/J)^J := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfact := Real.pow_div_factorial_le_exp (J : ℝ) (Nat.cast_nonneg J : (0 : ℝ) ≤ J) J
  have hexp : Real.exp (J : ℝ) = (Real.exp 1)^J := by
    simp [← Real.exp_nat_mul]
  rw [hexp] at hfact
  calc
    _ = (lambda/(J : ℝ))^J * ((J : ℝ)^J/(Nat.factorial J : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ (lambda/(J : ℝ))^J * (Real.exp 1)^J :=
      mul_le_mul_of_nonneg_left hfact (pow_nonneg (div_nonneg hl hJR.le) J)
    _ = _ := by rw [← mul_pow]; congr 1; ring

/-- Both inequalities of (28) apply to the public Gaussian moment tail. [Under the stated conditions](hyp:hpos,hJ). [This is the stated conclusion](goal). -/
-- @node: lower_momentTail_exponential_le
lemma lower_momentTail_exponential_le (sigma ell : ℝ) (J : ℕ)
    (hpos : 0 < J) (hJ : 2 * (ell ^ 2 / sigma ^ 2) ≤ (J : ℝ)) :
    momentTail sigma ell J ≤ 2*(Real.exp 1*(ell^2/sigma^2)/J)^J := by
  have hterm := lower_factorial_term_exponential_le (ell^2/sigma^2) J (by positivity) hpos
  calc
    _ ≤ 2*((ell^2/sigma^2)^J/(Nat.factorial J : ℝ)) := by
      simpa [mul_div_assoc] using lower_momentTail_geometric_le sigma ell J hJ
    _ ≤ _ := mul_le_mul_of_nonneg_left hterm (by norm_num)

/-- Equation (34): the small radius and linear cancellation order give exponential
suppression in the packet degree, uniformly at the intermediate-regime boundary. [Under the stated conditions](hyp:hg,hm,hlambda,ha,horder,hexp). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_tail_decay
lemma lower_intermediate_tail_decay (sigma ell a gamma : ℝ) (m J : ℕ)
    (hg : 0 < gamma) (hm : 0 < m)
    (hlambda : ell^2/sigma^2 = a^2*m)
    (horder : gamma*m ≤ (J : ℝ))
    (ha : a^2 ≤ gamma/2)
    (hexp : Real.exp 1*a^2/gamma ≤ Real.exp (-1/gamma)) :
    momentTail sigma ell J ≤ 2*Real.exp (-(m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hJR : (0 : ℝ) < J := (mul_pos hg hmR).trans_le horder
  have hJ : 0 < J := by exact_mod_cast hJR
  have hcut : 2*(ell^2/sigma^2) ≤ (J : ℝ) := by
    rw [hlambda]
    nlinarith
  have hbase : Real.exp 1*(ell^2/sigma^2)/J ≤ Real.exp (-1/gamma) := by
    rw [hlambda]
    apply le_trans _ hexp
    apply (div_le_div_iff₀ hJR hg).2
    have := mul_le_mul_of_nonneg_left horder (show 0 ≤ Real.exp 1*a^2 by positivity)
    nlinarith
  calc
    _ ≤ 2*(Real.exp 1*(ell^2/sigma^2)/J)^J :=
      lower_momentTail_exponential_le sigma ell J hJ hcut
    _ ≤ 2*(Real.exp (-1/gamma))^J :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase J) (by norm_num)
    _ = 2*Real.exp ((J : ℝ)*(-1/gamma)) := by rw [Real.exp_nat_mul]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      rw [show (J : ℝ)*(-1/gamma) = -(J : ℝ)/gamma by ring]
      apply (div_le_iff₀ hg).2
      nlinarith

/-- The logarithmic degree choice in (30) absorbs the effective sample size in (35). [Under the stated conditions](hyp:hN,hm). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_sample_decay
lemma lower_intermediate_sample_decay (N : ℝ) (m : ℕ)
    (hN : 0 ≤ N) (hm : Real.log (Real.exp 1+N) ≤ (m : ℝ)) :
    N*Real.exp (-(m : ℝ)) ≤ 1 := by
  have hpos : 0 < Real.exp 1+N := by positivity
  calc
    _ ≤ N*Real.exp (-Real.log (Real.exp 1+N)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg hm)) hN
    _ = N/(Real.exp 1+N) := by rw [Real.exp_neg, Real.exp_log hpos, div_eq_mul_inv]
    _ ≤ 1 := (div_le_one hpos).2 (by linarith [Real.exp_pos (1 : ℝ)])

/-- Equations (29), (34), and (35) bound the complete intermediate-regime
Gaussian-series sample factor by two, without a noise-dependent constant. [Under the stated conditions](hyp:h,hk,hd,hh,hhs,hg,hm,hlambda,ha,horder,hexp,hdegree). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_gaussian_sample_budget
lemma lower_intermediate_gaussian_sample_budget (beta kappa sigma h ell a gamma : ℝ)
    (n m J : ℕ) (hk : 0 ≤ kappa) (hd : 0 ≤ effDim beta kappa)
    (hh : 0 < h) (hhs : h ≤ sigma) (hg : 0 < gamma) (hm : 0 < m)
    (hlambda : ell^2/sigma^2 = a^2*m) (horder : gamma*m ≤ (J : ℝ))
    (ha : a^2 ≤ gamma/2)
    (hexp : Real.exp 1*a^2/gamma ≤ Real.exp (-1/gamma))
    (hdegree : Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa) ≤ (m : ℝ)) :
    (n : ℝ)*(sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J) ≤ 2 := by
  have hs := hh.trans_le hhs
  have hpref := (lower_gaussian_prefactor_le beta kappa sigma h hk hh hhs).trans
    (Real.rpow_le_rpow hh.le hhs hd)
  have htail := lower_intermediate_tail_decay sigma ell a gamma m J hg hm hlambda horder ha hexp
  have hsample := lower_intermediate_sample_decay ((n : ℝ)*sigma^effDim beta kappa)
    m (by positivity) hdegree
  calc
    _ ≤ (n : ℝ)*(sigma^effDim beta kappa*(2*Real.exp (-(m : ℝ)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hpref htail (by
        unfold momentTail
        exact tsum_nonneg (fun _ => by positivity)) (by positivity)) (Nat.cast_nonneg n)
    _ = 2*(((n : ℝ)*sigma^effDim beta kappa)*Real.exp (-(m : ℝ))) := by ring
    _ ≤ 2 := by linarith

/-- The decay exponent in (45) yields the compact-regime tail estimate used in (46). [Under the stated conditions](hyp:hJ,hlambda,hcut,hdecay). [This is the stated conclusion](goal). -/
-- @node: lower_compact_tail_decay
lemma lower_compact_tail_decay (sigma ell L : ℝ) (J : ℕ)
    (hJ : 0 < J) (hlambda : 0 < ell^2/sigma^2)
    (hcut : 2*(ell^2/sigma^2) ≤ (J : ℝ))
    (hdecay : 4*L ≤ (J : ℝ)*Real.log ((J : ℝ)/(Real.exp 1*(ell^2/sigma^2)))) :
    momentTail sigma ell J ≤ 2*Real.exp (-4*L) := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hbase : 0 < Real.exp 1*(ell^2/sigma^2)/J := by positivity
  have hlog : Real.log (Real.exp 1*(ell^2/sigma^2)/J) =
      -Real.log ((J : ℝ)/(Real.exp 1*(ell^2/sigma^2))) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  calc
    _ ≤ 2*(Real.exp 1*(ell^2/sigma^2)/J)^J :=
      lower_momentTail_exponential_le sigma ell J hJ hcut
    _ = 2*Real.exp ((J : ℝ)*Real.log (Real.exp 1*(ell^2/sigma^2)/J)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbase]
    _ ≤ _ := by
      rw [hlog]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      linarith

/-- The compact-regime exponential tail absorbs the sample size in (46). [Under the stated conditions](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: lower_compact_sample_decay
lemma lower_compact_sample_decay (n : ℕ) (hn : 0 < n) :
    (n : ℝ)*Real.exp (-4*logScale n) ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hL : 0 ≤ logScale n := by
    unfold logScale
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hn1
  calc
    _ ≤ (n : ℝ)*Real.exp (-logScale n) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hnR.le
    _ = 1/Real.exp 1 := by
      rw [logScale, Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
    _ ≤ 1 := (div_le_one (Real.exp_pos 1)).2 (Real.one_le_exp (by norm_num))

/-- Equations (29), (45), and (46) give a uniform compact-regime Gaussian-series
sample budget, after the degree choice has supplied the logarithmic decay. [Under the stated conditions](hyp:h,hk,hd,hhs,hn,hJ,hlambda,hh,hcut,hdecay). [This is the stated conclusion](goal). -/
-- @node: lower_compact_gaussian_sample_budget
lemma lower_compact_gaussian_sample_budget (beta kappa sigma h ell : ℝ) (n J : ℕ)
    (hk : 0 ≤ kappa) (hd : 0 ≤ effDim beta kappa)
    (hh : h ∈ Ioc (0 : ℝ) 1) (hhs : h ≤ sigma) (hn : 0 < n)
    (hJ : 0 < J) (hlambda : 0 < ell^2/sigma^2)
    (hcut : 2*(ell^2/sigma^2) ≤ (J : ℝ))
    (hdecay : 4*logScale n ≤
      (J : ℝ)*Real.log ((J : ℝ)/(Real.exp 1*(ell^2/sigma^2)))) :
    (n : ℝ)*(sigma^(-kappa-1)*h^(2*beta+2*kappa+2)*momentTail sigma ell J) ≤ 2 := by
  have hpref := (lower_gaussian_prefactor_le beta kappa sigma h hk hh.1 hhs).trans
    (Real.rpow_le_one hh.1.le hh.2 hd)
  have htail := lower_compact_tail_decay sigma ell (logScale n) J hJ hlambda hcut hdecay
  have hsample := lower_compact_sample_decay n hn
  calc
    _ ≤ (n : ℝ)*(1*(2*Real.exp (-4*logScale n))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hpref htail (by
        unfold momentTail
        exact tsum_nonneg (fun _ => by positivity)) (by norm_num)) (Nat.cast_nonneg n)
    _ = 2*((n : ℝ)*Real.exp (-4*logScale n)) := by ring
    _ ≤ 2 := by linarith

/-- Equation (32): rounding the logarithmic degree preserves both comparison constants. [Under the stated conditions](hyp:hCI,hS). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_degree_bounds
lemma lower_intermediate_degree_bounds (CI S : ℝ) (hCI : 1 ≤ CI) (hS : 1 ≤ S) :
    CI*S ≤ (Nat.ceil (CI*S) : ℝ) ∧
      (Nat.ceil (CI*S) : ℝ) ≤ (CI+1)*S ∧ 1 ≤ Nat.ceil (CI*S) := by
  have hlo := Nat.le_ceil (CI*S)
  have hhi := Nat.ceil_lt_add_one (show 0 ≤ CI*S by positivity)
  have hone : (1 : ℝ) ≤ Nat.ceil (CI*S) := by nlinarith
  exact ⟨hlo, by nlinarith, by exact_mod_cast hone⟩

/-- Equation (33): the concrete intermediate radius is legal and its bandwidth is below noise. [Under the stated conditions](hyp:hs,ha,ha1,hCI,hS,hSL,hsL,haCI). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_radius_bounds
lemma lower_intermediate_radius_bounds (sigma a CI S L : ℝ)
    (hs : 0 < sigma) (ha : 0 < a) (ha1 : a ≤ 1)
    (hCI : 1 ≤ CI) (hS : 1 ≤ S) (hSL : S ≤ L)
    (hsL : sigma*Real.sqrt L ≤ 1)
    (haCI : a*Real.sqrt (CI+1) ≤ 1/4) :
    let m := Nat.ceil (CI*S)
    let ell := a*sigma*Real.sqrt m
    ell ∈ Ioc (0 : ℝ) (1/4) ∧
      0 < ell/(m : ℝ) ∧ ell/(m : ℝ) ≤ sigma := by
  dsimp only
  obtain ⟨hlo, hhi, hm⟩ := lower_intermediate_degree_bounds CI S hCI hS
  have hmR : (1 : ℝ) ≤ Nat.ceil (CI*S) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < Nat.ceil (CI*S) := by linarith
  have hroot : Real.sqrt (Nat.ceil (CI*S) : ℝ) ≤ Real.sqrt (CI+1)*Real.sqrt L := by
    rw [← Real.sqrt_mul (by linarith : 0 ≤ CI+1)]
    apply Real.sqrt_le_sqrt
    exact hhi.trans (mul_le_mul_of_nonneg_left hSL (by linarith))
  have hell : a*sigma*Real.sqrt (Nat.ceil (CI*S) : ℝ) ≤ 1/4 := by
    calc
      _ ≤ a*sigma*(Real.sqrt (CI+1)*Real.sqrt L) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
      _ = (a*Real.sqrt (CI+1))*(sigma*Real.sqrt L) := by ring
      _ ≤ (a*Real.sqrt (CI+1))*1 :=
        mul_le_mul_of_nonneg_left hsL (by positivity)
      _ ≤ 1/4 := by simpa using haCI
  have hsqrt : Real.sqrt (Nat.ceil (CI*S) : ℝ) ≤ (Nat.ceil (CI*S) : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · nlinarith
  refine ⟨⟨by positivity, hell⟩, by positivity, ?_⟩
  apply (div_le_iff₀ hm0).2
  calc
    _ ≤ 1*sigma*Real.sqrt (Nat.ceil (CI*S) : ℝ) := by gcongr
    _ ≤ sigma*(Nat.ceil (CI*S) : ℝ) := by simpa using mul_le_mul_of_nonneg_left hsqrt hs.le

/-- The radius in (30) gives exactly the moment-tail parameter a²m. [Under the stated conditions](hyp:hs). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_lambda_identity
lemma lower_intermediate_lambda_identity (sigma a : ℝ) (m : ℕ)
    (hs : 0 < sigma) :
    (a*sigma*Real.sqrt m)^2/sigma^2 = a^2*m := by
  rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]
  field_simp

/-- Equation (36): the rounded degree preserves a uniform fraction of the intermediate frontier. [Under the stated conditions](hyp:hs,ha,hCI,hS). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_bandwidth_comparison
lemma lower_intermediate_bandwidth_comparison (sigma a CI S : ℝ)
    (hs : 0 < sigma) (ha : 0 < a) (hCI : 1 ≤ CI) (hS : 1 ≤ S) :
    (a/Real.sqrt (CI+1))*(sigma/Real.sqrt S) ≤
      (a*sigma*Real.sqrt (Nat.ceil (CI*S) : ℝ))/(Nat.ceil (CI*S) : ℝ) := by
  obtain ⟨hlo, hhi, hm⟩ := lower_intermediate_degree_bounds CI S hCI hS
  have hmR : (0 : ℝ) < Nat.ceil (CI*S) := by exact_mod_cast (show 0 < Nat.ceil (CI*S) by omega)
  have hr : 0 < Real.sqrt (Nat.ceil (CI*S) : ℝ) := Real.sqrt_pos.2 hmR
  have hroot := Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul (by linarith : 0 ≤ CI+1)] at hroot
  have hid : (a*sigma*Real.sqrt (Nat.ceil (CI*S) : ℝ))/(Nat.ceil (CI*S) : ℝ) =
      a*sigma/Real.sqrt (Nat.ceil (CI*S) : ℝ) := by
    apply (div_eq_div_iff hmR.ne' hr.ne').2
    calc
      _ = a*sigma*(Real.sqrt (Nat.ceil (CI*S) : ℝ))^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hmR.le]
  rw [hid]
  calc
    _ = a*sigma/(Real.sqrt (CI+1)*Real.sqrt S) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hr hroot

/-- The fixed degree threshold in (19) also supplies the intermediate multiplier in (32). [Under the stated conditions](hyp:hc). [This is the stated conclusion](goal). -/
-- @node: lower_packet_degree_constants
lemma lower_packet_degree_constants (cPacket : ℝ) (hc : 0 < cPacket) :
    ∃ M : ℕ, ∃ CI : ℝ,
      4 ≤ M ∧ 2 ≤ cPacket*M ∧ 4 ≤ CI ∧ 2 ≤ cPacket*CI ∧ (M : ℝ) ≤ CI := by
  let M := Nat.ceil (max (4 : ℝ) (2/cPacket))
  have h4 : (4 : ℝ) ≤ M := (le_max_left _ _).trans (Nat.le_ceil _)
  have hcut : 2/cPacket ≤ (M : ℝ) := (le_max_right _ _).trans (Nat.le_ceil _)
  have hcM : 2 ≤ cPacket*M := by
    have := (div_le_iff₀ hc).1 hcut
    nlinarith
  exact ⟨M, (M : ℝ), by exact_mod_cast h4, hcM, h4, hcM, le_rfl⟩

/-- After fixing the intermediate degree constant, all four small-radius restrictions
in (31) can be met by one positive constant, independent of sample size and noise. [Under the stated conditions](hyp:hCI,hc). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_radius_constant
lemma lower_intermediate_radius_constant (CI cPacket : ℝ)
    (hCI : 4 ≤ CI) (hc : 0 < cPacket) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ a*Real.sqrt (CI+1) ≤ 1/4 ∧
      a^2 ≤ (cPacket/2)/2 ∧
      Real.exp 1*a^2/(cPacket/2) ≤ Real.exp (-1/(cPacket/2)) := by
  let gamma := cPacket/2
  have hg : 0 < gamma := by dsimp [gamma]; positivity
  let b := min (gamma/2) (gamma*Real.exp (-1/gamma)/Real.exp 1)
  have hb : 0 < b := by dsimp [b]; positivity
  let a := min 1 (min (1/(4*Real.sqrt (CI+1))) (Real.sqrt b))
  have hroot : 0 < Real.sqrt (CI+1) := Real.sqrt_pos.2 (by linarith)
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a ≤ 1 := min_le_left _ _
  have har : a ≤ 1/(4*Real.sqrt (CI+1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have has : a ≤ Real.sqrt b := (min_le_right _ _).trans (min_le_right _ _)
  have hasq : a^2 ≤ b := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b]
  have hsmall : a^2 ≤ gamma/2 := hasq.trans (min_le_left _ _)
  have hexp : a^2 ≤ gamma*Real.exp (-1/gamma)/Real.exp 1 :=
    hasq.trans (min_le_right _ _)
  refine ⟨a, ha, ha1, ?_, hsmall, ?_⟩
  · have := (le_div_iff₀ (by positivity : 0 < 4*Real.sqrt (CI+1))).1 har
    nlinarith
  · change Real.exp 1*a^2/gamma ≤ Real.exp (-1/gamma)
    apply (div_le_iff₀ hg).2
    simpa only [mul_comm] using (le_div_iff₀ (Real.exp_pos 1)).1 hexp

/-- The large compact multiplier in (41) satisfies both the tail and sample-budget
restrictions with the fixed support radius, independently of sample size and noise. [Under the stated conditions](hyp:hc,hell). [This is the stated conclusion](goal). -/
-- @node: lower_compact_multiplier_constant
lemma lower_compact_multiplier_constant (cPacket ell : ℝ)
    (hc : 0 < cPacket) (hell : 0 < ell) :
    ∃ CM : ℝ, 1 ≤ CM ∧
      2*Real.exp 1 ≤ (cPacket/2)*CM/(Real.exp 1*ell^2) ∧
      8 ≤ (cPacket/2)*CM := by
  let gamma := cPacket/2
  have hg : 0 < gamma := by dsimp [gamma]; positivity
  let CM := max 1 (max (8/gamma) (2*Real.exp 1*(Real.exp 1*ell^2)/gamma))
  have h1 : 1 ≤ CM := le_max_left _ _
  have h8 : 8/gamma ≤ CM := (le_max_left _ _).trans (le_max_right _ _)
  have htail : 2*Real.exp 1*(Real.exp 1*ell^2)/gamma ≤ CM :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨CM, h1, ?_, ?_⟩
  · change 2*Real.exp 1 ≤ gamma*CM/(Real.exp 1*ell^2)
    apply (le_div_iff₀ (by positivity : 0 < Real.exp 1*ell^2)).2
    simpa only [mul_comm] using (div_le_iff₀ hg).1 htail
  · change 8 ≤ gamma*CM
    simpa only [mul_comm] using (div_le_iff₀ hg).1 h8

/-- One positive amplitude meets the direct and inverse range/smoothness requirements
and the common logarithmic testing budget log(1+τ²) in (51). The multiplier is fixed before
choosing the amplitude, as required by (48). [Under the stated conditions](hyp:hC,hstar,htau). [This is the stated conclusion](goal). -/
-- @node: lower_common_amplitude_constant
lemma lower_common_amplitude_constant (Cpacket Cstar tau : ℝ)
    (hC : 0 < Cpacket) (hstar : 0 < Cstar) (htau : 0 < tau) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1/8 ∧
      4*epsilon ≤ 1 ∧ epsilon*Cpacket ≤ 1/8 ∧
      Cstar*epsilon^2 ≤ Real.log (1 + tau^2) := by
  have hlog : 0 < Real.log (1 + tau^2) := Real.log_pos (by have := pow_pos htau 2; linarith)
  let b := Real.log (1 + tau^2)/Cstar
  have hb : 0 < b := by dsimp [b]; positivity
  let epsilon := min (1/8 : ℝ) (min (1/(8*Cpacket)) (Real.sqrt b))
  have he : 0 < epsilon := by dsimp [epsilon]; positivity
  have heSmall : epsilon ≤ 1/8 := min_le_left _ _
  have heC : epsilon ≤ 1/(8*Cpacket) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have heRoot : epsilon ≤ Real.sqrt b :=
    (min_le_right _ _).trans (min_le_right _ _)
  have heSq : epsilon^2 ≤ b := by
    nlinarith [Real.sq_sqrt hb.le, Real.sqrt_nonneg b]
  refine ⟨epsilon, he, heSmall, by linarith, ?_, ?_⟩
  · have := (le_div_iff₀ (by positivity : 0 < 8*Cpacket)).1 heC
    nlinarith
  · have := (le_div_iff₀ hstar).1 heSq
    nlinarith

/-- For every admissible noise scale, the intermediate logarithm lies between one
and the public sample logarithm once there are at least two observations; this is
uniform in noise as used in (32)--(33). [Under the stated conditions](hyp:hd,hn,hs). [This is the stated conclusion](goal). -/
-- @node: lower_intermediate_log_window
lemma lower_intermediate_log_window (beta kappa sigma : ℝ) (n : ℕ)
    (hd : 0 ≤ effDim beta kappa) (hs : sigma ∈ Icc (0 : ℝ) (1/4))
    (hn : 2 ≤ n) :
    1 ≤ Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa) ∧
      Real.log (Real.exp 1+(n : ℝ)*sigma^effDim beta kappa) ≤ logScale n := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have he : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpower : sigma^effDim beta kappa ≤ 1 :=
    Real.rpow_le_one hs.1 (by linarith [hs.2]) hd
  have hN : (n : ℝ)*sigma^effDim beta kappa ≤ n := by
    simpa using mul_le_mul_of_nonneg_left hpower (Nat.cast_nonneg n)
  have hNpos : 0 ≤ (n : ℝ)*sigma^effDim beta kappa :=
    mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg hs.1 _)
  constructor
  · have hlog := Real.log_le_log (Real.exp_pos 1)
      (show Real.exp 1 ≤ Real.exp 1+(n : ℝ)*sigma^effDim beta kappa by linarith)
    simpa using hlog
  · have hbound : Real.exp 1+(n : ℝ)*sigma^effDim beta kappa ≤ Real.exp 1*n := by
      nlinarith
    simpa only [logScale] using Real.log_le_log
      (show 0 < Real.exp 1+(n : ℝ)*sigma^effDim beta kappa by
        linarith [Real.exp_pos (1 : ℝ)]) hbound

/-- A deterministic sample cutoff makes the compact degree size condition hold
uniformly in noise, without adding it as an assumption on the model. [This is the stated conclusion](goal). -/
-- @node: lower_log_sample_cutoff
lemma lower_log_sample_cutoff (M : ℝ) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0, M^2 ≤ logScale n := by
  let n0 := max 2 (Nat.ceil (Real.exp (M^2)))
  refine ⟨n0, le_max_left _ _, ?_⟩
  intro n hn
  have hceil : Nat.ceil (Real.exp (M^2)) ≤ n := (le_max_right _ _).trans hn
  have hlarge : Real.exp (M^2) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have he : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hproduct : Real.exp (M^2) ≤ Real.exp 1*n :=
    hlarge.trans (le_mul_of_one_le_left (Nat.cast_nonneg n) he)
  have := Real.log_le_log (Real.exp_pos (M^2)) hproduct
  simpa only [Real.log_exp, logScale] using this

end CausalSmith.Stat.NoisydoseWeakdesignTransition
