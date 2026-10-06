module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.Upper

/-!
# Converse resource calibration

The prescribed amplitude and rounded moment degree yield separation at the
square-root frontier rate, in both resource branches including saturation.
-/

public section

noncomputable section
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hx condition](hyp:hx). [Rounding the even approximation degree costs at most a factor thirty-four](goal). -/
-- @node: converse_even_degree_bound
lemma converse_even_degree_bound (x : ℝ) (hx : 0 < x) :
    0 < 2 * ⌈16*x⌉₊ ∧ Even (2 * ⌈16*x⌉₊) ∧
      (2 * ⌈16*x⌉₊ : ℕ) ≤ 34 * max 1 x := by
  have hceil := Nat.le_ceil (16*x)
  have hceilpos : 0 < ⌈16*x⌉₊ := by
    by_contra h
    have hz : ⌈16*x⌉₊ = 0 := by omega
    rw [hz] at hceil
    norm_num at hceil
    linarith
  refine ⟨by omega, ⟨⌈16*x⌉₊, by omega⟩, ?_⟩
  have hround := Nat.ceil_lt_add_one (show 0 ≤ 16*x by positivity)
  push_cast
  have hm1 : 1 ≤ max 1 x := le_max_left _ _
  have hmx : x ≤ max 1 x := le_max_right _ _
  linarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The public amplitude is positive and remains inside the paired parameter cube](goal). -/
-- @node: frontier_converse_amplitude_domain
lemma frontier_converse_amplitude_domain (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    (frontierResources n d eps).converseAmp ∈ Set.Ioc 0 (1/2 : ℝ) := by
  have hL := logDim_pos d hAllowed.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ)*eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hd : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
  have hz : 0 < (d : ℝ)^2 * logDim d / (n*eps^2) := by positivity
  change (if (d : ℝ)^2 * logDim d / (n*eps^2) ≤ 1 then
    (1/100 : ℝ)*Real.sqrt ((d : ℝ)^2 * logDim d / (n*eps^2)) else 1/100) ∈ _
  split_ifs with hsmall
  · have hs := Real.sqrt_pos.mpr hz
    have hu : Real.sqrt ((d : ℝ)^2 * logDim d / (n*eps^2)) ≤ 1 := by
      exact (Real.sqrt_le_one).mpr hsmall
    constructor
    · positivity
    · linarith
  · constructor <;> norm_num

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The chosen approximation degree is a positive even number, before adding one to obtain the matching order in the contraction theorem](goal). -/
-- @node: frontier_converse_degree_domain
lemma frontier_converse_degree_domain (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    0 < (frontierResources n d eps).converseDegree - 1 ∧
      Even ((frontierResources n d eps).converseDegree - 1) := by
  have hL := logDim_pos d hAllowed.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ)*eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hz : 0 ≤ (d : ℝ)^2 * logDim d / (n*eps^2) := by positivity
  have hw : 0 < Real.log (Real.exp 1 + (d : ℝ)^2 * logDim d / (n*eps^2)) := by
    have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    apply Real.log_pos
    linarith
  dsimp only [frontierResources]
  split_ifs
  · have h := converse_even_degree_bound (logDim d) hL
    have hp := And.intro h.1 h.2.1
    simpa only [Nat.add_sub_cancel] using hp
  · have h := converse_even_degree_bound
      (logDim d/Real.log (Real.exp 1+(d : ℝ)^2*logDim d/(n*eps^2))) (div_pos hL hw)
    have hp := And.intro h.1 h.2.1
    simpa only [Nat.add_sub_cancel, mul_div_assoc] using hp

/-- Assume [the stated hx condition](hyp:hx), [the stated hr0 condition](hyp:hr0), [the stated hr1 condition](hyp:hr1), and [the stated hrx condition](hyp:hrx). [A normalized rate factor cancels the reciprocal resource scale in the rounded degree](goal). -/
-- @node: converse_even_degree_normalized
lemma converse_even_degree_normalized (x r : ℝ) (hx : 0 < x)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hrx : r * x ≤ 1) :
    r * (2 * ⌈16*x⌉₊ : ℕ) ≤ 34 := by
  have hround := Nat.ceil_lt_add_one (show 0 ≤ 16*x by positivity)
  have hm := mul_le_mul_of_nonneg_left hround.le hr0
  push_cast
  nlinarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The prescribed amplitude divided by the approximation degree dominates one thirty-four-hundredth of the square-root frontier rate](goal). -/
-- @node: frontier_converse_gap_rate
lemma frontier_converse_gap_rate (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    (1/3400 : ℝ) * rateH .SI n d eps ≤
      (frontierResources n d eps).converseAmp /
        (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ) := by
  let L := logDim d
  let t := (n : ℝ)*eps^2
  let z := (d : ℝ)^2*L/t
  let w := Real.log (Real.exp 1+z)
  have hL : 0 < L := logDim_pos d hAllowed.2.1
  have hL1 : 1 ≤ L := (logDim_bounds d hAllowed.2.1).1
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < t := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hd : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
  have hz : 0 < z := by dsimp [z]; positivity
  have hw : 0 < w := by
    have he := Real.one_lt_exp_iff.mpr (show (0 : ℝ) < 1 by norm_num)
    apply Real.log_pos
    linarith
  have hdegree : (0 : ℝ) < ((frontierResources n d eps).converseDegree - 1 : ℕ) :=
    by exact_mod_cast (frontier_converse_degree_domain n d eps hAllowed).1
  apply (le_div_iff₀ hdegree).mpr
  by_cases hsmall : z ≤ 1
  · have hbranch : (d : ℝ)^2*L ≤ t := (div_le_one ht).mp hsmall
    have hrate : rateH .SI n d eps = Real.sqrt z/L := by
      unfold rateH rateR rho
      rw [if_pos hbranch]
      have heq : (d : ℝ)^2/(t*L) = z/L^2 := by dsimp [z]; field_simp
      change Real.sqrt ((d : ℝ)^2/(t*L)) = _
      rw [heq, Real.sqrt_div hz.le, Real.sqrt_sq hL.le]
    have hbound := (converse_even_degree_bound L hL).2.2
    rw [max_eq_right hL1] at hbound
    have hm := mul_le_mul_of_nonneg_left hbound (div_nonneg (Real.sqrt_nonneg z) hL.le)
    have heq : (Real.sqrt z/L)*(34*L) = 34*Real.sqrt z := by field_simp
    rw [heq] at hm
    have hamp : (frontierResources n d eps).converseAmp = (1/100 : ℝ)*Real.sqrt z := by
      dsimp only [frontierResources]
      exact if_pos hsmall
    have hdeg : (frontierResources n d eps).converseDegree - 1 = 2*⌈16*L⌉₊ := by
      dsimp only [frontierResources]
      rw [if_pos hsmall, Nat.add_sub_cancel]
    rw [hrate, hamp, hdeg]
    nlinarith
  · have hbranch : ¬ (d : ℝ)^2*L ≤ t := by
      intro h
      exact hsmall ((div_le_one ht).mpr h)
    let r := min 1 (w/L)
    have hr0 : 0 ≤ r := le_min (by norm_num) (div_pos hw hL).le
    have hr1 : r ≤ 1 := min_le_left _ _
    have hrx : r*(L/w) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (min_le_right 1 (w/L)) (div_pos hL hw).le
      have heq : (w/L)*(L/w) = 1 := by field_simp
      rwa [heq] at h
    have hbound := converse_even_degree_normalized (L/w) r (div_pos hL hw) hr0 hr1 hrx
    have hrate : rateH .SI n d eps = r := by
      unfold rateH rateR rho
      rw [if_neg hbranch]
      change Real.sqrt (r^2) = r
      exact Real.sqrt_sq hr0
    have hamp : (frontierResources n d eps).converseAmp = (1/100 : ℝ) := by
      dsimp only [frontierResources]
      exact if_neg hsmall
    have hdeg : (frontierResources n d eps).converseDegree - 1 = 2*⌈16*(L/w)⌉₊ := by
      dsimp only [frontierResources]
      rw [if_neg hsmall, Nat.add_sub_cancel]
      simp only [mul_div_assoc, L, w, z, t]
    rw [hrate, hamp, hdeg]
    nlinarith

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [In either resource branch, the positive even approximation degree is at most thirty-four times the logarithmic dimension, uniformly in sample size and privacy](goal). -/
-- @node: frontier_converse_degree_log_bound
lemma frontier_converse_degree_log_bound (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ) ≤ 34 * logDim d := by
  have hL := logDim_pos d hAllowed.2.1
  have hL1 := (logDim_bounds d hAllowed.2.1).1
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have ht : 0 < (n : ℝ)*eps^2 := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hz : 0 ≤ (d : ℝ)^2 * logDim d / (n*eps^2) := by positivity
  have hw : 1 ≤ Real.log (Real.exp 1 + (d : ℝ)^2*logDim d/(n*eps^2)) := by
    calc
      1 = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  dsimp only [frontierResources]
  split_ifs
  · simpa only [Nat.add_sub_cancel, max_eq_right hL1] using
      (converse_even_degree_bound (logDim d) hL).2.2
  · have hwpos : 0 < Real.log (Real.exp 1 + (d : ℝ)^2*logDim d/(n*eps^2)) :=
      lt_of_lt_of_le (by norm_num) hw
    have hx : logDim d / Real.log (Real.exp 1 + (d : ℝ)^2*logDim d/(n*eps^2)) ≤
        logDim d := (div_le_iff₀ hwpos).mpr (by nlinarith)
    have hm : max 1 (logDim d /
        Real.log (Real.exp 1 + (d : ℝ)^2*logDim d/(n*eps^2))) ≤ logDim d :=
      max_le hL1 hx
    have hb := (converse_even_degree_bound _ (div_pos hL hwpos)).2.2
    simp only [Nat.add_sub_cancel, mul_div_assoc] at *
    exact hb.trans (mul_le_mul_of_nonneg_left hm (by norm_num))

/-- [Squared logarithmic dimension divided by dimension vanishes, giving a universal cutoff for concentration of the prescribed product priors](goal). -/
-- @node: logDim_sq_div_tendsto_zero
lemma logDim_sq_div_tendsto_zero :
    Filter.Tendsto (fun d : ℕ => (logDim d)^2 / (d : ℝ))
      Filter.atTop (nhds 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop
    (Real.exp 1)⁻¹ 0 2 (by positivity)).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (Real.exp_pos 1))
  simpa only [Function.comp_def, logDim, mul_assoc, inv_mul_cancel_left₀
    (ne_of_gt (Real.exp_pos 1)), add_zero] using h

/-- Assume [the stated hb condition](hyp:hb). [Once the dimension exceeds a constant depending only on the universal approximation constant, the prior escape bound is at most one hundredth, uniformly over every allowed resource tuple](goal). -/
-- @node: frontier_converse_concentration_cutoff
lemma frontier_converse_concentration_cutoff (b : ℝ) (hb : 0 < b) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ n d eps, Allowed n d eps → D < d →
      16 * (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ)^2 /
        (b^2*d) ≤ (1/100 : ℝ) := by
  have hlim := logDim_sq_div_tendsto_zero.const_mul (16*34^2/b^2)
  simp only [mul_zero] at hlim
  have hsmall := hlim.eventually_lt_const (show (0 : ℝ) < 1/100 by norm_num)
  obtain ⟨D, hD⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨max 2 D, le_max_left _ _, ?_⟩
  intro n d eps hAllowed hdim
  have hd : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
  have hdegree := frontier_converse_degree_log_bound n d eps hAllowed
  have hsq := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ (((frontierResources n d eps).converseDegree - 1 : ℕ) : ℝ)) hdegree 2
  have htail := hD d (by omega)
  calc
    _ ≤ 16 * (34*logDim d)^2 / (b^2*d) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (by positivity)
    _ = (16*34^2/b^2) * ((logDim d)^2/(d : ℝ)) := by ring
    _ ≤ 1/100 := by simpa using htail.le

end CausalSmith.Stat.LdpOptvalueUniformFrontier
