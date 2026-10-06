module

public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Contraction.Density
public import CausalSmith.Stat.STAT_LdpOptvalueUniformFrontier_Research.Helpers.Frontier.ConverseResources
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Geometric calibration of adaptive contraction

The binomial and privacy bounds turn the adaptive contraction coefficient into
its resource-normalized geometric form, as in equation (15) of the proof.
-/

public section

noncomputable section
open scoped BigOperators
namespace CausalSmith.Stat.LdpOptvalueUniformFrontier

/-- Assume [the stated hk condition](hyp:hk). [The exponential-series bound gives the classical exponential upper bound on a binomial coefficient](goal). -/
-- @node: contraction_choose_le_exp_power
lemma contraction_choose_le_exp_power (n k : ℕ) (hk : 0 < k) :
    (Nat.choose n k : ℝ) ≤ (Real.exp 1 * n / k)^k := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hexp := Real.pow_div_factorial_le_exp (k : ℝ) (show (0 : ℝ) ≤ k by positivity) k
  have hfactor : (k : ℝ)^k / (k.factorial : ℝ) ≤ (Real.exp 1)^k := by
    simpa only [← Real.exp_nat_mul, mul_one] using hexp
  calc
    (Nat.choose n k : ℝ) ≤ (n : ℝ)^k / (k.factorial : ℝ) := Nat.choose_le_pow_div k n
    _ = ((n : ℝ)/k)^k * ((k : ℝ)^k / (k.factorial : ℝ)) := by
      rw [div_pow]
      field_simp
    _ ≤ ((n : ℝ)/k)^k * (Real.exp 1)^k :=
      mul_le_mul_of_nonneg_left hfactor (by positivity)
    _ = (Real.exp 1 * n / k)^k := by rw [← mul_pow]; congr 1; ring

/-- Assume [the stated hk condition](hyp:hk). [Taking square roots gives the factor appearing in the higher-order adaptive first-moment bound](goal). -/
-- @node: contraction_sqrt_choose_le
lemma contraction_sqrt_choose_le (n k : ℕ) (hk : 0 < k) :
    Real.sqrt (Nat.choose n k) ≤ (Real.sqrt (Real.exp 1 * n / k))^k := by
  have hbase : 0 ≤ Real.exp 1 * (n : ℝ) / k := by positivity
  have hs : ((Real.sqrt (Real.exp 1 * n / k))^k)^2 =
      (Real.exp 1 * (n : ℝ) / k)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, Real.sq_sqrt hbase]
  have hchoose := contraction_choose_le_exp_power n k hk
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ Nat.choose n k by positivity)
  nlinarith [Real.sqrt_nonneg (Nat.choose n k),
    pow_nonneg (Real.sqrt_nonneg (Real.exp 1 * (n : ℝ) / k)) k]

/-- Assume [positive dimension](hyp:hd) and [a privacy budget in the interval from zero to one](hyp:heps). [Pure local privacy on the stated budget range bounds the coordinate score scale by epsilon divided by dimension](goal). -/
-- @node: contraction_derivativeScale_le
lemma contraction_derivativeScale_le (d : ℕ) (hd : 0 < d) (eps : ℝ)
    (heps : eps ∈ Set.Ioc 0 1) : derivativeScale d eps ≤ eps / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Real.abs_exp_sub_one_le (show |eps| ≤ 1 by
    rw [abs_of_pos heps.1]; exact heps.2)
  rw [abs_of_pos heps.1] at h
  have hbound := (le_abs_self (Real.exp eps - 1)).trans h
  unfold derivativeScale
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2*d) hdR).mpr
  nlinarith

/-- Assume [positive dimension](hyp:hd), [the stated hk condition](hyp:hk), [a privacy budget in the interval from zero to one](hyp:heps), and [nonnegative amplitude](hyp:ha). [Equation (15): the binomial contraction coefficient is bounded by a geometric power of the resource-normalized amplitude](goal). -/
-- @node: contraction_coefficient_geometric_le
lemma contraction_coefficient_geometric_le (n d k : ℕ) (hd : 0 < d)
    (hk : 0 < k) (eps a : ℝ) (heps : eps ∈ Set.Ioc 0 1) (ha : 0 ≤ a) :
    (d : ℝ)*a^k*Real.sqrt (Nat.choose n k)*(derivativeScale d eps)^k ≤
      (d : ℝ)*(a*Real.sqrt (Real.exp 1*n/k)*(eps/d))^k := by
  have hbeta : 0 ≤ derivativeScale d eps := by
    unfold derivativeScale
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp_iff.mpr heps.1.le)) (by positivity)
  calc
    _ ≤ (d : ℝ)*a^k*(Real.sqrt (Real.exp 1*n/k))^k*(eps/d)^k := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (contraction_sqrt_choose_le n k hk) (by positivity)
      · exact pow_le_pow_left₀ hbeta (contraction_derivativeScale_le d hd eps heps) k
      · positivity
      · positivity
    _ = _ := by simp only [mul_pow]; ring

/-- Assume [the stated hz condition](hyp:hz), [the stated hw condition](hyp:hw), [the stated hk condition](hyp:hk), [a nonnegative bias bound](hyp:hB), [the stated hround condition](hyp:hround), [the stated hsq condition](hyp:hsq), and [the stated hbudget condition](hyp:hbudget). [A rounded matching order turns a squared geometric coefficient bound into exponential decay in the resource logarithm](goal). -/
-- @node: converse_geometric_base_decay
lemma converse_geometric_base_decay (L z w a B : ℝ) (k : ℕ)
    (hz : 0 < z) (hw : 0 < w) (hk : 0 < k) (hB : 0 ≤ B)
    (hround : 32*L ≤ (k : ℝ)*w)
    (hsq : B^2 ≤ a^2*Real.exp 1*L/((k : ℝ)*z))
    (hbudget : a^2*Real.exp 1*w*Real.exp (w/2) ≤ 32*z) :
    B ≤ Real.exp (-w/4) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hE : 0 < Real.exp (w/2) := Real.exp_pos _
  have hm := mul_le_mul_of_nonneg_left hround
    (show 0 ≤ a^2*Real.exp 1*Real.exp (w/2) by positivity)
  have hb := mul_le_mul_of_nonneg_left hbudget hkR.le
  have hnum : a^2*Real.exp 1*L*Real.exp (w/2) ≤ (k : ℝ)*z := by
    nlinarith only [hm, hb]
  have hratio : a^2*Real.exp 1*L/((k : ℝ)*z) ≤ 1/Real.exp (w/2) := by
    apply (div_le_div_iff₀ (mul_pos hkR hz) hE).mpr
    simpa using hnum
  have hident : (Real.exp (-w/4))^2 = 1/Real.exp (w/2) := by
    rw [← Real.exp_nat_mul, one_div, ← Real.exp_neg]
    congr 1
    push_cast
    ring
  have hfinal := hsq.trans hratio
  rw [← hident] at hfinal
  nlinarith [Real.exp_pos (-w/4)]

/-- Assume [the stated hz condition](hyp:hz). [The logarithm in the nondense branch has the exponential budget needed for the fixed amplitude one hundredth](goal). -/
-- @node: converse_nondense_exponential_budget
lemma converse_nondense_exponential_budget (z : ℝ) (hz : 1 ≤ z) :
    (1/100 : ℝ)^2*Real.exp 1*Real.log (Real.exp 1+z)*
      Real.exp (Real.log (Real.exp 1+z)/2) ≤ 32*z := by
  let w := Real.log (Real.exp 1+z)
  have hE : 0 < Real.exp (w/2) := Real.exp_pos _
  have hlog : Real.exp w = Real.exp 1+z := Real.exp_log (by positivity)
  have hsq : (Real.exp (w/2))^2 = Real.exp 1+z := by
    rw [← Real.exp_nat_mul]
    convert hlog using 1 <;> congr 1 <;> push_cast <;> ring
  have hlin : w ≤ 2*Real.exp (w/2) := by
    linarith [Real.add_one_le_exp (w/2)]
  have hprod : w*Real.exp (w/2) ≤ 8*z := by
    have hm := mul_le_mul_of_nonneg_right hlin hE.le
    nlinarith [Real.exp_one_lt_three]
  have hwp : 0 ≤ w*Real.exp (w/2) := by
    apply mul_nonneg _ hE.le
    exact (Real.log_nonneg (by linarith [Real.add_one_le_exp 1]))
  change (1/100 : ℝ)^2*Real.exp 1*w*Real.exp (w/2) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le hwp]

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [At the prescribed public amplitude and matching order, the geometric coefficient has exponentially small base in each resource branch](goal). -/
-- @node: frontier_converse_geometric_base
lemma frontier_converse_geometric_base (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    let z := (d : ℝ)^2*logDim d/((n : ℝ)*eps^2)
    let w := if z ≤ 1 then 1 else Real.log (Real.exp 1+z)
    let k := (frontierResources n d eps).converseDegree
    (frontierResources n d eps).converseAmp * Real.sqrt (Real.exp 1*n/k)*(eps/d) ≤
      Real.exp (-w/4) ∧ 32*logDim d ≤ (k : ℝ)*w := by
  let L := logDim d
  let t := (n : ℝ)*eps^2
  let z := (d : ℝ)^2*L/t
  let k := (frontierResources n d eps).converseDegree
  let a := (frontierResources n d eps).converseAmp
  let B := a*Real.sqrt (Real.exp 1*n/k)*(eps/d)
  have hL : 0 < L := logDim_pos d hAllowed.2.1
  have hn : (0 : ℝ) < n := by exact_mod_cast (by have := hAllowed.1; omega : 0 < n)
  have hd : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
  have ht : 0 < t := mul_pos hn (sq_pos_of_pos hAllowed.2.2.1)
  have hz : 0 < z := by dsimp [z]; positivity
  have hk : 0 < k := by
    have h := (frontier_converse_degree_domain n d eps hAllowed).1
    dsimp [k]
    omega
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have ha : 0 < a := (frontier_converse_amplitude_domain n d eps hAllowed).1
  have heps : 0 < eps := hAllowed.2.2.1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsq : B^2 = a^2*Real.exp 1*L/((k : ℝ)*z) := by
    dsimp only [B]
    rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), div_pow]
    dsimp [z, t]
    field_simp
  change B ≤ Real.exp (-(if z ≤ 1 then 1 else Real.log (Real.exp 1+z))/4) ∧
    32*L ≤ (k : ℝ)*(if z ≤ 1 then 1 else Real.log (Real.exp 1+z))
  by_cases hs : z ≤ 1
  · have hak : a = (1/100 : ℝ)*Real.sqrt z ∧ k = 2*⌈16*L⌉₊+1 := by
      dsimp only [a, k, frontierResources]
      simp only [z, t, L] at hs ⊢
      simp only [if_pos hs, and_self]
    have hround : 32*L ≤ (k : ℝ)*1 := by
      rw [hak.2]
      have hc := Nat.le_ceil (16*L)
      push_cast
      linarith
    have hbudget : a^2*Real.exp 1*1*Real.exp (1/2) ≤ 32*z := by
      rw [hak.1, mul_pow, Real.sq_sqrt hz.le]
      have hhalf : Real.exp ((1 : ℝ)/2) ≤ 3 :=
        (Real.exp_le_exp.mpr (by norm_num)).trans Real.exp_one_lt_three.le
      have hm := mul_le_mul Real.exp_one_lt_three.le hhalf
        (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 3)
      nlinarith
    rw [if_pos hs]
    exact ⟨converse_geometric_base_decay L z 1 a B k hz (by norm_num)
      hk hB hround hsq.le hbudget, hround⟩
  · let w := Real.log (Real.exp 1+z)
    have hw : 0 < w := by
      apply Real.log_pos
      linarith [Real.add_one_le_exp 1]
    have hak : a = (1/100 : ℝ) ∧ k = 2*⌈16*L/w⌉₊+1 := by
      dsimp only [a, k, frontierResources]
      simp only [z, t, L, w] at hs ⊢
      simp only [if_neg hs, and_self]
    have hround : 32*L ≤ (k : ℝ)*w := by
      have hc := Nat.le_ceil (16*L/w)
      have hm := (div_le_iff₀ hw).mp hc
      rw [hak.2]
      push_cast
      nlinarith
    have hbudget : a^2*Real.exp 1*w*Real.exp (w/2) ≤ 32*z := by
      rw [hak.1]
      exact converse_nondense_exponential_budget z (le_of_not_ge hs)
    rw [if_neg hs]
    exact ⟨converse_geometric_base_decay L z w a B k hz hw hk hB
      hround hsq.le hbudget, hround⟩

/-- Assume [an admissible sample size, dimension, and privacy budget](hyp:hAllowed). [The exact prescribed amplitude and rounded matching order make equation (15)'s geometric transcript bound at most one hundredth, in both branches](goal). -/
-- @node: frontier_converse_geometric_small
lemma frontier_converse_geometric_small (n d : ℕ) (eps : ℝ)
    (hAllowed : Allowed n d eps) :
    (d : ℝ)*((frontierResources n d eps).converseAmp *
      Real.sqrt (Real.exp 1*n/(frontierResources n d eps).converseDegree)*(eps/d))^
        (frontierResources n d eps).converseDegree ≤ (1/100 : ℝ) := by
  let L := logDim d
  let z := (d : ℝ)^2*L/((n : ℝ)*eps^2)
  let w := if z ≤ 1 then 1 else Real.log (Real.exp 1+z)
  let k := (frontierResources n d eps).converseDegree
  let B := (frontierResources n d eps).converseAmp * Real.sqrt (Real.exp 1*n/k)*(eps/d)
  obtain ⟨hbase, hround⟩ := frontier_converse_geometric_base n d eps hAllowed
  change B ≤ Real.exp (-w/4) at hbase
  change 32*L ≤ (k : ℝ)*w at hround
  have hd : (0 : ℝ) < d := by exact_mod_cast (by have := hAllowed.2.1; omega : 0 < d)
  have heps := hAllowed.2.2.1
  have ha := (frontier_converse_amplitude_domain n d eps hAllowed).1
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hp := pow_le_pow_left₀ hB hbase k
  rw [← Real.exp_nat_mul] at hp
  have hexp : Real.exp ((k : ℝ)*(-w/4)) ≤ Real.exp (-8*L) :=
    Real.exp_le_exp.mpr (by linarith)
  have hdim : (d : ℝ) ≤ Real.exp L := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    have hlog : Real.exp L = Real.exp 1*d := Real.exp_log (by positivity)
    rw [hlog]
    nlinarith
  have hL : 1 ≤ L := (logDim_bounds d hAllowed.2.1).1
  have hseven : 100 ≤ Real.exp (7 : ℝ) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 7
    rw [← Real.exp_nat_mul] at hh
    norm_num at hh ⊢
    linarith
  change (d : ℝ)*B^k ≤ _
  calc
    _ ≤ (d : ℝ)*Real.exp (-8*L) := mul_le_mul_of_nonneg_left (hp.trans hexp) hd.le
    _ ≤ Real.exp L*Real.exp (-8*L) := mul_le_mul_of_nonneg_right hdim (Real.exp_pos _).le
    _ = Real.exp (-7*L) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-7) := Real.exp_le_exp.mpr (by linarith)
    _ ≤ 1/100 := by
      rw [Real.exp_neg]
      rw [← one_div]
      exact one_div_le_one_div_of_le (by norm_num) hseven

end CausalSmith.Stat.LdpOptvalueUniformFrontier
