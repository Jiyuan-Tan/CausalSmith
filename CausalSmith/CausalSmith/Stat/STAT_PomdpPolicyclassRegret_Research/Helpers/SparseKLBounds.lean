module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.ObservedKLChain
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFairObservedLaw
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.SparseFilterRecursion
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TSparsePackingMembership
public import Mathlib.InformationTheory.KullbackLeibler.Basic

/-! # Uniform filter bootstrap and retention-window KL constants -/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory InformationTheory
open CausalSmith.Stat.PomdpLatentOverlapMinimax
/-- [the reset ratio quantity](goal) is defined from [the mixing scale](hyp:t0). -/

noncomputable def resetRatio (t0 : ℝ) : ℝ :=
  mixingAlpha t0 / (1 - sparseSignal t0)
/-- [the filter constant quantity](goal) is defined from [the mixing scale](hyp:t0). -/

noncomputable def filterConstant (t0 : ℝ) : ℝ :=
  Real.exp (sparseSignal t0 * resetRatio t0 /
    ((1 - sparseSignal t0) * (1 - resetRatio t0) ^ 2))
/-- [the kl constant quantity](goal) is defined from [the mixing scale](hyp:t0) and
[the policy-overlap scale](hyp:zeta). -/

noncomputable def klConstant (t0 zeta : ℝ) : ℝ :=
  sparseSignal t0 ^ 2 * filterConstant t0 ^ 2 *
    Real.exp (policyFactor zeta - 1) / 4

/-- The sparse-context retention cost is uniformly bounded in the depth. This is estimate (20)
in the observed-word KL calculation. For [the hidden-depth scale](hyp:Q),
[the policy-overlap scale](hyp:zeta), and [the policy-overlap scale assumption](hyp:hzeta), this
establishes [the sparse retention probability pow bound result](goal). -/
-- @node: sparseRetentionProbability_pow_le
lemma sparseRetentionProbability_pow_le (Q : Nat) (zeta : ℝ)
    (hzeta : 0 < zeta) :
    sparseRetentionProbability Q zeta ^ Q ≤
      Real.exp (policyFactor zeta - 1) * policyFactor zeta ^ (-(Q : ℤ)) := by
  have hL : 1 ≤ policyFactor zeta := by
    unfold policyFactor
    exact (Real.one_le_exp_iff).2 (le_of_lt hzeta)
  have hLpos : 0 < policyFactor zeta := by
    unfold policyFactor
    exact Real.exp_pos _
  have hh : 0 < hdepth Q := by simp [hdepth]
  have hQh : Q ≤ hdepth Q := by simp [hdepth]
  have hhreal : (0 : ℝ) < hdepth Q := by exact_mod_cast hh
  have hQhreal : (Q : ℝ) ≤ hdepth Q := by exact_mod_cast hQh
  have hx : 0 ≤ (policyFactor zeta - 1) / hdepth Q :=
    div_nonneg (by linarith) (le_of_lt hhreal)
  have hbase : 1 ≤ 1 + (policyFactor zeta - 1) / hdepth Q := by linarith
  have hpow : (1 + (policyFactor zeta - 1) / hdepth Q) ^ Q ≤
      Real.exp (policyFactor zeta - 1) := by
    calc
      _ ≤ (Real.exp ((policyFactor zeta - 1) / hdepth Q)) ^ Q := by
        gcongr
        simpa [add_comm] using Real.add_one_le_exp
          ((policyFactor zeta - 1) / hdepth Q)
      _ = Real.exp ((Q : ℝ) * ((policyFactor zeta - 1) / hdepth Q)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (policyFactor zeta - 1) := by
        apply Real.exp_le_exp.mpr
        have hratio : (Q : ℝ) / hdepth Q ≤ 1 := (div_le_iff₀ hhreal).2 (by simpa using hQhreal)
        have hmul := mul_le_mul_of_nonneg_right hratio (by linarith : 0 ≤ policyFactor zeta - 1)
        calc
          (Q : ℝ) * ((policyFactor zeta - 1) / hdepth Q) =
              ((Q : ℝ) / hdepth Q) * (policyFactor zeta - 1) := by ring
          _ ≤ 1 * (policyFactor zeta - 1) := hmul
          _ = policyFactor zeta - 1 := one_mul _
  have hfactor : sparseRetentionProbability Q zeta =
      (policyFactor zeta)⁻¹ *
        (1 + (policyFactor zeta - 1) / hdepth Q) := by
    unfold sparseRetentionProbability
    field_simp
  rw [hfactor, mul_pow]
  have hinv : (policyFactor zeta)⁻¹ ^ Q = policyFactor zeta ^ (-(Q : ℤ)) := by
    simp [zpow_neg, zpow_natCast]
  rw [hinv]
  calc
    policyFactor zeta ^ (-(Q : ℤ)) *
        (1 + (policyFactor zeta - 1) / hdepth Q) ^ Q ≤
      policyFactor zeta ^ (-(Q : ℤ)) * Real.exp (policyFactor zeta - 1) :=
        mul_le_mul_of_nonneg_left hpow (zpow_nonneg (le_of_lt hLpos) _)
    _ = Real.exp (policyFactor zeta - 1) * policyFactor zeta ^ (-(Q : ℤ)) := mul_comm _ _

-- @node: resetRatio_lt_one
/-- For [the mixing scale](hyp:t0) and [the mixing scale assumption](hyp:ht0), this establishes
[the reset ratio strict bound one result](goal). -/
lemma resetRatio_lt_one (t0 : ℝ) (ht0 : 0 < t0) : resetRatio t0 < 1 := by
  have hα : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < 1 / t0 := by positivity
    linarith
  have hαpos : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have hden : 0 < 1 - sparseSignal t0 := by
    unfold sparseSignal
    linarith
  unfold resetRatio
  rw [div_lt_iff₀ hden]
  unfold sparseSignal
  linarith

/-- The weighted geometric series controls every finite-depth filter correction. For
[the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0), and
[the hidden-depth scale](hyp:Q), this establishes [the reset ratio depth bound result](goal). -/
-- @node: resetRatio_depth_bound
lemma resetRatio_depth_bound (t0 : ℝ) (ht0 : 0 < t0) (Q : Nat) :
    (Q : ℝ) * resetRatio t0 ^ Q ≤
      resetRatio t0 / (1 - resetRatio t0) ^ 2 := by
  have hrpos : 0 ≤ resetRatio t0 := by
    unfold resetRatio sparseSignal mixingAlpha
    have hα : Real.exp (-(1 / t0)) ≤ 1 :=
      (Real.exp_le_one_iff).2 (neg_nonpos.mpr (by positivity))
    have hden : 0 < 1 - (1 - Real.exp (-(1 / t0))) / 4 := by
      have h := Real.exp_pos (-(1 / t0))
      linarith
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hden)
  have hrlt := resetRatio_lt_one t0 ht0
  have hnorm : ‖resetRatio t0‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg hrpos] using hrlt
  have hs := (hasSum_coe_mul_geometric_of_norm_lt_one (𝕜 := ℝ) hnorm)
  have hterm : (Q : ℝ) * resetRatio t0 ^ Q ≤
      ∑' n : Nat, (n : ℝ) * resetRatio t0 ^ n := by
    simpa using hs.summable.sum_le_tsum {Q}
      (fun n _ ↦ mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hrpos _))
  simpa only [hs.tsum_eq] using hterm

/-- Each Bayes denominator in the hidden-depth filter is bounded by an exponential with a
uniform denominator. This is step (14) of the roadmap. For [the c](hyp:c), [the z](hyp:z),
[the c0 assumption](hyp:hc0), [the c1 assumption](hyp:hc1), [the z0 assumption](hyp:hz0), and
[the z1 assumption](hyp:hz1), this establishes [the filter factor bound exp result](goal). -/
-- @node: filter_factor_le_exp
lemma filter_factor_le_exp (c z : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    (1 - c * z)⁻¹ ≤ Real.exp (c * z / (1 - c)) := by
  have hcz0 : 0 ≤ c * z := mul_nonneg hc0 hz0
  have hcz1 : c * z ≤ c := by nlinarith
  have hden : 0 < 1 - c * z := by linarith
  have hcden : 0 < 1 - c := by linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  have hfrac : (1 - c * z)⁻¹ - 1 ≤ c * z / (1 - c) := by
    have hid : (1 - c * z)⁻¹ - 1 = c * z / (1 - c * z) := by
      field_simp
      ring
    rw [hid]
    exact div_le_div_of_nonneg_left hcz0 hcden (by linarith)
  calc
    (1 - c * z)⁻¹ = Real.exp (Real.log ((1 - c * z)⁻¹)) :=
      (Real.exp_log (inv_pos.mpr hden)).symm
    _ ≤ Real.exp (c * z / (1 - c)) := Real.exp_le_exp.mpr (hlog.trans hfrac)

/-- The finite-word version of the logarithmic filter estimate. For [the ι](hyp:ι),
[the state](hyp:s), [the z](hyp:z), [the c](hyp:c), [the c0 assumption](hyp:hc0),
[the c1 assumption](hyp:hc1), [the z0 assumption](hyp:hz0), and [the z1 assumption](hyp:hz1),
this establishes [the filter product bound exp sum result](goal). -/
-- @node: filter_product_le_exp_sum
lemma filter_product_le_exp_sum {ι : Type*} (s : Finset ι) (z : ι → ℝ)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1) :
    (∏ i ∈ s, (1 - c * z i)⁻¹) ≤
      Real.exp (c / (1 - c) * ∑ i ∈ s, z i) := by
  classical
  calc
    (∏ i ∈ s, (1 - c * z i)⁻¹) ≤
        ∏ i ∈ s, Real.exp (c * z i / (1 - c)) := by
      apply Finset.prod_le_prod
      · intro i hi
        apply inv_nonneg.mpr
        have hcz : c * z i ≤ c := by nlinarith [hz1 i hi]
        linarith
      · intro i hi
        exact filter_factor_le_exp c (z i) hc0 hc1 (hz0 i hi) (hz1 i hi)
    _ = Real.exp (c / (1 - c) * ∑ i ∈ s, z i) := by
      rw [← Real.exp_sum]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Once the coarse posterior estimate is known, every stationary or complete filter window has
the same multiplicative correction bound. For [the ι](hyp:ι), [the mixing scale](hyp:t0),
[the mixing scale assumption](hyp:ht0), [the hidden-depth scale](hyp:Q), [the state](hyp:s),
[the z](hyp:z), [the card assumption](hyp:hcard), [the z0 assumption](hyp:hz0),
[the z1 assumption](hyp:hz1), and [the zr assumption](hyp:hzr), this establishes
[the filter product bound constant result](goal). -/
-- @node: filter_product_le_constant
lemma filter_product_le_constant {ι : Type*} (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (s : Finset ι) (z : ι → ℝ) (hcard : s.card ≤ Q)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hzr : ∀ i ∈ s, z i ≤ resetRatio t0 ^ Q) :
    (∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹) ≤ filterConstant t0 := by
  have hαlo : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have hαhi : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < 1 / t0 := by positivity
    linarith
  have hc0 : 0 ≤ sparseSignal t0 := by
    unfold sparseSignal
    linarith
  have hc1 : sparseSignal t0 < 1 := by
    unfold sparseSignal
    linarith
  have hr0 : 0 ≤ resetRatio t0 := by
    unfold resetRatio
    exact div_nonneg (le_of_lt hαlo) (by unfold sparseSignal; linarith)
  have hsum : (∑ i ∈ s, z i) ≤ (Q : ℝ) * resetRatio t0 ^ Q := by
    calc
      (∑ i ∈ s, z i) ≤ ∑ _i ∈ s, resetRatio t0 ^ Q := by
        apply Finset.sum_le_sum
        intro i hi
        exact hzr i hi
      _ = (s.card : ℝ) * resetRatio t0 ^ Q := by simp
      _ ≤ (Q : ℝ) * resetRatio t0 ^ Q := by
        gcongr
  have hcoeff : 0 ≤ sparseSignal t0 / (1 - sparseSignal t0) :=
    div_nonneg hc0 (by linarith)
  have hdepth := resetRatio_depth_bound t0 ht0 Q
  have hexp : Real.exp (sparseSignal t0 / (1 - sparseSignal t0) *
      ∑ i ∈ s, z i) ≤ filterConstant t0 := by
    unfold filterConstant
    apply Real.exp_le_exp.mpr
    have hmain := mul_le_mul_of_nonneg_left (hsum.trans hdepth) hcoeff
    simpa only [div_mul_div_comm] using hmain
  exact (filter_product_le_exp_sum s z (sparseSignal t0) hc0 hc1 hz0 hz1).trans hexp

/-- The coarse depth-filter estimate (13), including stationary prefix windows. For
[the ι](hyp:ι), [the mixing scale](hyp:t0), [the mixing scale assumption](hyp:ht0),
[the hidden-depth scale](hyp:Q), [the state](hyp:s), [the z](hyp:z), [the z₀](hyp:z₀),
[the card assumption](hyp:hcard), [the z0 assumption](hyp:_hz0), [the z1 assumption](hyp:hz1),
and [the rec assumption](hyp:hrec), this establishes
[the filter recursion coarse bound result](goal). -/
-- @node: filter_recursion_coarse_bound
lemma filter_recursion_coarse_bound {ι : Type*} (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (s : Finset ι) (z : ι → ℝ) (z₀ : ℝ) (hcard : s.card ≤ Q)
    (_hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hrec : z₀ ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹) :
    z₀ ≤ resetRatio t0 ^ Q := by
  have hαpos : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have hαlt : mixingAlpha t0 < 1 := by
    unfold mixingAlpha
    apply Real.exp_lt_one_iff.mpr
    have h : 0 < 1 / t0 := by positivity
    linarith
  have hc0 : 0 ≤ sparseSignal t0 := by
    unfold sparseSignal
    linarith
  have hc1 : sparseSignal t0 < 1 := by
    unfold sparseSignal
    linarith
  have hden : 0 < 1 - sparseSignal t0 := by linarith
  have hbase : 1 ≤ (1 - sparseSignal t0)⁻¹ :=
    (one_le_inv₀ hden).2 (by linarith)
  have hprod : (∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹) ≤
      (1 - sparseSignal t0)⁻¹ ^ Q := by
    calc
      _ ≤ ∏ _i ∈ s, (1 - sparseSignal t0)⁻¹ := by
        apply Finset.prod_le_prod
        · intro i hi
          have hzi : sparseSignal t0 * z i ≤ sparseSignal t0 := by
            nlinarith [hz1 i hi]
          exact inv_nonneg.mpr (by linarith)
        · intro i hi
          have hzi : sparseSignal t0 * z i ≤ sparseSignal t0 := by
            nlinarith [hz1 i hi]
          exact (inv_le_inv₀ (by linarith : 0 < 1 - sparseSignal t0 * z i)
            hden).2 (by linarith)
      _ = (1 - sparseSignal t0)⁻¹ ^ s.card := by simp
      _ ≤ (1 - sparseSignal t0)⁻¹ ^ Q := pow_le_pow_right₀ hbase hcard
  calc
    z₀ ≤ mixingAlpha t0 ^ Q * (∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹) := hrec
    _ ≤ mixingAlpha t0 ^ Q * (1 - sparseSignal t0)⁻¹ ^ Q :=
      mul_le_mul_of_nonneg_left hprod (by unfold mixingAlpha; positivity)
    _ = resetRatio t0 ^ Q := by rw [← mul_pow]; rfl

/-- The uniform depth-filter estimate (15) follows from the finite-word recursion, without
exposing reset indicators. For [the ι](hyp:ι), [the mixing scale](hyp:t0),
[the mixing scale assumption](hyp:ht0), [the hidden-depth scale](hyp:Q), [the state](hyp:s),
[the z](hyp:z), [the z₀](hyp:z₀), [the card assumption](hyp:hcard),
[the z0 assumption](hyp:hz0), [the z1 assumption](hyp:hz1), [the zr assumption](hyp:hzr), and
[the rec assumption](hyp:hrec), this establishes
[the filter recursion uniform bound result](goal). -/
-- @node: filter_recursion_uniform_bound
lemma filter_recursion_uniform_bound {ι : Type*} (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (s : Finset ι) (z : ι → ℝ) (z₀ : ℝ) (hcard : s.card ≤ Q)
    (hz0 : ∀ i ∈ s, 0 ≤ z i) (hz1 : ∀ i ∈ s, z i ≤ 1)
    (hzr : ∀ i ∈ s, z i ≤ resetRatio t0 ^ Q)
    (hrec : z₀ ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹) :
    z₀ ≤ filterConstant t0 * mixingAlpha t0 ^ Q := by
  have hprod := filter_product_le_constant t0 ht0 Q s z hcard hz0 hz1 hzr
  calc
    z₀ ≤ mixingAlpha t0 ^ Q *
        ∏ i ∈ s, (1 - sparseSignal t0 * z i)⁻¹ := hrec
    _ ≤ mixingAlpha t0 ^ Q * filterConstant t0 :=
      mul_le_mul_of_nonneg_left hprod (by unfold mixingAlpha; positivity)
    _ = filterConstant t0 * mixingAlpha t0 ^ Q := mul_comm _ _

/-- A finite-word posterior recursion gives the uniform bound (15) at every epoch, including
incomplete windows at the stationary start. For [the ι](hyp:ι), [the mixing scale](hyp:t0),
[the mixing scale assumption](hyp:ht0), [the hidden-depth scale](hyp:Q), [the state](hyp:s),
[the z](hyp:z), [the card assumption](hyp:hcard), [the z0 assumption](hyp:hz0),
[the z1 assumption](hyp:hz1), [the rec assumption](hyp:hrec), and the epoch index, this
establishes [the filter recursion global bound result](goal). -/
-- @node: filter_recursion_global_bound
lemma filter_recursion_global_bound {ι : Type*} (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (s : ι → Finset ι) (z : ι → ℝ)
    (hcard : ∀ t, (s t).card ≤ Q)
    (hz0 : ∀ t, 0 ≤ z t) (hz1 : ∀ t, z t ≤ 1)
    (hrec : ∀ t, z t ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ s t, (1 - sparseSignal t0 * z i)⁻¹) :
    ∀ t, z t ≤ filterConstant t0 * mixingAlpha t0 ^ Q := by
  have hcoarse : ∀ t, z t ≤ resetRatio t0 ^ Q := by
    intro t
    exact filter_recursion_coarse_bound t0 ht0 Q (s t) z (z t) (hcard t)
      (fun i _ ↦ hz0 i) (fun i _ ↦ hz1 i) (hrec t)
  intro t
  exact filter_recursion_uniform_bound t0 ht0 Q (s t) z (z t) (hcard t)
    (fun i _ ↦ hz0 i) (fun i _ ↦ hz1 i) (fun i _ ↦ hcoarse i) (hrec t)

/-- The pointwise squared conditional reward mean in step (18), obtained from the
observed-prefix filter recursion. For [the ι](hyp:ι), [the mixing scale](hyp:t0),
[the mixing scale assumption](hyp:ht0), [the hidden-depth scale](hyp:Q), [the state](hyp:s),
[the z](hyp:z), [the action](hyp:a), [the ε](hyp:ε), [the card assumption](hyp:hcard),
[the z0 assumption](hyp:hz0), [the z1 assumption](hyp:hz1), [the rec assumption](hyp:hrec), and
[the epoch index](hyp:t), this establishes [the filter reward mean sq bound result](goal). -/
-- @node: filter_reward_mean_sq_bound
lemma filter_reward_mean_sq_bound {ι : Type*} (t0 : ℝ) (ht0 : 0 < t0)
    (Q : Nat) (s : ι → Finset ι) (z a : ι → ℝ) (ε : ℝ)
    (hcard : ∀ t, (s t).card ≤ Q)
    (hz0 : ∀ t, 0 ≤ z t) (hz1 : ∀ t, z t ≤ 1)
    (hrec : ∀ t, z t ≤ mixingAlpha t0 ^ Q *
      ∏ i ∈ s t, (1 - sparseSignal t0 * z i)⁻¹)
    (t : ι) :
    (sparseSignal t0 * ε * a t * z t) ^ 2 ≤
      (sparseSignal t0 * ε * a t *
        (filterConstant t0 * mixingAlpha t0 ^ Q)) ^ 2 := by
  have hz := filter_recursion_global_bound t0 ht0 Q s z hcard hz0 hz1 hrec t
  have hzsq : (z t) ^ 2 ≤ (filterConstant t0 * mixingAlpha t0 ^ Q) ^ 2 := by
    gcongr
    exact hz0 t
  calc
    (sparseSignal t0 * ε * a t * z t) ^ 2 =
        (sparseSignal t0 * ε * a t) ^ 2 * (z t) ^ 2 := by ring
    _ ≤ (sparseSignal t0 * ε * a t) ^ 2 *
        (filterConstant t0 * mixingAlpha t0 ^ Q) ^ 2 :=
          mul_le_mul_of_nonneg_left hzsq (sq_nonneg _)
    _ = (sparseSignal t0 * ε * a t *
          (filterConstant t0 * mixingAlpha t0 ^ Q)) ^ 2 := by ring

/-- The one-step KL cost of a Rademacher reward with conditional mean `m`. This is the
logarithmic estimate in step (17) of the observed-word proof. For [the model](hyp:m),
[the mlo assumption](hyp:hmlo), and [the mhi assumption](hyp:hmhi), this establishes
[the rademacher KL bound sq result](goal). -/
-- @node: rademacher_kl_le_sq
lemma rademacher_kl_le_sq (m : ℝ) (hmlo : -1 < m) (hmhi : m < 1) :
    (1 + m) / 2 * Real.log (1 + m) +
      (1 - m) / 2 * Real.log (1 - m) ≤ m ^ 2 := by
  have hp : 0 ≤ (1 + m) / 2 := by linarith
  have hn : 0 ≤ (1 - m) / 2 := by linarith
  have hlp : Real.log (1 + m) ≤ m := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + m)
    linarith
  have hln : Real.log (1 - m) ≤ -m := by
    have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - m)
    linarith
  have h₁ := mul_le_mul_of_nonneg_left hlp hp
  have h₂ := mul_le_mul_of_nonneg_left hln hn
  nlinarith

/-- Combine the conditional KL estimate with the retention-window moment bound. This is the
numerical substitution from (18)--(20). For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C),
[the policy-overlap scale assumption](hyp:hzeta), [the time horizon](hyp:T),
[the hidden-depth scale](hyp:Q), [the d](hyp:D), and [the d assumption](hyp:hD), this
establishes [the KL from retention window bound result](goal). -/
-- @node: kl_from_retention_window_bound
lemma kl_from_retention_window_bound (t0 zeta C : ℝ) (hzeta : 0 < zeta)
    (T Q : Nat) (D : ℝ)
    (hD : D ≤ sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
      filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) *
        (T : ℝ) * sparseRetentionProbability Q zeta ^ Q) :
    D ≤ klConstant t0 zeta * T * overlapRadius C ^ 2 *
      mixingAlpha t0 ^ (2 * Q) *
        policyFactor zeta ^ (-(Q : ℤ)) := by
  have hret := sparseRetentionProbability_pow_le Q zeta hzeta
  have hα : 0 < mixingAlpha t0 := by
    unfold mixingAlpha
    positivity
  have hcoef : 0 ≤ sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
      filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) * (T : ℝ) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_left hret hcoef
  calc
    D ≤ sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
        filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          (T : ℝ) * sparseRetentionProbability Q zeta ^ Q := hD
    _ ≤ sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 *
        filterConstant t0 ^ 2 * mixingAlpha t0 ^ (2 * Q) *
          (T : ℝ) *
            (Real.exp (policyFactor zeta - 1) *
              policyFactor zeta ^ (-(Q : ℤ))) := hmul
    _ = klConstant t0 zeta * T * overlapRadius C ^ 2 *
          mixingAlpha t0 ^ (2 * Q) *
            policyFactor zeta ^ (-(Q : ℤ)) := by
      unfold klConstant sparseEpsilon
      ring

/-- The latent-trajectory Bayes denominator equals the observed-word prefix mass used in the
likelihood chain, without revealing hidden states. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), and [the observed word](hyp:w), this establishes
[the observed prefix mass equality observed word prefix mass result](goal). -/
-- @node: observedPrefixMass_eq_observedWordPrefixMass
lemma observedPrefixMass_eq_observedWordPrefixMass {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
    observedPrefixMass hd t0 zeta C code v t w =
      observedWordPrefixMass (sparseObservedPMF hd t0 zeta C code v false) t.val w := by
  classical
  let F := sparseFinite (T := T) (Q := Q) hd t0 zeta C code v false
  have h := finiteRewardModel_observed_sum F
    (fun u ↦ if observedPrefixAgrees t u w then (1 : ℝ) else 0)
  simpa [F, observedPrefixMass, observedWordPrefixMass, sparseObservedPMF,
    observedPrefixAgrees, mul_ite] using h.symm

/-- Any positive-mass observed word has a positive Bayes denominator at every epoch, so
likelihood divisions are legitimate on the support. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the binary code](hyp:code), [the codeword index](hyp:v),
[the epoch index](hyp:t), [the observed word](hyp:w), and
[the observed word assumption](hyp:hw), this establishes
[the observed prefix mass positivity of word positivity result](goal). -/
-- @node: observedPrefixMass_pos_of_word_pos
lemma observedPrefixMass_pos_of_word_pos {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (code : Fin M → Fin d → Bool) (v : Fin M)
    (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2)
    (hw : 0 < (sparseObservedPMF hd t0 zeta C code v false w).toReal) :
    0 < observedPrefixMass hd t0 zeta C code v t w := by
  rw [observedPrefixMass_eq_observedWordPrefixMass]
  exact lt_of_lt_of_le hw (observedWordPrefixMass_ge_word _ t.val w)

/-- The finite-word Bayes recursion (12) implies the uniform posterior bound (15), with the same
window for early and late epochs. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the binary code](hyp:code), [the codeword index](hyp:v), [the observed word](hyp:w),
[the rec assumption](hyp:hrec), and the epoch index, this establishes
[the terminal posterior bound of window recursion result](goal). -/
-- @node: terminalPosterior_le_of_window_recursion
lemma terminalPosterior_le_of_window_recursion {T M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (w : FiniteObsView T (d * hdepth Q) 2)
    (hrec : ∀ t : Fin T, terminalPosterior hd t0 zeta C code v t w ≤
      mixingAlpha t0 ^ Q *
        ∏ r ∈ (Finset.univ : Finset (Fin T)).filter
          (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val),
          (1 - sparseSignal t0 * terminalPosterior hd t0 zeta C code v r w)⁻¹) :
    ∀ t : Fin T, terminalPosterior hd t0 zeta C code v t w ≤
      filterConstant t0 * mixingAlpha t0 ^ Q := by
  classical
  apply filter_recursion_global_bound t0 ht0 Q
    (fun t ↦ (Finset.univ : Finset (Fin T)).filter
      (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val))
    (fun t ↦ terminalPosterior hd t0 zeta C code v t w)
  · intro t
    rw [retention_window_card Q t]
    exact min_le_left _ _
  · intro t
    exact (terminalPosterior_mem_unitInterval hd t0 zeta C code v t w).1
  · intro t
    exact (terminalPosterior_mem_unitInterval hd t0 zeta C code v t w).2
  · exact hrec

/-- Summing the actual observed-law moments covers all stationary-prefix and complete retention
windows without a depth-dependent loss. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code), and
[the codeword index](hyp:v), this establishes
[the sparse observed total retention second moment bound result](goal). -/
-- @node: sparse_observed_total_retention_second_moment_le
lemma sparse_observed_total_retention_second_moment_le {T M d Q : Nat}
    (hd : 0 < d) (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (code : Fin M → Fin d → Bool) (v : Fin M) :
    (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        retentionFactor hd zeta code v t w ^ 2) ≤
      (T : ℝ) * sparseRetentionProbability Q zeta ^ Q := by
  calc
    _ ≤ ∑ _t : Fin T, sparseRetentionProbability Q zeta ^ Q := by
      apply Finset.sum_le_sum
      intro t _
      exact sparse_observed_retention_second_moment_le hd t0 zeta C
        ht0 hzeta hC code v t
    _ = _ := by simp

/-- Once the observed-prefix Bayes recursion is established, the actual alternative-law
expectation of the squared expression in (8) satisfies (18)--(19). No likelihood identity is
presumed by this moment lemma. For [the time horizon](hyp:T),
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), and [the rec assumption](hyp:hrec), this establishes
[the sparse observed reward mean square sum bound result](goal). -/
-- @node: sparse_observed_reward_mean_square_sum_le
lemma sparse_observed_reward_mean_square_sum_le {T M d Q : Nat}
    (hd : 0 < d) (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta)
    (hC : 1 ≤ C) (code : Fin M → Fin d → Bool) (v : Fin M)
    (hrec : ∀ (w : FiniteObsView T (d * hdepth Q) 2) (t : Fin T),
      terminalPosterior hd t0 zeta C code v t w ≤ mixingAlpha t0 ^ Q *
        ∏ r ∈ (Finset.univ : Finset (Fin T)).filter
          (fun r ↦ t.val - min Q t.val ≤ r.val ∧ r.val < t.val),
          (1 - sparseSignal t0 * terminalPosterior hd t0 zeta C code v r w)⁻¹) :
    (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
      (sparseObservedPMF hd t0 zeta C code v false w).toReal *
        (sparseSignal t0 * sparseEpsilon C * retentionFactor hd zeta code v t w *
          terminalPosterior hd t0 zeta C code v t w) ^ 2) ≤
      sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
        mixingAlpha t0 ^ (2 * Q) * T * sparseRetentionProbability Q zeta ^ Q := by
  classical
  let A := sparseSignal t0 ^ 2 * sparseEpsilon C ^ 2 * filterConstant t0 ^ 2 *
    mixingAlpha t0 ^ (2 * Q)
  have hA : 0 ≤ A := by dsimp [A]; unfold mixingAlpha; positivity
  have hpoint (t : Fin T) (w : FiniteObsView T (d * hdepth Q) 2) :
      (sparseSignal t0 * sparseEpsilon C * retentionFactor hd zeta code v t w *
        terminalPosterior hd t0 zeta C code v t w) ^ 2 ≤
      A * retentionFactor hd zeta code v t w ^ 2 := by
    have hz := terminalPosterior_le_of_window_recursion hd t0 zeta C ht0
      code v w (hrec w) t
    have hzsq : terminalPosterior hd t0 zeta C code v t w ^ 2 ≤
        (filterConstant t0 * mixingAlpha t0 ^ Q) ^ 2 := by
      gcongr
      exact (terminalPosterior_mem_unitInterval hd t0 zeta C code v t w).1
    have hmul := mul_le_mul_of_nonneg_left hzsq
      (sq_nonneg (sparseSignal t0 * sparseEpsilon C * retentionFactor hd zeta code v t w))
    have hpow : mixingAlpha t0 ^ (2 * Q) = (mixingAlpha t0 ^ Q) ^ 2 := by
      rw [mul_comm 2 Q, pow_mul]
    dsimp [A]
    rw [hpow]
    nlinarith only [hmul]
  calc
    _ ≤ ∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          (A * retentionFactor hd zeta code v t w ^ 2) := by
      apply Finset.sum_le_sum
      intro t _
      apply Finset.sum_le_sum
      intro w _
      exact mul_le_mul_of_nonneg_left (hpoint t w) ENNReal.toReal_nonneg
    _ = A * (∑ t : Fin T, ∑ w : FiniteObsView T (d * hdepth Q) 2,
        (sparseObservedPMF hd t0 zeta C code v false w).toReal *
          retentionFactor hd zeta code v t w ^ 2) := by
      simp_rw [← mul_assoc, mul_comm _ A, mul_assoc]
      simp only [Finset.mul_sum]
    _ ≤ A * ((T : ℝ) * sparseRetentionProbability Q zeta ^ Q) :=
      mul_le_mul_of_nonneg_left
        (sparse_observed_total_retention_second_moment_le hd t0 zeta C
          ht0 hzeta hC code v) hA
    _ = _ := by dsimp [A]; ring

/-- Applying the analytic bootstrap to the actual recursive observed filter proves (15) for
arbitrary words, including every stationary initial window. For
[the candidate-policy count](hyp:M), [the code dimension](hyp:d),
[the hidden-depth scale](hyp:Q), [the code dimension assumption](hyp:hd),
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the latent-overlap radius](hyp:C), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta),
[the latent-overlap radius assumption](hyp:hC), [the binary code](hyp:code),
[the codeword index](hyp:v), [the observed state](hyp:x), [the action](hyp:a),
[the reward symbol](hyp:r), and [the sample size](hyp:n), this establishes
[the sparse hidden filter uniform bound result](goal). -/
-- @node: sparse_hidden_filter_uniform_bound
lemma sparse_hidden_filter_uniform_bound {M d Q : Nat} (hd : 0 < d)
    (t0 zeta C : ℝ) (ht0 : 0 < t0) (hzeta : 0 < zeta) (hC : 1 ≤ C)
    (code : Fin M → Fin d → Bool) (v : Fin M)
    (x : Nat → Fin (d * hdepth Q)) (a : Nat → Bool) (r : Nat → Fin 2)
    (n : Nat) :
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (Fin.last Q, u))) /
      (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h) ≤
        filterConstant t0 * mixingAlpha t0 ^ Q := by
  let z := fun n : Nat ↦
    (∑ u, sparseHiddenFilter hd t0 zeta C code v x a r n
      (depthSignEquiv Q (Fin.last Q, u))) /
      (∑ h, sparseHiddenFilter hd t0 zeta C code v x a r n h)
  apply filter_recursion_global_bound t0 ht0 Q
    (fun n ↦ Finset.Ico (n - min Q n) n) z
  · intro k
    rw [Nat.card_Ico]
    omega
  · intro k
    exact (sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
      ht0 hzeta hC k (Fin.last Q)).1
  · intro k
    exact (sparse_hidden_filter_depth_ratio_bounds hd t0 zeta C code v x a r
      ht0 hzeta hC k (Fin.last Q)).2
  · intro k
    exact sparse_hidden_filter_posterior_recursion_Ico hd t0 zeta C code v x a r
      ht0 hzeta hC k

end CausalSmith.Stat.PomdpPolicyclassRegret
