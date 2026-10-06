module
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ConditionalLikelihoodBounds
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.GeniePartition
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.GoodEvent
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.HiddenAllocationContraction
public import CausalSmith.Experimentation.EXP_ThinnedgraphAdditiveRiskFrontier_Research.Helpers.ReverseTest
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Uniform nonlocal original-record testing scale
-/

public section

open scoped BigOperators ENNReal
open MeasureTheory
namespace CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
attribute [local instance] Classical.propDecidable

/-- The nonlocal testing scale is positive and at most one.  [For the stated data and conditions](hyp:B,d,q,hB,hd), [the stated conclusion holds](goal). -/
-- @node: testingScale_pos_le_one
lemma testingScale_pos_le_one (B d : ℕ) (q : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d) :
    0 < testingScale B d q ∧ testingScale B d q ≤ 1 := by
  have hm : (0 : ℝ) < (B * d : ℕ) := by exact_mod_cast (show 0 < B * d by positivity)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  unfold testingScale
  split_ifs with hp
  · exact ⟨lt_min (by norm_num) (div_pos hd' (Real.sqrt_pos.2 (mul_pos hm hp))), min_le_left _ _⟩
  · norm_num

/-- The chosen testing amplitude is in the baseline channel's declared domain.  [For the stated data and conditions](hyp:B,d,q,h,hB,hd,hh,hsmall), [the stated conclusion holds](goal). -/
-- @node: testing_small_amplitude_mem
lemma testing_small_amplitude_mem (B d : ℕ) (q h : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hh : 0 ≤ h) (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q) :
    h ∈ Set.Icc 0 (1 / 4) := by
  have hs := testingScale_pos_le_one B d q hB hd
  have hku : (100 * Real.pi)⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 100 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  exact ⟨hh, hsmall.trans ((mul_le_of_le_one_right (by positivity) hs.2).trans hku)⟩

/-- The testing scale bounds the source-retention energy without dividing by zero.  [For the stated data and conditions](hyp:B,d,q,h,hB,hd,hq,hh,hsmall), [the stated conclusion holds](goal). -/
-- @node: testing_small_retention_energy
lemma testing_small_retention_energy (B d : ℕ) (q h : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc 0 1) (hh : 0 ≤ h)
    (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q) :
    h ^ 2 * (B * d : ℕ) * retentionP d q ≤ (100 * Real.pi)⁻¹ ^ 2 * (d : ℝ) ^ 2 := by
  have hp := retentionP_mem_Icc d q hq
  by_cases hpzero : retentionP d q = 0
  · simp only [hpzero, mul_zero]; positivity
  have hppos : 0 < retentionP d q := lt_of_le_of_ne hp.1 (Ne.symm hpzero)
  have hm : (0 : ℝ) < (B * d : ℕ) := by exact_mod_cast (show 0 < B * d by positivity)
  have hr : 0 < Real.sqrt ((B * d : ℕ) * retentionP d q) := Real.sqrt_pos.2 (mul_pos hm hppos)
  have hscale : testingScale B d q ≤ (d : ℝ) / Real.sqrt ((B * d : ℕ) * retentionP d q) := by
    rw [testingScale, if_pos hppos]
    exact min_le_right _ _
  have hmul : h * Real.sqrt ((B * d : ℕ) * retentionP d q) ≤ (100 * Real.pi)⁻¹ * d := by
    apply (le_div_iff₀ hr).mp
    exact hsmall.trans (by simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ (100 * Real.pi)⁻¹))
  have hsq := Real.sq_sqrt (le_of_lt (mul_pos hm hppos))
  have hsquares := mul_self_le_mul_self (by positivity : 0 ≤ h * Real.sqrt ((B * d : ℕ) * retentionP d q)) hmul
  nlinarith

/-- Walsh energy at the testing amplitude is small, both per row and after retention weighting.  [For the stated data and conditions](hyp:B,d,q,h,hB,hd,hq,hh,hsmall), [the stated conclusion holds](goal). -/
-- @node: testing_small_channel_energy
lemma testing_small_channel_energy (B d : ℕ) (q h : ℝ) (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hq : q ∈ Set.Icc 0 1) (hh : 0 ≤ h)
    (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q) :
    eta d h ≤ (3 / 2500 : ℝ) ∧ (B : ℝ) * retentionP d q * etaOne d h ≤ 3 / 2500 := by
  have hw := walsh_channel_energy d h hd (testing_small_amplitude_mem B d q h hB hd hh hsmall)
  have he := testing_small_retention_energy B d q h hB hd hq hh hsmall
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < d := by positivity
  have hp := retentionP_mem_Icc d q hq
  have hhu : h ≤ (100 * Real.pi)⁻¹ := hsmall.trans
    (mul_le_of_le_one_right (by positivity) (testingScale_pos_le_one B d q hB hd).2)
  have hsq := mul_self_le_mul_self hh hhu
  have hk : Real.pi ^ 2 * ((100 * Real.pi)⁻¹) ^ 2 = (1 / 10000 : ℝ) := by
    field_simp <;> ring
  have hrow : etaOne d h ≤ 3 / 2500 := by
    apply hw.2.2.2.2.trans
    apply (div_le_iff₀ hdpos).2
    have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 12 * Real.pi ^ 2)
    nlinarith only [hm, hk, hdreal]
  refine ⟨hw.2.2.2.1.trans hrow, ?_⟩
  have hweight := mul_le_mul_of_nonneg_left hw.2.2.2.2
    (mul_nonneg (Nat.cast_nonneg B) hp.1)
  have hid : (B : ℝ) * retentionP d q * (12 * Real.pi ^ 2 * h ^ 2 / d) =
      12 * Real.pi ^ 2 * (h ^ 2 * (B * d : ℕ) * retentionP d q) / (d : ℝ) ^ 2 := by
    push_cast
    field_simp <;> ring
  rw [hid] at hweight
  apply hweight.trans
  apply (div_le_iff₀ (sq_pos_of_pos hdpos)).2
  have hem := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 12 * Real.pi ^ 2)
  nlinarith only [hem, hk]

/-- The numerical exponential and geometric factors leave a chi-squared budget below one sixteenth.  [For the stated data and conditions](hyp:a,b,ha,hb,hau,hbu), [the stated conclusion holds](goal). -/
-- @node: testing_contraction_rhs_small
lemma testing_contraction_rhs_small (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hau : a ≤ 3 / 2500) (hbu : b ≤ 3 / 2500) :
    4 * Real.exp 1 * a < 1 ∧
      Real.exp (Real.exp 1 * b) / (1 - 4 * Real.exp 1 * a) - 1 ≤ 1 / 16 := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  have hden : 4 * Real.exp 1 * a < 1 / 50 := by
    nlinarith [mul_le_mul_of_nonneg_left hau hepos.le]
  have hexpArg : Real.exp 1 * b ≤ 1 / 100 := by
    nlinarith [mul_le_mul_of_nonneg_left hbu hepos.le]
  have hexp : Real.exp (Real.exp 1 * b) ≤ 51 / 50 := by
    apply (Real.exp_le_exp.mpr hexpArg).trans
    have h := Real.exp_bound_div_one_sub_of_interval
      (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 / 100 : ℝ) < 1)
    norm_num at h
    linarith
  refine ⟨by linarith, ?_⟩
  have hd : 0 < 1 - 4 * Real.exp 1 * a := by linarith
  have hquot : Real.exp (Real.exp 1 * b) / (1 - 4 * Real.exp 1 * a) ≤ 51 / 49 := by
    apply (div_le_iff₀ hd).2
    linarith
  linarith

/-- The hidden-allocation contraction theorem, with its numerical premise discharged by Walsh energy,
bounds the good-event chi-squared integral at the chosen amplitude.  [For the stated data and conditions](hyp:n,B,d,q,h,D,hn,hB,hd,hfit,hq,ha,hw,hi,hh,hsmall), [the stated conclusion holds](goal). -/
lemma testing_small_good_chiSq_bound (n B d : ℕ) (q h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D)
    (hh : 0 ≤ h) (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q) :
    (∫ H, Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
      (hiddenChiSq n B d D h) H ∂(retainedGraphMarginal n B d D)) ≤ 1 / 16 := by
  have he := testing_small_channel_energy B d q h hB hd hq hh hsmall
  have hetaNonneg := (eta_nonneg_le_etaOne d h).1
  have hone : 0 ≤ etaOne d h := hetaNonneg.trans (eta_nonneg_le_etaOne d h).2
  have hp := retentionP_mem_Icc d q hq
  have hc := testing_contraction_rhs_small (eta d h) ((B : ℝ) * retentionP d q * etaOne d h)
    hetaNonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg B) hp.1) hone) he.1 he.2
  rw [design_eq_thinnedDesign D q ha hw hi]
  have hcontract := hidden_allocation_contraction n B d h q (halfBernoulli (Fin n))
    hn hB hd hfit (testing_small_amplitude_mem B d q h hB hd hh hsmall) hq (thinnedDesign_assignment q hq) hc.1
  exact hcontract.trans (by simpa only [mul_assoc] using hc.2)

/-- A genie bound closes the high-retention regime of the testing proof.  [For the stated data and conditions](hyp:n,B,d,q,h,D,hB,hd,hfit,hq,ha,hw,hi,hh,hsmall,hp), [the stated conclusion holds](goal). -/
-- @node: testing_small_high_retention
lemma testing_small_high_retention (n B d : ℕ) (q h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D)
    (hh : 0 ≤ h) (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q)
    (hp : (1 / 2 : ℝ) ≤ retentionP d q) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤ 1 / 2 := by
  have hgenie := genie_partition_tv_bound n B d h q D hB hd hfit
    (testing_small_amplitude_mem B d q h hB hd hh hsmall) hq ha hw hi
  have he := testing_small_retention_energy B d q h hB hd hq hh hsmall
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ (B : ℝ) / d)
  have hnat : (B * d : ℕ) = (B : ℝ) * d := by push_cast; rfl
  rw [hnat] at he
  have henergy : h ^ 2 * ((B : ℝ) / d) ≤ 2 * (100 * Real.pi)⁻¹ ^ 2 := by
    have hbd : (B : ℝ) / d * (d : ℝ) ^ 2 = (B : ℝ) * d := by
      field_simp <;> ring
    have hhalf : h ^ 2 * ((B : ℝ) * d) / 2 ≤ h ^ 2 * ((B : ℝ) * d) * retentionP d q := by
      nlinarith [mul_nonneg (sq_nonneg h) (by positivity : 0 ≤ (B : ℝ) * d)]
    rw [← hbd] at he hhalf
    nlinarith [sq_pos_of_pos hdpos]
  have hk : Real.pi ^ 2 * ((100 * Real.pi)⁻¹) ^ 2 = (1 / 10000 : ℝ) := by
    field_simp <;> ring
  have hbound : 2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) ≤ 1 / 2 := by
    have he' := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ 4 * Real.pi ^ 2)
    have hid : (2 * Real.pi * h * Real.sqrt ((B : ℝ) / d)) ^ 2 =
        4 * Real.pi ^ 2 * (h ^ 2 * ((B : ℝ) / d)) := by
      rw [mul_pow, mul_pow, mul_pow, hroot]
      ring
    have hnum : 4 * Real.pi ^ 2 * (2 * (100 * Real.pi)⁻¹ ^ 2) = (8 / 10000 : ℝ) := by
      nlinarith only [hk]
    rw [← hid, hnum] at he'
    nlinarith only [he', sq_nonneg (2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) - 1 / 2)]
  exact hgenie.trans hbound

/-- The same genie bound closes every retention level with fewer than thirty-two sources.  [For the stated data and conditions](hyp:n,B,d,q,h,D,hB,hd,hfit,hq,ha,hw,hi,hh,hsmall,hm), [the stated conclusion holds](goal). -/
-- @node: testing_small_few_sources
lemma testing_small_few_sources (n B d : ℕ) (q h : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D)
    (hh : 0 ≤ h) (hsmall : h ≤ (100 * Real.pi)⁻¹ * testingScale B d q)
    (hm : B * d < 32) :
    Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h) ≤ 1 / 2 := by
  have hgenie := genie_partition_tv_bound n B d h q D hB hd hfit
    (testing_small_amplitude_mem B d q h hB hd hh hsmall) hq ha hw hi
  have hhu : h ≤ (100 * Real.pi)⁻¹ := hsmall.trans
    (mul_le_of_le_one_right (by positivity) (testingScale_pos_le_one B d q hB hd).2)
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hmreal : (B : ℝ) * d < 32 := by exact_mod_cast hm
  have hbd : (B : ℝ) / d ≤ 32 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < d)).2
    nlinarith [Nat.cast_nonneg (α := ℝ) B]
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ (B : ℝ) / d)
  have hsq := mul_self_le_mul_self hh hhu
  have hk : Real.pi ^ 2 * ((100 * Real.pi)⁻¹) ^ 2 = (1 / 10000 : ℝ) := by
    field_simp <;> ring
  have hb : h ^ 2 * ((B : ℝ) / d) ≤ 32 * (100 * Real.pi)⁻¹ ^ 2 :=
    (mul_le_mul_of_nonneg_left hbd (sq_nonneg h)).trans
      (by nlinarith)
  have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 4 * Real.pi ^ 2)
  have hbound : 2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) ≤ 1 / 2 := by
    have hid : (2 * Real.pi * h * Real.sqrt ((B : ℝ) / d)) ^ 2 =
        4 * Real.pi ^ 2 * (h ^ 2 * ((B : ℝ) / d)) := by
      rw [mul_pow, mul_pow, mul_pow, hroot]
      ring
    have hnum : 4 * Real.pi ^ 2 * (32 * (100 * Real.pi)⁻¹ ^ 2) = (128 / 10000 : ℝ) := by
      nlinarith only [hk]
    rw [← hid, hnum] at hb'
    nlinarith only [hb', sq_nonneg (2 * Real.pi * h * Real.sqrt ((B : ℝ) / d) - 1 / 2)]
  exact hgenie.trans hbound

/-- Above twice the unclipped testing scale, the reverse bound excludes an amplitude
from the set whose total variation is at most one half.  [For the stated data and conditions](hyp:B,d,q,TV,hB,hd,hreverse,h,hh,hTV), [the stated conclusion holds](goal). -/
-- @node: testing_radius_member_le
lemma testing_radius_member_le (B d : ℕ) (q : ℝ) (TV : ℝ → ℝ)
    (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hreverse : ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → 0 < retentionP d q →
      1 - 7 * (d : ℝ) ^ 2 / (8 * h ^ 2 * (B * d : ℕ) * retentionP d q) ≤ TV h)
    (h : ℝ) (hh : h ∈ Set.Icc 0 (1 / 4)) (hTV : TV h ≤ 1 / 2) :
    h ≤ 2 * testingScale B d q := by
  have hs := testingScale_pos_le_one B d q hB hd
  by_cases hsone : testingScale B d q = 1
  · rw [hsone]
    linarith [hh.2]
  · have hp : 0 < retentionP d q := by
      by_contra hp
      exact hsone (by simp [testingScale, hp])
    have hscale : testingScale B d q =
        (d : ℝ) / Real.sqrt ((B * d : ℕ) * retentionP d q) := by
      rw [testingScale, if_pos hp] at hsone ⊢
      exact min_eq_right (le_of_not_ge (fun hle => hsone (min_eq_left hle)))
    by_contra hle
    have hlarge : 2 * testingScale B d q < h := lt_of_not_ge hle
    have hhpos : 0 < h := lt_trans (mul_pos (by norm_num) hs.1) hlarge
    have hm : (0 : ℝ) < (B * d : ℕ) := by
      exact_mod_cast (show 0 < B * d by positivity)
    have hx : 0 < (B * d : ℕ) * retentionP d q := mul_pos hm hp
    have hr : 0 < Real.sqrt ((B * d : ℕ) * retentionP d q) := Real.sqrt_pos.2 hx
    have hsq := Real.sq_sqrt (le_of_lt hx)
    have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hmul : 2 * (d : ℝ) < h * Real.sqrt ((B * d : ℕ) * retentionP d q) := by
      rw [hscale, ← mul_div_assoc] at hlarge
      exact (div_lt_iff₀ hr).mp hlarge
    have henergy : 4 * (d : ℝ) ^ 2 < h ^ 2 * ((B * d : ℕ) * retentionP d q) := by
      nlinarith [sq_nonneg (h * Real.sqrt ((B * d : ℕ) * retentionP d q) - 2 * d)]
    have hden : 0 < 8 * h ^ 2 * (B * d : ℕ) * retentionP d q := by positivity
    have hfraction : 7 * (d : ℝ) ^ 2 /
        (8 * h ^ 2 * (B * d : ℕ) * retentionP d q) < 1 / 2 := by
      apply (div_lt_iff₀ hden).2
      nlinarith [sq_pos_of_pos hdpos]
    have hb := hreverse h hhpos hh.2 hp
    linarith

/-- Small-distance membership and the reverse bound give both endpoints of the testing radius;
no monotonicity of total variation in amplitude is required.  [For the stated data and conditions](hyp:B,d,q,TV,hB,hd,hsmall,hreverse), [the stated conclusion holds](goal). -/
-- @node: testing_radius_of_bounds
lemma testing_radius_of_bounds (B d : ℕ) (q : ℝ) (TV : ℝ → ℝ)
    (hB : 1 ≤ B) (hd : 1 ≤ d)
    (hsmall : ∀ h : ℝ, 0 ≤ h → h ≤ (100 * Real.pi)⁻¹ * testingScale B d q → TV h ≤ 1 / 2)
    (hreverse : ∀ h : ℝ, 0 < h → h ≤ 1 / 4 → 0 < retentionP d q →
      1 - 7 * (d : ℝ) ^ 2 / (8 * h ^ 2 * (B * d : ℕ) * retentionP d q) ≤ TV h) :
    (100 * Real.pi)⁻¹ * testingScale B d q ≤
      sSup {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2} ∧
    sSup {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2} ≤ 2 * testingScale B d q := by
  have hs := testingScale_pos_le_one B d q hB hd
  have hkpos : 0 < (100 * Real.pi)⁻¹ := by positivity
  have hku : (100 * Real.pi)⁻¹ ≤ (1 / 4 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ (by positivity : 0 < 100 * Real.pi)).2
    nlinarith [Real.pi_gt_three]
  have hapos : 0 ≤ (100 * Real.pi)⁻¹ * testingScale B d q :=
    mul_nonneg (le_of_lt hkpos) (le_of_lt hs.1)
  have hau : (100 * Real.pi)⁻¹ * testingScale B d q ≤ (1 / 4 : ℝ) :=
    (mul_le_of_le_one_right (le_of_lt hkpos) hs.2).trans hku
  have hmem : (100 * Real.pi)⁻¹ * testingScale B d q ∈
      {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2} :=
    ⟨⟨hapos, hau⟩, hsmall _ hapos le_rfl⟩
  constructor
  · exact le_csSup ⟨1 / 4, fun h hh => hh.1.2⟩ hmem
  · apply csSup_le ⟨_, hmem⟩
    intro h hh
    exact testing_radius_member_le B d q TV hB hd hreverse h hh.1 hh.2

/-- The all-degree complete-record testing bound, reverse bound, and two-sided testing radius.  [For the stated data and conditions](hyp:n,B,d,q,D,hn,hB,hd,hfit,hq,ha,hw,hi), [the stated conclusion holds](goal). -/
-- @node: thm:block-testing-scale
theorem block_testing_scale (n B d : ℕ) (q : ℝ)
    (D : Measure (Assign (Fin n) × Audit (Fin n)))
    (hn : 4 ≤ n) (hB : 1 ≤ B) (hd : 1 ≤ d) (hfit : 2 * (B * d) ≤ n) (hq : q ∈ Set.Icc 0 1)
    (ha : AssignmentLaw D) (hw : AuditLaw D q) (hi : DesignIndependent D) :
    let s := testingScale B d q
    let κ := (100 * Real.pi)⁻¹
    let TV := fun h => Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
      (blockMixtureLawOf n B d D false h)
    (∀ h : ℝ, 0 ≤ h → h ≤ κ * s → TV h ≤ 1 / 2) ∧
    (∀ h : ℝ, 0 < h → h ≤ 1 / 4 → 0 < retentionP d q →
      1 - 7 * (d : ℝ) ^ 2 / (8 * h ^ 2 * (B * d : ℕ) * retentionP d q) ≤ TV h) ∧
    (κ * s ≤ sSup {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2} ∧
      sSup {h : ℝ | h ∈ Set.Icc 0 (1 / 4) ∧ TV h ≤ 1 / 2} ≤ 2 * s) := by
  dsimp only
  have hsmall : ∀ h : ℝ, 0 ≤ h → h ≤ (100 * Real.pi)⁻¹ * testingScale B d q →
      Causalean.Stat.tvDist (blockMixtureLawOf n B d D true h)
        (blockMixtureLawOf n B d D false h) ≤ 1 / 2 := by
    intro h hh hhu
    by_cases hp : (1 / 2 : ℝ) ≤ retentionP d q
    · exact testing_small_high_retention n B d q h D hB hd hfit hq ha hw hi hh hhu hp
    by_cases hm : B * d < 32
    · exact testing_small_few_sources n B d q h D hB hd hfit hq ha hw hi hh hhu hm
    have htail := hidden_count_good_event_of_retention_half n B d q D hB hd hfit hq
      (le_of_lt (lt_of_not_ge hp)) (Nat.le_of_not_gt hm) ha hw hi
    have hchi := testing_small_good_chiSq_bound n B d q h D hn hB hd hfit hq ha hw hi hh hhu
    let := design_isProbabilityMeasure D q ha hw hi
    have htv := blockMixture_tvDist_good_event_chiSq_le n B d hd hfit D h
      {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
    have hcompl : {H : OffDiag (Fin n) → Bool |
        (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}ᶜ =
        {H | (undiscovered n B d H : ℝ) < (B * d : ℕ) / 4} := by
      ext H
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hcompl] at htv
    have hsqrt : Real.sqrt (∫ H,
        Set.indicator {H | (B * d : ℕ) / (4 : ℝ) ≤ undiscovered n B d H}
          (hiddenChiSq n B d D h) H ∂(retainedGraphMarginal n B d D)) ≤ 1 / 4 := by
      exact (Real.sqrt_le_sqrt hchi).trans_eq
        ((Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2 (by norm_num))
    exact htv.trans (by linarith only [htail, hsqrt])
  have hreverse := fun h hh hhu hp =>
    reverse_test_tv_bound n B d h q D hB hd hfit hh hhu hq hp ha hw hi
  exact ⟨hsmall, hreverse, testing_radius_of_bounds B d q _ hB hd hsmall hreverse⟩

end CausalSmith.Experimentation.ThinnedgraphAdditiveRiskFrontier
