module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.CopulaLegalityBasics

/-! Numerical separation from the centered second moment of the interpolated paired tent. -/
public section
noncomputable section
open MeasureTheory
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Finite squared-frame interpolation is continuous on the original design space. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: continuous_smoothedTent_design
@[fun_prop] lemma continuous_smoothedTent_design (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) :
    Continuous (fun x : unitInterval => smoothedTent K M σ x) := by
  unfold smoothedTent
  fun_prop

/-- The convex interpolation envelope bounds its design second moment by one. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: smoothedTent_second_moment_le_one
lemma smoothedTent_second_moment_le_one (K M : ℕ) (hK : 0 < K)
    (σ : Fin (M/2) → Bool) :
    (∫ x : unitInterval, (smoothedTent K M σ x)^2 ∂design) ≤ 1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  calc
    _ ≤ ∫ _x : unitInterval, (1 : ℝ) ∂design := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (integrable_const 1)
      apply Filter.Eventually.of_forall
      intro x
      have hb := abs_le.mp (smoothedTent_abs_le_one K M hK σ x)
      nlinarith [sq_nonneg (smoothedTent K M σ x)]
    _ = 1 := by simp

/-- The two prescribed amplitudes multiply to the claimed smoothness power. This statement assumes [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_amplitude_product
lemma legality_amplitude_product (v : Params) (K : ℕ) (hK : 0 < K) :
    legalityA v K * legalityB v K = (K : ℝ)^(-sumReg v)/4096 := by
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  unfold legalityA legalityB sumReg
  rw [div_mul_div_comm, ← Real.rpow_add hk]
  congr 1 <;> ring

/-- The effect multiplier lies between the two numerical smoothness scales. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_effect_amplitude_bounds
lemma legality_effect_amplitude_bounds (v : Params) (hv : v.Valid)
    (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℝ)^(-15 : ℤ)*(K : ℝ)^(-sumReg v) ≤
        2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2) ∧
    2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2) ≤
        (2 : ℝ)^(-14 : ℤ)*(K : ℝ)^(-sumReg v) := by
  have ha := (legality_tuning_bounds v hv K hK).1
  have hs : 0 ≤ legalityA v K^2 := sq_nonneg _
  have hs' : legalityA v K^2 ≤ 1/256 := by nlinarith [ha.1, ha.2]
  have hd : 0 < 1-legalityA v K^2 := by linarith
  have hp := legality_amplitude_product v K (by omega)
  have he : 2*legalityA v K*legalityB v K*kappa0 =
      (K : ℝ)^(-sumReg v)/32768 := by
    calc
      _ = 2*(legalityA v K*legalityB v K)*kappa0 := by ring
      _ = _ := by rw [hp]; norm_num [kappa0]; ring
  rw [he]
  norm_num
  have ht : 0 ≤ (K : ℝ)^(-sumReg v) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  constructor
  · apply (le_div_iff₀ hd).mpr
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    nlinarith

/-- The upper separation scale is strictly below the public distance cap. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: legality_separation_scale_lt_d0
lemma legality_separation_scale_lt_d0 (v : Params) (hv : v.Valid)
    (K : ℕ) (hK : 1 ≤ K) :
    (2 : ℝ)^(-14 : ℤ)*(K : ℝ)^(-sumReg v) < d0 := by
  have hs : 0 < sumReg v := by unfold sumReg; linarith [hv.2.1.1, hv.2.2.1.1]
  have hk : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hp := Real.rpow_le_one_of_one_le_of_nonpos hk (neg_nonpos.mpr hs.le)
  have hroot : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hd : (1 : ℝ)/16384 < d0 := by
    unfold d0
    apply (lt_div_iff₀ (by positivity : 0 < 8*Real.sqrt 2)).mpr
    nlinarith
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hp (by positivity)) (by norm_num at hd ⊢; exact hd)

/-- A centered interpolated effect has distance equal to its amplitude times its root second moment. This statement assumes [the hA condition](hyp:hA), [the hτ condition](hyp:hτ), [the hmean condition](hyp:hmean). [This is the stated conclusion](goal). -/
-- @node: hetDist_of_centered_smoothed_effect
lemma hetDist_of_centered_smoothed_effect (law : ObservedLaw) (K M : ℕ)
    (σ : Fin (M/2) → Bool) (A : ℝ) (hA : 0 ≤ A)
    (hτ : ∀ x : unitInterval, law.tau x = -A*smoothedTent K M σ x)
    (hmean : (∫ x : unitInterval, smoothedTent K M σ x ∂design) = 0) :
    meanTau law = 0 ∧ hetDist law =
      A*Real.sqrt (∫ x : unitInterval, (smoothedTent K M σ x)^2 ∂design) := by
  have hm : meanTau law = 0 := by
    unfold meanTau
    simp_rw [hτ]
    rw [integral_const_mul, hmean, mul_zero]
  refine ⟨hm, ?_⟩
  unfold hetDist
  rw [hm]
  simp_rw [hτ, sub_zero, mul_pow, neg_sq]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq hA]

/-- The roadmap's centered second-moment interval gives all claimed numerical distance bounds. This statement assumes [the hv condition](hyp:hv), [the hK condition](hyp:hK), [the hτ condition](hyp:hτ), [the hmean condition](hyp:hmean), [the hsecond condition](hyp:hsecond). [This is the stated conclusion](goal). -/
-- @node: legality_separation_of_moments
lemma legality_separation_of_moments (v : Params) (hv : v.Valid) (K M : ℕ)
    (hK : 1 ≤ K) (idx : CopulaIndex K M) (law : ObservedLaw)
    (hτ : ∀ x : unitInterval, law.tau x =
      -(2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2))*smoothedTent K M idx.1 x)
    (hmean : (∫ x : unitInterval, smoothedTent K M idx.1 x ∂design) = 0)
    (hsecond : (1 : ℝ)/16 ≤ (∫ x : unitInterval, (smoothedTent K M idx.1 x)^2 ∂design) ∧
      (∫ x : unitInterval, (smoothedTent K M idx.1 x)^2 ∂design) ≤ 1) :
    CopulaEffectConclusion v K M idx law := by
  let A := 2*legalityA v K*legalityB v K*kappa0/(1-legalityA v K^2)
  have hb := legality_effect_amplitude_bounds v hv K hK
  have hA : 0 ≤ A := le_trans (by positivity) hb.1
  obtain ⟨hm, hd⟩ := hetDist_of_centered_smoothed_effect law K M idx.1 A hA hτ hmean
  have hlo : (1 : ℝ)/4 ≤ Real.sqrt (∫ x : unitInterval, (smoothedTent K M idx.1 x)^2 ∂design) := by
    have hh := Real.sqrt_le_sqrt hsecond.1
    rw [show (1 : ℝ)/16 = (1/4)^2 by norm_num, Real.sqrt_sq (by norm_num)] at hh
    exact hh
  have hup : Real.sqrt (∫ x : unitInterval, (smoothedTent K M idx.1 x)^2 ∂design) ≤ 1 := by
    simpa using Real.sqrt_le_sqrt hsecond.2
  have hlower : (2 : ℝ)^(-17 : ℤ)*(K : ℝ)^(-sumReg v) ≤ hetDist law := by
    rw [hd]
    calc
      _ = ((2 : ℝ)^(-15 : ℤ)*(K : ℝ)^(-sumReg v))*(1/4) := by norm_num; ring
      _ ≤ A*Real.sqrt (∫ x : unitInterval, (smoothedTent K M idx.1 x)^2 ∂design) :=
        mul_le_mul hb.1 hlo (by norm_num) hA
  have hupper : hetDist law ≤ (2 : ℝ)^(-14 : ℤ)*(K : ℝ)^(-sumReg v) := by
    rw [hd]
    exact (mul_le_mul_of_nonneg_left hup hA).trans (by simpa using hb.2)
  exact ⟨hτ, hm, hlower, hupper, hupper.trans_lt (legality_separation_scale_lt_d0 v hv K hK)⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
