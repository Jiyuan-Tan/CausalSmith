module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerBanditCode
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.LowerSparseTesting
public import Causalean.Mathlib.InformationTheory.ProductKLLeCam
public import Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL.ChainRule

/-! # Information budget for the fully observed bandit experiment

Equation (44) follows from the conditional Bernoulli information bound and
independent replication of the common context-action law. These laws use Boolean
reward symbols; their identification with the POMDP observed law and membership
in the model class remain separate construction obligations.
-/

@[expose] public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open MeasureTheory InformationTheory
open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli
open Causalean.Mathlib.Probability.Kernel.ThreeBernoulli.SelectedLawKL
open CausalSmith.Stat.PomdpLatentOverlapMinimax

/-- The conditional reward probability in equation (41). -/
-- @node: lowerBanditRewardMean
noncomputable def lowerBanditRewardMean (gamma : ℝ) (bit action : Bool) : ℝ :=
  1 / 2 + gamma * (if bit then 1 else -1) * (if action then 1 else -1)

/-- The small reward amplitude keeps every conditional law in the quarter band. For
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0),
[the gamma1 assumption](hyp:hgamma1), [the bit](hyp:bit), and [the action](hyp:action), this
establishes [the lower bandit reward quarter band result](goal). -/
-- @node: lower_bandit_reward_quarter_band
lemma lower_bandit_reward_quarter_band (gamma : ℝ) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1 / 16) (bit action : Bool) :
    lowerBanditRewardMean gamma bit action ∈ Set.Icc (1 / 4 : ℝ) (1 - 1 / 4) := by
  cases bit <;> cases action <;> simp [lowerBanditRewardMean] <;>
    constructor <;> linarith

/-- The one-reward divergence from a fair reward is at most four amplitude squares. For
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0),
[the gamma1 assumption](hyp:hgamma1), [the bit](hyp:bit), and [the action](hyp:action), this
establishes [the lower bandit reward KL bound result](goal). -/
-- @node: lower_bandit_reward_kl_le
lemma lower_bandit_reward_kl_le (gamma : ℝ) (hgamma0 : 0 ≤ gamma)
    (hgamma1 : gamma ≤ 1 / 16) (bit action : Bool) :
    bernoulliKL (lowerBanditRewardMean gamma bit action) (1 / 2) ≤ 4 * gamma ^ 2 := by
  have hb := lower_bandit_reward_quarter_band gamma hgamma0 hgamma1 bit action
  have h := Causalean.Mathlib.Analysis.bernoulli_kl_le_four_sq_sub_of_mem_quarter_band
    hb.1 (by linarith [hb.2]) (p := lowerBanditRewardMean gamma bit action)
    (q := 1 / 2) (by norm_num) (by norm_num)
  change bernoulliKL _ _ ≤ _ at h
  convert h using 1
  cases bit <;> cases action <;> simp [lowerBanditRewardMean] <;> ring

/-- A context, fair logging action, and the environment's conditional reward. -/
-- @node: lowerBanditObservationLaw
noncomputable def lowerBanditObservationLaw {d : Nat} (μ : Measure (Fin d))
    (word : Fin d → Bool) (gamma : ℝ) : Measure (SelectedCoord (Fin d)) :=
  selectedLaw μ (fun _ ↦ 1 / 2)
    (fun x ↦ lowerBanditRewardMean gamma (word x) false)
    (fun x ↦ lowerBanditRewardMean gamma (word x) true)

/-- The one-step experiment is a probability law, including the fair reference. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0), and
[the gamma1 assumption](hyp:hgamma1), this establishes
[the lower bandit observation probability result](goal). -/
-- @node: lower_bandit_observation_probability
lemma lower_bandit_observation_probability {d : Nat} (μ : Measure (Fin d))
    [IsProbabilityMeasure μ] (word : Fin d → Bool) (gamma : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1 / 16) :
    IsProbabilityMeasure (lowerBanditObservationLaw μ word gamma) := by
  apply selectedLaw_probability
  · fun_prop
  · fun_prop
  · fun_prop
  · intro x; norm_num
  · intro x
    exact lower_bandit_reward_prob_unit gamma hgamma0 hgamma1 (word x) false
  · intro x
    exact lower_bandit_reward_prob_unit gamma hgamma0 hgamma1 (word x) true

/-- Fair reference rewards dominate the alternative, with integrable log ratio. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0), and
[the gamma1 assumption](hyp:hgamma1), this establishes
[the lower bandit observation KL regular result](goal). -/
-- @node: lower_bandit_observation_kl_regular
lemma lower_bandit_observation_kl_regular {d : Nat} (μ : Measure (Fin d))
    [IsProbabilityMeasure μ] (word : Fin d → Bool) (gamma : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1 / 16) :
    lowerBanditObservationLaw μ word gamma ≪ lowerBanditObservationLaw μ word 0 ∧
      Integrable (llr (lowerBanditObservationLaw μ word gamma)
        (lowerBanditObservationLaw μ word 0)) (lowerBanditObservationLaw μ word gamma) := by
  have hhalf : ∀ x : Fin d, (1 / 2 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 - 1 / 4) := by
    intro x; norm_num
  have hq (a : Bool) := fun x : Fin d ↦
    lower_bandit_reward_quarter_band gamma hgamma0 hgamma1 (word x) a
  have href (a : Bool) := fun x : Fin d ↦
    lower_bandit_reward_quarter_band 0 (by norm_num) (by norm_num) (word x) a
  dsimp only [lowerBanditObservationLaw]
  constructor
  · apply selectedLaw_ac (η := 1 / 4) μ
    all_goals solve | fun_prop | norm_num | exact hhalf | exact hq false |
      exact hq true | exact href false | exact href true
  · apply selectedLaw_llr_integrable (η := 1 / 4) μ
    all_goals solve | fun_prop | norm_num | exact hhalf | exact hq false |
      exact hq true | exact href false | exact href true

/-- Averaging the two action-conditional costs proves the one-step KL bound. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0), and
[the gamma1 assumption](hyp:hgamma1), this establishes
[the lower bandit observation KL bound result](goal). -/
-- @node: lower_bandit_observation_kl_le
lemma lower_bandit_observation_kl_le {d : Nat} (μ : Measure (Fin d))
    [IsProbabilityMeasure μ] (word : Fin d → Bool) (gamma : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1 / 16) :
    (klDiv (lowerBanditObservationLaw μ word gamma)
      (lowerBanditObservationLaw μ word 0)).toReal ≤ 4 * gamma ^ 2 := by
  have hhalf : ∀ x : Fin d, (1 / 2 : ℝ) ∈ Set.Icc (1 / 4 : ℝ) (1 - 1 / 4) := by
    intro x; norm_num
  have hq (a : Bool) := fun x : Fin d ↦
    lower_bandit_reward_quarter_band gamma hgamma0 hgamma1 (word x) a
  have href (a : Bool) := fun x : Fin d ↦
    lower_bandit_reward_quarter_band 0 (by norm_num) (by norm_num) (word x) a
  rw [lowerBanditObservationLaw, lowerBanditObservationLaw,
    selectedLaw_klDiv_toReal_eq_integral (η := 1 / 4) μ _ _ _ _ _
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by norm_num) hhalf (hq false) (hq true) (href false) (href true)]
  have hzero (bit a : Bool) : lowerBanditRewardMean 0 bit a = 1 / 2 := by
    simp [lowerBanditRewardMean]
  simp_rw [hzero]
  calc
    _ ≤ ∫ _x : Fin d, 4 * gamma ^ 2 ∂μ := by
      apply integral_mono Integrable.of_finite Integrable.of_finite
      intro x
      have h0 := lower_bandit_reward_kl_le gamma hgamma0 hgamma1 (word x) false
      have h1 := lower_bandit_reward_kl_le gamma hgamma0 hgamma1 (word x) true
      linarith
    _ = _ := by simp

/-- Independent replication gives the actual product-law information bound in (44). Finiteness
is retained explicitly before converting the KL divergence to reals. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the word](hyp:word),
[the rate parameter](hyp:gamma), [the gamma0 assumption](hyp:hgamma0),
[the gamma1 assumption](hyp:hgamma1), and [the time horizon](hyp:T), this establishes
[the lower bandit product KL bound result](goal). -/
-- @node: lower_bandit_product_kl_le
lemma lower_bandit_product_kl_le {d : Nat} (μ : Measure (Fin d))
    [IsProbabilityMeasure μ] (word : Fin d → Bool) (gamma : ℝ)
    (hgamma0 : 0 ≤ gamma) (hgamma1 : gamma ≤ 1 / 16) (T : Nat) :
    klDiv (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word gamma))
      (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word 0)) ≠ ⊤ ∧
    (klDiv (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word gamma))
      (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word 0))).toReal ≤
        4 * T * gamma ^ 2 := by
  letI := lower_bandit_observation_probability μ word gamma hgamma0 hgamma1
  letI := lower_bandit_observation_probability μ word 0 (by norm_num) (by norm_num)
  obtain ⟨hac, hint⟩ := lower_bandit_observation_kl_regular μ word gamma hgamma0 hgamma1
  have htensor := Causalean.Mathlib.InformationTheory.productKL_tensorization T
    (lowerBanditObservationLaw μ word gamma) (lowerBanditObservationLaw μ word 0) hac hint
  refine ⟨htensor.1, ?_⟩
  calc
    _ ≤ (T : ℝ) * (klDiv (lowerBanditObservationLaw μ word gamma)
        (lowerBanditObservationLaw μ word 0)).toReal := htensor.2.2
    _ ≤ (T : ℝ) * (4 * gamma ^ 2) := mul_le_mul_of_nonneg_left
      (lower_bandit_observation_kl_le μ word gamma hgamma0 hgamma1) (by positivity)
    _ = _ := by ring

/-- The fair reference does not depend on the environment codeword. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the codeword index](hyp:v), and
[the observed word](hyp:w), this establishes [the lower bandit reference equality result](goal). -/
-- @node: lower_bandit_reference_eq
lemma lower_bandit_reference_eq {d : Nat} (μ : Measure (Fin d))
    (v w : Fin d → Bool) :
    lowerBanditObservationLaw μ v 0 = lowerBanditObservationLaw μ w 0 := by
  simp [lowerBanditObservationLaw, lowerBanditRewardMean]

/-- The reward amplitude chosen in equation (41). -/
-- @node: lowerBanditRewardAmplitude
noncomputable def lowerBanditRewardAmplitude (T M : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) : ℝ :=
  (1 / 16) * min 1 (Real.sqrt ((listInformationRatio T M (by omega) hM)))

/-- The amplitude is positive at positive sample size and a nontrivial list. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the time horizon assumption](hyp:hT), and [the candidate-policy count assumption](hyp:hM), this
establishes [the lower bandit reward amplitude bounds result](goal). -/
-- @node: lower_bandit_reward_amplitude_bounds
lemma lower_bandit_reward_amplitude_bounds (T M : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) :
    0 < (lowerBanditRewardAmplitude T M (by omega) hM) ∧ (lowerBanditRewardAmplitude T M (by omega) hM) ≤ 1 / 16 := by
  have hu : 0 < (listInformationRatio T M (by omega) hM) := by
    unfold listInformationRatio
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < M by omega)))
      (by exact_mod_cast (show 0 < T by omega))
  unfold lowerBanditRewardAmplitude
  constructor
  · exact mul_pos (by norm_num) (lt_min (by norm_num) (Real.sqrt_pos.2 hu))
  · have h := min_le_left (1 : ℝ) (Real.sqrt ((listInformationRatio T M (by omega) hM)))
    linarith

/-- Squaring the capped amplitude yields the sharp reference KL budget in (44). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the time horizon assumption](hyp:hT), and [the candidate-policy count assumption](hyp:hM), this
establishes [the lower bandit reward amplitude budget result](goal). -/
-- @node: lower_bandit_reward_amplitude_budget
lemma lower_bandit_reward_amplitude_budget (T M : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) :
    4 * T * (lowerBanditRewardAmplitude T M (by omega) hM) ^ 2 ≤ Real.log (M : ℝ) / 64 := by
  have hlog : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hTR : 0 < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hu : 0 ≤ (listInformationRatio T M (by omega) hM) := div_nonneg hlog.le hTR.le
  have hs := Real.sq_sqrt hu
  have hmin0 : 0 ≤ min (1 : ℝ) (Real.sqrt ((listInformationRatio T M (by omega) hM))) := by positivity
  have hmin : min (1 : ℝ) (Real.sqrt ((listInformationRatio T M (by omega) hM))) ^ 2 ≤
      (listInformationRatio T M (by omega) hM) := by
    calc
      _ ≤ Real.sqrt ((listInformationRatio T M (by omega) hM)) ^ 2 :=
        pow_le_pow_left₀ hmin0 (min_le_right _ _) 2
      _ = _ := hs
  have hmul := mul_le_mul_of_nonneg_left hmin hTR.le
  have hcancel : (T : ℝ) * (listInformationRatio T M (by omega) hM) = Real.log (M : ℝ) := by
    unfold listInformationRatio
    field_simp
  rw [hcancel] at hmul
  unfold lowerBanditRewardAmplitude
  nlinarith

/-- Equation (44) for the independent observed bandit sample, with finite KL. For
[the code dimension](hyp:d), [the measure](hyp:μ), [the word](hyp:word),
[the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the time horizon assumption](hyp:hT), and [the candidate-policy count assumption](hyp:hM), this
establishes [the lower bandit product information budget result](goal). -/
-- @node: lower_bandit_product_information_budget
lemma lower_bandit_product_information_budget {d : Nat} (μ : Measure (Fin d))
    [IsProbabilityMeasure μ] (word : Fin d → Bool) (T M : Nat)
    (hT : 1 ≤ T) (hM : 2 ≤ M) :
    klDiv (Measure.pi (fun _ : Fin T ↦
      lowerBanditObservationLaw μ word ((lowerBanditRewardAmplitude T M (by omega) hM))))
      (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word 0)) ≠ ⊤ ∧
    (klDiv (Measure.pi (fun _ : Fin T ↦
      lowerBanditObservationLaw μ word ((lowerBanditRewardAmplitude T M (by omega) hM))))
      (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ word 0))).toReal ≤
        Real.log (M : ℝ) / 64 := by
  obtain ⟨hg0, hg1⟩ := lower_bandit_reward_amplitude_bounds T M hT hM
  obtain ⟨hfin, hkl⟩ := lower_bandit_product_kl_le μ word
    ((lowerBanditRewardAmplitude T M (by omega) hM)) hg0.le hg1 T
  exact ⟨hfin, hkl.trans (lower_bandit_reward_amplitude_budget T M hT hM)⟩

/-- The common fair reference turns the bandit information budget into the average testing error
floor used in equation (45). For [the code dimension](hyp:d),
[the measure](hyp:μ), [the time horizon](hyp:T), [the candidate-policy count](hyp:M),
[the time horizon assumption](hyp:hT), [the candidate-policy count assumption](hyp:hM),
[the binary code](hyp:code), [the ψ](hyp:ψ), and [the ψ assumption](hyp:hψ), this establishes
[the lower bandit product testing error result](goal). -/
-- @node: lower_bandit_product_testing_error
lemma lower_bandit_product_testing_error {d : Nat}
    (μ : Measure (Fin d)) [IsProbabilityMeasure μ]
    (T M : Nat) (hT : 1 ≤ T) (hM : 2 ≤ M) (code : Fin M → Fin d → Bool)
    (ψ : (Fin T → SelectedCoord (Fin d)) → Fin M) (hψ : Measurable ψ) :
    1 / 8 < (M : ℝ)⁻¹ * ∑ v : Fin M,
      (Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ (code v)
        ((lowerBanditRewardAmplitude T M (by omega) hM)))).real {w | ψ w ≠ v} := by
  let v0 : Fin M := ⟨0, by omega⟩
  let P := fun v : Fin M ↦ Measure.pi (fun _ : Fin T ↦
    lowerBanditObservationLaw μ (code v) ((lowerBanditRewardAmplitude T M (by omega) hM)))
  let P0 := Measure.pi (fun _ : Fin T ↦ lowerBanditObservationLaw μ (code v0) 0)
  obtain ⟨hg0, hg1⟩ := lower_bandit_reward_amplitude_bounds T M hT hM
  have hprob : ∀ v : Fin M, IsProbabilityMeasure (P v) := by
    intro v
    letI := lower_bandit_observation_probability μ (code v)
      ((lowerBanditRewardAmplitude T M (by omega) hM)) hg0.le hg1
    exact inferInstance
  have hprob0 : IsProbabilityMeasure P0 := by
    letI := lower_bandit_observation_probability μ (code v0) 0 (by norm_num) (by norm_num)
    exact inferInstance
  have hbudget (v : Fin M) : klDiv (P v) P0 ≠ ⊤ ∧
      (klDiv (P v) P0).toReal ≤ Real.log (M : ℝ) / 64 := by
    have h := lower_bandit_product_information_budget μ (code v) T M hT hM
    simpa only [P, P0, lower_bandit_reference_eq μ (code v) (code v0)] using h
  apply lower_test_error_of_reference_kl M hM P hprob P0 hprob0
    (fun v ↦ (hbudget v).1) _ ψ hψ
  intro v
  have hlog : 0 ≤ Real.log (M : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < M by omega))).le
  exact (hbudget v).2.trans (by linarith)

end CausalSmith.Stat.PomdpPolicyclassRegret
