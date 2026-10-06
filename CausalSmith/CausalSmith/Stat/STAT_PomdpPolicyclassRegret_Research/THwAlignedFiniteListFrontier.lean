module
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TCommonKernelLower
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.Helpers.HwTuning
public import CausalSmith.Stat.STAT_PomdpPolicyclassRegret_Research.TObservableSelectorUpper

/-! # Hu–Wager-aligned broader-class finite-list frontier -/

public section

namespace CausalSmith.Stat.PomdpPolicyclassRegret

open CausalSmith.Stat.PomdpLatentOverlapMinimax
open MeasureTheory
open scoped BigOperators

/-- Stationary values in the broader HW class remain in the reward interval. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
and [the candidate index](hyp:j), this establishes
[the Hu–Wager policy value unit result](goal). -/
-- @node: hw_policyValue_unit
lemma hw_policyValue_unit {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m) (j : Fin M) :
    policyValue m j ∈ Set.Icc (0 : ℝ) 1 := by
  have hd := (hw_target_stationary t0 zeta m hClass j).1
  have hg := phiw_list_reward_regression_unit m (m.Mx.E j)
    (hClass.action_overlap j).1
  change (∑ s, listStationaryLaw m (m.Mx.E j) s *
    listRewardRegression m (m.Mx.E j) s) ∈ Set.Icc (0 : ℝ) 1
  constructor
  · exact Finset.sum_nonneg fun s _ ↦ mul_nonneg (hd.1 s) (hg s).1
  · calc
      _ ≤ ∑ s, listStationaryLaw m (m.Mx.E j) s * 1 :=
        Finset.sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left (hg s).2 (hd.1 s)
      _ = 1 := by simpa using hd.2

/-- The universal regret cap also applies without uniform stationary overlap. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the model](hyp:m), [the class assumption](hyp:hClass),
and [the candidate index](hyp:j), this establishes
[the Hu–Wager simple regret unit result](goal). -/
-- @node: hw_simpleRegret_unit
lemma hw_simpleRegret_unit {T M : Nat} (t0 zeta : ℝ)
    (m : ModelIndex T M) (hClass : HWPolicyListClass t0 zeta m) (j : Fin M) :
    simpleRegret m j ∈ Set.Icc (0 : ℝ) 1 := by
  let : Nonempty (Fin M) := ⟨j⟩
  obtain ⟨hj0, hj1⟩ := hw_policyValue_unit t0 zeta m hClass j
  have hsup : (⨆ i, policyValue m i) ≤ 1 :=
    ciSup_le fun i ↦ (hw_policyValue_unit t0 zeta m hClass i).2
  have hle := le_ciSup (Finite.bddAbove_range (policyValue m)) j
  unfold simpleRegret
  constructor <;> linarith

/-- Bounded measurable regret has a unit-interval expectation under every HW law. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the observable selector](hyp:sel), [the model](hyp:m),
and [the class assumption](hyp:hClass), this establishes
[the Hu–Wager expected regret unit result](goal). -/
-- @node: hw_expectedRegret_unit
lemma hw_expectedRegret_unit {T M : Nat} (t0 zeta : ℝ)
    (sel : ObservableSelector T M) (m : ModelIndex T M)
    (hClass : HWPolicyListClass t0 zeta m) :
    expectedRegret sel m ∈ Set.Icc (0 : ℝ) 1 := by
  let : MeasureTheory.IsProbabilityMeasure (obsLaw m.Mx.toRawB) := by
    unfold obsLaw
    have hobs : Measurable (@obsProj T m.nX m.nH) := by fun_prop
    exact MeasureTheory.Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hm : Measurable (fun w ↦ simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w)) := by
    first
    | fun_prop
    | exact (measurable_of_finite (simpleRegret m)).comp (sel.2 m.nX m.Mx.b m.Mx.E)
  have hi : MeasureTheory.Integrable
      (fun w ↦ simpleRegret m (sel.1 m.nX m.Mx.b m.Mx.E w))
      (obsLaw m.Mx.toRawB) :=
    MeasureTheory.Integrable.of_mem_Icc 0 1 hm.aemeasurable
      (Filter.Eventually.of_forall fun w ↦ hw_simpleRegret_unit t0 zeta m hClass _)
  constructor
  · exact MeasureTheory.integral_nonneg fun w ↦ (hw_simpleRegret_unit t0 zeta m hClass _).1
  · calc
      expectedRegret sel m ≤ ∫ _ : ObsView T m.nX, (1 : ℝ) ∂obsLaw m.Mx.toRawB :=
        MeasureTheory.integral_mono_ae hi (MeasureTheory.integrable_const 1)
          (Filter.Eventually.of_forall fun w ↦ (hw_simpleRegret_unit t0 zeta m hClass _).2)
      _ = 1 := by simp

/-- The same observable rules face a larger model class in the HW problem, as in (75). For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the latent-overlap radius](hyp:C), and
[the candidate-policy count assumption](hyp:hM), this establishes
[the minimax regret bound Hu–Wager minimax regret result](goal). -/
-- @node: minimaxRegret_le_hwMinimaxRegret
lemma minimaxRegret_le_hwMinimaxRegret (T M : Nat) (t0 zeta C : ℝ)
    (hM : 0 < M) :
    minimaxRegret T M t0 zeta C ≤ hwMinimaxRegret T M t0 zeta := by
  classical
  let : Nonempty (ObservableSelector T M) :=
    ⟨⟨fun _ _ _ _ ↦ ⟨0, hM⟩, fun _ _ _ ↦ measurable_const⟩⟩
  unfold minimaxRegret hwMinimaxRegret
  apply Causalean.Stat.minimaxValue_mono_class_of_nonneg
    (fun m ↦ ⟨m.1, m.2.toHW⟩)
  · intro sel m
    exact (hw_expectedRegret_unit t0 zeta sel m.1 m.2.toHW).1
  · intro sel m
    exact (hw_expectedRegret_unit t0 zeta sel m.1 m.2).1
  · intro sel
    refine ⟨1, ?_⟩
    rintro r ⟨m, rfl⟩
    exact (hw_expectedRegret_unit t0 zeta sel m.1 m.2).2
  · intro sel m
    exact le_rfl

/-- Equation (60) identifies the HW exponent with the stated hidden-memory exponent. For
[the mixing scale](hyp:t0) and [the policy-overlap scale](hyp:zeta), this establishes
[the Hu–Wager rate exponent half result](goal). -/
-- @node: hw_rateExponent_half
lemma hw_rateExponent_half (t0 zeta : ℝ) :
    rateExponent t0 zeta / 2 = 1 / (2 + t0 * zeta) := by
  unfold rateExponent
  ring

/-- At radius two the hidden-term coefficient is positive and at most one. For
[the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and [the policy-overlap scale assumption](hyp:hzeta),
this establishes [the Hu–Wager radius two coefficient unit result](goal). -/
-- @node: hw_radius_two_coefficient_unit
lemma hw_radius_two_coefficient_unit (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    0 < overlapRadius 2 ^ (1 - rateExponent t0 zeta) ∧
      overlapRadius 2 ^ (1 - rateExponent t0 zeta) ≤ 1 := by
  have hq : overlapRadius 2 = (1 / 2 : ℝ) := by norm_num [overlapRadius]
  have hβ : rateExponent t0 zeta ≤ 1 := by
    unfold rateExponent
    apply (div_le_one (by positivity : 0 < 2 + t0 * zeta)).mpr
    nlinarith [mul_pos ht0 hzeta]
  rw [hq]
  exact ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)⟩

/-- Equation (76): the fixed-radius frontier dominates the truncated HW coordinate. For
[the time horizon](hyp:T), [the candidate-policy count](hyp:M), [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0),
[the policy-overlap scale assumption](hyp:hzeta), [the time horizon assumption](hyp:hT), and
[the candidate-policy count assumption](hyp:hM), this establishes
[the Hu–Wager rate bound radius two frontier result](goal). -/
-- @node: hw_rate_le_radius_two_frontier
lemma hw_rate_le_radius_two_frontier (T M : Nat) (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) (hT : 1 ≤ T) (hM : 2 ≤ M) :
    overlapRadius 2 ^ (1 - rateExponent t0 zeta) *
        min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) ≤
      (regretFrontier T M t0 zeta 2 ht0 hzeta (by norm_num) (by omega) hM) := by
  obtain ⟨ha0, ha1⟩ := hw_radius_two_coefficient_unit t0 zeta ht0 hzeta
  unfold regretFrontier
  rw [mul_min_of_nonneg _ _ ha0.le, mul_one]
  apply min_le_min ha1
  exact le_add_of_nonneg_left (Real.sqrt_nonneg _)

/-- The HW lower half follows from the common-kernel converse at the fixed radius two. For
[the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the Hu–Wager common kernel lower result](goal). -/
-- @node: hw_common_kernel_lower
lemma hw_common_kernel_lower (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ (cHW : ℝ) (THW : Nat), 0 < cHW ∧
      ∀ (T M : Nat), THW ≤ T → 2 ≤ M →
        cHW * min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) ≤
          hwMinimaxRegret T M t0 zeta := by
  obtain ⟨cl, Tl, hcl, hl⟩ := common_kernel_lower t0 zeta ht0 hzeta
  obtain ⟨ha0, _⟩ := hw_radius_two_coefficient_unit t0 zeta ht0 hzeta
  refine ⟨cl * overlapRadius 2 ^ (1 - rateExponent t0 zeta), max 1 Tl,
    mul_pos hcl ha0, ?_⟩
  intro T M hT hM
  calc
    _ = cl * (overlapRadius 2 ^ (1 - rateExponent t0 zeta) *
        min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2))) := by ring
    _ ≤ cl * (regretFrontier T M t0 zeta 2 ht0 hzeta (by norm_num) (by omega) hM) :=
      mul_le_mul_of_nonneg_left (hw_rate_le_radius_two_frontier T M t0 zeta ht0 hzeta (by omega) hM) hcl.le
    _ ≤ minimaxRegret T M t0 zeta 2 := hl T M 2 hT hM (by norm_num)
    _ ≤ hwMinimaxRegret T M t0 zeta :=
      minimaxRegret_le_hwMinimaxRegret T M t0 zeta 2 (by omega)

/-- The actual observable conservative-depth selector attains the HW upper frontier. Large
blocks use (72); short blocks use the regret cap and (73). For [the mixing scale](hyp:t0),
[the policy-overlap scale](hyp:zeta), [the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the Hu–Wager observable selector upper result](goal). -/
-- @node: hw_observable_selector_upper
lemma hw_observable_selector_upper (t0 zeta : ℝ) (ht0 : 0 < t0)
    (hzeta : 0 < zeta) :
    ∃ (Ku : ℝ) (Tu : Nat), 0 < Ku ∧
      ∀ (T M : Nat), Tu ≤ T → (hM : 2 ≤ M) →
        Causalean.Stat.worstCaseRiskReal
          (fun (sel : ObservableSelector T M)
            (m : {m : ModelIndex T M // HWPolicyListClass t0 zeta m}) ↦
            expectedRegret sel m.1)
          (hwBlockSelector T M (by omega) t0 zeta) ≤
          Ku * min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) := by
  classical
  obtain ⟨K, n0, hK, hn0, hrate⟩ := hw_expectedRegret_block_rate t0 zeta ht0 hzeta
  let cB := 2 + 4 / Real.log 2
  let γ := rateExponent t0 zeta / 2
  let δ := min 1 ((1 / (cB * (n0 : ℝ))) ^ γ)
  let Ku := K * (2 * cB) + δ⁻¹ + 1
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hcB : 0 < cB := by dsimp [cB]; positivity
  have hn0R : (0 : ℝ) < n0 := by exact_mod_cast (by omega : 0 < n0)
  have hγ0 : 0 ≤ γ := by dsimp [γ, rateExponent]; positivity
  have hγ1 : γ ≤ 1 := by
    dsimp [γ, rateExponent]
    have hden : 0 < 2 + t0 * zeta := by positivity
    have hb : 2 / (2 + t0 * zeta) ≤ (1 : ℝ) := (div_le_one hden).mpr (by nlinarith [mul_pos ht0 hzeta])
    linarith
  have hH : 1 ≤ 2 * cB := by
    have : 0 ≤ 4 / Real.log (2 : ℝ) := by positivity
    dsimp [cB]
    linarith
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hKu : 0 < Ku := by dsimp [Ku]; positivity
  have hKlarge : K * (2 * cB) ≤ Ku := by
    have : 0 < δ⁻¹ := inv_pos.mpr hδ
    dsimp [Ku]
    linarith
  have hKsmall : δ⁻¹ ≤ Ku := by
    have : 0 < K * (2 * cB) := by positivity
    dsimp [Ku]
    linarith
  have hKu1 : 1 ≤ Ku := by
    have : 0 < K * (2 * cB) + δ⁻¹ := by positivity
    dsimp [Ku]
    linarith
  refine ⟨Ku, 1, hKu, ?_⟩
  intro T M hT hM
  have hTpos : 0 < T := by omega
  let u := Real.log (M : ℝ) / T
  let f := u ^ γ
  have hu : 0 ≤ u := by
    dsimp [u]
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))) (Nat.cast_nonneg T)
  have hf : 0 ≤ f := Real.rpow_nonneg hu _
  rcases isEmpty_or_nonempty {m : ModelIndex T M // HWPolicyListClass t0 zeta m} with h | h
  · letI := h
    rw [Causalean.Stat.worstCaseRisk_of_isEmpty_class]
    exact mul_nonneg hKu.le (le_min (by norm_num) hf)
  · letI := h
    apply Causalean.Stat.worstCaseRisk_le
    intro m
    have hunit := (hw_expectedRegret_unit t0 zeta
      (hwBlockSelector T M (by omega) t0 zeta) m.1 m.2).2
    change expectedRegret _ m.1 ≤ Ku * min 1 f
    by_cases hf1 : 1 ≤ f
    · rw [min_eq_left hf1]
      simpa only [mul_one] using hunit.trans hKu1
    · rw [min_eq_right (le_of_not_ge hf1)]
      by_cases hn : n0 ≤ blockLen T M
      · have hr := hrate m.1 m.2 hn
        have hinv := selector_inv_blockLen_le_list_coordinate T M hTpos hM (by omega)
        change 1 / (blockLen T M : ℝ) ≤ (2 * cB) * u at hinv
        have hp : (blockLen T M : ℝ) ^ (-γ) ≤ (2 * cB) * f := by
          rw [Real.rpow_neg_eq_inv_rpow, ← one_div]
          calc
            _ ≤ ((2 * cB) * u) ^ γ := Real.rpow_le_rpow (by positivity) hinv hγ0
            _ = (2 * cB) ^ γ * u ^ γ := Real.mul_rpow (by positivity) hu
            _ ≤ (2 * cB) * f := mul_le_mul_of_nonneg_right
              (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hH hγ1) hf
        calc
          _ ≤ _ := hr
          _ ≤ K * ((2 * cB) * f) := mul_le_mul_of_nonneg_left hp hK.le
          _ = (K * (2 * cB)) * f := by ring
          _ ≤ Ku * f := mul_le_mul_of_nonneg_right hKlarge hf
      · have hlower := selector_small_block_coordinate_lower T M n0 hTpos hM
          (by omega) (by omega)
        change 1 / (cB * (n0 : ℝ)) ≤ u at hlower
        have hδf : δ ≤ f := (min_le_right _ _).trans
          (Real.rpow_le_rpow (by positivity) hlower hγ0)
        have hone : 1 ≤ δ⁻¹ * f := by
          have hh := mul_le_mul_of_nonneg_left hδf (inv_nonneg.mpr hδ.le)
          simpa only [inv_mul_cancel₀ hδ.ne'] using hh
        exact hunit.trans (hone.trans (mul_le_mul_of_nonneg_right hKsmall hf))

-- @node: thm:hw-aligned-finite-list-frontier
/-- For [the mixing scale](hyp:t0), [the policy-overlap scale](hyp:zeta),
[the mixing scale assumption](hyp:ht0), and
[the policy-overlap scale assumption](hyp:hzeta), this establishes
[the Hu–Wager aligned finite list frontier result](goal). -/
theorem hw_aligned_finite_list_frontier (t0 zeta : ℝ)
    (ht0 : 0 < t0) (hzeta : 0 < zeta) :
    ∃ (cHW KHW : ℝ) (THW : Nat), 0 < cHW ∧ cHW ≤ KHW ∧
      rateExponent t0 zeta / 2 = 1 / (2 + t0 * zeta) ∧
      ∀ (T M : Nat) (hT : THW ≤ T) (hM : 2 ≤ M),
        cHW * min 1 ((Real.log (M : ℝ) / T) ^
          (rateExponent t0 zeta / 2)) ≤
          hwMinimaxRegret T M t0 zeta ∧
        hwMinimaxRegret T M t0 zeta ≤
          KHW * min 1 ((Real.log (M : ℝ) / T) ^
            (rateExponent t0 zeta / 2)) ∧
        Causalean.Stat.worstCaseRiskReal
          (fun (sel : ObservableSelector T M)
            (m : {m : ModelIndex T M // HWPolicyListClass t0 zeta m}) ↦
            expectedRegret sel m.1)
          (hwBlockSelector T M (by omega) t0 zeta) ≤
          KHW * min 1 ((Real.log (M : ℝ) / T) ^
            (rateExponent t0 zeta / 2)) := by
  -- Assemble the conservative selector upper bound and the fixed-radius converse.
  have hu : ∃ (Ku : ℝ) (Tu : Nat), 0 < Ku ∧
      ∀ (T M : Nat), Tu ≤ T → (hM : 2 ≤ M) →
        Causalean.Stat.worstCaseRiskReal
          (fun (sel : ObservableSelector T M)
            (m : {m : ModelIndex T M // HWPolicyListClass t0 zeta m}) ↦
            expectedRegret sel m.1)
          (hwBlockSelector T M (by omega) t0 zeta) ≤
          Ku * min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) := by
    exact hw_observable_selector_upper t0 zeta ht0 hzeta
  obtain ⟨Ku, Tu, hKu, hu⟩ := hu
  obtain ⟨cl, Tl, hcl, hl⟩ := hw_common_kernel_lower t0 zeta ht0 hzeta
  refine ⟨cl, max Ku cl, max Tu Tl, hcl, le_max_right _ _,
    hw_rateExponent_half t0 zeta, ?_⟩
  intro T M hT hM
  have hrate : 0 ≤ min 1 ((Real.log (M : ℝ) / T) ^ (rateExponent t0 zeta / 2)) := by
    apply le_min (by norm_num)
    apply Real.rpow_nonneg
    apply div_nonneg
    · exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ M))
    · positivity
  have hsel := hu T M (le_trans (le_max_left _ _) hT) hM
  have hsel' := hsel.trans (mul_le_mul_of_nonneg_right (le_max_left Ku cl) hrate)
  refine ⟨hl T M (le_trans (le_max_right _ _) hT) hM, ?_, hsel'⟩
  calc
    hwMinimaxRegret T M t0 zeta ≤
        Causalean.Stat.worstCaseRiskReal
          (fun (sel : ObservableSelector T M)
            (m : {m : ModelIndex T M // HWPolicyListClass t0 zeta m}) ↦
            expectedRegret sel m.1)
          (hwBlockSelector T M (by omega) t0 zeta) :=
      by
        unfold hwMinimaxRegret
        apply Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg
        intro sel m
        exact (hw_expectedRegret_unit t0 zeta sel m.1 m.2).1
    _ ≤ _ := hsel'

end CausalSmith.Stat.PomdpPolicyclassRegret
