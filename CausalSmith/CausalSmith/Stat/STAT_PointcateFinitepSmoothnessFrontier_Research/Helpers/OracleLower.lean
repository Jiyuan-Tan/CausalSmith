module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleConstruction
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerRegularity

/-! Model membership of the oracle experiment's two-atom triangular lower alternatives. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params) (n : ℕ)

/-- The triangular oracle bump has unit range and its bandwidth-scaled Lipschitz increment. -/
-- @node: oracle_lower_cutoff_bounds
lemma oracle_lower_cutoff_bounds (hd : κ.Valid ∧ 2 ≤ n) (x z : unitInterval) :
    let k := fun x : unitInterval => max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n)
    (0 ≤ k x ∧ k x ≤ 1) ∧ |k x-k z| ≤ |(x : ℝ)-z|/oracleLowerH κ n := by
  dsimp only
  have hh := (oracle_lower_scale_bounds κ n hd).1
  constructor
  · exact ⟨le_max_left _ _, max_le (by norm_num)
      (by linarith [div_nonneg (abs_nonneg ((x : ℝ)-1/2)) hh.le])⟩
  · have h := abs_max_sub_max_le_max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n)
      0 (1-|(z : ℝ)-1/2|/oracleLowerH κ n)
    simp only [sub_self, abs_zero, max_eq_right (abs_nonneg (_ : ℝ))] at h
    have hid : 1-|(x : ℝ)-1/2|/oracleLowerH κ n-(1-|(z : ℝ)-1/2|/oracleLowerH κ n) =
        -(|(x : ℝ)-1/2|-|(z : ℝ)-1/2|)/oracleLowerH κ n := by ring
    rw [hid, abs_div, abs_neg, abs_of_pos hh] at h
    apply h.trans
    apply div_le_div_of_nonneg_right _ hh.le
    simpa only [sub_sub_sub_cancel_right] using
      abs_abs_sub_abs_le_abs_sub ((x : ℝ)-1/2) ((z : ℝ)-1/2)

/-- The oracle effect amplitude is at most one quarter, including the smallest sample sizes. -/
-- @node: oracle_lower_effect_range
lemma oracle_lower_effect_range (hd : κ.Valid ∧ 2 ≤ n) (ε : Bool) (x : unitInterval) :
    0 ≤ oracleLowerEffect κ n ε x ∧ |oracleLowerEffect κ n ε x| ≤ 1/4 := by
  have hb := oracle_lower_scale_bounds κ n hd
  have ht : oracleLowerT κ n ≤ 1/4 := by
    have h := Real.rpow_le_one hb.1.le hb.2.1 hd.1.2.2.2.1.le
    unfold oracleLowerT
    linarith
  have hk := (oracle_lower_cutoff_bounds κ n hd x x).1
  cases ε
  · simp [oracleLowerEffect]
  · simp only [oracleLowerEffect, ↓reduceIte]
    have he := mul_nonneg hb.2.2.1.le hk.1
    exact ⟨he, by rw [abs_of_nonneg he]; nlinarith [mul_le_mul_of_nonneg_left hk.2 hb.2.2.1.le]⟩

/-- Range and Lipschitz interpolation give the oracle effect's stated Hölder ball. -/
-- @node: oracle_lower_effect_holder
lemma oracle_lower_effect_holder (hd : κ.Valid ∧ 2 ≤ n) (ε : Bool) :
    holderBall κ.γ (oracleLowerEffect κ n ε) := by
  refine ⟨by unfold oracleLowerEffect; cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop, ?_, ?_⟩
  · intro x
    exact (oracle_lower_effect_range κ n hd ε x).2.trans (by norm_num)
  · intro x z
    cases ε
    · simp [oracleLowerEffect]; positivity
    · let k := fun x : unitInterval => max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n)
      have hx := (oracle_lower_cutoff_bounds κ n hd x z).1
      have hz := (oracle_lower_cutoff_bounds κ n hd z x).1
      have hi := (oracle_lower_cutoff_bounds κ n hd x z).2
      have hab : |k x-k z| ≤ 1 := abs_le.mpr ⟨by dsimp [k]; linarith, by dsimp [k]; linarith⟩
      have hh := (oracle_lower_scale_bounds κ n hd).1
      have hinter := lower_increment_interpolation hh (abs_nonneg ((x : ℝ)-z))
        hd.1.2.2.2 (by norm_num : (0 : ℝ) ≤ 1) hab (by simpa [k] using hi)
      rw [one_mul, Real.div_rpow (abs_nonneg _) hh.le] at hinter
      change |oracleLowerT κ n*k x-oracleLowerT κ n*k z| ≤ _
      rw [← mul_sub, abs_mul, abs_of_pos (oracle_lower_scale_bounds κ n hd).2.2.1]
      have hprod := mul_le_mul_of_nonneg_left hinter
        (oracle_lower_scale_bounds κ n hd).2.2.1.le
      have hhpow : oracleLowerH κ n ^ κ.γ ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hh _)
      have hid : oracleLowerT κ n*(|(x : ℝ)-z|^κ.γ/oracleLowerH κ n^κ.γ) =
          |(x : ℝ)-z|^κ.γ/4 := by
        unfold oracleLowerT
        field_simp
      rw [hid] at hprod
      exact hprod.trans (by nlinarith [Real.rpow_nonneg (abs_nonneg ((x : ℝ)-z)) κ.γ])

/-- The rare outcome amplitude makes its p-minus-one power exactly the inverse effect amplitude. -/
-- @node: oracle_lower_amplitude_identity
lemma oracle_lower_amplitude_identity (hd : κ.Valid ∧ 2 ≤ n) :
    oracleLowerAmplitude κ n ^ (κ.p-1) = (oracleLowerT κ n)⁻¹ := by
  have ht := (oracle_lower_scale_bounds κ n hd).2.2.1
  unfold oracleLowerAmplitude
  rw [← Real.rpow_mul ht.le]
  have hp : κ.p-1 ≠ 0 := ne_of_gt (sub_pos.mpr hd.1.1.1)
  rw [div_mul_cancel₀ _ hp, Real.rpow_neg_one]

/-- Every original arm of the oracle pair has raw p-moment at most one. -/
-- @node: oracle_lower_conditional_moment
lemma oracle_lower_conditional_moment (hd : κ.Valid ∧ 2 ≤ n) (ε a : Bool) (x : unitInterval) :
    (∫⁻ y, ENNReal.ofReal (|y|^κ.p) ∂oracleLowerKernel κ n ε a x) ≤ 1 := by
  have hb := oracle_lower_scale_bounds κ n hd
  have hB : 0 < oracleLowerAmplitude κ n := lt_of_lt_of_le (by norm_num) hb.2.2.2.2
  have hp : κ.p ≠ 0 := ne_of_gt (lt_trans (by norm_num) hd.1.1.1)
  cases a
  · simp [oracleLowerKernel, oracleLowerOutcomeMeasure, Real.zero_rpow hp]
  · simp only [oracleLowerKernel, Kernel.coe_mk, oracleLowerOutcomeMeasure, ↓reduceIte,
      lintegral_add_measure, lintegral_smul_measure, lintegral_dirac, smul_eq_mul, abs_zero,
      Real.zero_rpow hp, ENNReal.ofReal_zero, mul_zero, zero_add, abs_of_pos hB]
    rw [← ENNReal.ofReal_mul (oracle_lower_mixing_bounds κ n hd ε x).1]
    have hid : oracleLowerEffect κ n ε x / oracleLowerAmplitude κ n * oracleLowerAmplitude κ n^κ.p =
        oracleLowerEffect κ n ε x / oracleLowerT κ n := by
      have hpow : oracleLowerAmplitude κ n^κ.p =
          oracleLowerAmplitude κ n^(κ.p-1)*oracleLowerAmplitude κ n := by
        calc
          _ = oracleLowerAmplitude κ n^((κ.p-1)+1) := by congr 1; ring
          _ = _ := by rw [Real.rpow_add hB, Real.rpow_one]
      rw [hpow, oracle_lower_amplitude_identity κ n hd]
      field_simp
    rw [hid]
    apply (ENNReal.ofReal_le_ofReal ?_).trans (by norm_num : ENNReal.ofReal (1 : ℝ) ≤ 1)
    apply (div_le_one hb.2.2.1).2
    cases ε
    · simp [oracleLowerEffect]; exact hb.2.2.1.le
    · simp only [oracleLowerEffect, ↓reduceIte]
      simpa using mul_le_mul_of_nonneg_left (oracle_lower_cutoff_bounds κ n hd x x).1.2 hb.2.2.1.le

/-- Exact uniform design, constant nuisances, bump regularity, and the two-atom moment give both model members. -/
-- @node: oracle_lower_membership
lemma oracle_lower_membership (hκ : κ.Valid) (hn : 2 ≤ n) (ε : Bool) :
    InModel κ (oracleLowerLaw κ n ε) := by
  have hd : κ.Valid ∧ 2 ≤ n := ⟨hκ, hn⟩
  rw [oracleLowerLaw, dif_pos hd]
  constructor
  · exact uniformRecord_marginal _ _ half_range _ (oracle_lower_versions κ n hd ε).1
  · intro x; norm_num [lawFromUniform]
  · change holderBall κ.α (fun _ => 1/2)
    refine ⟨continuous_const, by intro x; norm_num, ?_⟩
    intro x z; simp; positivity
  · change holderBall κ.β (fun _ => 0)
    refine ⟨continuous_const, by intro x; norm_num, ?_⟩
    intro x z; simp; positivity
  · exact oracle_lower_effect_holder κ n hd ε
  · intro x
    exact (oracle_lower_effect_range κ n hd ε x).2.trans (by norm_num)
  · filter_upwards [] with x a
    exact (oracle_lower_conditional_moment κ n hd ε a x).trans (by norm_num)

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
