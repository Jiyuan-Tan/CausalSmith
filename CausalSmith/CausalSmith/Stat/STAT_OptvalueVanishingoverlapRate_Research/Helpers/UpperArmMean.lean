module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperBinomialCounts
public import Causalean.Stat.Sample.Stratified.TreatmentRegression.ResidualWeights

/-! # Bernoulli arm-mean second moments

Roadmap equation (5) combines the centered selected-arm variance with the
empty-arm contribution. The finite observed law allows boundary means and
null cells throughout the residual calculation.
-/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators


-- @node: armMass_mul_outcomeMean
/-- Multiplying the totalized arm mean by its arm mass recovers the success mass, including a null arm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma armMass_mul_outcomeMean {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) :
    armMass P a x * outcomeMean P a x = jointMass P x a true := by
  have hsum : armMass P a x = jointMass P x a false + jointMass P x a true := by
    simp [armMass]; ring
  by_cases h : armMass P a x = 0
  · have hz : jointMass P x a true = 0 := by
      have h0 : 0 ≤ jointMass P x a false := ENNReal.toReal_nonneg
      have h1 : 0 ≤ jointMass P x a true := ENNReal.toReal_nonneg
      rw [h] at hsum
      linarith
    simp [h, hz]
  · rw [outcomeMean]
    field_simp [h]


-- @node: integral_observedArm_eq
/-- Integrals restricted to one observed arm reduce to its two outcome atoms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_observedArm_eq {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d)
    (f : Bool → ℝ) :
    (∫ z in {z : Obs d | z.1 = x ∧ z.2.1 = a}, f z.2.2 ∂P.pmf.toMeasure) =
      jointMass P x a false * f false + jointMass P x a true * f true := by
  classical
  rw [← integral_indicator (Set.toFinite _).measurableSet, PMF.integral_eq_sum]
  cases a <;> simp [Set.indicator, Fintype.sum_prod_type, jointMass, smul_eq_mul] <;> ring


-- @node: observedArm_residual_centered
/-- The binary outcome residual is centered on every arm, including null arms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedArm_residual_centered {d : ℕ} (P : DiscreteLaw d) (a : Bool) (x : Fin d) :
    (∫ z in {z : Obs d | z.1 = x ∧ z.2.1 = a},
      ((if z.2.2 then (1 : ℝ) else 0) - outcomeMean P a x) ∂P.pmf.toMeasure) = 0 := by
  rw [integral_observedArm_eq P a x (fun y => (if y then (1 : ℝ) else 0) - outcomeMean P a x)]
  have hm := armMass_mul_outcomeMean P a x
  have hs : armMass P a x = jointMass P x a false + jointMass P x a true := by
    simp [armMass]; ring
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hs] at hm
  nlinarith


-- @node: observedArm_residual_secondMoment_le
/-- The binary residual second moment is at most one quarter of the arm mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedArm_residual_secondMoment_le {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) :
    (∫ z in {z : Obs d | z.1 = x ∧ z.2.1 = a},
      ((if z.2.2 then (1 : ℝ) else 0) - outcomeMean P a x) ^ 2 ∂P.pmf.toMeasure) ≤
      armMass P a x * (1 / 2 : ℝ) ^ 2 := by
  rw [integral_observedArm_eq P a x (fun y => ((if y then (1 : ℝ) else 0) - outcomeMean P a x) ^ 2)]
  have hm := armMass_mul_outcomeMean P a x
  have hs : armMass P a x = jointMass P x a false + jointMass P x a true := by
    simp [armMass]; ring
  have hp : 0 ≤ armMass P a x := Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  have hvar : outcomeMean P a x * (1 - outcomeMean P a x) ≤ (1 / 2 : ℝ) ^ 2 := by
    nlinarith [sq_nonneg (outcomeMean P a x - 1 / 2)]
  have heq : jointMass P x a false * (0 - outcomeMean P a x) ^ 2 +
      jointMass P x a true * (1 - outcomeMean P a x) ^ 2 =
      armMass P a x * (outcomeMean P a x * (1 - outcomeMean P a x)) := by
    calc
      _ = armMass P a x * outcomeMean P a x ^ 2 + jointMass P x a true *
          (1 - 2 * outcomeMean P a x) := by rw [hs]; ring
      _ = _ := by rw [← hm]; ring
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [heq]
  exact mul_le_mul_of_nonneg_left hvar hp


-- @node: selectedArm_coeff_sq_sum
/-- The sum of squares of selected-arm averaging coefficients is the totalized inverse count. This is the finite-design variance factor in equation (5). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma selectedArm_coeff_sq_sum {n d : ℕ} (D : Fin n → Fin d × Bool)
    (x : Fin d) (a : Bool) :
    (∑ i, (if (D i).1 = x ∧ (D i).2 = a then
      ((∑ j : Fin n, if (D j).1 = x ∧ (D j).2 = a then 1 else 0 : ℕ) : ℝ)⁻¹
      else 0) ^ 2) =
      if 0 < (∑ j : Fin n, if (D j).1 = x ∧ (D j).2 = a then 1 else 0 : ℕ) then
        ((∑ j : Fin n, if (D j).1 = x ∧ (D j).2 = a then 1 else 0 : ℕ) : ℝ)⁻¹
      else 0 := by
  classical
  let N : ℕ := ∑ j, if (D j).1 = x ∧ (D j).2 = a then 1 else 0
  have heq : (∑ i, (if (D i).1 = x ∧ (D i).2 = a then (N : ℝ)⁻¹ else 0) ^ 2) =
      (N : ℝ) * (N : ℝ)⁻¹ ^ 2 := by
    rw [show (N : ℝ) = ∑ i : Fin n, if (D i).1 = x ∧ (D i).2 = a then
      (1 : ℝ) else 0 by simp [N, Nat.cast_sum], Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  change (∑ i, (if (D i).1 = x ∧ (D i).2 = a then (N : ℝ)⁻¹ else 0) ^ 2) =
    if 0 < N then (N : ℝ)⁻¹ else 0
  rw [heq]
  by_cases hN : 0 < N
  · rw [if_pos hN]
    have h : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    field_simp
  · have h : N = 0 := Nat.eq_zero_of_not_pos hN
    simp [h]


-- @node: selectedArm_residual_eq
/-- The selected design-weighted residual is the centered empirical numerator scaled by its arm count; at an empty arm it is zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma selectedArm_residual_eq {n d : ℕ} (P : DiscreteLaw d) (o : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    Causalean.Stat.Sample.Stratified.TreatmentRegression.designWeightedResidual
      Prod.fst (fun z : Obs d => z.2.1) (fun z : Obs d => if z.2.2 then 1 else 0)
      (outcomeMean P)
      (fun D i => if (D i).1 = x ∧ (D i).2 = a then
        ((∑ j : Fin n, if (D j).1 = x ∧ (D j).2 = a then 1 else 0 : ℕ) : ℝ)⁻¹
        else 0) o =
      ((sampleSuccessCount o x a : ℝ) -
        (sampleArmCount o x a : ℝ) * outcomeMean P a x) / sampleArmCount o x a := by
  classical
  simp only [Causalean.Stat.Sample.Stratified.TreatmentRegression.designWeightedResidual,
    Causalean.Stat.sampleDesign]
  change (∑ i, (if (o i).1 = x ∧ (o i).2.1 = a then
    (sampleArmCount o x a : ℝ)⁻¹ else 0) *
      ((if (o i).2.2 then 1 else 0) - outcomeMean P (o i).2.1 (o i).1)) = _
  have hterm (i : Fin n) : (if (o i).1 = x ∧ (o i).2.1 = a then
      (sampleArmCount o x a : ℝ)⁻¹ else 0) *
        ((if (o i).2.2 then 1 else 0) - outcomeMean P (o i).2.1 (o i).1) =
      (sampleArmCount o x a : ℝ)⁻¹ *
        ((if (o i).1 = x ∧ (o i).2.1 = a ∧ (o i).2.2 = true then 1 else 0) -
          (if (o i).1 = x ∧ (o i).2.1 = a then 1 else 0) * outcomeMean P a x) := by
    by_cases h : (o i).1 = x ∧ (o i).2.1 = a
    · simp only [h, if_pos, h.1, h.2, true_and, one_mul]
    · have hn : ¬ ((o i).1 = x ∧ (o i).2.1 = a ∧ (o i).2.2 = true) :=
        fun hh => h ⟨hh.1, hh.2.1⟩
      simp [h, hn]
  simp_rw [hterm]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  simp only [sampleSuccessCount, sampleArmCount, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, div_eq_mul_inv, mul_comm]


-- @node: empiricalArmCentered_mse_le_inverse
/-- Conditional Bernoulli centering removes cross-coordinate terms even though the averaging denominator depends on the entire observed design. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalArmCentered_mse_le_inverse {n d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) :
    (∫ o, (((sampleSuccessCount o x a : ℝ) -
      (sampleArmCount o x a : ℝ) * outcomeMean P a x) / sampleArmCount o x a) ^ 2
      ∂productLaw P n) ≤
      (1 / 4 : ℝ) * ∫ o,
        if 0 < sampleArmCount o x a then (sampleArmCount o x a : ℝ)⁻¹ else 0
        ∂productLaw P n := by
  have hmem : ∀ b y, MemLp
      (Causalean.Stat.supportedArmGroupResidual Prod.fst
        (fun z : Obs d => z.2.1) (fun z : Obs d => if z.2.2 then 1 else 0)
        (outcomeMean P) b y) 2 P.pmf.toMeasure := by
    intro b y
    apply (memLp_two_iff_integrable_sq ?_).2 Integrable.of_finite
    fun_prop
  have hc : ∀ b y, (∫ z in Causalean.Stat.armGroupEvent Prod.fst
      (fun z : Obs d => z.2.1) b y,
      Causalean.Stat.armGroupResidual (fun z : Obs d => if z.2.2 then 1 else 0)
        (outcomeMean P) b y z ∂P.pmf.toMeasure) = 0 :=
    fun b y => observedArm_residual_centered P b y
  have hs : ∀ b y, (∫ z in Causalean.Stat.armGroupEvent Prod.fst
      (fun z : Obs d => z.2.1) b y,
      (Causalean.Stat.armGroupResidual (fun z : Obs d => if z.2.2 then 1 else 0)
        (outcomeMean P) b y z) ^ 2 ∂P.pmf.toMeasure) ≤
      (P.pmf.toMeasure (Causalean.Stat.armGroupEvent Prod.fst
        (fun z : Obs d => z.2.1) b y)).toReal * (1 / 2 : ℝ) ^ 2 := by
    intro b y
    change _ ≤ P.pmf.toMeasure.real {z : Obs d | z.1 = y ∧ z.2.1 = b} * _
    rw [armEvent_mass_eq_armMass]
    exact observedArm_residual_secondMoment_le P b y
  classical
  have h := Causalean.Stat.Sample.Stratified.TreatmentRegression.integral_designWeightedResidual_sq_le
    n P.pmf.toMeasure Prod.fst (fun z : Obs d => z.2.1)
    (fun z : Obs d => if z.2.2 then 1 else 0) (outcomeMean P) (1 / 2)
    (by fun_prop) (by fun_prop) hmem hc hs
    (fun D i => if (D i).1 = x ∧ (D i).2 = a then
      ((∑ j : Fin n, if (D j).1 = x ∧ (D j).2 = a then 1 else 0 : ℕ) : ℝ)⁻¹
      else 0) (fun _ => 1) (fun _ => by norm_num)
  simp only [one_mul, selectedArm_residual_eq, selectedArm_coeff_sq_sum] at h
  convert h using 1
  · rfl
  · norm_num only [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]
    congr 1


-- @node: empiricalArm_error_sq_eq
/-- Separating the empty arm from the centered numerator gives the exact pointwise variance-plus-empty-arm decomposition. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalArm_error_sq_eq {n d : ℕ} (P : DiscreteLaw d) (o : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2 =
      (((sampleSuccessCount o x a : ℝ) -
        (sampleArmCount o x a : ℝ) * outcomeMean P a x) / sampleArmCount o x a) ^ 2 +
      (if sampleArmCount o x a = 0 then (1 : ℝ) else 0) * outcomeMean P a x ^ 2 := by
  by_cases h : sampleArmCount o x a = 0
  · simp [h]
  · have hR : (sampleArmCount o x a : ℝ) ≠ 0 := by exact_mod_cast h
    rw [if_neg h, zero_mul, add_zero, sub_div, mul_div_cancel_left₀ _ hR]


-- @node: empiricalOutcomeMean_mse_le
/-- Equation (5) for an actual observed arm. The inverse occupied-count term and the empty-arm term are bounded separately using equation (4). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma empiricalOutcomeMean_mse_le {n d : ℕ} (P : DiscreteLaw d) (x : Fin d)
    (a : Bool) (hp : 0 < armMass P a x) :
    (∫ o, ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a -
      outcomeMean P a x) ^ 2 ∂productLaw P n) ≤
      3 / (2 * ((n + 1 : ℝ) * armMass P a x)) := by
  let : IsProbabilityMeasure (productLaw P n) := by
    dsimp [productLaw]
    infer_instance
  have hm := outcomeMean_mem_unitInterval P a x
  have hm2 : outcomeMean P a x ^ 2 ≤ 1 := by nlinarith [hm.1, hm.2]
  have hc := empiricalArmCentered_mse_le_inverse (n := n) P x a
  have hi := integral_sampleArmCount_inverse_le (n := n) P x a hp
  have he := integral_sampleArmCount_empty_le (n := n) P x a hp
  have hden : 0 < (n + 1 : ℝ) * armMass P a x := mul_pos (by positivity) hp
  calc
    _ = (∫ o, (((sampleSuccessCount o x a : ℝ) -
        (sampleArmCount o x a : ℝ) * outcomeMean P a x) / sampleArmCount o x a) ^ 2
        ∂productLaw P n) +
      (∫ o, if sampleArmCount o x a = 0 then (1 : ℝ) else 0 ∂productLaw P n) *
        outcomeMean P a x ^ 2 := by
      simp_rw [empiricalArm_error_sq_eq]
      rw [integral_add Integrable.of_finite Integrable.of_finite, integral_mul_const]
    _ ≤ (1 / 4 : ℝ) * (2 / ((n + 1 : ℝ) * armMass P a x)) +
        1 / ((n + 1 : ℝ) * armMass P a x) := by
      apply add_le_add
      · exact hc.trans (mul_le_mul_of_nonneg_left hi (by norm_num))
      · exact (mul_le_mul_of_nonneg_right he (sq_nonneg _)).trans
          (mul_le_of_le_one_right (by positivity) hm2)
    _ = _ := by
      field_simp [ne_of_gt hden]
      <;> ring


-- @node: observedClass_armMass_lower
/-- Occupied-cell propensity overlap gives the same lower mass bound in each arm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP,hp), the [stated conclusion](goal) holds. -/
lemma observedClass_armMass_lower {d : ℕ} {ε : ℝ} (P : DiscreteLaw d)
    (hP : ObservedClass ε P) (x : Fin d) (a : Bool) (hp : 0 < cellMass P x) :
    ε * cellMass P x ≤ armMass P a x := by
  obtain ⟨hlo, hhi⟩ := hP.overlap x hp
  have hs : cellMass P x = armMass P false x + armMass P true x := by
    simp [cellMass, armMass]; ring
  rw [propensity] at hlo hhi
  have hl := (le_div_iff₀ hp).mp hlo
  have hh := (div_le_iff₀ hp).mp hhi
  cases a
  · nlinarith
  · exact hl


-- @node: cellMass_mul_empiricalOutcomeMean_mse_le
/-- Multiplying equation (5) by cell mass removes the unknown cell mass from its bound. Null cells vanish before any division. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP,hε), the [stated conclusion](goal) holds. -/
lemma cellMass_mul_empiricalOutcomeMean_mse_le {n d : ℕ} {ε : ℝ}
    (P : DiscreteLaw d) (hP : ObservedClass ε P) (hε : 0 < ε)
    (x : Fin d) (a : Bool) :
    cellMass P x * (∫ o, ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a -
      outcomeMean P a x) ^ 2 ∂productLaw P n) ≤ 3 / (2 * (n + 1 : ℝ) * ε) := by
  have hp0 : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg
  by_cases hp : cellMass P x = 0
  · rw [hp, zero_mul]
    positivity
  · have hp1 : 0 < cellMass P x := lt_of_le_of_ne hp0 (Ne.symm hp)
    have hl := observedClass_armMass_lower P hP x a hp1
    have harm : 0 < armMass P a x := lt_of_lt_of_le (mul_pos hε hp1) hl
    have hN : 0 < (n + 1 : ℝ) := by positivity
    calc
      _ ≤ cellMass P x * (3 / (2 * ((n + 1 : ℝ) * armMass P a x))) :=
        mul_le_mul_of_nonneg_left (empiricalOutcomeMean_mse_le P x a harm) hp0
      _ = 3 * cellMass P x / (2 * (n + 1 : ℝ) * armMass P a x) := by ring
      _ ≤ 3 * cellMass P x / (2 * (n + 1 : ℝ) * (ε * cellMass P x)) := by
        gcongr
      _ = _ := by field_simp


-- @node: empiricalArmMax_mse_le
/-- Equation (6): the squared mass-weighted maximum arm error is at most 3d/((n+1)ε), using the two Bernoulli arm-mean bounds. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hP,hε), the [stated conclusion](goal) holds. -/
lemma empiricalArmMax_mse_le {n d : ℕ} {ε : ℝ} (P : DiscreteLaw d)
    (hP : ObservedClass ε P) (hε : 0 < ε) :
    (∫ o, (∑ x : Fin d, cellMass P x *
      max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
        |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x|) ^ 2
      ∂productLaw P n) ≤ 3 * d / ((n + 1 : ℝ) * ε) := by
  let : IsProbabilityMeasure (productLaw P n) := by dsimp [productLaw]; infer_instance
  calc
    _ ≤ ∫ o, ∑ x : Fin d, cellMass P x * ∑ a : Bool,
        ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2
        ∂productLaw P n :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun o => cellMass_weighted_armMax_sq_le P (fun a x =>
          (sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x))
    _ = ∑ x : Fin d, ∑ a : Bool, cellMass P x * ∫ o,
        ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2
        ∂productLaw P n := by
      rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
      apply Finset.sum_congr rfl
      intro x hx
      rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite),
        Finset.mul_sum]
    _ ≤ ∑ x : Fin d, ∑ a : Bool, 3 / (2 * (n + 1 : ℝ) * ε) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.sum_le_sum fun a _ => cellMass_mul_empiricalOutcomeMean_mse_le P hP hε x a
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
      field_simp
      <;> ring


-- @node: empiricalValue_sqRisk_le
/-- The projected empirical-ratio estimator has the parametric upper bound needed on the bounded-alphabet branch; both terms in equation (6) are derived under the actual iid law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hP,hε,hε1), the [stated conclusion](goal) holds. -/
lemma empiricalValue_sqRisk_le {n d : ℕ} {ε : ℝ} (hn : 0 < n)
    (P : DiscreteLaw d) (hP : ObservedClass ε P) (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    Causalean.Stat.sqRisk (productLaw P n) empiricalValue (observedValue P) ≤
      8 * d / ((n : ℝ) * ε) := by
  let : IsProbabilityMeasure (productLaw P n) := by dsimp [productLaw]; infer_instance
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hmass := empiricalMassError_mse_le hn P
  have harm := empiricalArmMax_mse_le (n := n) P hP hε
  calc
    _ ≤ 2 * (∫ o, (∑ x : Fin d,
        |(sampleCellCount o x : ℝ) / n - cellMass P x|) ^ 2 ∂productLaw P n) +
      2 * (∫ o, (∑ x : Fin d, cellMass P x *
        max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
          |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x|) ^ 2
        ∂productLaw P n) := by
      unfold Causalean.Stat.sqRisk
      rw [← integral_const_mul, ← integral_const_mul,
        ← integral_add Integrable.of_finite Integrable.of_finite]
      exact integral_mono Integrable.of_finite Integrable.of_finite
        (fun o => empiricalValue_sq_error_le_components o P)
    _ ≤ 2 * ((d : ℝ) / n) + 2 * (3 * d / ((n + 1 : ℝ) * ε)) := by linarith
    _ ≤ 2 * ((d : ℝ) / ((n : ℝ) * ε)) + 2 * (3 * d / ((n : ℝ) * ε)) := by
      apply add_le_add
      · gcongr
        nlinarith
      · gcongr
        linarith
    _ = _ := by ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
