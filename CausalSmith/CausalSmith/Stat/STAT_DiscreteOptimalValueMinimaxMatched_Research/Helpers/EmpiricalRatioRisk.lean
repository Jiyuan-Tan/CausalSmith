import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.UpperRiskCoupling
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TIdentificationAndExtension
import Causalean.Stat.Sample.FiniteStratumMarkedRatioMse

set_option linter.style.longLine false
/-! The bounded-alphabet empirical-ratio branch of the upper bound. -/
namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open Causalean.Stat.FiniteStratumMarkedRatioMse

-- @node: observedBinaryMark
/-- For [the specified observed datum](hyp:o), the [observed binary mark is one for a successful outcome and zero otherwise](goal). -/
noncomputable def observedBinaryMark {d : ℕ} (o : Obs d) : ℝ :=
  if o.2.2 then 1 else 0

-- @node: categoryMass_obsLaw
/-- [under the observed-data law, a category has probability equal to its cell mass](goal). -/
lemma categoryMass_obsLaw {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    categoryMass (obsLaw P) (fun o : Obs d => o.1) x = cellMass P x := by
  unfold categoryMass categoryEvent Causalean.Stat.groupEvent obsLaw
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · simp only [if_true]
    rw [ENNReal.toReal_sum (by simp [P.pmf.apply_ne_top])]
    apply congrArg
    funext a
    rw [ENNReal.toReal_sum (by simp [P.pmf.apply_ne_top])]
    rfl
  · intro b _ hb
    simp [hb]
  · simp

-- @node: armCategoryMass_obsLaw
/-- [under the observed-data law, an arm-and-cell category has probability equal to its arm mass](goal). -/
lemma armCategoryMass_obsLaw {d : ℕ} (P : DiscreteLaw d) (x : Fin d) (a : Bool) :
    armCategoryMass (obsLaw P) (fun o : Obs d => o.1) (fun o => o.2.1) a x =
      armMass P a x := by
  unfold armCategoryMass armCategoryEvent Causalean.Stat.armGroupEvent obsLaw
  rw [PMF.toMeasure_apply_fintype]
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x]
  · simp only [true_and]
    rw [Finset.sum_eq_single a]
    · simp only [if_true]
      rw [ENNReal.toReal_sum (by simp [P.pmf.apply_ne_top])]
      rfl
    · intro b _ hb
      simp [hb]
    · simp
  · intro b _ hb
    simp [hb]
  · simp

-- @node: categoryCount_eq_sampleCellCount
/-- [the stated category count identity sample cell count relation holds](goal). -/
lemma categoryCount_eq_sampleCellCount {n d : ℕ} (z : Fin n → Obs d) (x : Fin d) :
    categoryCount (fun o : Obs d => o.1) (fun o => o.2.1) z x =
      sampleCellCount z x := by
  unfold categoryCount Causalean.Stat.groupCount Causalean.Stat.groupArmCount sampleCellCount
  rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : (z i).2.1 <;> simp [h]

-- @node: categoryArmCount_eq_sampleArmCount
/-- [the stated category arm count identity sample arm count relation holds](goal). -/
lemma categoryArmCount_eq_sampleArmCount {n d : ℕ} (z : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    categoryArmCount (fun o : Obs d => o.1) (fun o => o.2.1) z a x =
      sampleArmCount z x a := by
  unfold categoryArmCount Causalean.Stat.groupArmCount sampleArmCount
  rw [Finset.card_eq_sum_ones]
  simp_rw [Finset.sum_filter]

-- @node: armMarkSum_eq_sampleSuccessCount
/-- [the stated arm mark sum identity sample success count relation holds](goal). -/
lemma armMarkSum_eq_sampleSuccessCount {n d : ℕ} (z : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    armMarkSum (fun o : Obs d => o.1) (fun o => o.2.1) observedBinaryMark z a x =
      sampleSuccessCount z x a := by
  unfold armMarkSum supportedArmMark armCategoryEvent Causalean.Stat.armGroupEvent
    observedBinaryMark sampleSuccessCount
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : (z i).1 = x ∧ (z i).2.1 = a
  · cases hy : (z i).2.2 <;> simp [ha, hy]
  · cases hy : (z i).2.2 <;> simp [ha, hy]

-- @node: totalizedArmMean_eq_sampleRatio
/-- [the stated totalized arm mean identity sample ratio relation holds](goal). -/
lemma totalizedArmMean_eq_sampleRatio {n d : ℕ} (z : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    totalizedArmMean (fun o : Obs d => o.1) (fun o => o.2.1)
        observedBinaryMark z a x =
      (sampleSuccessCount z x a : ℝ) / sampleArmCount z x a := by
  unfold totalizedArmMean
  rw [categoryArmCount_eq_sampleArmCount, armMarkSum_eq_sampleSuccessCount]
  by_cases h : 0 < sampleArmCount z x a
  · rw [if_pos h, div_eq_inv_mul]
  · rw [if_neg h]
    have hz : sampleArmCount z x a = 0 := Nat.eq_zero_of_not_pos h
    simp [hz]

-- @node: fixedStratumArmScore_singleton_eq
/-- [the stated fixed stratum arm score singleton identity relation holds](goal). -/
lemma fixedStratumArmScore_singleton_eq {n d : ℕ} (z : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
        observedBinaryMark {x} a z =
      (sampleCellCount z x : ℝ) / n *
        ((sampleSuccessCount z x a : ℝ) / sampleArmCount z x a) := by
  unfold fixedStratumArmScore
  simp only [Finset.sum_singleton, categoryCount_eq_sampleCellCount]
  rw [totalizedArmMean_eq_sampleRatio]

-- @node: integral_observedBinaryMark_armCategory
/-- [the stated integral observed binary mark arm category relation holds](goal). -/
lemma integral_observedBinaryMark_armCategory {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) :
    (∫ o in armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x,
      observedBinaryMark o ∂obsLaw P) = jointMass P x a true := by
  rw [← integral_indicator]
  · unfold obsLaw
    rw [PMF.integral_eq_sum]
    unfold armCategoryEvent Causalean.Stat.armGroupEvent observedBinaryMark
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x]
    · simp only [true_and]
      rw [Finset.sum_eq_single a]
      · simpa [jointMass]
      · intro b _ hb
        simp [hb]
      · simp
    · intro b _ hb
      simp [hb]
    · simp
  · exact Causalean.Stat.measurableSet_armGroupEvent _ _ (by fun_prop) (by fun_prop) _ _

-- @node: outcomeMean_mem_unitInterval_empirical
/-- [the stated outcome mean mem unit interval empirical relation holds](goal). -/
lemma outcomeMean_mem_unitInterval_empirical {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) : outcomeMean P a x ∈ Set.Icc (0 : ℝ) 1 := by
  have hj (y : Bool) : 0 ≤ jointMass P x a y := ENNReal.toReal_nonneg
  have ha : 0 ≤ armMass P a x := Finset.sum_nonneg fun y _ => hj y
  have hle : jointMass P x a true ≤ armMass P a x := by
    simp [armMass]
    exact hj false
  exact ⟨div_nonneg (hj true) ha, div_le_one_of_le₀ hle ha⟩

-- @node: integral_observedBinaryResidual_eq_zero
/-- [the stated integral observed binary residual identity zero relation holds](goal). -/
lemma integral_observedBinaryResidual_eq_zero {d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (a : Bool) :
    (∫ o in armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x,
      (observedBinaryMark o - outcomeMean P a x) ∂obsLaw P) = 0 := by
  have hset := Causalean.Stat.measurableSet_armGroupEvent
    (fun o : Obs d => o.1) (fun o => o.2.1) (by fun_prop) (by fun_prop) a x
  rw [integral_sub (by fun_prop) (integrableOn_const (C := outcomeMean P a x)),
    integral_observedBinaryMark_armCategory, setIntegral_const]
  change jointMass P x a true -
      (obsLaw P
        (armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x)).toReal *
        outcomeMean P a x = 0
  rw [show (obsLaw P
      (armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x)).toReal =
      armMass P a x by exact armCategoryMass_obsLaw P x a]
  unfold outcomeMean
  by_cases ha : armMass P a x = 0
  · have hj : 0 ≤ jointMass P x a true := ENNReal.toReal_nonneg
    have hle : jointMass P x a true ≤ armMass P a x := by
      simp [armMass]
      exact ENNReal.toReal_nonneg
    have hz : jointMass P x a true = 0 := le_antisymm (hle.trans_eq ha) hj
    simp [ha, hz]
  · field_simp [ha]
    ring

-- @node: observedArmResidual_memLp_two
/-- [the stated observed arm residual mem lp two relation holds](goal). -/
lemma observedArmResidual_memLp_two {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) :
    MemLp (supportedArmResidual (fun o : Obs d => o.1) (fun o => o.2.1)
      observedBinaryMark (fun a x => outcomeMean P a x) a x) 2 (obsLaw P) := by
  apply MemLp.of_bound (by fun_prop) 1
  filter_upwards [] with o
  rw [Real.norm_eq_abs]
  unfold supportedArmResidual Causalean.Stat.supportedArmGroupResidual
    Causalean.Stat.armGroupResidual
  by_cases h : o ∈ Causalean.Stat.armGroupEvent
      (fun o : Obs d => o.1) (fun o => o.2.1) a x
  · rw [Set.indicator_of_mem h]
    have hm := outcomeMean_mem_unitInterval_empirical P a x
    have habs : |outcomeMean P a x| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
    have habs1 : |1 - outcomeMean P a x| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
    cases hy : o.2.2
    · simpa [observedBinaryMark, hy] using habs
    · simpa [observedBinaryMark, hy] using habs1
  · simp [h]

-- @node: integral_observedBinaryResidual_sq_le
/-- [the stated integral observed binary residual squared upper bound relation holds](goal). -/
lemma integral_observedBinaryResidual_sq_le {d : ℕ} (P : DiscreteLaw d)
    (a : Bool) (x : Fin d) :
    (∫ o in armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x,
      (observedBinaryMark o - outcomeMean P a x) ^ 2 ∂obsLaw P) ≤ armMass P a x := by
  have hset := Causalean.Stat.measurableSet_armGroupEvent
    (fun o : Obs d => o.1) (fun o => o.2.1) (by fun_prop) (by fun_prop) a x
  have hint : IntegrableOn
      (fun o : Obs d => (observedBinaryMark o - outcomeMean P a x) ^ 2)
      (armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x) (obsLaw P) := by
    exact (Integrable.of_finite : Integrable
      (fun o : Obs d => (observedBinaryMark o - outcomeMean P a x) ^ 2)
      (obsLaw P)).integrableOn
  calc
    _ ≤ ∫ _o in armCategoryEvent (fun o : Obs d => o.1) (fun o => o.2.1) a x,
        (1 : ℝ) ∂obsLaw P := by
      apply MeasureTheory.setIntegral_mono_on hint (integrableOn_const) hset
      intro o ho
      have hm := outcomeMean_mem_unitInterval_empirical P a x
      have habs : |outcomeMean P a x| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hm.1], hm.2⟩
      have habs1 : |1 - outcomeMean P a x| ≤ 1 :=
        abs_le.mpr ⟨by linarith [hm.2], by linarith [hm.1]⟩
      cases hy : o.2.2
      · simp [observedBinaryMark, hy]
        nlinarith [sq_abs (outcomeMean P a x), habs,
          sq_nonneg (outcomeMean P a x)]
      · simp [observedBinaryMark, hy]
        nlinarith [sq_abs (1 - outcomeMean P a x), habs1,
          sq_nonneg (1 - outcomeMean P a x)]
    _ = armMass P a x := by
      rw [setIntegral_const]
      rw [smul_eq_mul, mul_one, measureReal_def]
      exact armCategoryMass_obsLaw P x a

-- @node: observedOverlap_armMass_lower
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), and [the stated x condition holds](hyp:hx), then [the stated observed overlap arm mass lower relation holds](goal). -/
lemma observedOverlap_armMass_lower {d : ℕ} {epsilon : ℝ} (P : DiscreteLaw d)
    (hP : ObservedModelClass epsilon P) (a : Bool) (x : Fin d)
    (hx : 0 < cellMass P x) : epsilon * cellMass P x ≤ armMass P a x := by
  have ht : epsilon * cellMass P x ≤ armMass P true x := by
    exact (le_div_iff₀ hx).mp (hP.overlap x hx).1
  have hsum : cellMass P x = armMass P false x + armMass P true x := by
    simp [cellMass, armMass]
    ring
  have hf : epsilon * cellMass P x ≤ armMass P false x := by
    have hu : armMass P true x ≤ (1 - epsilon) * cellMass P x := by
      exact (div_le_iff₀ hx).mp (hP.overlap x hx).2
    nlinarith
  cases a <;> assumption

-- @node: fixedStratumArmTarget_singleton_eq
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the stated fixed stratum arm target singleton identity relation holds](goal). -/
lemma fixedStratumArmTarget_singleton_eq {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) (x : Fin d) (a : Bool) :
    fixedStratumArmTarget (obsLaw P) (fun o : Obs d => o.1) (fun o => o.2.1)
        observedBinaryMark {x} a = cellMass P x * outcomeMean P a x := by
  have hpositive : ∀ k ∈ ({x} : Finset (Fin d)),
      0 < categoryMass (obsLaw P) (fun o : Obs d => o.1) k →
        0 < armCategoryMass (obsLaw P) (fun o => o.1) (fun o => o.2.1) a k := by
    intro k hk hmass
    rw [categoryMass_obsLaw] at hmass
    rw [armCategoryMass_obsLaw]
    exact (mul_pos hP.epsilon_pos hmass).trans_le
      (observedOverlap_armMass_lower P hP a k hmass)
  have hcenter := fixedStratumArmCenterTarget_eq_target
    (obsLaw P) (fun o : Obs d => o.1) (fun o => o.2.1) observedBinaryMark
    (fun a x => outcomeMean P a x) {x} a (by fun_prop) (by fun_prop)
    (fun k => observedArmResidual_memLp_two P a k)
    (fun k => integral_observedBinaryResidual_eq_zero P k a) hpositive
  rw [← hcenter]
  simp [fixedStratumArmCenterTarget, categoryMass_obsLaw]

-- @node: nonneg_mul_exp_neg_le_inv
/-- If [the stated u condition holds](hyp:hu), and [the stated p condition holds](hyp:hp), then [the stated nonnegativity product exp neg upper bound reciprocal relation holds](goal). -/
lemma nonneg_mul_exp_neg_le_inv (u p : ℝ) (hu : 0 < u) (hp : 0 ≤ p) :
    p * Real.exp (-(u * p)) ≤ u⁻¹ := by
  by_cases hz : p = 0
  · simp [hz, le_of_lt hu]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have ht : 0 < u * p := mul_pos hu hp'
  have hlin : u * p ≤ Real.exp (u * p) := by
    nlinarith [Real.add_one_le_exp (u * p)]
  have hmul := mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-(u * p))).le
  rw [← Real.exp_add] at hmul
  simp only [add_neg_cancel, Real.exp_zero] at hmul
  rw [inv_eq_one_div, le_div_iff₀ hu]
  nlinarith

-- @node: missingArmEnvelope_singleton_le
/-- If [the sample size satisfies its stated restriction](hyp:hn), and [the overlap parameter satisfies its stated range restriction](hyp:hepsilon), then [the stated missing arm envelope singleton upper bound relation holds](goal). -/
lemma missingArmEnvelope_singleton_le {n d : ℕ} (P : DiscreteLaw d)
    (x : Fin d) (epsilon : ℝ) (hn : 4 ≤ n) (hepsilon : 0 < epsilon) :
    missingArmExponentialEnvelope (obsLaw P) (fun o : Obs d => o.1)
        n epsilon {x} ≤ 4 / (n * epsilon) := by
  rw [show missingArmExponentialEnvelope (obsLaw P) (fun o : Obs d => o.1)
      n epsilon {x} = cellMass P x *
        Real.exp (-(((n - 2 : ℕ) : ℝ) / 2 * epsilon * cellMass P x)) by
    simp [missingArmExponentialEnvelope, categoryMass_obsLaw]]
  let u : ℝ := ((n - 2 : ℕ) : ℝ) / 2 * epsilon
  have hnR : 0 < (n : ℝ) := by positivity
  have hsub : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have hu : 0 < u := by
    dsimp [u]
    rw [hsub]
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    exact mul_pos (by nlinarith) hepsilon
  have hbase := nonneg_mul_exp_neg_le_inv u (cellMass P x) hu (cellMass_nonneg P x)
  have hulower : (n : ℝ) * epsilon / 4 ≤ u := by
    dsimp [u]
    rw [hsub]
    have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  calc
    cellMass P x * Real.exp (-(((n - 2 : ℕ) : ℝ) / 2 * epsilon * cellMass P x)) =
        cellMass P x * Real.exp (-(u * cellMass P x)) := by rfl
    _ ≤ u⁻¹ := hbase
    _ ≤ 4 / (n * epsilon) := by
      have hden : 0 < (n : ℝ) * epsilon / 4 := by positivity
      calc
        u⁻¹ = 1 / u := by rw [one_div]
        _ ≤ 1 / ((n : ℝ) * epsilon / 4) :=
          one_div_le_one_div_of_le hden hulower
        _ = 4 / (n * epsilon) := by field_simp

-- @node: cellMass_le_one_empirical
/-- [every cell mass is at most one](goal). -/
lemma cellMass_le_one_empirical {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    cellMass P x ≤ 1 := by
  have hsum : ∑ k : Fin d, cellMass P k = 1 := by
    calc
      _ = ∑ z : Obs d, (P.pmf z).toReal := by
        simp [cellMass, jointMass, Fintype.sum_prod_type]
      _ = 1 := by
        simpa using (PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : ℝ))).symm
  calc
    cellMass P x ≤ ∑ k : Fin d, cellMass P k :=
      Finset.single_le_sum (fun k _ => cellMass_nonneg P k) (Finset.mem_univ x)
    _ = 1 := hsum

-- @node: fixedStratumArmScore_singleton_mse_le
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), and [the sample size satisfies its stated restriction](hyp:hn), then [the stated fixed stratum arm score singleton mse upper bound relation holds](goal). -/
lemma fixedStratumArmScore_singleton_mse_le {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) (x : Fin d) (a : Bool)
    (hn : 4 ≤ n) :
    ∫ z : Fin n → Obs d,
        (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
          observedBinaryMark {x} a z - cellMass P x * outcomeMean P a x) ^ 2
      ∂productLaw P n ≤ 100 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := by
  have hbase := integral_fixedStratumArm_error_sq_le_exponential (m := n)
    (obsLaw P) (fun o : Obs d => o.1) (fun o => o.2.1) observedBinaryMark
    (fun a x => outcomeMean P a x) {x} a 1 epsilon (by fun_prop) (by fun_prop)
    (by fun_prop)
    (fun k => observedArmResidual_memLp_two P a k)
    (fun k => integral_observedBinaryResidual_eq_zero P k a)
    (fun k => by
      rw [armCategoryMass_obsLaw]
      simpa using integral_observedBinaryResidual_sq_le P a k)
    (fun k => by
      have hm := outcomeMean_mem_unitInterval_empirical P a k
      exact abs_le.mpr ⟨by linarith [hm.1], hm.2⟩)
    hP.epsilon_pos
    (fun k hk => by
      rw [categoryMass_obsLaw] at hk ⊢
      rw [armCategoryMass_obsLaw]
      exact observedOverlap_armMass_lower P hP a k hk)
  rw [fixedStratumArmTarget_singleton_eq P hP x a] at hbase
  change (∫ z : Fin n → Obs d, _ ∂productLaw P n) ≤ _
  rw [show productLaw P n = Measure.pi (fun _ : Fin n => obsLaw P) by rfl]
  calc
    _ ≤ 1 ^ 2 *
        (8 * (∑ k ∈ ({x} : Finset (Fin d)),
            categoryMass (obsLaw P) (fun o : Obs d => o.1) k) /
            (safeSampleSize n * epsilon) +
          6 / safeSampleSize n +
          4 * (missingArmExponentialEnvelope (obsLaw P)
            (fun o : Obs d => o.1) n epsilon {x}) ^ 2) := hbase
    _ ≤ 100 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := by
      have hnR : 0 < (n : ℝ) := by positivity
      have hsafe : safeSampleSize n = n := by
        simp [safeSampleSize, max_eq_right (by omega : 1 ≤ n)]
      have henv := missingArmEnvelope_singleton_le P x epsilon hn hP.epsilon_pos
      have henv0 : 0 ≤ missingArmExponentialEnvelope (obsLaw P)
          (fun o : Obs d => o.1) n epsilon {x} := by
        simp only [missingArmExponentialEnvelope, Finset.sum_singleton,
          categoryMass_obsLaw]
        exact mul_nonneg (cellMass_nonneg P x) (Real.exp_nonneg _)
      have henvSq := pow_le_pow_left₀ henv0 henv 2
      have hp := cellMass_le_one_empirical P x
      simp only [Finset.sum_singleton, categoryMass_obsLaw, one_pow, one_mul]
      rw [hsafe]
      have hterm1 : 8 * cellMass P x / (n * epsilon) ≤
          8 * epsilon⁻¹ / n := by
        calc
          _ ≤ 8 * 1 / (n * epsilon) := by
            apply div_le_div_of_nonneg_right
            · nlinarith
            · exact (mul_pos hnR hP.epsilon_pos).le
          _ = 8 * epsilon⁻¹ / n := by
            field_simp [ne_of_gt hnR, ne_of_gt hP.epsilon_pos]
      have hterm3 : 4 * missingArmExponentialEnvelope (obsLaw P)
            (fun o : Obs d => o.1) n epsilon {x} ^ 2 ≤
          64 * epsilon⁻¹ ^ 2 / n := by
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by omega : 1 ≤ 4) hn)
        have hinv0 : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (le_of_lt hnR)
        have hinv1 : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hnR).2 hn1
        have hinvSq : (n : ℝ)⁻¹ ^ 2 ≤ (n : ℝ)⁻¹ := by nlinarith [sq_nonneg ((n : ℝ)⁻¹)]
        calc
          _ ≤ 4 * (4 / (n * epsilon)) ^ 2 := by nlinarith
          _ = 64 * epsilon⁻¹ ^ 2 * (n : ℝ)⁻¹ ^ 2 := by
            field_simp [ne_of_gt hnR, ne_of_gt hP.epsilon_pos] <;> norm_num
          _ ≤ 64 * epsilon⁻¹ ^ 2 * (n : ℝ)⁻¹ := by
            gcongr
          _ = 64 * epsilon⁻¹ ^ 2 / n := by rw [div_eq_mul_inv]
      calc
        8 * cellMass P x / (n * epsilon) + 6 / n +
            4 * missingArmExponentialEnvelope (obsLaw P)
              (fun o : Obs d => o.1) n epsilon {x} ^ 2 ≤
            8 * epsilon⁻¹ / n + 6 / n + 64 * epsilon⁻¹ ^ 2 / n := by
          linarith
        _ ≤ 100 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := by
          let t : ℝ := epsilon⁻¹
          change 8 * t / n + 6 / n + 64 * t ^ 2 / n ≤
            100 * (1 + t + t ^ 2) / n
          have ht : 0 ≤ t := by
            dsimp [t]
            exact inv_nonneg.mpr (le_of_lt hP.epsilon_pos)
          field_simp [ne_of_gt hnR]
          nlinarith [sq_nonneg t]

-- @node: empiricalRatio_eq_max_armScores
/-- [the empirical-ratio estimator equals the sum across strata of the larger empirical arm score](goal). -/
lemma empiricalRatio_eq_max_armScores {n d : ℕ} (z : Fin n → Obs d) :
    empiricalRatioEstimator z = ∑ x : Fin d,
      max
        (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
          observedBinaryMark {x} false z)
        (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
          observedBinaryMark {x} true z) := by
  unfold empiricalRatioEstimator
  apply Finset.sum_congr rfl
  intro x hx
  rw [fixedStratumArmScore_singleton_eq, fixedStratumArmScore_singleton_eq,
    ← mul_max_of_nonneg]
  positivity

-- @node: observedOptimalValue_eq_max_armTargets
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the stated observed optimal value identity max arm targets relation holds](goal). -/
lemma observedOptimalValue_eq_max_armTargets {d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P) :
    observedOptimalValue P hP = ∑ x : Fin d,
      max (cellMass P x * outcomeMean P false x)
        (cellMass P x * outcomeMean P true x) := by
  unfold observedOptimalValue observedOptimalValueRaw
  apply Finset.sum_congr rfl
  intro x hx
  rw [← mul_max_of_nonneg]
  exact cellMass_nonneg P x

-- @node: empiricalRatio_pointwise_sq_le_armScores
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), then [the squared empirical-ratio error is bounded by twice the sum of the two arm-score errors](goal). -/
lemma empiricalRatio_pointwise_sq_le_armScores {n d : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw d) (hP : ObservedModelClass epsilon P)
    (z : Fin n → Obs d) :
    (empiricalRatioEstimator z - observedOptimalValue P hP) ^ 2 ≤
      (2 * d) * ∑ xa : Fin d × Bool,
        (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
          observedBinaryMark {xa.1} xa.2 z -
            cellMass P xa.1 * outcomeMean P xa.2 xa.1) ^ 2 := by
  let e : Fin d → Bool → ℝ := fun x a =>
    fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
      observedBinaryMark {x} a z - cellMass P x * outcomeMean P a x
  have habs : |empiricalRatioEstimator z - observedOptimalValue P hP| ≤
      ∑ xa : Fin d × Bool, |e xa.1 xa.2| := by
    rw [empiricalRatio_eq_max_armScores, observedOptimalValue_eq_max_armTargets,
      ← Finset.sum_sub_distrib]
    calc
      |∑ x : Fin d,
          (max
            (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
              observedBinaryMark {x} false z)
            (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
              observedBinaryMark {x} true z) -
           max (cellMass P x * outcomeMean P false x)
             (cellMass P x * outcomeMean P true x))| ≤
          ∑ x : Fin d, |max
            (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
              observedBinaryMark {x} false z)
            (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
              observedBinaryMark {x} true z) -
           max (cellMass P x * outcomeMean P false x)
             (cellMass P x * outcomeMean P true x)| := by
            simpa using Finset.abs_sum_le_sum_abs (fun x : Fin d =>
              max
                (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
                  observedBinaryMark {x} false z)
                (fixedStratumArmScore (fun o : Obs d => o.1) (fun o => o.2.1)
                  observedBinaryMark {x} true z) -
              max (cellMass P x * outcomeMean P false x)
                (cellMass P x * outcomeMean P true x)) Finset.univ
      _ ≤ ∑ x : Fin d, (|e x false| + |e x true|) := by
        apply Finset.sum_le_sum
        intro x hx
        refine (abs_max_sub_max_le_max _ _ _ _).trans ?_
        exact max_le (le_add_of_nonneg_right (abs_nonneg _))
          (le_add_of_nonneg_left (abs_nonneg _))
      _ = ∑ xa : Fin d × Bool, |e xa.1 xa.2| := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro x hx
        simp [Fintype.sum_bool, add_comm]
  have hsum := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun xa : Fin d × Bool => |e xa.1 xa.2|)
  calc
    (empiricalRatioEstimator z - observedOptimalValue P hP) ^ 2 =
        |empiricalRatioEstimator z - observedOptimalValue P hP| ^ 2 := by rw [sq_abs]
    _ ≤ (∑ xa : Fin d × Bool, |e xa.1 xa.2|) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ (2 * d) * ∑ xa : Fin d × Bool, |e xa.1 xa.2| ^ 2 := by
      simpa [mul_comm] using hsum
    _ = (2 * d) * ∑ xa : Fin d × Bool, (e xa.1 xa.2) ^ 2 := by
      simp only [sq_abs]

-- @node: empiricalRatio_sqRisk_two_le
/-- If [the observed law satisfies the stated model restrictions](hyp:hP), and [the sample size satisfies its stated restriction](hyp:hn), then [the empirical-ratio estimator has the stated uniform squared-risk upper bound](goal). -/
lemma empiricalRatio_sqRisk_two_le {n : ℕ} {epsilon : ℝ}
    (P : DiscreteLaw 2) (hP : ObservedModelClass epsilon P) (hn : 4 ≤ n) :
    Causalean.Stat.sqRisk (productLaw P n) empiricalRatioEstimator
        (observedOptimalValue P hP) ≤
      1600 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := by
  unfold Causalean.Stat.sqRisk
  have hpoint := empiricalRatio_pointwise_sq_le_armScores (n := n) P hP
  calc
    _ ≤ ∫ z : Fin n → Obs 2,
        (4 * ∑ xa : Fin 2 × Bool,
          (fixedStratumArmScore (fun o : Obs 2 => o.1) (fun o => o.2.1)
            observedBinaryMark {xa.1} xa.2 z -
              cellMass P xa.1 * outcomeMean P xa.2 xa.1) ^ 2) ∂productLaw P n := by
      apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
      intro z
      have hz := hpoint z
      norm_num at hz
      exact hz
    _ = 4 * ∑ xa : Fin 2 × Bool,
        ∫ z : Fin n → Obs 2,
          (fixedStratumArmScore (fun o : Obs 2 => o.1) (fun o => o.2.1)
            observedBinaryMark {xa.1} xa.2 z -
              cellMass P xa.1 * outcomeMean P xa.2 xa.1) ^ 2 ∂productLaw P n := by
      rw [integral_const_mul, integral_finset_sum]
      intro xa hxa
      exact Integrable.of_finite
    _ ≤ 4 * ∑ _xa : Fin 2 × Bool,
        (100 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n) := by
      gcongr
      exact fixedStratumArmScore_singleton_mse_le P hP _ _ hn
    _ = 1600 * (1 + epsilon⁻¹ + epsilon⁻¹ ^ 2) / n := by
      norm_num [Fintype.sum_prod_type, Fintype.sum_bool]
      ring

-- @node: sampleSuccessCount_le_sampleArmCount
/-- [the stated sample success count upper bound sample arm count relation holds](goal). -/
lemma sampleSuccessCount_le_sampleArmCount {n d : ℕ} (z : Fin n → Obs d)
    (x : Fin d) (a : Bool) : sampleSuccessCount z x a ≤ sampleArmCount z x a := by
  unfold sampleSuccessCount sampleArmCount
  apply Finset.sum_le_sum
  intro i hi
  split <;> split <;> simp_all

-- @node: sum_sampleCellCount
/-- [sample cell counts sum to the total sample size](goal). -/
lemma sum_sampleCellCount {n d : ℕ} (z : Fin n → Obs d) :
    ∑ x : Fin d, sampleCellCount z x = n := by
  unfold sampleCellCount
  rw [Finset.sum_comm]
  calc
    (∑ i : Fin n, ∑ x : Fin d, if (z i).1 = x then 1 else 0) =
        ∑ _i : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_eq_single (z i).1]
      · simp
      · intro x _ hx
        simp [hx.symm]
      · simp
    _ = n := by simp

-- @node: empiricalRatioEstimator_mem_unitInterval
/-- If [the sample size satisfies its stated restriction](hyp:hn), then [the stated empirical ratio estimator mem unit interval relation holds](goal). -/
lemma empiricalRatioEstimator_mem_unitInterval {n d : ℕ} (z : Fin n → Obs d)
    (hn : 0 < n) : empiricalRatioEstimator z ∈ Set.Icc (0 : ℝ) 1 := by
  have hratio (x : Fin d) (a : Bool) :
      (sampleSuccessCount z x a : ℝ) / sampleArmCount z x a ∈ Set.Icc (0 : ℝ) 1 := by
    have hs0 : (0 : ℝ) ≤ sampleSuccessCount z x a := by positivity
    have ha0 : (0 : ℝ) ≤ sampleArmCount z x a := by positivity
    have hle : (sampleSuccessCount z x a : ℝ) ≤ sampleArmCount z x a := by
      exact_mod_cast sampleSuccessCount_le_sampleArmCount z x a
    exact ⟨div_nonneg hs0 ha0, div_le_one_of_le₀ hle ha0⟩
  have hweights : ∑ x : Fin d, (sampleCellCount z x : ℝ) / n = 1 := by
    rw [← Finset.sum_div, ← Nat.cast_sum, sum_sampleCellCount]
    field_simp
  unfold empiricalRatioEstimator
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (by positivity)
      ((hratio x false).1.trans (le_max_left _ _))
  · calc
      ∑ x : Fin d, (sampleCellCount z x : ℝ) / n *
          max ((sampleSuccessCount z x false : ℝ) / sampleArmCount z x false)
            ((sampleSuccessCount z x true : ℝ) / sampleArmCount z x true) ≤
          ∑ x : Fin d, (sampleCellCount z x : ℝ) / n * 1 := by
        apply Finset.sum_le_sum
        intro x hx
        gcongr
        exact max_le (hratio x false).2 (hratio x true).2
      _ = 1 := by simpa using hweights

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
