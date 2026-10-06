module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperEmpiricalRatio
public import Causalean.Mathlib.Probability.BernoulliMeasure

/-! # Binomial count bounds for the empirical-ratio branch

Roadmap equation (4) controls the inverse occupied-arm count and the empty-arm
probability. These bounds retain the extra trial in the denominator and allow
success probability one. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators
open Causalean.Mathlib.Probability


-- @node: integral_boolCount_eq_binomial
/-- A function of the success count in iid Boolean trials has the binomial expectation. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp0,hp1), the [stated conclusion](goal) holds. -/
lemma integral_boolCount_eq_binomial (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (F : ℕ → ℝ) :
    (∫ b : Fin n → Bool, F (Finset.univ.filter fun i => b i = true).card
      ∂Measure.pi (fun _ => bernoulliBool p)) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n p k * F k := by
  let : IsProbabilityMeasure (bernoulliBool p) := bernoulliBool_isProbabilityMeasure hp0 hp1
  rw [integral_fintype Integrable.of_finite]
  have hmass (b : Fin n → Bool) :
      (Measure.pi (fun _ : Fin n => bernoulliBool p)).real {b} =
        ∏ i, if b i then p else 1 - p := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i hi
    cases b i <;> simp [bernoulliBool, hp0, sub_nonneg.mpr hp1]
  simp_rw [hmass, smul_eq_mul]
  simpa using sum_bernoulli_eq_binomial (ι := Fin n) p F

-- @node: integral_boolCount_inverse_le
/-- Equation (4)'s reciprocal bound for iid Boolean success counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hp1), the [stated conclusion](goal) holds. -/
lemma integral_boolCount_inverse_le (n : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ b : Fin n → Bool,
      if 0 < (Finset.univ.filter fun i => b i = true).card then
        ((Finset.univ.filter fun i => b i = true).card : ℝ)⁻¹ else 0
      ∂Measure.pi (fun _ => bernoulliBool p)) ≤ 2 / ((n + 1 : ℝ) * p) := by
  rw [integral_boolCount_eq_binomial n p hp.le hp1 (fun k => if 0 < k then (k : ℝ)⁻¹ else 0)]
  simpa only [Nat.cast_add, Nat.cast_one] using binomial_totalized_inverse_count_le n p hp hp1

-- @node: integral_boolCount_empty_eq
/-- Empty iid Boolean counts have the exact binomial zero probability. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp0,hp1), the [stated conclusion](goal) holds. -/
lemma integral_boolCount_empty_eq (n : ℕ) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∫ b : Fin n → Bool,
      if (Finset.univ.filter fun i => b i = true).card = 0 then (1 : ℝ) else 0
      ∂Measure.pi (fun _ => bernoulliBool p)) = (1 - p) ^ n := by
  rw [integral_boolCount_eq_binomial n p hp0 hp1 (fun k => if k = 0 then 1 else 0)]
  simp [binomialWeight]

-- @node: binomial_empty_probability_le
/-- The probability of no binomial successes is bounded by the reciprocal expected count with one extra trial, as in equation (4). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hp1), the [stated conclusion](goal) holds. -/
lemma binomial_empty_probability_le (n : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (1 - p) ^ n ≤ 1 / ((n + 1 : ℝ) * p) := by
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsum : (n + 1 : ℝ) * (1 - p) ^ n ≤
      ∑ k ∈ Finset.range (n + 1), (1 - p) ^ k := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1), (1 - p) ^ n := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_of_le_one hq (by linarith) (by simpa using Finset.mem_range.mp hk)
  have hid := geom_sum_mul_neg (1 - p) (n + 1)
  have hbound : (n + 1 : ℝ) * (1 - p) ^ n * p ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hsum hp.le
    have hpow := pow_nonneg hq (n + 1)
    nlinarith
  apply (le_div_iff₀ (mul_pos (by positivity) hp)).2
  nlinarith

-- @node: integral_boolCount_empty_le
/-- The empty-count expectation obeys the second inequality in equation (4). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp,hp1), the [stated conclusion](goal) holds. -/
lemma integral_boolCount_empty_le (n : ℕ) (p : ℝ)
    (hp : 0 < p) (hp1 : p ≤ 1) :
    (∫ b : Fin n → Bool,
      if (Finset.univ.filter fun i => b i = true).card = 0 then (1 : ℝ) else 0
      ∂Measure.pi (fun _ => bernoulliBool p)) ≤ 1 / ((n + 1 : ℝ) * p) := by
  rw [integral_boolCount_empty_eq n p hp.le hp1]
  exact binomial_empty_probability_le n p hp hp1

open Classical in
-- @node: eventIndicator_measurePreserving
/-- A measurable event indicator pushes its probability law to the Boolean Bernoulli law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA), the [stated conclusion](goal) holds. -/
lemma eventIndicator_measurePreserving {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A) :
    MeasurePreserving (fun z => decide (z ∈ A)) μ (bernoulliBool (μ.real A)) := by
  classical
  have hf : Measurable (fun z => decide (z ∈ A)) := by
    have h : Measurable (fun z => if z ∈ A then true else false) :=
      Measurable.ite hA measurable_const measurable_const
    simpa using h
  have hp0 : 0 ≤ μ.real A := ENNReal.toReal_nonneg
  have hp1 : μ.real A ≤ 1 := measureReal_le_one
  let : IsProbabilityMeasure (bernoulliBool (μ.real A)) :=
    bernoulliBool_isProbabilityMeasure hp0 hp1
  refine ⟨hf, Measure.ext_of_singleton fun b => ?_⟩
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (μ.map (fun z => decide (z ∈ A))).real {b} = _
  rw [map_measureReal_apply hf (measurableSet_singleton b)]
  cases b
  · have hcompl : μ.real {z | z ∉ A} = 1 - μ.real A := by
      change μ.real Aᶜ = 1 - μ.real A
      simpa using measureReal_compl (μ := μ) hA
    simpa [bernoulliBool, sub_nonneg.mpr hp1, Set.preimage] using hcompl
  · simp [bernoulliBool, Set.preimage]
    rfl

open Classical in
-- @node: integral_eventCount_eq_binomial
/-- Under iid sampling, any function of an event count has the binomial expectation. This transports equation (4) from Boolean trials to actual observed-category counts. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hA), the [stated conclusion](goal) holds. -/
lemma integral_eventCount_eq_binomial {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Set Ω) (hA : MeasurableSet A)
    (n : ℕ) (F : ℕ → ℝ) :
    (∫ z : Fin n → Ω, F (Finset.univ.filter fun i => z i ∈ A).card
      ∂Measure.pi (fun _ => μ)) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n (μ.real A) k * F k := by
  classical
  let : IsProbabilityMeasure (bernoulliBool (μ.real A)) :=
    bernoulliBool_isProbabilityMeasure ENNReal.toReal_nonneg measureReal_le_one
  have hmp := measurePreserving_pi (fun _ : Fin n => μ)
    (fun _ => bernoulliBool (μ.real A))
    (fun _ => eventIndicator_measurePreserving μ A hA)
  rw [← integral_boolCount_eq_binomial n (μ.real A) ENNReal.toReal_nonneg measureReal_le_one F]
  rw [← hmp.map_eq, integral_map_of_stronglyMeasurable hmp.measurable
    (Measurable.of_discrete.stronglyMeasurable)]
  simp

-- @node: armEvent_mass_eq_armMass
/-- The event selecting one covariate cell and treatment arm has mass equal to its atom sum. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma armEvent_mass_eq_armMass {d : ℕ} (P : DiscreteLaw d) (x : Fin d) (a : Bool) :
    P.pmf.toMeasure.real {z : Obs d | z.1 = x ∧ z.2.1 = a} = armMass P a x := by
  classical
  rw [← integral_indicator_one (Set.toFinite _).measurableSet, PMF.integral_eq_sum]
  cases a <;>
    simp [Set.indicator, Fintype.sum_prod_type, armMass, jointMass, smul_eq_mul,
      Finset.sum_add_distrib]

-- @node: integral_sampleArmCount_eq_binomial
/-- The observed arm count has the binomial expectation formula under the actual iid law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_sampleArmCount_eq_binomial {n d : ℕ}
    (P : DiscreteLaw d) (x : Fin d) (a : Bool) (F : ℕ → ℝ) :
    (∫ o, F (sampleArmCount o x a) ∂productLaw P n) =
      ∑ k ∈ Finset.range (n + 1), binomialWeight n (armMass P a x) k * F k := by
  classical
  have h := integral_eventCount_eq_binomial P.pmf.toMeasure
    {z : Obs d | z.1 = x ∧ z.2.1 = a} (Set.toFinite _).measurableSet n F
  rw [armEvent_mass_eq_armMass] at h
  have hc (o : Fin n → Obs d) :
      (Finset.univ.filter fun i => o i ∈ {z : Obs d | z.1 = x ∧ z.2.1 = a}).card =
        sampleArmCount o x a := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    rfl
  calc
    _ = ∫ o : Fin n → Obs d,
        F (Finset.univ.filter fun i => o i ∈ {z : Obs d | z.1 = x ∧ z.2.1 = a}).card
        ∂productLaw P n := by
      apply integral_congr_ae
      filter_upwards [] with o
      exact congrArg F (hc o).symm
    _ = _ := by
      convert h using 1
      simp only [productLaw]
      apply integral_congr_ae
      filter_upwards [] with o
      congr 2
      ext i
      simp

-- @node: integral_sampleArmCount_inverse_le
/-- Equation (4)'s occupied-count reciprocal bound for an observed cell and arm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma integral_sampleArmCount_inverse_le {n d : ℕ}
    (P : DiscreteLaw d) (x : Fin d) (a : Bool) (hp : 0 < armMass P a x) :
    (∫ o, if 0 < sampleArmCount o x a then (sampleArmCount o x a : ℝ)⁻¹ else 0
      ∂productLaw P n) ≤ 2 / ((n + 1 : ℝ) * armMass P a x) := by
  have hp1 : armMass P a x ≤ 1 := by
    rw [← armEvent_mass_eq_armMass P x a]
    exact measureReal_le_one
  rw [integral_sampleArmCount_eq_binomial P x a (fun k => if 0 < k then (k : ℝ)⁻¹ else 0)]
  simpa only [Nat.cast_add, Nat.cast_one] using
    binomial_totalized_inverse_count_le n (armMass P a x) hp hp1

-- @node: integral_sampleArmCount_empty_eq
/-- Empty observed arms have the exact binomial zero probability, including null arms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_sampleArmCount_empty_eq {n d : ℕ}
    (P : DiscreteLaw d) (x : Fin d) (a : Bool) :
    (∫ o, if sampleArmCount o x a = 0 then (1 : ℝ) else 0 ∂productLaw P n) =
      (1 - armMass P a x) ^ n := by
  rw [integral_sampleArmCount_eq_binomial P x a (fun k => if k = 0 then 1 else 0)]
  simp [binomialWeight]

-- @node: integral_sampleArmCount_empty_le
/-- Equation (4)'s empty-arm probability bound holds for every occupied observed arm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hp), the [stated conclusion](goal) holds. -/
lemma integral_sampleArmCount_empty_le {n d : ℕ}
    (P : DiscreteLaw d) (x : Fin d) (a : Bool) (hp : 0 < armMass P a x) :
    (∫ o, if sampleArmCount o x a = 0 then (1 : ℝ) else 0 ∂productLaw P n) ≤
      1 / ((n + 1 : ℝ) * armMass P a x) := by
  rw [integral_sampleArmCount_empty_eq]
  apply binomial_empty_probability_le n (armMass P a x) hp
  rw [← armEvent_mass_eq_armMass P x a]
  exact measureReal_le_one

end CausalSmith.Stat.OptvalueVanishingoverlapRate
