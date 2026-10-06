module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperCap
public import Causalean.Mathlib.Probability.BernoulliMeasure
public import Causalean.Mathlib.Probability.Poisson.FinitePartition

/-! # Marked Poissonization of the observable estimator

Roadmap equations (7)–(8) use iid observation–fair-mark pairs, stopped at an
independent Poisson count. The statistic below is the uncapped version of the
actual capped statistic, with intensity fixed by the original sample size.
Its fixed-count fibres and prefix identities connect that experiment to the
finite Rao–Blackwell sum in equation (37).
-/

@[expose] public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open Causalean.Mathlib.Probability
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.Probability.Poisson.FinitePartition.CappedPrefix
open scoped BigOperators NNReal


-- @node: fairBool_isProbabilityMeasure
/-- Fair Boolean marks form a probability law.

For no explicit parameters, [fairBool_isProbabilityMeasure](goal) is the object specified by this definition. -/
instance fairBool_isProbabilityMeasure : IsProbabilityMeasure (bernoulliBool (1 / 2)) :=
  bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)


-- @node: markedPoissonStatistic
/-- The uncapped statistic uses all pairs in a finite marked sample, while
retaining the intensity and degree chosen from the original sample size.

For [the displayed parameters](hyp:n,d,H₀,hH₀,s), [markedPoissonStatistic](goal) is the object specified by this definition. -/
noncomputable def markedPoissonStatistic (n d : ℕ) (H₀ : ℝ) (hH₀ : 0 < H₀)
    (κ ε : ℝ) (s : FiniteSample (Obs d × Bool)) : ℝ :=
  projectUnit <| ∑ x : Fin d,
      let Np := markedCount (le_refl s.1) (fun i => (s.2 i).1)
        (fun i => (s.2 i).2) true x
      let Ne := markedCount (le_refl s.1) (fun i => (s.2 i).1)
        (fun i => (s.2 i).2) false x
      clippedCellValueFormula ε (jacksonDegree κ d) d (poissonIntensityFormula n)
        (pilotMidpoint H₀ hH₀ (poissonIntensityFormula n) (logAlphabet d) Np)
        (pilotRadiusFormula H₀ hH₀ (poissonIntensityFormula n) (logAlphabet d) Np) Ne


-- @node: markedPoissonStatistic_mem_unitInterval
/-- The marked statistic has unit range even when its count exceeds the sample cap. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_mem_unitInterval (n d : ℕ) (H₀ : ℝ)
    (hH₀ : 0 < H₀) (κ ε : ℝ) (s : FiniteSample (Obs d × Bool)) :
    0 ≤ markedPoissonStatistic n d H₀ hH₀ κ ε s ∧
      markedPoissonStatistic n d H₀ hH₀ κ ε s ≤ 1 :=
  projectUnit_mem_unitInterval _

/-- Reading the statistic is measurable on the countable finite-sample space. Under [the stated hypotheses](hyp:H₀,hH₀), the [stated conclusion](goal) holds. -/
-- @node: markedPoissonStatistic_measurable
@[fun_prop] lemma markedPoissonStatistic_measurable (n d : ℕ) (H₀ : ℝ)
    (hH₀ : 0 < H₀) (κ ε : ℝ) :
    Measurable (markedPoissonStatistic n d H₀ hH₀ κ ε) := by
  intro A hA
  rw [MeasurableSpace.measurableSet_iInf]
  intro k
  change MeasurableSet ((fun z : Fin k → Obs d × Bool =>
    markedPoissonStatistic n d H₀ hH₀ κ ε ⟨k, z⟩) ⁻¹' A)
  exact Measurable.of_discrete hA


-- @node: markedPoissonStatistic_sq_integrable
/-- Boundedness supplies squared-loss integrability without an added regularity premise. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_sq_integrable (n d : ℕ) (H₀ : ℝ)
    (hH₀ : 0 < H₀) (κ ε t : ℝ)
    (μ : Measure (FiniteSample (Obs d × Bool))) [IsFiniteMeasure μ] :
    Integrable (fun s => (markedPoissonStatistic n d H₀ hH₀ κ ε s - t) ^ 2) μ := by
  apply Integrable.of_bound (by fun_prop) ((1 + |t|) ^ 2)
  filter_upwards [] with s
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hv := markedPoissonStatistic_mem_unitInterval n d H₀ hH₀ κ ε s
  have ha : |markedPoissonStatistic n d H₀ hH₀ κ ε s - t| ≤ 1 + |t| := by
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg hv.1]; linarith [hv.2])
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) ha 2

/-- Below the cap, the uncapped marked statistic equals the implemented capped statistic on the first k observations and their marks. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hk,H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_prefix_eq {n d k : ℕ} (hk : k ≤ n)
    (H₀ : ℝ) (hH₀ : 0 < H₀) (κ ε : ℝ)
    (o : Fin n → Obs d) (marks : Fin n → Bool) :
    markedPoissonStatistic n d H₀ hH₀ κ ε
      (prefixOfLE (fun i => (o i, marks i)) k hk) =
    cappedStatisticFormula hk H₀ hH₀ κ ε o
      (fun i => marks ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) := by
  simp only [markedPoissonStatistic, prefixOfLE, cappedStatisticFormula]
  congr 1


-- @node: fairMarkLaw_singleton_real
/-- Fair Boolean marks have constant singleton mass, including the empty array. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma fairMarkLaw_singleton_real (k : ℕ) (marks : Fin k → Bool) :
    (Measure.pi (fun _ : Fin k => bernoulliBool (1 / 2))).real {marks} =
      (1 / 2 : ℝ) ^ k := by
  let : IsProbabilityMeasure (bernoulliBool (1 / 2)) :=
    bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  have hm (i : Fin k) : (bernoulliBool (1 / 2) {marks i}).toReal = (1 / 2 : ℝ) := by
    cases marks i <;> norm_num [bernoulliBool]
  simp only [hm, Finset.prod_const, Finset.card_univ, Fintype.card_fin]


-- @node: integral_fairMarks_eq_sum
/-- Integrating independent fair marks is exactly the finite average used by the observable estimator. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_fairMarks_eq_sum (k : ℕ) (f : (Fin k → Bool) → ℝ) :
    (∫ marks, f marks ∂Measure.pi (fun _ : Fin k => bernoulliBool (1 / 2))) =
      ∑ marks, (1 / 2 : ℝ) ^ k * f marks := by
  let : IsProbabilityMeasure (bernoulliBool (1 / 2)) :=
    bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)
  rw [integral_fintype Integrable.of_finite]
  simp only [fairMarkLaw_singleton_real, smul_eq_mul]


-- @node: integral_iid_observation_fairMarks
/-- Iid observation–mark pairs integrate as a finite fair-mark average of iid observation expectations. This identifies the auxiliary averaging law exactly. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_iid_observation_fairMarks {d : ℕ} (P : DiscreteLaw d)
    (k : ℕ) (f : (Fin k → Obs d) → (Fin k → Bool) → ℝ) :
    (∫ z : Fin k → Obs d × Bool,
      f (fun i => (z i).1) (fun i => (z i).2)
      ∂Measure.pi (fun _ => P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))) =
    ∑ marks, (1 / 2 : ℝ) ^ k * ∫ o, f o marks ∂productLaw P k := by
  let : IsProbabilityMeasure (bernoulliBool (1 / 2)) :=
    bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)
  have hmp := measurePreserving_arrowProdEquivProdArrow (Obs d) Bool (Fin k)
    (fun _ => P.pmf.toMeasure) (fun _ => bernoulliBool (1 / 2))
  have he := integral_map_of_stronglyMeasurable
    (μ := Measure.pi (fun _ : Fin k => P.pmf.toMeasure.prod (bernoulliBool (1 / 2))))
    hmp.measurable
    (Measurable.of_discrete (f := fun z => f z.1 z.2)).stronglyMeasurable
  rw [hmp.map_eq] at he
  simp only [MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk] at he
  rw [← he, integral_prod_symm _ Integrable.of_finite,
    integral_fairMarks_eq_sum]
  rfl


-- @node: fairMarkPrefix_map_eq
/-- Taking the first k fair marks from n fair marks preserves their product law. This removes unused marks from each count fibre. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hk), the [stated conclusion](goal) holds. -/
lemma fairMarkPrefix_map_eq {n k : ℕ} (hk : k ≤ n) :
    Measure.map (fun marks : Fin n → Bool => fun i : Fin k =>
      marks ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)
      (Measure.pi (fun _ : Fin n => bernoulliBool (1 / 2))) =
    Measure.pi (fun _ : Fin k => bernoulliBool (1 / 2)) := by
  rw [← iidStreamLaw_map_finPrefix (bernoulliBool (1 / 2)) n,
    Measure.map_map (by fun_prop) (by fun_prop)]
  exact iidStreamLaw_map_finPrefix (bernoulliBool (1 / 2)) k


-- @node: fairMark_average_prefix_eq
/-- The finite fair-mark average of a prefix statistic is independent of how many unused fair marks are appended. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hk), the [stated conclusion](goal) holds. -/
lemma fairMark_average_prefix_eq {n k : ℕ} (hk : k ≤ n)
    (f : (Fin k → Bool) → ℝ) :
    (∑ marks : Fin n → Bool, (1 / 2 : ℝ) ^ n *
      f (fun i => marks ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)) =
    ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k * f marks := by
  rw [← integral_fairMarks_eq_sum, ← integral_fairMarks_eq_sum,
    ← fairMarkPrefix_map_eq hk]
  exact (integral_map_of_stronglyMeasurable (by fun_prop)
    Measurable.of_discrete.stronglyMeasurable).symm

/-- On a count fibre that fits the sample, the marked Poisson squared-loss integral is its Poisson mass times the exact fair-mark average of capped risk. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hk,H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_count_fibre_sqRisk_eq {n d k : ℕ} (hk : k ≤ n)
    (H₀ : ℝ) (hH₀ : 0 < H₀) (κ ε t : ℝ) (P : DiscreteLaw d) :
    (∫ s : FiniteSample (Obs d × Bool) in FiniteSample.count ⁻¹' ({k} : Set ℕ),
      (markedPoissonStatistic n d H₀ hH₀ κ ε s - t) ^ 2
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) =
    poissonWeight (n / 4) k * ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k *
      Causalean.Stat.sqRisk (productLaw P n)
        (fun o => cappedStatisticFormula hk H₀ hH₀ κ ε o marks) t := by
  let : IsProbabilityMeasure (bernoulliBool (1 / 2)) :=
    bernoulliBool_isProbabilityMeasure (by norm_num) (by norm_num)
  rw [poisson_prefix_count_fibre_integral _ _ n k hk _
    (markedPoissonStatistic_sq_integrable n d H₀ hH₀ κ ε t _)]
  simp_rw [markedPoissonStatistic_prefix_eq hk]
  rw [integral_iid_observation_fairMarks P n (fun o marks =>
    (cappedStatisticFormula hk H₀ hH₀ κ ε o
      (fun i => marks ⟨i.val, lt_of_lt_of_le i.isLt hk⟩) - t) ^ 2)]
  rw [show ((ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4)) {k}).toReal =
      poissonWeight (n / 4) k by
    simp only [ProbabilityTheory.poissonMeasure_singleton, NNReal.coe_div,
      NNReal.coe_natCast, NNReal.coe_ofNat, poissonWeight, ENNReal.toReal_ofReal_eq_iff]
    positivity]
  congr 1
  exact fairMark_average_prefix_eq hk (fun marks =>
    Causalean.Stat.sqRisk (productLaw P n)
      (fun o => cappedStatisticFormula hk H₀ hH₀ κ ε o marks) t)

/-- The count-capped part of the Poisson risk is the weighted auxiliary risk appearing in the finite Rao–Blackwell inequality, with no unused marks. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:H₀,hH₀), the [stated conclusion](goal) holds. -/
lemma markedPoissonStatistic_nonoverflow_sqRisk_eq (n d : ℕ) (H₀ : ℝ)
    (hH₀ : 0 < H₀) (κ ε t : ℝ) (P : DiscreteLaw d) :
    (∫ s : FiniteSample (Obs d × Bool),
      if s.count ≤ n then (markedPoissonStatistic n d H₀ hH₀ κ ε s - t) ^ 2 else 0
      ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4)) =
    ∑ k ∈ Finset.range (n + 1), if hk : k ≤ n then
      poissonWeight (n / 4) k * ∑ marks : Fin k → Bool, (1 / 2 : ℝ) ^ k *
        Causalean.Stat.sqRisk (productLaw P n)
          (fun o => cappedStatisticFormula hk H₀ hH₀ κ ε o marks) t else 0 := by
  rw [poisson_nonoverflow_integral_eq_sum_count_fibres _ _ n _
    (markedPoissonStatistic_sq_integrable n d H₀ hH₀ κ ε t _)]
  have hf (k : Fin (n + 1)) := markedPoissonStatistic_count_fibre_sqRisk_eq
    (Nat.le_of_lt_succ k.isLt) H₀ hH₀ κ ε t P
  simp_rw [hf]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [dif_pos (Nat.le_of_lt_succ k.isLt)]


-- @node: poissonWeight_quarter_missing_mass_le
/-- The missing mass in the finite count average is the quarter-mean Poisson overflow probability, so equation (35) applies to the implemented weights. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma poissonWeight_quarter_missing_mass_le (n : ℕ) :
    1 - ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k ≤
      Real.exp (-(n : ℝ) / 2) := by
  let μ := ProbabilityTheory.poissonMeasure ((n : ℝ≥0) / 4)
  have hw (k : ℕ) : μ.real {k} = poissonWeight (n / 4) k := by
    simp only [μ, measureReal_def, ProbabilityTheory.poissonMeasure_singleton,
      NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat, poissonWeight,
      ENNReal.toReal_ofReal_eq_iff]
    positivity
  have hs : μ.real (Set.Iic n) = ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k := by
    rw [show Set.Iic n = (Finset.range (n + 1) : Set ℕ) by
      ext k; simp only [Set.mem_Iic, Finset.mem_coe, Finset.mem_range]; omega,
      ← sum_measureReal_singleton]
    simp_rw [hw]
  have hc : μ.real (Set.Ioi n) = 1 - μ.real (Set.Iic n) := by
    simpa only [Set.compl_Iic, probReal_univ] using
      (measureReal_compl (μ := μ) measurableSet_Iic)
  rw [← hs, ← hc]
  exact quarterPoisson_overflow_prob_le μ n id
    ⟨measurable_id.aemeasurable, by simp [μ]⟩

/-- Equation (37) and restoration of the cap for the actual implemented estimator. Its fixed-sample risk is bounded by the uncapped marked Poisson risk plus the exponential cap penalty; no auxiliary risk bound is assumed. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hd,hactive), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_active_le_markedPoisson_sqRisk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hd : D₀ ≤ d)
    (hactive : (d : ℝ) / logAlphabet d ≤ (n : ℝ) * ε) (P : DiscreteLaw d) :
    Causalean.Stat.sqRisk (productLaw P n)
      (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) (observedValue P) ≤
    Causalean.Stat.sqRisk
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))
      (markedPoissonStatistic n d H₀ hH₀ κ ε) (observedValue P) +
      Real.exp (-(n : ℝ) / 2) := by
  let : IsProbabilityMeasure (productLaw P n) := by dsimp [productLaw]; infer_instance
  have hr := armwiseEstimator_active_sqRisk_le H₀ κ D₀ hH₀ hκ hD₀
    hd hactive P (productLaw P n)
  rw [← markedPoissonStatistic_nonoverflow_sqRisk_eq n d H₀ hH₀ κ ε (observedValue P) P] at hr
  have hnonoverflow :
      (∫ s : FiniteSample (Obs d × Bool),
        if s.count ≤ n then
          (markedPoissonStatistic n d H₀ hH₀ κ ε s - observedValue P) ^ 2 else 0
        ∂finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
          ((n : ℝ≥0) / 4)) ≤
      Causalean.Stat.sqRisk
        (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
          ((n : ℝ≥0) / 4))
        (markedPoissonStatistic n d H₀ hH₀ κ ε) (observedValue P) := by
    have hi := markedPoissonStatistic_sq_integrable n d H₀ hH₀ κ ε (observedValue P)
      (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
        ((n : ℝ≥0) / 4))
    have hiCap : Integrable (fun s : FiniteSample (Obs d × Bool) =>
        if s.count ≤ n then
          (markedPoissonStatistic n d H₀ hH₀ κ ε s - observedValue P) ^ 2 else 0)
        (finitePoissonSampleLaw (P.pmf.toMeasure.prod (bernoulliBool (1 / 2)))
          ((n : ℝ≥0) / 4)) := by
      have heq : (fun s : FiniteSample (Obs d × Bool) =>
          if s.count ≤ n then
            (markedPoissonStatistic n d H₀ hH₀ κ ε s - observedValue P) ^ 2 else 0) =
          (FiniteSample.count ⁻¹' Set.Iic n).indicator (fun s =>
            (markedPoissonStatistic n d H₀ hH₀ κ ε s - observedValue P) ^ 2) := by
        funext s
        simp [Set.indicator]
      rw [heq]
      exact hi.indicator (measurable_finiteSample_count measurableSet_Iic)
    apply integral_mono hiCap hi
    intro s
    dsimp only
    split_ifs
    · rfl
    · exact sq_nonneg _
  have ht := observedValue_mem_unitInterval P
  have ht₂ : (observedValue P) ^ 2 ≤ 1 := by nlinarith
  have hm : 0 ≤ 1 - ∑ k ∈ Finset.range (n + 1), poissonWeight (n / 4) k :=
    sub_nonneg.mpr (poissonWeight_sum_le_one (by positivity) n)
  have htail := (mul_le_of_le_one_right hm ht₂).trans
    (poissonWeight_quarter_missing_mass_le n)
  exact hr.trans (add_le_add hnonoverflow htail)

end CausalSmith.Stat.OptvalueVanishingoverlapRate
