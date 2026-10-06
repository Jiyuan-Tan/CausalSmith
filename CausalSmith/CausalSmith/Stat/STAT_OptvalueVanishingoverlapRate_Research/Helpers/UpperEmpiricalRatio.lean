module
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.Estimator
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.Helpers.UpperClipping
public import CausalSmith.Stat.STAT_OptvalueVanishingoverlapRate_Research.TIdentification
public import Causalean.Mathlib.Analysis.WeightedCauchySchwarz
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! # Nonpolynomial upper-bound branches

The observed value lies in the unit interval, and the constant branch has risk
at most one quarter in the saturated regime. Empirical arm means stay in the
unit interval even for empty arms. The pathwise empirical-ratio error splits
into mass error and mass-weighted arm error, giving the two squared-loss terms
in roadmap equation (6) after projection. Weighted Cauchy–Schwarz reduces arm
error to individual second moments without excluding null cells. The iid
cell-indicator mean-square bound proves the mass term is at most `d / n`. -/

public section

namespace CausalSmith.Stat.OptvalueVanishingoverlapRate

open MeasureTheory
open scoped BigOperators


-- @node: cellMass_sum_eq_one
/-- The covariate cell masses of a finite observed probability law sum to one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma cellMass_sum_eq_one {d : ℕ} (P : DiscreteLaw d) :
    ∑ x : Fin d, cellMass P x = 1 := by
  have h := ENNReal.tsum_toReal_eq (fun z => P.pmf.apply_ne_top z)
  rw [P.pmf.tsum_coe] at h
  simpa [cellMass, jointMass, tsum_fintype, Fintype.sum_prod_type] using h.symm


-- @node: observedValue_mem_unitInterval
/-- The oracle observed value is between zero and one for every finite observed law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma observedValue_mem_unitInterval {d : ℕ} (P : DiscreteLaw d) :
    0 ≤ observedValue P ∧ observedValue P ≤ 1 := by
  have hp (x : Fin d) : 0 ≤ cellMass P x := by
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have hm (x : Fin d) :
      0 ≤ max (outcomeMean P false x) (outcomeMean P true x) ∧
      max (outcomeMean P false x) (outcomeMean P true x) ≤ 1 :=
    ⟨le_trans (outcomeMean_mem_unitInterval P false x).1 (le_max_left _ _),
      max_le (outcomeMean_mem_unitInterval P false x).2
        (outcomeMean_mem_unitInterval P true x).2⟩
  constructor
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hp x) (hm x).1
  · calc
      observedValue P ≤ ∑ x : Fin d, cellMass P x := by
        apply Finset.sum_le_sum
        intro x _
        simpa using mul_le_mul_of_nonneg_left (hm x).2 (hp x)
      _ = 1 := cellMass_sum_eq_one P


-- @node: halfEstimator_sqRisk_le_quarter
/-- The constant one-half estimator has squared risk at most one quarter. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma halfEstimator_sqRisk_le_quarter {d n : ℕ} (P : DiscreteLaw d)
    (μ : Measure (Fin n → Obs d)) [IsProbabilityMeasure μ] :
    Causalean.Stat.sqRisk μ (fun _ => 1 / 2) (observedValue P) ≤ 1 / 4 := by
  obtain ⟨hlo, hhi⟩ := observedValue_mem_unitInterval P
  have hprod : 0 ≤ observedValue P * (1 - observedValue P) :=
    mul_nonneg hlo (by linarith)
  simpa [Causalean.Stat.sqRisk] using
    (show (1 / 2 - observedValue P) ^ 2 ≤ (1 / 4 : ℝ) by nlinarith)


-- @node: logAlphabet_pos
/-- The logarithmic alphabet scale is positive for a nonempty alphabet. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hd), the [stated conclusion](goal) holds. -/
lemma logAlphabet_pos {d : ℕ} (hd : 1 ≤ d) : 0 < logAlphabet d := by
  apply Real.log_pos
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
  nlinarith [Real.exp_pos (1 : ℝ)]


-- @node: rateScale_eq_one_of_saturated
/-- On the constant branch the minimum-form rate scale is exactly one. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn,hd,hε,hsat), the [stated conclusion](goal) holds. -/
lemma rateScale_eq_one_of_saturated {n d : ℕ} {ε : ℝ}
    (hn : 1 ≤ n) (hd : 1 ≤ d) (hε : 0 < ε)
    (hsat : (n : ℝ) * ε < (d : ℝ) / logAlphabet d) :
    rateScale n d ε = 1 := by
  have hL := logAlphabet_pos hd
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hden : 0 < (n : ℝ) * ε * logAlphabet d := mul_pos (mul_pos hn' hε) hL
  have hnum : (n : ℝ) * ε * logAlphabet d < d := (lt_div_iff₀ hL).mp hsat
  exact min_eq_left ((lt_div_iff₀ hden).mpr (by simpa using hnum)).le

/-- The large-alphabet constant branch is measurable and has risk at most one quarter. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hd,hsat,hiid), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_saturated_risk (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hd : D₀ ≤ d)
    (hsat : (n : ℝ) * ε < (d : ℝ) / logAlphabet d)
    (P : DiscreteLaw d) (μ : Measure (Fin n → Obs d)) (hiid : IidSampling P μ) :
    Measurable (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) ∧
    Causalean.Stat.sqRisk μ
      (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) (observedValue P) ≤ 1 / 4 := by
  have heq : armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε = fun _ => 1 / 2 := by
    funext o
    simp [armwiseEstimatorFormula, not_lt.mpr hd, hsat]
  rw [heq]
  constructor
  · fun_prop
  · have hμ : μ = productLaw P n := hiid
    subst μ
    let : IsProbabilityMeasure (productLaw P n) := by
      dsimp [productLaw]
      infer_instance
    exact halfEstimator_sqRisk_le_quarter P (productLaw P n)

/-- The saturated branch satisfies the desired minimum-form risk bound with constant one quarter. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hH₀,hκ,hD₀,hn,hd,hε,hsat,hiid), the [stated conclusion](goal) holds. -/
lemma armwiseEstimator_saturated_rate_bound (H₀ κ : ℝ) (D₀ : ℕ)
    (hH₀ : 0 < H₀) (hκ : 0 < κ) (hD₀ : 2 ≤ D₀)
    {n d : ℕ} {ε : ℝ} (hn : 1 ≤ n) (hd : D₀ ≤ d) (hε : 0 < ε)
    (hsat : (n : ℝ) * ε < (d : ℝ) / logAlphabet d)
    (P : DiscreteLaw d) (μ : Measure (Fin n → Obs d)) (hiid : IidSampling P μ) :
    Causalean.Stat.sqRisk μ
      (armwiseEstimatorFormula H₀ κ D₀ hH₀ hκ hD₀ n d ε) (observedValue P) ≤
      (1 / 4 : ℝ) * rateScale n d ε := by
  rw [rateScale_eq_one_of_saturated hn (by omega) hε hsat, mul_one]
  exact (armwiseEstimator_saturated_risk H₀ κ D₀ hH₀ hκ hD₀ hd hsat P μ hiid).2


-- @node: sampleSuccessCount_le_sampleArmCount
/-- Successes form a subset of the observations in each treatment arm. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma sampleSuccessCount_le_sampleArmCount {n d : ℕ} (o : Fin n → Obs d)
    (x : Fin d) (a : Bool) : sampleSuccessCount o x a ≤ sampleArmCount o x a := by
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : (o i).1 = x ∧ (o i).2.1 = a ∧ (o i).2.2 = true
  · rw [if_pos h, if_pos ⟨h.1, h.2.1⟩]
  · rw [if_neg h]
    exact Nat.zero_le _


-- @node: empiricalOutcomeMean_mem_unitInterval
/-- The empirical arm mean lies in the unit interval, including empty arms. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalOutcomeMean_mem_unitInterval {n d : ℕ} (o : Fin n → Obs d)
    (x : Fin d) (a : Bool) :
    0 ≤ (sampleSuccessCount o x a : ℝ) / sampleArmCount o x a ∧
    (sampleSuccessCount o x a : ℝ) / sampleArmCount o x a ≤ 1 := by
  constructor
  · positivity
  · exact div_le_one_of_le₀ (by exact_mod_cast sampleSuccessCount_le_sampleArmCount o x a)
      (Nat.cast_nonneg _)


-- @node: empiricalArmMax_mem_unitInterval
/-- The two empirical arm means have a maximum in the unit interval. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalArmMax_mem_unitInterval {n d : ℕ} (o : Fin n → Obs d)
    (x : Fin d) :
    let v := max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false)
      ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true)
    0 ≤ v ∧ v ≤ 1 := by
  exact ⟨le_trans (empiricalOutcomeMean_mem_unitInterval o x false).1 (le_max_left _ _),
    max_le (empiricalOutcomeMean_mem_unitInterval o x false).2
      (empiricalOutcomeMean_mem_unitInterval o x true).2⟩


-- @node: empiricalCell_abs_error_le
/-- The cell error splits into empirical mass error and mass-weighted arm error. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalCell_abs_error_le {n d : ℕ} (o : Fin n → Obs d)
    (P : DiscreteLaw d) (x : Fin d) :
    let v := max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false)
      ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true)
    |(sampleCellCount o x : ℝ) / n * v -
      cellMass P x * max (outcomeMean P false x) (outcomeMean P true x)| ≤
      |(sampleCellCount o x : ℝ) / n - cellMass P x| + cellMass P x *
        max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
          |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x| := by
  dsimp only
  let v := max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false)
    ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true)
  let w := max (outcomeMean P false x) (outcomeMean P true x)
  have hp : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have hv := empiricalArmMax_mem_unitInterval o x
  change |(sampleCellCount o x : ℝ) / n * v - cellMass P x * w| ≤ _
  calc
    _ = |((sampleCellCount o x : ℝ) / n - cellMass P x) * v +
        cellMass P x * (v - w)| := by congr 1; ring
    _ ≤ |((sampleCellCount o x : ℝ) / n - cellMass P x) * v| +
        |cellMass P x * (v - w)| := abs_add_le _ _
    _ ≤ |(sampleCellCount o x : ℝ) / n - cellMass P x| + cellMass P x *
        max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
          |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hv.1, abs_of_nonneg hp]
      apply add_le_add
      · exact mul_le_of_le_one_right (abs_nonneg _) hv.2
      · exact mul_le_mul_of_nonneg_left (abs_max_sub_max_le_max _ _ _ _) hp


-- @node: empiricalRawValue_abs_error_le
/-- Summing the cell bounds gives the pathwise decomposition preceding equation (6). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalRawValue_abs_error_le {n d : ℕ} (o : Fin n → Obs d)
    (P : DiscreteLaw d) :
    |(∑ x : Fin d, (sampleCellCount o x : ℝ) / n *
      max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false)
        ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true)) - observedValue P| ≤
      (∑ x : Fin d, |(sampleCellCount o x : ℝ) / n - cellMass P x|) +
      ∑ x : Fin d, cellMass P x *
        max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
          |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x| := by
  rw [observedValue, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun x _ => empiricalCell_abs_error_le o P x)


-- @node: empiricalValue_sq_error_le_components
/-- Projection and the pathwise decomposition reduce squared loss to the two terms in (6). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalValue_sq_error_le_components {n d : ℕ} (o : Fin n → Obs d)
    (P : DiscreteLaw d) :
    let A := ∑ x : Fin d, |(sampleCellCount o x : ℝ) / n - cellMass P x|
    let B := ∑ x : Fin d, cellMass P x *
      max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
        |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x|
    (empiricalValue o - observedValue P) ^ 2 ≤ 2 * A ^ 2 + 2 * B ^ 2 := by
  dsimp only
  let T := ∑ x : Fin d, (sampleCellCount o x : ℝ) / n *
    max ((sampleSuccessCount o x false : ℝ) / sampleArmCount o x false)
      ((sampleSuccessCount o x true : ℝ) / sampleArmCount o x true)
  let A := ∑ x : Fin d, |(sampleCellCount o x : ℝ) / n - cellMass P x|
  let B := ∑ x : Fin d, cellMass P x *
    max |(sampleSuccessCount o x false : ℝ) / sampleArmCount o x false - outcomeMean P false x|
      |(sampleSuccessCount o x true : ℝ) / sampleArmCount o x true - outcomeMean P true x|
  have hA : 0 ≤ A := Finset.sum_nonneg fun x _ => abs_nonneg _
  have hB : 0 ≤ B := by
    apply Finset.sum_nonneg
    intro x hx
    apply mul_nonneg
    · exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
    · exact le_trans (abs_nonneg _) (le_max_left _ _)
  have habs : |T - observedValue P| ≤ A + B := empiricalRawValue_abs_error_le o P
  have hsq : (T - observedValue P) ^ 2 ≤ (A + B) ^ 2 := by
    simpa only [← pow_two, sq_abs] using
      mul_self_le_mul_self (abs_nonneg (T - observedValue P)) habs
  have hp := observedValue_mem_unitInterval P
  calc
    (empiricalValue o - observedValue P) ^ 2 ≤ (T - observedValue P) ^ 2 :=
      projectUnit_sq_error_le hp
    _ ≤ 2 * A ^ 2 + 2 * B ^ 2 := by nlinarith [sq_nonneg (A - B)]



-- @node: empiricalMassError_sq_le
/-- Cauchy–Schwarz bounds the squared total mass error by the sum of cellwise errors. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalMassError_sq_le {n d : ℕ} (o : Fin n → Obs d)
    (P : DiscreteLaw d) :
    (∑ x : Fin d, |(sampleCellCount o x : ℝ) / n - cellMass P x|) ^ 2 ≤
      (d : ℝ) * ∑ x : Fin d, ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun _ => (1 : ℝ)) (fun x => |(sampleCellCount o x : ℝ) / n - cellMass P x|)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, sq_abs] using h


-- @node: cellMass_weighted_armMax_sq_le
/-- Probability-weighted Cauchy–Schwarz controls the arm error without dividing by cell masses. In particular, null cells contribute zero. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma cellMass_weighted_armMax_sq_le {d : ℕ} (P : DiscreteLaw d)
    (e : Bool → Fin d → ℝ) :
    (∑ x : Fin d, cellMass P x * max |e false x| |e true x|) ^ 2 ≤
      ∑ x : Fin d, cellMass P x * ∑ a : Bool, (e a x) ^ 2 := by
  have hp (x : Fin d) : 0 ≤ cellMass P x :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun y _ => ENNReal.toReal_nonneg
  have h := Causalean.Mathlib.Analysis.weighted_inner_sq_le Finset.univ
    (cellMass P) (fun _ => 1) (fun x => max |e false x| |e true x|)
    (fun x _ => hp x)
  simp only [one_mul, one_pow, mul_one, cellMass_sum_eq_one] at h
  apply h.trans
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (hp x)
  simp only [Fintype.sum_bool]
  rcases le_total |e false x| |e true x| with he | he
  · rw [max_eq_right he, sq_abs]
    nlinarith [sq_nonneg (e false x)]
  · rw [max_eq_left he, sq_abs]
    nlinarith [sq_nonneg (e true x)]


-- @node: empiricalValue_sq_error_le_cellwise
/-- The projected empirical statistic is controlled by individual mass and arm squared errors, as required for the expectation bounds in equation (6). In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalValue_sq_error_le_cellwise {n d : ℕ} (o : Fin n → Obs d)
    (P : DiscreteLaw d) :
    (empiricalValue o - observedValue P) ^ 2 ≤
      2 * ((d : ℝ) * ∑ x : Fin d,
        ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2) +
      2 * ∑ x : Fin d, cellMass P x * ∑ a : Bool,
        ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2 := by
  apply (empiricalValue_sq_error_le_components o P).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (empiricalMassError_sq_le o P) (by norm_num)
  · exact mul_le_mul_of_nonneg_left
      (cellMass_weighted_armMax_sq_le P (fun a x =>
        (sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x))
      (by norm_num)


-- @node: empiricalValue_sqRisk_le_cellwise
/-- Integrating the cellwise inequality reduces empirical-ratio risk to marginal second moments. All integrability conditions are automatic on the finite observed sample space. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma empiricalValue_sqRisk_le_cellwise {n d : ℕ} (P : DiscreteLaw d)
    (μ : Measure (Fin n → Obs d)) [IsFiniteMeasure μ] :
    Causalean.Stat.sqRisk μ empiricalValue (observedValue P) ≤
      2 * ((d : ℝ) * ∑ x : Fin d, ∫ o,
        ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2 ∂μ) +
      2 * ∑ x : Fin d, cellMass P x * ∑ a : Bool, ∫ o,
        ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2 ∂μ := by
  unfold Causalean.Stat.sqRisk
  calc
    _ ≤ ∫ o, (2 * ((d : ℝ) * ∑ x : Fin d,
        ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2) +
      2 * ∑ x : Fin d, cellMass P x * ∑ a : Bool,
        ((sampleSuccessCount o x a : ℝ) / sampleArmCount o x a - outcomeMean P a x) ^ 2) ∂μ :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun o => empiricalValue_sq_error_le_cellwise o P)
    _ = _ := by
      rw [integral_add Integrable.of_finite Integrable.of_finite]
      simp only [integral_const_mul]
      congr 1
      · congr 1
        congr 1
        exact integral_finsetSum _ (fun _ _ => Integrable.of_finite)
      · congr 1
        rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
        apply Finset.sum_congr rfl
        intro x hx
        rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]



-- @node: integral_cellIndicator_eq_cellMass
/-- The one-observation indicator of a covariate cell has mean equal to its cell mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. The [stated conclusion](goal) holds. -/
lemma integral_cellIndicator_eq_cellMass {d : ℕ} (P : DiscreteLaw d) (x : Fin d) :
    (∫ z : Obs d, (if z.1 = x then (1 : ℝ) else 0) ∂P.pmf.toMeasure) =
      cellMass P x := by
  rw [PMF.integral_eq_sum]
  simp [Fintype.sum_prod_type, cellMass, jointMass, smul_eq_mul, Finset.sum_add_distrib]


-- @node: empiricalCellMass_mse_le
/-- Under iid sampling, each empirical cell mass has mean squared error at most its mass over n. The bound also holds for null cells, without a positivity assumption on their mass. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn), the [stated conclusion](goal) holds. -/
lemma empiricalCellMass_mse_le {n d : ℕ} (hn : 0 < n)
    (P : DiscreteLaw d) (x : Fin d) :
    (∫ o, ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2 ∂productLaw P n) ≤
      cellMass P x / n := by
  let f : Obs d → ℝ := fun z => if z.1 = x then 1 else 0
  have hf : MemLp f 2 P.pmf.toMeasure := by
    apply (memLp_two_iff_integrable_sq ?_).2 Integrable.of_finite
    fun_prop
  have hm : (∫ z, f z ∂P.pmf.toMeasure) = cellMass P x :=
    integral_cellIndicator_eq_cellMass P x
  have hs : (∫ z, (f z) ^ 2 ∂P.pmf.toMeasure) = cellMass P x := by
    have heq : (fun z => (f z) ^ 2) = f := by
      funext z
      simp only [f]
      split_ifs <;> norm_num
    rw [heq, hm]
  have hc (o : Fin n → Obs d) : (sampleCellCount o x : ℝ) = ∑ i : Fin n, f (o i) := by
    simp [sampleCellCount, f]
  have h := Causalean.Mathlib.Probability.iid_mean_sq_le P.pmf.toMeasure hn f hf
  rw [hm, hs] at h
  simpa only [productLaw, hc, div_eq_mul_inv, mul_comm] using h


-- @node: empiricalMassError_mse_le
/-- Equation (6)'s mass-error term is bounded by d/n under the actual iid observed law. In the econometric construction, the displayed inputs and assumptions imply the stated mathematical conclusion. Under [the stated hypotheses](hyp:hn), the [stated conclusion](goal) holds. -/
lemma empiricalMassError_mse_le {n d : ℕ} (hn : 0 < n) (P : DiscreteLaw d) :
    (∫ o, (∑ x : Fin d, |(sampleCellCount o x : ℝ) / n - cellMass P x|) ^ 2
      ∂productLaw P n) ≤ (d : ℝ) / n := by
  let : IsProbabilityMeasure (productLaw P n) := by
    dsimp [productLaw]
    infer_instance
  calc
    _ ≤ ∫ o, (d : ℝ) * ∑ x : Fin d,
        ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2 ∂productLaw P n :=
      integral_mono Integrable.of_finite Integrable.of_finite
        (fun o => empiricalMassError_sq_le o P)
    _ = (d : ℝ) * ∑ x : Fin d, ∫ o,
        ((sampleCellCount o x : ℝ) / n - cellMass P x) ^ 2 ∂productLaw P n := by
      rw [integral_const_mul, integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    _ ≤ (d : ℝ) * ∑ x : Fin d, cellMass P x / n := by
      gcongr with x
      exact empiricalCellMass_mse_le hn P x
    _ = (d : ℝ) / n := by rw [← Finset.sum_div, cellMass_sum_eq_one]; ring

end CausalSmith.Stat.OptvalueVanishingoverlapRate
