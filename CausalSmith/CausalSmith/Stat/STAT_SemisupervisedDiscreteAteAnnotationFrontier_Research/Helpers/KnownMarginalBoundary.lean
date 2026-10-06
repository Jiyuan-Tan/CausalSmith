module
public import CausalSmith.Stat.STAT_SemisupervisedDiscreteAteAnnotationFrontier_Research.Helpers.ParametricLabelFloor
public import Causalean.Mathlib.Probability.IidMeanVariance
public import Mathlib.Probability.Moments.Variance

/-! Finite-sample ingredients for the exact-known-marginal benchmark. -/

@[expose] public section

namespace CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier

open MeasureTheory ProbabilityTheory
open scoped BigOperators

-- @node: knownMarginalScore
/-- The inverse-propensity score, written directly in terms of the supplied table.  [the stated conditions](hyp:table,z) [the stated conclusion](goal). -/
noncomputable def knownMarginalScore {d : Nat} (table : AuxTable d) (z : Obs d) : Real :=
  let p := table (z.1, false) + table (z.1, true)
  if z.2.2 then
    if z.2.1 then p / table (z.1, true) else -(p / table (z.1, false))
  else 0

-- @node: knownMarginalEstimator
/-- The clipped empirical mean of the known-marginal inverse-propensity score.  [the stated conditions](hyp:n,d) [the stated conclusion](goal). -/
noncomputable def knownMarginalEstimator (n d : Nat) : KnownSample n d → Real :=
  fun z => clipAte ((n : Real)⁻¹ * ∑ i, knownMarginalScore z.2 (z.1 i))

-- @node: measurable_auxTable_sample_eval
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma measurable_auxTable_sample_eval {n d : Nat} (i : Fin n) (a : Bool) :
    Measurable fun z : KnownSample n d => z.2 ((z.1 i).1, a) := by
  classical
  rw [show (fun z : KnownSample n d => z.2 ((z.1 i).1, a)) =
      fun z => ∑ q : AuxObs d, if ((z.1 i).1, a) = q then z.2 q else 0 by
    funext z
    simp]
  apply Finset.measurable_sum
  intro q hq
  apply Measurable.ite
  · apply measurableSet_eq_fun
    · fun_prop
    · fun_prop
  · exact (measurable_pi_apply q).comp measurable_snd
  · fun_prop

-- @node: knownMarginalScore_sample_measurable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma knownMarginalScore_sample_measurable {n d : Nat} (i : Fin n) :
    Measurable fun z : KnownSample n d => knownMarginalScore z.2 (z.1 i) := by
  unfold knownMarginalScore
  apply Measurable.ite
  · apply measurableSet_eq_fun <;> fun_prop
  · apply Measurable.ite
    · apply measurableSet_eq_fun <;> fun_prop
    · exact ((measurable_auxTable_sample_eval i false).add
        (measurable_auxTable_sample_eval i true)).div
          (measurable_auxTable_sample_eval i true)
    · exact (((measurable_auxTable_sample_eval i false).add
        (measurable_auxTable_sample_eval i true)).div
          (measurable_auxTable_sample_eval i false)).neg
  · fun_prop

-- @node: knownMarginalEstimator_measurable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma knownMarginalEstimator_measurable (n d : Nat) :
    Measurable (knownMarginalEstimator n d) := by
  unfold knownMarginalEstimator clipAte
  apply measurable_const.max
  apply measurable_const.min
  apply measurable_const.mul
  exact Finset.measurable_sum _ fun i _ => knownMarginalScore_sample_measurable i

-- @node: knownMarginalEstimator_mem
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma knownMarginalEstimator_mem (n d : Nat) (z : KnownSample n d) :
    knownMarginalEstimator n d z ∈ Set.Icc (-1 : Real) 1 := by
  constructor <;> simp [knownMarginalEstimator, clipAte, max_le_iff]

-- @node: cellMass_eq_armMass_add
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma cellMass_eq_armMass_add {d : Nat} (P : DiscreteLaw d) (x : Fin d) :
    cellMass P x = armMass P x false + armMass P x true := by
  simp [cellMass, armMass]
  ring

-- @node: jointMass_nonneg
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma jointMass_nonneg {d : Nat} (P : DiscreteLaw d) (x : Fin d) (a y : Bool) :
    0 ≤ jointMass P x a y := by
  exact ENNReal.toReal_nonneg

-- @node: armMass_nonneg
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma armMass_nonneg {d : Nat} (P : DiscreteLaw d) (x : Fin d) (a : Bool) :
    0 ≤ armMass P x a := by
  exact Finset.sum_nonneg fun _ _ => jointMass_nonneg P x a _

-- @node: cellMass_nonneg
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma cellMass_nonneg {d : Nat} (P : DiscreteLaw d) (x : Fin d) :
    0 ≤ cellMass P x := by
  rw [cellMass_eq_armMass_add]
  exact add_nonneg (armMass_nonneg P x false) (armMass_nonneg P x true)

-- @node: jointMass_le_armMass
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma jointMass_le_armMass {d : Nat} (P : DiscreteLaw d) (x : Fin d) (a y : Bool) :
    jointMass P x a y ≤ armMass P x a := by
  simp [armMass]
  cases y <;> linarith [jointMass_nonneg P x a false, jointMass_nonneg P x a true]

-- @node: cellMass_sum_eq_one
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma cellMass_sum_eq_one {d : Nat} (P : DiscreteLaw d) :
    ∑ x : Fin d, cellMass P x = 1 := by
  classical
  have h := PMF.integral_eq_sum P.pmf (fun _ : Obs d => (1 : Real))
  rw [integral_const, probReal_univ, one_smul] at h
  simpa [cellMass, jointMass, Fintype.sum_prod_type] using h.symm

-- @node: knownMarginal_arm_bounds
/-- [the stated conditions](hyp:hP,hx) establishes [the stated conclusion](goal). -/
lemma knownMarginal_arm_bounds {d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) (x : Fin d) (hx : 0 < cellMass P x) :
    eps * cellMass P x ≤ armMass P x true ∧
      eps * cellMass P x ≤ armMass P x false := by
  have hp := hP.overlap x hx
  have hne : cellMass P x ≠ 0 := ne_of_gt hx
  have ht : armMass P x true = propensity P x * cellMass P x := by
    rw [propensity]
    field_simp
  constructor
  · rw [ht]
    exact mul_le_mul_of_nonneg_right hp.1 hx.le
  · have hcell := cellMass_eq_armMass_add P x
    have hf : armMass P x false = (1 - propensity P x) * cellMass P x := by
      rw [ht] at hcell
      linarith
    calc
      eps * cellMass P x ≤ (1 - propensity P x) * cellMass P x :=
        mul_le_mul_of_nonneg_right (by linarith [hp.2]) hx.le
      _ = armMass P x false := hf.symm

-- @node: knownMarginalScore_mean
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/
lemma knownMarginalScore_mean {d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) :
    ∫ z, knownMarginalScore (auxTableOf P) z ∂obsLaw P = ateFunctional P := by
  classical
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type]
  simp only [smul_eq_mul]
  rw [ateFunctional]
  apply Finset.sum_congr rfl
  intro x hxmem
  exact show ∑ a : Bool, ∑ y : Bool,
      (P.pmf (x, a, y)).toReal * knownMarginalScore (auxTableOf P) (x, a, y) =
      cellMass P x * (outcomeMean P true x - outcomeMean P false x) from by
    simp [knownMarginalScore, auxTableOf, jointMass]
    by_cases hx : 0 < cellMass P x
    · obtain ⟨ht, hf⟩ := knownMarginal_arm_bounds P hP x hx
      have he : 0 < eps := hP.eps_pos
      have ht0 : armMass P x true ≠ 0 := ne_of_gt (lt_of_lt_of_le (mul_pos he hx) ht)
      have hf0 : armMass P x false ≠ 0 := ne_of_gt (lt_of_lt_of_le (mul_pos he hx) hf)
      rw [← cellMass_eq_armMass_add P x]
      simp [outcomeMean]
      field_simp [ht0, hf0]
      change jointMass P x true true * armMass P x false -
          armMass P x true * jointMass P x false true = _
      ring
    · have hx0 : cellMass P x = 0 := le_antisymm (not_lt.mp hx) (cellMass_nonneg P x)
      have ha0 (a : Bool) : armMass P x a = 0 := by
        have ha := armMass_nonneg P x a
        rw [cellMass_eq_armMass_add] at hx0
        cases a <;> linarith [armMass_nonneg P x false, armMass_nonneg P x true]
      simp [hx0, ha0]

-- @node: knownMarginalScore_sq_integral_le
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/
lemma knownMarginalScore_sq_integral_le {d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) :
    ∫ z, knownMarginalScore (auxTableOf P) z ^ 2 ∂obsLaw P ≤ 2 * eps⁻¹ := by
  classical
  rw [show obsLaw P = P.pmf.toMeasure by rfl, PMF.integral_eq_sum]
  simp only [Fintype.sum_prod_type]
  calc
    ∑ x : Fin d, ∑ a : Bool, ∑ y : Bool,
        (P.pmf (x, a, y)).toReal * knownMarginalScore (auxTableOf P) (x, a, y) ^ 2
        ≤ ∑ x : Fin d, 2 * eps⁻¹ * cellMass P x := by
      apply Finset.sum_le_sum
      intro x hxmem
      by_cases hx : 0 < cellMass P x
      · obtain ⟨ht, hf⟩ := knownMarginal_arm_bounds P hP x hx
        have he : 0 < eps := hP.eps_pos
        have ht0 : 0 < armMass P x true := lt_of_lt_of_le (mul_pos he hx) ht
        have hf0 : 0 < armMass P x false := lt_of_lt_of_le (mul_pos he hx) hf
        have hrt : cellMass P x / armMass P x true ≤ eps⁻¹ := by
          calc
            cellMass P x / armMass P x true ≤ (armMass P x true / eps) /
                armMass P x true := div_le_div_of_nonneg_right
                  ((le_div_iff₀ he).2 (by simpa [mul_comm] using ht)) ht0.le
            _ = eps⁻¹ := by field_simp
        have hrf : cellMass P x / armMass P x false ≤ eps⁻¹ := by
          calc
            cellMass P x / armMass P x false ≤ (armMass P x false / eps) /
                armMass P x false := div_le_div_of_nonneg_right
                  ((le_div_iff₀ he).2 (by simpa [mul_comm] using hf)) hf0.le
            _ = eps⁻¹ := by field_simp
        simp [knownMarginalScore, auxTableOf]
        have hyt := jointMass_le_armMass P x true true
        have hyf := jointMass_le_armMass P x false true
        have hct := cellMass_nonneg P x
        have hit : 0 ≤ eps⁻¹ := inv_nonneg.mpr he.le
        change jointMass P x true true *
              ((armMass P x false + armMass P x true) / armMass P x true) ^ 2 +
            jointMass P x false true *
              ((armMass P x false + armMass P x true) / armMass P x false) ^ 2 ≤
            2 * eps⁻¹ * cellMass P x
        rw [← cellMass_eq_armMass_add P x]
        calc
          jointMass P x true true * (cellMass P x / armMass P x true) ^ 2 +
              jointMass P x false true * (cellMass P x / armMass P x false) ^ 2
              ≤ armMass P x false * (cellMass P x / armMass P x false) ^ 2 +
                armMass P x true * (cellMass P x / armMass P x true) ^ 2 := by
                nlinarith [sq_nonneg (cellMass P x / armMass P x false),
                  sq_nonneg (cellMass P x / armMass P x true)]
          _ = cellMass P x * (cellMass P x / armMass P x false) +
                cellMass P x * (cellMass P x / armMass P x true) := by
                field_simp [ne_of_gt ht0, ne_of_gt hf0]
          _ ≤ cellMass P x * eps⁻¹ + cellMass P x * eps⁻¹ := by gcongr
          _ = 2 * eps⁻¹ * cellMass P x := by ring
      · have hx0 : cellMass P x = 0 := le_antisymm (not_lt.mp hx) (cellMass_nonneg P x)
        have ha0 (a : Bool) : armMass P x a = 0 := by
          rw [cellMass_eq_armMass_add] at hx0
          cases a <;> linarith [armMass_nonneg P x false, armMass_nonneg P x true]
        simp [knownMarginalScore, auxTableOf, jointMass, hx0, ha0]
    _ = 2 * eps⁻¹ := by rw [← Finset.mul_sum, cellMass_sum_eq_one P, mul_one]

-- @node: knownMarginalScore_variance_le
/-- [the stated conditions](hyp:hP) establishes [the stated conclusion](goal). -/
lemma knownMarginalScore_variance_le {d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) :
    variance (knownMarginalScore (auxTableOf P)) (obsLaw P) ≤ 2 * eps⁻¹ := by
  rw [variance_eq_sub (MemLp.of_discrete :
    MemLp (knownMarginalScore (auxTableOf P)) 2 (obsLaw P))]
  exact (sub_le_self _ (sq_nonneg _)).trans (knownMarginalScore_sq_integral_le P hP)

-- @node: knownMarginalRawEstimator
/-- [the stated conditions](hyp:n,d) defines [the specified object](goal). -/
noncomputable def knownMarginalRawEstimator (n d : Nat) : KnownSample n d → Real :=
  fun z => (n : Real)⁻¹ * ∑ i, knownMarginalScore z.2 (z.1 i)

-- @node: knownMarginalRawEstimator_measurable
/-- The formal statement establishes [the stated conclusion](goal). -/
lemma knownMarginalRawEstimator_measurable (n d : Nat) :
    Measurable (knownMarginalRawEstimator n d) := by
  unfold knownMarginalRawEstimator
  apply measurable_const.mul
  exact Finset.measurable_sum _ fun i _ => knownMarginalScore_sample_measurable i

-- @node: knownMarginalRawEstimator_mean
/-- [the stated conditions](hyp:hP,hn) establishes [the stated conclusion](goal). -/
lemma knownMarginalRawEstimator_mean {n d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) (hn : 0 < n) :
    ∫ sample, knownMarginalRawEstimator n d (sample, auxTableOf P) ∂labeledProductLaw P n =
      ateFunctional P := by
  rw [show labeledProductLaw P n = Measure.pi (fun _ : Fin n => obsLaw P) by rfl]
  unfold knownMarginalRawEstimator
  change ∫ sample, (n : Real)⁻¹ *
      ∑ i, knownMarginalScore (auxTableOf P) (sample i) ∂Measure.pi (fun _ => obsLaw P) = _
  rw [Causalean.Mathlib.Probability.iid_average_integral (obsLaw P) n hn
    (knownMarginalScore (auxTableOf P)) Integrable.of_finite]
  exact knownMarginalScore_mean P hP

-- @node: knownMarginalRawEstimator_variance_le
/-- [the stated conditions](hyp:hP,hn) establishes [the stated conclusion](goal). -/
lemma knownMarginalRawEstimator_variance_le {n d : Nat} {eps : Real} (P : DiscreteLaw d)
    (hP : ModelClass d eps P) (hn : 0 < n) :
    variance (fun sample => knownMarginalRawEstimator n d (sample, auxTableOf P))
        (labeledProductLaw P n) ≤ 2 * eps⁻¹ / n := by
  rw [show labeledProductLaw P n = Measure.pi (fun _ : Fin n => obsLaw P) by rfl]
  unfold knownMarginalRawEstimator
  rw [Causalean.Mathlib.Probability.iid_average_variance (obsLaw P) n
    (knownMarginalScore (auxTableOf P)) MemLp.of_discrete]
  calc
    (n : Real)⁻¹ * variance (knownMarginalScore (auxTableOf P)) (obsLaw P)
        ≤ (n : Real)⁻¹ * (2 * eps⁻¹) := by
          gcongr
          exact knownMarginalScore_variance_le P hP
    _ = 2 * eps⁻¹ / n := by ring

-- @node: integral_sq_error_eq_variance_of_mean_eq
/-- [the stated conditions](hyp:hmean) establishes [the stated conclusion](goal). -/
lemma integral_sq_error_eq_variance_of_mean_eq {α : Type*} [MeasurableSpace α]
    [DiscreteMeasurableSpace α] [Finite α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → Real) (target : Real)
    (hmean : ∫ x, f x ∂mu = target) :
    ∫ x, (f x - target) ^ 2 ∂mu = variance f mu := by
  have hf : MemLp f 2 mu := MemLp.of_discrete
  rw [variance_eq_sub hf]
  have hsq := hf.integrable_sq
  have hint := hf.integrable one_le_two
  have hlinear : Integrable (fun x => 2 * target * f x) mu := hint.const_mul _
  have hpow : (∫ x, (f ^ 2) x ∂mu) = ∫ x, f x ^ 2 ∂mu := by rfl
  calc
    ∫ x, (f x - target) ^ 2 ∂mu =
        ∫ x, f x ^ 2 - 2 * target * f x + target ^ 2 ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = (∫ x, f x ^ 2 - 2 * target * f x ∂mu) +
        (∫ _x, target ^ 2 ∂mu) :=
      integral_add (hsq.sub hlinear) (integrable_const _)
    _ = (∫ x, f x ^ 2 ∂mu) - (∫ x, 2 * target * f x ∂mu) + target ^ 2 := by
      rw [integral_sub hsq hlinear, integral_const, probReal_univ, one_smul]
    _ = (∫ x, f x ^ 2 ∂mu) - 2 * target * (∫ x, f x ∂mu) + target ^ 2 := by
      rw [integral_const_mul]
    _ = (∫ x, (f ^ 2) x ∂mu) - (∫ x, f x ∂mu) ^ 2 := by
      rw [hpow, hmean]
      ring

-- @node: knownMarginalRisk_upper
/-- [the stated conditions](hyp:heps) establishes [the stated conclusion](goal). -/
lemma knownMarginalRisk_upper {eps : Real} (heps : 0 < eps) :
    ∀ (n d : Nat), 1 ≤ n → 2 ≤ d → knownMarginalRisk n d eps ≤ 2 * eps⁻¹ / n := by
  intro n d hn hd
  let raw := knownMarginalRawEstimator n d
  obtain ⟨clipped, hclip⟩ := exists_clipped_knownMarginalEstimator n d raw
    (knownMarginalRawEstimator_measurable n d)
  unfold knownMarginalRisk
  have hbInf : BddBelow (Set.range (fun est : {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1} =>
      ⨆ P : ClassLaw d eps,
        ∫ x, (est.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨est, rfl⟩
    exact Real.iSup_nonneg fun P => integral_nonneg fun x => sq_nonneg _
  apply ciInf_le_of_le hbInf clipped
  apply Real.iSup_le
  · intro P
    letI : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
      unfold labeledProductLaw
      infer_instance
    calc
      ∫ x, (clipped.1 (x, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n
        ≤ ∫ x, (raw (x, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n :=
          integral_mono_ae Integrable.of_finite Integrable.of_finite <|
            ae_of_all _ fun x => hclip (x, auxTableOf P.1) _
              (ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap)
    _ = variance (fun x => raw (x, auxTableOf P.1)) (labeledProductLaw P.1 n) :=
      integral_sq_error_eq_variance_of_mean_eq _ _ _
        (knownMarginalRawEstimator_mean P.1 P.2 (by omega))
    _ ≤ 2 * eps⁻¹ / n := knownMarginalRawEstimator_variance_le P.1 P.2 (by omega)
  · positivity

-- @node: knownMarginalRisk_ge_two_model_tv
/-- [the stated conditions](hyp:htable,hs,hsep,htv) establishes [the stated conclusion](goal). -/
lemma knownMarginalRisk_ge_two_model_tv {n d : Nat} {eps s : Real}
    (P0 P1 : ClassLaw d eps) (htable : auxTableOf P0.1 = auxTableOf P1.1)
    (hs : 0 ≤ s) (hsep : 2 * s ≤ |ateFunctional P0.1 - ateFunctional P1.1|)
    (htv : Causalean.Stat.tvDist (labeledProductLaw P0.1 n)
      (labeledProductLaw P1.1 n) ≤ 1 / 2) :
    s ^ 2 / 4 ≤ knownMarginalRisk n d eps := by
  classical
  letI : IsProbabilityMeasure (labeledProductLaw P0.1 n) := by
    unfold labeledProductLaw
    infer_instance
  letI : IsProbabilityMeasure (labeledProductLaw P1.1 n) := by
    unfold labeledProductLaw
    infer_instance
  letI : Nonempty {f : KnownSample n d → Real //
      Measurable f ∧ ∀ z, f z ∈ Set.Icc (-1 : Real) 1} :=
    ⟨⟨fun _ => 0, measurable_const, fun _ => by constructor <;> norm_num⟩⟩
  unfold knownMarginalRisk
  apply le_ciInf
  intro est
  let f : (Fin n → Obs d) → Real := fun x => est.1 (x, auxTableOf P0.1)
  have hf : Measurable f := est.2.1.comp (measurable_id.prodMk measurable_const)
  have ht := Causalean.Stat.two_point_lower_bound_of_tvDist_le
    (P₀ := labeledProductLaw P0.1 n) (P₁ := labeledProductLaw P1.1 n) hf
    (θ₀ := ateFunctional P0.1) (θ₁ := ateFunctional P1.1)
    (s := s) (c := (1 / 2 : Real)) hsep htv
  have hp : 1 / 4 ≤ max
      ((labeledProductLaw P0.1 n).real {z | s ≤ |f z - ateFunctional P0.1|})
      ((labeledProductLaw P1.1 n).real {z | s ≤ |f z - ateFunctional P1.1|}) := by
    convert ht using 1 <;> norm_num
  have hrisk (P : ClassLaw d eps) (htableP : auxTableOf P.1 = auxTableOf P0.1) :
      s ^ 2 * (labeledProductLaw P.1 n).real {z | s ≤ |f z - ateFunctional P.1|} ≤
        ∫ z, (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n := by
    letI : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
      unfold labeledProductLaw
      infer_instance
    have hmarkov := mul_meas_ge_le_integral_of_nonneg
      (μ := labeledProductLaw P.1 n)
      (f := fun z => (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2)
      (ae_of_all _ fun z => sq_nonneg _) Integrable.of_finite (s ^ 2)
    have he : {z | s ≤ |f z - ateFunctional P.1|} =
        {z | s ^ 2 ≤ (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2} := by
      ext z
      change s ≤ |f z - ateFunctional P.1| ↔
        s ^ 2 ≤ (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2
      rw [show f z = est.1 (z, auxTableOf P.1) by
        simp only [f]
        rw [htableP]]
      simpa [abs_of_nonneg hs, sq_abs] using
        (sq_le_sq₀ hs (abs_nonneg (est.1 (z, auxTableOf P.1) - ateFunctional P.1))).symm
    rw [he]
    simpa using hmarkov
  have hb : BddAbove (Set.range (fun P : ClassLaw d eps =>
      ∫ z, (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨P, rfl⟩
    letI : IsProbabilityMeasure (labeledProductLaw P.1 n) := by
      unfold labeledProductLaw
      infer_instance
    calc
      ∫ z, (est.1 (z, auxTableOf P.1) - ateFunctional P.1) ^ 2 ∂labeledProductLaw P.1 n
          ≤ ∫ _z, (4 : Real) ∂labeledProductLaw P.1 n := by
            apply integral_mono_ae Integrable.of_finite Integrable.of_finite
            filter_upwards with z
            rcases est.2.2 (z, auxTableOf P.1) with ⟨he0, he1⟩
            rcases ateFunctional_mem_Icc_neg_one_one P.1 P.2.overlap with ⟨ht0, ht1⟩
            nlinarith [sq_nonneg (est.1 (z, auxTableOf P.1) - ateFunctional P.1 - 2),
              sq_nonneg (est.1 (z, auxTableOf P.1) - ateFunctional P.1 + 2)]
      _ = 4 := by simp
  have hm : s ^ 2 / 4 ≤ max
      (∫ z, (est.1 (z, auxTableOf P0.1) - ateFunctional P0.1) ^ 2 ∂labeledProductLaw P0.1 n)
      (∫ z, (est.1 (z, auxTableOf P1.1) - ateFunctional P1.1) ^ 2 ∂labeledProductLaw P1.1 n) := by
    calc
      s ^ 2 / 4 = s ^ 2 * (1 / 4) := by ring
      _ ≤ s ^ 2 * max
          ((labeledProductLaw P0.1 n).real {z | s ≤ |f z - ateFunctional P0.1|})
          ((labeledProductLaw P1.1 n).real {z | s ≤ |f z - ateFunctional P1.1|}) := by gcongr
      _ = max
          (s ^ 2 * (labeledProductLaw P0.1 n).real {z | s ≤ |f z - ateFunctional P0.1|})
          (s ^ 2 * (labeledProductLaw P1.1 n).real {z | s ≤ |f z - ateFunctional P1.1|}) := by
            rw [mul_max_of_nonneg _ _ (sq_nonneg s)]
      _ ≤ _ := max_le_max (hrisk P0 rfl) (hrisk P1 htable.symm)
  exact hm.trans (max_le (le_ciSup hb P0) (le_ciSup hb P1))

end CausalSmith.Stat.SemisupervisedDiscreteAteAnnotationFrontier
