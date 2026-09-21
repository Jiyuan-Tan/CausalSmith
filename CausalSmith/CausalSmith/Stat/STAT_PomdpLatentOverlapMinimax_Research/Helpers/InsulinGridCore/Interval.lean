module
public import Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
public import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinGridCore.Model

@[expose] public section

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open Causalean.Mathlib.Analysis.IntervalArithmetic
open Causalean.Mathlib.Analysis.IntervalArithmetic.Contour
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

/-- [this defines the insulin Normalization Certificate object](goal). [defining clause 1](step:1); and [defining clause 2](step:2). -/
def insulinNormalizationCertificate : NormalizationCertificate where
  schedule := { fuel := 10 }
  enclosure := normalizationInterval { fuel := 10 }

/-- [the insulin Pi Interval lo pos assertion holds](goal). -/
lemma insulinPiInterval_lo_pos (n : ℕ) :
    0 < (Transcendental.piInterval n).lo := by
  induction n with
  | zero => norm_num [Transcendental.piInterval,
      Transcendental.piRaw, Transcendental.atanRaw,
      Transcendental.atanPartial,
      Transcendental.atanError, Finset.sum_range_succ, RatInterval.point,
      RatInterval.mul, RatInterval.sub, RatInterval.neg, RatInterval.add]
  | succ n ih =>
      rw [Transcendental.piInterval]
      unfold RatInterval.tighten
      split
      · exact ih.trans_le (le_max_left _ _)
      · exact ih

/-- Assuming [the hq condition](hyp:hq), [the insulin Sqrt Upper pos assertion holds](goal). -/
lemma insulinSqrtUpper_pos (q : ℚ) (hq : 0 ≤ q) (n : ℕ) :
    0 < RatInterval.sqrtUpper q n := by
  induction n with
  | zero => simp [RatInterval.sqrtUpper]; positivity
  | succ n ih =>
      rw [RatInterval.sqrtUpper]
      have hdiv : 0 ≤ q / RatInterval.sqrtUpper q n := div_nonneg hq ih.le
      positivity

set_option maxRecDepth 100000 in
/-- [the insulin Normalization Certificate checked assertion holds](goal). -/
lemma insulinNormalizationCertificate_checked :
    normalizationCheck insulinNormalizationCertificate = true := by
  have htwo : 0 < (twoPiInterval 10).lo := by
    have hpi := insulinPiInterval_lo_pos 10
    simp only [twoPiInterval, RatInterval.point, RatInterval.mul]
    rw [min_eq_left (mul_le_mul_of_nonneg_left
      (Transcendental.piInterval 10).lo_le_hi (by norm_num))]
    simp only [min_self]
    positivity
  have hroot : 0 < (RatInterval.sqrtInterval (twoPiInterval 10) htwo.le 10).lo := by
    simp only [RatInterval.sqrtInterval, RatInterval.sqrtLower]
    exact div_pos htwo (insulinSqrtUpper_pos _ htwo.le 10)
  unfold normalizationCheck normalizationScheduleCheck insulinNormalizationCertificate
  rw [dif_pos htwo.le]
  dsimp only
  rw [show decide
      ((RatInterval.sqrtInterval (twoPiInterval 10) htwo.le 10).hi < 0 ∨
        0 < (RatInterval.sqrtInterval (twoPiInterval 10) htwo.le 10).lo) = true by
    exact decide_eq_true (Or.inr hroot)]
  simp [normalizationInterval, htwo.le, hroot]

/-- [this defines the insulin Central Certificate object](goal). [defining clause 1](step:1); and [defining clause 2](step:2). -/
def insulinCentralCertificate : CentralCertificate where
  degree := 118
  normalization := insulinNormalizationCertificate

/-- Assuming [the hq condition](hyp:hq), [the insulin Central Interval sound assertion holds](goal). -/
lemma insulinCentralInterval_sound {q : ℚ} (hq : |q| ≤ 8) :
    (centralInterval q insulinCentralCertificate).Contains
      (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  apply centralCheck_sound (c := insulinCentralCertificate)
    (reported := centralInterval q insulinCentralCertificate)
  unfold centralCheck
  dsimp only [insulinCentralCertificate]
  rw [insulinNormalizationCertificate_checked]
  simp only [Bool.true_and]
  apply decide_eq_true
  refine ⟨hq, ?_, le_rfl, le_rfl⟩
  have habs0 : 0 ≤ |q| := abs_nonneg q
  have hsquare : |q| ^ 2 ≤ (8 : ℚ) ^ 2 :=
    (sq_le_sq₀ habs0 (by norm_num)).2 hq
  norm_num at hsquare ⊢
  exact hsquare.trans (by norm_num)

/-- For [the q input](hyp:q), [this defines the insulin CDFRaw Interval object](goal). -/
def insulinCDFRawInterval (q : ℚ) : RatInterval :=
  if |q| ≤ 8 then centralInterval q insulinCentralCertificate
  else if q < 0 then
    ⟨0, (centralInterval (-8) insulinCentralCertificate).hi, by
      have hs := insulinCentralInterval_sound (q := (-8 : ℚ)) (by norm_num)
      have hs' : Causalean.Mathlib.stdNormalCDF (-8 : ℝ) ≤
          ((centralInterval (-8) insulinCentralCertificate).hi : ℝ) := by
        convert hs.2 using 1 <;> norm_num
      have hr : (0 : ℝ) ≤ ((centralInterval (-8) insulinCentralCertificate).hi : ℝ) :=
        (Causalean.Mathlib.stdNormalCDF_nonneg (-8 : ℝ)).trans hs'
      exact_mod_cast hr⟩
  else
    ⟨(centralInterval 8 insulinCentralCertificate).lo, 1, by
      have hs := insulinCentralInterval_sound (q := (8 : ℚ)) (by norm_num)
      have hs' : ((centralInterval 8 insulinCentralCertificate).lo : ℝ) ≤
          Causalean.Mathlib.stdNormalCDF (8 : ℝ) := by
        convert hs.1 using 1 <;> norm_num
      have hr : ((centralInterval 8 insulinCentralCertificate).lo : ℝ) ≤ 1 :=
        hs'.trans (Causalean.Mathlib.stdNormalCDF_le_one (8 : ℝ))
      exact_mod_cast hr⟩

/-- [the insulin CDFRaw Interval sound assertion holds](goal). -/
lemma insulinCDFRawInterval_sound (q : ℚ) :
    (insulinCDFRawInterval q).Contains
      (Causalean.Mathlib.stdNormalCDF (q : ℝ)) := by
  by_cases hcentral : |q| ≤ 8
  · simpa [insulinCDFRawInterval, hcentral] using insulinCentralInterval_sound hcentral
  · have habs_gt : 8 < |q| := lt_of_not_ge hcentral
    by_cases hq : q < 0
    · rw [insulinCDFRawInterval, if_neg hcentral, if_pos hq]
      constructor
      · simpa only [Rat.cast_zero] using Causalean.Mathlib.stdNormalCDF_nonneg (q : ℝ)
      · have hq8 : (q : ℝ) ≤ (-8 : ℝ) := by
          have : q ≤ -8 := by
            rw [abs_of_neg hq] at habs_gt
            linarith
          exact_mod_cast this
        have hcentral8 : Causalean.Mathlib.stdNormalCDF (-8 : ℝ) ≤
            ((centralInterval (-8 : ℚ) insulinCentralCertificate).hi : ℝ) := by
          convert (insulinCentralInterval_sound (q := (-8 : ℚ)) (by norm_num)).2 using 1 <;>
            norm_num
        simpa only using (Causalean.Mathlib.stdNormalCDF_monotone hq8).trans hcentral8
    · rw [insulinCDFRawInterval, if_neg hcentral, if_neg hq]
      constructor
      · have h8q : (8 : ℝ) ≤ (q : ℝ) := by
          have hq0 : 0 ≤ q := le_of_not_gt hq
          rw [abs_of_nonneg hq0] at habs_gt
          exact_mod_cast habs_gt.le
        exact (insulinCentralInterval_sound (q := (8 : ℚ)) (by norm_num)).1.trans
          (Causalean.Mathlib.stdNormalCDF_monotone h8q)
      · simpa only [Rat.cast_one] using Causalean.Mathlib.stdNormalCDF_le_one (q : ℝ)

/-- For [the scale input](hyp:scale), [the hscale input](hyp:hscale), [the I input](hyp:I), [this defines the quantize Interval object](goal). -/
def quantizeInterval (scale : ℕ) (hscale : 0 < scale)
    (I : RatInterval) : RatInterval :=
  let lo : ℚ := (Rat.floor (scale * I.lo) : ℤ) / scale
  let hi : ℚ := (Rat.ceil (scale * I.hi) : ℤ) / scale
  ⟨lo, hi, by
    dsimp [lo, hi]
    have hs : (0 : ℚ) < scale := by exact_mod_cast hscale
    apply (div_le_div_iff_of_pos_right hs).2
    exact (Rat.floor_le (scale * I.lo)).trans
      ((mul_le_mul_of_nonneg_left I.lo_le_hi hs.le).trans (Rat.le_ceil))⟩

/-- Assuming [the hscale condition](hyp:hscale), [the subinterval quantize Interval assertion holds](goal). -/
lemma subinterval_quantizeInterval (scale : ℕ) (hscale : 0 < scale)
    (I : RatInterval) : I.Subinterval (quantizeInterval scale hscale I) := by
  constructor
  · dsimp [quantizeInterval]
    have hs : (0 : ℚ) < scale := by exact_mod_cast hscale
    apply (div_le_iff₀ hs).2
    simpa [mul_comm] using Rat.floor_le (scale * I.lo)
  · dsimp [quantizeInterval]
    have hs : (0 : ℚ) < scale := by exact_mod_cast hscale
    apply (le_div_iff₀ hs).2
    simpa [mul_comm] using (Rat.le_ceil : scale * I.hi ≤ _)

/-- For [the q input](hyp:q), [this defines the insulin CDFInterval object](goal). -/
def insulinCDFInterval (q : ℚ) : RatInterval :=
  quantizeInterval (10 ^ 12) (by positivity) (insulinCDFRawInterval q)

/-- [the insulin CDFInterval sound assertion holds](goal). -/
lemma insulinCDFInterval_sound (q : ℚ) :
    (insulinCDFInterval q).Contains
      (Causalean.Mathlib.stdNormalCDF (q : ℝ)) :=
  RatInterval.Contains.mono
    (subinterval_quantizeInterval (10 ^ 12) (by positivity) _) (insulinCDFRawInterval_sound q)

/-- For [the x input](hyp:x), [this defines the insulin Glucose Rat object](goal). -/
def insulinGlucoseRat (x : Fin 90) : ℚ :=
  match x.val / 18 with
  | 0 => 50 | 1 => 100 | 2 => 150 | 3 => 200 | _ => 250

/-- For [the i input](hyp:i), [this defines the insulin Activity Rat object](goal). -/
def insulinActivityRat (i : ℕ) : ℚ :=
  if i = 0 then 0 else if i = 1 then 31 else 850

/-- [the insulin Glucose Rat cast assertion holds](goal). -/
lemma insulinGlucoseRat_cast (x : Fin 90) :
    (insulinGlucoseRat x : ℝ) = glucoseGridValue x := by
  fin_cases x <;> norm_num [insulinGlucoseRat, glucoseGridValue]

/-- [the insulin Activity Rat cast assertion holds](goal). -/
lemma insulinActivityRat_cast (i : ℕ) :
    (insulinActivityRat i : ℝ) = insulinActivityValue i := by
  unfold insulinActivityRat insulinActivityValue
  split_ifs <;> norm_num

/-- For [the s input](hyp:s), [the a input](hyp:a), [this defines the insulin Mean Rat object](goal). -/
def insulinMeanRat (s : JointState 90 4) (a : Bool) : ℚ :=
  10 + 9 / 10 * insulinGlucoseRat s.1 + 1 / 10 *
      (if s.2.val / 2 = 0 then 0 else 78) +
    1 / 10 * (if s.2.val % 2 = 0 then 0 else 78) -
    1 / 100 * insulinActivityRat (s.1.val / 6 % 3) -
    1 / 100 * insulinActivityRat (s.1.val / 2 % 3) -
    2 * (if a then 1 else 0) - 4 * (s.1.val % 2 : ℕ)

/-- [the insulin Mean Rat cast assertion holds](goal). -/
lemma insulinMeanRat_cast (s : JointState 90 4) (a : Bool) :
    (insulinMeanRat s a : ℝ) = insulinMean s a := by
  unfold insulinMeanRat insulinMean
  push_cast
  rw [insulinGlucoseRat_cast, insulinActivityRat_cast, insulinActivityRat_cast]
  split_ifs <;> norm_num <;> ring

/-- For [the k input](hyp:k), [this defines the insulin Cutoff object](goal). -/
def insulinCutoff (k : Fin 4) : ℚ := 75 + 50 * k.val

/-- For [the s input](hyp:s), [the a input](hyp:a), [the k input](hyp:k), [this defines the insulin CDFArgument object](goal). -/
def insulinCDFArgument (s : JointState 90 4) (a : Bool) (k : Fin 4) : ℚ :=
  (insulinCutoff k - insulinMeanRat s a) / 5

/-- [this defines the insulin Joint Equiv object](goal). -/
def insulinJointEquiv : JointState 90 4 ≃ Fin 360 := finProdFinEquiv

/-- The record collecting the data for Insulin CDFCutoff Row. -/
structure InsulinCDFCutoffRow where
  data : Array RatInterval
  size_eq : data.size = 4

/-- For [the r input](hyp:r), [the k input](hyp:k), [this defines the get object](goal). -/
def InsulinCDFCutoffRow.get (r : InsulinCDFCutoffRow) (k : Fin 4) : RatInterval :=
  r.data[k.val]'(by rw [r.size_eq]; exact k.isLt)

/-- The record collecting the data for Insulin CDFAction Row. -/
structure InsulinCDFActionRow where
  data : Array InsulinCDFCutoffRow
  size_eq : data.size = 2

/-- For [the r input](hyp:r), [the a input](hyp:a), [this defines the get object](goal). -/
def InsulinCDFActionRow.get (r : InsulinCDFActionRow)
    (a : Fin 2) : InsulinCDFCutoffRow :=
  r.data[a.val]'(by rw [r.size_eq]; exact a.isLt)

/-- The record collecting the data for Insulin CDFTable. -/
structure InsulinCDFTable where
  data : Array InsulinCDFActionRow
  size_eq : data.size = 360

/-- For [the r input](hyp:r), [the s input](hyp:s), [this defines the get object](goal). -/
def InsulinCDFTable.get (r : InsulinCDFTable) (s : Fin 360) : InsulinCDFActionRow :=
  r.data[s.val]'(by rw [r.size_eq]; exact s.isLt)

/-- [this defines the insulin CDFTable object](goal). [defining clause 1](step:1); and [defining clause 2](step:2). -/
def insulinCDFTable : InsulinCDFTable where
  -- `List.ofFn … |>.toArray` rather than `Array.ofFn`: the latter is well-founded recursion,
  -- whose termination proofs are invisible to module importers, so the kernel could not
  -- evaluate the table in the `decide +kernel` chunk certificates.
  data := (List.ofFn fun i : Fin 360 =>
    { data := (List.ofFn fun a : Fin 2 =>
        { data := (List.ofFn fun k : Fin 4 =>
            insulinCDFInterval (insulinCDFArgument (insulinJointEquiv.symm i)
              (insulinBoolEquivFin.symm a) k)).toArray
          size_eq := by rw [List.size_toArray, List.length_ofFn] }).toArray
      size_eq := by rw [List.size_toArray, List.length_ofFn] }).toArray
  size_eq := by rw [List.size_toArray, List.length_ofFn]

/-- For [the table input](hyp:table), [the s input](hyp:s), [the a input](hyp:a), [the k input](hyp:k), [this defines the insulin CDFEntry With Table object](goal). -/
def insulinCDFEntryWithTable (table : InsulinCDFTable)
    (s : JointState 90 4) (a : Bool) (k : Fin 4) : RatInterval :=
  (((table.get (insulinJointEquiv s)).get (insulinBoolEquivFin a)).get k)

/-- For [the s input](hyp:s), [the a input](hyp:a), [the k input](hyp:k), [this defines the insulin CDFEntry object](goal). -/
def insulinCDFEntry (s : JointState 90 4) (a : Bool) (k : Fin 4) : RatInterval :=
  insulinCDFEntryWithTable insulinCDFTable s a k

/-- [the insulin CDFEntry With Table eq assertion holds](goal). -/
lemma insulinCDFEntryWithTable_eq (s : JointState 90 4) (a : Bool) (k : Fin 4) :
    insulinCDFEntryWithTable insulinCDFTable s a k = insulinCDFEntry s a k := rfl

/-- [the insulin CDFEntry eq assertion holds](goal). -/
lemma insulinCDFEntry_eq (s : JointState 90 4) (a : Bool) (k : Fin 4) :
    insulinCDFEntry s a k = insulinCDFInterval (insulinCDFArgument s a k) := by
  simp only [insulinCDFEntry, insulinCDFEntryWithTable, insulinCDFTable, InsulinCDFTable.get,
    InsulinCDFActionRow.get, InsulinCDFCutoffRow.get, List.getElem_toArray, List.getElem_ofFn,
    Fin.eta, Equiv.symm_apply_apply]

/-- [the insulin CDFEntry sound assertion holds](goal). -/
lemma insulinCDFEntry_sound (s : JointState 90 4) (a : Bool) (k : Fin 4) :
    (insulinCDFEntry s a k).Contains
      (gaussianCDF (((insulinCutoff k : ℝ) - insulinMean s a) / 5)) := by
  rw [gaussianCDF_eq_stdNormalCDF]
  rw [insulinCDFEntry_eq]
  change (insulinCDFInterval (insulinCDFArgument s a k)).Contains
    (Causalean.Mathlib.stdNormalCDF (((insulinCutoff k : ℝ) - insulinMean s a) / 5))
  convert insulinCDFInterval_sound (insulinCDFArgument s a k) using 1
  simp only [insulinCDFArgument, Rat.cast_div, Rat.cast_sub, insulinCutoff,
    Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  rw [insulinMeanRat_cast]

/-- For [the table input](hyp:table), [the s input](hyp:s), [the a input](hyp:a), [the x' input](hyp:x'), [this defines the insulin Rounded Interval With Table object](goal). -/
def insulinRoundedIntervalWithTable (table : InsulinCDFTable)
    (s : JointState 90 4) (a : Bool)
    (x' : Fin 90) : RatInterval :=
  let i := x'.val / 18
  if h0 : i = 0 then insulinCDFEntryWithTable table s a 0
  else if h4 : i = 4 then (RatInterval.point 1).sub
    (insulinCDFEntryWithTable table s a 3)
  else (insulinCDFEntryWithTable table s a ⟨i, by omega⟩).sub
    (insulinCDFEntryWithTable table s a ⟨i - 1, by omega⟩)

/-- For [the s input](hyp:s), [the a input](hyp:a), [the x' input](hyp:x'), [this defines the insulin Rounded Interval object](goal). -/
def insulinRoundedInterval (s : JointState 90 4) (a : Bool)
    (x' : Fin 90) : RatInterval :=
  insulinRoundedIntervalWithTable insulinCDFTable s a x'

/-- [the insulin Rounded Interval With Table eq assertion holds](goal). -/
lemma insulinRoundedIntervalWithTable_eq (s : JointState 90 4) (a : Bool)
    (x' : Fin 90) :
    insulinRoundedIntervalWithTable insulinCDFTable s a x' =
      insulinRoundedInterval s a x' := rfl

/-- [the insulin Rounded Interval sound assertion holds](goal). -/
lemma insulinRoundedInterval_sound (s : JointState 90 4) (a : Bool)
    (x' : Fin 90) :
    (insulinRoundedInterval s a x').Contains (roundedGlucoseWeight s a x') := by
  unfold insulinRoundedInterval insulinRoundedIntervalWithTable roundedGlucoseWeight
  simp_rw [insulinCDFEntryWithTable_eq]
  split_ifs with h0 h4
  · convert insulinCDFEntry_sound s a 0 using 1 <;> norm_num [insulinCutoff]
  · convert RatInterval.sub_sound (RatInterval.point_sound 1)
      (insulinCDFEntry_sound s a 3) using 1 <;> norm_num [insulinCutoff]
  · have hi : x'.val / 18 < 4 := by
      have hx := x'.isLt
      omega
    apply RatInterval.sub_sound
    · simpa [insulinCutoff] using
        insulinCDFEntry_sound s a ⟨x'.val / 18, hi⟩
    · convert insulinCDFEntry_sound s a ⟨x'.val / 18 - 1, by omega⟩ using 1 <;>
        norm_num [insulinCutoff, Nat.cast_sub (by omega : 1 ≤ x'.val / 18)]

/-- For [the table input](hyp:table), [the s input](hyp:s), [the a input](hyp:a), [the s' input](hyp:s'), [this defines the insulin Dynamic Interval With Table object](goal). -/
def insulinDynamicIntervalWithTable (table : InsulinCDFTable)
    (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : RatInterval :=
  if s'.2.val % 2 = s.2.val / 2 ∧
      s'.1.val / 2 % 3 = s.1.val / 6 % 3 ∧
      decide (s'.1.val % 2 = 1) = a then
    ((insulinRoundedIntervalWithTable table s a s'.1).mul (RatInterval.point
      (if s'.2.val / 2 = 0 then 4 / 5 else 1 / 5))).mul (RatInterval.point
      (if s'.1.val / 6 % 3 = 0 then 2 / 5
        else if s'.1.val / 6 % 3 = 1 then 2 / 5 else 1 / 5))
  else RatInterval.point 0

/-- For [the s input](hyp:s), [the a input](hyp:a), [the s' input](hyp:s'), [this defines the insulin Dynamic Interval object](goal). -/
def insulinDynamicInterval (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) : RatInterval :=
  insulinDynamicIntervalWithTable insulinCDFTable s a s'

/-- [the insulin Dynamic Interval With Table eq assertion holds](goal). -/
lemma insulinDynamicIntervalWithTable_eq (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) :
    insulinDynamicIntervalWithTable insulinCDFTable s a s' =
      insulinDynamicInterval s a s' := rfl

/-- [the insulin Dynamic Interval sound assertion holds](goal). -/
lemma insulinDynamicInterval_sound (s : JointState 90 4) (a : Bool)
    (s' : JointState 90 4) :
    (insulinDynamicInterval s a s').Contains (insulinDynamicWeight s a s') := by
  unfold insulinDynamicInterval insulinDynamicIntervalWithTable insulinDynamicWeight
  by_cases h : s'.2.val % 2 = s.2.val / 2 ∧
      s'.1.val / 2 % 3 = s.1.val / 6 % 3 ∧
      decide (s'.1.val % 2 = 1) = a
  · rw [if_pos h]
    rcases h with ⟨h1, h2, h3⟩
    rw [insulinRoundedIntervalWithTable_eq]
    convert RatInterval.mul_sound
      (RatInterval.mul_sound (insulinRoundedInterval_sound s a s'.1)
        (RatInterval.point_sound _)) (RatInterval.point_sound _) using 1 <;>
      split_ifs <;> norm_num
  · rw [if_neg h, RatInterval.contains_point_iff]
    by_cases h1 : s'.2.val % 2 = s.2.val / 2
    · by_cases h2 : s'.1.val / 2 % 3 = s.1.val / 6 % 3
      · have h3 : decide (s'.1.val % 2 = 1) ≠ a := by
          intro h3
          exact h ⟨h1, h2, h3⟩
        simp [h3]
      · simp [h2]
    · simp [h1]

/-- For [the target input](hyp:target), [the x input](hyp:x), [the a input](hyp:a), [this defines the insulin Policy Rat object](goal). -/
def insulinPolicyRat (target : Bool) (x : Fin 90) (a : Bool) : ℚ :=
  if target then
    if a = decide (125 ≤ insulinGlucoseRat x) then 1 else 0
  else if a then 3 / 10 else 7 / 10

/-- For [the table input](hyp:table), [the target input](hyp:target), [the s input](hyp:s), [the s' input](hyp:s'), [this defines the insulin Policy Interval With Table object](goal). -/
def insulinPolicyIntervalWithTable (table : InsulinCDFTable) (target : Bool)
    (s s' : JointState 90 4) : RatInterval :=
  (RatInterval.point (1 / 720)).add
    ((RatInterval.point (1 / 2)).mul (intervalSum fun a : Bool =>
      (RatInterval.point (insulinPolicyRat target s.1 a)).mul
        (insulinDynamicIntervalWithTable table s a s')))

/-- For [the target input](hyp:target), [the s input](hyp:s), [the s' input](hyp:s'), [this defines the insulin Policy Interval object](goal). -/
def insulinPolicyInterval (target : Bool)
    (s s' : JointState 90 4) : RatInterval :=
  insulinPolicyIntervalWithTable insulinCDFTable target s s'

/-- For [the target input](hyp:target), [this defines the insulin Policy Interval Matrix object](goal). -/
def insulinPolicyIntervalMatrix (target : Bool) :
    IntervalMatrix (JointState 90 4) (JointState 90 4) :=
  insulinPolicyInterval target

/-- [the insulin Policy Interval Matrix eq assertion holds](goal). -/
lemma insulinPolicyIntervalMatrix_eq (target : Bool)
    (s s' : JointState 90 4) :
    insulinPolicyIntervalMatrix target s s' = insulinPolicyInterval target s s' := by
  rfl

/-- [the insulin Behaviour PMF apply assertion holds](goal). -/
lemma insulinBehaviourPMF_apply (x : Fin 90) (a : Bool) :
    ((insulinGridFinite T).b x a).toReal = (insulinPolicyRat false x a : ℚ) := by
  change ((@pmfOfRealWeight Bool inferInstance inferInstance insulinBehaviourWeight) a).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one]
  · rw [ENNReal.toReal_ofReal]
    · cases a <;> norm_num [insulinBehaviourWeight, insulinPolicyRat]
    · cases a <;> norm_num [insulinBehaviourWeight]
  · intro b
    cases b <;> norm_num [insulinBehaviourWeight]
  · norm_num [Fin.sum_univ_succ, insulinBehaviourWeight]

/-- [the insulin Target PMF apply assertion holds](goal). -/
lemma insulinTargetPMF_apply (x : Fin 90) (a : Bool) :
    ((insulinGridFinite T).e x a).toReal = (insulinPolicyRat true x a : ℚ) := by
  change ((@pmfOfRealWeight Bool inferInstance inferInstance
    (insulinTargetWeight x)) a).toReal = _
  rw [pmfOfRealWeight_apply_of_nonneg_sum_one]
  · rw [ENNReal.toReal_ofReal]
    · unfold insulinTargetWeight
      have heq : decide (125 ≤ glucoseGridValue x) =
          decide (125 ≤ insulinGlucoseRat x) := by
        fin_cases x <;> norm_num [insulinGlucoseRat, glucoseGridValue]
      simp [insulinPolicyRat, heq]
      split_ifs <;> norm_num
    · unfold insulinTargetWeight
      split_ifs <;> norm_num
  · intro b
    unfold insulinTargetWeight
    split_ifs <;> norm_num
  · unfold insulinTargetWeight
    cases decide (125 ≤ glucoseGridValue x) <;> norm_num

/-- [the insulin Policy Interval Matrix contains assertion holds](goal). -/
lemma insulinPolicyIntervalMatrix_contains (target : Bool) :
    ContainsMatrix (insulinPolicyIntervalMatrix target)
      (finitePolicyKernel (insulinGridFinite T)
        (if target then (insulinGridFinite T).e else (insulinGridFinite T).b)) := by
  intro s s'
  rw [insulinPolicyIntervalMatrix_eq]
  rw [insulinFinitePolicyKernel_eq]
  unfold insulinPolicyInterval insulinPolicyIntervalWithTable
  simp_rw [insulinDynamicIntervalWithTable_eq]
  have hpolicy (a : Bool) :
      (((if target then (insulinGridFinite T).e else (insulinGridFinite T).b) s.1) a).toReal =
        (insulinPolicyRat target s.1 a : ℚ) := by
    cases target
    · exact insulinBehaviourPMF_apply (T := T) s.1 a
    · exact insulinTargetPMF_apply (T := T) s.1 a
  simp_rw [hpolicy]
  convert RatInterval.add_sound (RatInterval.point_sound (1 / 720))
    (RatInterval.mul_sound (RatInterval.point_sound (1 / 2))
      (intervalSum_sound fun a => RatInterval.mul_sound
        (RatInterval.point_sound (insulinPolicyRat target s.1 a))
        (insulinDynamicInterval_sound s a s'))) using 1 <;> norm_num

/-- [the insulin Finite Policy Kernel stochastic assertion holds](goal). -/
lemma insulinFinitePolicyKernel_stochastic (target : Bool) :
    IsStochasticMatrix (finitePolicyKernel (insulinGridFinite T)
      (if target then (insulinGridFinite T).e else (insulinGridFinite T).b)) := by
  let p := if target then (insulinGridFinite T).e else (insulinGridFinite T).b
  have hp : PolicyVector (fun x a => (p x a).toReal) := by
    cases target
    · exact (embed_sequentialIgnorability (insulinGridFinite T)).1
    · exact (insulinGrid_policyOverlap T).1
  have hrow (s : JointState 90 4) : ProbabilityVector
      (finitePolicyKernel (insulinGridFinite T) p s) := by
    rw [← embed_policyKernel_eq]
    exact policyKernel_probabilityVector _ (embed_pomdpKernelLaw _) _ hp s
  exact ⟨fun i j => (hrow i).1 j, fun i => (hrow i).2⟩

/-- For [the target input](hyp:target), [this defines the insulin Certified Kernel object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3). -/
def insulinCertifiedKernel (target : Bool) : CertifiedKernel
    (finitePolicyKernel (insulinGridFinite T)
      (if target then (insulinGridFinite T).e else (insulinGridFinite T).b)) where
  intervals := insulinPolicyIntervalMatrix target
  contains := insulinPolicyIntervalMatrix_contains (T := T) target
  stochastic := insulinFinitePolicyKernel_stochastic (T := T) target

/-- [the insulin Finite Policy Kernel contracts L1 assertion holds](goal). -/
lemma insulinFinitePolicyKernel_contractsL1 (target : Bool) :
    ContractsL1 (finitePolicyKernel (insulinGridFinite T)
      (if target then (insulinGridFinite T).e else (insulinGridFinite T).b)) (1 / 2) := by
  intro p q hp hq
  have hp' : ProbabilityVector p := hp
  have hq' : ProbabilityVector q := hq
  have h := insulinPolicy_contraction T
    (if target then (insulinGridFinite T).e else (insulinGridFinite T).b) p q hp' hq'
  unfold l1Distance markovStep Matrix.vecMul dotProduct
  unfold tvNorm applyKernel at h
  simp only [Pi.sub_apply] at h ⊢
  have h2 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
  norm_num at h2
  simpa only [Pi.sub_apply] using h2

end CausalSmith.Stat.PomdpLatentOverlapMinimax
