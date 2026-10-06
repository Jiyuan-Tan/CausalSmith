module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LawConstruction
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.TwoPrior
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperHandle

/-! Total oracle decisions and the explicit two-atom lower-pair construction. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


variable (κ : Params)
/-- Public finite-p score moment envelope. -/
def oracleMoment : ℝ := 10*(4 : ℝ)^κ.p
/-- Public oracle risk certificate. -/
def oracleConstant : ℝ := 20+oracleMoment κ+Real.sqrt (oracleMoment κ)
/-- Public oracle comparison constant covers both risk and honest length. -/
def oracleUpper : ℝ := 20*oracleConstant κ
/-- Deterministic oracle bandwidth. -/
def oracleH (n : ℕ) : ℝ := (n : ℝ)^(-qExp κ/(κ.γ+qExp κ))
/-- Deterministic oracle score threshold. -/
def oracleT (n : ℕ) : ℝ := ((n : ℝ)*oracleH κ n)^(1/κ.p)
/-- A supplied nuisance is clipped to the overlap range, making the decision total. -/
def suppliedScore (f : Nuisance) (o : O) : ℝ :=
  scoreZ (fun x => max (1/4) (min (f x) (3/4))) o
/-- The supplied score is jointly Borel in the nuisance and original record. -/
-- @node: measurable_suppliedScore
@[fun_prop] lemma measurable_suppliedScore :
    Measurable (fun z : Nuisance × O => suppliedScore z.1 z.2) := by
  unfold suppliedScore scoreZ X A Y
  have heval : Measurable (fun z : Nuisance × O => z.1 z.2.1) := by
    apply Continuous.measurable
    fun_prop
  apply Measurable.ite
  · exact measurableSet_eq_fun (by fun_prop) measurable_const
  · fun_prop
  · fun_prop
/-- Total clipped oracle estimator on the entire augmented decision domain. -/
def oracleEstimator (n : ℕ) (z : Dataset n × unitInterval × Nuisance) : ℝ :=
  clip (((n : ℝ)*oracleH κ n)⁻¹ * ∑ i : Fin n,
    if X (z.1 i) ∈ window (oracleH κ n) then trunc (oracleT κ n) (suppliedScore z.2.2 (z.1 i)) else 0)
/-- The oracle interval radius is a deterministic public quantity. -/
def oracleInterval (n : ℕ) (z : Dataset n × unitInterval × Nuisance) : IntervalCode :=
  closedInterval (max (-1/2) (oracleEstimator κ n z-max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ))))
    (min (1/2) (oracleEstimator κ n z+max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ))))
/-- The oracle decision is Borel and range-valued even on off-model supplied functions. -/
-- @node: oracleEstimator_total
lemma oracleEstimator_total (n : ℕ) : Measurable (oracleEstimator κ n) ∧
  ∀ z, oracleEstimator κ n z ∈ Icc (-1/2) (1/2) := by
  constructor
  · unfold oracleEstimator
    apply measurable_clip.comp
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro i hi
    apply Measurable.ite
    · exact measurableSet_Icc.preimage (by unfold X; fun_prop)
    · exact (measurable_trunc _).comp
        (measurable_suppliedScore.comp
          (by fun_prop : Measurable (fun z : Dataset n × unitInterval × Nuisance =>
            (z.2.2, z.1 i))))
    · fun_prop
  · intro z
    unfold oracleEstimator clip
    constructor
    · exact le_max_left _ _
    · exact max_le (by norm_num) (min_le_right _ _)
/-- The oracle interval is a total Borel map. -/
-- @node: measurable_oracleInterval
@[fun_prop] lemma measurable_oracleInterval (n : ℕ) : Measurable (oracleInterval κ n) := by
  unfold oracleInterval
  have ht := (oracleEstimator_total κ n).1
  fun_prop
/-- Bundled revealed-propensity estimator. -/
def oracleDecision (n : ℕ) : SideEstimator n Nuisance := ⟨oracleEstimator κ n, oracleEstimator_total κ n⟩
/-- Bundled revealed-propensity interval. -/
def oracleIntervalDecision (n : ℕ) : IntervalProc n Nuisance := ⟨oracleInterval κ n, measurable_oracleInterval κ n⟩
/-- Lower pair bandwidth. -/
def oracleLowerH (n : ℕ) : ℝ := oracleH κ n/4
/-- Lower pair triangular amplitude. -/
def oracleLowerT (n : ℕ) : ℝ := oracleLowerH κ n ^ κ.γ/4
/-- Lower pair rare treated outcome. -/
def oracleLowerAmplitude (n : ℕ) : ℝ := oracleLowerT κ n ^ (-1/(κ.p-1))
/-- The lower pair has a triangular deterministic effect. -/
def oracleLowerEffect (n : ℕ) (ε : Bool) (x : unitInterval) : ℝ :=
  if ε then oracleLowerT κ n*max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n) else 0
/-- The original lower pair shares the exact uniform design and the same supplied functions. -/
def oracleLowerOutcomeMeasure (n : ℕ) (ε z : Bool) (x : unitInterval) : Measure ℝ :=
  if z then
    ENNReal.ofReal (1-oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) • Measure.dirac 0 +
    ENNReal.ofReal (oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) • Measure.dirac (oracleLowerAmplitude κ n)
  else Measure.dirac 0
/-- The two-atom original lower pair is Borel. -/
-- @node: measurable_oracleLowerOutcome
@[fun_prop] lemma measurable_oracleLowerOutcome (n : ℕ) (ε z : Bool) :
  Measurable (oracleLowerOutcomeMeasure κ n ε z) := by
  unfold oracleLowerOutcomeMeasure oracleLowerEffect
  cases z <;> cases ε <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
/-- Explicit arm kernel of the original lower pair. -/
def oracleLowerKernel (n : ℕ) (ε z : Bool) : Kernel unitInterval ℝ :=
  ⟨oracleLowerOutcomeMeasure κ n ε z, measurable_oracleLowerOutcome κ n ε z⟩
/-- The lower-pair bandwidth and effect amplitude are positive and at most one. -/
-- @node: oracle_lower_scale_bounds
lemma oracle_lower_scale_bounds (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) :
    0 < oracleLowerH κ n ∧ oracleLowerH κ n ≤ 1 ∧
    0 < oracleLowerT κ n ∧ oracleLowerT κ n ≤ 1 ∧
    1 ≤ oracleLowerAmplitude κ n := by
  have hp : 0 < κ.p := by linarith [hd.1.1.1]
  have hp1 : 0 < κ.p-1 := sub_pos.mpr hd.1.1.1
  have hg : 0 < κ.γ := hd.1.2.2.2.1
  have hq : 0 < qExp κ := div_pos hp1 hp
  have hn : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn
  have hhpos : 0 < oracleLowerH κ n := by
    unfold oracleLowerH oracleH
    positivity
  have hhle : oracleLowerH κ n ≤ 1 := by
    have hh := Real.rpow_le_one_of_one_le_of_nonpos hn
      (show -qExp κ/(κ.γ+qExp κ) ≤ 0 from
        div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) (by positivity))
    unfold oracleLowerH oracleH
    linarith
  have htpos : 0 < oracleLowerT κ n := by
    unfold oracleLowerT
    positivity
  have htle : oracleLowerT κ n ≤ 1 := by
    have ht := Real.rpow_le_one hhpos.le hhle hg.le
    unfold oracleLowerT
    linarith
  refine ⟨hhpos, hhle, htpos, htle, ?_⟩
  unfold oracleLowerAmplitude
  exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos htpos htle
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hp1.le)

/-- The deterministic effect gives a valid two-atom mixing probability at every covariate. -/
-- @node: oracle_lower_mixing_bounds
lemma oracle_lower_mixing_bounds (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n)
    (ε : Bool) (x : unitInterval) :
    0 ≤ oracleLowerEffect κ n ε x / oracleLowerAmplitude κ n ∧
    oracleLowerEffect κ n ε x / oracleLowerAmplitude κ n ≤ 1 := by
  have hb := oracle_lower_scale_bounds κ n hd
  have hB : 0 < oracleLowerAmplitude κ n := lt_of_lt_of_le (by norm_num) hb.2.2.2.2
  have hk : max 0 (1-|(x : ℝ)-1/2|/oracleLowerH κ n) ≤ 1 := by
    apply max_le (by norm_num)
    have : 0 ≤ |(x : ℝ)-1/2|/oracleLowerH κ n := div_nonneg (abs_nonneg _) hb.1.le
    linarith
  have he : 0 ≤ oracleLowerEffect κ n ε x ∧ oracleLowerEffect κ n ε x ≤ 1 := by
    cases ε
    · simp [oracleLowerEffect]
    · simp only [oracleLowerEffect, ↓reduceIte]
      exact ⟨mul_nonneg hb.2.2.1.le (le_max_left _ _),
        (mul_le_mul_of_nonneg_left hk hb.2.2.1.le).trans (by simpa using hb.2.2.2.1)⟩
  exact ⟨div_nonneg he.1 hB.le, (div_le_one hB).mpr (he.2.trans hb.2.2.2.2)⟩

/-- The lower-pair original arm kernels are normalized and have the prescribed means. -/
-- @node: oracle_lower_versions
lemma oracle_lower_versions (n : ℕ) (hd : κ.Valid ∧ 2 ≤ n) (ε : Bool) :
  (∀ z, IsMarkovKernel (oracleLowerKernel κ n ε z)) ∧
  (∀ᵐ x ∂design, (0 : ℝ) = ∫ y, y ∂oracleLowerKernel κ n ε false x) ∧
  (∀ᵐ x ∂design, (0 : ℝ)+oracleLowerEffect κ n ε x = ∫ y, y ∂oracleLowerKernel κ n ε true x) := by
  have hb := oracle_lower_scale_bounds κ n hd
  have hB : 0 < oracleLowerAmplitude κ n := lt_of_lt_of_le (by norm_num) hb.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · intro z
    constructor
    intro x
    constructor
    cases z
    · simp [oracleLowerKernel, oracleLowerOutcomeMeasure]
    · change (oracleLowerOutcomeMeasure κ n ε true x) univ = 1
      have hw := oracle_lower_mixing_bounds κ n hd ε x
      simp only [oracleLowerOutcomeMeasure, ↓reduceIte, Measure.add_apply,
        Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
      rw [← ENNReal.ofReal_add (sub_nonneg.mpr hw.2) hw.1]
      simp
  · filter_upwards [] with x
    simp [oracleLowerKernel, oracleLowerOutcomeMeasure]
  · filter_upwards [] with x
    have hw := oracle_lower_mixing_bounds κ n hd ε x
    change 0 + oracleLowerEffect κ n ε x =
      ∫ y : ℝ, y ∂(ENNReal.ofReal (1-oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) • Measure.dirac 0 +
        ENNReal.ofReal (oracleLowerEffect κ n ε x/oracleLowerAmplitude κ n) • Measure.dirac (oracleLowerAmplitude κ n))
    have hi (a w : ℝ) : Integrable (fun y : ℝ => y) (ENNReal.ofReal w • Measure.dirac a) := by
      first | fun_prop | exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    rw [integral_add_measure (hi _ _) (hi _ _)]
    simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      mul_zero, zero_add, ENNReal.toReal_ofReal hw.1]
    exact (div_mul_cancel₀ _ hB.ne').symm
/-- The two explicit alternatives used for both revelation lower bounds. -/
def oracleLowerLaw (n : ℕ) (ε : Bool) : ObservedLaw :=
  if hd : κ.Valid ∧ 2 ≤ n then
    lawFromUniform (fun _ => 1/2) measurable_const half_range (oracleLowerKernel κ n ε)
      (oracle_lower_versions κ n hd ε).1 (fun _ => 0) (oracleLowerEffect κ n ε)
      (oracle_lower_versions κ n hd ε).2.1 (oracle_lower_versions κ n hd ε).2.2
  else referenceLaw
/-- The four revelation minimax quantities in risk-e, length-e, risk-em, length-em order. -/
def oracleValues (n : ℕ) (expLaw : ExperimentFamily) (j : Fin 4) : ℝ :=
  if j.val = 0 then oracleRisk κ n else if j.val = 1 then oracleLengthE κ n
  else if j.val = 2 then oracleRiskEM κ n else oracleLengthEM κ n

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
