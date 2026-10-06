module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleComparison
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.UpperRisk
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TInteractionObstruction
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TOracleExperiment
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Finite-moment point-CATE frontier: TSharpFiniteMomentPointFrontier. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- Computable public lower constant, independent of the sample size. -/
def cFront (κ : Params) : ℝ := min (3/256) (cInter κ)
/-- Computable public upper constant, independent of the sample size. -/
def CFront (κ : Params) : ℝ := 20*cPub κ
/-- Original values matched to the four revelation comparisons. -/
def originalValues (κ : Params) (n : ℕ) (expLaw : ExperimentFamily) (j : Fin 4) : ℝ :=
  if j.val = 0 ∨ j.val = 2 then minimaxRisk κ n else honestLength κ n
/-- The four original-to-revelation precision ratios. -/
def precisionRatio (κ : Params) (n : ℕ) (expLaw : ExperimentFamily) (j : Fin 4) : ℝ :=
  originalValues κ n expLaw j / oracleValues κ n expLaw j
/-- A nonnegative bound also controls a real supremum when its index type is empty. -/
-- @node: frontier_real_iSup_le
lemma frontier_real_iSup_le {ι : Type*} (f : ι → ℝ) (b : ℝ)
    (hb : 0 ≤ b) (hf : ∀ i, f i ≤ b) : (⨆ i, f i) ≤ b := by
  cases isEmpty_or_nonempty ι with
  | inl hi =>
    letI := hi
    simpa only [iSup, Set.range_eq_empty, Real.sSup_empty] using hb
  | inr hi =>
    letI := hi
    exact ciSup_le hf

/-- Positivity of the explicit grid constant makes the global lower constant positive,
including outside the interaction region where its bound is not needed. -/
-- @node: frontier_lower_constant_positive
lemma frontier_lower_constant_positive (κ : Params) : 0 < cFront κ := by
  have hc : 0 < lowerC κ := by
    unfold lowerC
    apply lt_min
    · norm_num
    · positivity
  have hi : 0 < cInter κ := by
    unfold cInter lowerP0
    positivity
  exact lt_min (by norm_num) hi

/-- The same fixed estimator and honest interval bound the two minimax infima. -/
-- @node: frontier_minimax_upper
lemma frontier_minimax_upper (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    minimaxRisk κ n ≤ CFront κ*rate κ n ∧
    honestLength κ n ≤ CFront κ*rate κ n := by
  have hiid : IIDSampling jointLaw := by
    intro n hn P hP
    rfl
  have hr := upper_risk κ hκ n hn jointLaw hiid
  have hc := cPub_positive κ hκ
  have hrate : 0 ≤ rate κ n := by unfold rate; positivity
  have hbound : 0 ≤ CFront κ*rate κ n := by unfold CFront; positivity
  have hrisk : ∀ law, InModel κ law →
      decisionRisk n jointLaw (fun _ => ()) (upperDecision κ n) law ≤ CFront κ*rate κ n := by
    intro law hm
    have h := hr.2.1 law hm
    unfold CFront
    nlinarith [mul_nonneg hc.le hrate]
  constructor
  · unfold minimaxRisk minimaxRiskWith
    refine ciInf_le_of_le ?_ (upperDecision κ n) ?_
    · refine ⟨0, ?_⟩
      rintro b ⟨t, rfl⟩
      exact Real.iSup_nonneg fun law => integral_nonneg fun z => abs_nonneg _
    · exact frontier_real_iSup_le _ _ hbound (fun law => hrisk law.1 law.2)
  · let i : {i : IntervalProc n Unit // ∀ law, InModel κ law →
        9/10 ≤ coverage n jointLaw (fun _ => ()) i law} :=
      ⟨upperIntervalDecision κ n, hr.2.2.1⟩
    unfold honestLength honestLengthWith
    refine ciInf_le_of_le ?_ i ?_
    · refine ⟨0, ?_⟩
      rintro b ⟨j, rfl⟩
      exact Real.iSup_nonneg fun law => integral_nonneg fun z => intervalCode_length_nonneg _
    · apply frontier_real_iSup_le _ _ hbound
      intro law
      letI : IsProbabilityMeasure (jointLaw n law.1.P) := by
        unfold jointLaw design
        infer_instance
      change (∫ z, (upperInterval κ n (z.1, z.2, ())).length ∂jointLaw n law.1.P) ≤ _
      calc
        _ ≤ ∫ _z, CFront κ*rate κ n ∂jointLaw n law.1.P := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall fun z => intervalCode_length_nonneg _
          · exact integrable_const _
          · exact Filter.Eventually.of_forall fun z =>
              ((hr.2.2.2 (z.1, z.2, ())).1).trans (min_le_right _ _)
        _ = CFront κ*rate κ n := by simp

/-- The oracle lower bound handles the oracle phase; the original-law interaction
certificate handles the other phase, with the explicit minimum constant in both. -/
-- @node: frontier_minimax_lower
lemma frontier_minimax_lower (κ : Params) (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
    cFront κ*rate κ n ≤ minimaxRisk κ n ∧
    cFront κ*rate κ n ≤ honestLength κ n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp : 0 ≤ (n : ℝ)^(-rOracle κ) := by positivity
  have hi : 0 ≤ (n : ℝ)^(-rInter κ) := by positivity
  have ho := (oracle_experiment_concrete κ hκ expLaw hiid).2.1 n hn
  have hcmp := oracle_comparison κ hκ n hn expLaw hiid
  have hR : (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ minimaxRisk κ n := by
    have h : (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ oracleRisk κ n := by
      simpa [oracleValues] using (ho 0).1
    exact h.trans hcmp.1
  have hL : (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ honestLength κ n := by
    have h : (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ oracleLengthE κ n := by
      simpa [oracleValues] using (ho 1).1
    exact h.trans hcmp.2.2.1
  by_cases hb : boundary κ ≤ 1
  · have hexp := (phase_algebra κ hκ).2.1.mpr hb
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hexp)
    have hr : rate κ n = (n : ℝ)^(-rInter κ) := max_eq_right hpow
    have hl := (interaction_obstruction_concrete κ hκ hb expLaw hiid).2.1 n hn
    have hc : cFront κ ≤ cInter κ := min_le_right _ _
    rw [hr]
    exact ⟨(mul_le_mul_of_nonneg_right hc hi).trans hl.1,
      (mul_le_mul_of_nonneg_right hc hi).trans hl.2.1⟩
  · have hexp : rOracle κ ≤ rInter κ := by
      have hnot : ¬ rInter κ ≤ rOracle κ := fun h => hb ((phase_algebra κ hκ).2.1.mp h)
      exact le_of_lt (lt_of_not_ge hnot)
    have hpow := Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hexp)
    have hr : rate κ n = (n : ℝ)^(-rOracle κ) := max_eq_left hpow
    have hc : cFront κ ≤ 3/256 := min_le_left _ _
    rw [hr]
    exact ⟨(mul_le_mul_of_nonneg_right hc hp).trans hR,
      (mul_le_mul_of_nonneg_right hc hp).trans hL⟩

/-- Matching finite-sample values and all deterministic certificates are assembled
from the explicit upper procedure and the two phase-specific lower comparisons. -/
-- @node: frontier_finite_sample_certificate
lemma frontier_finite_sample_certificate (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  (0 < cFront κ ∧ cFront κ ≤ CFront κ) ∧
  (∀ n : ℕ, 2 ≤ n →
    (cFront κ*rate κ n ≤ minimaxRisk κ n ∧ minimaxRisk κ n ≤ CFront κ*rate κ n) ∧
    (cFront κ*rate κ n ≤ honestLength κ n ∧ honestLength κ n ≤ CFront κ*rate κ n) ∧
    Measurable (upperEstimator κ n) ∧ (∀ z, upperEstimator κ n z ∈ Icc (-1/2) (1/2)) ∧
    Measurable (upperInterval κ n) ∧
    (∀ law, InModel κ law → decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤ cPub κ*rate κ n ∧
      9/10 ≤ coverage n expLaw (fun _ => ()) (upperIntervalDecision κ n) law) ∧
    (∀ z, (upperInterval κ n z).length ≤ min 1 (20*cPub κ*rate κ n) ∧
      ∃ c : Endpoints, upperInterval κ n z = .inr c ∧ c.1.2.2.1 = true ∧ c.1.2.2.2 = true) ∧
    (0 < upperH κ n ∧ upperH κ n ≤ 1) ∧
    1 ≤ (n : ℝ)*upperH κ n ∧
    cellLen (upperH κ n) (upperJ κ n)^effectiveS κ ≤ 4*rate κ n ∧
    (∀ j, 1 ≤ upperT κ n j) ∧
    (0 < constantA κ ∧ 0 < constantE κ ∧ 0 < constantF κ) ∧
    (∀ law, InModel κ law → 3/16 ≤ localDenominator law (upperH κ n) (upperJ κ n))) := by
  have hc := frontier_lower_constant_positive κ
  have hconst : cFront κ ≤ CFront κ := by
    have hl := (frontier_minimax_lower κ hκ 2 (by omega) expLaw hiid).1
    have hu := (frontier_minimax_upper κ hκ 2 (by omega)).1
    have hp : 0 < rate κ 2 := by unfold rate; positivity
    nlinarith [hl.trans hu]
  refine ⟨⟨hc, hconst⟩, ?_⟩
  intro n hn
  have hl := frontier_minimax_lower κ hκ n hn expLaw hiid
  have hu := frontier_minimax_upper κ hκ n hn
  have hr := upper_risk κ hκ n hn expLaw hiid
  have ht := upper_tuning κ hκ n hn
  have hphase := phase_algebra κ hκ
  refine ⟨⟨hl.1, hu.1⟩, ⟨hl.2, hu.2⟩,
    (upperEstimator_total κ n).1, (upperEstimator_total κ n).2,
    measurable_upperInterval κ n, ?_, hr.2.2.2, ht.1, ht.2.1,
    ht.2.2.2.2.1, ht.2.2.2.2.2.1, hphase.2.2.2.2, ?_⟩
  · intro law hm
    exact ⟨hr.2.1 law hm, hr.2.2.1 law hm⟩
  · intro law hm
    exact (local_covariance_bias κ hκ law hm _ ht.1 (upperJ κ n)).1

/-- Each original quantity has the same finite-sample sandwich, including both
copies used for the two revelation experiments. -/
-- @node: frontier_original_values_bounds
lemma frontier_original_values_bounds (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) (n : ℕ) (hn : 2 ≤ n)
    (j : Fin 4) :
    cFront κ*rate κ n ≤ originalValues κ n expLaw j ∧
    originalValues κ n expLaw j ≤ CFront κ*rate κ n := by
  have hl := frontier_minimax_lower κ hκ n hn expLaw hiid
  have hu := frontier_minimax_upper κ hκ n hn
  unfold originalValues
  split
  · exact ⟨hl.1, hu.1⟩
  · exact ⟨hl.2, hu.2⟩

/-- Dividing the benchmark by the oracle power leaves the maximum of one and
the interaction-to-oracle power. -/
-- @node: frontier_rate_quotient
lemma frontier_rate_quotient (κ : Params) (n : ℕ) (hn : 2 ≤ n) :
    rate κ n / (n : ℝ)^(-rOracle κ) =
      max 1 ((n : ℝ)^(rOracle κ-rInter κ)) := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ)^(-rOracle κ) := Real.rpow_pos_of_pos hnpos _
  unfold rate
  rw [← max_div_div_right hp.le, div_self hp.ne', ← Real.rpow_sub hnpos]
  congr 2
  ring

/-- Full-experiment and oracle certificates give a two-sided ratio bound with
strictly positive denominators for all four revelation comparisons. -/
-- @node: frontier_precision_ratio_bounds
lemma frontier_precision_ratio_bounds (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) (n : ℕ) (hn : 2 ≤ n)
    (j : Fin 4) :
    (cFront κ / oracleUpper κ)*max 1 ((n : ℝ)^(rOracle κ-rInter κ)) ≤
      precisionRatio κ n expLaw j ∧
    precisionRatio κ n expLaw j ≤
      (CFront κ / (3/256))*max 1 ((n : ℝ)^(rOracle κ-rInter κ)) := by
  have ho := oracle_experiment_concrete κ hκ expLaw hiid
  have hu : 0 < oracleUpper κ := lt_of_lt_of_le ho.1.1 ho.1.2.1
  have hf := frontier_original_values_bounds κ hκ expLaw hiid n hn j
  have hor := ho.2.1 n hn j
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ)^(-rOracle κ) := Real.rpow_pos_of_pos hnpos _
  have hd : 0 < oracleValues κ n expLaw j :=
    lt_of_lt_of_le (mul_pos (by norm_num) hp) hor.1
  have hr : 0 < rate κ n := by unfold rate; positivity
  have hc := frontier_lower_constant_positive κ
  have hquot := frontier_rate_quotient κ n hn
  have hl : cFront κ*rate κ n / (oracleUpper κ*(n : ℝ)^(-rOracle κ)) ≤
      precisionRatio κ n expLaw j := by
    unfold precisionRatio
    apply (div_le_div_iff₀ (mul_pos hu hp) hd).mpr
    exact (mul_le_mul_of_nonneg_left hor.2 (mul_pos hc hr).le).trans
      (mul_le_mul_of_nonneg_right hf.1 (mul_pos hu hp).le)
  have hh : precisionRatio κ n expLaw j ≤
      CFront κ*rate κ n / ((3/256)*(n : ℝ)^(-rOracle κ)) := by
    unfold precisionRatio
    apply (div_le_div_iff₀ hd (mul_pos (by norm_num) hp)).mpr
    have hC : 0 ≤ CFront κ*rate κ n := (hf.1.trans hf.2).trans' (mul_pos hc hr).le
    exact (mul_le_mul_of_nonneg_right hf.2 (mul_pos (by norm_num) hp).le).trans
      (mul_le_mul_of_nonneg_left hor.1 hC)
  have he (a b : ℝ) : a*rate κ n / (b*(n : ℝ)^(-rOracle κ)) =
      (a/b)*max 1 ((n : ℝ)^(rOracle κ-rInter κ)) := by
    rw [← hquot]
    ring
  exact ⟨by simpa only [he] using hl, by simpa only [he] using hh⟩

/-- The positive coefficient in the phase identity makes the oracle-minus-
interaction gap positive exactly below the boundary, and nonpositive above it. -/
-- @node: frontier_phase_gap_sign
lemma frontier_phase_gap_sign (κ : Params) (hκ : κ.Valid) :
    (0 < rOracle κ-rInter κ ↔ boundary κ < 1) ∧
    (rOracle κ-rInter κ ≤ 0 ↔ 1 ≤ boundary κ) := by
  have hp : 0 < κ.p := lt_trans (by norm_num) hκ.1.1
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hg := hκ.2.2.2.1
  have hβ := hκ.2.2.1.1
  have hα := hκ.2.1.1
  let D := 1+(κ.α+κ.β)/κ.γ+2*κ.α+κ.β/qExp κ
  have hf : 0 < κ.γ*qExp κ/(D*(κ.γ+qExp κ)) := by dsimp [D]; positivity
  have hbid : boundary κ = (κ.α+κ.β)/κ.γ+2*κ.α/(κ.p-1)+κ.β/qExp κ := by
    unfold boundary sumReg qExp
    field_simp
    ring
  have hid := phase_exponent_difference κ hκ κ.α hα
  change rInter κ-rOracle κ = _ at hid
  rw [← hbid] at hid
  have hgap : rOracle κ-rInter κ =
      (κ.γ*qExp κ/(D*(κ.γ+qExp κ)))*(1-boundary κ) := by
    dsimp [D]
    linarith [hid]
  rw [hgap, mul_pos_iff_of_pos_left hf, sub_pos, mul_nonpos_iff, sub_nonpos]
  simp only [hf.le, not_le.mpr hf, true_and, false_and, or_false]

/-- Below the public boundary the maximum power is the strictly increasing
interaction-to-oracle power, giving its order for each risk and length ratio. -/
-- @node: frontier_precision_ratio_order
lemma frontier_precision_ratio_order (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) (hb : boundary κ < 1) :
    ∀ j : Fin 4, ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
      c*(n : ℝ)^(rOracle κ-rInter κ) ≤ precisionRatio κ n expLaw j ∧
      precisionRatio κ n expLaw j ≤ C*(n : ℝ)^(rOracle κ-rInter κ) := by
  have ho := oracle_experiment_concrete κ hκ expLaw hiid
  have hu : 0 < oracleUpper κ := lt_of_lt_of_le ho.1.1 ho.1.2.1
  have hc := frontier_lower_constant_positive κ
  have hle := (frontier_finite_sample_certificate κ hκ expLaw hiid).1.2
  have hexp := (frontier_phase_gap_sign κ hκ).1.mpr hb
  intro j
  refine ⟨cFront κ/oracleUpper κ, CFront κ/(3/256), div_pos hc hu, ?_, ?_⟩
  · apply (div_le_div_iff₀ hu (by norm_num : (0 : ℝ) < 3/256)).mpr
    exact (mul_le_mul_of_nonneg_right hle (by norm_num)).trans
      (mul_le_mul_of_nonneg_left ho.1.2.1 (hc.le.trans hle))
  · intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    simpa only [max_eq_right (Real.one_le_rpow hn1 hexp.le)] using
      frontier_precision_ratio_bounds κ hκ expLaw hiid n hn j

/-- Ratios are bounded exactly in the oracle phase; in the other phase their
positive power lower bound rules out any finite upper bound. -/
-- @node: frontier_precision_ratio_boundary
lemma frontier_precision_ratio_boundary (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) (j : Fin 4) :
    BddAbove {v : ℝ | ∃ n : ℕ, 2 ≤ n ∧ v = precisionRatio κ n expLaw j} ↔
      1 ≤ boundary κ := by
  constructor
  · intro hbounded
    by_contra hb
    have hb' : boundary κ < 1 := lt_of_not_ge hb
    obtain ⟨c, C, hc, hle, hbounds⟩ := frontier_precision_ratio_order κ hκ expLaw hiid hb' j
    have hexp := (frontier_phase_gap_sign κ hκ).1.mpr hb'
    obtain ⟨b, hbound⟩ := hbounded
    have ht : Filter.Tendsto (fun n : ℕ => (n : ℝ)^(rOracle κ-rInter κ))
        Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
    obtain ⟨n, hn, hnlarge⟩ := Filter.exists_lt_of_tendsto_atTop ht 2 (b/c)
    have hv := hbound (show precisionRatio κ n expLaw j ∈
        {v : ℝ | ∃ n : ℕ, 2 ≤ n ∧ v = precisionRatio κ n expLaw j} from ⟨n, hn, rfl⟩)
    have hgt : b < c*(n : ℝ)^(rOracle κ-rInter κ) := by
      simpa only [mul_comm] using (div_lt_iff₀ hc).mp hnlarge
    linarith [(hbounds n hn).1]
  · intro hb
    have hexp := (frontier_phase_gap_sign κ hκ).2.mpr hb
    refine ⟨CFront κ/(3/256), ?_⟩
    rintro v ⟨n, hn, rfl⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
    have hpow := Real.rpow_le_one_of_one_le_of_nonpos hn1 hexp
    simpa only [max_eq_left hpow, mul_one] using
      (frontier_precision_ratio_bounds κ hκ expLaw hiid n hn j).2

/-- The coordinate functions of the public tuple are continuous in its
specified product topology. -/
-- @node: frontier_parameter_coordinates_continuous
lemma frontier_parameter_coordinates_continuous :
    Continuous (fun κ : Params => κ.p) ∧ Continuous (fun κ : Params => κ.α) ∧
    Continuous (fun κ : Params => κ.β) ∧ Continuous (fun κ : Params => κ.γ) := by
  have h : Continuous (fun κ : Params => (κ.p, κ.α, κ.β, κ.γ)) := continuous_induced_dom
  exact ⟨h.fst, h.snd.fst, h.snd.snd.fst, h.snd.snd.snd⟩

/-- The explicit lower constant is continuous on any set of valid tuples:
the smoothness sum is nonzero and every real-power base is positive. -/
-- @node: frontier_lower_constant_continuousOn
lemma frontier_lower_constant_continuousOn (K : Set Params)
    (hK : K ⊆ {κ | κ.Valid}) : ContinuousOn cFront K := by
  obtain ⟨hp, ha, hb, hg⟩ := frontier_parameter_coordinates_continuous
  have hs : ContinuousOn sumReg K := ha.continuousOn.add hb.continuousOn
  have hsne : ∀ κ ∈ K, sumReg κ ≠ 0 := by
    intro κ hκ
    have hm := hK hκ
    exact (add_pos hm.2.1.1 hm.2.2.1.1).ne'
  have hlc : ContinuousOn lowerC K := by
    unfold lowerC
    apply continuousOn_const.inf
    apply continuousOn_const.rpow ((hg.continuousOn.neg).div hs hsne)
    intro κ hκ
    left
    norm_num
  have hlpos : ∀ κ ∈ K, lowerC κ ≠ 0 := by
    intro κ hκ
    unfold lowerC
    apply ne_of_gt
    apply lt_min
    · norm_num
    · positivity
  have hpow := hlc.rpow hs (fun κ hκ => Or.inl (hlpos κ hκ))
  unfold cFront cInter
  exact continuousOn_const.inf
    ((continuousOn_const.mul hpow).div_const _)

/-- Every denominator in the public upper ledger stays nonzero on valid
parameters, so the finite sums, square roots and real powers are continuous. -/
-- @node: frontier_upper_constant_continuousOn
lemma frontier_upper_constant_continuousOn (K : Set Params)
    (hK : K ⊆ {κ | κ.Valid}) : ContinuousOn CFront K := by
  obtain ⟨hp, ha, hb, hg⟩ := frontier_parameter_coordinates_continuous
  have hpne : ∀ κ ∈ K, κ.p ≠ 0 := by
    intro κ hκ
    exact (lt_trans (by norm_num) (hK hκ).1.1).ne'
  have hq : ContinuousOn qExp K :=
    (hp.continuousOn.sub continuousOn_const).div hp.continuousOn hpne
  have hA : ContinuousOn effectiveA K :=
    ha.continuousOn.inf ((hp.continuousOn.sub continuousOn_const).div_const 2)
  have hD : ContinuousOn effectiveD K :=
    hq.sub ((hA.mul (continuousOn_const.sub hp.continuousOn)).div hp.continuousOn hpne)
  have hpow (f : Params → ℝ) (hf : ContinuousOn f K) :
      ContinuousOn (fun κ => (2 : ℝ)^(f κ)) K :=
    continuousOn_const.rpow hf (fun κ hκ => Or.inl (by norm_num))
  have hcA : ContinuousOn constantA K := continuousOn_const.sub (hpow _ hA.neg)
  have hcE : ContinuousOn constantE K := continuousOn_const.sub (hpow _ hD.neg)
  have hcF : ContinuousOn constantF K :=
    continuousOn_const.sub (hpow _ (continuousOn_const.mul hq))
  have hneA : ∀ κ ∈ K, constantA κ ≠ 0 :=
    fun κ hκ => (phase_algebra κ (hK hκ)).2.2.2.2.1.ne'
  have hneE : ∀ κ ∈ K, constantE κ ≠ 0 :=
    fun κ hκ => (phase_algebra κ (hK hκ)).2.2.2.2.2.1.ne'
  have hneF : ∀ κ ∈ K, constantF κ ≠ 0 :=
    fun κ hκ => (phase_algebra κ (hK hκ)).2.2.2.2.2.2.ne'
  have hcG : ContinuousOn cG K := by
    unfold cG
    apply continuousOn_const.mul
    exact continuousOn_const.rpow (continuousOn_const.div hp.continuousOn hpne)
      (fun κ hκ => Or.inl (by norm_num))
  have hcB : ContinuousOn cBias K :=
    (continuousOn_const.add (continuousOn_const.div hcA hneA)).add
      (continuousOn_const.div hcE hneE)
  have hinv (f : Params → ℝ) (hf : ContinuousOn f K)
      (hfpos : ∀ κ ∈ K, 0 < f κ) :
      ContinuousOn (fun κ => (1-(2 : ℝ)^(-2*f κ))⁻¹) K := by
    apply (continuousOn_const.sub (hpow _ (continuousOn_const.mul hf))).inv₀
    intro κ hκ
    apply ne_of_gt
    apply sub_pos.mpr
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      change -2*f κ < 0
      linarith [hfpos κ hκ])
  have hiA := hinv effectiveA hA (fun κ hκ => (phase_algebra κ (hK hκ)).2.2.1)
  have hiD := hinv effectiveD hD (fun κ hκ => (phase_algebra κ (hK hκ)).2.2.2.1)
  have hcN : ContinuousOn cNoise K :=
    ((continuousOn_const.mul
      (continuousOn_const.add (continuousOn_const.div hcA hneA))).add
      ((continuousOn_const.mul
        (hcG.add (continuousOn_const.div hcF hneF))).sqrt)).add
      ((continuousOn_const.mul
        ((continuousOn_const.add hiA).add (continuousOn_const.mul hiD))).sqrt)
  unfold CFront cPub
  exact continuousOn_const.mul
    (continuousOn_const.mul ((hcB.add hcN).add continuousOn_const))

/-- Attainment of the positive minimum and finite maximum of the public
constant formulas yields uniform constants on every compact parameter set. -/
-- @node: frontier_compact_constants
lemma frontier_compact_constants (K : Set Params) (hcompact : IsCompact K)
    (hK : K ⊆ {κ | κ.Valid}) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧ ∀ κ ∈ K, c0 ≤ cFront κ ∧ CFront κ ≤ C0 := by
  by_cases hne : K.Nonempty
  · obtain ⟨a, ha, hmin⟩ := hcompact.exists_isMinOn hne
      (frontier_lower_constant_continuousOn K hK)
    obtain ⟨b, hb, hmax⟩ := hcompact.exists_isMaxOn hne
      (frontier_upper_constant_continuousOn K hK)
    refine ⟨cFront a, max (cFront a) (CFront b), frontier_lower_constant_positive a,
      le_max_left _ _, ?_⟩
    intro κ hκ
    exact ⟨hmin hκ, (hmax hκ).trans (le_max_right _ _)⟩
  · refine ⟨1, 1, by norm_num, le_rfl, ?_⟩
    intro κ hκ
    exact (hne ⟨κ, hκ⟩).elim

-- @node: thm:sharp-finite-moment-point-frontier
/-- For [a valid public tuple](hyp:κ,hκ) and [iid original experiments](hyp:expLaw,hiid),
[the pure-power risk and honest-length frontier is attained by one pair of public procedures at
every finite sample size, with compact-uniform constants, all four revelation-survival boundaries
and the full diverging-ratio order below the boundary](goal). -/
theorem sharp_finite_moment_point_frontier (κ : Params) (hκ : κ.Valid)
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  (0 < cFront κ ∧ cFront κ ≤ CFront κ) ∧
  (∀ n : ℕ, 2 ≤ n →
    (cFront κ*rate κ n ≤ minimaxRisk κ n ∧ minimaxRisk κ n ≤ CFront κ*rate κ n) ∧
    (cFront κ*rate κ n ≤ honestLength κ n ∧ honestLength κ n ≤ CFront κ*rate κ n) ∧
    Measurable (upperEstimator κ n) ∧ (∀ z, upperEstimator κ n z ∈ Icc (-1/2) (1/2)) ∧
    Measurable (upperInterval κ n) ∧
    (∀ law, InModel κ law → decisionRisk n expLaw (fun _ => ()) (upperDecision κ n) law ≤ cPub κ*rate κ n ∧
      9/10 ≤ coverage n expLaw (fun _ => ()) (upperIntervalDecision κ n) law) ∧
    (∀ z, (upperInterval κ n z).length ≤ min 1 (20*cPub κ*rate κ n) ∧
      ∃ c : Endpoints, upperInterval κ n z = .inr c ∧ c.1.2.2.1 = true ∧ c.1.2.2.2 = true) ∧
    (0 < upperH κ n ∧ upperH κ n ≤ 1) ∧
    1 ≤ (n : ℝ)*upperH κ n ∧
    cellLen (upperH κ n) (upperJ κ n)^effectiveS κ ≤ 4*rate κ n ∧
    (∀ j, 1 ≤ upperT κ n j) ∧
    (0 < constantA κ ∧ 0 < constantE κ ∧ 0 < constantF κ) ∧
    (∀ law, InModel κ law → 3/16 ≤ localDenominator law (upperH κ n) (upperJ κ n))) ∧
  (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid} →
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧ ∀ κ' ∈ K, c0 ≤ cFront κ' ∧ CFront κ' ≤ C0) ∧
  (∀ j : Fin 4, BddAbove {v : ℝ | ∃ n : ℕ, 2 ≤ n ∧ v = precisionRatio κ n expLaw j} ↔ 1 ≤ boundary κ) ∧
  (boundary κ < 1 → ∀ j : Fin 4, ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
    c*(n : ℝ)^(rOracle κ-rInter κ) ≤ precisionRatio κ n expLaw j ∧
    precisionRatio κ n expLaw j ≤ C*(n : ℝ)^(rOracle κ-rInter κ)) := by
  have hf := frontier_finite_sample_certificate κ hκ expLaw hiid
  exact ⟨hf.1, hf.2, frontier_compact_constants,
    frontier_precision_ratio_boundary κ hκ expLaw hiid,
    frontier_precision_ratio_order κ hκ expLaw hiid⟩

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
