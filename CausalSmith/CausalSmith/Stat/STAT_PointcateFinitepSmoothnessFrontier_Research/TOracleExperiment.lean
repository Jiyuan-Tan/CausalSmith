module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LowerIntervalDecision
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleCoverage
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleSampleRisk
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleRecord
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleTV
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.OracleUpperReduction

/-! Finite-moment point-CATE frontier: TOracleExperiment. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
variable (κ : Params)

/-- The oracle localization balances the Holder bias and the heavy-tail sampling power exactly. -/
-- @node: oracle_tuning_identities
lemma oracle_tuning_identities (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (0 < oracleH κ n ∧ oracleH κ n ≤ 1) ∧
    1 ≤ (n : ℝ)*oracleH κ n ∧ 1 ≤ oracleT κ n ∧
    oracleH κ n^κ.γ = (n : ℝ)^(-rOracle κ) ∧
    oracleT κ n^(1-κ.p) = (n : ℝ)^(-rOracle κ) ∧
    oracleT κ n^(2-κ.p)/((n : ℝ)*oracleH κ n) =
      ((n : ℝ)^(-rOracle κ))^2 := by
  have hp : 0 < κ.p := by linarith [hκ.1.1]
  have hq : 0 < qExp κ := div_pos (sub_pos.mpr hκ.1.1) hp
  have hg := hκ.2.2.2.1
  have hden : 0 < κ.γ+qExp κ := by positivity
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num) hn1
  have hh : 0 < oracleH κ n := by unfold oracleH; positivity
  have hprod : (n : ℝ)*oracleH κ n = (n : ℝ)^(κ.γ/(κ.γ+qExp κ)) := by
    unfold oracleH
    calc
      (n : ℝ) * (n : ℝ)^(-qExp κ/(κ.γ+qExp κ)) =
          (n : ℝ)^1 * (n : ℝ)^(-qExp κ/(κ.γ+qExp κ)) := by rw [Real.rpow_one]
      _ = (n : ℝ)^(1 + -qExp κ/(κ.γ+qExp κ)) := (Real.rpow_add hnpos _ _).symm
      _ = (n : ℝ)^(κ.γ/(κ.γ+qExp κ)) := by
        congr 1
        field_simp
        ring
  have hnh : 1 ≤ (n : ℝ)*oracleH κ n := by
    rw [hprod]
    exact Real.one_le_rpow hn1 (by positivity)
  have hnhpos : 0 < (n : ℝ)*oracleH κ n := by positivity
  have hnoise : ((n : ℝ)*oracleH κ n)^(-qExp κ) = (n : ℝ)^(-rOracle κ) := by
    rw [hprod, ← Real.rpow_mul hnpos.le]
    unfold rOracle
    congr 1
    ring
  refine ⟨⟨hh, ?_⟩, hnh, ?_, ?_, ?_, ?_⟩
  · unfold oracleH
    exact Real.rpow_le_one_of_one_le_of_nonpos hn1
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq.le) hden.le)
  · unfold oracleT
    exact Real.one_le_rpow hnh (by positivity)
  · unfold oracleH
    rw [← Real.rpow_mul hnpos.le]
    unfold rOracle
    congr 1
    ring
  · unfold oracleT
    rw [← Real.rpow_mul hnhpos.le]
    have hexp : 1/κ.p*(1-κ.p) = -qExp κ := by unfold qExp; ring
    rw [hexp, hnoise]
  · unfold oracleT
    rw [← Real.rpow_mul hnhpos.le]
    have hdiv (a : ℝ) : ((n : ℝ)*oracleH κ n)^a / ((n : ℝ)*oracleH κ n) =
        ((n : ℝ)*oracleH κ n)^(a-1) := by
      simpa only [Real.rpow_one] using (Real.rpow_sub hnhpos a 1).symm
    rw [hdiv]
    have hexp : 1/κ.p*(2-κ.p)-1 = -qExp κ*2 := by
      unfold qExp
      field_simp
      ring
    rw [hexp, Real.rpow_mul hnhpos.le, hnoise, Real.rpow_two]

/-- The public tuning turns the bias-plus-standard-deviation bound into the oracle power. -/
-- @node: oracle_tuned_risk_bound
lemma oracle_tuned_risk_bound (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) (R : ℝ)
    (hR : R ≤ 20*oracleH κ n^κ.γ + oracleMoment κ*oracleT κ n^(1-κ.p) +
      Real.sqrt (oracleMoment κ*(oracleT κ n^(2-κ.p)/((n : ℝ)*oracleH κ n)))) :
    R ≤ oracleConstant κ*(n : ℝ)^(-rOracle κ) := by
  have ht := oracle_tuning_identities κ hκ n hn
  have hM : 0 ≤ oracleMoment κ := by unfold oracleMoment; positivity
  have hr : 0 ≤ (n : ℝ)^(-rOracle κ) := by positivity
  rw [ht.2.2.2.1, ht.2.2.2.2.1, ht.2.2.2.2.2,
    Real.sqrt_mul hM, Real.sqrt_sq_eq_abs, abs_of_nonneg hr] at hR
  unfold oracleConstant
  nlinarith [hR]

/-- The score envelope and comparison constants have a universal numerical upper bound. -/
-- @node: oracle_constant_bounds
lemma oracle_constant_bounds (hκ : κ.Valid) :
    0 < (3/256 : ℝ) ∧ (3/256 : ℝ) ≤ oracleUpper κ ∧ oracleUpper κ ≤ 4000 := by
  have hmpos : 0 ≤ oracleMoment κ := by unfold oracleMoment; positivity
  have hm : oracleMoment κ ≤ 160 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 4 by norm_num) hκ.1.2
    norm_num at hpow
    unfold oracleMoment
    linarith
  have hs : Real.sqrt (oracleMoment κ) ≤ 20 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · linarith
  unfold oracleUpper oracleConstant
  refine ⟨by norm_num, ?_, ?_⟩
  · nlinarith [Real.sqrt_nonneg (oracleMoment κ)]
  · linarith

/-- Universal constants supply the requested uniformity on every compact parameter set. -/
-- @node: oracle_compact_constants
lemma oracle_compact_constants (K : Set Params) (hK : IsCompact K)
    (hsub : K ⊆ {κ | κ.Valid}) :
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧
      ∀ κ' ∈ K, c0 ≤ (3/256 : ℝ) ∧ oracleUpper κ' ≤ C0 := by
  refine ⟨3/256, 4000, by norm_num, by norm_num, ?_⟩
  intro κ' hmem
  exact ⟨le_rfl, (oracle_constant_bounds κ' (hsub hmem)).2.2⟩

/-- The public-radius oracle interval has the stated finite-sample length on every input. -/
-- @node: oracle_interval_length
lemma oracle_interval_length (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (z : Dataset n × unitInterval × Nuisance) :
    (oracleInterval κ n z).length ≤ min 1 (20*oracleConstant κ*(n : ℝ)^(-rOracle κ)) := by
  have ht := (oracleEstimator_total κ n).2 z
  have hc : 0 ≤ oracleConstant κ := by unfold oracleConstant oracleMoment; positivity
  have hr : 0 ≤ 10*oracleConstant κ*(n : ℝ)^(-rOracle κ) := by positivity
  let t := oracleEstimator κ n z
  let r := 10*oracleConstant κ*(n : ℝ)^(-rOracle κ)
  have hlo : max (-1/2 : ℝ) (t-r) ≤ t := max_le ht.1 (by dsimp [r]; linarith)
  have hhi : t ≤ min (1/2 : ℝ) (t+r) := le_min ht.2 (by dsimp [r]; linarith)
  have hv : (-1/2 : ℝ) ≤ max (-1/2) (t-r) ∧
      max (-1/2) (t-r) ≤ min (1/2) (t+r) ∧ min (1/2) (t+r) ≤ 1/2 :=
    ⟨le_max_left _ _, hlo.trans hhi, min_le_left _ _⟩
  change (closedInterval (max (-1/2) (t-max 0 r)) (min (1/2) (t+max 0 r))).length ≤ _
  rw [max_eq_right hr]
  dsimp only [r] at hv
  simp only [closedInterval, dif_pos hv, IntervalCode.length, Causalean.Stat.intervalLength]
  apply max_le
  · exact le_min (by norm_num) (by positivity)
  · apply le_min
    · linarith [le_max_left (-1/2 : ℝ) (t-r), min_le_left (1/2 : ℝ) (t+r)]
    · have h1 := le_max_right (-1/2 : ℝ) (t-r)
      have h2 := min_le_right (1/2 : ℝ) (t+r)
      dsimp [r] at h1 h2
      linarith

/-- Both lower alternatives reveal the identical propensity and baseline functions. -/
-- @node: oracle_lower_revelations
lemma oracle_lower_revelations (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    sideEM (oracleLowerLaw κ n true) = sideEM (oracleLowerLaw κ n false) ∧
    sideE (oracleLowerLaw κ n true) = sideE (oracleLowerLaw κ n false) := by
  simp [sideEM, sideE, oracleLowerLaw, dif_pos (And.intro hκ hn), lawFromUniform]

/-- The explicit rare-outcome pair has the roadmap's deterministic oracle target separation. -/
-- @node: oracle_lower_separation
lemma oracle_lower_separation (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    (1/16 : ℝ)*(n : ℝ)^(-rOracle κ) ≤
      |(oracleLowerLaw κ n true).theta-(oracleLowerLaw κ n false).theta| := by
  have hb := oracle_lower_scale_bounds κ n ⟨hκ, hn⟩
  have heq : |(oracleLowerLaw κ n true).theta-(oracleLowerLaw κ n false).theta| =
      oracleLowerT κ n := by
    simp [oracleLowerLaw, dif_pos (And.intro hκ hn), ObservedLaw.theta, lawFromUniform,
      oracleLowerEffect, xstar, abs_of_pos hb.2.2.1]
  rw [heq]
  have hquarter : (1/4 : ℝ) ≤ (1/4 : ℝ)^κ.γ := by
    have h := Real.rpow_le_rpow_of_exponent_ge (show (0 : ℝ) < 1/4 by norm_num)
      (show (1/4 : ℝ) ≤ 1 by norm_num) hκ.2.2.2.2
    simpa only [Real.rpow_one] using h
  have hh := (oracle_tuning_identities κ hκ n hn).1.1
  have ht : oracleLowerT κ n = oracleH κ n^κ.γ * (1/4 : ℝ)^κ.γ / 4 := by
    unfold oracleLowerT oracleLowerH
    have hmul : oracleH κ n / 4 = oracleH κ n * (1/4 : ℝ) := by ring
    rw [hmul, Real.mul_rpow hh.le (by norm_num)]
  rw [ht, (oracle_tuning_identities κ hκ n hn).2.2.2.1]
  have hr : 0 ≤ (n : ℝ)^(-rOracle κ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hquarter hr]

/-- Fixing supplied information gives an original measurable range-valued estimator. -/
-- @node: oracle_fixed_side_estimator
def oracle_fixed_side_estimator {S : Type*} [MeasurableSpace S] (n : ℕ)
    (t : SideEstimator n S) (s : S) : Estimator n :=
  ⟨fun z => t.1 (z.1,z.2.1,s), t.2.1.comp (by fun_prop), fun z => t.2.2 _⟩

/-- Bounded decisions give integrable loss and risk at most one for every supplied value. -/
-- @node: oracle_side_risk_bounds
lemma oracle_side_risk_bounds {S : Type*} [MeasurableSpace S] (n : ℕ)
    (side : ObservedLaw → S) (t : SideEstimator n S) (law : ObservedLaw)
    (hm : InModel κ law) :
    Integrable (fun z : Experiment n => |t.1 (z.1,z.2,side law)-law.theta|)
      (jointLaw n law.P) ∧ decisionRisk n jointLaw side t law ≤ 1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (jointLaw n law.P) := by unfold jointLaw; infer_instance
  exact ⟨lower_decision_loss_integrable n (oracle_fixed_side_estimator n t (side law)) _ _,
    (lower_decision_risk_bounds κ n (oracle_fixed_side_estimator n t (side law)) law hm).2⟩

/-- Identical supplied functions let the oracle pair force a lower risk for every decision. -/
-- @node: oracle_lower_worst_risk
lemma oracle_lower_worst_risk {S : Type*} [MeasurableSpace S] (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (side : ObservedLaw → S)
    (hs : side (oracleLowerLaw κ n true) = side (oracleLowerLaw κ n false))
    (t : SideEstimator n S) :
    (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤
      ⨆ law : {law // InModel κ law}, decisionRisk n jointLaw side t law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let ν0 := jointLaw n (oracleLowerLaw κ n true).P
  let ν1 := jointLaw n (oracleLowerLaw κ n false).P
  letI : IsProbabilityMeasure ν0 := by dsimp [ν0]; unfold jointLaw; infer_instance
  letI : IsProbabilityMeasure ν1 := by dsimp [ν1]; unfold jointLaw; infer_instance
  have hm := oracle_lower_membership κ n hκ hn
  have hsep := oracle_lower_separation κ hκ n hn
  have hpos : 0 < |(oracleLowerLaw κ n false).theta-(oracleLowerLaw κ n true).theta| := by
    rw [abs_sub_comm]
    exact lt_of_lt_of_le (by positivity) hsep
  have h := two_prior_absolute_risk ν0 ν1 _ _ (1/4) hpos
    (oracle_lower_joint_tv κ n ⟨hκ,hn⟩)
    (fun z => t.1 (z.1,z.2,side (oracleLowerLaw κ n true)))
    (t.2.1.comp (by fun_prop))
  have hi0 := (oracle_side_risk_bounds κ n side t _ (hm true)).1
  have hi1 := (oracle_side_risk_bounds κ n side t _ (hm false)).1
  rw [← hs] at hi1
  rw [← ofReal_integral_eq_lintegral_ofReal hi0
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hi1
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _)), ← ENNReal.ofReal_max] at h
  have hr := (ENNReal.ofReal_le_ofReal_iff (le_trans
    (integral_nonneg (fun _ => abs_nonneg _)) (le_max_left _ _))).mp h
  rw [hs] at hr
  have hB : BddAbove (Set.range (fun law : {law // InModel κ law} =>
      decisionRisk n jointLaw side t law.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law,rfl⟩
    exact (oracle_side_risk_bounds κ n side t law.1 law.2).2
  have hmax : max (decisionRisk n jointLaw side t (oracleLowerLaw κ n true))
      (decisionRisk n jointLaw side t (oracleLowerLaw κ n false)) ≤
      ⨆ law : {law // InModel κ law}, decisionRisk n jointLaw side t law.1 :=
    max_le (le_ciSup hB ⟨_,hm true⟩) (le_ciSup hB ⟨_,hm false⟩)
  have hr' : (3/16 : ℝ)*|(oracleLowerLaw κ n true).theta-
      (oracleLowerLaw κ n false).theta| ≤
      max (decisionRisk n jointLaw side t (oracleLowerLaw κ n true))
        (decisionRisk n jointLaw side t (oracleLowerLaw κ n false)) := by
    convert hr using 1
    · rw [abs_sub_comm]; ring
    · simp only [decisionRisk, hs]
  exact (show (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤
    (3/16 : ℝ)*|(oracleLowerLaw κ n true).theta-(oracleLowerLaw κ n false).theta| by
      nlinarith [hsep]).trans (hr'.trans hmax)

/-- Infimizing the pairwise reduction proves the oracle power for any identical revelation. -/
-- @node: oracle_lower_minimax_risk
lemma oracle_lower_minimax_risk {S : Type*} [MeasurableSpace S] (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (side : ObservedLaw → S)
    (hs : side (oracleLowerLaw κ n true) = side (oracleLowerLaw κ n false)) :
    (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ minimaxRiskWith κ n jointLaw side := by
  haveI : Nonempty (SideEstimator n S) := ⟨⟨fun _ => 0, measurable_const,
    fun _ => ⟨by norm_num,by norm_num⟩⟩⟩
  exact le_ciInf (oracle_lower_worst_risk κ hκ n hn side hs)

/-- Fixing supplied information gives an original measurable interval procedure. -/
-- @node: oracle_fixed_side_interval
def oracle_fixed_side_interval {S : Type*} [MeasurableSpace S] (n : ℕ)
    (i : IntervalProc n S) (s : S) : OriginalIntervalProc n :=
  ⟨fun z => i.1 (z.1,z.2.1,s), i.2.comp (by fun_prop)⟩

/-- Coverage of the identical-revelation pair forces positive expected length. -/
-- @node: oracle_lower_worst_length
lemma oracle_lower_worst_length {S : Type*} [MeasurableSpace S] (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (side : ObservedLaw → S)
    (hs : side (oracleLowerLaw κ n true) = side (oracleLowerLaw κ n false))
    (i : IntervalProc n S)
    (hh : ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw side i law) :
    (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤
      ⨆ law : {law // InModel κ law}, expectedLength n jointLaw side i law.1 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let ν0 := jointLaw n (oracleLowerLaw κ n true).P
  let ν1 := jointLaw n (oracleLowerLaw κ n false).P
  letI : IsProbabilityMeasure ν0 := by dsimp [ν0]; unfold jointLaw; infer_instance
  letI : IsProbabilityMeasure ν1 := by dsimp [ν1]; unfold jointLaw; infer_instance
  let I := fun z : Experiment n => i.1 (z.1,z.2,side (oracleLowerLaw κ n true))
  let E0 := {z | (oracleLowerLaw κ n true).theta ∈ (I z).toSet}
  let E1 := {z | (oracleLowerLaw κ n false).theta ∈ (I z).toSet}
  have hI : Measurable I := i.2.comp (by fun_prop)
  have hE0 : MeasurableSet E0 := (lower_interval_membership_measurable _).preimage hI
  have hE1 : MeasurableSet E1 := (lower_interval_membership_measurable _).preimage hI
  have hm := oracle_lower_membership κ n hκ hn
  have hc0 : 9/10 ≤ ν0.real E0 := hh _ (hm true)
  have hc1 : 9/10 ≤ ν1.real E1 := by
    simpa only [coverage, ← hs] using hh _ (hm false)
  have htv := oracle_lower_joint_tv κ n ⟨hκ,hn⟩
  have htransfer := (Causalean.Stat.measureReal_sub_le_tvDist
    (μ := ν0) (ν := ν1) hE1).trans htv
  have hmass : (11/20 : ℝ) ≤ ν0.real (E0 ∩ E1) := by
    have h := measureReal_union_add_inter (μ := ν0) (s := E0) hE1
    have hu : ν0.real (E0 ∪ E1) ≤ 1 := measureReal_le_one
    linarith
  let Δ := |(oracleLowerLaw κ n false).theta-(oracleLowerLaw κ n true).theta|
  have hi : Integrable (fun z => (I z).length) ν0 :=
    lower_interval_length_integrable n
      (oracle_fixed_side_interval n i (side (oracleLowerLaw κ n true))) ν0
  have hthreshold := threshold_mass_le_lintegral ν0 (fun z => (I z).length) Δ
    (abs_nonneg _) (E0 ∩ E1) (hE0.inter hE1)
    (fun z hz => lower_interval_separation _ _ _ hz.1 hz.2)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun z => (lower_interval_length_properties.2 _).1))] at hthreshold
  have hr := (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg (fun z => (lower_interval_length_properties.2 _).1))).mp hthreshold
  have hsep := oracle_lower_separation κ hκ n hn
  have hΔ : 0 ≤ Δ := abs_nonneg _
  have hgap : (1/16 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ Δ := by
    dsimp [Δ]; rw [abs_sub_comm]; exact hsep
  have hlen : (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤
      expectedLength n jointLaw side i (oracleLowerLaw κ n true) := by
    have hmul := mul_le_mul_of_nonneg_left hmass hΔ
    change _ ≤ ∫ z, (I z).length ∂ν0
    nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ n by positivity) (-rOracle κ)]
  have hB : BddAbove (Set.range (fun law : {law // InModel κ law} =>
      expectedLength n jointLaw side i law.1)) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨law,rfl⟩
    letI : IsProbabilityMeasure (jointLaw n law.1.P) := by unfold jointLaw; infer_instance
    simpa [expectedLength, oracle_fixed_side_interval] using integral_mono
      (lower_interval_length_integrable n (oracle_fixed_side_interval n i (side law.1)) (jointLaw n law.1.P))
      (integrable_const (1 : ℝ)) (fun z => (lower_interval_length_properties.2 _).2)
  exact hlen.trans (le_ciSup hB ⟨_,hm true⟩)

/-- The full target interval is honest with any supplied information. -/
-- @node: oracle_side_honest_nonempty
lemma oracle_side_honest_nonempty {S : Type*} [MeasurableSpace S] (n : ℕ)
    (side : ObservedLaw → S) :
    Nonempty {i : IntervalProc n S //
      ∀ law, InModel κ law → 9/10 ≤ coverage n jointLaw side i law} := by
  let c : IntervalCode := .inr ⟨(-1/2,1/2,true,true),by norm_num⟩
  refine ⟨⟨⟨fun _ => c,measurable_const⟩,?_⟩⟩
  intro law hm
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  letI : IsProbabilityMeasure (jointLaw n law.P) := by unfold jointLaw; infer_instance
  have hθ : law.theta ∈ c.toSet := by
    have ht := hm.effectRange xstar
    change |law.theta| ≤ 1/2 at ht
    have ha := abs_le.mp ht
    change -1/2 ≤ law.theta ∧ law.theta ≤ 1/2
    constructor <;> linarith [ha.1,ha.2]
  simp [coverage,hθ]
  norm_num

/-- Infimizing over honest decisions retains the oracle pair's expected-length lower bound. -/
-- @node: oracle_lower_honest_length
lemma oracle_lower_honest_length {S : Type*} [MeasurableSpace S] (hκ : κ.Valid)
    (n : ℕ) (hn : 2 ≤ n) (side : ObservedLaw → S)
    (hs : side (oracleLowerLaw κ n true) = side (oracleLowerLaw κ n false)) :
    (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ honestLengthWith κ n jointLaw side := by
  haveI := oracle_side_honest_nonempty κ n side
  exact le_ciInf (fun i => oracle_lower_worst_length κ hκ n hn side hs i.1 i.2)

/-- Both revealed experiments have the oracle lower power for risk and honest length. -/
-- @node: oracle_values_lower
lemma oracle_values_lower (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n)
    (expLaw : ExperimentFamily) (j : Fin 4) :
    (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ oracleValues κ n expLaw j := by
  have hs := oracle_lower_revelations κ hκ n hn
  unfold oracleValues
  split
  · exact oracle_lower_minimax_risk κ hκ n hn sideE hs.2
  · split
    · exact oracle_lower_honest_length κ hκ n hn sideE hs.2
    · split
      · exact oracle_lower_minimax_risk κ hκ n hn sideEM hs.1
      · exact oracle_lower_honest_length κ hκ n hn sideEM hs.1

/-- The localized truncated score has oracle risk and its public Markov radius is honest. -/
-- @node: oracle_score_risk_coverage
lemma oracle_score_risk_coverage (hκ : κ.Valid) (n : ℕ) (hn : 2 ≤ n) :
    ∀ law, InModel κ law →
      decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤
        oracleConstant κ*(n : ℝ)^(-rOracle κ) ∧
      9/10 ≤ coverage n jointLaw sideE (oracleIntervalDecision κ n) law := by
  intro law hm
  have hrisk : decisionRisk n jointLaw sideE (oracleDecision κ n) law ≤
      oracleConstant κ*(n : ℝ)^(-rOracle κ) := by
    apply oracle_tuned_risk_bound κ hκ n hn
    have ht := oracle_tuning_identities κ hκ n hn
    have hsample := oracle_decision_sample_risk κ n law hm
    dsimp only at hsample
    let f : O → ℝ := fun o => if X o ∈ window (oracleH κ n) then
      trunc (oracleT κ n) (suppliedScore (sideE law) o) else 0
    let c : ℝ := ((n : ℝ)*oracleH κ n)⁻¹
    have hrecord :
        |c * (n : ℝ) * (∫ o, f o ∂law.P) - law.theta| ≤
          20*oracleH κ n^κ.γ + oracleMoment κ*oracleT κ n^(1-κ.p) ∧
        c^2 * (n : ℝ) * (∫ o, (f o)^2 ∂law.P) ≤
          oracleMoment κ*(oracleT κ n^(2-κ.p)/((n : ℝ)*oracleH κ n)) := by
      have hlocal := oracle_record_local_bounds κ hκ law hm
        (oracleH κ n) (oracleT κ n) ht.1 (lt_of_lt_of_le (by norm_num) ht.2.2.1)
      dsimp only at hlocal
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
      have hh0 : oracleH κ n ≠ 0 := ht.1.1.ne'
      have hc : c * (n : ℝ) = (oracleH κ n)⁻¹ := by
        dsimp only [c]
        field_simp
      constructor
      · rw [hc]
        exact hlocal.1
      · have heq : c^2 * (n : ℝ) * (∫ o, (f o)^2 ∂law.P) =
            ((oracleH κ n)⁻¹ * (∫ o, (f o)^2 ∂law.P)) /
              ((n : ℝ)*oracleH κ n) := by
          dsimp only [c]
          field_simp
          <;> ring
        rw [heq]
        exact (div_le_div_of_nonneg_right hlocal.2
          (mul_nonneg (by positivity) ht.1.1.le)).trans_eq (by ring)
    exact hsample.trans (add_le_add hrecord.1 (Real.sqrt_le_sqrt hrecord.2))
  exact ⟨hrisk, oracleInterval_coverage_of_risk κ n hn law hm hrisk⟩

/-- Concrete constructions and numerical certificates used as existential proof witnesses. -/
lemma oracle_experiment_concrete (hκ : κ.Valid) (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  (0 < (3/256 : ℝ) ∧ (3/256 : ℝ) ≤ oracleUpper κ ∧ oracleUpper κ ≤ 4000) ∧
  (∀ n : ℕ, 2 ≤ n → -- @realizes n(sample size at least two)
    ∀ j : Fin 4, (3/256 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ oracleValues κ n expLaw j ∧
    oracleValues κ n expLaw j ≤ oracleUpper κ*(n : ℝ)^(-rOracle κ)) ∧
  (∀ law, InModel κ law →
    (∀ᵐ x ∂design, law.e x*(∫ y, scoreZ law.e (x,true,y) ∂law.Q true x) +
      (1-law.e x)*(∫ y, scoreZ law.e (x,false,y) ∂law.Q false x) = law.tau x) ∧
    (∀ᵐ x ∂design,
      ENNReal.ofReal (law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,true,y)|^κ.p) ∂law.Q true x) +
      ENNReal.ofReal (1-law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,false,y)|^κ.p) ∂law.Q false x) ≤
        ENNReal.ofReal (oracleMoment κ))) ∧
  (∀ n : ℕ, 2 ≤ n →
    (∀ law, InModel κ law → decisionRisk n expLaw sideE (oracleDecision κ n) law ≤ oracleConstant κ*(n : ℝ)^(-rOracle κ) ∧
      9/10 ≤ coverage n expLaw sideE (oracleIntervalDecision κ n) law) ∧
    (∀ z, (oracleInterval κ n z).length ≤ min 1 (20*oracleConstant κ*(n : ℝ)^(-rOracle κ))) ∧
    (∀ ε, InModel κ (oracleLowerLaw κ n ε)) ∧
    sideEM (oracleLowerLaw κ n true) = sideEM (oracleLowerLaw κ n false) ∧
    sideE (oracleLowerLaw κ n true) = sideE (oracleLowerLaw κ n false) ∧
    (1/16 : ℝ)*(n : ℝ)^(-rOracle κ) ≤ |(oracleLowerLaw κ n true).theta-(oracleLowerLaw κ n false).theta| ∧
    Causalean.Stat.tvDist (jointLaw n (oracleLowerLaw κ n true).P) (jointLaw n (oracleLowerLaw κ n false).P) ≤ 1/4) ∧
  (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid} →
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧ ∀ κ' ∈ K, c0 ≤ (3/256 : ℝ) ∧ oracleUpper κ' ≤ C0) := by
  refine ⟨oracle_constant_bounds κ hκ, ?_, ?_, ?_, oracle_compact_constants⟩
  · intro n hn j
    refine ⟨oracle_values_lower κ hκ n hn expLaw j, ?_⟩
    exact oracle_values_upper_of_procedures κ n expLaw
      (fun law hm => (oracle_score_risk_coverage κ hκ n hn law hm).1)
      (fun law hm => (oracle_score_risk_coverage κ hκ n hn law hm).2)
      (oracle_interval_length κ hκ n hn) j
  · intro law hm
    exact ⟨oracle_score_mean κ law hm, oracle_score_moment κ hκ law hm⟩
  · intro n hn
    have hreveal := oracle_lower_revelations κ hκ n hn
    refine ⟨?_, oracle_interval_length κ hκ n hn,
      oracle_lower_membership κ n hκ hn, hreveal.1, hreveal.2,
      oracle_lower_separation κ hκ n hn, ?_⟩
    · intro law hm
      have heq : expLaw n law.P = jointLaw n law.P := hiid n hn law.P law.probability
      simpa only [decisionRisk, coverage, heq] using
        oracle_score_risk_coverage κ hκ n hn law hm
    · exact oracle_lower_joint_tv κ n ⟨hκ, hn⟩

-- @node: thm:oracle-experiment
/-- Revelation has the oracle power with existential constants and total public-radius
procedures. The lower alternatives share both nuisances, and one constant family is uniform
on compact subsets of the public domain. Concrete numerical certificates remain auxiliary. -/
theorem oracle_experiment (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  ∃ c C : Params → ℝ,
  (∀ κ, κ.Valid → 0 < c κ ∧ c κ ≤ C κ ∧
    ∀ n : ℕ, 2 ≤ n → -- @realizes n(sample size at least two)
      (∀ j : Fin 4, c κ*(n : ℝ)^(-rOracle κ) ≤ oracleValues κ n expLaw j ∧
        oracleValues κ n expLaw j ≤ C κ*(n : ℝ)^(-rOracle κ)) ∧
      (∃ radius : ℝ, 0 ≤ radius ∧ 2*radius ≤ C κ*(n : ℝ)^(-rOracle κ) ∧
        ∃ tE : SideEstimator n Nuisance, ∃ tEM : SideEstimator n (Nuisance × Nuisance),
        ∃ iE : IntervalProc n Nuisance, ∃ iEM : IntervalProc n (Nuisance × Nuisance),
          (∀ law, InModel κ law →
            decisionRisk n jointLaw sideE tE law ≤ C κ*(n : ℝ)^(-rOracle κ) ∧
            decisionRisk n jointLaw sideEM tEM law ≤ C κ*(n : ℝ)^(-rOracle κ) ∧
            9/10 ≤ coverage n jointLaw sideE iE law ∧
            9/10 ≤ coverage n jointLaw sideEM iEM law) ∧
          (∀ z, iE.1 z = closedInterval (max (-1/2) (tE.1 z-radius))
            (min (1/2) (tE.1 z+radius))) ∧
          (∀ z, iEM.1 z = closedInterval (max (-1/2) (tEM.1 z-radius))
            (min (1/2) (tEM.1 z+radius))) ∧
          (∀ z, (iE.1 z).length ≤ min 1 (2*radius)) ∧
          (∀ z, (iEM.1 z).length ≤ min 1 (2*radius))) ∧
      (∃ law0 law1 : ObservedLaw, InModel κ law0 ∧ InModel κ law1 ∧
        sideEM law0 = sideEM law1 ∧ sideE law0 = sideE law1 ∧
        c κ*(n : ℝ)^(-rOracle κ) ≤ |law1.theta-law0.theta| ∧
        Causalean.Stat.tvDist (jointLaw n law0.P) (jointLaw n law1.P) ≤ 1/4)) ∧
  (∀ K : Set Params, IsCompact K → K ⊆ {κ | κ.Valid} →
    ∃ c0 C0 : ℝ, 0 < c0 ∧ c0 ≤ C0 ∧ ∀ κ ∈ K, c0 ≤ c κ ∧ C κ ≤ C0) ∧
  (∀ κ, κ.Valid → ∀ law, InModel κ law →
    (∀ᵐ x ∂design, law.e x*(∫ y, scoreZ law.e (x,true,y) ∂law.Q true x) +
      (1-law.e x)*(∫ y, scoreZ law.e (x,false,y) ∂law.Q false x) = law.tau x) ∧
    (∀ᵐ x ∂design,
      ENNReal.ofReal (law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,true,y)|^κ.p) ∂law.Q true x) +
      ENNReal.ofReal (1-law.e x)*(∫⁻ y, ENNReal.ofReal (|scoreZ law.e (x,false,y)|^κ.p) ∂law.Q false x) ≤
        ENNReal.ofReal (oracleMoment κ))) := by
  have hjoint : IIDSampling jointLaw := by
    intro n hn P hP
    rfl
  refine ⟨fun _ => 3/256, oracleUpper, ?_, ?_, ?_⟩
  · intro κ hκ
    have hc := oracle_experiment_concrete κ hκ expLaw hiid
    refine ⟨hc.1.1, hc.1.2.1, ?_⟩
    intro n hn
    have hw := (oracle_experiment_concrete κ hκ jointLaw hjoint).2.2.2.1 n hn
    have hpos : 0 < oracleConstant κ := by
      have := hc.1.2.1
      unfold oracleUpper at this
      linarith
    have hpow : 0 ≤ (n : ℝ)^(-rOracle κ) := Real.rpow_nonneg (by positivity) _
    have hr : 0 ≤ 10*oracleConstant κ*(n : ℝ)^(-rOracle κ) := by positivity
    have hmax : max 0 (10*oracleConstant κ*(n : ℝ)^(-rOracle κ)) =
        10*oracleConstant κ*(n : ℝ)^(-rOracle κ) := max_eq_right hr
    let tEM : SideEstimator n (Nuisance × Nuisance) :=
      ⟨fun z => (oracleDecision κ n).1 (z.1, z.2.1, z.2.2.1), by
        constructor
        · exact (oracleDecision κ n).2.1.comp
            (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
              (measurable_fst.comp (measurable_snd.comp measurable_snd))))
        · intro z
          exact (oracleDecision κ n).2.2 _⟩
    let iEM : IntervalProc n (Nuisance × Nuisance) :=
      ⟨fun z => (oracleIntervalDecision κ n).1 (z.1, z.2.1, z.2.2.1),
        (oracleIntervalDecision κ n).2.comp
          (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
            (measurable_fst.comp (measurable_snd.comp measurable_snd))))⟩
    refine ⟨hc.2.1 n hn, ?_, ?_⟩
    · refine ⟨10*oracleConstant κ*(n : ℝ)^(-rOracle κ), hr, ?_,
        oracleDecision κ n, tEM, oracleIntervalDecision κ n, iEM, ?_, ?_, ?_, ?_, ?_⟩
      · unfold oracleUpper
        ring_nf
        exact le_rfl
      · intro law hlaw
        have hb := hw.1 law hlaw
        have hbC : oracleConstant κ*(n : ℝ)^(-rOracle κ) ≤
            oracleUpper κ*(n : ℝ)^(-rOracle κ) := by
          unfold oracleUpper
          nlinarith [mul_nonneg hpos.le hpow]
        exact ⟨hb.1.trans hbC, hb.1.trans hbC, hb.2, hb.2⟩
      · intro z
        change oracleInterval κ n z = _
        simp only [oracleInterval, oracleDecision, oracleEstimator, hmax]
      · intro z
        change oracleInterval κ n (z.1, z.2.1, z.2.2.1) = _
        simp only [oracleInterval, tEM, oracleDecision, oracleEstimator, hmax]
      · intro z
        change (oracleInterval κ n z).length ≤ _
        rw [show 2*(10*oracleConstant κ*(n : ℝ)^(-rOracle κ)) =
          20*oracleConstant κ*(n : ℝ)^(-rOracle κ) by ring]
        exact hw.2.1 z
      · intro z
        change (oracleInterval κ n (z.1, z.2.1, z.2.2.1)).length ≤ _
        rw [show 2*(10*oracleConstant κ*(n : ℝ)^(-rOracle κ)) =
          20*oracleConstant κ*(n : ℝ)^(-rOracle κ) by ring]
        exact hw.2.1 (z.1, z.2.1, z.2.2.1)
    · refine ⟨oracleLowerLaw κ n true, oracleLowerLaw κ n false,
        hw.2.2.1 true, hw.2.2.1 false, hw.2.2.2.1, hw.2.2.2.2.1, ?_, ?_⟩
      · rw [abs_sub_comm]
        exact (mul_le_mul_of_nonneg_right (by norm_num : (3/256 : ℝ) ≤ 1/16) hpow).trans
          hw.2.2.2.2.2.1
      · exact hw.2.2.2.2.2.2
  · intro K hK hsub
    by_cases hne : K.Nonempty
    · obtain ⟨κ, hκK⟩ := hne
      exact (oracle_experiment_concrete κ (hsub hκK) expLaw hiid).2.2.2.2 K hK hsub
    · refine ⟨1, 1, by norm_num, le_rfl, ?_⟩
      intro κ hκ
      exact (hne ⟨κ, hκ⟩).elim
  · intro κ hκ law hlaw
    exact (oracle_experiment_concrete κ hκ expLaw hiid).2.2.1 law hlaw

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
