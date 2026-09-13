import CausalSmith.Stat.STAT_PomdpLatentOverlapMinimax_Research.Helpers.InsulinGridCore.Interval

set_option linter.style.longLine false

namespace CausalSmith.Stat.PomdpLatentOverlapMinimax

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

open Causalean.Mathlib.Analysis.CertifiedContourIntervalArithmetic
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation
open Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.CertifiedNormalCDFEnclosure

/-- For [the r input](hyp:r), [this defines the insulin Reward Rat object](goal). -/
def insulinRewardRat (r : Fin 4) : ℚ :=
  match r.val with
  | 0 => -1
  | 1 => -(2 / 3)
  | 2 => -(1 / 3)
  | _ => 0

/-- [the insulin Reward Rat cast assertion holds](goal). -/
lemma insulinRewardRat_cast (r : Fin 4) :
    (insulinRewardRat r : ℝ) = insulinRewardValue r := by
  fin_cases r <;> norm_num [insulinRewardRat, insulinRewardValue]

/-- For [the x input](hyp:x), [this defines the insulin Reward Symbol Rat object](goal). -/
def insulinRewardSymbolRat (x : Fin 90) : Fin 4 :=
  if insulinGlucoseRat x ≤ 70 then 0
  else if 150 < insulinGlucoseRat x then 1
  else if insulinGlucoseRat x ≤ 80 ∨
      (120 < insulinGlucoseRat x ∧ insulinGlucoseRat x ≤ 150) then 2 else 3

/-- [the insulin Reward Symbol Rat eq assertion holds](goal). -/
lemma insulinRewardSymbolRat_eq (x : Fin 90) :
    insulinRewardSymbolRat x = insulinRewardSymbol x := by
  fin_cases x <;> norm_num [insulinRewardSymbolRat, insulinRewardSymbol, insulinGlucoseRat, glucoseGridValue]

/-- For [the s input](hyp:s), [this defines the insulin State Reward object](goal). -/
noncomputable def insulinStateReward (s : JointState 90 4) : ℝ :=
  insulinRewardValue (insulinRewardSymbol s.1)

/-- [this defines the insulin Reward Certificate object](goal). [defining clause 1](step:1); and [defining clause 2](step:2); and [defining clause 3](step:3); and [defining clause 4](step:4); and [defining clause 5](step:5). -/
noncomputable def insulinRewardCertificate :
    BoundedRewardCertificate insulinStateReward where
  intervals := fun s => RatInterval.point (insulinRewardRat (insulinRewardSymbolRat s.1))
  contains := by
    intro s
    change (RatInterval.point (insulinRewardRat (insulinRewardSymbolRat s.1))).Contains
      (insulinRewardValue (insulinRewardSymbol s.1))
    rw [insulinRewardSymbolRat_eq, RatInterval.contains_point_iff]
    exact (insulinRewardRat_cast _).symm
  bound := 1
  bound_nonneg := by norm_num
  endpoints_bounded := by
    intro s
    generalize insulinRewardSymbolRat s.1 = r
    fin_cases r <;> norm_num [insulinRewardRat, RatInterval.point, RatInterval.maxAbs]

/-- [the insulin Finite Stationary assertion holds](goal). -/
lemma insulinFiniteStationary (target : Bool) :
    Causalean.Mathlib.Probability.CertifiedFiniteMarkovExpectation.IsStationary
      (finitePolicyKernel (insulinGridFinite T)
        (if target then (insulinGridFinite T).e else (insulinGridFinite T).b))
      (stationaryLaw (finitePolicyKernel (insulinGridFinite T)
        (if target then (insulinGridFinite T).e else (insulinGridFinite T).b))) := by
  let p := if target then (insulinGridFinite T).e else (insulinGridFinite T).b
  have hp : PolicyVector (fun x a => (p x a).toReal) := by
    cases target
    · exact (embed_sequentialIgnorability (insulinGridFinite T)).1
    · exact (insulinGrid_policyOverlap T).1
  have hc := insulinGrid_contraction T (fun x a => (p x a).toReal) (by
    cases target <;> simp [p, insulinGrid, embed])
  have h := insulinStationaryLaw_isStationary T _ hp hc
  change IsStationary
    (policyKernel (embed (insulinGridFinite T)) (fun x a => (p x a).toReal))
    (stationaryLaw
      (policyKernel (embed (insulinGridFinite T)) (fun x a => (p x a).toReal))) at h
  rw [embed_policyKernel_eq] at h
  dsimp only [p] at h
  constructor
  · exact h.1
  · funext s'
    exact h.2 s'

/-- [the insulin Kernel reward Mean assertion holds](goal). -/
lemma insulinKernel_rewardMean (s : JointState 90 4) (a : Bool) :
    ∑ p : Fin 4 × JointState 90 4,
        ((insulinGridFinite T).kernel s a p).toReal * insulinRewardValue p.1 =
      insulinStateReward s := by
  change ∑ p : Fin 4 × JointState 90 4,
      (pmfOfRealWeight (fun q : Fin 4 × JointState 90 4 ↦
        (if q.1 = insulinRewardSymbol s.1 then 1 else 0) *
          insulinStateWeight s a q.2) p).toReal * insulinRewardValue p.1 = _
  simp_rw [pmfOfRealWeight_apply_of_nonneg_sum_one _
    (insulinKernelWeight_nonneg s a) (sum_insulinKernelWeight s a)]
  simp_rw [ENNReal.toReal_ofReal (insulinKernelWeight_nonneg s a _)]
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  simp
  rw [← Finset.sum_mul, sum_insulinStateWeight, one_mul]
  rfl

/-- [the insulin Embedded Kernel reward Mean assertion holds](goal). -/
lemma insulinEmbeddedKernel_rewardMean (s : JointState 90 4) (a : Bool) :
    ∫ p, p.1 ∂((insulinGrid T).K s a) = insulinStateReward s := by
  change ∫ q, q.1 ∂(((insulinGridFinite T).kernel s a).map
    (fun p ↦ (insulinRewardValue p.1, p.2))).toMeasure = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_finite _)]
  rw [MeasureTheory.integral_map (measurable_of_finite _).aemeasurable
    measurable_fst.aestronglyMeasurable, PMF.integral_eq_sum]
  simpa only [smul_eq_mul] using insulinKernel_rewardMean (T := T) s a

/-- [the insulin Target Reward Regression assertion holds](goal). -/
lemma insulinTargetRewardRegression (s : JointState 90 4) :
    rewardRegression (insulinGrid T) s = insulinStateReward s := by
  unfold rewardRegression
  simp_rw [insulinEmbeddedKernel_rewardMean]
  rw [← Finset.sum_mul, ((insulinGrid_policyOverlap T).1 s.1).2, one_mul]

/-- [the insulin Behaviour Ratio Cancel assertion holds](goal). -/
lemma insulinBehaviourRatioCancel (x : Fin 90) (a : Bool) :
    (insulinGrid T).b x a * ratio (insulinGrid T).b (insulinGrid T).e x a =
      (insulinGrid T).e x a := by
  have hb : (insulinGrid T).b x a ≠ 0 := by
    change ((insulinGridFinite T).b x a).toReal ≠ 0
    rw [insulinBehaviourPMF_apply]
    cases a <;> norm_num [insulinPolicyRat]
  rw [ratio, if_neg hb]
  field_simp

/-- [the insulin Immediate Reward Regression assertion holds](goal). -/
lemma insulinImmediateRewardRegression (s : JointState 90 4) :
    ∑ a : Bool, (insulinGrid T).b s.1 a *
        ratio (insulinGrid T).b (insulinGrid T).e s.1 a *
          ∫ p, p.1 ∂((insulinGrid T).K s a) = insulinStateReward s := by
  simp_rw [insulinEmbeddedKernel_rewardMean (T := T), insulinBehaviourRatioCancel (T := T)]
  rw [← Finset.sum_mul, ((insulinGrid_policyOverlap T).1 s.1).2, one_mul]

/-- [the insulin Immediate Weight Bias eq assertion holds](goal). -/
lemma insulinImmediateWeightBias_eq :
    immediateWeightBias T =
      rewardExpectation
          (stationaryLaw (finitePolicyKernel (insulinGridFinite T)
            (insulinGridFinite T).b)) insulinStateReward -
        rewardExpectation
          (stationaryLaw (finitePolicyKernel (insulinGridFinite T)
            (insulinGridFinite T).e)) insulinStateReward := by
  unfold immediateWeightBias targetValue rewardExpectation
  simp_rw [insulinImmediateRewardRegression, insulinTargetRewardRegression]
  rw [show policyKernel (insulinGrid T) (insulinGrid T).b =
      finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).b by
    exact embed_policyKernel_eq _ _]
  rw [show policyKernel (insulinGrid T) (insulinGrid T).e =
      finitePolicyKernel (insulinGridFinite T) (insulinGridFinite T).e by
    exact embed_policyKernel_eq _ _]

/-- [this defines the insulin Reward Intervals object](goal). -/
def insulinRewardIntervals : IntervalVector (JointState 90 4) :=
  fun s => RatInterval.point (insulinRewardRat (insulinRewardSymbolRat s.1))

/-- [the insulin Rho nonneg assertion holds](goal). -/
lemma insulinRho_nonneg : (0 : ℚ) ≤ 1 / 2 := by norm_num

/-- [the insulin Rho lt one assertion holds](goal). -/
lemma insulinRho_lt_one : (1 / 2 : ℚ) < 1 := by norm_num

end CausalSmith.Stat.PomdpLatentOverlapMinimax
