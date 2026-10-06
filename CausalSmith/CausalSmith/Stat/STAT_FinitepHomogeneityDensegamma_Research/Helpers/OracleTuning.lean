module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleCalibration
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TwoPrior

/-! Exact dyadic bias and variance balance for the supplied-propensity rule. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The oracle exponent balances approximation, tail clipping, and quadratic variance exactly. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracle_exponent_balance
lemma oracle_exponent_balance (v : Params) (hv : v.Valid) :
    E0 v*(2+tExp v+1/(2*v.γ)) = 1 := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  unfold E0 tExp
  field_simp [he.ne', hm.ne', hg.ne']
  unfold qExp
  field_simp
  <;> ring

/-- The half-sample oracle scale is positive and at most one. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracleA_bounds
lemma oracleA_bounds (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    0 < oracleA n v ∧ oracleA n v ≤ 1 := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    exact_mod_cast (show 1 ≤ blockSize n by unfold blockSize; omega)
  constructor
  · unfold oracleA; positivity
  · exact Real.rpow_le_one_of_one_le_of_nonpos hs (neg_nonpos.mpr (E0_pos v hv).le)

/-- Both dyadic targets are at least one, so upward rounding costs at most two. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracle_rounding_bounds
lemma oracle_rounding_bounds (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    oracleA n v^(-1/(v.p-1)) ≤ oracleT n v ∧
    oracleT n v ≤ 2*oracleA n v^(-1/(v.p-1)) ∧
    oracleA n v^(-1/v.γ) ≤ (oracleJ n v:ℝ) ∧
    (oracleJ n v:ℝ) ≤ 2*oracleA n v^(-1/v.γ) := by
  obtain ⟨ha, ha1⟩ := oracleA_bounds n v hn hv
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  have hT : 1 ≤ oracleA n v^(-1/(v.p-1)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (div_nonpos_of_nonpos_of_nonneg (by norm_num) hm.le)
  have hJ : 1 ≤ oracleA n v^(-1/v.γ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ha ha1 (div_nonpos_of_nonpos_of_nonneg (by norm_num) hg.le)
  unfold oracleT oracleJ
  rw [leastPow2Ge_eq_dyadUp hJ]
  exact ⟨le_dyadUp (by positivity), (ledger_dyadUp_bounds hT).2,
    le_dyadUp (by positivity), (ledger_dyadUp_bounds hJ).2⟩

/-- Upward clipping and histogram rounding each keep their bias within the target scale. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracle_bias_rate_bounds
lemma oracle_bias_rate_bounds (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    oracleBias n v ≤ 20*oracleA n v ∧
    (oracleJ n v:ℝ)^(-v.γ) ≤ oracleA n v := by
  obtain ⟨ha, ha1⟩ := oracleA_bounds n v hn hv
  obtain ⟨hT, hThi, hJ, hJhi⟩ := oracle_rounding_bounds n v hn hv
  have hm : 0 < v.p-1 := by linarith [hv.1.1]
  have hg : 0 < v.γ := by linarith [hv.2.2.2.1]
  constructor
  · unfold oracleBias
    have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < oracleA n v^(-1/(v.p-1)))
      hT (by linarith : 1-v.p ≤ 0)
    rw [← Real.rpow_mul ha.le, show (-1/(v.p-1))*(1-v.p)=1 by field_simp; ring,
      Real.rpow_one] at hh
    linarith
  · have hh := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < oracleA n v^(-1/v.γ))
      hJ (by linarith : -v.γ ≤ 0)
    rw [← Real.rpow_mul ha.le, show (-1/v.γ)*(-v.γ)=1 by field_simp,
      Real.rpow_one] at hh
    exact hh

/-- The dyadic covariance budget has exactly the squared oracle signal order. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracle_covariance_rate_bound
lemma oracle_covariance_rate_bound (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    Real.sqrt (oracleJ n v)*oracleCov n v ≤ 160*Real.sqrt 2*oracleA n v^2 := by
  obtain ⟨ha, ha1⟩ := oracleA_bounds n v hn hv
  obtain ⟨hT, hThi, hJ, hJhi⟩ := oracle_rounding_bounds n v hn hv
  have hs : (0:ℝ) < blockSize n := by
    exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
  have hpow : oracleT n v^(2-v.p) ≤ 2*oracleA n v^(-tExp v) := by
    have hh := Real.rpow_le_rpow (by linarith [oracleT_one_le n v hn hv]) hThi
      (by linarith [hv.1.2] : 0 ≤ 2-v.p)
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul ha.le] at hh
    have hid : (-1/(v.p-1))*(2-v.p) = -tExp v := by unfold tExp; ring
    rw [hid] at hh
    have htwo : (2:ℝ)^(2-v.p) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by linarith [hv.1.1] : 2-v.p ≤ 1)
    exact hh.trans (mul_le_mul_of_nonneg_right htwo (by positivity))
  have hroot : Real.sqrt (oracleJ n v) ≤ Real.sqrt 2*oracleA n v^(-1/(2*v.γ)) := by
    have hh := Real.sqrt_le_sqrt hJhi
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (oracleA n v^(-1/v.γ)), ← Real.rpow_mul ha.le] at hh
    have hid : (-1/v.γ)*(1/2) = -1/(2*v.γ) := by ring
    rwa [hid] at hh
  have hbal : oracleA n v^(-1/(2*v.γ))*oracleA n v^(-tExp v)/(blockSize n:ℝ) =
      oracleA n v^2 := by
    rw [← Real.rpow_add ha]
    unfold oracleA
    rw [← Real.rpow_two, ← Real.rpow_mul hs.le, ← Real.rpow_mul hs.le]
    apply (div_eq_iff hs.ne').mpr
    calc
      _ = (blockSize n:ℝ)^(-E0 v*2+1) := by
        congr 1
        linear_combination oracle_exponent_balance v hv
      _ = _ := by rw [Real.rpow_add hs, Real.rpow_one]
  have hTpos : 0 < oracleT n v := lt_of_lt_of_le zero_lt_one (oracleT_one_le n v hn hv)
  unfold oracleCov
  calc
    _ ≤ (Real.sqrt 2*oracleA n v^(-1/(2*v.γ)))*
        (80*(2*oracleA n v^(-tExp v))/(blockSize n:ℝ)) := by
      apply mul_le_mul hroot (div_le_div_of_nonneg_right (by linarith) hs.le)
        (by positivity) (by positivity)
    _ = 160*Real.sqrt 2*oracleA n v^2 := by rw [← hbal]; ring

/-- The oracle exponent never exceeds one on the full public domain. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: E0_le_one
lemma E0_le_one (v : Params) (hv : v.Valid) : E0 v ≤ 1 := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  unfold E0
  apply (div_le_iff₀ he).mpr
  nlinarith

/-- Passing from the half-sample oracle scale to the full sample costs at most three. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracleA_le_three_rhoOracle
lemma oracleA_le_three_rhoOracle (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    oracleA n v ≤ 3*rhoOracle n v := by
  have hs : (0:ℝ) < blockSize n := by
    exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
  have hn3 : (n:ℝ) ≤ 3*(blockSize n:ℝ) := by
    exact_mod_cast (show n ≤ 3*blockSize n by unfold blockSize; omega)
  have hr := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (n:ℝ)) hn3
    (neg_nonpos.mpr (E0_pos v hv).le)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hs.le] at hr
  have h3 : (3:ℝ)^E0 v ≤ 3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 3) (E0_le_one v hv)
  have hid : (3:ℝ)^E0 v*(3:ℝ)^(-E0 v) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  unfold oracleA rhoOracle
  calc
    _ = (3:ℝ)^E0 v*((3:ℝ)^(-E0 v)*(blockSize n:ℝ)^(-E0 v)) := by
      rw [← mul_assoc, hid, one_mul]
    _ ≤ (3:ℝ)^E0 v*(n:ℝ)^(-E0 v) := mul_le_mul_of_nonneg_left hr (by positivity)
    _ ≤ 3*(n:ℝ)^(-E0 v) := mul_le_mul_of_nonneg_right h3 (by positivity)

/-- The roadmap's sufficient signal margin is bounded by the public oracle separation. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracle_attaining_separation_le
lemma oracle_attaining_separation_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    20*(oracleJ n v:ℝ)^(-v.γ)+5*oracleBias n v+
      128*Real.sqrt (Real.sqrt (oracleJ n v)*oracleCov n v) ≤ COr*rhoOracle n v := by
  obtain ⟨ha, ha1⟩ := oracleA_bounds n v hn hv
  obtain ⟨hb, hJ⟩ := oracle_bias_rate_bounds n v hn hv
  have hroot := Real.sqrt_le_sqrt (oracle_covariance_rate_bound n v hn hv)
  rw [Real.sqrt_mul (by positivity : 0 ≤ 160*Real.sqrt 2), Real.sqrt_sq ha.le] at hroot
  have hscale := oracleA_le_three_rhoOracle n v hn hv
  have hbudget : 20*(oracleJ n v:ℝ)^(-v.γ)+5*oracleBias n v+
      128*Real.sqrt (Real.sqrt (oracleJ n v)*oracleCov n v) ≤
      (120+128*Real.sqrt (160*Real.sqrt 2))*oracleA n v := by linarith
  apply hbudget.trans
  unfold COr
  nlinarith [mul_le_mul_of_nonneg_left hscale
    (show 0 ≤ 120+128*Real.sqrt (160*Real.sqrt 2) by positivity)]

/-- A calibrated oracle rule bounds the capped radius, including the saturation branch. This statement assumes [the hD condition](hyp:hD), [the hr condition](hyp:hr), [the hlevel condition](hyp:hlevel), [the hpower condition](hyp:hpower). [This is the stated conclusion](goal). -/
-- @node: oracleCriticalRadius_le_of_test
lemma oracleCriticalRadius_le_of_test (n : ℕ) (v : Params) (r : ℝ)
    (hD : 0 ≤ maxDist v) (hr : 0 < r) (φ : OracleTest n)
    (hlevel : ∀ law, InNull v law → oracleRejectProb n law φ ≤ 1/10)
    (hpower : r < maxDist v → ∀ law, InModel v law → r ≤ hetDist law →
      1-oracleRejectProb n law φ ≤ 1/10) : oracleCriticalRadius n v ≤ r := by
  have hb : BddBelow ({t | 0 < t ∧ t < maxDist v ∧ oracleTestingRisk n v t ≤ 1/10} ∪
      {maxDist v}) := by
    refine ⟨0, ?_⟩
    intro t ht
    rcases ht with ht | ht
    · exact ht.1.le
    · simpa only [Set.mem_singleton_iff.mp ht] using hD
  by_cases hrd : r < maxDist v
  · have hrisk : oracleTestingRisk n v r ≤ 1/10 := by
      unfold oracleTestingRisk
      refine ciInf_le_of_le ?_ ⟨φ, hlevel⟩ ?_
      · refine ⟨0, ?_⟩
        rintro _ ⟨ψ, rfl⟩
        by_cases hA : Nonempty {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law}
        · obtain ⟨P⟩ := hA
          exact oracleWorstError_nonneg n v r ψ.1 ⟨P.1, P.2⟩
        · have := not_nonempty_iff.mp hA
          dsimp only
          rw [Real.iSup_of_isEmpty]
      · by_cases hA : Nonempty {law : ObservedLaw // InModel v law ∧ r ≤ hetDist law}
        · have := hA
          apply ciSup_le
          intro P
          exact hpower hrd P.1 P.2.1 P.2.2
        · have := not_nonempty_iff.mp hA
          rw [Real.iSup_of_isEmpty]
          norm_num
    exact csInf_le hb (Or.inl ⟨hr, hrd, hrisk⟩)
  · exact (csInf_le hb (Or.inr (Set.mem_singleton _))).trans (le_of_not_gt hrd)

/-- A calibrated oracle rule bounds the broader capped radius, including saturation. This statement assumes [the hD condition](hyp:hD), [the hr condition](hyp:hr), [the hlevel condition](hyp:hlevel), [the hpower condition](hyp:hpower). [This is the stated conclusion](goal). -/
lemma oracleBroadCriticalRadius_le_of_test (n : ℕ) (v : Params) (r : ℝ)
    (hD : 0 ≤ maxDistOracle v) (hr : 0 < r) (φ : OracleTest n)
    (hlevel : ∀ law, InOracleNull v law → oracleRejectProb n law φ ≤ 1/10)
    (hpower : r < maxDistOracle v → ∀ law, InOracleModel v law → r ≤ hetDist law →
      1-oracleRejectProb n law φ ≤ 1/10) : oracleBroadCriticalRadius n v ≤ r := by
  have hb : BddBelow ({t | 0 < t ∧ t < maxDistOracle v ∧
      oracleBroadTestingRisk n v t ≤ 1/10} ∪ {maxDistOracle v}) := by
    refine ⟨0, ?_⟩
    intro t ht
    rcases ht with ht | ht
    · exact ht.1.le
    · simpa only [Set.mem_singleton_iff.mp ht] using hD
  by_cases hrd : r < maxDistOracle v
  · have hrisk : oracleBroadTestingRisk n v r ≤ 1/10 := by
      unfold oracleBroadTestingRisk
      refine ciInf_le_of_le ?_ ⟨φ, hlevel⟩ ?_
      · refine ⟨0, ?_⟩
        rintro _ ⟨ψ, rfl⟩
        by_cases hA : Nonempty {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law}
        · obtain ⟨P⟩ := hA
          exact oracleBroadWorstError_nonneg n v r ψ.1 ⟨P.1, P.2⟩
        · have := not_nonempty_iff.mp hA
          dsimp only
          rw [Real.iSup_of_isEmpty]
      · by_cases hA : Nonempty {law : ObservedLaw // InOracleModel v law ∧ r ≤ hetDist law}
        · have := hA
          apply ciSup_le
          intro P
          exact hpower hrd P.1 P.2.1 P.2.2
        · have := not_nonempty_iff.mp hA
          rw [Real.iSup_of_isEmpty]
          norm_num
    exact csInf_le hb (Or.inl ⟨hr, hrd, hrisk⟩)
  · exact (csInf_le hb (Or.inr (Set.mem_singleton _))).trans (le_of_not_gt hrd)

end CausalSmith.Stat.FinitepHomogeneityDensegamma
