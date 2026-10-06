module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleMoments

/-! Oracle quadratic-statistic concentration and deterministic rejection cutoff comparisons. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The supplied-propensity testing exponent is strictly positive on every public tuple. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: E0_pos
lemma E0_pos (v : Params) (hv : v.Valid) : 0 < E0 v := by
  obtain ⟨hp, hm, hg, hs, hq, hqh, he, hd⟩ := phase_denominators v hv
  exact div_pos (mul_pos (mul_pos (by norm_num) hg) hq) he

/-- The paired-tent multiplier has the stated uniform positive lower bound. This statement assumes [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: cOracle_uniform_lower
lemma cOracle_uniform_lower (v : Params) (hv : v.Valid) :
    1/(64*Real.sqrt 3) ≤ cOracle v := by
  have hr : (4:ℝ)^(-1:ℝ) ≤ (4:ℝ)^(-v.γ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hv.2.2.2.2])
  norm_num [Real.rpow_neg_one] at hr
  unfold cOracle
  have hs : 0 < Real.sqrt (3:ℝ) := by positivity
  apply (le_div_iff₀ (by positivity : 0 < 16*Real.sqrt (3:ℝ))).mpr
  have he : (1/(64*Real.sqrt (3:ℝ)))*(16*Real.sqrt 3) = 1/4 := by
    field_simp
    <;> ring
  rw [he]
  exact hr

/-- The explicit upper multiplier is a finite positive real number. [This is the stated conclusion](goal). -/
-- @node: COr_pos
lemma COr_pos : 0 < COr := by unfold COr; positivity

/-- The public ceiling threshold places the nominal oracle separation below half the witness distance. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: oracle_attainment_threshold
lemma oracle_attainment_threshold (v : Params) (hv : v.Valid) (n : ℕ) (hn : NOr v ≤ n) :
    COr*rhoOracle n v ≤ d0/2 := by
  have he := E0_pos v hv
  have hc := COr_pos
  have hd : 0 < d0 := by unfold d0; positivity
  have ht : 0 < 2*COr/d0 := by positivity
  have hceil : max 2 ((2*COr/d0)^(1/E0 v)) ≤ (n:ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have htarget := (le_max_right (2:ℝ) ((2*COr/d0)^(1/E0 v))).trans hceil
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < (2*COr/d0)^(1/E0 v))
    htarget (neg_nonpos.mpr he.le)
  rw [← Real.rpow_mul ht.le] at hp
  have hid : (1/E0 v)*(-E0 v) = -1 := by field_simp
  rw [hid, Real.rpow_neg_one] at hp
  calc
    _ ≤ COr*(2*COr/d0)⁻¹ := mul_le_mul_of_nonneg_left hp hc.le
    _ = d0/2 := by field_simp

/-- Conditional arm means identify the original effect before clipping the observed score. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracle_untruncated_mean_identity
lemma oracle_untruncated_mean_identity (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InOracleModel v law) :
    ∀ᵐ x ∂design,
      law.e x*(∫ y, ipwUntruncated law.e (x,true,y) ∂law.Q true x)+
        (1-law.e x)*(∫ y, ipwUntruncated law.e (x,false,y) ∂law.Q false x) = law.tau x := by
  filter_upwards [law.mean0_version, law.mean1_version] with x hm0 hm1
  have he : 0 < law.e x := by linarith [(hm.overlap x).1]
  have hc : 0 < 1-law.e x := by linarith [(hm.overlap x).2]
  have hs1 (y : ℝ) : ipwUntruncated law.e (x,true,y) = y/law.e x := by
    simp [ipwUntruncated, treatment, A, X, Y, clipProp_eq_of_overlap law hm.overlap x]
  have hs0 (y : ℝ) : ipwUntruncated law.e (x,false,y) = -(y/(1-law.e x)) := by
    simp [ipwUntruncated, treatment, A, X, Y, clipProp_eq_of_overlap law hm.overlap x]
  simp only [hs1, hs0, integral_neg, integral_div]
  rw [← hm0, ← hm1]
  field_simp [he.ne', hc.ne']
  <;> ring

/-- The oracle variance envelope gives a strict-error probability of at most one percent. This statement assumes [the hW condition](hyp:hW), [the ht condition](hyp:ht), [the hΛ condition](hyp:hΛ), [the hJ condition](hyp:hJ), [the hmean condition](hyp:hmean), [the hvar condition](hyp:hvar). [This is the stated conclusion](goal). -/
-- @node: oracle_quadratic_tail_le
lemma oracle_quadratic_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (W : Ω → ℝ) (t Λ : ℝ) (J : ℕ)
    (hW : MemLp W 2 ν) (ht : 0 ≤ t) (hΛ : 0 < Λ) (hJ : 0 < J)
    (hmean : (∫ ω, W ω ∂ν) = t^2)
    (hvar : variance W ν ≤ 2*Λ*t^2+(J:ℝ)*Λ^2) :
    ν.real {ω | 16*(Real.sqrt Λ*t+Real.sqrt J*Λ) < |W ω-t^2|} ≤ 0.01 := by
  have hJr : (0:ℝ) < J := by exact_mod_cast hJ
  have hsΛ := Real.sq_sqrt hΛ.le
  have hsJ := Real.sq_sqrt hJr.le
  have hp : 0 < 16*(Real.sqrt Λ*t+Real.sqrt J*Λ) := by positivity
  have hc := Causalean.Stat.Concentration.probability_abs_sub_mean_gt_le ν W (t^2)
    (2*Λ*t^2+(J:ℝ)*Λ^2) (16*(Real.sqrt Λ*t+Real.sqrt J*Λ)) hW hp hmean hvar
  apply hc.trans
  apply (div_le_iff₀ (sq_pos_of_pos hp)).mpr
  have h1 : (Real.sqrt Λ*t)^2 = Λ*t^2 := by rw [mul_pow, hsΛ]
  have h2 : (Real.sqrt J*Λ)^2 = (J:ℝ)*Λ^2 := by rw [mul_pow, hsJ]
  have hx : 0 ≤ Real.sqrt Λ*t := mul_nonneg (Real.sqrt_nonneg _) ht
  have hy : 0 ≤ Real.sqrt J*Λ := mul_nonneg (Real.sqrt_nonneg _) hΛ.le
  nlinarith [mul_nonneg hx hy]

/-- The actual original-record oracle statistic satisfies the roadmap's 99 percent event. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_tail_le
lemma oracleBlockVec_tail_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) :
    let m := ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)
    let W := fun data => inner ℝ (oracleBlockVec n v law.e false data)
      (oracleBlockVec n v law.e true data)
    (Measure.pi (fun _ : Fin n => law.P)).real
      {data | 16*(Real.sqrt (oracleCov n v)*‖m‖+Real.sqrt (oracleJ n v)*oracleCov n v) <
        |W data-‖m‖^2|} ≤ 0.01 := by
  dsimp only
  have hB (b : Bool) : Measurable (oracleBlockVec n v law.e b) := by
    have hz : Measurable (fun data : Dataset n => (law.e, (data, (0 : unitInterval)))) := by
      fun_prop
    have hh := (measurable_oracleBlockVec n v b).comp hz
    change Measurable (oracleBlockVec n v law.e b) at hh
    exact hh
  have hW : MemLp (fun data => inner ℝ (oracleBlockVec n v law.e false data)
      (oracleBlockVec n v law.e true data)) 2 (Measure.pi fun _ : Fin n => law.P) := by
    apply (memLp_two_iff_integrable_sq ((hB false).inner (hB true)).aestronglyMeasurable).mpr
    exact Causalean.Stat.Concentration.integrable_indep_inner_sq _ _ _ (hB false) (hB true)
      (oracleBlockVec_memLp n v law.e false _ 2) (oracleBlockVec_memLp n v law.e true _ 2)
      (oracleBlockVec_indep n v law.e law)
  have hΛ : 0 < oracleCov n v := by
    have hT : 0 < oracleT n v := lt_of_lt_of_le zero_lt_one (oracleT_one_le n v hn hv)
    have hs : (0:ℝ) < blockSize n := by
      exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
    unfold oracleCov
    positivity
  exact oracle_quadratic_tail_le _ _ _ _ _ hW (norm_nonneg _) hΛ (oracleJ_pos n v)
    (oracleBlockVec_inner_integral n v hn law.e law)
    (oracleBlockVec_quadratic_variance_le n v hn hv law hm)

/-- Under a null mean bound, the good concentration event stays below the rejection cutoff. This statement assumes [the ht condition](hyp:ht), [the hb condition](hyp:hb), [the hΛ condition](hyp:hΛ), [the hJ condition](hyp:hJ), [the herr condition](hyp:herr). [This is the stated conclusion](goal). -/
-- @node: oracle_null_cutoff_le
lemma oracle_null_cutoff_le (W t b Λ : ℝ) (J : ℕ)
    (ht : 0 ≤ t) (hb : t ≤ b) (hΛ : 0 ≤ Λ) (hJ : 1 ≤ J)
    (herr : |W-t^2| ≤ 16*(Real.sqrt Λ*t+Real.sqrt J*Λ)) :
    W ≤ 2*b^2+1024*Real.sqrt J*Λ := by
  have hbr : 0 ≤ b := ht.trans hb
  have hsJ : 1 ≤ Real.sqrt J := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast hJ
  have hsΛ := Real.sq_sqrt hΛ
  have ht2 : t^2 ≤ b^2 := pow_le_pow_left₀ ht hb 2
  have hcross : 16*Real.sqrt Λ*t ≤ b^2+64*Λ := by
    have hmono := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ 16*Real.sqrt Λ)
    nlinarith [sq_nonneg (b-8*Real.sqrt Λ)]
  have hbudget : Λ ≤ Real.sqrt J*Λ := by nlinarith
  have hw := (abs_le.mp herr).2
  nlinarith

/-- The roadmap's signal margin forces rejection on the good concentration event. This statement assumes [the hb condition](hyp:hb), [the hΛ condition](hyp:hΛ), [the hJ condition](hyp:hJ), [the hsignal condition](hyp:hsignal), [the herr condition](hyp:herr). [This is the stated conclusion](goal). -/
-- @node: oracle_power_cutoff_lt
lemma oracle_power_cutoff_lt (W t b Λ : ℝ) (J : ℕ)
    (hb : 0 ≤ b) (hΛ : 0 < Λ) (hJ : 1 ≤ J)
    (hsignal : 4*b+128*Real.sqrt (Real.sqrt J*Λ) ≤ t)
    (herr : |W-t^2| ≤ 16*(Real.sqrt Λ*t+Real.sqrt J*Λ)) :
    2*b^2+1024*Real.sqrt J*Λ < W := by
  have hJr : (0:ℝ) < J := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have hsJ : 1 ≤ Real.sqrt J := Real.one_le_sqrt.mpr (by exact_mod_cast hJ)
  have hy : 0 < Real.sqrt (Real.sqrt J*Λ) := by positivity
  have hy2 := Real.sq_sqrt (show 0 ≤ Real.sqrt J*Λ by positivity)
  have hx2 := Real.sq_sqrt hΛ.le
  have hxy : Real.sqrt Λ ≤ Real.sqrt (Real.sqrt J*Λ) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have ht : 0 ≤ t := by linarith
  have hyt : 128*Real.sqrt (Real.sqrt J*Λ) ≤ t := by linarith
  have hcross : 16*Real.sqrt Λ*t ≤ t^2/2 := by
    have h1 := mul_le_mul_of_nonneg_right hxy ht
    have h2 := mul_le_mul_of_nonneg_right hyt ht
    nlinarith
  have ht2 : (4*b+128*Real.sqrt (Real.sqrt J*Λ))^2 ≤ t^2 :=
    pow_le_pow_left₀ (by positivity) hsignal 2
  have hw := (abs_le.mp herr).1
  nlinarith [mul_nonneg hb hy.le]

/-- The deterministic oracle rule has rejection expectation equal to its data event probability. [This is the stated conclusion](goal). -/
-- @node: oracleRejectProb_eq_measureReal
lemma oracleRejectProb_eq_measureReal (n : ℕ) (v : Params) (law : ObservedLaw) :
    oracleRejectProb n law (oracleTest n v) =
      (Measure.pi (fun _ : Fin n => law.P)).real
        {data | 2*oracleBias n v^2+1024*Real.sqrt (oracleJ n v)*oracleCov n v <
          inner ℝ (oracleBlockVec n v law.e false data)
            (oracleBlockVec n v law.e true data)} := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let ν := Measure.pi (fun _ : Fin n => law.P)
  let S : Set (Dataset n) := {data | 2*oracleBias n v^2+
    1024*Real.sqrt (oracleJ n v)*oracleCov n v <
      inner ℝ (oracleBlockVec n v law.e false data) (oracleBlockVec n v law.e true data)}
  have hB (b : Bool) : Measurable (oracleBlockVec n v law.e b) := by
    have hz : Measurable (fun data : Dataset n => (law.e, (data, (0 : unitInterval)))) := by
      fun_prop
    have hh := (measurable_oracleBlockVec n v b).comp hz
    change Measurable (oracleBlockVec n v law.e b) at hh
    exact hh
  have hS : MeasurableSet S := measurableSet_lt measurable_const ((hB false).inner (hB true))
  have he (z : Experiment n) : (oracleTest n v).1 (law.e,z) = S.indicator (fun _ => (1:ℝ)) z.1 := by
    simp only [oracleTest, oracleRule, Set.indicator, Set.mem_setOf_eq, S]
  unfold oracleRejectProb
  simp_rw [he]
  rw [expLaw, integral_prod]
  · simp only [integral_const, Measure.real, design, measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul]
    exact integral_indicator_one hS
  · apply Integrable.of_bound ((measurable_const.indicator hS).comp measurable_fst).aestronglyMeasurable 1
    exact ae_of_all _ (fun z => by by_cases hz : z.1 ∈ S <;> simp [hz])

/-- A population null mean bounded by the clipping budget gives the actual one-percent size bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hmean condition](hyp:hmean). [This is the stated conclusion](goal). -/
-- @node: oracle_size_of_mean_bound
lemma oracle_size_of_mean_bound (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law)
    (hmean : ‖∫ data, oracleBlockVec n v law.e false data
      ∂Measure.pi (fun _ : Fin n => law.P)‖ ≤ oracleBias n v) :
    oracleRejectProb n law (oracleTest n v) ≤ 0.01 := by
  let m := ∫ data, oracleBlockVec n v law.e false data
    ∂Measure.pi (fun _ : Fin n => law.P)
  have hΛ : 0 < oracleCov n v := by
    have hT : 0 < oracleT n v := lt_of_lt_of_le zero_lt_one (oracleT_one_le n v hn hv)
    have hs : (0:ℝ) < blockSize n := by
      exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
    unfold oracleCov
    positivity
  rw [oracleRejectProb_eq_measureReal]
  apply (measureReal_mono (s₂ := {data |
    16*(Real.sqrt (oracleCov n v)*‖m‖+Real.sqrt (oracleJ n v)*oracleCov n v) <
      |inner ℝ (oracleBlockVec n v law.e false data)
        (oracleBlockVec n v law.e true data)-‖m‖^2|}) ?_).trans
    (oracleBlockVec_tail_le n v hn hv law hm)
  intro data hrej
  by_contra hbad
  simp only [Set.mem_setOf_eq] at hbad
  have hgood := le_of_not_gt hbad
  have hcut := oracle_null_cutoff_le _ ‖m‖ (oracleBias n v) (oracleCov n v)
    (oracleJ n v) (norm_nonneg _) hmean hΛ.le (oracleJ_pos n v) hgood
  exact (not_lt_of_ge hcut) hrej

/-- A population signal margin gives the actual one-percent type-II bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hmean condition](hyp:hmean). [This is the stated conclusion](goal). -/
-- @node: oracle_power_of_mean_bound
lemma oracle_power_of_mean_bound (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law)
    (hmean : 4*oracleBias n v+128*Real.sqrt (Real.sqrt (oracleJ n v)*oracleCov n v) ≤
      ‖∫ data, oracleBlockVec n v law.e false data
        ∂Measure.pi (fun _ : Fin n => law.P)‖) :
    1-oracleRejectProb n law (oracleTest n v) ≤ 0.01 := by
  let ν := Measure.pi (fun _ : Fin n => law.P)
  let m := ∫ data, oracleBlockVec n v law.e false data ∂ν
  let S : Set (Dataset n) := {data | 2*oracleBias n v^2+
    1024*Real.sqrt (oracleJ n v)*oracleCov n v <
      inner ℝ (oracleBlockVec n v law.e false data) (oracleBlockVec n v law.e true data)}
  have hB (b : Bool) : Measurable (oracleBlockVec n v law.e b) := by
    have hz : Measurable (fun data : Dataset n => (law.e, (data, (0 : unitInterval)))) := by
      fun_prop
    have hh := (measurable_oracleBlockVec n v b).comp hz
    change Measurable (oracleBlockVec n v law.e b) at hh
    exact hh
  have hS : MeasurableSet S := measurableSet_lt measurable_const ((hB false).inner (hB true))
  have hΛ : 0 < oracleCov n v := by
    have hT : 0 < oracleT n v := lt_of_lt_of_le zero_lt_one (oracleT_one_le n v hn hv)
    have hs : (0:ℝ) < blockSize n := by
      exact_mod_cast (show 0 < blockSize n by unfold blockSize; omega)
    unfold oracleCov
    positivity
  have hb : 0 ≤ oracleBias n v := by
    have hT := (oracleT_one_le n v hn hv).trans' zero_le_one
    unfold oracleBias
    positivity
  rw [oracleRejectProb_eq_measureReal]
  change 1-ν.real S ≤ 0.01
  rw [← probReal_compl_eq_one_sub hS]
  apply (measureReal_mono (s₂ := {data |
    16*(Real.sqrt (oracleCov n v)*‖m‖+Real.sqrt (oracleJ n v)*oracleCov n v) <
      |inner ℝ (oracleBlockVec n v law.e false data)
        (oracleBlockVec n v law.e true data)-‖m‖^2|}) ?_).trans
    (oracleBlockVec_tail_le n v hn hv law hm)
  intro data hnrej
  by_contra hbad
  simp only [Set.mem_setOf_eq] at hbad
  have hcut := oracle_power_cutoff_lt _ ‖m‖ (oracleBias n v) (oracleCov n v)
    (oracleJ n v) hb hΛ (oracleJ_pos n v) hmean (le_of_not_gt hbad)
  exact hnrej hcut

end CausalSmith.Stat.FinitepHomogeneityDensegamma
