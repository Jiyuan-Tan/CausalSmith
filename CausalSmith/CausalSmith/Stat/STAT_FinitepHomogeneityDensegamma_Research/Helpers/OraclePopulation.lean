module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleCalibration
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.WeightedSeparation

/-! Centered oracle population means, whole-null calibration, and alternative separation. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- Centering commutes with integration of an integrable histogram coefficient. This statement assumes [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: integral_centered_feature_coefficient
lemma integral_centered_feature_coefficient (J : ℕ) (f : unitInterval → ℝ)
    (hf : Integrable f design) (hfm : Measurable f) :
    (∫ x, f x • centerVec (featureMap J x) ∂design) =
      centerVec (∫ x, f x • featureMap J x ∂design) := by
  have hi := integrable_feature_coefficient J f hf hfm
  have hc : Integrable (fun x => f x • centerVec (featureMap J x)) design := by
    apply (hf.norm.mul_const (Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
    exact ae_of_all _ (fun x => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        ((centerVec_norm_le _).trans (featureMap_norm_bound J x)) (norm_nonneg _))
  have hip (j : Fin J) : (∫ x, (f x • featureMap J x) j ∂design) =
      (∫ x, f x • featureMap J x ∂design) j :=
    (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integral_comp_comm hi
  have hcp (j : Fin J) : (∫ x, (f x • centerVec (featureMap J x)) j ∂design) =
      (∫ x, f x • centerVec (featureMap J x) ∂design) j :=
    (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integral_comp_comm hc
  have hij (j : Fin J) : Integrable (fun x => (f x • featureMap J x) j) design :=
    (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integrable_comp hi
  ext j
  rw [← hcp j, centerVec_apply]
  simp_rw [← hip]
  rw [← integral_finsetSum _ (fun k _ => hij k), ← integral_div]
  rw [← integral_sub (hij j) ((integrable_finsetSum _ (fun k _ => hij k)).div_const _)]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    simp only [PiLp.smul_apply, centerVec_apply, smul_eq_mul, ← Finset.mul_sum]
    ring)

/-- Every constant effect has zero centered histogram coefficient, at every positive rank. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: centered_constant_feature_integral
lemma centered_constant_feature_integral (J : ℕ) (hJ : 0 < J) (c : ℝ) :
    (∫ x, c • centerVec (featureMap J x) ∂design) = 0 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  rw [integral_centered_feature_coefficient J (fun _ => c) (integrable_const c) measurable_const]
  have he : (∫ x, c • featureMap J x ∂design) =
      WithLp.toLp 2 (fun _ : Fin J => Real.sqrt J*c*(J:ℝ)⁻¹) := by
    have hi := integrable_feature_coefficient J (fun _ => c) (integrable_const c) measurable_const
    ext j
    have hp := (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integral_comp_comm hi
    change (∫ x, (c • featureMap J x) j ∂design) =
      (∫ x, c • featureMap J x ∂design) j at hp
    rw [← hp]
    have hx (x : unitInterval) : (c • featureMap J x) j =
        (cell J j).indicator (fun _ => Real.sqrt J*c) x := by
      by_cases h : x ∈ cell J j <;> simp [featureMap, h, mul_comm]
    simp_rw [hx]
    rw [integral_indicator_const _ (measurableSet_histogram_cell J j)]
    simp [Measure.real, histogram_cell_volume J hJ j, mul_comm]
  rw [he, centerVec_const]

/-- Clipped inverse weighting integrates against the original conditional score mean. This statement assumes [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_population_integral
lemma oracleBlockVec_population_integral (n : ℕ) (v : Params) (hn : 2 ≤ n)
    (law : ObservedLaw) (hm : InOracleModel v law) :
    (∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ x, recordMarkMean law (ipwScore law.e (oracleT n v)) x •
        centerVec (featureMap (oracleJ n v) x) ∂design := by
  rw [oracleBlockVec_integral n v hn law.e false law]
  have hs : Measurable (ipwScore law.e (oracleT n v)) :=
    (measurable_ipwScore _).comp (measurable_const.prodMk measurable_id)
  exact original_record_weighted_integral law hm.uniform _ hs (4*|oracleT n v|)
    (by positivity) (ipwScore_abs_bound _ _) _
    ((continuous_centerVec _).measurable.comp (measurable_featureMap _))
    (Real.sqrt ((oracleJ n v:ℝ)*oracleJ n v)) (by positivity)
    (fun x => (centerVec_norm_le _).trans (featureMap_norm_bound _ x))

/-- Projection removes the unknown null constant exactly, leaving only the clipping bias. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hnull condition](hyp:hnull). [This is the stated conclusion](goal). -/
-- @node: oracle_null_population_norm_le
lemma oracle_null_population_norm_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hnull : InOracleNull v law) :
    ‖∫ data, oracleBlockVec n v law.e false data
      ∂Measure.pi (fun _ : Fin n => law.P)‖ ≤ oracleBias n v := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  obtain ⟨c, hc0, hc1, hconst⟩ := hnull.nullConstancy
  let g := recordMarkMean law (ipwScore law.e (oracleT n v))
  have hs : Measurable (ipwScore law.e (oracleT n v)) :=
    (measurable_ipwScore _).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable g := measurable_recordMarkMean law _ hs
  have hgi : Integrable g design := by
    apply Integrable.of_bound hg.aestronglyMeasurable (4*|oracleT n v|)
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using recordMarkMean_bound law _ hs _
        (by positivity) (ipwScore_abs_bound _ _) x)
  have hb : 0 ≤ oracleBias n v := by
    have hT := (oracleT_one_le n v hn hv).trans' zero_le_one
    unfold oracleBias
    positivity
  have hclip : ∀ᵐ x ∂design, |g x-c| ≤ oracleBias n v := by
    filter_upwards [oracle_clipping_moments v hv law hnull.toInOracleModel
      (oracleT n v) (oracleT_one_le n v hn hv)] with x hx
    simpa only [g, recordMarkMean, hconst x, oracleBias] using hx.1
  rw [oracleBlockVec_population_integral n v hn law hnull.toInOracleModel]
  have hi := integrable_feature_coefficient (oracleJ n v) g hgi hg
  have hci := integrable_feature_coefficient (oracleJ n v) (fun _ => c)
    (integrable_const c) measurable_const
  have he : (∫ x, g x • centerVec (featureMap (oracleJ n v) x) ∂design) =
      centerVec (∫ x, (g x-c) • featureMap (oracleJ n v) x ∂design) := by
    rw [integral_centered_feature_coefficient _ g hgi hg]
    have hzero := centered_constant_feature_integral (oracleJ n v) (oracleJ_pos n v) c
    rw [integral_centered_feature_coefficient _ (fun _ => c) (integrable_const c)
      measurable_const] at hzero
    have hsub : (∫ x, (g x-c) • featureMap (oracleJ n v) x ∂design) =
        (∫ x, g x • featureMap (oracleJ n v) x ∂design)-
          (∫ x, c • featureMap (oracleJ n v) x ∂design) := by
      simp_rw [sub_smul]
      exact integral_sub hi hci
    rw [hsub]
    ext j
    simp only [centerVec_apply, PiLp.sub_apply, Finset.sum_sub_distrib, sub_div]
    have hj := congrArg (fun z : Vec (oracleJ n v) => z j) hzero
    simp only [centerVec_apply, PiLp.zero_apply] at hj
    linarith
  change ‖∫ x, g x • centerVec (featureMap (oracleJ n v) x) ∂design‖ ≤ _
  rw [he]
  exact (centerVec_norm_le _).trans
    (histogram_coefficient_norm_le _ (oracleJ_pos n v) (fun x => g x-c)
      (hgi.sub (integrable_const c)) (hg.sub measurable_const) _ hb hclip)

/-- The explicit oracle test is calibrated on the entire original-mean null. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hnull condition](hyp:hnull). [This is the stated conclusion](goal). -/
-- @node: oracle_whole_null_size_le
lemma oracle_whole_null_size_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hnull : InOracleNull v law) :
    oracleRejectProb n law (oracleTest n v) ≤ 0.01 :=
  oracle_size_of_mean_bound n v hn hv law hnull.toInOracleModel
    (oracle_null_population_norm_le n v hn hv law hnull)


/-- Constant histogram coefficients have the same value in every coordinate. This statement assumes [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: constant_histogram_coefficient_coordinate
lemma constant_histogram_coefficient_coordinate (J : ℕ) (hJ : 0 < J) (c : ℝ)
    (j : Fin J) :
    (∫ x, c • featureMap J x ∂design) j = Real.sqrt J*c*(J:ℝ)⁻¹ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  rw [histogram_coefficient_coordinate J (fun _ => c) (integrable_const c)
    measurable_const, setIntegral_const]
  simp [Measure.real, histogram_cell_volume J hJ j, mul_comm, mul_left_comm, mul_assoc]

/-- Centering a histogram coefficient subtracts one scalar constant from its input. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: centered_histogram_coefficient_as_shift
lemma centered_histogram_coefficient_as_shift (J : ℕ) (hJ : 0 < J)
    (f : unitInterval → ℝ) (hf : Integrable f design) (hfm : Measurable f) :
    ∃ c : ℝ, centerVec (∫ x, f x • featureMap J x ∂design) =
      ∫ x, (f x-c) • featureMap J x ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let z : Vec J := ∫ x, f x • featureMap J x ∂design
  let c : ℝ := (∑ k : Fin J, z k)/Real.sqrt J
  refine ⟨c, ?_⟩
  simp_rw [sub_smul]
  rw [integral_sub (integrable_feature_coefficient J f hf hfm)
    (integrable_feature_coefficient J (fun _ => c) (integrable_const c) measurable_const)]
  ext j
  rw [centerVec_apply, PiLp.sub_apply, constant_histogram_coefficient_coordinate J hJ c j]
  dsimp only [z, c]
  rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr (by exact_mod_cast hJ)).ne']
  simp [div_eq_mul_inv]

/-- The broader oracle class retains exactly the effect assumptions needed for histogram approximation. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
lemma oracle_effect_histogram_coefficient_distance (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) (J : ℕ) (hJ : 0 < J) (c : ℝ) :
    hetDist law-20*(J:ℝ)^(-v.γ) ≤
      ‖∫ x, (projOp J law.tau x-c) • featureMap J x ∂design‖ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let f := fun x => law.tau x-c
  have ht : MemLp (fun x => law.tau x) 2 design :=
    MemLp.of_bound (by fun_prop) (1/2) (ae_of_all _ (fun x => by simpa using hm.effectCap x))
  have hf : MemLp f 2 design := ht.sub (memLp_const c)
  have hfi := ht.integrable (by norm_num)
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have he (x : unitInterval) : f x-projOp J f x = law.tau x-projOp J law.tau x := by
    rw [projOp_sub_const J hJ law.tau hfi c x]
    dsimp [f]
    ring
  have hδ : 0 ≤ 20*(J:ℝ)^(-v.γ) := by positivity
  have hb (x : unitInterval) : |f x-projOp J f x| ≤ 20*(J:ℝ)^(-v.γ) := by
    rw [he]
    exact projection_holder_error J hJ v.γ ⟨by linarith [hv.2.2.2.1], hv.2.2.2.2⟩
      law.tau hm.effectSmooth x
  have hres : (∫ x, (f x-projOp J f x)^2 ∂design) ≤ (20*(J:ℝ)^(-v.γ))^2 := by
    calc
      _ ≤ ∫ _x, (20*(J:ℝ)^(-v.γ))^2 ∂design := by
        apply integral_mono_of_nonneg (ae_of_all _ (fun x => sq_nonneg _)) (integrable_const _)
        exact ae_of_all _ (fun x => by simpa only [sq_abs] using
          (sq_le_sq₀ (abs_nonneg _) hδ).mpr (hb x))
      _ = _ := by simp
  have henergy := histogram_projection_energy J hJ f hf hfm
  have hd := effect_distance_sq_le_const_energy law hm.effectCap c
  have hqeq : (∫ x, f x • featureMap J x ∂design) =
      ∫ x, (projOp J law.tau x-c) • featureMap J x ∂design := by
    have hconst (x : unitInterval) : projOp J (fun _ => (1:ℝ)) x = 1 := by
      simpa [projOp] using (projection_rows J hJ x).1
    have hs := histogram_feature_selfAdjoint_integrable J J hJ hJ (dvd_refl J)
      f (fun _ => (1:ℝ)) hfm measurable_const (integrable_const 1)
      (1/2+|c|) (by positivity) (fun x => by
        dsimp [f]
        exact (abs_sub _ _).trans (by linarith [hm.effectCap x]))
    simp only [hconst, mul_one] at hs
    rw [hs]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by
      dsimp only
      change projOp J (fun z => law.tau z-c) x • featureMap J x = _
      rw [projOp_sub_const J hJ law.tau hfi c x])
  rw [hqeq] at henergy
  have hdnonneg : 0 ≤ hetDist law := Real.sqrt_nonneg _
  have hqnonneg := norm_nonneg (∫ x, (projOp J law.tau x-c) • featureMap J x ∂design)
  change hetDist law^2 ≤ ∫ x, f x^2 ∂design at hd
  nlinarith

/-- The centered original-effect histogram loses only the Holder approximation error. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ). [This is the stated conclusion](goal). -/
-- @node: centered_effect_histogram_distance
lemma centered_effect_histogram_distance (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) (J : ℕ) (hJ : 0 < J) :
    hetDist law-20*(J:ℝ)^(-v.γ) ≤
      ‖centerVec (∫ x, law.tau x • featureMap J x ∂design)‖ := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have ht : Integrable (fun x => law.tau x) design :=
    (integrable_const (1/2:ℝ)).mono' (by fun_prop)
      (ae_of_all _ (fun x => by simpa using hm.effectCap x))
  obtain ⟨c, hc⟩ := centered_histogram_coefficient_as_shift J hJ law.tau ht
    law.tau.continuous.measurable
  rw [hc]
  have hp (x : unitInterval) : projOp J (fun _ => (1:ℝ)) x = 1 := by
    simpa [projOp] using (projection_rows J hJ x).1
  have he := histogram_feature_selfAdjoint J J hJ hJ (dvd_refl J)
    (fun _ => (1:ℝ)) law.tau measurable_const law.tau.continuous.measurable
    1 (1/2) (by norm_num) (by norm_num) (fun _ => by norm_num) hm.effectCap
  simp only [hp, one_mul] at he
  have hi : Integrable (projOp J law.tau) design :=
    (integrable_const (1/2:ℝ)).mono' (by fun_prop)
      (ae_of_all _ (fun x => by
        simpa only [Real.norm_eq_abs] using
          (projOp_abs_le_ae_bound J hJ law.tau (1/2) (by norm_num)
            (ae_of_all _ hm.effectCap) x)))
  have hs : (∫ x, (law.tau x-c) • featureMap J x ∂design) =
      ∫ x, (projOp J law.tau x-c) • featureMap J x ∂design := by
    simp_rw [sub_smul]
    rw [integral_sub (integrable_feature_coefficient J law.tau ht (by fun_prop))
      (integrable_feature_coefficient J (fun _ => c) (integrable_const c) measurable_const),
      integral_sub (integrable_feature_coefficient J _ hi (by fun_prop))
      (integrable_feature_coefficient J (fun _ => c) (integrable_const c) measurable_const), he]
  rw [hs]
  exact oracle_effect_histogram_coefficient_distance v hv law hm J hJ c

/-- Clipping perturbs the centered oracle population coefficient by at most its bias ledger. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracle_population_clipping_error
lemma oracle_population_clipping_error (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) :
    ‖(∫ data, oracleBlockVec n v law.e false data
        ∂Measure.pi (fun _ : Fin n => law.P))-
      centerVec (∫ x, law.tau x • featureMap (oracleJ n v) x ∂design)‖ ≤
      oracleBias n v := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let g := recordMarkMean law (ipwScore law.e (oracleT n v))
  have hs : Measurable (ipwScore law.e (oracleT n v)) :=
    (measurable_ipwScore _).comp (measurable_const.prodMk measurable_id)
  have hg : Measurable g := measurable_recordMarkMean law _ hs
  have hgi : Integrable g design := by
    apply Integrable.of_bound hg.aestronglyMeasurable (4*|oracleT n v|)
    exact ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs] using recordMarkMean_bound law _ hs _
        (by positivity) (ipwScore_abs_bound _ _) x)
  have ht : Integrable (fun x => law.tau x) design :=
    (integrable_const (1/2:ℝ)).mono' (by fun_prop)
      (ae_of_all _ (fun x => by simpa using hm.effectCap x))
  have hb : ∀ᵐ x ∂design, |g x-law.tau x| ≤ oracleBias n v := by
    filter_upwards [oracle_clipping_moments v hv law hm (oracleT n v)
      (oracleT_one_le n v hn hv)] with x hx
    simpa only [g, recordMarkMean, oracleBias] using hx.1
  rw [oracleBlockVec_population_integral n v hn law hm,
    integral_centered_feature_coefficient _ g hgi hg]
  have he : centerVec (∫ x, g x • featureMap (oracleJ n v) x ∂design)-
      centerVec (∫ x, law.tau x • featureMap (oracleJ n v) x ∂design) =
      centerVec (∫ x, (g x-law.tau x) • featureMap (oracleJ n v) x ∂design) := by
    simp_rw [sub_smul]
    rw [integral_sub (integrable_feature_coefficient _ g hgi hg)
      (integrable_feature_coefficient _ law.tau ht (by fun_prop))]
    ext j
    simp only [centerVec_apply, PiLp.sub_apply, Finset.sum_sub_distrib, sub_div]
    ring
  rw [he]
  exact (centerVec_norm_le _).trans
    (histogram_coefficient_norm_le _ (oracleJ_pos n v) _ (hgi.sub ht)
      (hg.sub law.tau.continuous.measurable) _ (by
        have hT : 0 ≤ oracleT n v := (oracleT_one_le n v hn hv).trans' zero_le_one
        unfold oracleBias
        positivity) hb)

/-- Original-effect approximation and clipping give the alternative population norm lower bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracle_alternative_population_norm_ge
lemma oracle_alternative_population_norm_ge (n : ℕ) (v : Params) (hn : 2 ≤ n)
    (hv : v.Valid) (law : ObservedLaw) (hm : InOracleModel v law) :
    hetDist law-20*(oracleJ n v:ℝ)^(-v.γ)-oracleBias n v ≤
      ‖∫ data, oracleBlockVec n v law.e false data
        ∂Measure.pi (fun _ : Fin n => law.P)‖ := by
  have hd := centered_effect_histogram_distance v hv law hm _ (oracleJ_pos n v)
  have he := oracle_population_clipping_error n v hn hv law hm
  have ht := norm_sub_norm_le
    (centerVec (∫ x, law.tau x • featureMap (oracleJ n v) x ∂design))
    (∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P))
  rw [norm_sub_rev] at ht
  linarith

end CausalSmith.Stat.FinitepHomogeneityDensegamma
