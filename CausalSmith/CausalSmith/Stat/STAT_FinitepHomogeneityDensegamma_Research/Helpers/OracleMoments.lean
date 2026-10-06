module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleBlockMeans
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.TruncationMoments
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerTuning
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.OracleQuadraticVariance
public import Mathlib.Probability.Moments.Variance

/-! Finite-moment homogeneity testing: Helpers/OracleMoments. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma


/-- On the model overlap interval the supplied propensity clipping is the identity. This statement assumes [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: clipProp_eq_of_overlap
lemma clipProp_eq_of_overlap (law : ObservedLaw) (hm : Overlap law) (x : unitInterval) :
    clipProp law.e x = law.e x := by
  simp only [clipProp, min_eq_left (hm x).2, max_eq_right (hm x).1]

/-- Oracle clipping moments: the displayed mathematical construction or bound. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: oracle_clipping_moments
lemma oracle_clipping_moments (v : Params) (hv : v.Valid) (law : ObservedLaw) (hm : InOracleModel v law)
    (T : ℝ) (hT : 1 ≤ T) :
    ∀ᵐ x ∂design,
      |law.e x*(∫ y, ipwScore law.e T (x,true,y) ∂law.Q true x)+
        (1-law.e x)*(∫ y, ipwScore law.e T (x,false,y) ∂law.Q false x)-law.tau x| ≤ 20*T^(1-v.p) ∧
      law.e x*(∫ y, ipwScore law.e T (x,true,y)^2 ∂law.Q true x)+
        (1-law.e x)*(∫ y, ipwScore law.e T (x,false,y)^2 ∂law.Q false x) ≤ 80*T^(2-v.p) := by
  have htrunc := conditional_truncation_moments v hv law hm.rawMoment T hT
  filter_upwards [htrunc true, htrunc false, law.mean0_version, law.mean1_version]
    with x h1 h0 hm0 hm1
  have he : 0 < law.e x := by linarith [(hm.overlap x).1]
  have hc : 0 < 1-law.e x := by linarith [(hm.overlap x).2]
  have hTp : 0 < T := by linarith
  have hi (a : Bool) : Integrable (fun y => clipY T y) (law.Q a x) := by
    apply (integrable_const T).mono' (by unfold clipY; fun_prop)
    exact Filter.Eventually.of_forall (fun y => by
      simpa only [Real.norm_eq_abs] using clipY_abs_le T y hTp.le)
  have hscore1 (y : ℝ) : ipwScore law.e T (x,true,y) = clipY T y/law.e x := by
    simp [ipwScore, treatment, A, X, Y, clipProp_eq_of_overlap law hm.overlap x]
  have hscore0 (y : ℝ) : ipwScore law.e T (x,false,y) = -(clipY T y/(1-law.e x)) := by
    simp [ipwScore, treatment, A, X, Y, clipProp_eq_of_overlap law hm.overlap x]
  simp only [hscore1, hscore0, neg_sq, div_pow, integral_neg, integral_div]
  have hmean1 : (∫ y, y-clipY T y ∂law.Q true x) =
      law.m0 x+law.tau x-(∫ y, clipY T y ∂law.Q true x) := by
    rw [integral_sub h1.1 (hi true), ← hm1]
  have hmean0 : (∫ y, y-clipY T y ∂law.Q false x) =
      law.m0 x-(∫ y, clipY T y ∂law.Q false x) := by
    rw [integral_sub h0.1 (hi false), ← hm0]
  constructor
  · have hid : law.e x*((∫ y, clipY T y ∂law.Q true x)/law.e x)+
        (1-law.e x)*-((∫ y, clipY T y ∂law.Q false x)/(1-law.e x))-law.tau x =
        (∫ y, y-clipY T y ∂law.Q false x)-(∫ y, y-clipY T y ∂law.Q true x) := by
      rw [hmean0, hmean1]
      field_simp [he.ne', hc.ne']
      ring
    rw [hid]
    calc
      _ ≤ |∫ y, y-clipY T y ∂law.Q false x|+|∫ y, y-clipY T y ∂law.Q true x| := abs_sub _ _
      _ ≤ 20*T^(1-v.p) := by linarith [h0.2.1, h1.2.1]
  · have hb1 : (∫ y, clipY T y^2 ∂law.Q true x)/law.e x ≤ 40*T^(2-v.p) := by
      apply (div_le_iff₀ he).mpr
      have hn : 0 ≤ T^(2-v.p) := Real.rpow_nonneg hTp.le _
      nlinarith [h1.2.2, (hm.overlap x).1]
    have hb0 : (∫ y, clipY T y^2 ∂law.Q false x)/(1-law.e x) ≤ 40*T^(2-v.p) := by
      apply (div_le_iff₀ hc).mpr
      have hn : 0 ≤ T^(2-v.p) := Real.rpow_nonneg hTp.le _
      nlinarith [h0.2.2, (hm.overlap x).2]
    have hid1 : law.e x*((∫ y, clipY T y^2 ∂law.Q true x)/law.e x^2) =
        (∫ y, clipY T y^2 ∂law.Q true x)/law.e x := by
      field_simp [he.ne']
    have hid0 : (1-law.e x)*((∫ y, clipY T y^2 ∂law.Q false x)/(1-law.e x)^2) =
        (∫ y, clipY T y^2 ∂law.Q false x)/(1-law.e x) := by
      field_simp [hc.ne']
    rw [hid1, hid0]
    linarith
/-- A centered histogram contrast is uniformly bounded by its Euclidean norm times the feature bound. [This is the stated conclusion](goal). -/
-- @node: centered_feature_contrast_bound
lemma centered_feature_contrast_bound (J : ℕ) (u : Vec J) (x : unitInterval) :
    |inner ℝ u (centerVec (featureMap J x))| ≤ ‖u‖*Real.sqrt ((J:ℝ)*J) := by
  exact (abs_real_inner_le_norm u _).trans
    (mul_le_mul_of_nonneg_left ((centerVec_norm_le _).trans (featureMap_norm_bound J x))
      (norm_nonneg u))

/-- Integrating the squared oracle contrast retains its conditional score second moment. This statement assumes [the hu condition](hyp:hu). [This is the stated conclusion](goal). -/
-- @node: oracle_contrast_second_moment_eq
lemma oracle_contrast_second_moment_eq (law : ObservedLaw) (hu : UniformDesign law)
    (J : ℕ) (T : ℝ) (u : Vec J) :
    (∫ o, (inner ℝ u (ipwScore law.e T o • centerVec (featureMap J (X o))))^2 ∂law.P) =
      ∫ x, (law.e x*(∫ y, ipwScore law.e T (x,true,y)^2 ∂law.Q true x)+
        (1-law.e x)*(∫ y, ipwScore law.e T (x,false,y)^2 ∂law.Q false x))*
          (inner ℝ u (centerVec (featureMap J x)))^2 ∂design := by
  have hm : Measurable (fun o : Record =>
      inner ℝ u (ipwScore law.e T o • centerVec (featureMap J (X o)))) := by
    have hs : Measurable (fun o : Record => ipwScore law.e T o) := (measurable_ipwScore T).comp (measurable_const.prodMk measurable_id)
    have hf := (continuous_centerVec J).measurable.comp ((measurable_featureMap J).comp
      (show Measurable X from by unfold X; fun_prop))
    exact (continuous_const.inner continuous_id).measurable.comp (hs.smul hf)
  rw [original_record_integral_arms law hu _ (hm.pow_const 2)
    ((4*|T| *(‖u‖*Real.sqrt ((J:ℝ)*J)))^2) (fun o => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), inner_smul_right,
        ← sq_abs (ipwScore law.e T o * inner ℝ u (centerVec (featureMap J (X o)))), abs_mul]
      exact pow_le_pow_left₀ (by positivity)
        (mul_le_mul (ipwScore_abs_bound law.e T o)
          (centered_feature_contrast_bound J u (X o)) (abs_nonneg _) (by positivity)) 2)]
  simp only [inner_smul_right, mul_pow, integral_mul_const, smul_eq_mul, X]
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by ring)

/-- The conditional clipped moment bound and histogram isometry give the single-record covariance budget. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: oracle_contrast_second_moment_le
lemma oracle_contrast_second_moment_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InOracleModel v law) (J : ℕ) (hJ : 0 < J) (T : ℝ) (hT : 1 ≤ T) (u : Vec J) :
    (∫ o, (inner ℝ u (ipwScore law.e T o • centerVec (featureMap J (X o))))^2 ∂law.P) ≤
      80*T^(2-v.p)*‖u‖^2 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hf : MemLp (fun x => inner ℝ u (centerVec (featureMap J x))) 2 design :=
    ((centeredFeature_memLp_top design J id measurable_id).const_inner u).mono_exponent le_top
  rw [oracle_contrast_second_moment_eq law hm.uniform]
  calc
    _ ≤ ∫ x, (80*T^(2-v.p))*(inner ℝ u (centerVec (featureMap J x)))^2 ∂design := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ (fun x => mul_nonneg
          (add_nonneg (mul_nonneg (law.e_range x).1 (integral_nonneg (fun _ => sq_nonneg _)))
            (mul_nonneg (sub_nonneg.mpr (law.e_range x).2) (integral_nonneg (fun _ => sq_nonneg _))))
          (sq_nonneg _))
      · exact hf.integrable_sq.const_mul _
      · filter_upwards [oracle_clipping_moments v hv law hm T hT] with x hx
        exact mul_le_mul_of_nonneg_right hx.2 (sq_nonneg _)
    _ = (80*T^(2-v.p))*(∫ x, (inner ℝ u (centerVec (featureMap J x)))^2 ∂design) :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (centered_feature_energy_le J hJ u) (by positivity)

/-- The oracle cutoff is at least one, even when the block contains just one record. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv). [This is the stated conclusion](goal). -/
-- @node: oracleT_one_le
lemma oracleT_one_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid) :
    1 ≤ oracleT n v := by
  have hs : 1 ≤ (blockSize n:ℝ) := by
    exact_mod_cast (show 1 ≤ blockSize n by unfold blockSize; omega)
  have hd := phase_denominators v hv
  have hE : 0 < E0 v := div_pos (mul_pos (mul_pos (by norm_num) hd.2.2.1) hd.2.2.2.2.1)
    hd.2.2.2.2.2.2.1
  have heq : oracleA n v ^ (-1/(v.p-1)) = (blockSize n:ℝ)^(E0 v/(v.p-1)) := by
    unfold oracleA
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ blockSize n)]
    congr 1
    ring
  unfold oracleT
  apply (ledger_dyadUp_bounds _).1
  rw [heq]
  exact Real.one_le_rpow hs (div_pos hE hd.2.1).le

/-- Upward dyadic oracle rank rounding always gives a positive rank. [This is the stated conclusion](goal). -/
-- @node: oracleJ_pos
lemma oracleJ_pos (n : ℕ) (v : Params) : 0 < oracleJ n v := by
  unfold oracleJ leastPow2Ge
  positivity

/-- An iid average over either public block has population variance divided by the block size. This statement assumes [the hn condition](hyp:hn), [the hg condition](hyp:hg). [This is the stated conclusion](goal). -/
-- @node: oracle_scalar_block_variance
lemma oracle_scalar_block_variance (n : ℕ) (hn : 2 ≤ n) (b : Bool) (law : ObservedLaw)
    (g : Record → ℝ) (hg : MemLp g 2 law.P) :
    variance (fun data : Dataset n => (blockSize n:ℝ)⁻¹ * ∑ i ∈ evalBlock n b, g (data i))
      (Measure.pi fun _ : Fin n => law.P) = variance g law.P/(blockSize n:ℝ) := by
  have hi (i : Fin n) : MemLp (fun data : Dataset n => g (data i)) 2
      (Measure.pi fun _ : Fin n => law.P) :=
    hg.comp_measurePreserving (measurePreserving_eval _ i)
  have hind : iIndepFun (fun i : Fin n => fun data : Dataset n => g (data i))
      (Measure.pi fun _ : Fin n => law.P) :=
    iIndepFun_pi (fun _ => hg.aemeasurable)
  have hsum := IndepFun.variance_sum (fun i (_ : i ∈ evalBlock n b) => hi i)
    (fun i (_ : i ∈ evalBlock n b) j (_ : j ∈ evalBlock n b) hij => hind.indepFun hij)
  have he : variance (fun data : Dataset n => ∑ i ∈ evalBlock n b, g (data i))
      (Measure.pi fun _ : Fin n => law.P) =
      (blockSize n:ℝ)*variance g law.P := by
    convert hsum using 1
    · congr 1
      funext data
      simp
    · simp only [(measurePreserving_eval (fun _ : Fin n => law.P) _).variance_fun_comp hg.aemeasurable,
        Finset.sum_const, evalBlock_card, nsmul_eq_mul]
  rw [variance_const_mul, he]
  have hs : (blockSize n:ℝ) ≠ 0 := by
    exact_mod_cast (show blockSize n ≠ 0 by unfold blockSize; omega)
  field_simp

/-- Every centered oracle block contrast has the displayed covariance budget. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_variance_le
lemma oracleBlockVec_variance_le (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) (b : Bool) (u : Vec (oracleJ n v)) :
    variance (fun data => inner ℝ u (oracleBlockVec n v law.e b data))
      (Measure.pi fun _ : Fin n => law.P) ≤ oracleCov n v*‖u‖^2 := by
  let g := fun o : Record => inner ℝ u
    (ipwScore law.e (oracleT n v) o • centerVec (featureMap (oracleJ n v) (X o)))
  have hg : MemLp g 2 law.P :=
    (((centeredFeature_memLp_top law.P _ X (by unfold X; fun_prop)).smul
      (ipwScore_memLp_top law.P law.e _ id measurable_id)).const_inner u).mono_exponent le_top
  have he : (fun data => inner ℝ u (oracleBlockVec n v law.e b data)) =
      fun data : Dataset n => (blockSize n:ℝ)⁻¹ * ∑ i ∈ evalBlock n b, g (data i) := by
    funext data
    simp [oracleBlockVec, inner_smul_right, inner_sum, g]
  rw [he, oracle_scalar_block_variance n hn b law g hg]
  have hvar : variance g law.P ≤ 80*oracleT n v^(2-v.p)*‖u‖^2 :=
    (variance_le_expectation_sq hg.aestronglyMeasurable).trans
      (oracle_contrast_second_moment_le v hv law hm _ (oracleJ_pos n v) _
        (oracleT_one_le n v hn hv) u)
  calc
    _ ≤ (80*oracleT n v^(2-v.p)*‖u‖^2)/(blockSize n:ℝ) :=
      div_le_div_of_nonneg_right hvar (by positivity)
    _ = _ := by unfold oracleCov; ring

/-- Subtracting the shared oracle block mean converts its variance budget into a second moment. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_centered_second_moment_le
lemma oracleBlockVec_centered_second_moment_le (n : ℕ) (v : Params) (hn : 2 ≤ n)
    (hv : v.Valid) (law : ObservedLaw) (hm : InOracleModel v law) (b : Bool)
    (u : Vec (oracleJ n v)) :
    let m := ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)
    (∫ data, (inner ℝ u (oracleBlockVec n v law.e b data-m))^2
      ∂Measure.pi (fun _ : Fin n => law.P)) ≤ oracleCov n v*‖u‖^2 := by
  dsimp only
  have hi : Integrable (oracleBlockVec n v law.e b)
      (Measure.pi fun _ : Fin n => law.P) :=
    (oracleBlockVec_memLp n v law.e b _ 1).integrable le_rfl
  have he : (∫ data, oracleBlockVec n v law.e b data ∂Measure.pi (fun _ : Fin n => law.P)) =
      ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P) := by
    rw [oracleBlockVec_integral n v hn law.e b law,
      oracleBlockVec_integral n v hn law.e false law]
  have h := oracleBlockVec_variance_le n v hn hv law hm b u
  rw [variance_eq_integral (oracleBlockVec_inner_memLp n v law.e b law u).aemeasurable,
    integral_inner hi, he] at h
  simpa only [inner_sub_right] using h

/-- The oracle quadratic statistic has the exact independent-block variance envelope. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracleBlockVec_quadratic_variance_le
lemma oracleBlockVec_quadratic_variance_le (n : ℕ) (v : Params) (hn : 2 ≤ n)
    (hv : v.Valid) (law : ObservedLaw) (hm : InOracleModel v law) :
    let m := ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)
    variance (fun data => inner ℝ (oracleBlockVec n v law.e false data)
      (oracleBlockVec n v law.e true data)) (Measure.pi fun _ : Fin n => law.P) ≤
      2*oracleCov n v*‖m‖^2+oracleJ n v*oracleCov n v^2 := by
  let ν := Measure.pi (fun _ : Fin n => law.P)
  let m := ∫ data, oracleBlockVec n v law.e false data ∂ν
  let B := fun b => oracleBlockVec n v law.e b
  let C := fun b data => B b data-m
  have hB (b : Bool) : Measurable (B b) := by
    have hz : Measurable (fun data : Dataset n => (law.e, (data, (0 : unitInterval)))) := by
      fun_prop
    have hh := (measurable_oracleBlockVec n v b).comp hz
    change Measurable (oracleBlockVec n v law.e b) at hh
    exact hh
  have hC (b : Bool) : Measurable (C b) := (hB b).sub measurable_const
  have hBL (b : Bool) : MemLp (B b) ∞ ν := oracleBlockVec_memLp_top n v law.e b ν
  have hCL (b : Bool) : MemLp (C b) ∞ ν := (hBL b).sub (memLp_const m)
  have hmean (b : Bool) : (∫ data, B b data ∂ν) = m := by
    dsimp [B, m, ν]
    rw [oracleBlockVec_integral n v hn law.e b law,
      oracleBlockVec_integral n v hn law.e false law]
  have hzero (b : Bool) : (∫ data, C b data ∂ν) = 0 := by
    dsimp [C]
    rw [integral_sub (((hBL b).mono_exponent (show 1 ≤ ∞ from le_top)).integrable le_rfl)
      (integrable_const m), hmean, integral_const]
    simp
  have hind : IndepFun (C false) (C true) ν :=
    (oracleBlockVec_indep n v law.e law).comp
      (measurable_id.sub measurable_const) (measurable_id.sub measurable_const)
  have hbound := centered_block_quadratic_second_moment_le ν (C false) (C true) m
    (oracleCov n v) (hC false) (hC true) (hCL false) (hCL true) hind
    (hzero false) (hzero true)
    (oracleBlockVec_centered_second_moment_le n v hn hv law hm false)
    (oracleBlockVec_centered_second_moment_le n v hn hv law hm true)
  have hW : Measurable (fun data => inner ℝ (B false data) (B true data)) := by
    fun_prop
  rw [variance_eq_integral hW.aemeasurable,
    oracleBlockVec_inner_integral n v hn law.e law]
  change (∫ data, (inner ℝ (B false data) (B true data)-‖m‖^2)^2 ∂ν) ≤ _
  convert hbound using 1
  congr 1
  funext data
  dsimp [C]
  simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
  rw [real_inner_comm (B false data) m]
  ring

/-- Oracle block moments: the displayed mathematical construction or bound. This statement assumes [the hn condition](hyp:hn), [the hv condition](hyp:hv), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: oracle_block_moments
lemma oracle_block_moments (n : ℕ) (v : Params) (hn : 2 ≤ n) (hv : v.Valid)
    (law : ObservedLaw) (hm : InOracleModel v law) :
    let μ := ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)
    let W := fun data => inner ℝ (oracleBlockVec n v law.e false data) (oracleBlockVec n v law.e true data)
    (∀ b u, MemLp (fun data => inner ℝ u (oracleBlockVec n v law.e b data)) 2 (Measure.pi fun _ : Fin n => law.P) ∧
      variance (fun data => inner ℝ u (oracleBlockVec n v law.e b data)) (Measure.pi fun _ : Fin n => law.P) ≤ oracleCov n v*‖u‖^2) ∧
    (∫ data, W data ∂Measure.pi (fun _ : Fin n => law.P)) = ‖μ‖^2 ∧
    variance W (Measure.pi fun _ : Fin n => law.P) ≤ 2*oracleCov n v*‖μ‖^2+oracleJ n v*oracleCov n v^2 := by
  let μ := ∫ data, oracleBlockVec n v law.e false data ∂Measure.pi (fun _ : Fin n => law.P)
  let W := fun data => inner ℝ (oracleBlockVec n v law.e false data) (oracleBlockVec n v law.e true data)
  have hquant : (∀ b u,
      variance (fun data => inner ℝ u (oracleBlockVec n v law.e b data))
        (Measure.pi fun _ : Fin n => law.P) ≤ oracleCov n v*‖u‖^2) ∧
      variance W (Measure.pi fun _ : Fin n => law.P) ≤
        2*oracleCov n v*‖μ‖^2+oracleJ n v*oracleCov n v^2 := by
    constructor
    · exact oracleBlockVec_variance_le n v hn hv law hm
    · exact oracleBlockVec_quadratic_variance_le n v hn hv law hm
  exact ⟨fun b u => ⟨oracleBlockVec_inner_memLp n v law.e b law u, hquant.1 b u⟩,
    oracleBlockVec_inner_integral n v hn law.e law, hquant.2⟩

end CausalSmith.Stat.FinitepHomogeneityDensegamma
