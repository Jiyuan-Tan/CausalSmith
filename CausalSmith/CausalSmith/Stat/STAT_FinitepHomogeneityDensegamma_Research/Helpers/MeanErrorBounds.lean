module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreMeans
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.LedgerBias

/-! Quantitative histogram coefficient and clipping-tail bounds for the score mean ledger. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- A bounded scalar coefficient has a histogram coefficient vector of no larger norm. This statement assumes [the hJ condition](hyp:hJ), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: histogram_coefficient_norm_le
lemma histogram_coefficient_norm_le (J : ℕ) (hJ : 0 < J)
    (f : unitInterval → ℝ) (hf : Integrable f design) (hfm : Measurable f)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ᵐ x ∂design, |f x| ≤ C) :
    ‖∫ x, f x • featureMap J x ∂design‖ ≤ C := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hi := integrable_feature_coefficient J f hf hfm
  have hJr : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.mpr hJr
  have hc (j : Fin J) :
      (∫ x, f x • featureMap J x ∂design) j =
        Real.sqrt J * ∫ x in cell J j, f x ∂design := by
    have he := (PiLp.proj 2 (fun _ : Fin J => ℝ) j : Vec J →L[ℝ] ℝ).integral_comp_comm hi
    change (∫ x, (f x • featureMap J x) j ∂design) =
      (∫ x, f x • featureMap J x ∂design) j at he
    rw [← he, ← integral_const_mul, ← integral_indicator (measurableSet_histogram_cell J j)]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    simp only [PiLp.smul_apply, featureMap, PiLp.toLp_apply, smul_eq_mul]
    by_cases hx : x ∈ cell J j <;> simp [hx, mul_comm]
  have hcoord (j : Fin J) :
      |(∫ x, f x • featureMap J x ∂design) j| ≤ C / Real.sqrt J := by
    have hh : |∫ x in cell J j, f x ∂design| ≤ C*(J:ℝ)⁻¹ := by
      have hr := norm_integral_le_of_norm_le_const
        (μ := design.restrict (cell J j)) (f := f)
        (by
          filter_upwards [ae_restrict_of_ae hb] with x hx
          simpa using hx)
      simpa [Real.norm_eq_abs, Measure.real, histogram_cell_volume J hJ j,
        ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (J:ℝ)⁻¹)] using hr
    rw [hc, abs_mul, abs_of_pos hs]
    calc
      _ ≤ Real.sqrt J*(C*(J:ℝ)⁻¹) := mul_le_mul_of_nonneg_left hh hs.le
      _ = C/Real.sqrt J := by
        apply (eq_div_iff hs.ne').mpr
        calc
          _ = C*((Real.sqrt J)^2*(J:ℝ)⁻¹) := by ring
          _ = C := by rw [Real.sq_sqrt hJr.le, mul_inv_cancel₀ hJr.ne', mul_one]
  have hsq : ‖∫ x, f x • featureMap J x ∂design‖^2 ≤ C^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _ : Fin J, (C / Real.sqrt J)^2 := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 (hcoord j)
      _ = C^2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [div_pow, Real.sq_sqrt hJr.le]
        field_simp
  nlinarith [norm_nonneg (∫ x, f x • featureMap J x ∂design)]

/-- Cell averaging preserves an almost-everywhere absolute bound with its exact constant. This statement assumes [the hK condition](hyp:hK), [the hC condition](hyp:hC), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: projOp_abs_le_ae_bound
lemma projOp_abs_le_ae_bound (K : ℕ) (hK : 0 < K)
    (f : unitInterval → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ᵐ z ∂design, |f z| ≤ C) (x : unitInterval) :
    |projOp K f x| ≤ C := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  obtain ⟨j, hj, _⟩ := histogram_cell_unique K hK x
  have he : projOp K f x = (K:ℝ)*∫ z in cell K j, f z ∂design := by
    rw [projOp, ← integral_const_mul, ← integral_indicator (measurableSet_histogram_cell K j)]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    dsimp only
    rw [histogram_kernel_row K hK x j hj z]
    by_cases hz : z ∈ cell K j <;> simp [hz]
  have hh := norm_integral_le_of_norm_le_const
    (μ := design.restrict (cell K j)) (f := f)
    (by
      filter_upwards [ae_restrict_of_ae hb] with z hz
      simpa using hz)
  have hh' : |∫ z in cell K j, f z ∂design| ≤ C*(K:ℝ)⁻¹ := by
    simpa [Real.norm_eq_abs, Measure.real, histogram_cell_volume K hK j,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (K:ℝ)⁻¹)] using hh
  rw [he, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ K)]
  calc
    _ ≤ (K:ℝ)*(C*(K:ℝ)⁻¹) := mul_le_mul_of_nonneg_left hh' (by positivity)
    _ = C := by field_simp

/-- The raw moment envelope bounds the arm-weighted clipping remainder almost everywhere. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: tailRemainder_abs_le
lemma tailRemainder_abs_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T) :
    ∀ᵐ x ∂design, |tailRemainder law T x| ≤ 10*T^(1-v.p) := by
  have ht := conditional_truncation_moments v hv law hm.rawMoment T hT
  filter_upwards [ht true, ht false] with x h1 h0
  unfold tailRemainder
  calc
    _ ≤ |law.e x*(∫ y, y-clipY T y ∂law.Q true x)|+
        |(1-law.e x)*(∫ y, y-clipY T y ∂law.Q false x)| := abs_add_le _ _
    _ ≤ law.e x*(10*T^(1-v.p))+(1-law.e x)*(10*T^(1-v.p)) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (law.e_range x).1,
        abs_of_nonneg (sub_nonneg.mpr (law.e_range x).2)]
      exact add_le_add (mul_le_mul_of_nonneg_left h1.2.1 (law.e_range x).1)
        (mul_le_mul_of_nonneg_left h0.2.1 (sub_nonneg.mpr (law.e_range x).2))
    _ = _ := by ring

/-- The treated-arm remainder has an integrable, measurable propensity-weighted coefficient. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: treated_tail_feature_norm_le
lemma treated_tail_feature_norm_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J : ℕ) (hJ : 0 < J) (T : ℝ) (hT : 1 ≤ T) :
    ‖∫ x, (law.e x*treatedTailRemainder law T x) • featureMap J x ∂design‖ ≤
      10*T^(1-v.p) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hme : Measurable (fun x => law.e x*treatedTailRemainder law T x) := by
    unfold treatedTailRemainder
    exact law.e.continuous.measurable.mul
      (show StronglyMeasurable (fun y : ℝ => y-clipY T y) from
        (by unfold clipY; fun_prop)).integral_kernel.measurable
  have hb : ∀ᵐ x ∂design, |law.e x*treatedTailRemainder law T x| ≤ 10*T^(1-v.p) := by
    filter_upwards [conditional_truncation_moments v hv law hm.rawMoment T hT true] with x hx
    rw [abs_mul, abs_of_nonneg (law.e_range x).1]
    exact (mul_le_mul_of_nonneg_left hx.2.1 (law.e_range x).1).trans
      (by nlinarith [(law.e_range x).2, Real.rpow_nonneg (by linarith : 0 ≤ T) (1-v.p)])
  have hi : Integrable (fun x => law.e x*treatedTailRemainder law T x) design :=
    (integrable_const (10*T^(1-v.p))).mono' hme.aestronglyMeasurable
      (hb.mono (fun x hx => by simpa using hx))
  exact histogram_coefficient_norm_le J hJ _ hi hme _ (by positivity) hb

/-- A single-rank correction's complete clipping error costs at most twice the arm tail envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: singleMeanTail_norm_le
lemma singleMeanTail_norm_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K)
    (T : ℝ) (hT : 1 ≤ T) :
    ‖singleMeanTail law J K T‖ ≤ 20*T^(1-v.p) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hme : Measurable (fun x => law.e x*projOp K (tailRemainder law T) x) := by fun_prop
  have hb : ∀ x, |law.e x*projOp K (tailRemainder law T) x| ≤ 10*T^(1-v.p) := by
    intro x
    rw [abs_mul, abs_of_nonneg (law.e_range x).1]
    exact (mul_le_mul_of_nonneg_left
      (projOp_abs_le_ae_bound K hK _ _ (by positivity) (tailRemainder_abs_le v hv law hm T hT) x)
      (law.e_range x).1).trans
        (by nlinarith [(law.e_range x).2, Real.rpow_nonneg (by linarith : 0 ≤ T) (1-v.p)])
  have hi : Integrable (fun x => law.e x*projOp K (tailRemainder law T) x) design :=
    (integrable_const (10*T^(1-v.p))).mono' hme.aestronglyMeasurable
      (ae_of_all _ (fun x => by simpa using hb x))
  have hp := histogram_coefficient_norm_le J hJ _ hi hme _ (by positivity) (ae_of_all _ hb)
  unfold singleMeanTail
  calc
    _ ≤ ‖-(∫ x, (law.e x*treatedTailRemainder law T x) • featureMap J x ∂design)‖+
      ‖∫ x, (law.e x*projOp K (tailRemainder law T) x) • featureMap J x ∂design‖ := norm_add_le _ _
    _ ≤ 20*T^(1-v.p) := by
      rw [norm_neg]
      linarith [treated_tail_feature_norm_le v hv law hm J hJ T hT]

/-- Self-adjointness against coarse features also holds for integrable, potentially irregular tails. This statement assumes [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the he condition](hyp:he), [the hf condition](hyp:hf), [the hfi condition](hyp:hfi), [the hCe condition](hyp:hCe), [the hbe condition](hyp:hbe). [This is the stated conclusion](goal). -/
-- @node: histogram_feature_selfAdjoint_integrable
lemma histogram_feature_selfAdjoint_integrable (J K : ℕ) (hJ : 0 < J) (hK : 0 < K)
    (hJK : J ∣ K) (e f : unitInterval → ℝ) (he : Measurable e) (hf : Measurable f)
    (hfi : Integrable f design) (Ce : ℝ) (hCe : 0 ≤ Ce) (hbe : ∀ x, |e x| ≤ Ce) :
    (∫ x, (e x*projOp K f x) • featureMap J x ∂design) =
      ∫ x, (projOp K e x*f x) • featureMap J x ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hi : Integrable (fun z : unitInterval × unitInterval =>
      (e z.1*projKernel K z.1 z.2*f z.2) • featureMap J z.1) (design.prod design) := by
    apply ((hfi.norm.comp_snd design).mul_const (Ce*(K:ℝ)*Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
    apply ae_of_all
    intro z
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    have hh := mul_le_mul (hbe z.1) (histogram_kernel_bounds K hK z.1 z.2).2
      (abs_nonneg _) hCe
    have hh' := mul_le_mul hh (featureMap_norm_bound J z.1)
      (norm_nonneg _) (by positivity : 0 ≤ Ce*(K:ℝ))
    have ht := mul_le_mul_of_nonneg_right hh' (abs_nonneg (f z.2))
    simpa only [Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using ht
  calc
    _ = ∫ x, ∫ z, (e x*projKernel K x z*f z) • featureMap J x ∂design ∂design := by
      simp only [integral_smul_const, mul_assoc, integral_const_mul, projOp]
    _ = ∫ z, ∫ x, (e x*projKernel K x z*f z) • featureMap J x ∂design ∂design := integral_integral_swap hi
    _ = ∫ z, ∫ x, (projKernel K z x*e x*f z) • featureMap J z ∂design ∂design := by
      apply integral_congr_ae
      apply ae_of_all
      intro z
      apply integral_congr_ae
      apply ae_of_all
      intro x
      calc
        _ = (e x*f z) • (projKernel K x z • featureMap J x) := by module
        _ = (e x*f z) • (projKernel K z x • featureMap J z) := by
          rw [histogram_feature_kernel_commute J K hJ hK hJK]
        _ = _ := by module
    _ = _ := by simp only [integral_smul_const, integral_mul_const, projOp]

/-- An increment of the propensity projection is controlled by the preceding rank's Holder error. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hK condition](hyp:hK). [This is the stated conclusion](goal). -/
-- @node: propensity_projection_increment_bound
lemma propensity_projection_increment_bound (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (K : ℕ) (hK : 0 < K) (x : unitInterval) :
    |projOp (2*K) law.e x-projOp K law.e x| ≤ 40*(K:ℝ)^(-v.α) := by
  have h1 := projection_holder_error K hK v.α hv.2.1 law.e hm.propensitySmooth x
  have h2 := projection_holder_error (2*K) (by omega) v.α hv.2.1 law.e hm.propensitySmooth x
  have hr : ((2*K:ℕ):ℝ)^(-v.α) ≤ (K:ℝ)^(-v.α) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by norm_cast; omega)
    linarith [hv.2.1.1]
  calc
    _ ≤ |law.e x-projOp (2*K) law.e x|+|law.e x-projOp K law.e x| := by
      have h := abs_sub (law.e x-projOp K law.e x) (law.e x-projOp (2*K) law.e x)
      rw [show law.e x-projOp K law.e x-(law.e x-projOp (2*K) law.e x) =
        projOp (2*K) law.e x-projOp K law.e x by ring, add_comm] at h
      exact h
    _ ≤ 40*(K:ℝ)^(-v.α) := by linarith

/-- A refinement tail costs its propensity-increment envelope times the raw moment tail. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: mean_increment_tail_norm_le
lemma mean_increment_tail_norm_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K)
    (T : ℝ) (hT : 1 ≤ T) :
    ‖∫ x, (law.e x*(∫ z, diffKernel K x z*tailRemainder law T z ∂design)) •
      featureMap J x ∂design‖ ≤ 10*(40*(K:ℝ)^(-v.α))*T^(1-v.p) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let f := tailRemainder law T
  have hfi := integrable_tailRemainder v hv law hm T hT
  have hfm := measurable_tailRemainder law T
  have he (x : unitInterval) : |law.e x| ≤ 1 := by
    rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2
  have hi (R : ℕ) (hR : 0 < R) := integrable_projected_tail_feature law J R hR f hfi hfm
  have hid : (∫ x, (law.e x*(∫ z, diffKernel K x z*f z ∂design)) • featureMap J x ∂design) =
      ∫ x, ((projOp (2*K) law.e x-projOp K law.e x)*f x) • featureMap J x ∂design := by
    simp_rw [diffKernel_integral_eq_sub K hK f hfi, mul_sub, sub_smul]
    rw [integral_sub (hi (2*K) (by omega)) (hi K hK),
      histogram_feature_selfAdjoint_integrable J (2*K) hJ (by omega)
        (dvd_mul_of_dvd_right hJK 2) law.e f law.e.continuous.measurable hfm hfi 1 (by norm_num) he,
      histogram_feature_selfAdjoint_integrable J K hJ hK hJK law.e f law.e.continuous.measurable hfm hfi 1 (by norm_num) he]
    have hip (R : ℕ) (hR : 0 < R) : Integrable (fun x => (projOp R law.e x*f x) • featureMap J x) design := by
      apply (hfi.norm.mul_const ((R:ℝ)*Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
      apply ae_of_all
      intro x
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      have h := mul_le_mul (projOp_bound_of_bound R hR law.e 1 (by norm_num) he x)
        (featureMap_norm_bound J x) (norm_nonneg _) (by positivity)
      simpa only [mul_one, Real.norm_eq_abs, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right h (abs_nonneg (f x))
    rw [← integral_sub (hip (2*K) (by omega)) (hip K hK)]
    congr 1
    funext x
    module
  rw [hid]
  have hme : Measurable (fun x => (projOp (2*K) law.e x-projOp K law.e x)*f x) := by fun_prop
  have hb : ∀ᵐ x ∂design,
      |(projOp (2*K) law.e x-projOp K law.e x)*f x| ≤ 10*(40*(K:ℝ)^(-v.α))*T^(1-v.p) := by
    filter_upwards [tailRemainder_abs_le v hv law hm T hT] with x hx
    rw [abs_mul]
    have h := mul_le_mul (propensity_projection_increment_bound v hv law hm K hK x) hx
      (abs_nonneg _) (by positivity)
    nlinarith [h]
  have hscalar : Integrable (fun x => (projOp (2*K) law.e x-projOp K law.e x)*f x) design :=
    (integrable_const _).mono' hme.aestronglyMeasurable (hb.mono (fun x hx => by simpa using hx))
  exact histogram_coefficient_norm_le J hJ _ hscalar hme _ (by positivity) hb

/-- All refinement tails assemble with the finite public sum and no regularity of clipped means. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hT0 condition](hyp:hT0), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: multiresMeanTail_norm_le
lemma multiresMeanTail_norm_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J L : ℕ) (hJ : 0 < J) (T0 : ℝ) (hT0 : 1 ≤ T0)
    (T : Fin L → ℝ) (hT : ∀ j, 1 ≤ T j) :
    ‖multiresMeanTail law J L T0 T‖ ≤ 20*T0^(1-v.p)+
      10*∑ j : Fin L, (40*((2^j.val*J:ℕ):ℝ)^(-v.α))*T j^(1-v.p) := by
  have hs := singleMeanTail_norm_le v hv law hm J J hJ hJ T0 hT0
  have ht (j : Fin L) := mean_increment_tail_norm_le v hv law hm J (2^j.val*J)
    hJ (by positivity) (dvd_mul_left J _) (T j) (hT j)
  unfold multiresMeanTail
  calc
    _ ≤ ‖singleMeanTail law J J T0‖+
      ∑ j : Fin L, ‖∫ x, (law.e x*(∫ z, diffKernel (2^j.val*J) x z*tailRemainder law (T j) z ∂design)) •
        featureMap J x ∂design‖ := (norm_add_le _ _).trans (add_le_add_right (norm_sum_le _ _) _)
    _ ≤ _ := by
      have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ht j)
      simp only [mul_assoc, ← Finset.mul_sum] at hh
      apply add_le_add hs
      simpa only [mul_assoc, ← Finset.mul_sum] using hh

/-- A propensity approximation residual is orthogonal to the projected baseline within coarse features. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: baseline_projection_residual_identity
lemma baseline_projection_residual_identity (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K) :
    (∫ x, ((law.e x-projOp K law.e x)*law.m0 x) • featureMap J x ∂design) =
      ∫ x, ((law.e x-projOp K law.e x)*(law.m0 x-projOp K law.m0 x)) • featureMap J x ∂design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let r := fun x => law.e x-projOp K law.e x
  have he (x : unitInterval) : |law.e x| ≤ 1 := by
    rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2
  have hep (x : unitInterval) : |projOp K law.e x| ≤ 1 :=
    projOp_abs_le_ae_bound K hK law.e 1 (by norm_num) (ae_of_all _ he) x
  have hr (x : unitInterval) : |r x| ≤ 2 :=
    (abs_sub _ _).trans (by linarith [he x, hep x])
  have hrm : Measurable r := by dsimp [r]; fun_prop
  have hei : Integrable (fun x => law.e x) design :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun x => by simpa using he x))
  have hepi : Integrable (projOp K law.e) design :=
    (integrable_const (1:ℝ)).mono' (by fun_prop) (ae_of_all _ (fun x => by simpa using hep x))
  have hproj (x : unitInterval) : projOp K r x = 0 := by
    unfold projOp
    dsimp only [r]
    simp only [mul_sub]
    rw [integral_sub (integrable_histogram_row_mul K hK x _ hei)
      (integrable_histogram_row_mul K hK x _ hepi)]
    change projOp K law.e x-projOp K (projOp K law.e) x=0
    rw [projection_nesting K K hK (dvd_refl K) hK law.e hei, sub_self]
  have hzero : (∫ x, (r x*projOp K law.m0 x) • featureMap J x ∂design) = 0 := by
    rw [histogram_feature_selfAdjoint J K hJ hK hJK r law.m0 hrm
      law.m0.continuous.measurable 2 (1/2) (by norm_num) (by norm_num) hr hm.baselineCap]
    simp only [hproj, zero_mul, zero_smul, integral_zero]
  have hi : Integrable (fun x => (r x*law.m0 x) • featureMap J x) design :=
    integrable_bounded_feature_coefficient J _ (by fun_prop) 1 (fun x => by
      rw [abs_mul]; nlinarith [mul_le_mul (hr x) (hm.baselineCap x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)])
  have hip : Integrable (fun x => (r x*projOp K law.m0 x) • featureMap J x) design :=
    integrable_bounded_feature_coefficient J _ (by fun_prop) 1 (fun x => by
      rw [abs_mul]
      have hmp := projOp_abs_le_ae_bound K hK law.m0 (1/2) (by norm_num) (ae_of_all _ hm.baselineCap) x
      nlinarith [mul_le_mul (hr x) hmp (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)])
  change (∫ x, (r x*law.m0 x) • featureMap J x ∂design) = _
  simp only [mul_sub, sub_smul]
  rw [integral_sub hi hip, hzero, sub_zero]

/-- Propensity and baseline Holder errors multiply, giving the interaction approximation budget. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: baseline_projection_residual_norm_le
lemma baseline_projection_residual_norm_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K) :
    ‖∫ x, ((law.e x-projOp K law.e x)*law.m0 x) • featureMap J x ∂design‖ ≤
      400*(K:ℝ)^(-sumReg v) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  rw [baseline_projection_residual_identity v hv law hm J K hJ hK hJK]
  let f := fun x => (law.e x-projOp K law.e x)*(law.m0 x-projOp K law.m0 x)
  have hme : Measurable f := by dsimp [f]; fun_prop
  have hb (x : unitInterval) : |f x| ≤ 400*(K:ℝ)^(-sumReg v) := by
    dsimp [f]
    rw [abs_mul]
    have h := mul_le_mul
      (projection_holder_error K hK v.α hv.2.1 law.e hm.propensitySmooth x)
      (projection_holder_error K hK v.β hv.2.2.1 law.m0 hm.baselineSmooth x)
      (abs_nonneg _) (by positivity)
    have heq : (20*(K:ℝ)^(-v.α))*(20*(K:ℝ)^(-v.β)) = 400*(K:ℝ)^(-sumReg v) := by
      rw [show (20*(K:ℝ)^(-v.α))*(20*(K:ℝ)^(-v.β)) =
        400*((K:ℝ)^(-v.α)*(K:ℝ)^(-v.β)) by ring, ← Real.rpow_add (by positivity)]
      congr 2
      dsimp [sumReg]
      ring
    exact h.trans_eq heq
  have hi : Integrable f design := (integrable_const _).mono' hme.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa using hb x))
  exact histogram_coefficient_norm_le J hJ f hi hme _ (by positivity) (ae_of_all _ hb)

/-- The exact original mean differs from its weighted effect vector only by the interaction budget. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK). [This is the stated conclusion](goal). -/
-- @node: origMeanVector_weighted_error_le
lemma origMeanVector_weighted_error_le (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K) (c : ℝ) :
    ‖origMeanVector law J K c-∫ x,
      (law.e x*(1-projOp K law.e x)*(law.tau x-c)) • featureMap J x ∂design‖ ≤
      400*(K:ℝ)^(-sumReg v) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have he (x : unitInterval) : |law.e x| ≤ 1 := by
    rw [abs_of_nonneg (law.e_range x).1]; exact (law.e_range x).2
  have hep (x : unitInterval) : |projOp K law.e x| ≤ 1 :=
    projOp_abs_le_ae_bound K hK law.e 1 (by norm_num) (ae_of_all _ he) x
  have hi : Integrable (fun x => (law.e x*(1-projOp K law.e x)*(law.tau x-c)) • featureMap J x) design :=
    integrable_bounded_feature_coefficient J _ (by fun_prop) (2*(1/2+|c|)) (fun x => by
      rw [abs_mul, abs_mul]
      have h1 : |1-projOp K law.e x| ≤ 2 := (abs_sub _ _).trans (by norm_num; linarith [hep x])
      have h2 : |law.tau x-c| ≤ 1/2+|c| := (abs_sub _ _).trans (add_le_add (hm.effectCap x) le_rfl)
      have h3 := mul_le_mul (he x) h1 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith [mul_le_mul h3 h2 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1*2)])
  have hb : Integrable (fun x => ((law.e x-projOp K law.e x)*law.m0 x) • featureMap J x) design :=
    integrable_bounded_feature_coefficient J _ (by fun_prop) 1 (fun x => by
      rw [abs_mul]
      have hr : |law.e x-projOp K law.e x| ≤ 2 := (abs_sub _ _).trans (by linarith [he x, hep x])
      nlinarith [mul_le_mul hr (hm.baselineCap x) (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 2)])
  unfold origMeanVector
  simp only [add_smul]
  rw [integral_add hi hb, add_sub_cancel_left]
  exact baseline_projection_residual_norm_le v hv law hm J K hJ hK hJK

/-- The dyadic increment chain ends at exactly the final fine rank. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledger_final_rank_eq
lemma ledger_final_rank_eq (n : ℕ) (v : Params) (hn : 4 ≤ n) :
    2^(ledgerL n v)*ledgerM n v=ledgerK n v := by
  obtain ⟨hm, hmk, _⟩ := ledger_increment_rank_bound n v hn
  obtain ⟨m, hmEq⟩ : ∃ m, ledgerM n v=2^m := by
    simp only [ledgerM, if_neg (by omega : ¬n < 4), leastPow2Ge]
    exact ⟨_, rfl⟩
  obtain ⟨k, hkEq⟩ : ∃ k, ledgerK n v=2^k := by
    simp only [ledgerK, if_neg (by omega : ¬n < 4), leastPow2Ge]
    exact ⟨_, rfl⟩
  have hle : m ≤ k := by
    rw [hmEq, hkEq] at hmk
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hmk
  have he : 2^(k-m)*2^m=2^k := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  have hd : 2^k/2^m=2^(k-m) := by
    rw [← he, Nat.mul_div_cancel _ (by positivity : 0 < 2^m)]
  unfold ledgerL
  rw [hmEq, hkEq, hd, Nat.log_pow (by norm_num : 1 < 2)]
  exact he

/-- The public coarse rank divides the fine rank because their dyadic chain is exact. This statement assumes [the hn condition](hyp:hn). [This is the stated conclusion](goal). -/
-- @node: ledger_coarse_dvd_fine
lemma ledger_coarse_dvd_fine (n : ℕ) (v : Params) (hn : 4 ≤ n) :
    ledgerM n v ∣ ledgerK n v := by
  rw [← ledger_final_rank_eq n v hn]
  exact dvd_mul_left _ _

/-- Every level-specific cutoff satisfies the construction's minimum clipping level. [This is the stated conclusion](goal). -/
-- @node: ledgerT_ge_one
lemma ledgerT_ge_one (n : ℕ) (v : Params) (j : ℕ) : 1 ≤ ledgerT n v j := by
  unfold ledgerT
  split
  · exact le_rfl
  · exact (le_max_left _ _).trans (le_dyadUp (by positivity))

/-- The two explicit score branches share the same interaction and tail mean-error ledger. This statement assumes [the hv condition](hyp:hv), [the hn condition](hyp:hn), [the hm condition](hyp:hm). [This is the stated conclusion](goal). -/
-- @node: ledgerScore_weighted_mean_error_le
lemma ledgerScore_weighted_mean_error_le (v : Params) (hv : v.Valid) (n : ℕ) (hn : 4 ≤ n)
    (law : ObservedLaw) (hm : InModel v law) (b : Bool) (c : ℝ) :
    ‖thetaVec law (ledgerScore n v b) c-∫ x,
      (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c)) • featureMap (ledgerM n v) x ∂design‖ ≤ ledgerBias n v := by
  obtain ⟨hM, hMK, _⟩ := ledger_increment_rank_bound n v hn
  have hK : 0 < ledgerK n v := lt_of_lt_of_le hM hMK
  have hdiv := ledger_coarse_dvd_fine n v hn
  have ho := origMeanVector_weighted_error_le v hv law hm _ _ hM hK hdiv c
  have hn' : ¬n < 4 := by omega
  by_cases hb : singleBranch v
  · have he : ledgerScore n v b =
        (fun c data => hScore n b (ledgerM n v) (ledgerT0 n v) c data-
          uScore n b (ledgerM n v) (projKernel (ledgerK n v)) (ledgerT0 n v) c data) := by
      funext c data
      simp only [ledgerScore, if_neg hn', if_pos hb]
    rw [he, singleMean_exact v hv law hm n _ _ hn hM hK hdiv b _ (ledgerT0_ge_one n v) c]
    have ht := singleMeanTail_norm_le v hv law hm _ _ hM hK _ (ledgerT0_ge_one n v)
    have htri := norm_add_le
      (origMeanVector law (ledgerM n v) (ledgerK n v) c-∫ x,
        (law.e x*(1-projOp (ledgerK n v) law.e x)*(law.tau x-c)) • featureMap (ledgerM n v) x ∂design)
      (singleMeanTail law (ledgerM n v) (ledgerK n v) (ledgerT0 n v))
    rw [show ∀ A B C : Vec (ledgerM n v), A+B-C=(A-C)+B by intros; module]
    simp only [ledgerBias, if_neg hn', if_pos hb, add_zero]
    exact htri.trans (add_le_add ho ht)
  · have he : ledgerScore n v b =
        (fun c => multiresScore n b (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
          (fun j => ledgerT n v (j.val+1)) c) := by
      funext c data
      simp only [ledgerScore, if_neg hn', if_neg hb]
    rw [he, multiresMean_exact v hv law hm n _ _ hn hM b _ _
      (ledgerT0_ge_one n v) (fun j => ledgerT_ge_one n v _) c,
      ledger_final_rank_eq n v hn]
    have ht := multiresMeanTail_norm_le v hv law hm _ _ hM _ (ledgerT0_ge_one n v)
      (fun j : Fin (ledgerL n v) => ledgerT n v (j.val+1)) (fun j => ledgerT_ge_one n v _)
    change ‖origMeanVector law (ledgerM n v) (ledgerK n v) c+
      multiresMeanTail law (ledgerM n v) (ledgerL n v) (ledgerT0 n v)
        (fun j => ledgerT n v (j.val+1))-_‖ ≤ _
    rw [show ∀ A B C : Vec (ledgerM n v), A+B-C=(A-C)+B by intros; module]
    apply (norm_add_le _ _).trans
    have hh := add_le_add ho ht
    simpa only [ledgerBias, if_neg hn', if_neg hb, aLev, Nat.add_sub_cancel,
      ledgerR, add_assoc] using hh

end CausalSmith.Stat.FinitepHomogeneityDensegamma
