module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreExpectations
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Exact mean telescoping for the clipped single and multiresolution scores. -/
public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The exact arm-weighted clipping remainder is measurable. [This is the stated conclusion](goal). -/
-- @node: measurable_tailRemainder
@[fun_prop] lemma measurable_tailRemainder (law : ObservedLaw) (T : ℝ) :
    Measurable (tailRemainder law T) := by
  have he := law.e.continuous.measurable
  have hr (a : Bool) : Measurable (fun x => ∫ y, y-clipY T y ∂law.Q a x) :=
    (show StronglyMeasurable (fun y : ℝ => y-clipY T y) from (by unfold clipY; fun_prop)).integral_kernel.measurable
  exact (he.mul (hr true)).add ((measurable_const.sub he).mul (hr false))

/-- The conditional moment envelope makes the complete clipping remainder integrable. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: integrable_tailRemainder
lemma integrable_tailRemainder (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T) :
    Integrable (tailRemainder law T) design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  apply (integrable_const (10*T^(1-v.p))).mono' (by fun_prop)
  have ht := conditional_truncation_moments v hv law hm.rawMoment T hT
  filter_upwards [ht true, ht false] with x h1 h0
  rw [Real.norm_eq_abs]
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

/-- A histogram row times an integrable function is integrable. This statement assumes [the hK condition](hyp:hK), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: integrable_histogram_row_mul
lemma integrable_histogram_row_mul (K : ℕ) (hK : 0 < K) (x : unitInterval)
    (f : unitInterval → ℝ) (hf : Integrable f design) :
    Integrable (fun z => projKernel K x z*f z) design := by
  apply hf.bdd_mul (by fun_prop)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using (histogram_kernel_bounds K hK x z).2)

/-- Histogram projection of an integrable function has a uniform finite bound. This statement assumes [the hK condition](hyp:hK), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: projOp_abs_le_integral_abs
lemma projOp_abs_le_integral_abs (K : ℕ) (hK : 0 < K)
    (f : unitInterval → ℝ) (hf : Integrable f design) (x : unitInterval) :
    |projOp K f x| ≤ (K:ℝ)*(∫ z, |f z| ∂design) := by
  unfold projOp
  calc
    _ ≤ ∫ z, |projKernel K x z*f z| ∂design := abs_integral_le_integral_abs
    _ ≤ ∫ z, (K:ℝ)*|f z| ∂design := by
      apply integral_mono_ae (integrable_histogram_row_mul K hK x f hf).abs
        (hf.abs.const_mul _)
      exact ae_of_all _ (fun z => by
        dsimp only
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (histogram_kernel_bounds K hK x z).2 (abs_nonneg _))
    _ = _ := integral_const_mul _ _

/-- The weighted feature coefficient of a histogram projection is integrable. This statement assumes [the hK condition](hyp:hK), [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: integrable_projected_tail_feature
lemma integrable_projected_tail_feature (law : ObservedLaw) (J K : ℕ) (hK : 0 < K)
    (f : unitInterval → ℝ) (hf : Integrable f design) (hfm : Measurable f) :
    Integrable (fun x => (law.e x*projOp K f x) • featureMap J x) design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hp : Measurable (projOp K f) := by
    unfold projOp
    exact (show Measurable (fun z : unitInterval × unitInterval =>
      projKernel K z.1 z.2*f z.2) from (by fun_prop)).stronglyMeasurable.integral_prod_right.measurable
  apply (integrable_const ((K:ℝ)*(∫ z, |f z| ∂design)*Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (law.e_range x).1]
  calc
    _ ≤ (1*((K:ℝ)*(∫ z, |f z| ∂design)))*Real.sqrt ((J:ℝ)*J) := by
      gcongr
      · exact (law.e_range x).2
      · exact projOp_abs_le_integral_abs K hK f hf x
      · exact featureMap_norm_bound J x
    _ = _ := by ring

/-- Multiplication by bounded histogram features preserves integrability of a scalar coefficient. This statement assumes [the hf condition](hyp:hf), [the hfm condition](hyp:hfm). [This is the stated conclusion](goal). -/
-- @node: integrable_feature_coefficient
lemma integrable_feature_coefficient (J : ℕ) (f : unitInterval → ℝ)
    (hf : Integrable f design) (hfm : Measurable f) :
    Integrable (fun x => f x • featureMap J x) design := by
  apply (hf.norm.mul_const (Real.sqrt ((J:ℝ)*J))).mono' (by fun_prop)
  apply ae_of_all
  intro x
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (featureMap_norm_bound J x) (norm_nonneg _)

/-- A deterministic absolute envelope gives an integrable feature coefficient under uniform design. This statement assumes [the hf condition](hyp:hf), [the hb condition](hyp:hb). [This is the stated conclusion](goal). -/
-- @node: integrable_bounded_feature_coefficient
lemma integrable_bounded_feature_coefficient (J : ℕ) (f : unitInterval → ℝ)
    (hf : Measurable f) (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    Integrable (fun x => f x • featureMap J x) design := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  apply integrable_feature_coefficient J f _ hf
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hb x))

/-- The exact single-correction mean is the original mean plus its arm-weighted clipping remainder. This statement assumes [the hv condition](hyp:hv), [the hlaw condition](hyp:hlaw), [the hn condition](hyp:hn), [the hJ condition](hyp:hJ), [the hK condition](hyp:hK), [the hJK condition](hyp:hJK), [the hT0 condition](hyp:hT0). [This is the stated conclusion](goal). -/
-- @node: singleMean_exact
lemma singleMean_exact (v : Params) (hv : v.Valid) (law : ObservedLaw) (hlaw : InModel v law)
    (n J K : ℕ) (hn : 4 ≤ n) (hJ : 0 < J) (hK : 0 < K) (hJK : J ∣ K)
    (b : Bool) (T0 : ℝ) (hT0 : 1 ≤ T0) (c : ℝ) :
    thetaVec law (fun c data => hScore n b J T0 c data-uScore n b J (projKernel K) T0 c data) c =
      origMeanVector law J K c+singleMeanTail law J K T0 := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let μ := Measure.pi (fun _ : Fin n => law.P)
  let q : Record → ℝ := fun o => clipY T0 (Y o)-c*treatment o
  let f : unitInterval → ℝ := fun x => law.m0 x+law.e x*(law.tau x-c)
  let m : unitInterval → ℝ := fun x => law.e x*(law.m0 x+law.tau x-c)
  have hqm : Measurable q := (show Measurable (fun o : Record => clipY T0 (Y o)) from
    (by unfold clipY Y; fun_prop)).sub (measurable_const.mul measurable_treatment)
  have hfm : Measurable f := by dsimp [f]; fun_prop
  have hmm : Measurable m := by dsimp [m]; fun_prop
  have heb (x : unitInterval) : |law.e x| ≤ 1 := by
    rw [abs_of_nonneg (law.e_range x).1]
    exact (law.e_range x).2
  have hfb (x : unitInterval) : |f x| ≤ 1+|c| := by
    dsimp [f]
    calc
      _ ≤ |law.m0 x|+|law.e x| *|law.tau x-c| := by simpa only [abs_mul] using abs_add_le (law.m0 x) (law.e x*(law.tau x-c))
      _ ≤ 1/2+1*(1/2+|c|) := by
        gcongr
        · exact hlaw.baselineCap x
        · exact heb x
        · exact (abs_sub _ _).trans (add_le_add (hlaw.effectCap x) (le_refl _))
      _ = _ := by ring
  have hmb (x : unitInterval) : |m x| ≤ 1+|c| := by
    dsimp [m]
    rw [abs_mul]
    calc
      _ ≤ 1*(1/2+1/2+|c|) := by
        apply mul_le_mul (heb x) _ (abs_nonneg _) (by norm_num)
        exact (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
          (add_le_add (hlaw.baselineCap x) (hlaw.effectCap x))) (le_refl _))
      _ = _ := by ring
  have hfi : Integrable f design := (integrable_const (1+|c|)).mono' hfm.aestronglyMeasurable
    (ae_of_all _ (fun x => by simpa only [Real.norm_eq_abs] using hfb x))
  have htail := integrable_tailRemainder v hv law hlaw T0 hT0
  have hmain := integrable_bounded_feature_coefficient J m hmm (1+|c|) hmb
  have hcor := integrable_projected_tail_feature law J K hK f hfi hfm
  have htc := integrable_projected_tail_feature law J K hK _ htail (measurable_tailRemainder law T0)
  have htrunc := conditional_truncation_moments v hv law hlaw.rawMoment T0 hT0
  have hclip (a : Bool) (x : unitInterval) : Integrable (fun y => clipY T0 y) (law.Q a x) :=
    (clippedOutcome_memLp_top (law.Q a x) T0 (fun y => (x,a,y)) (by fun_prop)).integrable (by norm_num)
  have htreated : Integrable (fun x => law.e x*treatedTailRemainder law T0 x) design := by
    apply (integrable_const (10*T0^(1-v.p))).mono' _ _
    · unfold treatedTailRemainder
      exact (law.e.continuous.measurable.mul
        (show StronglyMeasurable (fun y : ℝ => y-clipY T0 y) from
          (by unfold clipY; fun_prop)).integral_kernel.measurable).aestronglyMeasurable
    · filter_upwards [htrunc true] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (heb x) hx.2.1 (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have htreatm : Measurable (fun x => law.e x*treatedTailRemainder law T0 x) := by
    unfold treatedTailRemainder
    exact law.e.continuous.measurable.mul
      (show StronglyMeasurable (fun y : ℝ => y-clipY T0 y) from
        (by unfold clipY; fun_prop)).integral_kernel.measurable
  have htv := integrable_feature_coefficient J _ htreated htreatm
  have hmark : recordMarkMean law q =ᵐ[design] fun x => f x-tailRemainder law T0 x := by
    filter_upwards [htrunc true, htrunc false, law.mean0_version, law.mean1_version]
      with x h1 h0 hm0 hm1
    have ht1 : (∫ y, y-clipY T0 y ∂law.Q true x) = law.m0 x+law.tau x-(∫ y, clipY T0 y ∂law.Q true x) := by
      rw [integral_sub h1.1 (hclip true x), ← hm1]
    have ht0 : (∫ y, y-clipY T0 y ∂law.Q false x) = law.m0 x-(∫ y, clipY T0 y ∂law.Q false x) := by
      rw [integral_sub h0.1 (hclip false x), ← hm0]
    dsimp [recordMarkMean, q, treatment, A, Y, f, tailRemainder]
    simp only [↓reduceIte, Bool.false_eq_true, mul_one, mul_zero, sub_zero]
    rw [integral_sub (hclip true x) (integrable_const c), integral_const]
    simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul]
    rw [ht1, ht0]
    ring
  have hp (x : unitInterval) : projOp K (recordMarkMean law q) x =
      projOp K f x-projOp K (tailRemainder law T0) x := by
    unfold projOp
    have heq : (fun z => projKernel K x z*recordMarkMean law q z) =ᵐ[design]
        (fun z => projKernel K x z*(f z-tailRemainder law T0 z)) := by
      filter_upwards [hmark] with z hz
      rw [hz]
    rw [integral_congr_ae heq]
    simp only [mul_sub]
    exact integral_sub (integrable_histogram_row_mul K hK x f hfi)
      (integrable_histogram_row_mul K hK x _ htail)
  have hH : (∫ data, hScore n b J T0 c data ∂μ) =
      (∫ x, m x • featureMap J x ∂design)-
        (∫ x, (law.e x*treatedTailRemainder law T0 x) • featureMap J x ∂design) := by
    rw [hScore_mean_record n J b hn law, treated_clipped_feature_integral law hlaw.uniform J T0 c,
      ← integral_sub hmain htv]
    apply integral_congr_ae
    filter_upwards [htrunc true, law.mean1_version] with x h1 hm1
    have ht1 : treatedTailRemainder law T0 x = law.m0 x+law.tau x-(∫ y, clipY T0 y ∂law.Q true x) := by
      unfold treatedTailRemainder
      rw [integral_sub h1.1 (hclip true x), ← hm1]
    rw [ht1]
    dsimp [m]
    module
  have hU : (∫ data, uScore n b J (projKernel K) T0 c data ∂μ) =
      (∫ x, (law.e x*projOp K f x) • featureMap J x ∂design)-
        (∫ x, (law.e x*projOp K (tailRemainder law T0) x) • featureMap J x ∂design) := by
    rw [uScore_mean_record n J K b hn law,
      treated_pair_histogram_integral law hlaw.uniform J K hK q hqm (|T0|+|c|)
        (by positivity) (clipped_mark_bound T0 c), ← integral_sub hcor htc]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    rw [hp]
    module
  have ho : origMeanVector law J K c =
      (∫ x, m x • featureMap J x ∂design)-
        (∫ x, (law.e x*projOp K f x) • featureMap J x ∂design) := by
    rw [histogram_feature_selfAdjoint J K hJ hK hJK law.e f law.e.continuous.measurable hfm
      1 (1+|c|) (by norm_num) (by positivity) heb hfb]
    have hi : Integrable (fun x => (projOp K law.e x*f x) • featureMap J x) design :=
      integrable_bounded_feature_coefficient J _
        ((measurable_projOp K law.e law.e.continuous.measurable).mul hfm)
        ((K:ℝ)*(1+|c|)) (fun x => by
          rw [abs_mul]
          simpa only [mul_one] using mul_le_mul
            (projOp_bound_of_bound K hK law.e 1 (by norm_num) heb x) (hfb x) (abs_nonneg _) (by positivity))
    rw [← integral_sub hmain hi]
    unfold origMeanVector
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp [m, f]
    module
  have hh : Integrable (hScore n b J T0 c) μ := (hScore_memLp_top n J b T0 c μ).integrable (by norm_num)
  have hu : Integrable (uScore n b J (projKernel K) T0 c) μ :=
    (uScore_memLp_top n J b (projKernel K) T0 c μ (fun i j =>
      projKernel_memLp_top μ K _ _ (by unfold X; fun_prop) (by unfold X; fun_prop))).integrable (by norm_num)
  change (∫ data, hScore n b J T0 c data-uScore n b J (projKernel K) T0 c data ∂μ) = _
  rw [integral_sub hh hu, hH, hU, ho]
  simp only [singleMeanTail]
  module

/-- Difference-kernel projection is the difference of its two histogram projections. This statement assumes [the hK condition](hyp:hK), [the hf condition](hyp:hf). [This is the stated conclusion](goal). -/
-- @node: diffKernel_integral_eq_sub
lemma diffKernel_integral_eq_sub (K : ℕ) (hK : 0 < K)
    (f : unitInterval → ℝ) (hf : Integrable f design) (x : unitInterval) :
    (∫ z, diffKernel K x z*f z ∂design) = projOp (2*K) f x-projOp K f x := by
  simp only [diffKernel, sub_mul, projOp]
  exact integral_sub (integrable_histogram_row_mul (2*K) (by omega) x f hf)
    (integrable_histogram_row_mul K hK x f hf)

/-- The exact tail correction on one refinement level is the difference of single-rank tails. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hK condition](hyp:hK), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: singleMeanTail_increment
lemma singleMeanTail_increment (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (J K : ℕ) (hK : 0 < K) (T : ℝ) (hT : 1 ≤ T) :
    singleMeanTail law J (2*K) T-singleMeanTail law J K T =
      ∫ x, (law.e x*(∫ z, diffKernel K x z*tailRemainder law T z ∂design)) •
        featureMap J x ∂design := by
  have hi := integrable_tailRemainder v hv law hm T hT
  simp only [singleMeanTail]
  rw [show ∀ A B C : Vec J, (-A+B)-(-A+C)=B-C by intros; module]
  rw [← integral_sub (integrable_projected_tail_feature law J (2*K) (by omega) _ hi (measurable_tailRemainder law T))
    (integrable_projected_tail_feature law J K hK _ hi (measurable_tailRemainder law T))]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  rw [diffKernel_integral_eq_sub K hK _ hi x, mul_sub, sub_smul]

/-- The ordered-pair score respects the subtraction defining a refinement kernel. [This is the stated conclusion](goal). -/
-- @node: uScore_diffKernel
lemma uScore_diffKernel (n J K : ℕ) (b : Bool) (T c : ℝ) (data : Dataset n) :
    uScore n b J (diffKernel K) T c data =
      uScore n b J (projKernel (2*K)) T c data-uScore n b J (projKernel K) T c data := by
  simp only [uScore, uIntercept, uTreatment, diffKernel]
  by_cases hn : n < 4
  · simp [hn]
  · simp only [if_neg hn, mul_sub, sub_mul, sub_smul, Finset.sum_sub_distrib, smul_sub]
    module

/-- Exact assembly of the truncated multiresolution mean from its original mean and tail remainder. This statement assumes [the hv condition](hyp:hv), [the hlaw condition](hyp:hlaw), [the hn condition](hyp:hn), [the hJ condition](hyp:hJ), [the hT0 condition](hyp:hT0), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
-- @node: multiresMean_exact
lemma multiresMean_exact (v : Params) (hv : v.Valid) (law : ObservedLaw) (hlaw : InModel v law)
    (n J L : ℕ) (hn : 4 ≤ n) (hJ : 0 < J) (b : Bool) (T0 : ℝ) (T : Fin L → ℝ)
    (hT0 : 1 ≤ T0) (hT : ∀ j, 1 ≤ T j) (c : ℝ) :
    thetaVec law (fun c => multiresScore n b J L T0 T c) c =
      origMeanVector law J (2^L*J) c+multiresMeanTail law J L T0 T := by
  let μ := Measure.pi (fun _ : Fin n => law.P)
  have hx (i : Fin n) : Measurable (fun data : Dataset n => X (data i)) := by
    unfold X
    fun_prop
  have hH (t : ℝ) : Integrable (hScore n b J t c) μ :=
    (hScore_memLp_top n J b t c μ).integrable (by norm_num)
  have hU (K : ℕ) (t : ℝ) : Integrable (uScore n b J (projKernel K) t c) μ :=
    (uScore_memLp_top n J b (projKernel K) t c μ
      (fun i j => projKernel_memLp_top μ K _ _ (hx i) (hx j))).integrable (by norm_num)
  have hD (K : ℕ) (t : ℝ) : Integrable (uScore n b J (diffKernel K) t c) μ :=
    (uScore_memLp_top n J b (diffKernel K) t c μ
      (fun i j => diffKernel_memLp_top μ K _ _ (hx i) (hx j))).integrable (by norm_num)
  have hsingle (K : ℕ) (hK : 0 < K) (hJK : J ∣ K) (t : ℝ) (ht : 1 ≤ t) :
      (∫ data, uScore n b J (projKernel K) t c data ∂μ) =
        (∫ data, hScore n b J t c data ∂μ)-
          (origMeanVector law J K c+singleMeanTail law J K t) := by
    have hs := singleMean_exact v hv law hlaw n J K hn hJ hK hJK b t ht c
    change (∫ data, hScore n b J t c data-uScore n b J (projKernel K) t c data ∂μ) = _ at hs
    rw [integral_sub (hH t) (hU K t)] at hs
    rw [← hs]
    module
  have hincr (j : Fin L) :
      (∫ data, uScore n b J (diffKernel (2^j.val*J)) (T j) c data ∂μ) =
      origMeanVector law J (2^j.val*J) c-origMeanVector law J (2^(j.val+1)*J) c-
        (∫ x, (law.e x*(∫ z, diffKernel (2^j.val*J) x z*tailRemainder law (T j) z ∂design)) •
          featureMap J x ∂design) := by
    have hk : 0 < 2^j.val*J := by positivity
    have hk2 : 0 < 2*(2^j.val*J) := by positivity
    have he : 2*(2^j.val*J) = 2^(j.val+1)*J := by ring
    have hu : uScore n b J (diffKernel (2^j.val*J)) (T j) c =
        fun data => uScore n b J (projKernel (2*(2^j.val*J))) (T j) c data-
          uScore n b J (projKernel (2^j.val*J)) (T j) c data := by
      funext data
      exact uScore_diffKernel n J _ b _ c data
    rw [hu, integral_sub (hU _ _) (hU _ _),
      hsingle _ hk2 (by simpa only [mul_assoc] using dvd_mul_left J (2*2^j.val)) _ (hT j),
      hsingle _ hk (dvd_mul_left J _) _ (hT j)]
    have ht := singleMeanTail_increment v hv law hlaw J (2^j.val*J) hk (T j) (hT j)
    rw [he] at ht ⊢
    rw [← ht]
    module
  have htel : (∑ j : Fin L,
      (origMeanVector law J (2^j.val*J) c-origMeanVector law J (2^(j.val+1)*J) c)) =
      origMeanVector law J J c-origMeanVector law J (2^L*J) c := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ =>
      origMeanVector law J (2^j*J) c-origMeanVector law J (2^(j+1)*J) c) L]
    simpa using Finset.sum_range_sub' (fun j => origMeanVector law J (2^j*J) c) L
  change (∫ data, multiresScore n b J L T0 T c data ∂μ) = _
  simp only [multiresScore]
  have hbase : Integrable (fun data => hScore n b J T0 c data-uScore n b J (projKernel J) T0 c data) μ :=
    (hH T0).sub (hU J T0)
  have hsum : Integrable (fun data => ∑ j : Fin L,
      uScore n b J (diffKernel (2^j.val*J)) (T j) c data) μ :=
    integrable_finsetSum _ (fun j _ => hD (2^j.val*J) (T j))
  rw [integral_sub hbase hsum,
    integral_sub (hH T0) (hU J T0),
    integral_finsetSum _ (fun j _ => hD (2^j.val*J) (T j)),
    hsingle J hJ (dvd_refl J) T0 hT0]
  simp_rw [hincr]
  rw [Finset.sum_sub_distrib, htel]
  simp only [singleMeanTail, multiresMeanTail]
  module


end CausalSmith.Stat.FinitepHomogeneityDensegamma
