module
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.MeanErrorBounds
public import CausalSmith.Stat.STAT_FinitepHomogeneityDensegamma_Research.Helpers.ScoreCovariance

/-! Pointwise Hölder and clipping bounds used by the score singleton projections. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace CausalSmith.Stat.FinitepHomogeneityDensegamma

/-- The original conditional affine mean has Hölder increment constant fifty-five at the minimum primitive smoothness. This statement assumes [the hm condition](hyp:hm), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
lemma originalConditionalMean_holder_increment (v : Params) (law : ObservedLaw)
    (hm : InModel v law) (c : ℝ) (hc : |c| ≤ 1/2) (x z : unitInterval) :
    |(law.m0 x+law.e x*(law.tau x-c))-
      (law.m0 z+law.e z*(law.tau z-c))| ≤
      55*|(x:ℝ)-(z:ℝ)|^(min v.α (min v.β v.γ)) := by
  let d := |(x:ℝ)-(z:ℝ)|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hd1 : d ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [x.property.1, x.property.2, z.property.1, z.property.2]
  by_cases hd : d = 0
  · have hxz : x = z := by
      apply Subtype.ext
      exact sub_eq_zero.mp (abs_eq_zero.mp hd)
    subst z
    simp only [sub_self, abs_zero]
    positivity
  have hdp : 0 < d := lt_of_le_of_ne hd0 (Ne.symm hd)
  have hα : d^v.α ≤ d^(min v.α (min v.β v.γ)) :=
    Real.rpow_le_rpow_of_exponent_ge hdp hd1 (min_le_left _ _)
  have hβ : d^v.β ≤ d^(min v.α (min v.β v.γ)) :=
    Real.rpow_le_rpow_of_exponent_ge hdp hd1
      (le_trans (min_le_right _ _) (min_le_left _ _))
  have hγ : d^v.γ ≤ d^(min v.α (min v.β v.γ)) :=
    Real.rpow_le_rpow_of_exponent_ge hdp hd1
      (le_trans (min_le_right _ _) (min_le_right _ _))
  have hm0 := hm.baselineSmooth.2.2 x z
  have he := hm.propensitySmooth.2.2 x z
  have ht := hm.effectSmooth.2.2 x z
  have hecap : |law.e x| ≤ 3/4 := by
    rw [abs_of_nonneg (law.e_range x).1]
    exact (hm.overlap x).2
  have htcap : |law.tau z-c| ≤ 1 := by
    calc
      _ ≤ |law.tau z|+|c| := abs_sub _ _
      _ ≤ 1 := by linarith [hm.effectCap z]
  calc
    _ ≤ |law.m0 x-law.m0 z|+
        |law.e x*(law.tau x-c)-law.e z*(law.tau z-c)| := by
      have hid : (law.m0 x+law.e x*(law.tau x-c))-
          (law.m0 z+law.e z*(law.tau z-c)) =
          (law.m0 x-law.m0 z)+
            (law.e x*(law.tau x-c)-law.e z*(law.tau z-c)) := by ring
      rw [hid]
      exact abs_add_le _ _
    _ ≤ |law.m0 x-law.m0 z|+
        (|law.e x| * |law.tau x-law.tau z|+
          |law.e x-law.e z| * |law.tau z-c|) := by
      gcongr
      calc
        _ = |law.e x*((law.tau x-c)-(law.tau z-c))+
            (law.e x-law.e z)*(law.tau z-c)| := by congr 1; ring
        _ ≤ |law.e x*((law.tau x-c)-(law.tau z-c))|+
            |(law.e x-law.e z)*(law.tau z-c)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]; congr 2; ring
    _ ≤ 20*d^v.β+((3/4)*(20*d^v.γ)+(20*d^v.α)*1) := by
      gcongr
    _ ≤ 55*d^(min v.α (min v.β v.γ)) := by
      nlinarith

/-- Scaling by `20/55` places the affine conditional mean in the radius-twenty Hölder ball. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hc condition](hyp:hc). [This is the stated conclusion](goal). -/
lemma scaledOriginalConditionalMean_holderBall (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (c : ℝ) (hc : |c| ≤ 1/2) :
    holderBall (min v.α (min v.β v.γ))
      (fun x => (20/55)* (law.m0 x+law.e x*(law.tau x-c))) := by
  constructor
  · fun_prop
  constructor
  · intro x
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 20/55)]
    have he : |law.e x| ≤ 3/4 := by
      rw [abs_of_nonneg (law.e_range x).1]
      exact (hm.overlap x).2
    have ht : |law.tau x-c| ≤ 1 :=
      (abs_sub _ _).trans (by linarith [hm.effectCap x])
    have hsum : |law.m0 x+law.e x*(law.tau x-c)| ≤ 5/4 := by
      calc
        _ ≤ |law.m0 x|+|law.e x*(law.tau x-c)| := abs_add_le _ _
        _ ≤ 1/2+(3/4)*1 := by
          rw [abs_mul]
          exact add_le_add (hm.baselineCap x)
            (mul_le_mul he ht (abs_nonneg _) (by positivity))
        _ = 5/4 := by norm_num
    norm_num at ⊢
    linarith
  · intro x z
    rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 20/55)]
    have h := originalConditionalMean_holder_increment v law hm c hc x z
    nlinarith

/-- A dyadic difference applied to the untruncated affine conditional mean has the exact `110 R⁻ˢ` pointwise envelope used in `dLev`. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hc condition](hyp:hc), [the hR condition](hyp:hR). [This is the stated conclusion](goal). -/
lemma diffKernel_originalConditionalMean_bound (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (c : ℝ) (hc : |c| ≤ 1/2)
    (R : ℕ) (hR : 0 < R) (x : unitInterval) :
    |∫ z, diffKernel R x z*(law.m0 z+law.e z*(law.tau z-c)) ∂design| ≤
      110*(R:ℝ)^(-min v.α (min v.β v.γ)) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  let s := min v.α (min v.β v.γ)
  let f : unitInterval → ℝ := fun z => law.m0 z+law.e z*(law.tau z-c)
  let fs : unitInterval → ℝ := fun z => (20/55)*f z
  have hs : 0 < s ∧ s ≤ 1 := by
    dsimp [s]
    constructor
    · exact lt_min hv.2.1.1 (lt_min hv.2.2.1.1 (by linarith [hv.2.2.2.1]))
    · exact (min_le_left _ _).trans hv.2.1.2
  have hfs : holderBall s fs := scaledOriginalConditionalMean_holderBall v hv law hm c hc
  have he1 := projection_holder_error R hR s hs fs hfs x
  have he2 := projection_holder_error (2*R) (by positivity) s hs fs hfs x
  have hrpow : ((2*R:ℕ):ℝ)^(-s) ≤ (R:ℝ)^(-s) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast (show R ≤ 2*R by omega)
    · linarith [hs.1]
  have hdiffs : |projOp (2*R) fs x-projOp R fs x| ≤ 40*(R:ℝ)^(-s) := by
    calc
      _ = |(fs x-projOp R fs x)-(fs x-projOp (2*R) fs x)| := by congr 1; ring
      _ ≤ |fs x-projOp R fs x|+|fs x-projOp (2*R) fs x| := abs_sub _ _
      _ ≤ 20*(R:ℝ)^(-s)+20*((2*R:ℕ):ℝ)^(-s) := add_le_add he1 he2
      _ ≤ 40*(R:ℝ)^(-s) := by nlinarith
  have hscale : (∫ z, diffKernel R x z*f z ∂design) =
      (55/20)*(projOp (2*R) fs x-projOp R fs x) := by
    have hfscale (z : unitInterval) : f z = (55/20)*fs z := by dsimp [fs]; ring
    unfold diffKernel
    simp_rw [hfscale]
    change (∫ z, (projKernel (2*R) x z-projKernel R x z)*((55/20)*fs z) ∂design) =
      (55/20)*((∫ z, projKernel (2*R) x z*fs z ∂design)-
        ∫ z, projKernel R x z*fs z ∂design)
    have hfsLp : MemLp fs ∞ design := by
      apply memLp_top_of_bound hfs.1.measurable.aestronglyMeasurable 20
      exact ae_of_all _ hfs.2.1
    have hfine : Integrable (fun z => projKernel (2*R) x z*fs z) design := by
      have ht := hfsLp.mul (r := ∞)
        (projKernel_memLp_top design (2*R) (fun _ => x) id measurable_const measurable_id)
      exact ht.integrable (by norm_num)
    have hcoarse : Integrable (fun z => projKernel R x z*fs z) design := by
      have ht := hfsLp.mul (r := ∞)
        (projKernel_memLp_top design R (fun _ => x) id measurable_const measurable_id)
      exact ht.integrable (by norm_num)
    calc
      _ = ∫ z, (55/20)*(projKernel (2*R) x z*fs z-
          projKernel R x z*fs z) ∂design := by
            apply integral_congr_ae
            exact ae_of_all _ (fun z => by ring)
      _ = _ := by rw [integral_const_mul, integral_sub hfine hcoarse]
  change |∫ z, diffKernel R x z*f z ∂design| ≤ 110*(R:ℝ)^(-s)
  rw [hscale, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 55/20)]
  norm_num at ⊢
  nlinarith

/-- The clipped-outcome conditional mark is the original conditional mean minus its exact clipping remainder. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT). [This is the stated conclusion](goal). -/
lemma scoreMark_false_mean_ae (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T) :
    recordMarkMean law (scoreMark T false) =ᵐ[design]
      fun x => law.m0 x+law.e x*law.tau x-tailRemainder law T x := by
  have ht := conditional_truncation_moments v hv law hm.rawMoment T hT
  filter_upwards [ht true, ht false, law.mean0_version, law.mean1_version]
    with x hx1 hx0 hm0 hm1
  have hc (a : Bool) : Integrable (fun y => clipY T y) (law.Q a x) := by
    apply (integrable_const T).mono' (by unfold clipY; fun_prop)
    exact ae_of_all _ (fun y => by
      simpa only [Real.norm_eq_abs] using clipY_abs_le T y (by linarith))
  unfold recordMarkMean scoreMark tailRemainder
  simp only [Bool.false_eq_true, ↓reduceIte, Y]
  have hr1 : (∫ y, y-clipY T y ∂law.Q true x) =
      law.m0 x+law.tau x-(∫ y, clipY T y ∂law.Q true x) := by
    rw [integral_sub hx1.1 (hc true), ← hm1]
  have hr0 : (∫ y, y-clipY T y ∂law.Q false x) =
      law.m0 x-(∫ y, clipY T y ∂law.Q false x) := by
    rw [integral_sub hx0.1 (hc false), ← hm0]
  rw [hr1, hr0]
  ring

/-- A dyadic difference of the exact clipping remainder costs twice its armwise tail bound. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT), [the hR condition](hyp:hR). [This is the stated conclusion](goal). -/
lemma diffKernel_tailRemainder_bound (v : Params) (hv : v.Valid) (law : ObservedLaw)
    (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T)
    (R : ℕ) (hR : 0 < R) (x : unitInterval) :
    |∫ z, diffKernel R x z*tailRemainder law T z ∂design| ≤
      20*T^(1-v.p) := by
  have hb := tailRemainder_abs_le v hv law hm T hT
  have hn : 0 ≤ 10*T^(1-v.p) := by positivity
  have h1 := projOp_abs_le_ae_bound R hR (tailRemainder law T)
    (10*T^(1-v.p)) hn hb x
  have h2 := projOp_abs_le_ae_bound (2*R) (by positivity) (tailRemainder law T)
    (10*T^(1-v.p)) hn hb x
  rw [diffKernel_integral_eq_sub R hR _ (integrable_tailRemainder v hv law hm T hT) x]
  exact (abs_sub _ _).trans (by linarith)

/-- Combining smooth and clipping pieces gives exactly the public `dLev` summand. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hT condition](hyp:hT), [the hR condition](hyp:hR). [This is the stated conclusion](goal). -/
lemma diffKernel_scoreMarkMean_false_bound (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law) (T : ℝ) (hT : 1 ≤ T)
    (R : ℕ) (hR : 0 < R) (x : unitInterval) :
    |∫ z, diffKernel R x z*recordMarkMean law (scoreMark T false) z ∂design| ≤
      110*(R:ℝ)^(-min v.α (min v.β v.γ))+20*T^(1-v.p) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have heq := scoreMark_false_mean_ae v hv law hm T hT
  have hreplace : (∫ z, diffKernel R x z*
      recordMarkMean law (scoreMark T false) z ∂design) =
      ∫ z, diffKernel R x z*((law.m0 z+law.e z*law.tau z)-
        tailRemainder law T z) ∂design := by
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
  rw [hreplace]
  have hs := diffKernel_originalConditionalMean_bound v hv law hm 0
    (by norm_num) R hR x
  have ht := diffKernel_tailRemainder_bound v hv law hm T hT R hR x
  let f : unitInterval → ℝ := fun z => law.m0 z+law.e z*law.tau z
  have hf : Integrable f design := by
    apply (integrable_const (2:ℝ)).mono' (by dsimp [f]; fun_prop)
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs]
      calc
        _ ≤ |law.m0 z|+|law.e z*law.tau z| := abs_add_le _ _
        _ ≤ 1/2+1*(1/2) := by
          rw [abs_mul]
          exact add_le_add (hm.baselineCap z)
            (mul_le_mul (by simpa [abs_of_nonneg (law.e_range z).1] using (law.e_range z).2)
              (hm.effectCap z) (abs_nonneg _) (by positivity))
        _ ≤ 2 := by norm_num)
  have hi1 : Integrable (fun z => diffKernel R x z*f z) design := by
    unfold diffKernel
    convert (integrable_histogram_row_mul (2*R) (by positivity) x f hf).sub
      (integrable_histogram_row_mul R hR x f hf) using 1
    funext z
    simp
    ring
  have hi2 : Integrable (fun z => diffKernel R x z*tailRemainder law T z) design := by
    unfold diffKernel
    convert (integrable_histogram_row_mul (2*R) (by positivity) x _
      (integrable_tailRemainder v hv law hm T hT)).sub
      (integrable_histogram_row_mul R hR x _
        (integrable_tailRemainder v hv law hm T hT)) using 1
    funext z
    simp
    ring
  have hid : (∫ z, diffKernel R x z*((law.m0 z+law.e z*law.tau z)-
      tailRemainder law T z) ∂design) =
      (∫ z, diffKernel R x z*(law.m0 z+law.e z*law.tau z) ∂design)-
        ∫ z, diffKernel R x z*tailRemainder law T z ∂design := by
    change (∫ z, diffKernel R x z*(f z-tailRemainder law T z) ∂design) = _
    calc
      _ = ∫ z, diffKernel R x z*f z-
          diffKernel R x z*tailRemainder law T z ∂design := by
            apply integral_congr_ae
            exact ae_of_all _ (fun z => by ring)
      _ = _ := integral_sub hi1 hi2
  rw [hid]
  have hs' : |∫ z, diffKernel R x z*(law.m0 z+law.e z*law.tau z) ∂design| ≤
      110*(R:ℝ)^(-min v.α (min v.β v.γ)) := by simpa using hs
  exact (abs_sub _ _).trans (add_le_add hs' ht)

/-- A dyadic difference applied to the propensity is exactly the public `aLev` envelope. This statement assumes [the hv condition](hyp:hv), [the hm condition](hyp:hm), [the hR condition](hyp:hR). [This is the stated conclusion](goal). -/
lemma diffKernel_propensity_bound (v : Params) (hv : v.Valid)
    (law : ObservedLaw) (hm : InModel v law)
    (R : ℕ) (hR : 0 < R) (x : unitInterval) :
    |∫ z, diffKernel R x z*law.e z ∂design| ≤ 40*(R:ℝ)^(-v.α) := by
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have heint : Integrable law.e design := by
    apply (integrable_const (1 : ℝ)).mono' hm.propensitySmooth.1.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (law.e_range z).1]
      exact (law.e_range z).2)
  rw [diffKernel_integral_eq_sub R hR law.e
    heint x]
  exact propensity_projection_increment_bound v hv law hm R hR x

/-- [the score Mark measurable' statement holds](goal). -/
lemma scoreMark_measurable' (T : ℝ) (r : Bool) : Measurable (scoreMark T r) := by
  unfold scoreMark
  split
  · exact measurable_treatment
  · unfold clipY Y
    fun_prop

/-- Under [the hT condition](hyp:hT), [the score Mark abs le' statement holds](goal). -/
lemma scoreMark_abs_le' (T : ℝ) (hT : 1 ≤ T) (r : Bool) (o : Record) :
    |scoreMark T r o| ≤ T := by
  cases r
  · simpa only [scoreMark, Bool.false_eq_true, ↓reduceIte] using
      clipY_abs_le T (Y o) (by linarith)
  · simp only [scoreMark, ↓reduceIte]
    exact (treatment_abs_le_one o).trans hT

/-- Under [the hu condition](hyp:hu), [the hR condition](hyp:hR), [the hq condition](hyp:hq), [the hC condition](hyp:hC), [the hb condition](hyp:hb), [the diff Kernel record Mark integral statement holds](goal). -/
lemma diffKernel_recordMark_integral (law : ObservedLaw) (hu : UniformDesign law)
    (R : ℕ) (hR : 0 < R) (q : Record → ℝ) (hq : Measurable q)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ o, |q o| ≤ C) (x : unitInterval) :
    (∫ o, diffKernel R x (X o)*q o ∂law.P) =
      ∫ z, diffKernel R x z*recordMarkMean law q z ∂design := by
  unfold diffKernel
  have hqf : Integrable (fun o => projKernel (2*R) x (X o)*q o) law.P := by
    apply (integrable_const (((2*R:ℕ):ℝ)*C)).mono'
      (((measurable_projKernel (2*R)).comp (measurable_const.prodMk measurable_fst)).mul hq).aestronglyMeasurable
    exact ae_of_all _ (fun o => by
      change |projKernel (2*R) x (X o)*q o| ≤ ((2*R:ℕ):ℝ)*C
      rw [abs_mul]
      exact mul_le_mul (histogram_kernel_bounds (2*R) (by positivity) x (X o)).2
        (hb o) (abs_nonneg _) (by positivity))
  have hqc : Integrable (fun o => projKernel R x (X o)*q o) law.P := by
    apply (integrable_const ((R:ℝ)*C)).mono'
      (((measurable_projKernel R).comp (measurable_const.prodMk measurable_fst)).mul hq).aestronglyMeasurable
    exact ae_of_all _ (fun o => by
      change |projKernel R x (X o)*q o| ≤ (R:ℝ)*C
      rw [abs_mul]
      exact mul_le_mul (histogram_kernel_bounds R hR x (X o)).2
        (hb o) (abs_nonneg _) (by positivity))
  rw [show (∫ o, (projKernel (2*R) x (X o)-projKernel R x (X o))*q o ∂law.P) =
      (∫ o, projKernel (2*R) x (X o)*q o ∂law.P)-
       ∫ o, projKernel R x (X o)*q o ∂law.P by
        convert integral_sub hqf hqc using 1 <;> apply integral_congr_ae <;>
          exact ae_of_all _ (fun o => by ring)]
  rw [record_histogram_mark_integral law hu (2*R) (by positivity) x q hq C hC hb,
    record_histogram_mark_integral law hu R hR x q hq C hC hb]
  let f := recordMarkMean law q
  letI : IsProbabilityMeasure design := by unfold design; infer_instance
  have hft : MemLp f ∞ design := memLp_top_of_bound
    (measurable_recordMarkMean law q hq).aestronglyMeasurable C
      (ae_of_all _ (recordMarkMean_bound law q hq C hC hb))
  have hrf : Integrable (fun z => projKernel (2*R) x z*f z) design :=
    by
      convert ((projKernel_memLp_top design (2*R) (fun _ => x) id measurable_const
        measurable_id).mul hft).integrable (by norm_num : (1:ENNReal) ≤ ∞) using 1
      funext z
      simp [mul_comm]
  have hrc : Integrable (fun z => projKernel R x z*f z) design :=
    by
      convert ((projKernel_memLp_top design R (fun _ => x) id measurable_const
        measurable_id).mul hft).integrable (by norm_num : (1:ENNReal) ≤ ∞) using 1
      funext z
      simp [mul_comm]
  unfold projOp
  rw [← integral_sub hrf hrc]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by ring)

/-- Under [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the diff Kernel feature commute statement holds](goal). -/
lemma diffKernel_feature_commute (J R : ℕ) (hJ : 0 < J) (hR : 0 < R) (hJR : J ∣ R)
    (x z : unitInterval) :
    diffKernel R x z • featureMap J x = diffKernel R z x • featureMap J z := by
  unfold diffKernel
  rw [sub_smul, sub_smul,
    histogram_feature_kernel_commute J (2*R) hJ (by positivity) (dvd_mul_of_dvd_right hJR 2) x z,
    histogram_feature_kernel_commute J R hJ hR hJR x z]

/-- Under [the hJ condition](hyp:hJ), [the hR condition](hyp:hR), [the hJR condition](hyp:hJR), [the diff Kernel feature inner commute statement holds](goal). -/
lemma diffKernel_feature_inner_commute (J R : ℕ) (hJ : 0 < J) (hR : 0 < R)
    (hJR : J ∣ R) (u : Vec J) (x z : unitInterval) :
    diffKernel R x z*inner ℝ u (featureMap J x) =
      diffKernel R z x*inner ℝ u (featureMap J z) := by
  have h := congrArg (fun w : Vec J => inner ℝ u w)
    (diffKernel_feature_commute J R hJ hR hJR x z)
  simpa only [inner_smul_right, smul_eq_mul] using h

end CausalSmith.Stat.FinitepHomogeneityDensegamma
