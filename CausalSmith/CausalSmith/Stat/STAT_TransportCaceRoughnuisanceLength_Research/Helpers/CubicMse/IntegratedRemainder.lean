module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.RemainderMoments
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Probability.Moments.Variance

/-! # Spatial integration of the cubic Taylor remainder

Jensen and Fubini turn the clipped pilot eighth moment into the integrated
remainder bound in roadmap (9), without adding regularity assumptions.
-/

public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- A bounded nonnegative majorant controls the square of a spatial integral
by its second moment under a probability measure.  Under [the displayed assumptions and inputs](hyp:X,r,g,C,hg,hb,hr), [the stated conclusion holds](goal). -/
-- @node: sq_integral_le_majorant_second_moment
lemma sq_integral_le_majorant_second_moment
    {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    (r g : X → ℝ) (C : ℝ) (hg : Measurable g)
    (hb : ∀ᵐ x ∂ν, |g x| ≤ C)
    (hr : ∀ᵐ x ∂ν, |r x| ≤ g x) :
    (∫ x, r x ∂ν) ^ 2 ≤ ∫ x, (g x) ^ 2 ∂ν := by
  have hlp : MemLp g 2 ν := MemLp.of_bound hg.aestronglyMeasurable C
    (by simpa only [Real.norm_eq_abs] using hb)
  have habs : |∫ x, r x ∂ν| ≤ ∫ x, g x ∂ν :=
    abs_integral_le_integral_abs.trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (hlp.integrable (by norm_num)) hr)
  have hj := ProbabilityTheory.variance_nonneg g ν
  rw [ProbabilityTheory.variance_eq_sub hlp] at hj
  calc
    _ ≤ (∫ x, g x ∂ν) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ ≤ _ := sub_nonneg.mp hj

/-- Joint measurability and a bounded majorant justify Fubini in the
integrated second-moment estimate.  Under [the displayed assumptions and inputs](hyp:Ω,X,r,g,C,B,hg,hb,hr,hmoment), [the stated conclusion holds](goal). -/
-- @node: integrated_second_moment_le_of_majorant
lemma integrated_second_moment_le_of_majorant
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (r g : Ω → X → ℝ) (C B : ℝ)
    (hg : Measurable (Function.uncurry g))
    (hb : ∀ ω, ∀ᵐ x ∂ν, |g ω x| ≤ C)
    (hr : ∀ ω, ∀ᵐ x ∂ν, |r ω x| ≤ g ω x)
    (hmoment : ∀ᵐ x ∂ν, (∫ ω, (g ω x) ^ 2 ∂μ) ≤ B) :
    (∫ ω, (∫ x, r ω x ∂ν) ^ 2 ∂μ) ≤ B := by
  have hi : Integrable (fun p : Ω × X => (g p.1 p.2) ^ 2) (μ.prod ν) := by
    apply Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable (C ^ 2)
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le (hg.pow_const 2).norm measurable_const)]
    filter_upwards [] with ω
    filter_upwards [hb ω] with x hx
    simpa only [Function.uncurry, Real.norm_eq_abs, abs_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hx 2
  calc
    _ ≤ ∫ ω, ∫ x, (g ω x) ^ 2 ∂ν ∂μ := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => sq_nonneg _) hi.integral_prod_left
      filter_upwards [] with ω
      exact sq_integral_le_majorant_second_moment ν (r ω) (g ω) C
        (hg.comp (measurable_const.prodMk measurable_id)) (hb ω) (hr ω)
    _ = ∫ x, ∫ ω, (g ω x) ^ 2 ∂μ ∂ν := integral_integral_swap hi
    _ ≤ ∫ _x, B ∂ν := integral_mono_ae hi.integral_prod_right (integrable_const B) hmoment
    _ = B := by simp

/-- The histogram is jointly measurable in the sample and covariate.  Under [the displayed assumptions and inputs](hyp:n,i,K,b), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: measurable_markedHistogram_joint
lemma measurable_markedHistogram_joint {n : ℕ} (i : Fin 7) (K : ℕ) (b : Fin 4) :
    Measurable (fun p : TwoSample n n × ℝ => markedHistogram p.1 i K b p.2) := by
  classical
  unfold markedHistogram
  split_ifs
  · fun_prop
  · apply Finset.measurable_sum
    intro l hl
    apply Measurable.ite ((measurableSet_cell K l).preimage measurable_snd)
    · apply Measurable.const_mul
      apply Finset.measurable_sum
      intro r hr
      apply Measurable.mul ((measurable_channelMark i r).comp measurable_fst)
      exact Measurable.ite ((measurableSet_cell K l).preimage
        ((measurable_channelX i r).comp measurable_fst)) measurable_const measurable_const
    · fun_prop

/-- Clipping preserves joint measurability of the pilot.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,n,i), [the stated conclusion holds](goal). -/
@[fun_prop]
-- @node: measurable_pilot_joint
lemma measurable_pilot_joint (c_f C_f : ℝ) {n : ℕ} (i : Fin 7) :
    Measurable (fun p : TwoSample n n × ℝ => pilot c_f C_f p.1 p.2 i) := by
  classical
  unfold pilot
  split_ifs
  · fun_prop
  · unfold clipChannel clip
    dsimp only
    split_ifs <;> fun_prop

/-- The true marked density, extended by zero outside its covariate domain,
is measurable; continuity on that domain provides this regularity.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP,i), [the stated conclusion holds](goal). -/
-- @node: measurable_markedDensityVector_indicator
lemma measurable_markedDensityVector_indicator (c_f C_f L : ℝ)
    (P : TransportLaw) (n : ℕ) (hP : ModelClass c_f C_f L P n) (i : Fin 7) :
    Measurable (covariateSpace.indicator
      (fun x => markedDensityVector c_f C_f L P n hP x i)) := by
  classical
  exact (markedDensityVector_continuousOn c_f C_f L P n hP i).measurable_piecewise
    continuousOn_const measurableSet_Icc

/-- Roadmap (9): the expected square of the spatially integrated exact
cubic Taylor remainder is bounded by the clipped pilot eighth moment.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: pilot_Phi_cubic_taylor_remainder_integrated_second_moment
lemma pilot_Phi_cubic_taylor_remainder_integrated_second_moment
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool) :
    (∫ ω, (∫ x in covariateSpace,
      (let v := pilot c_f C_f ω x
       let h := markedDensityVector c_f C_f L P n hP x - v
       Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
         iteratedFDeriv ℝ 1 (Phi A) v ![h] +
         iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
         iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6))) ^ 2 ∂dataLaw P n n) ≤
      (fourthDerivativeEnvelope c_f C_f / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) *
        pilotEighthConstant C_f L * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
  classical
  let μ := dataLaw P n n
  let ν := volume.restrict covariateSpace
  let : IsProbabilityMeasure (sourceObsLaw P) :=
    sourceObsLaw_isProbabilityMeasure c_f C_f L P n hP
  let : IsProbabilityMeasure (targetXLaw P) :=
    targetXLaw_isProbabilityMeasure c_f C_f L P n hP
  have hprob : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [dataLaw_eq_source_target_pi c_f C_f L P n hP]
    infer_instance
  let := hprob
  have hvol : IsProbabilityMeasure ν := ⟨by simp [ν, covariateSpace]⟩
  let := hvol
  let F (x : ℝ) (i : Fin 7) := covariateSpace.indicator
    (fun y => markedDensityVector c_f C_f L P n hP y i) x
  let e (ω : TwoSample n n) (x : ℝ) (i : Fin 7) := pilot c_f C_f ω x i - F x i
  let M := fourthDerivativeEnvelope c_f C_f / 24
  let g (ω : TwoSample n n) (x : ℝ) := M * (∑ i : Fin 7, |e ω x i|) ^ 4
  let r (ω : TwoSample n n) (x : ℝ) :=
    let v := pilot c_f C_f ω x
    let h := markedDensityVector c_f C_f L P n hP x - v
    Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
      iteratedFDeriv ℝ 1 (Phi A) v ![h] +
      iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
      iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6)
  have hc := hP.sourceBounds.1.1
  have hC : 0 ≤ C_f := le_trans (by norm_num) hP.sourceBounds.2.1.le
  have hM : 0 ≤ M := by dsimp [M, fourthDerivativeEnvelope]; positivity
  have he_meas (i : Fin 7) :
      Measurable (fun p : TwoSample n n × ℝ => e p.1 p.2 i) :=
    (measurable_pilot_joint c_f C_f i).sub
      ((measurable_markedDensityVector_indicator c_f C_f L P n hP i).comp measurable_snd)
  have hg : Measurable (Function.uncurry g) := by
    dsimp [g, Function.uncurry]
    fun_prop
  have he_bound (ω : TwoSample n n) (x : ℝ) (hx : x ∈ covariateSpace)
      (i : Fin 7) : |e ω x i| ≤ 2 * C_f := by
    dsimp [e, F]
    rw [Set.indicator_of_mem hx]
    simpa only [two_mul] using (abs_sub _ _).trans (add_le_add
      (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
        (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) i)
      (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
        (markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx) i))
  have hbound (ω : TwoSample n n) : ∀ᵐ x ∂ν,
      |g ω x| ≤ M * (14 * C_f) ^ 4 := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    have hs : (∑ i : Fin 7, |e ω x i|) ≤ 14 * C_f := by
      calc
        _ ≤ ∑ _i : Fin 7, 2 * C_f := Finset.sum_le_sum fun i _ => he_bound ω x hx i
        _ = _ := by simp; ring
    dsimp [g]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hs 4) hM
  have hr (ω : TwoSample n n) : ∀ᵐ x ∂ν, |r ω x| ≤ g ω x := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    have ht := pilot_Phi_cubic_taylor_remainder_abs_le c_f C_f L P n hn hP A ω x hx
    simpa [r, g, M, e, F, hx, Pi.sub_apply, abs_sub_comm] using ht
  have hmoment : ∀ᵐ x ∂ν, (∫ ω, (g ω x) ^ 2 ∂μ) ≤
      M ^ 2 * (7 : ℝ) ^ (8 : ℕ) * pilotEighthConstant C_f L *
        (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    have hi (i : Fin 7) : Integrable (fun ω => |e ω x i| ^ (8 : ℕ)) μ := by
      simpa [e, F, hx, μ] using
        integrable_pilot_error_eighth c_f C_f L P n hn hP x hx i
    calc
      _ ≤ ∫ ω, (M ^ 2 * (7 : ℝ) ^ (7 : ℕ)) *
          ∑ i : Fin 7, |e ω x i| ^ (8 : ℕ) ∂μ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
          ((integrable_finsetSum Finset.univ (fun i _ => hi i)).const_mul _)
        filter_upwards [] with ω
        dsimp only [g]
        rw [mul_pow, ← pow_mul]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (sum_abs_eighth_le (e ω x)) (sq_nonneg _)
      _ = (M ^ 2 * (7 : ℝ) ^ (7 : ℕ)) *
          ∑ i : Fin 7, ∫ ω, |e ω x i| ^ (8 : ℕ) ∂μ := by
        rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hi i)]
      _ ≤ (M ^ 2 * (7 : ℝ) ^ (7 : ℕ)) *
          ∑ _i : Fin 7, pilotEighthConstant C_f L * (n : ℝ) ^ (-(4 / 5 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro i _
        simpa [e, F, hx, μ] using
          pilot_eighth_moment c_f C_f L P n hn hP i x hx
      _ = _ := by simp; ring
  exact integrated_second_moment_le_of_majorant μ ν r g
    (M * (14 * C_f) ^ 4) _ hg hbound hr hmoment

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
