module
public import CausalSmith.Stat.STAT_TransportCaceRoughnuisanceLength_Research.Helpers.CubicMse.IntegratedRemainder

/-! # Integrable majorant for the integrated Taylor remainder

The nonnegative fourth-order pilot-error envelope has an integrable square
and the exact BR bound. This permits combining bias components without
assuming measurability or integrability of their Taylor representations.
-/

@[expose] public section

open MeasureTheory Set
namespace CausalSmith.Stat.TransportCaceRoughnuisanceLength

/-- The spatial integral of the fourth-order Taylor remainder envelope.  For [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hP), [the stated object is defined](goal). -/
-- @node: pilotRemainderMajorant
noncomputable def pilotRemainderMajorant (c_f C_f L : ℝ) (P : TransportLaw)
    (n : ℕ) (hP : ModelClass c_f C_f L P n) (ω : TwoSample n n) : ℝ :=
  ∫ x in covariateSpace, (fourthDerivativeEnvelope c_f C_f / 24) *
    (∑ i : Fin 7, |pilot c_f C_f ω x i -
      markedDensityVector c_f C_f L P n hP x i|) ^ 4

/-- Clipping and the eighth pilot moment give an integrable squared
remainder envelope and the exact second-moment constant BR.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP), [the stated conclusion holds](goal). -/
-- @node: pilotRemainderMajorant_integrable_sq_and_moment
lemma pilotRemainderMajorant_integrable_sq_and_moment
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) :
    Integrable (fun ω => pilotRemainderMajorant c_f C_f L P n hP ω ^ 2)
      (dataLaw P n n) ∧
    (∫ ω, pilotRemainderMajorant c_f C_f L P n hP ω ^ 2 ∂dataLaw P n n) ≤
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
  have hnonneg (ω : TwoSample n n) : ∀ᵐ x ∂ν, 0 ≤ g ω x := by
    filter_upwards [] with x
    dsimp [g]
    positivity
  have hr (ω : TwoSample n n) : ∀ᵐ x ∂ν, |g ω x| ≤ g ω x := by
    filter_upwards [hnonneg ω] with x hx
    rw [abs_of_nonneg hx]
  have hm := integrated_second_moment_le_of_majorant μ ν g g
    (M * (14 * C_f) ^ 4) _ hg hbound hr hmoment
  have heq (ω : TwoSample n n) :
      pilotRemainderMajorant c_f C_f L P n hP ω = ∫ x, g ω x ∂ν := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    simp [g, M, e, F, hx]
  have hi : Integrable (fun ω => (∫ x, g ω x ∂ν) ^ 2) μ := by
    apply Integrable.of_bound
      (hg.stronglyMeasurable.integral_prod_right.pow 2).aestronglyMeasurable
      ((M * (14 * C_f) ^ 4) ^ 2)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have habs : |∫ x, g ω x ∂ν| ≤ M * (14 * C_f) ^ 4 :=
      (abs_integral_le_integral_abs.trans
        (integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => abs_nonneg _)
          (integrable_const _) (hbound ω))).trans_eq (by simp)
    simpa only [sq_abs, Pi.pow_apply] using pow_le_pow_left₀ (abs_nonneg _) habs 2
  constructor
  · simpa only [← heq] using hi
  · simpa only [← heq] using hm

/-- The exact spatial Taylor remainder is dominated by its nonnegative,
integrable spatial envelope.  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP,A), [the stated conclusion holds](goal). -/
-- @node: pilot_remainder_integral_abs_le_majorant
lemma pilot_remainder_integral_abs_le_majorant
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) (A : Bool)
    (ω : TwoSample n n) :
    |∫ x in covariateSpace,
      (let v := pilot c_f C_f ω x
       let h := markedDensityVector c_f C_f L P n hP x - v
       Phi A (markedDensityVector c_f C_f L P n hP x) - (Phi A v +
         iteratedFDeriv ℝ 1 (Phi A) v ![h] +
         iteratedFDeriv ℝ 2 (Phi A) v ![h, h] / 2 +
         iteratedFDeriv ℝ 3 (Phi A) v ![h, h, h] / 6))| ≤
      pilotRemainderMajorant c_f C_f L P n hP ω := by
  let ν := volume.restrict covariateSpace
  let : IsProbabilityMeasure ν := ⟨by simp [ν, covariateSpace]⟩
  let F (x : ℝ) (i : Fin 7) := covariateSpace.indicator
    (fun y => markedDensityVector c_f C_f L P n hP y i) x
  let g (x : ℝ) := (fourthDerivativeEnvelope c_f C_f / 24) *
    (∑ i : Fin 7, |pilot c_f C_f ω x i - F x i|) ^ 4
  have hc := hP.sourceBounds.1.1
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hM : 0 ≤ fourthDerivativeEnvelope c_f C_f / 24 := by
    unfold fourthDerivativeEnvelope
    positivity
  have hF (i : Fin 7) : Measurable (fun x => F x i) :=
    measurable_markedDensityVector_indicator c_f C_f L P n hP i
  have hg : Measurable g := by
    dsimp [g]
    fun_prop
  have hb : ∀ᵐ x ∂ν, |g x| ≤
      (fourthDerivativeEnvelope c_f C_f / 24) * (14 * C_f) ^ 4 := by
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    have he (i : Fin 7) : |pilot c_f C_f ω x i - F x i| ≤ 2 * C_f := by
      dsimp [F]
      rw [Set.indicator_of_mem hx]
      simpa only [two_mul] using (abs_sub _ _).trans (add_le_add
        (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
          (pilot_mem_clippingRectangle c_f C_f L P n hn hP ω x) i)
        (clippingRectangle_coordinate_abs_le c_f C_f hc hC _
          (markedDensityVector_mem_clippingRectangle c_f C_f L P n hP x hx) i))
    have hs : (∑ i : Fin 7, |pilot c_f C_f ω x i - F x i|) ≤ 14 * C_f := by
      calc
        _ ≤ ∑ _i : Fin 7, 2 * C_f := Finset.sum_le_sum fun i _ => he i
        _ = _ := by simp; ring
    dsimp [g]
    rw [abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => abs_nonneg _) hs 4) hM
  have hi : Integrable g ν := Integrable.of_bound hg.aestronglyMeasurable _
    (by simpa only [Real.norm_eq_abs] using hb)
  have heq : (∫ x, g x ∂ν) = pilotRemainderMajorant c_f C_f L P n hP ω := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    change x ∈ covariateSpace at hx
    simp [g, F, hx]
  rw [← heq]
  apply abs_integral_le_integral_abs.trans
    (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => abs_nonneg _) hi _)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro x hx
  change x ∈ covariateSpace at hx
  simpa [g, F, hx, abs_sub_comm] using
    pilot_Phi_cubic_taylor_remainder_abs_le c_f C_f L P n hn hP A ω x hx

/-- The remainder envelope has the common n^(-2/3) rate needed in (14).  Under [the displayed assumptions and inputs](hyp:c_f,C_f,L,P,n,hn,hP), [the stated conclusion holds](goal). -/
-- @node: pilotRemainderMajorant_sample_rate
lemma pilotRemainderMajorant_sample_rate
    (c_f C_f L : ℝ) (P : TransportLaw) (n : ℕ)
    (hn : threshold ≤ n) (hP : ModelClass c_f C_f L P n) :
    (∫ ω, pilotRemainderMajorant c_f C_f L P n hP ω ^ 2 ∂dataLaw P n n) ≤
      ((fourthDerivativeEnvelope c_f C_f / 24) ^ 2 * (7 : ℝ) ^ (8 : ℕ) *
        pilotEighthConstant C_f L) * (n : ℝ) ^ (-(2 / 3 : ℝ)) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show 1 ≤ n by norm_num [threshold] at hn; omega)
  have hC : 0 ≤ C_f := hP.sourceBounds.2.1.le.trans' (by norm_num)
  have hA8 : 0 ≤ pilotEighthConstant C_f L := by
    unfold pilotEighthConstant
    positivity
  exact (pilotRemainderMajorant_integrable_sq_and_moment c_f C_f L P n hn hP).2.trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)) (by positivity))

end CausalSmith.Stat.TransportCaceRoughnuisanceLength
