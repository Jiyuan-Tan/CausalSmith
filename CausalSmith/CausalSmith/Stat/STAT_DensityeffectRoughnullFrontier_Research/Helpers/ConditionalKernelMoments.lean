module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CellAverageContraction
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ResidualSecondMoment

/-! Conditional full-overlap second moments for the multiband and triple kernels.
The residual estimate is applied to a covariate-dependent test before integrating
exact squared-kernel masses, as in (7) and (14) of the covariance roadmap. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- Conditional outcome integration preserves measurability of a scalar score. -/
-- @node: measurable_armOutcomeMean
@[fun_prop] lemma measurable_armOutcomeMean (P : ObsLaw) (g : Omega → ℝ)
    (hg : Measurable g) : Measurable (armOutcomeMean P g) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  unfold armOutcomeMean
  apply Finset.measurable_sum
  intro a _
  have hm : Measurable (fun z : ℝ × ℝ =>
      (pi P a z.1 * P.eta a z.1 z.2) * g (z.1, a, z.2)) := by
    have hp : Measurable (pi P a) := by
      cases a
      · exact measurable_const.sub P.e_measurable
      · exact P.e_measurable
    exact ((hp.comp measurable_fst).mul (P.eta_measurable a)).mul
      (hg.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Squared residual tests have nonnegative conditional moments on the design support. -/
-- @node: armOutcomeMean_Vres_sq_nonneg
lemma armOutcomeMean_Vres_sq_nonneg {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) (f : Hj J) :
    0 ≤ armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x := by
  rw [armOutcomeMean_Vres_sq]
  apply mul_nonneg
  · exact div_nonneg (by linarith [(model_pi_mem_Icc P hModel a x hx).1]) (sq_nonneg _)
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_nonneg (P.eta_nonneg a x y hx hy) (sq_nonneg _)

/-- Covariate-dependent conditional residual moments are integrable under an integrable
squared test envelope; this justifies their subsequent observed-law transport. -/
-- @node: integrable_armOutcomeMean_Vres_sq_test
lemma integrable_armOutcomeMean_Vres_sq_test {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (v : ℝ → Hj J)
    (hv : StronglyMeasurable v) (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume)
    (a : Bool) :
    Integrable (fun x => armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my J a o) (v x)) ^ 2) x) unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hm : Measurable (fun o => (inner ℝ (Vres train mx my J a o) (v (X o))) ^ 2) := by
    have hvm : Measurable v := hv.measurable
    exact (((continuous_fst.inner continuous_snd).measurable).comp
      ((measurable_Vres train mx my J a).prodMk (hvm.comp measurable_fst))).pow_const 2
  have he : (fun x => armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my J a o) (v x)) ^ 2) x) =
      armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) (v (X o))) ^ 2) := by
    funext x
    rfl
  have hmom : AEStronglyMeasurable (fun x => armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my J a o) (v x)) ^ 2) x) unitVolume := by
    rw [he]
    exact (measurable_armOutcomeMean P _ hm).aestronglyMeasurable
  apply (hv2.const_mul 4096).mono' hmom
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg
    (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx (v x))]
  exact armOutcomeMean_Vres_sq_le P hModel train mx my J hJ a x hx (v x)

/-- Integrating a covariate-dependent squared residual test costs only its design energy. -/
-- @node: integral_armOutcomeMean_Vres_sq_le
lemma integral_armOutcomeMean_Vres_sq_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (v : ℝ → Hj J)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) (a : Bool) :
    (∫ x, armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my J a o) (v x)) ^ 2) x ∂unitVolume) ≤
      4096 * ∫ x, ‖v x‖ ^ 2 ∂unitVolume := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx (v x)
  · exact hv2.const_mul 4096
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact armOutcomeMean_Vres_sq_le P hModel train mx my J hJ a x hx (v x)

/-- The full multiband overlap has the exact rank-weighted budget with no band-count loss. -/
-- @node: conditional_multiband_full_overlap_le
lemma conditional_multiband_full_overlap_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (a : Bool) (f : Hj (2 ^ T * L)) :
    (∫ x, ∫ z, 9 * armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my (2 ^ T * L) a o)
        (∑ t ∈ Finset.range (T + 1),
          covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f)) ^ 2) z
      ∂unitVolume ∂unitVolume) ≤
      36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hJ : 0 < 2 ^ T * L := by positivity
  have he (x z : ℝ) :
      ‖∑ t ∈ Finset.range (T + 1),
        covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2 =
      ∑ t ∈ Finset.range (T + 1), (covariateKernel (kt t) x z) ^ 2 *
        ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    simp_rw [← Qband_smul]
    rw [band_remainder_sum_norm_sq L T hL _
      (fun t ht => by have := Finset.mem_range.mp ht; omega)]
    simp only [Qband_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hb (x : ℝ) :
      (∫ z, 9 * armOutcomeMean P
        (fun o => (inner ℝ (Vres train mx my (2 ^ T * L) a o)
          (∑ t ∈ Finset.range (T + 1),
            covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f)) ^ 2) z ∂unitVolume) ≤
      36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
    rw [integral_const_mul]
    have hi : Integrable (fun z =>
        ‖∑ t ∈ Finset.range (T + 1),
          covariateKernel (kt t) x z • Qband L (2 ^ T * L) t f‖ ^ 2) unitVolume := by
      simp_rw [he]
      exact integrable_finsetSum _ (fun t _ =>
        (integrable_covariateKernel_sq (kt t) x).mul_const _)
    have h := integral_armOutcomeMean_Vres_sq_le P hModel train mx my
      (2 ^ T * L) hJ _ hi a
    simp_rw [he] at h
    rw [integral_finsetSum _ (fun t _ =>
      (integrable_covariateKernel_sq (kt t) x).mul_const _)] at h
    simp_rw [integral_mul_const] at h
    have hr (t : ℕ) (ht : t ∈ Finset.range (T + 1)) :=
      integral_covariateKernel_sq (kt t) (hkt t (by have := Finset.mem_range.mp ht; omega)) x
    have hsum : (∑ t ∈ Finset.range (T + 1),
        (∫ z, (covariateKernel (kt t) x z) ^ 2 ∂unitVolume) *
          ‖Qband L (2 ^ T * L) t f‖ ^ 2) =
        ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hr t ht]
    rw [hsum] at h
    nlinarith
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  calc
    _ ≤ ∫ _ : ℝ, 36864 * ∑ t ∈ Finset.range (T + 1),
        (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun x => integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
          exact mul_nonneg (by norm_num)
            (armOutcomeMean_Vres_sq_nonneg P hModel train mx my _ a z hz _)))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hb
    _ = _ := by simp

/-- A nonnegative design weight can be integrated after the conditional residual bound. -/
-- @node: integral_weighted_armOutcomeMean_Vres_sq_le
lemma integral_weighted_armOutcomeMean_Vres_sq_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool) (f : Hj J)
    (w : ℝ → ℝ) (hw : Integrable w unitVolume) (hw0 : ∀ᵐ x ∂unitVolume, 0 ≤ w x) :
    (∫ x, w x * armOutcomeMean P
      (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x ∂unitVolume) ≤
      (4096 * ‖f‖ ^ 2) * ∫ x, w x ∂unitVolume := by
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg
  · filter_upwards [hw0, ae_restrict_mem measurableSet_Icc] with x hwx hx
    exact mul_nonneg hwx
      (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx f)
  · exact hw.const_mul _
  · filter_upwards [hw0, ae_restrict_mem measurableSet_Icc] with x hwx hx
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (armOutcomeMean_Vres_sq_le P hModel train mx my J hJ a x hx f) hwx

/-- The full triple overlap integrates both squared kernels to q squared, as in (14). -/
-- @node: conditional_third_full_overlap_le
lemma conditional_third_full_overlap_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ x, ∫ z, ∫ w, 81 * (covariateKernel q x z) ^ 2 * (covariateKernel q z w) ^ 2 *
      armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) w
      ∂unitVolume ∂unitVolume ∂unitVolume) ≤
      331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hrow (z : ℝ) := integral_weighted_armOutcomeMean_Vres_sq_le
    P hModel train mx my J hJ a f (fun w => (covariateKernel q z w) ^ 2)
    (integrable_covariateKernel_sq q z) (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  simp_rw [integral_covariateKernel_sq q hq] at hrow
  have hz (x : ℝ) :
      (∫ z, ∫ w, 81 * (covariateKernel q x z) ^ 2 * (covariateKernel q z w) ^ 2 *
        armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) w
        ∂unitVolume ∂unitVolume) ≤ 331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 := by
    have he (z : ℝ) :
        (∫ w, 81 * (covariateKernel q x z) ^ 2 * (covariateKernel q z w) ^ 2 *
          armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) w
          ∂unitVolume) ≤ (81 * (4096 * ‖f‖ ^ 2) * q) * (covariateKernel q x z) ^ 2 := by
      simp_rw [mul_assoc (81 * (covariateKernel q x z) ^ 2)]
      rw [integral_const_mul]
      have h := mul_le_mul_of_nonneg_left (hrow z)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 81) (sq_nonneg (covariateKernel q x z)))
      exact h.trans_eq (by ring)
    calc
      _ ≤ ∫ z, (81 * (4096 * ‖f‖ ^ 2) * q) * (covariateKernel q x z) ^ 2
          ∂unitVolume := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun z => integral_nonneg_of_ae (by
            filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
            exact mul_nonneg (by positivity)
              (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a w hw f)))
        · exact (integrable_covariateKernel_sq q x).const_mul _
        · exact Filter.Eventually.of_forall he
      _ = _ := by rw [integral_const_mul, integral_covariateKernel_sq q hq]; ring
  calc
    _ ≤ ∫ _ : ℝ, 331776 * (q : ℝ) ^ 2 * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun x => integral_nonneg_of_ae (by
          filter_upwards [] with z
          apply integral_nonneg_of_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
          exact mul_nonneg (by positivity)
            (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a w hw f)))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hz
    _ = _ := by simp

/-- The outcome singleton in (10) has second moment at most 65536 times test energy. -/
-- @node: conditional_third_outcome_singleton_le
lemma conditional_third_outcome_singleton_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ x, (cellAverage q (uerr P train mx a) x) ^ 4 *
      armOutcomeMean P (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x
      ∂unitVolume) ≤ 65536 * ‖f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hb (x : ℝ) : (cellAverage q (uerr P train mx a) x) ^ 4 ≤ 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (cellAverage_abs_le q hq _ 2 hu x) 4
    have ha : |cellAverage q (uerr P train mx a) x| ^ 4 =
        (cellAverage q (uerr P train mx a) x) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    rw [ha] at h
    norm_num only at h
    exact h
  calc
    _ ≤ ∫ _ : ℝ, 65536 * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact mul_nonneg (by positivity)
          (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx f)
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        have hn := armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx f
        have hmom := armOutcomeMean_Vres_sq_le P hModel train mx my J hJ a x hx f
        calc
          _ ≤ 16 * armOutcomeMean P
              (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) x :=
            mul_le_mul_of_nonneg_right (hb x) hn
          _ ≤ 16 * (4096 * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left hmom (by norm_num)
          _ = _ := by ring
    _ = _ := by simp

/-- A cell-averaged vector's scalar test contracts under the uniform design. -/
-- @node: integral_cellAverage_inner_sq_le
lemma integral_cellAverage_inner_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (q : ℕ) (hq : 0 < q) (v : ℝ → E)
    (hv : Integrable v unitVolume) (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume)
    (f : E) :
    (∫ x, (inner ℝ (cellAverage q v x) f) ^ 2 ∂unitVolume) ≤
      (∫ x, ‖v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
  have hb (x : ℝ) : (inner ℝ (cellAverage q v x) f) ^ 2 ≤
      ‖cellAverage q v x‖ ^ 2 * ‖f‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (cellAverage q v x) f
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
  calc
    _ ≤ ∫ x, ‖cellAverage q v x‖ ^ 2 * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact (integrable_cellAverage_norm_sq q hq v).mul_const _
      · exact Filter.Eventually.of_forall hb
    _ = (∫ x, ‖cellAverage q v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (integral_cellAverage_norm_sq_le q hq v hv hv2) (sq_nonneg _)

/-- The treatment singleton in (10) costs 36 times the original vector energy.
Taking that energy at most 900 yields the roadmap's constant 32400. -/
-- @node: conditional_third_treatment_singleton_le
lemma conditional_third_treatment_singleton_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx q : ℕ) (hq : 0 < q) (a : Bool)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : ℝ → E) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) (f : E) :
    (∫ x, 9 * (cellAverage q (uerr P train mx a) x) ^ 2 *
      (inner ℝ (cellAverage q v x) f) ^ 2 ∂unitVolume) ≤
      36 * (∫ x, ‖v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hb (x : ℝ) : (cellAverage q (uerr P train mx a) x) ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
      (cellAverage_abs_le q hq _ 2 hu x)
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hn (x : ℝ) : (inner ℝ (cellAverage q v x) f) ^ 2 ≤
      ‖cellAverage q v x‖ ^ 2 * ‖f‖ ^ 2 := by
    have h := norm_inner_le_norm (𝕜 := ℝ) (cellAverage q v x) f
    rw [Real.norm_eq_abs] at h
    simpa only [sq_abs, mul_pow] using
      (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 h
  calc
    _ ≤ ∫ x, 36 * (‖cellAverage q v x‖ ^ 2 * ‖f‖ ^ 2) ∂unitVolume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun x => by positivity)
      · exact ((integrable_cellAverage_norm_sq q hq v).mul_const _).const_mul _
      · filter_upwards [] with x
        calc
          _ ≤ 36 * (inner ℝ (cellAverage q v x) f) ^ 2 := by
            nlinarith [mul_le_mul_of_nonneg_right (hb x)
              (sq_nonneg (inner ℝ (cellAverage q v x) f))]
          _ ≤ _ := mul_le_mul_of_nonneg_left (hn x) (by norm_num)
    _ = 36 * (∫ x, ‖cellAverage q v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
      rw [integral_const_mul, integral_mul_const]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (integral_cellAverage_norm_sq_le q hq v hv hv2)
        (by norm_num)) (sq_nonneg _)

/-- The pair {1,2} in (12) costs 81q times vector energy after integrating its kernel row. -/
-- @node: conditional_third_treatment_pair_le
lemma conditional_third_treatment_pair_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (q : ℕ) (hq : 0 < q) (v : ℝ → E)
    (hv : Integrable v unitVolume) (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume)
    (f : E) :
    (∫ z, ∫ x, 81 * (covariateKernel q x z) ^ 2 *
      (inner ℝ (cellAverage q v z) f) ^ 2 ∂unitVolume ∂unitVolume) ≤
      81 * q * (∫ x, ‖v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
  have he (z : ℝ) : (∫ x, 81 * (covariateKernel q x z) ^ 2 *
      (inner ℝ (cellAverage q v z) f) ^ 2 ∂unitVolume) =
      (81 * q) * (inner ℝ (cellAverage q v z) f) ^ 2 := by
    rw [integral_mul_const, integral_const_mul]
    have hs (x : ℝ) : covariateKernel q x z = covariateKernel q z x := by
      simp only [covariateKernel, eq_comm]
    simp_rw [hs]
    rw [integral_covariateKernel_sq q hq]
  simp_rw [he]
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (integral_cellAverage_inner_sq_le q hq v hv hv2 f)
    (by positivity : (0 : ℝ) ≤ 81 * q)
  exact h.trans_eq (by ring)

/-- Both outcome-containing pair projections in (12) have the uniform 147456q budget. -/
-- @node: conditional_third_outcome_pair_le
lemma conditional_third_outcome_pair_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ x, ∫ z, 9 * (cellAverage q (uerr P train mx a) x) ^ 2 *
      (covariateKernel q x z) ^ 2 * armOutcomeMean P
        (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) z
      ∂unitVolume ∂unitVolume) ≤ 147456 * q * ‖f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hb (x : ℝ) : (cellAverage q (uerr P train mx a) x) ^ 2 ≤ 4 := by
    have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
      (cellAverage_abs_le q hq _ 2 hu x)
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hr (x : ℝ) := integral_weighted_armOutcomeMean_Vres_sq_le
    P hModel train mx my J hJ a f (fun z => (covariateKernel q x z) ^ 2)
    (integrable_covariateKernel_sq q x) (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
  simp_rw [integral_covariateKernel_sq q hq] at hr
  have hx (x : ℝ) : (∫ z, 9 * (cellAverage q (uerr P train mx a) x) ^ 2 *
      (covariateKernel q x z) ^ 2 * armOutcomeMean P
        (fun o => (inner ℝ (Vres train mx my J a o) f) ^ 2) z ∂unitVolume) ≤
      147456 * q * ‖f‖ ^ 2 := by
    simp_rw [mul_assoc (9 * (cellAverage q (uerr P train mx a) x) ^ 2)]
    rw [integral_const_mul]
    calc
      _ ≤ (9 * (cellAverage q (uerr P train mx a) x) ^ 2) * (4096 * ‖f‖ ^ 2 * q) :=
        mul_le_mul_of_nonneg_left (hr x) (by positivity)
      _ ≤ 36 * (4096 * ‖f‖ ^ 2 * q) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        nlinarith [hb x]
      _ = _ := by ring
  calc
    _ ≤ ∫ _ : ℝ, 147456 * q * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun x => integral_nonneg_of_ae (by
          filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
          exact mul_nonneg (by positivity)
            (armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a z hz f)))
      · exact integrable_const _
      · exact Filter.Eventually.of_forall hx
    _ = _ := by simp

/-- The first multiband singleton uses contraction before summing bands, as in (5).
The residual's squared envelope contributes only a factor of nine. -/
-- @node: conditional_multiband_treatment_singleton_le
lemma conditional_multiband_treatment_singleton_le (L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (v : ℝ → Hj (2 ^ T * L)) (hv : Integrable v unitVolume)
    (hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume) (f : Hj (2 ^ T * L)) :
    (∫ x, 9 * (inner ℝ (∑ t ∈ Finset.range (T + 1),
      cellAverage (kt t) (fun z => Qband L (2 ^ T * L) t (v z)) x) f) ^ 2
      ∂unitVolume) ≤ 9 * (∫ x, ‖v x‖ ^ 2 ∂unitVolume) * ‖f‖ ^ 2 := by
  rw [integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    (integral_multiband_cellAverage_inner_sq_le L T hL kt hkt v hv hv2 f)
    (by norm_num : (0 : ℝ) ≤ 9)
  exact h.trans_eq (by ring)

/-- In the second multiband singleton, bounded cell means and orthogonality give (6). -/
-- @node: conditional_multiband_outcome_singleton_le
lemma conditional_multiband_outcome_singleton_le {m : ℕ} (P : ObsLaw) (hModel : Model P)
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t)
    (a : Bool) (f : Hj (2 ^ T * L)) :
    (∫ x, armOutcomeMean P (fun o => (inner ℝ (Vres train mx my (2 ^ T * L) a o)
      (∑ t ∈ Finset.range (T + 1),
        cellAverage (kt t) (uerr P train mx a) x • Qband L (2 ^ T * L) t f)) ^ 2) x
      ∂unitVolume) ≤ 16384 * ‖f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hJ : 0 < 2 ^ T * L := by positivity
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hb (x : ℝ) :
      ‖∑ t ∈ Finset.range (T + 1),
        cellAverage (kt t) (uerr P train mx a) x • Qband L (2 ^ T * L) t f‖ ^ 2 ≤
      4 * ‖f‖ ^ 2 := by
    have ht (t : ℕ) (ht : t ∈ Finset.range (T + 1)) : t ≤ T := by
      have := Finset.mem_range.mp ht
      omega
    have he : ‖∑ t ∈ Finset.range (T + 1),
        cellAverage (kt t) (uerr P train mx a) x • Qband L (2 ^ T * L) t f‖ ^ 2 =
        ∑ t ∈ Finset.range (T + 1),
          (cellAverage (kt t) (uerr P train mx a) x) ^ 2 *
            ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
      simp_rw [← Qband_smul]
      rw [band_remainder_sum_norm_sq L T hL _ ht]
      simp only [Qband_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [he]
    calc
      _ ≤ ∑ t ∈ Finset.range (T + 1), 4 * ‖Qband L (2 ^ T * L) t f‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro t hmem
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        have h := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2
          (cellAverage_abs_le (kt t) (hkt t (ht t hmem)) _ 2 hu x)
        simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
      _ = 4 * ‖f‖ ^ 2 := by
        rw [← Finset.mul_sum]
        have hs := band_remainder_sum_norm_sq L T hL _ ht (fun _ => f)
        rw [(band_projection_algebra L T hL).1 f] at hs
        rw [← hs]
  calc
    _ ≤ ∫ _ : ℝ, 16384 * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact armOutcomeMean_Vres_sq_nonneg P hModel train mx my _ a x hx _
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact (armOutcomeMean_Vres_sq_le P hModel train mx my _ hJ a x hx _).trans
          ((mul_le_mul_of_nonneg_left (hb x) (by norm_num : (0 : ℝ) ≤ 4096)).trans_eq
            (by ring))
    _ = _ := by simp

end CausalSmith.Stat.DensityEffectRoughNull
