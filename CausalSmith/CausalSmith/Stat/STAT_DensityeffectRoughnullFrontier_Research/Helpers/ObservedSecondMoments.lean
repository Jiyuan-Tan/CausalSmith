module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ConditionalKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedDesignMeans
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleVarianceTransport

/-! Transport of observed second moments to the conditional density calculation.
The rectangle specification determines each arm's joint covariate/outcome law,
allowing the covariance roadmap's conditional bounds to control actual sampled residuals. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- The joint covariate/outcome law restricted to an arm has its specified density. -/
-- @node: observed_arm_joint_law
lemma observed_arm_joint_law (P : ObsLaw) (a : Bool) :
    (P.law.restrict {o | A o = a}).map (fun o => (X o, Y o)) =
      (unitVolume.prod unitVolume).withDensity
        (fun z => ENNReal.ofReal (pi P a z.1 * P.eta a z.1 z.2)) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hm : Measurable (fun z : ℝ × ℝ => pi P a z.1 * P.eta a z.1 z.2) := by
    exact ((measurable_pi_design P a).comp measurable_fst).mul (P.eta_measurable a)
  apply Measure.ext_prod
  intro B D hB hD
  rw [Measure.map_apply (by unfold X Y; fun_prop) (hB.prod hD),
    Measure.restrict_apply ((hB.prod hD).preimage (by unfold X Y; fun_prop))]
  have hs : (fun o : Omega => (X o, Y o)) ⁻¹' (B ×ˢ D) ∩ {o | A o = a} =
      {o | X o ∈ B ∧ A o = a ∧ Y o ∈ D} := by
    ext o
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq]
    tauto
  rw [hs, ← ENNReal.ofReal_toReal (measure_ne_top P.law _)]
  rw [show (P.law {o | X o ∈ B ∧ A o = a ∧ Y o ∈ D}).toReal =
      ∫ x in B, pi P a x * (∫ y in D, P.eta a x y ∂unitVolume) ∂unitVolume by
        simpa only [measureReal_def, pi] using P.rectangles B D hB hD a]
  rw [withDensity_apply _ (hB.prod hD),
    setLIntegral_prod _ hm.ennreal_ofReal.aemeasurable]
  rw [ofReal_integral_eq_lintegral_ofReal
    (integrable_pi_eta_bin_probability P a D).integrableOn]
  · apply lintegral_congr_ae
    filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with x hx
    have hp : 0 ≤ pi P a x := by
      have he := P.e_range x hx
      cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [he.1, he.2]
    rw [← ofReal_integral_eq_lintegral_ofReal
      ((P.eta_integrable a x hx).const_mul (pi P a x)).integrableOn]
    · rw [integral_const_mul]
    · filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with y hy
      exact mul_nonneg hp (P.eta_nonneg a x y hx hy)
  · filter_upwards [(ae_restrict_mem measurableSet_Icc).filter_mono ae_restrict_le] with x hx
    have he := P.e_range x hx
    have hp : 0 ≤ pi P a x := by
      cases a <;> simp only [pi, armProbability, Bool.false_eq_true, ↓reduceIte] <;>
        linarith [he.1, he.2]
    exact mul_nonneg hp (eta_bin_probability_mem_Icc P a D x hx).1

/-- Unit design product measure is supported on the two unit intervals. -/
-- @node: unitVolume_prod_support
lemma unitVolume_prod_support :
    ∀ᵐ z ∂unitVolume.prod unitVolume,
      z.1 ∈ Set.Icc (0 : ℝ) 1 ∧ z.2 ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.prod measurableSet_Icc)).2
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
  exact ⟨hx, hy⟩

/-- A finite-range test times the joint density is integrable under the model envelopes. -/
-- @node: integrable_arm_joint_test
lemma integrable_arm_joint_test (P : ObsLaw) (hModel : Model P) (a : Bool)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (hgf : (Set.range g).Finite) :
    Integrable (fun z => (pi P a z.1 * P.eta a z.1 z.2) * g z)
      (unitVolume.prod unitVolume) := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  obtain ⟨C, hC⟩ := hgf.isBounded.exists_norm_le
  have hm : Measurable (fun z : ℝ × ℝ => (pi P a z.1 * P.eta a z.1 z.2) * g z) :=
    (((measurable_pi_design P a).comp measurable_fst).mul (P.eta_measurable a)).mul hg
  apply Integrable.of_bound hm.aestronglyMeasurable (4 * C)
  filter_upwards [unitVolume_prod_support] with z hz
  have hp := model_pi_mem_Icc P hModel a z.1 hz.1
  have he := hModel.density_envelope a z.1 z.2 hz.1 hz.2
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by linarith [hp.1]), abs_of_nonneg (by linarith [he.1])]
  have hpc : pi P a z.1 ≤ 1 := by linarith [hp.2]
  have hw : pi P a z.1 * P.eta a z.1 z.2 ≤ 4 :=
    (mul_le_mul hpc he.2 (by linarith [he.1]) (by norm_num)).trans_eq (by norm_num)
  exact mul_le_mul hw (hC _ ⟨z, rfl⟩) (norm_nonneg _) (by norm_num)

/-- Every measurable finite-range joint test in an arm integrates using its density. -/
-- @node: integral_observed_arm_joint
lemma integral_observed_arm_joint (P : ObsLaw) (hModel : Model P) (a : Bool)
    (g : ℝ × ℝ → ℝ) (hg : Measurable g) (hgf : (Set.range g).Finite) :
    (∫ o in {o | A o = a}, g (X o, Y o) ∂P.law) =
      ∫ x, ∫ y, (pi P a x * P.eta a x y) * g (x, y) ∂unitVolume ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hm : Measurable (fun z : ℝ × ℝ => pi P a z.1 * P.eta a z.1 z.2) :=
    ((measurable_pi_design P a).comp measurable_fst).mul (P.eta_measurable a)
  rw [← integral_map (by unfold X Y; fun_prop) hg.aestronglyMeasurable,
    observed_arm_joint_law]
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  have he : (∫ z, (ENNReal.ofReal (pi P a z.1 * P.eta a z.1 z.2)).toReal • g z
      ∂unitVolume.prod unitVolume) =
      ∫ z, (pi P a z.1 * P.eta a z.1 z.2) * g z ∂unitVolume.prod unitVolume := by
    apply integral_congr_ae
    filter_upwards [unitVolume_prod_support] with z hz
    rw [ENNReal.toReal_ofReal (mul_nonneg
      (by linarith [(model_pi_mem_Icc P hModel a z.1 hz.1).1])
      (P.eta_nonneg a z.1 z.2 hz.1 hz.2)), smul_eq_mul]
  rw [he]
  exact integral_prod _ (integrable_arm_joint_test P hModel a g hg hgf)

/-- The rectangle specification transports every finite-range scalar moment to the
conditional arm/outcome integral, including squared residual tests. -/
-- @node: integral_observed_eq_armOutcomeMean
lemma integral_observed_eq_armOutcomeMean (P : ObsLaw) (hModel : Model P)
    (g : Omega → ℝ) (hg : Measurable g) (hgf : (Set.range g).Finite) :
    (∫ o, g o ∂P.law) = ∫ x, armOutcomeMean P g x ∂unitVolume := by
  classical
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hA (a : Bool) : MeasurableSet {o : Omega | A o = a} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) measurable_const
  have hgi := integrable_of_measurable_finite_range P.law g hg hgf
  have hi (a : Bool) : Integrable (fun x => ∫ y,
      (pi P a x * P.eta a x y) * g (x, a, y) ∂unitVolume) unitVolume :=
    (integrable_arm_joint_test P hModel a (fun z => g (z.1, a, z.2))
      (by fun_prop) (chain_finite_range_precomp hgf _)).integral_prod_left
  calc
    _ = ∫ o, ∑ a : Bool, {o | A o = a}.indicator g o ∂P.law := by
      apply integral_congr_ae
      filter_upwards [] with o
      cases ha : A o <;> simp [ha]
    _ = ∑ a : Bool, ∫ o in {o | A o = a}, g o ∂P.law := by
      rw [integral_finsetSum _ (fun a _ => hgi.indicator (hA a))]
      simp only [integral_indicator (hA _)]
    _ = ∑ a : Bool, ∫ x, ∫ y,
        (pi P a x * P.eta a x y) * g (x, a, y) ∂unitVolume ∂unitVolume := by
      apply Finset.sum_congr rfl
      intro a _
      have hr : (∫ o in {o | A o = a}, g o ∂P.law) =
          ∫ o in {o | A o = a}, g (X o, a, Y o) ∂P.law := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hA a)] with o ho
        have hao : A o = a := ho
        simp only [X, A, Y] at hao ⊢
        rw [← hao]
      rw [hr]
      exact integral_observed_arm_joint P hModel a (fun z : ℝ × ℝ => g (z.1, a, z.2)) (by fun_prop)
        (chain_finite_range_precomp hgf _)
    _ = _ := by
      unfold armOutcomeMean
      simp only [smul_eq_mul]
      exact (integral_finsetSum _ (fun a _ => hi a)).symm

/-- Covariate cell averages have finite range at every finite rank. -/
lemma finite_range_cellAverage {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (q : ℕ) (v : ℝ → E) : (Set.range (cellAverage q v)).Finite := by
  apply chain_finite_range_of_factors (finite_range_cell q)
  intro x z h
  simp only [cellAverage, covariateKernel, h]

/-- A finite-range covariate-dependent residual test has its genuine conditional moment. -/
-- @node: integral_observed_inner_Vres_test_sq
lemma integral_observed_inner_Vres_test_sq (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (a : Bool) (v : ℝ → Hj J)
    (hv : @Measurable ℝ (Hj J) _ (borel _) v) (hvf : (Set.range v).Finite) :
    (∫ o, (inner ℝ (Vres train mx my J a o) (v (X o))) ^ 2 ∂P.law) =
      ∫ x, armOutcomeMean P
        (fun o => (inner ℝ (Vres train mx my J a o) (v x)) ^ 2) x ∂unitVolume := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hf := chain_finite_range_binary (finite_range_Vres train mx my J a)
    (chain_finite_range_precomp hvf X) (fun w z => (inner ℝ w z) ^ 2)
  rw [integral_observed_eq_armOutcomeMean P hModel _ (by unfold X; fun_prop) hf]
  rfl

/-- Observed squared residual tests with covariate-dependent histogram vectors are
controlled by their design energy, preserving the conditional estimate's constant. -/
-- @node: integral_observed_inner_Vres_test_sq_le
lemma integral_observed_inner_Vres_test_sq_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool)
    (v : ℝ → Hj J) (hv : @Measurable ℝ (Hj J) _ (borel _) v)
    (hvf : (Set.range v).Finite) :
    (∫ o, (inner ℝ (Vres train mx my J a o) (v (X o))) ^ 2 ∂P.law) ≤
      4096 * ∫ x, ‖v x‖ ^ 2 ∂unitVolume := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  rw [integral_observed_inner_Vres_test_sq P hModel train mx my J a v hv hvf]
  exact integral_armOutcomeMean_Vres_sq_le P hModel train mx my J hJ v
    (integrable_of_measurable_finite_range unitVolume _ (by fun_prop)
      (chain_finite_range_comp hvf (fun z => ‖z‖ ^ 2))) a

/-- The observable second-role projection of the multiband kernel satisfies (6),
with no band-count loss and no upper bound on the covariate ranks. -/
-- @node: observed_multiband_outcome_singleton_moment_le
lemma observed_multiband_outcome_singleton_moment_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool)
    (f : Hj (2 ^ T * L)) :
    (∫ o, (inner ℝ (Vres train mx my (2 ^ T * L) a o)
      (∑ t ∈ Finset.range (T + 1), cellAverage (kt t) (uerr P train mx a) (X o) •
        Qband L (2 ^ T * L) t f)) ^ 2 ∂P.law) ≤ 16384 * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  rw [integral_observed_inner_Vres_test_sq P hModel train mx my _ a
    (fun x => ∑ t ∈ Finset.range (T + 1),
      cellAverage (kt t) (uerr P train mx a) x • Qband L (2 ^ T * L) t f)
    (by fun_prop)
    (chain_finite_range_sum _ _ (fun t _ =>
      chain_finite_range_comp (finite_range_cellAverage (kt t) (uerr P train mx a))
        (fun r => r • Qband L (2 ^ T * L) t f)))]
  exact conditional_multiband_outcome_singleton_le P hModel train mx my L T hL kt hkt a f

/-- The conditional residual second-moment bound holds under the actual observed law. -/
-- @node: integral_observed_inner_Vres_sq_le
lemma integral_observed_inner_Vres_sq_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool) (f : Hj J) :
    (∫ o, (inner ℝ (Vres train mx my J a o) f) ^ 2 ∂P.law) ≤ 4096 * ‖f‖ ^ 2 := by
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  rw [integral_observed_eq_armOutcomeMean P hModel _ (by fun_prop)
    (chain_finite_range_comp (finite_range_Vres train mx my J a)
      (fun v => (inner ℝ v f) ^ 2))]
  calc
    _ ≤ ∫ _ : ℝ, 4096 * ‖f‖ ^ 2 ∂unitVolume := by
      apply integral_mono_of_nonneg
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact armOutcomeMean_Vres_sq_nonneg P hModel train mx my J a x hx f
      · exact integrable_const _
      · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        exact armOutcomeMean_Vres_sq_le P hModel train mx my J hJ a x hx f
    _ = _ := by simp

/-- The first-order sampled coefficient has the roadmap's uniform 4096/m variance budget. -/
-- @node: variance_inner_Uone_le
lemma variance_inner_Uone_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J)
    (b : Fin 2) (a : Bool) (f : Hj J) :
    variance (fun eval => inner ℝ (Uone train mx my J eval b a) f) (evalLaw P m) ≤
      4096 * (m : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  rw [variance_inner_Uone]
  have hv := (variance_le_expectation_sq
    (memLp_inner_Vres P train mx my J a f).aestronglyMeasurable).trans
      (integral_observed_inner_Vres_sq_le P hModel train mx my J hJ a f)
  exact (mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹)).trans_eq
    (by ring)

/-- The actual outcome singleton projection (10) obeys the bound (11) under P,
including every trained realization and every positive averaging rank. -/
-- @node: observed_third_outcome_singleton_moment_le
lemma observed_third_outcome_singleton_moment_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J q : ℕ) (hJ : 0 < J) (hq : 0 < q)
    (a : Bool) (f : Hj J) :
    (∫ o, (inner ℝ ((cellAverage q (uerr P train mx a) (X o)) ^ 2 •
      Vres train mx my J a o) f) ^ 2 ∂P.law) ≤ 65536 * ‖f‖ ^ 2 := by
  have hu : ∀ᵐ x ∂unitVolume, |uerr P train mx a x| ≤ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact uerr_abs_le P hModel train mx a x hx
  have hb (x : ℝ) : (cellAverage q (uerr P train mx a) x) ^ 4 ≤ 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg _) (cellAverage_abs_le q hq _ 2 hu x) 4
    have he : |cellAverage q (uerr P train mx a) x| ^ 4 =
        (cellAverage q (uerr P train mx a) x) ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs, ← pow_mul]
    rw [he] at h
    norm_num only at h
    exact h
  calc
    _ ≤ ∫ o, 16 * (inner ℝ (Vres train mx my J a o) f) ^ 2 ∂P.law := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact (memLp_inner_Vres P train mx my J a f).integrable_sq.const_mul 16
      · filter_upwards [] with o
        simp only [real_inner_smul_left, mul_pow, ← pow_mul]
        exact mul_le_mul_of_nonneg_right (hb (X o)) (sq_nonneg _)
    _ = 16 * ∫ o, (inner ℝ (Vres train mx my J a o) f) ^ 2 ∂P.law := integral_const_mul _ _
    _ ≤ 16 * (4096 * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left
      (integral_observed_inner_Vres_sq_le P hModel train mx my J hJ a f) (by norm_num)
    _ = _ := by ring

end CausalSmith.Stat.DensityEffectRoughNull
