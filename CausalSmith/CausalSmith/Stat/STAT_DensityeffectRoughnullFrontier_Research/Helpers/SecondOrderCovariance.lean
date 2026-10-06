module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.CovarianceAssembly
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ObservedKernelMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.RoleVarianceTransport
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.ThirdRoleProjections

/-! Canonical singleton projections and sampled second-order covariance control.
The treatment singleton is bounded before summing bands, so no band-count loss occurs. -/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull

/-- A finite-range two-role kernel can be integrated by retaining only its first role. -/
-- @node: partial_role_two_first
lemma partial_role_two_first {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (h : (Fin 2 → E) → ℝ)
    (hh : Measurable h) (hf : (Set.range h).Finite) (o : Fin 2 → E) :
    partialRoleKernel μ 2 {0} h o = ∫ y, h ![o 0, y] ∂μ := by
  unfold partialRoleKernel
  rw [integral_two_roles_eq_iterated μ _
    (integrable_of_measurable_finite_range _ _ (by
      apply hh.comp
      apply measurable_pi_lambda
      intro r
      split_ifs <;> fun_prop)
      (chain_finite_range_precomp hf _))]
  have he (x y : E) : h (fun r => if r ∈ ({0} : Finset (Fin 2)) then o r else (![x, y]) r) =
      h ![o 0, y] := by
    congr 1
    funext r
    fin_cases r <;> simp
  simp_rw [he]
  simp

/-- Retaining only the second role integrates out exactly the first observation. -/
-- @node: partial_role_two_second
lemma partial_role_two_second {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (h : (Fin 2 → E) → ℝ)
    (hh : Measurable h) (hf : (Set.range h).Finite) (o : Fin 2 → E) :
    partialRoleKernel μ 2 {1} h o = ∫ x, h ![x, o 1] ∂μ := by
  unfold partialRoleKernel
  rw [integral_two_roles_eq_iterated μ _
    (integrable_of_measurable_finite_range _ _ (by
      apply hh.comp
      apply measurable_pi_lambda
      intro r
      split_ifs <;> fun_prop)
      (chain_finite_range_precomp hf _))]
  have he (x y : E) : h (fun r => if r ∈ ({1} : Finset (Fin 2)) then o r else (![x, y]) r) =
      h ![x, o 1] := by
    congr 1
    funext r
    fin_cases r <;> simp
  simp_rw [he]
  simp

/-- Keeping every role leaves the original kernel, including at exceptional points. -/
-- @node: partial_role_univ
lemma partial_role_univ {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (d : ℕ)
    (h : (Fin d → E) → ℝ) (o : Fin d → E) :
    partialRoleKernel μ d Finset.univ h o = h o := by
  simp [partialRoleKernel]

/-- The weighted outcome-error coefficients have the roadmap's uniform norm bound. -/
-- @node: verr_coefficients_norm_le
lemma verr_coefficients_norm_le (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my J : ℕ) (hJ : 0 < J) (a : Bool)
    (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    ‖coefficients J (verr P train mx my a x)‖ ≤ 30 := by
  have hp : ‖pilotCoefficients train mx my J a x‖ ≤ 8 := by
    have h := pilotCoefficients_inner_sq_le train mx my J hJ a x
      (pilotCoefficients train mx my J a x)
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [sq_nonneg (‖pilotCoefficients train mx my J a x‖ ^ 2 - 64),
      norm_nonneg (pilotCoefficients train mx my J a x)]
  have ht : ‖coefficients J (P.eta a x)‖ ≤ 2 := by
    have h := density_histogram_integral_sq_le J (coefficients J (P.eta a x))
      (P.eta a x) (P.eta_integrable a x hx) (P.eta_normalized a x hx) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact P.eta_nonneg a x y hx hy)
    rw [← inner_coefficients_eq_integral J _ _ (P.eta_integrable a x hx),
      real_inner_self_eq_norm_sq] at h
    have he := density_histogram_energy_le J hJ (coefficients J (P.eta a x))
      (P.eta a x) (P.eta_integrable a x hx) 4 (by norm_num) (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
        exact (hModel.density_envelope a x y hx hy).2)
    nlinarith [sq_nonneg (‖coefficients J (P.eta a x)‖ ^ 2 - 4),
      norm_nonneg (coefficients J (P.eta a x))]
  have hu := uerr_mem_Icc P hModel train mx a x hx
  have he : coefficients J (verr P train mx my a x) =
      (1 + uerr P train mx a x) •
        (coefficients J (P.eta a x) - pilotCoefficients train mx my J a x) := by
    exact coefficients_const_mul_sub J _ _ _ (P.eta_integrable a x hx)
      (densityPilot_integrable train mx my a x)
  rw [he, norm_smul, Real.norm_eq_abs]
  have hd := (norm_sub_le _ _).trans (add_le_add ht hp)
  have hc : |1 + uerr P train mx a x| ≤ 3 := by rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  exact (mul_le_mul hc hd (norm_nonneg _) (by norm_num)).trans (by norm_num)

/-- Singleton and full second moments imply the sharp rectangular two-role budget. -/
-- @node: two_role_variance_le_of_singleton_moments
lemma two_role_variance_le_of_singleton_moments {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (m : ℕ) (hm : 1 ≤ m)
    (h : (Fin 2 → E) → ℝ) (hh : Measurable h) (hf : (Set.range h).Finite)
    (F S : ℝ) (hF : 0 ≤ F) (hS : 0 ≤ S)
    (hfirst : (∫ x, (∫ y, h ![x, y] ∂μ) ^ 2 ∂μ) ≤ 8100 * F)
    (hsecond : (∫ y, (∫ x, h ![x, y] ∂μ) ^ 2 ∂μ) ≤ 16384 * F)
    (hfull : (∫ o, (h o) ^ 2 ∂Measure.pi (fun _ : Fin 2 => μ)) ≤ 36864 * S) :
    variance (roleAverage 2 m h)
      (Measure.pi (fun _ : Fin 2 => Measure.pi (fun _ : Fin m => μ))) ≤
      (2 : ℝ) ^ 16 * ((m : ℝ)⁻¹ * F + (m : ℝ) ^ (-2 : ℤ) * S) := by
  have hL2 : MemLp h 2 (Measure.pi (fun _ : Fin 2 => μ)) := by
    obtain ⟨C, hC⟩ := hf.isBounded.exists_norm_le
    exact MemLp.of_bound hh.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun o => hC _ ⟨o, rfl⟩))
  apply two_role_variance_le_of_projection_moments μ m hm h hh hL2 F S hF hS
  · have hi := (partial_role_kernel_memLp μ 2 {0} h hL2).integrable_sq
    rw [integral_two_roles_eq_iterated μ _ hi]
    simp_rw [partial_role_two_first μ h hh hf]
    simpa using hfirst
  · have hi := (partial_role_kernel_memLp μ 2 {1} h hL2).integrable_sq
    have hp := measurePreserving_eval (fun _ : Fin 2 => μ) (1 : Fin 2)
    have hg : AEStronglyMeasurable (fun y => (∫ x, h ![x, y] ∂μ) ^ 2) μ := by
      have hm : Measurable (fun z : E × E => h ![z.1, z.2]) := by
        apply hh.comp
        apply measurable_pi_lambda
        intro i
        fin_cases i
        · exact measurable_fst
        · exact measurable_snd
      exact hm.stronglyMeasurable.integral_prod_left.aestronglyMeasurable.pow 2
    have he := integral_map hp.aemeasurable (hp.map_eq.symm ▸ hg)
    rw [hp.map_eq] at he
    simp_rw [partial_role_two_second μ h hh hf]
    exact he.symm.trans_le hsecond
  · simpa only [show ({0, 1} : Finset (Fin 2)) = Finset.univ by decide,
      partial_role_univ] using hfull

/-- Testing the observable outcome kernel integrates to the tested coefficient cell mean. -/
-- @node: integral_tested_Vres_covariateKernel
lemma integral_tested_Vres_covariateKernel (P : ObsLaw) {m : ℕ}
    (train : Fin m → Omega) (mx my J k : ℕ) (a : Bool) (x : ℝ) (f : Hj J) :
    (∫ o, covariateKernel k x (X o) * inner ℝ (Vres train mx my J a o) f ∂P.law) =
      inner ℝ (cellAverage k (fun z => coefficients J (verr P train mx my a z)) x) f := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hi : Integrable (fun o => covariateKernel k x (X o) •
      Vres train mx my J a o) P.law := by
    apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_precomp (finite_range_covariateKernel k) (fun o => (x, X o)))
      (finite_range_Vres train mx my J a) (· • ·)
  calc
    _ = ∫ o, inner ℝ f (covariateKernel k x (X o) • Vres train mx my J a o) ∂P.law := by
      apply integral_congr_ae
      filter_upwards [] with o
      rw [real_inner_smul_right, real_inner_comm]
    _ = inner ℝ f (∫ o, covariateKernel k x (X o) • Vres train mx my J a o ∂P.law) :=
      integral_inner hi f
    _ = _ := by rw [integral_Vres_covariateKernel]; exact real_inner_comm _ _

/-- Integrating the treatment singleton in the multiband score gives its projected cell means. -/
-- @node: multiband_score_first_projection
lemma multiband_score_first_projection (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J : ℕ) (kt : ℕ → ℕ)
    (a : Bool) (f : Hj J) (o : Omega) :
    (∫ v, Rres train mx a o *
      inner ℝ (Vres train mx my J a v)
        (∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X o) (X v) • Qband L J t f)
        ∂P.law) =
      Rres train mx a o * inner ℝ
        (∑ t ∈ Finset.range (T + 1), cellAverage (kt t)
          (fun z => Qband L J t (coefficients J (verr P train mx my a z))) (X o)) f := by
  let : MeasurableSpace (Hj J) := borel _
  let : BorelSpace (Hj J) := ⟨rfl⟩
  have hv : Integrable (fun z => coefficients J (verr P train mx my a z)) unitVolume := by
    apply integrable_coefficients_design
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul, Function.uncurry] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  rw [integral_const_mul]
  simp only [inner_sum, real_inner_smul_right]
  rw [integral_finsetSum _ (fun t _ => by
    apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
    exact chain_finite_range_binary
      (chain_finite_range_precomp (finite_range_covariateKernel (kt t)) (fun v => (X o, X v)))
      (chain_finite_range_comp (finite_range_Vres train mx my J a)
        (fun v => inner ℝ v (Qband L J t f))) (· * ·))]
  simp_rw [integral_tested_Vres_covariateKernel]
  simp only [sum_inner, ← Qband_inner, Qband_cellAverage _ _ _ _ _ hv]

/-- Integrating the first treatment role gives the outcome singleton without a band loss. -/
-- @node: multiband_score_second_projection
lemma multiband_score_second_projection (P : ObsLaw) (hModel : Model P) {m : ℕ}
    (train : Fin m → Omega) (mx my L T J : ℕ) (kt : ℕ → ℕ)
    (a : Bool) (f : Hj J) (v : Omega) :
    (∫ o, Rres train mx a o *
      inner ℝ (Vres train mx my J a v)
        (∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X o) (X v) • Qband L J t f)
        ∂P.law) =
      inner ℝ (Vres train mx my J a v)
        (∑ t ∈ Finset.range (T + 1), cellAverage (kt t) (uerr P train mx a) (X v) •
          Qband L J t f) := by
  simp only [inner_sum, real_inner_smul_right, Finset.mul_sum]
  rw [integral_finsetSum _ (fun t _ => by
    apply integrable_of_measurable_finite_range _ _ (by unfold X; fun_prop)
    simpa only [mul_assoc] using chain_finite_range_comp
      (chain_finite_range_binary (finite_range_Rres train mx a)
        (chain_finite_range_precomp (finite_range_covariateKernel (kt t)) (fun o => (X o, X v)))
        (· * ·)) (fun z => z * inner ℝ (Vres train mx my J a v) (Qband L J t f)))]
  simp_rw [← mul_assoc, integral_mul_const, integral_Rres_covariateKernel P hModel]

/-- The treatment singleton has second moment at most 8100 times test energy under P. -/
-- @node: observed_multiband_treatment_singleton_moment_le
lemma observed_multiband_treatment_singleton_moment_le (P : ObsLaw) (hModel : Model P)
    {m : ℕ} (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (a : Bool)
    (f : Hj (2 ^ T * L)) :
    (∫ o, (Rres train mx a o * inner ℝ
        (∑ t ∈ Finset.range (T + 1), cellAverage (kt t)
          (fun z => Qband L (2 ^ T * L) t (coefficients (2 ^ T * L)
            (verr P train mx my a z))) (X o)) f) ^ 2 ∂P.law) ≤ 8100 * ‖f‖ ^ 2 := by
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  let : IsProbabilityMeasure unitVolume := ⟨by simp [unitVolume]⟩
  have hLpos : 0 < L := by obtain ⟨l, rfl⟩ := hL; positivity
  have hJ : 0 < 2 ^ T * L := by positivity
  let v := fun z => coefficients (2 ^ T * L) (verr P train mx my a z)
  have hv : Integrable v unitVolume := by
    apply integrable_coefficients_design
    change Integrable (fun z : ℝ × ℝ => verr P train mx my a z.1 z.2) _
    simpa only [pow_zero, one_mul, Function.uncurry] using
      integrable_uerr_pow_mul_verr_joint P hModel train mx my a 0
  have hv2 : Integrable (fun x => ‖v x‖ ^ 2) unitVolume := by
    apply (integrable_const (900 : ℝ)).mono' (hv.aestronglyMeasurable.norm.pow 2)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change ‖v x‖ ^ 2 ≤ 900
    nlinarith [verr_coefficients_norm_le P hModel train mx my _ hJ a x hx, norm_nonneg (v x)]
  have hvbound : (∫ x, ‖v x‖ ^ 2 ∂unitVolume) ≤ 900 := by
    calc
      _ ≤ ∫ _ : ℝ, (900 : ℝ) ∂unitVolume := by
        apply integral_mono_ae hv2 (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
        nlinarith [verr_coefficients_norm_le P hModel train mx my _ hJ a x hx, norm_nonneg (v x)]
      _ = _ := by simp
  have h := integral_Rres_design_sq_le P hModel train mx a
    (fun x => inner ℝ (∑ t ∈ Finset.range (T + 1), cellAverage (kt t)
      (fun z => Qband L (2 ^ T * L) t (v z)) x) f) (by
      simp only [sum_inner]
      apply Finset.measurable_sum
      intro t _
      apply measurable_of_histogram_const (kt t)
      intro x z hxz
      rw [cellAverage_eq_of_cell_eq _ _ _ _ hxz])
    (chain_finite_range_comp (chain_finite_range_sum _ _ (fun t _ =>
      finite_range_cellAverage (kt t) _)) (fun z => inner ℝ z f))
  have hc := conditional_multiband_treatment_singleton_le L T hL kt hkt v hv hv2 f
  rw [integral_const_mul] at hc
  exact h.trans (hc.trans (by nlinarith [mul_le_mul_of_nonneg_right hvbound (sq_nonneg ‖f‖)]))

/-- The actual sampled second-order statistic obeys (8) with the public 2^16 constant. -/
-- @node: variance_inner_Utwo_le
lemma variance_inner_Utwo_le (P : ObsLaw) (hModel : Model P) {m : ℕ} (hm : 1 ≤ m)
    (train : Fin m → Omega) (mx my L T : ℕ) (hL : Dyadic L)
    (kt : ℕ → ℕ) (hkt : ∀ t, t ≤ T → 0 < kt t) (b : Fin 2) (a : Bool)
    (f : Hj (2 ^ T * L)) :
    variance (fun eval => inner ℝ (Utwo train mx my L T (2 ^ T * L) kt eval b a) f)
      (evalLaw P m) ≤ (2 : ℝ) ^ 16 *
        ((m : ℝ)⁻¹ * ‖f‖ ^ 2 + (m : ℝ) ^ (-2 : ℤ) *
          ∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2) := by
  let : MeasurableSpace (Hj (2 ^ T * L)) := borel _
  let : BorelSpace (Hj (2 ^ T * L)) := ⟨rfl⟩
  let h : (Fin 2 → Omega) → ℝ := fun o => Rres train mx a (o 0) *
    inner ℝ (Vres train mx my (2 ^ T * L) a (o 1))
      (∑ t ∈ Finset.range (T + 1), covariateKernel (kt t) (X (o 0)) (X (o 1)) •
        Qband L (2 ^ T * L) t f)
  have hh : Measurable h := by dsimp [h]; unfold X; fun_prop
  have hf : (Set.range h).Finite :=
    finite_range_multiband_role_kernel train mx my L T (2 ^ T * L) kt a f
  have hb := two_role_variance_le_of_singleton_moments P.law m hm h hh hf
    (‖f‖ ^ 2)
    (∑ t ∈ Finset.range (T + 1), (kt t : ℝ) * ‖Qband L (2 ^ T * L) t f‖ ^ 2)
    (sq_nonneg _) (Finset.sum_nonneg (fun t _ => by positivity))
    (by
      simp only [h, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp_rw [multiband_score_first_projection P hModel]
      exact observed_multiband_treatment_singleton_moment_le P hModel train mx my L T hL kt hkt a f)
    (by
      simp only [h, Matrix.cons_val_zero, Matrix.cons_val_one]
      simp_rw [multiband_score_second_projection P hModel]
      exact observed_multiband_outcome_singleton_moment_le P hModel train mx my L T hL kt hkt a f)
    (multiband_role_kernel_second_moment_le P hModel train mx my L T hL kt hkt a f)
  rw [variance_inner_Utwo_eq_roleAverage]
  simpa only [h, inner_sum, real_inner_smul_right] using hb

end CausalSmith.Stat.DensityEffectRoughNull
