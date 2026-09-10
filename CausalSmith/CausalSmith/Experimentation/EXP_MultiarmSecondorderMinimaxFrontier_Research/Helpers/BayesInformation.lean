import Causalean.Stat.Limit.ObservationDependentVanTrees.Main

/-!
Bayesian information inequality over a general σ-finite observation measure.
The bundle below exposes the paper's density, support, a.e.-AC, derivative,
differentiation-under-the-integral, finite-information, and joint-integrability
premises without replacing them by everywhere differentiability or an
unweighted `T²` assumption.
-/

open MeasureTheory Set Filter
open scoped Interval

namespace CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier

/-- The Bayes joint integral averages an observation field against its likelihood and then against the parameter prior. -/
noncomputable def bayesJointIntegral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ell u : ℝ) (w : ℝ → ℝ)
    (p f : ℝ → Ω → ℝ) : ℝ :=
  ∫ θ in ell..u, ∫ x, f θ x * p θ x * w θ ∂μ

/-- Prior information is the prior expectation of the squared logarithmic derivative of the prior density. -/
noncomputable def priorInformation (ell u : ℝ) (w dw : ℝ → ℝ) : ℝ :=
  ∫ θ in ell..u, if 0 < w θ then dw θ ^ 2 / w θ else 0

/-- Fisher information is the joint prior-and-observation expectation of the squared likelihood score. -/
noncomputable def fisherInformation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p dp : ℝ → Ω → ℝ) (θ : ℝ) : ℝ :=
  ∫ x, if 0 < p θ x then dp θ x ^ 2 / p θ x else 0 ∂μ

/-- All hypotheses stated in the paper for the observation-dependent van Trees bound. -/
structure BayesianInformationRegularity {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ell u : ℝ) (w dw : ℝ → ℝ)
    (p dp g dg : ℝ → Ω → ℝ) (T : Ω → ℝ) : Prop where
  interval_nonempty : ell < u
  prior_nonnegative : ∀ θ, 0 ≤ w θ
  prior_probability : ∫ θ in ell..u, w θ = 1
  prior_C1 : ContDiff ℝ 1 w
  prior_compact_support : IsCompact (tsupport w) ∧ tsupport w ⊆ Ioo ell u
  prior_positive_on_interior : ∀ θ ∈ interior (tsupport w), 0 < w θ
  prior_derivative : ∀ θ, dw θ = deriv w θ
  density_nonnegative : ∀ θ ∈ Ioo ell u, ∀ᵐ x ∂μ, 0 ≤ p θ x
  density_probability : ∀ θ ∈ Ioo ell u, ∫ x, p θ x ∂μ = 1
  density_integrable : ∀ θ ∈ Ioo ell u, Integrable (fun x => p θ x) μ
  density_derivative_integrable : ∀ θ ∈ Ioo ell u, Integrable (fun x => dp θ x) μ
  density_integral_derivative : ∀ θ ∈ Ioo ell u,
    HasDerivAt (fun t => ∫ x, p t x ∂μ) (∫ x, dp θ x ∂μ) θ
  likelihood_ac_ae : ∀ᵐ x ∂μ, ∀ a ∈ Ioo ell u, ∀ b ∈ Ioo ell u,
    AbsolutelyContinuousOnInterval (fun θ => p θ x) a b
  likelihood_derivative_ae : ∀ᵐ x ∂μ, ∀ᵐ θ ∂volume.restrict (Ioo ell u),
    dp θ x = deriv (fun s => p s x) θ
  target_ac_ae : ∀ᵐ x ∂μ, ∀ a ∈ Ioo ell u, ∀ b ∈ Ioo ell u,
    AbsolutelyContinuousOnInterval (fun θ => g θ x) a b
  target_derivative_ae : ∀ᵐ x ∂μ, ∀ᵐ θ ∂volume.restrict (Ioo ell u),
    dg θ x = deriv (fun s => g s x) θ
  likelihood_hasDerivAt_ae : ∀ᵐ z ∂((volume.restrict (Ioo ell u)).prod μ),
    HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1
  target_hasDerivAt_ae : ∀ᵐ z ∂((volume.restrict (Ioo ell u)).prod μ),
    HasDerivAt (fun t => g t z.2) (dg z.1 z.2) z.1
  differentiation_under_integral : ∀ θ ∈ Ioo ell u, ∫ x, dp θ x ∂μ = 0
  prior_information_integrable :
    IntegrableOn (fun θ => if 0 < w θ then dw θ ^ 2 / w θ else 0) (Icc ell u)
  fisher_information_integrable : ∀ θ ∈ Ioo ell u,
    Integrable (fun x => if 0 < p θ x then dp θ x ^ 2 / p θ x else 0) μ
  total_information_positive :
    0 < priorInformation ell u w dw +
      ∫ θ in ell..u, fisherInformation μ p dp θ * w θ
  risk_joint_integrable : Integrable
    (fun z : ℝ × Ω => (T z.2 - g z.1 z.2) ^ 2 * p z.1 z.2 * w z.1)
    ((volume.restrict (Icc ell u)).prod μ)
  derivative_joint_integrable : Integrable
    (fun z : ℝ × Ω => dg z.1 z.2 * p z.1 z.2 * w z.1)
    ((volume.restrict (Icc ell u)).prod μ)
  score_joint_integrable : Integrable
    (fun z : ℝ × Ω =>
      ((if 0 < w z.1 then dw z.1 / w z.1 else 0) +
        (if 0 < p z.1 z.2 then dp z.1 z.2 / p z.1 z.2 else 0)) ^ 2 *
        p z.1 z.2 * w z.1)
    ((volume.restrict (Icc ell u)).prod μ)
  product_ac_ae : ∀ᵐ x ∂μ, AbsolutelyContinuousOnInterval
    (fun θ => w θ * p θ x * (T x - g θ x)) ell u
  boundary_vanishes_ae : ∀ᵐ x ∂μ,
    w ell * p ell x * (T x - g ell x) = 0 ∧
    w u * p u x * (T x - g u x) = 0
  derivative_balance_joint_integrable : Integrable
    (Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
      w dw p dp g dg T) ((volume.restrict (Icc ell u)).prod μ)
  error_score_joint_integrable : Integrable
    (Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField w dw p dp g T)
    ((volume.restrict (Icc ell u)).prod μ)
  joint_score_sq_integrable : Integrable
    (Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField w dw p dp)
    ((volume.restrict (Icc ell u)).prod μ)
  prior_score_sq_integrable : Integrable
    (fun θ => w θ *
      (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw θ) ^ 2)
    (volume.restrict (Icc ell u))
  prior_score_joint_sq_integrable : Integrable
    (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
      (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2)
    ((volume.restrict (Icc ell u)).prod μ)
  fisher_score_joint_sq_integrable : Integrable
    (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
      (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
        p dp z.1 z.2) ^ 2)
    ((volume.restrict (Icc ell u)).prod μ)
  score_cross_joint_integrable : Integrable
    (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
      (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
        Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
          p dp z.1 z.2))
    ((volume.restrict (Icc ell u)).prod μ)

-- @node: bayesianInformation_ae_section_nonnegative
/-- [the population size is positive](hyp:hn), [the relevant sections are almost everywhere absolutely continuous](hyp:hac), [Sectionwise absolute continuity turns parameterwise a.e. nonnegativity into a common full-measure set of sections that are nonnegative on the interval.](goal) -/
lemma bayesianInformation_ae_section_nonnegative
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {ell u : ℝ} {p : ℝ → Ω → ℝ}
    (hn : ∀ θ, θ ∈ Ioo ell u → ∀ᵐ x ∂μ, 0 ≤ p θ x)
    (hac : ∀ᵐ x ∂μ, ∀ a ∈ Ioo ell u, ∀ b ∈ Ioo ell u,
      AbsolutelyContinuousOnInterval (fun θ => p θ x) a b) :
    ∀ᵐ x ∂μ, ∀ θ, θ ∈ Ioo ell u → 0 ≤ p θ x := by
  have hrat : ∀ᵐ x ∂μ, ∀ q : ℚ, ((q : ℝ) ∈ Ioo ell u → 0 ≤ p q x) := by
    rw [ae_all_iff]
    intro q
    by_cases hq : (q : ℝ) ∈ Ioo ell u
    · exact (hn q hq).mono (fun _ hx _ => hx)
    · exact Filter.Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [hac, hrat] with x hxac hxrat
  intro θ hθ
  rcases hθ with ⟨hellθ, hθu⟩
  obtain ⟨q, _hqmono, hqθ, hqlim⟩ :=
    Rat.denseRange_cast.exists_seq_strictMono_tendsto Rat.cast_mono θ
  let a := (ell + θ) / 2
  let b := (θ + u) / 2
  have ha : a ∈ Ioo ell u := by dsimp [a]; constructor <;> linarith
  have hb : b ∈ Ioo ell u := by dsimp [b]; constructor <;> linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hθab : θ ∈ Ioo a b := by dsimp [a, b]; constructor <;> linarith
  have hcont : ContinuousAt (fun s => p s x) θ :=
    (hxac a ha b hb).continuousOn.continuousAt
      (by simpa [hab.le] using Icc_mem_nhds hθab.1 hθab.2)
  apply isClosed_Ici.mem_of_tendsto (hcont.tendsto.comp hqlim)
  filter_upwards [(tendsto_order.1 hqlim).1 a hθab.1] with n hn
  exact hxrat (q n) ⟨ha.1.trans hn, (hqθ n).trans hθu⟩

-- @node: lem:bayesian-information-inequality
/-- [The AC-regularity Bayesian Cramér–Rao inequality for a target `g(θ,x)`.](goal) -/
lemma bayesianInformationInequality
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SigmaFinite μ]
    (ell u : ℝ) (w dw : ℝ → ℝ) (p dp g dg : ℝ → Ω → ℝ) (T : Ω → ℝ)
    (h : BayesianInformationRegularity μ ell u w dw p dp g dg T) :
    bayesJointIntegral μ ell u w p (fun θ x => (T x - g θ x) ^ 2) ≥
      bayesJointIntegral μ ell u w p dg ^ 2 /
        (priorInformation ell u w dw +
          ∫ θ in ell..u, fisherInformation μ p dp θ * w θ) := by
  let PM := Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
  have hsupport : Function.support w ⊆ Icc ell u := by
    intro θ hθ
    exact ⟨le_of_lt (h.prior_compact_support.2 (subset_tsupport w hθ)).1,
      le_of_lt (h.prior_compact_support.2 (subset_tsupport w hθ)).2⟩
  have hwderiv : ∀ θ, HasDerivAt w (dw θ) θ := by
    intro θ
    rw [h.prior_derivative θ]
    exact (h.prior_C1.differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hwnorm : ∫ θ, w θ ∂PM ell u = 1 := by
    rw [← h.prior_probability, intervalIntegral.integral_of_le h.interval_nonempty.le]
    unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    rw [restrict_Ioc_eq_restrict_Icc]
  have hboundary : ∀ᵐ x ∂μ,
      w u * p u x * (T x - g u x) = 0 ∧
        w ell * p ell x * (T x - g ell x) = 0 := by
    filter_upwards [h.boundary_vanishes_ae] with x hx
    exact ⟨hx.2, hx.1⟩
  have hsensitivityInt : Integrable
      (Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField w p dg)
      ((PM ell u).prod μ) := by
    change Integrable
      (Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField w p dg)
      ((volume.restrict (Icc ell u)).prod μ)
    convert h.derivative_joint_integrable using 1
    ext z
    simp [Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField,
      Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
    ring
  have herrorSqInt : Integrable
      (Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w p g T)
      ((PM ell u).prod μ) := by
    change Integrable
      (Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w p g T)
      ((volume.restrict (Icc ell u)).prod μ)
    convert h.risk_joint_integrable using 1
    ext z
    simp [Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField,
      Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
    ring
  letI : IsFiniteMeasure (PM ell u) := by
    unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    infer_instance
  have hrisk : bayesJointIntegral μ ell u w p (fun θ x => (T x - g θ x) ^ 2) =
      ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w p g T z
        ∂((PM ell u).prod μ) := by
    calc
      _ = ∫ θ, ∫ x, (T x - g θ x) ^ 2 * p θ x * w θ ∂μ ∂PM ell u := by
        rw [bayesJointIntegral, intervalIntegral.integral_of_le h.interval_nonempty.le]
        unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
        rw [restrict_Ioc_eq_restrict_Icc]
      _ = _ := by
        rw [MeasureTheory.integral_prod _ herrorSqInt]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField,
          Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
        ring
  have hsensitivity : bayesJointIntegral μ ell u w p dg =
      ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField w p dg z
        ∂((PM ell u).prod μ) := by
    calc
      _ = ∫ θ, ∫ x, dg θ x * p θ x * w θ ∂μ ∂PM ell u := by
        rw [bayesJointIntegral, intervalIntegral.integral_of_le h.interval_nonempty.le]
        unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
        rw [restrict_Ioc_eq_restrict_Icc]
      _ = _ := by
        rw [MeasureTheory.integral_prod _ hsensitivityInt]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with θ
        apply MeasureTheory.integral_congr_ae
        filter_upwards with x
        simp [Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField,
          Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
        ring
  have hprior : priorInformation ell u w dw =
      Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation ell u w dw := by
    rw [priorInformation,
      Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation,
      intervalIntegral.integral_of_le h.interval_nonempty.le]
    rw [Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure,
      ← restrict_Ioc_eq_restrict_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    simp [Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore]
    split_ifs with hθ
    · field_simp
    · ring
  have hfisher : (∫ θ in ell..u, fisherInformation μ p dp θ * w θ) =
      ∫ θ, w θ *
        Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ
        ∂PM ell u := by
    rw [intervalIntegral.integral_of_le h.interval_nonempty.le]
    unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
    rw [restrict_Ioc_eq_restrict_Icc]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with θ
    have hFI : fisherInformation μ p dp θ =
        Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ := by
      rw [fisherInformation,
        Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      simp [Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore]
      split_ifs with hx
      · field_simp
      · ring
    rw [hFI, mul_comm]
  have hinfoPos : 0 <
      Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation ell u w dw +
        ∫ θ, w θ *
          Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ
          ∂PM ell u := by
    rw [← hprior, ← hfisher]
    exact h.total_information_positive
  have hvt :
      (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField
          w p dg z ∂((PM ell u).prod μ)) ^ 2 /
          (Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation ell u w dw +
            ∫ θ, w θ *
              Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ
              ∂PM ell u) ≤
        ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField w p g T z
          ∂((PM ell u).prod μ) := by
    letI : IsFiniteMeasure (PM ell u) := by
      unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      infer_instance
    have hmemIcc : ∀ᵐ θ ∂PM ell u, θ ∈ Icc ell u := by
      unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
      exact ae_restrict_mem measurableSet_Icc
    have hmemIoo : ∀ᵐ θ ∂PM ell u, θ ∈ Ioo ell u := by
      filter_upwards [hmemIcc,
        (by unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
            exact ae_restrict_of_ae (volume.ae_ne ell)),
        (by unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
            exact ae_restrict_of_ae (volume.ae_ne u))] with θ hθ hθell hθu
      exact ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθell), lt_of_le_of_ne hθ.2 hθu⟩
    have hpSections : ∀ᵐ x ∂μ, ∀ θ, θ ∈ Ioo ell u → 0 ≤ p θ x :=
      bayesianInformation_ae_section_nonnegative μ h.density_nonnegative h.likelihood_ac_ae
    have hpNonneg : ∀ᵐ z ∂((PM ell u).prod μ), 0 ≤ p z.1 z.2 := by
      have hx : ∀ᵐ z ∂((PM ell u).prod μ),
          ∀ θ, θ ∈ Ioo ell u → 0 ≤ p θ z.2 :=
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hpSections
      have hθ : ∀ᵐ z ∂((PM ell u).prod μ), z.1 ∈ Ioo ell u :=
        Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hmemIoo
      filter_upwards [hx, hθ] with z hxz hθz
      exact hxz z.1 hθz
    have hwzero : ∀ θ, w θ = 0 → dw θ = 0 := by
      intro θ hzero
      exact Causalean.Stat.Limit.ObservationDependentVanTrees.derivative_eq_zero_of_nonnegative_of_eq_zero
        h.prior_nonnegative (hwderiv θ) hzero
    have hpzero : ∀ᵐ z ∂((PM ell u).prod μ),
        p z.1 z.2 = 0 → dp z.1 z.2 = 0 := by
      have hx : ∀ᵐ z ∂((PM ell u).prod μ),
          ∀ θ, θ ∈ Ioo ell u → 0 ≤ p θ z.2 :=
        Measure.quasiMeasurePreserving_snd.tendsto_ae.eventually hpSections
      have hθ : ∀ᵐ z ∂((PM ell u).prod μ), z.1 ∈ Ioo ell u :=
        Measure.quasiMeasurePreserving_fst.tendsto_ae.eventually hmemIoo
      have hderiv : ∀ᵐ z ∂((PM ell u).prod μ),
          HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1 := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure,
          restrict_Ioo_eq_restrict_Icc] using h.likelihood_hasDerivAt_ae
      filter_upwards [hderiv, hx, hθ] with z hder hxz hθz
      intro hz
      have hmin : IsLocalMin (fun t => p t z.2) z.1 := by
        filter_upwards [Ioo_mem_nhds hθz.1 hθz.2] with t ht
        rw [hz]
        exact hxz t ht
      exact hmin.hasDerivAt_eq_zero hder
    have hdpSwap : ∀ᵐ z ∂(μ.prod (PM ell u)),
        HasDerivAt (fun t => p t z.1) (dp z.2 z.1) z.2 := by
      have hderiv : ∀ᵐ z ∂((PM ell u).prod μ),
          HasDerivAt (fun t => p t z.2) (dp z.1 z.2) z.1 := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure,
          restrict_Ioo_eq_restrict_Icc] using h.likelihood_hasDerivAt_ae
      have hz := Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually hderiv
      simpa [Prod.swap] using hz
    have hdgSwap : ∀ᵐ z ∂(μ.prod (PM ell u)),
        HasDerivAt (fun t => g t z.1) (dg z.2 z.1) z.2 := by
      have hderiv : ∀ᵐ z ∂((PM ell u).prod μ),
          HasDerivAt (fun t => g t z.2) (dg z.1 z.2) z.1 := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure,
          restrict_Ioo_eq_restrict_Icc] using h.target_hasDerivAt_ae
      have hz := Measure.measurePreserving_swap.quasiMeasurePreserving.tendsto_ae.eventually hderiv
      simpa [Prod.swap] using hz
    have hdpSections : ∀ᵐ x ∂μ, ∀ᵐ θ ∂PM ell u,
        HasDerivAt (fun t => p t x) (dp θ x) θ := by
      simpa using Measure.ae_ae_of_ae_prod hdpSwap
    have hdgSections : ∀ᵐ x ∂μ, ∀ᵐ θ ∂PM ell u,
        HasDerivAt (fun t => g t x) (dg θ x) θ := by
      simpa using Measure.ae_ae_of_ae_prod hdgSwap
    have hbalanceZero :
        ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
          w dw p dp g dg T z ∂((PM ell u).prod μ) = 0 := by
      have hbalanceInt : Integrable
          (Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
            w dw p dp g dg T) ((PM ell u).prod μ) := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure] using
          h.derivative_balance_joint_integrable
      rw [integral_prod_symm _ hbalanceInt]
      apply integral_eq_zero_of_ae
      filter_upwards [h.product_ac_ae, hboundary, hdpSections, hdgSections,
        hbalanceInt.prod_left_ae] with
          x hacx hboundaryx hdpx hdgx hintx
      let q : ℝ → ℝ := fun θ => w θ * p θ x * (T x - g θ x)
      have hqderiv : ∀ᵐ θ ∂PM ell u,
          HasDerivAt q
            (Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
              w dw p dp g dg T (θ, x)) θ := by
        filter_upwards [hdpx, hdgx] with θ hdpθ hdgθ
        have hm := ((hwderiv θ).mul hdpθ).mul (hdgθ.const_sub (T x))
        simp only [Pi.mul_apply] at hm
        have hfun : q = (w * (fun t => p t x)) * (fun t => T x - g t x) := by
          funext t
          rfl
        have hcoef :
            Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
                w dw p dp g dg T (θ, x) =
              (dw θ * p θ x + w θ * dp θ x) * (T x - g θ x) +
                w θ * p θ x * -dg θ x := by
          simp [Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField,
            Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
          ring
        rw [hfun, hcoef]
        exact hm
      calc
        (∫ θ, Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
            w dw p dp g dg T (θ, x) ∂PM ell u) =
            ∫ θ, deriv q θ ∂PM ell u := by
          apply integral_congr_ae
          filter_upwards [hqderiv] with θ hθ
          exact hθ.deriv.symm
        _ = ∫ θ in ell..u, deriv q θ := by
          unfold PM Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure
          rw [intervalIntegral.integral_of_le h.interval_nonempty.le,
            restrict_Ioc_eq_restrict_Icc]
        _ = q u - q ell := hacx.integral_deriv_eq_sub
        _ = 0 := by simp [q, hboundaryx.1, hboundaryx.2]
    have herrorSensitivity :
        (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField
          w dw p dp g T z ∂((PM ell u).prod μ)) =
          ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField
            w p dg z ∂((PM ell u).prod μ) := by
      have hre :
          (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField
            w dw p dp g dg T z ∂((PM ell u).prod μ)) =
          (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField
            w dw p dp g T z ∂((PM ell u).prod μ)) -
          ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField
            w p dg z ∂((PM ell u).prod μ) := by
        calc
          _ = ∫ z,
              Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField
                w dw p dp g T z -
              Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField
                w p dg z ∂((PM ell u).prod μ) := by
            apply integral_congr_ae
            filter_upwards [hpNonneg, hpzero] with z hpz hpzeroz
            rw [Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField_eq_numerator
              (h.prior_nonnegative z.1) hpz
                (hwzero z.1) hpzeroz]
            simp [Causalean.Stat.Limit.ObservationDependentVanTrees.derivativeBalanceField,
              Causalean.Stat.Limit.ObservationDependentVanTrees.sensitivityField,
              Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity]
            ring
          _ = _ := integral_sub h.error_score_joint_integrable hsensitivityInt
      rw [hbalanceZero] at hre
      linarith
    have hpzeroSections : ∀ᵐ θ ∂PM ell u,
        ∀ᵐ x ∂μ, p θ x = 0 → dp θ x = 0 := Measure.ae_ae_of_ae_prod hpzero
    have hpNonnegSections : ∀ᵐ θ ∂PM ell u,
        ∀ᵐ x ∂μ, 0 ≤ p θ x := Measure.ae_ae_of_ae_prod hpNonneg
    have hnormAE : ∀ᵐ θ ∂PM ell u, ∫ x, p θ x ∂μ = 1 := by
      filter_upwards [hmemIoo] with θ hθ
      exact h.density_probability θ hθ
    have hcenter : ∀ᵐ θ ∂PM ell u,
        ∫ x, Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
          p dp θ x * p θ x ∂μ = 0 := by
      filter_upwards [hmemIoo, hpzeroSections, hpNonnegSections] with θ hθ hz hn
      calc
        _ = ∫ x, dp θ x ∂μ := by
          apply integral_congr_ae
          filter_upwards [hz, hn] with x hzx hnx
          exact Causalean.Stat.Limit.ObservationDependentVanTrees.guarded_score_mul_density
            hnx hzx
        _ = 0 := h.differentiation_under_integral θ hθ
    have hinformation :
        (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField
          w dw p dp z ∂((PM ell u).prod μ)) =
          Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation ell u w dw +
            ∫ θ, w θ *
              Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ
              ∂PM ell u := by
      have hpriorJointInt : Integrable
          (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
            (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2)
          ((PM ell u).prod μ) := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure] using
          h.prior_score_joint_sq_integrable
      have hfisherJointInt : Integrable
          (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
            (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
              p dp z.1 z.2) ^ 2) ((PM ell u).prod μ) := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure] using
          h.fisher_score_joint_sq_integrable
      have hcrossInt : Integrable
          (fun z : ℝ × Ω => w z.1 * p z.1 z.2 *
            (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
              Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                p dp z.1 z.2)) ((PM ell u).prod μ) := by
        simpa [PM, Causalean.Stat.Limit.ObservationDependentVanTrees.parameterMeasure] using
          h.score_cross_joint_integrable
      have hexpand : ∀ᵐ z ∂((PM ell u).prod μ),
          Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField w dw p dp z =
            w z.1 * p z.1 z.2 *
                (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2 +
              (w z.1 * p z.1 z.2 *
                  (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                    p dp z.1 z.2) ^ 2 +
                2 * (w z.1 * p z.1 z.2 *
                  (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
                    Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                      p dp z.1 z.2))) := by
        filter_upwards [hpNonneg] with z hpz
        by_cases hwpos : 0 < w z.1
        · by_cases hppos : 0 < p z.1 z.2
          · simp [Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField,
              Causalean.Stat.Limit.ObservationDependentVanTrees.jointScore,
              Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity,
              Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore,
              Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore,
              hwpos, hppos, mul_pos]
            field_simp
            ring
          · have hpz : p z.1 z.2 = 0 := le_antisymm (le_of_not_gt hppos) hpz
            simp [Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField,
              Causalean.Stat.Limit.ObservationDependentVanTrees.jointScore,
              Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity, hpz]
        · have hwz : w z.1 = 0 :=
            le_antisymm (le_of_not_gt hwpos) (h.prior_nonnegative z.1)
          simp [Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField,
            Causalean.Stat.Limit.ObservationDependentVanTrees.jointScore,
            Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity, hwz]
      have hsplit :
          (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField
            w dw p dp z ∂((PM ell u).prod μ)) =
            (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2
              ∂((PM ell u).prod μ)) +
            (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                p dp z.1 z.2) ^ 2 ∂((PM ell u).prod μ)) +
            2 * (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
                Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                  p dp z.1 z.2) ∂((PM ell u).prod μ)) := by
        calc
          _ = ∫ z : ℝ × Ω,
              (w z.1 * p z.1 z.2 *
                (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2) +
              ((w z.1 * p z.1 z.2 *
                (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                  p dp z.1 z.2) ^ 2) +
                2 * (w z.1 * p z.1 z.2 *
                  (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
                    Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                      p dp z.1 z.2))) ∂((PM ell u).prod μ) := integral_congr_ae hexpand
          _ = (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
                (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2
                ∂((PM ell u).prod μ)) +
              ∫ z : ℝ × Ω,
                (w z.1 * p z.1 z.2 *
                  (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                    p dp z.1 z.2) ^ 2) +
                2 * (w z.1 * p z.1 z.2 *
                  (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
                    Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                      p dp z.1 z.2)) ∂((PM ell u).prod μ) :=
            integral_add hpriorJointInt
              (hfisherJointInt.add (hcrossInt.const_mul 2))
          _ = _ := by
            rw [integral_add hfisherJointInt (hcrossInt.const_mul 2), integral_const_mul]
            ring
      have hpriorEval :
          (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1) ^ 2
              ∂((PM ell u).prod μ)) =
            Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation ell u w dw := by
        rw [integral_prod _ hpriorJointInt]
        unfold Causalean.Stat.Limit.ObservationDependentVanTrees.priorInformation
        apply integral_congr_ae
        filter_upwards [hnormAE] with θ hnormθ
        calc
          _ = (w θ *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw θ) ^ 2) *
                ∫ x, p θ x ∂μ := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = _ := by rw [hnormθ]; ring
      have hfisherEval :
          (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                p dp z.1 z.2) ^ 2 ∂((PM ell u).prod μ)) =
            ∫ θ, w θ *
              Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation μ p dp θ
              ∂PM ell u := by
        rw [integral_prod _ hfisherJointInt]
        apply integral_congr_ae
        filter_upwards with θ
        unfold Causalean.Stat.Limit.ObservationDependentVanTrees.fisherInformation
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        ring
      have hcrossEval :
          (∫ z : ℝ × Ω, w z.1 * p z.1 z.2 *
              (Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw z.1 *
                Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                  p dp z.1 z.2) ∂((PM ell u).prod μ)) = 0 := by
        rw [integral_prod _ hcrossInt]
        apply integral_eq_zero_of_ae
        filter_upwards [hcenter] with θ hcenterθ
        calc
          _ = (w θ *
              Causalean.Stat.Limit.ObservationDependentVanTrees.priorScore w dw θ) *
                ∫ x, Causalean.Stat.Limit.ObservationDependentVanTrees.likelihoodScore
                  p dp θ x * p θ x ∂μ := by
            rw [← integral_const_mul]
            apply integral_congr_ae
            filter_upwards with x
            ring
          _ = 0 := by rw [hcenterθ, mul_zero]
      rw [hsplit, hpriorEval, hfisherEval, hcrossEval]
      ring
    have hcs :
        (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField
          w dw p dp g T z ∂((PM ell u).prod μ)) ^ 2 ≤
          (∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField
            w p g T z ∂((PM ell u).prod μ)) *
          ∫ z, Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField
            w dw p dp z ∂((PM ell u).prod μ) := by
      simpa only [Causalean.Stat.Limit.ObservationDependentVanTrees.errorScoreField,
          Causalean.Stat.Limit.ObservationDependentVanTrees.errorSqField,
          Causalean.Stat.Limit.ObservationDependentVanTrees.scoreSqField] using
        (Causalean.Stat.Limit.ObservationDependentVanTrees.weighted_integral_mul_sq_le
          (μ := (PM ell u).prod μ)
          (q := Causalean.Stat.Limit.ObservationDependentVanTrees.jointDensity w p)
          (f := fun z : ℝ × Ω => T z.2 - g z.1 z.2)
          (s := Causalean.Stat.Limit.ObservationDependentVanTrees.jointScore w dw p dp)
          (by filter_upwards [hpNonneg] with z hpz
              exact mul_nonneg (h.prior_nonnegative z.1) hpz)
          herrorSqInt.aestronglyMeasurable h.joint_score_sq_integrable.aestronglyMeasurable
          h.error_score_joint_integrable.aestronglyMeasurable herrorSqInt
          h.joint_score_sq_integrable h.error_score_joint_integrable)
    apply (div_le_iff₀ hinfoPos).2
    rw [← hinformation, ← herrorSensitivity]
    exact hcs
  rw [hrisk, hsensitivity, hprior, hfisher]
  exact hvt

end CausalSmith.Experimentation.MultiarmSecondorderMinimaxFrontier
