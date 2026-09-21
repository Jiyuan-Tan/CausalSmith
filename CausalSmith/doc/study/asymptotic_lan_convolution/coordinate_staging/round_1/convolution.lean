import Causalean.Estimation.Efficiency.AsymptoticLanConvolution.ConvolutionCore

/-!
# Scalar convolution theorem for regular LAN estimators

This module derives the scalar Hájek--Le Cam convolution conclusion from LAN, regularity under local alternatives, and a canonical-gradient representation.  It identifies every regular estimator limit as an efficient centered Gaussian law convolved with an independent residual law.
-/

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory ProbabilityTheory Topology
open scoped RealInnerProductSpace

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

private lemma analyticOnNhd_weightedExp
    {S : Type*} [MeasurableSpace S] {μ : Measure S} (X Y : S → ℝ)
    (hX : Measurable X) (hY : Measurable Y)
    (hexp : ∀ s : ℝ, Integrable (fun ω => Real.exp (s * Y ω)) μ) (t : ℝ) :
    AnalyticOnNhd ℂ
      (fun z => ∫ ω, Complex.exp ((t * X ω : ℂ) * Complex.I) *
        Complex.exp (z * Y ω) ∂μ) Set.univ := by
  apply DifferentiableOn.analyticOnNhd
  · rw [differentiableOn_univ]
    intro z
    let r : ℝ := 1
    have hr : 0 < r := by simp [r]
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (bound := fun ω => |Y ω| * Real.exp (z.re * Y ω + r / 2 * |Y ω|))
      (F := fun z ω => Complex.exp ((t * X ω : ℂ) * Complex.I) *
        Complex.exp (z * Y ω))
      (F' := fun z ω => Complex.exp ((t * X ω : ℂ) * Complex.I) *
        (Complex.exp (z * Y ω) * (Y ω : ℂ)))
      (Metric.ball_mem_nhds _ (half_pos hr)) ?_ ?_ ?_ ?_ ?_ ?_).2.differentiableAt
    · exact .of_forall fun z => by fun_prop
    · refine (hexp z.re).mono' (by fun_prop) ?_
      filter_upwards with ω
      simp [Complex.norm_exp]
    · fun_prop
    · refine ae_of_all _ fun ω z' hz' => ?_
      simp only [Metric.mem_ball, dist_eq_norm] at hz'
      simp [Complex.norm_exp]
      rw [mul_comm (Real.exp _) |Y ω|]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      have hz_eq : z' = z + (z' - z) := by abel
      rw [hz_eq, Complex.add_re, add_mul, add_le_add_iff_left]
      refine (le_abs_self _).trans ?_
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact (Complex.abs_re_le_norm _).trans (le_of_lt hz')
    · simpa [r, add_assoc] using
        (integrable_pow_abs_mul_exp_add_of_integrable_exp_mul
          (hexp (z.re + r)) (hexp (z.re - r)) (by positivity) (by norm_num [r]) 1)
    · exact ae_of_all _ fun ω z' _ => by
        have hzmul : HasDerivAt (fun q : ℂ => q * (Y ω : ℂ)) (Y ω : ℂ) z' := by
          simpa using (hasDerivAt_id z').mul_const (Y ω : ℂ)
        have hexp' := (Complex.hasDerivAt_exp (z' * (Y ω : ℂ))).comp z' hzmul
        exact hexp'.const_mul (Complex.exp ((t * X ω : ℂ) * Complex.I))
  · exact isOpen_univ

private lemma weightedExp_eq_of_eq_real
    (F : ℂ → ℂ) (v t : ℝ) (c : ℂ)
    (hF : AnalyticOnNhd ℂ F Set.univ)
    (hreal : ∀ q : ℝ, F q =
      Complex.exp ((v / 2 : ℂ) * (q : ℂ) ^ 2 +
        ((t * v : ℂ) * Complex.I) * q) * c) :
    ∀ z : ℂ, F z =
      Complex.exp ((v / 2 : ℂ) * z ^ 2 + ((t * v : ℂ) * Complex.I) * z) * c := by
  let G : ℂ → ℂ := fun z =>
    Complex.exp ((v / 2 : ℂ) * z ^ 2 + ((t * v : ℂ) * Complex.I) * z) * c
  have hG : AnalyticOnNhd ℂ G Set.univ := by
    apply DifferentiableOn.analyticOnNhd
    · fun_prop
    · exact isOpen_univ
  have hreal' : ∃ᶠ (x : ℝ) in 𝓝[≠] 0, F x = G x := by
    exact .of_forall fun x => hreal x
  rw [frequently_iff_seq_forall] at hreal'
  obtain ⟨xs, hx_tendsto, hx_eq⟩ := hreal'
  have hfreq : ∃ᶠ (z : ℂ) in 𝓝[≠] (0 : ℂ), F z = G z := by
    rw [frequently_iff_seq_forall]
    refine ⟨fun n => xs n, ?_, fun n => ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · exact Complex.continuous_ofReal.continuousAt.tendsto.comp hx_tendsto.1
      · simpa using hx_tendsto.2
    · simpa [G] using hx_eq n
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG isPreconnected_univ
    (z₀ := (0 : ℂ)) (by simp) hfreq
  intro z
  exact heq (Set.mem_univ z)
/-- Given [local asymptotic normality](hyp:lan), [a joint weak subsequential limit](hyp:joint), [measurability of the estimator under local laws](hyp:hlocalMeasurable), [likelihood-ratio normalization](hyp:hnormalized), and [a fixed Fourier frequency and local direction](hyp:t,h), [the estimator characteristic function under the local law converges to its exponentially tilted joint-limit integral](goal). -/
theorem lan_tilted_charFun_tendsto_of_jointWeakSubsequence
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H}
    {statistic : (n : ℕ) → Ω n → ℝ} {limitLaw : Measure ℝ}
    {scoreLimit : Measure H} {jointLaw : Measure (ℝ × H)} {subsequence : ℕ → ℕ}
    (lan : IsLAN E centralSequence information scoreLimit)
    (joint : JointWeakSubsequence subsequence E.baseLaw statistic centralSequence
      limitLaw scoreLimit jointLaw)
    (hlocalMeasurable : ∀ n h, AEMeasurable (statistic n) (E.localLaw n h))
    (hnormalized : ∀ h : H,
      Tendsto (fun n => ∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n)
        atTop (𝓝 1)) :
    ∀ (t : ℝ) (h : H),
      Tendsto (fun n => ∫ ω, Complex.exp ((t * statistic (subsequence n) ω : ℂ) *
          Complex.I) ∂E.localLaw (subsequence n) h) atTop
        (𝓝 (∫ z, Complex.exp ((t * z.1 : ℂ) * Complex.I) *
          Complex.exp ((inner ℝ h z.2 - (1 / 2 : ℝ) * information h h : ℝ))
            ∂jointLaw)) := by
  intro t h
  let Y : (n : ℕ) → Ω (subsequence n) → ℝ × H := fun n ω =>
    (statistic (subsequence n) ω, centralSequence (subsequence n) ω)
  let a : C(ℝ × H, ℝ) :=
    ⟨fun z => inner ℝ h z.2 - (1 / 2 : ℝ) * information h h, by fun_prop⟩
  let f : BoundedContinuousFunction (ℝ × H) ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z => Complex.exp ((t * z.1 : ℂ) * Complex.I))
      (by fun_prop) 1 (fun z => by simp [Complex.norm_exp])
  let R : (n : ℕ) → Ω (subsequence n) → ℝ := fun n ω =>
    E.logLikelihoodRatio (subsequence n) h ω -
      inner ℝ h (centralSequence (subsequence n) ω) +
        (1 / 2 : ℝ) * information h h
  have hstatBase (n : ℕ) : AEMeasurable (statistic n) (E.baseLaw n) := by
    simpa [E.local_zero] using hlocalMeasurable n (0 : H)
  have hY : WeaklyConverges (fun n => E.baseLaw (subsequence n)) Y jointLaw := by
    refine ⟨fun n => (hstatBase _).prodMk (lan.central_measurable _), ?_⟩
    intro g
    exact joint.converges g
  have hR : TendstoInProbability (fun n => E.baseLaw (subsequence n)) R 0 := by
    intro ε hε
    exact (lan.expansion h ε hε).comp joint.subsequence_strictMono.tendsto_atTop
  have hllr (n : ℕ) :
      AEMeasurable (E.logLikelihoodRatio n h) (E.baseLaw n) := by
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    have hr : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    unfold LocalExperiment.logLikelihoodRatio
    exact (Measurable.ite (hr (measurableSet_singleton 0)) measurable_const hr.log).aemeasurable
  have hRmeas (n : ℕ) : AEMeasurable (R n) (E.baseLaw (subsequence n)) := by
    dsimp only [R]
    have hi : Continuous (fun z : H => inner ℝ h z) := by fun_prop
    exact ((hllr _).sub
      (hi.aemeasurable.comp_aemeasurable (lan.central_measurable _))).add aemeasurable_const
  have hrowIntegrable (n : ℕ) :
      Integrable (fun ω => Real.exp (E.logLikelihoodRatio n h ω)) (E.baseLaw n) := by
    letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hr_int : Integrable r (E.baseLaw n) := by
      simpa only [integrableOn_univ] using
        (Measure.integrableOn_toReal_rnDeriv
          (μ := E.localLaw n h) (ν := E.baseLaw n) (s := Set.univ)
          (measure_ne_top _ _))
    apply (hr_int.add (integrable_const (Real.exp (-(n : ℝ))))).mono'
      (hllr n).exp.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      change Real.exp (E.logLikelihoodRatio n h ω) ≤ r ω + Real.exp (-(n : ℝ))
      unfold LocalExperiment.logLikelihoodRatio
      dsimp only
      by_cases hz : r ω = 0
      · rw [if_pos hz, hz, zero_add]
      · rw [if_neg hz, Real.exp_log
            (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hv : 0 ≤ information h h := lan.information_nonnegative h
  have hproj : Measure.map (fun z => inner ℝ h z) scoreLimit =
      gaussianReal 0 (information h h).toNNReal := by
    letI : IsProbabilityMeasure scoreLimit := lan.gaussian_probability
    apply Measure.ext_of_charFun
    funext s
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    have heq :
        (∫ x, Complex.exp ((inner ℝ (inner ℝ h x) s : ℂ) * Complex.I) ∂scoreLimit) =
          charFun scoreLimit (s • h) := by
      rw [charFun_apply]
      congr with x
      congr 2
      simp [inner_smul_right, real_inner_comm]
    rw [heq, lan.gaussian_charFun (s • h), charFun_gaussianReal]
    simp [Real.coe_toNNReal _ hv, map_smul]
    congr 1
    ring
  have hscoreIntegrable : Integrable
      (fun y => Real.exp (inner ℝ h y - (1 / 2 : ℝ) * information h h)) scoreLimit := by
    have hg : Integrable
        (fun x => Real.exp (x - (1 / 2 : ℝ) * information h h))
        (gaussianReal 0 (information h h).toNNReal) := by
      convert (integrable_exp_mul_gaussianReal (μ := 0)
        (v := (information h h).toNNReal) 1).mul_const
          (Real.exp (-(1 / 2 : ℝ) * information h h)) using 1
      funext x
      rw [Real.exp_sub]
      simp only [one_mul, div_eq_mul_inv]
      rw [← Real.exp_neg]
      congr 2
      ring
    rw [← hproj] at hg
    exact (integrable_map_measure
      (f := fun y : H => inner ℝ h y)
      (g := fun x : ℝ => Real.exp (x - (1 / 2 : ℝ) * information h h))
      (by fun_prop) (by fun_prop)).mp hg
  have hlimitIntegrable : Integrable (fun z => Real.exp (a z)) jointLaw := by
    rw [show (fun z => Real.exp (a z)) =
        (fun y => Real.exp (inner ℝ h y - (1 / 2 : ℝ) * information h h)) ∘ Prod.snd
      by rfl]
    have hs := hscoreIntegrable
    rw [← joint.snd_marginal] at hs
    exact (integrable_map_measure
      (f := Prod.snd) (g := fun y : H =>
        Real.exp (inner ℝ h y - (1 / 2 : ℝ) * information h h))
      (by fun_prop) (by fun_prop)).mp hs
  have hlimitIntegral : (∫ z, Real.exp (a z) ∂jointLaw) = 1 := by
    calc
      (∫ z, Real.exp (a z) ∂jointLaw) =
          ∫ y, Real.exp (inner ℝ h y - (1 / 2 : ℝ) * information h h) ∂scoreLimit := by
            rw [← joint.snd_marginal, integral_map (by fun_prop) (by fun_prop)]
            rfl
      _ = ∫ x, Real.exp x ∂lanLogLikelihoodLimit information scoreLimit h := by
        unfold lanLogLikelihoodLimit
        rw [integral_map (by fun_prop) (by fun_prop)]
      _ = 1 := integral_exp_lanLogLikelihoodLimit
        lan.gaussian_probability lan.gaussian_charFun h
  have hweighted := integral_boundedContinuous_mul_exp_tendsto_of_normalized
    a f (fun n => E.base_probability (subsequence n)) joint.probability hY hR hRmeas
    (fun n => by
      convert hrowIntegrable (subsequence n) using 1
      funext ω
      dsimp only [a, Y, R, ContinuousMap.coe_mk]
      congr 1
      ring)
    hlimitIntegrable (by
      rw [hlimitIntegral]
      convert (hnormalized h).comp joint.subsequence_strictMono.tendsto_atTop using 1
      funext n
      congr 1 with ω
      dsimp only [a, Y, R, ContinuousMap.coe_mk]
      congr 1
      ring)
  have hφlocal (n : ℕ) : AEMeasurable
      (fun ω => Complex.exp ((t * statistic n ω : ℂ) * Complex.I))
      (E.localLaw n h) := by
    fun_prop
  have hφbase (n : ℕ) : AEMeasurable
      (fun ω => Complex.exp ((t * statistic n ω : ℂ) * Complex.I))
      (E.baseLaw n) := by
    fun_prop
  have hreplace :=
    (local_integral_sub_exp_logLikelihoodRatio_integral_tendsto_zero (E := E) h
      (φ := fun n ω => Complex.exp ((t * statistic n ω : ℂ) * Complex.I))
      hφlocal hφbase
      ⟨1, by positivity, fun n ω => by simp [Complex.norm_exp]⟩ (hnormalized h)).comp
        joint.subsequence_strictMono.tendsto_atTop
  convert hreplace.add hweighted using 1 <;> simp [f, Y, a, R]

/-- Along any joint weak subsequence of the base-law estimator and central sequence, LAN and
regularity identify the exponentially tilted characteristic function.  This is the scalar
Le Cam third-lemma step; in particular, contiguity and control of the unbounded likelihood
weight are conclusions of LAN rather than extra assumptions. -/
theorem lan_tilt_identity_of_jointWeakSubsequence
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H}
    {statistic : (n : ℕ) → Ω n → ℝ} {targetDerivative : H →ₗ[ℝ] ℝ}
    {limitLaw : Measure ℝ} {scoreLimit : Measure H} {jointLaw : Measure (ℝ × H)}
    {subsequence : ℕ → ℕ}
    (lan : IsLAN E centralSequence information scoreLimit)
    (regular : IsRegularEstimator E statistic targetDerivative limitLaw)
    (joint : JointWeakSubsequence subsequence E.baseLaw statistic centralSequence
      limitLaw scoreLimit jointLaw) :
    ∀ (t : ℝ) (h : H),
      ∫ z, Complex.exp ((t * z.1 : ℂ) * Complex.I) *
          Complex.exp ((inner ℝ h z.2 - (1 / 2 : ℝ) * information h h : ℝ)) ∂jointLaw =
        Complex.exp ((t * targetDerivative h : ℂ) * Complex.I) * charFun limitLaw t := by
  intro t h
  have htilt := lan_tilted_charFun_tendsto_of_jointWeakSubsequence
    lan joint regular.measurable (fun g => lan_likelihoodRatio_integral_tendsto_one lan g) t h
  let localPM : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨Measure.map (fun ω => statistic n ω - targetDerivative h) (E.localLaw n h),
      by
        letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
        exact Measure.isProbabilityMeasure_map ((regular.regular h).1 n)⟩
  let limitPM : ProbabilityMeasure ℝ := ⟨limitLaw, regular.limit_probability⟩
  have hPM : Tendsto localPM atTop (𝓝 limitPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro g
    simpa only [localPM, limitPM, ProbabilityMeasure.coe_mk,
      integral_map ((regular.regular h).1 _) g.continuous.aestronglyMeasurable] using
        (regular.regular h).2 g
  let g : BoundedContinuousFunction ℝ ℂ :=
    BoundedContinuousFunction.ofNormedAddCommGroup
      (fun x => Complex.exp ((t * (x + targetDerivative h) : ℂ) * Complex.I))
      (by fun_prop) 1 (fun x => by simp [Complex.norm_exp])
  have hg :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hPM g
  have hlocal : Tendsto (fun n => ∫ ω,
      Complex.exp ((t * statistic n ω : ℂ) * Complex.I) ∂E.localLaw n h) atTop
      (𝓝 (Complex.exp ((t * targetDerivative h : ℂ) * Complex.I) *
        charFun limitLaw t)) := by
    convert hg using 1
    · funext n
      rw [show (localPM n : Measure ℝ) =
          Measure.map (fun ω => statistic n ω - targetDerivative h) (E.localLaw n h) from rfl,
        integral_map ((regular.regular h).1 n) g.continuous.aestronglyMeasurable]
      congr 1 with ω
      simp only [g, BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      congr 1
      push_cast
      ring
    · simp only [limitPM, ProbabilityMeasure.coe_mk, g,
        BoundedContinuousFunction.coe_ofNormedAddCommGroup]
      rw [charFun_apply, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        simp only
        rw [← Complex.exp_add]
        congr 1
        simp
        ring
  exact tendsto_nhds_unique htilt
    (hlocal.comp joint.subsequence_strictMono.tendsto_atTop)

/-- LAN, convergence of the estimator at the base law, and regularity under every fixed local
alternative produce a joint subsequential limit satisfying the Gaussian-shift tilt identity.
The tightness needed to choose a joint limit follows from the two convergent marginals in finite
dimension. -/
theorem exists_regularLANJointLimit
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H}
    {statistic : (n : ℕ) → Ω n → ℝ} {targetDerivative : H →ₗ[ℝ] ℝ}
    {limitLaw : Measure ℝ} {scoreLimit : Measure H}
    (lan : IsLAN E centralSequence information scoreLimit)
    (regular : IsRegularEstimator E statistic targetDerivative limitLaw) :
    ∃ jointLaw : Measure (ℝ × H),
      RegularLANJointLimit information targetDerivative limitLaw scoreLimit jointLaw := by
  have hbase : WeaklyConverges E.baseLaw statistic limitLaw := by
    simpa [E.local_zero] using regular.regular (0 : H)
  obtain ⟨jointLaw, subsequence, joint⟩ := exists_jointWeakSubsequence
    E.base_probability regular.limit_probability lan.gaussian_probability
    hbase lan.central_converges
  refine ⟨jointLaw, ?_⟩
  exact
    { probability := joint.probability
      fst_marginal := joint.fst_marginal
      snd_marginal := joint.snd_marginal
      tilt_identity := lan_tilt_identity_of_jointWeakSubsequence lan regular joint }

/-- The Gaussian-shift tilt identity and a canonical-gradient representer imply that the scalar
estimator marginal is the convolution of the efficient centered Gaussian law with a residual
probability law.  This is the limit-experiment form of the convolution argument. -/
theorem jointLimit_convolution_factorization
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {information : LinearMap.BilinForm ℝ H} {targetDerivative : H →ₗ[ℝ] ℝ}
    {scoreMap : H →ₗ[ℝ] K} {gradient : K} {limitLaw : Measure ℝ} {scoreLimit : Measure H}
    {jointLaw : Measure (ℝ × H)}
    (hscoreProb : IsProbabilityMeasure scoreLimit)
    (hscoreChar : ∀ t : H,
      charFun scoreLimit t = Complex.exp (-((information t t : ℂ) / 2)))
    (joint : RegularLANJointLimit information targetDerivative limitLaw scoreLimit jointLaw)
    (canonical : CanonicalGradientPairing information targetDerivative scoreMap gradient) :
    ∃ residualLaw : Measure ℝ, IsProbabilityMeasure residualLaw ∧
      limitLaw = (efficientGaussianLaw gradient).conv residualLaw := by
  rcases canonical.gradient_mem_range with ⟨a, ha⟩
  let X : ℝ × H → ℝ := Prod.fst
  let Y : ℝ × H → ℝ := fun z => inner ℝ a z.2
  let v : ℝ := ‖gradient‖ ^ 2
  letI : IsProbabilityMeasure scoreLimit := hscoreProb
  letI : IsProbabilityMeasure jointLaw := joint.probability
  have hcoord : Measure.map (fun z : H => inner ℝ a z) scoreLimit =
      efficientGaussianLaw gradient := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    have heq : (∫ x : H, Complex.exp ((t * inner ℝ a x : ℂ) * Complex.I) ∂scoreLimit) =
        charFun scoreLimit (t • a) := by
      rw [charFun_apply]
      congr 1
      funext x
      congr 1
      norm_cast
      rw [real_inner_comm, inner_smul_right]
    rw [heq, hscoreChar]
    unfold efficientGaussianLaw
    rw [ProbabilityTheory.charFun_gaussianReal]
    rw [canonical.information_eq_inner]
    simp [ha, norm_smul, Real.norm_eq_abs]
    congr 1
    norm_cast
    rw [mul_pow, sq_abs]
    ring
  have hYmap : Measure.map Y jointLaw = efficientGaussianLaw gradient := by
    calc
      Measure.map Y jointLaw =
          Measure.map (fun z : H => inner ℝ a z) (Measure.map Prod.snd jointLaw) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
      _ = Measure.map (fun z : H => inner ℝ a z) scoreLimit := by
        rw [joint.snd_marginal]
      _ = efficientGaussianLaw gradient := hcoord
  have hexp (q : ℝ) : Integrable (fun z => Real.exp (q * Y z)) jointLaw := by
    have h := ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := (‖gradient‖ ^ 2).toNNReal) q
    change Integrable (fun x => Real.exp (q * x)) (efficientGaussianLaw gradient) at h
    rw [← hYmap] at h
    exact h.comp_aemeasurable (by fun_prop)
  let F : ℝ → ℂ → ℂ := fun t z => ∫ w,
    Complex.exp ((t * X w : ℂ) * Complex.I) * Complex.exp (z * Y w) ∂jointLaw
  have hFanalytic (t : ℝ) : AnalyticOnNhd ℂ (F t) Set.univ := by
    exact analyticOnNhd_weightedExp X Y (by fun_prop) (by fun_prop) hexp t
  have hreal (t q : ℝ) : F t q =
      Complex.exp ((v / 2 : ℂ) * (q : ℂ) ^ 2 +
        ((t * v : ℂ) * Complex.I) * q) * charFun limitLaw t := by
    have ht := joint.tilt_identity t (q • a)
    rw [canonical.information_eq_inner, canonical.derivative_eq_inner] at ht
    simp [ha, inner_smul_left, inner_smul_right] at ht
    have hqnorm : ‖q • gradient‖ ^ 2 = q ^ 2 * v := by
      simp [v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hqnormc : (‖q • gradient‖ ^ 2 : ℂ) = ((q ^ 2 * v : ℝ) : ℂ) := by
      exact_mod_cast hqnorm
    rw [hqnormc] at ht
    simp_rw [Complex.exp_sub] at ht
    have hc : Complex.exp ((2 : ℂ)⁻¹ * ((q ^ 2 * v : ℝ) : ℂ)) =
        Complex.exp (((q ^ 2 * v : ℝ) : ℂ) / 2) := by
      congr 1
      ring
    rw [hc] at ht
    simp only [div_eq_mul_inv, mul_assoc] at ht
    have ht' : (∫ z : ℝ × H, Complex.exp ((t * z.1 : ℂ) * Complex.I) *
          Complex.exp ((q : ℂ) * inner ℝ a z.2) ∂jointLaw) *
          (Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹))⁻¹ =
        Complex.exp ((t * (q * ‖gradient‖ ^ 2) : ℂ) * Complex.I) *
          charFun limitLaw t := by
      rw [← integral_mul_const]
      simpa only [mul_assoc] using ht
    dsimp [F, X, Y]
    calc
      (∫ w : ℝ × H, Complex.exp ((t * w.1 : ℂ) * Complex.I) *
          Complex.exp ((q : ℂ) * inner ℝ a w.2) ∂jointLaw) =
          ((∫ w : ℝ × H, Complex.exp ((t * w.1 : ℂ) * Complex.I) *
            Complex.exp ((q : ℂ) * inner ℝ a w.2) ∂jointLaw) *
            (Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹))⁻¹) *
            Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹) := by
              rw [mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), mul_one]
      _ = (Complex.exp ((t * (q * ‖gradient‖ ^ 2) : ℂ) * Complex.I) *
            charFun limitLaw t) *
            Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹) := by
              rw [ht']
      _ = (Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹) *
            Complex.exp ((t * (q * ‖gradient‖ ^ 2) : ℂ) * Complex.I)) *
            charFun limitLaw t := by ring
      _ = Complex.exp (((q ^ 2 * v : ℝ) : ℂ) * (2 : ℂ)⁻¹ +
            (t * (q * ‖gradient‖ ^ 2) : ℂ) * Complex.I) * charFun limitLaw t := by
              rw [Complex.exp_add]
      _ = Complex.exp ((v / 2 : ℂ) * (q : ℂ) ^ 2 +
            ((t * v : ℂ) * Complex.I) * q) * charFun limitLaw t := by
              congr 2
              push_cast
              simp [v]
              ring
  have hcomplex (t : ℝ) (z : ℂ) : F t z =
      Complex.exp ((v / 2 : ℂ) * z ^ 2 + ((t * v : ℂ) * Complex.I) * z) *
        charFun limitLaw t :=
    weightedExp_eq_of_eq_real (F t) v t (charFun limitLaw t) (hFanalytic t) (hreal t) z
  let R : ℝ × H → ℝ := fun w => X w - Y w
  let residualLaw : Measure ℝ := Measure.map R jointLaw
  have hRchar (t : ℝ) : charFun residualLaw t =
      Complex.exp ((v / 2 : ℂ) * (t : ℂ) ^ 2) * charFun limitLaw t := by
    rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop)]
    have hc := hcomplex t ((-t : ℂ) * Complex.I)
    dsimp [F, R, residualLaw, X, Y] at hc ⊢
    convert hc using 1
    · apply integral_congr_ae
      filter_upwards with w
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · congr 1
      ring_nf
      rw [Complex.I_sq]
      ring
  have hfactor (s t : ℝ) :
      (∫ w, Complex.exp (((s * Y w + t * R w : ℝ) : ℂ) * Complex.I) ∂jointLaw) =
        charFun (Measure.map Y jointLaw) s * charFun residualLaw t := by
    have hc := hcomplex t (((s - t : ℝ) : ℂ) * Complex.I)
    rw [hYmap]
    unfold efficientGaussianLaw
    rw [ProbabilityTheory.charFun_gaussianReal, hRchar]
    dsimp [F, R, X, Y] at hc ⊢
    convert hc using 1
    · apply integral_congr_ae
      filter_upwards with w
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    · simp [v]
      rw [← mul_assoc, ← Complex.exp_add]
      congr 2
      ring_nf
      rw [Complex.I_sq]
      ring
  have hIndep : IndepFun Y R jointLaw := by
    rw [indepFun_iff_charFun_prod (by fun_prop) (by fun_prop)]
    intro p
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    simpa [WithLp.prod_inner_apply] using hfactor p.ofLp.1 p.ofLp.2
  have hresidualProb : IsProbabilityMeasure residualLaw := by
    dsimp [residualLaw]
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  refine ⟨residualLaw, hresidualProb, ?_⟩
  have hadd := hIndep.map_add_eq_map_conv_map (by fun_prop) (by fun_prop)
  calc
    limitLaw = Measure.map X jointLaw := by
      simpa [X] using joint.fst_marginal.symm
    _ = Measure.map (Y + R) jointLaw := by
      congr 1
      funext w
      simp [R]
    _ = Measure.map Y jointLaw ∗ Measure.map R jointLaw := hadd
    _ = efficientGaussianLaw gradient ∗ residualLaw := by rw [hYmap]

/-- In a finite-dimensional experiment with [local asymptotic normality](hyp:lan), [a scalar estimator regular under each fixed local alternative](hyp:regular), and [a canonical-gradient representation of its target derivative](hyp:canonical), [the common estimator limit is the efficient centered Gaussian law convolved with a residual probability law](goal). -/
theorem regular_convolution_limit
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H}
    {statistic : (n : ℕ) → Ω n → ℝ} {targetDerivative : H →ₗ[ℝ] ℝ}
    {scoreMap : H →ₗ[ℝ] K} {gradient : K} {limitLaw : Measure ℝ}
    {scoreLimit : Measure H}
    (lan : IsLAN E centralSequence information scoreLimit)
    (regular : IsRegularEstimator E statistic targetDerivative limitLaw)
    (canonical : CanonicalGradientPairing information targetDerivative scoreMap gradient) :
    ∃ residualLaw : Measure ℝ, IsProbabilityMeasure residualLaw ∧
      limitLaw = (efficientGaussianLaw gradient).conv residualLaw := by
  obtain ⟨jointLaw, joint⟩ := exists_regularLANJointLimit lan regular
  exact jointLimit_convolution_factorization lan.gaussian_probability
    lan.gaussian_charFun joint canonical

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
