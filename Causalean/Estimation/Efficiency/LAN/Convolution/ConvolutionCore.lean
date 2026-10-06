/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Causalean.Estimation.Efficiency.LAN.Convolution.ExponentialTilt
public import Causalean.Estimation.Efficiency.LAN.Convolution.LikelihoodNormalization
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Joint weak limits for LAN experiments

This module supplies the compactness, likelihood-normalization, and Gaussian-limit ingredients
used in the scalar Hájek--Le Cam convolution argument.  The resulting exponential-tilt identity
and convolution factorization are completed in `Convolution`.
-/

@[expose] public section

namespace Causalean.Estimation.Efficiency.AsymptoticLanConvolution

open Filter MeasureTheory ProbabilityTheory Topology
open scoped RealInnerProductSpace

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]

/-- The efficient scalar Gaussian law associated with a canonical gradient is the centered
normal distribution with variance equal to the squared norm of that gradient. -/
noncomputable def efficientGaussianLaw
    {K : Type*} [NormedAddCommGroup K] (gradient : K) : Measure ℝ :=
  gaussianReal 0 (‖gradient‖ ^ 2).toNNReal

/-- The efficient Gaussian law is a probability measure. -/
instance efficientGaussianLaw_probability
    {K : Type*} [NormedAddCommGroup K] (gradient : K) :
    IsProbabilityMeasure (efficientGaussianLaw gradient) := by
  unfold efficientGaussianLaw
  infer_instance

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

/-- A joint weak subsequential limit couples two row-indexed statistics whose marginal laws
converge.  The selected indices are strictly increasing, the joint laws converge against every
bounded continuous test function, and the two marginals of the limit are the prescribed laws.

This is the compactness layer used before any likelihood-ratio or LAN argument. -/
structure JointWeakSubsequence
    (subsequence : ℕ → ℕ)
    (P : (n : ℕ) → Measure (Ω n))
    (statistic : (n : ℕ) → Ω n → ℝ) (centralSequence : (n : ℕ) → Ω n → H)
    (limitLaw : Measure ℝ) (scoreLimit : Measure H) (jointLaw : Measure (ℝ × H)) : Prop where
  /-- The selected indices are strictly increasing. -/
  subsequence_strictMono : StrictMono subsequence
  /-- The joint limit has total mass one. -/
  probability : IsProbabilityMeasure jointLaw
  /-- The joint pushforward laws converge weakly along the selected indices. -/
  converges : ∀ f : BoundedContinuousFunction (ℝ × H) ℝ,
    Tendsto (fun n => ∫ ω,
      f (statistic (subsequence n) ω, centralSequence (subsequence n) ω)
        ∂P (subsequence n)) atTop
      (𝓝 (∫ z, f z ∂jointLaw))
  /-- The first marginal is the prescribed scalar limit. -/
  fst_marginal : Measure.map Prod.fst jointLaw = limitLaw
  /-- The second marginal is the prescribed score limit. -/
  snd_marginal : Measure.map Prod.snd jointLaw = scoreLimit

/-- Two measurable row-indexed statistics with weakly convergent probability marginals have a
joint weakly convergent subsequence, and every such joint limit has the prescribed marginals. -/
theorem exists_jointWeakSubsequence
    {P : (n : ℕ) → Measure (Ω n)}
    {statistic : (n : ℕ) → Ω n → ℝ} {centralSequence : (n : ℕ) → Ω n → H}
    {limitLaw : Measure ℝ} {scoreLimit : Measure H}
    (hP : ∀ n, IsProbabilityMeasure (P n))
    (hlimit : IsProbabilityMeasure limitLaw) (hscore : IsProbabilityMeasure scoreLimit)
    (hstatistic : WeaklyConverges P statistic limitLaw)
    (hcentral : WeaklyConverges P centralSequence scoreLimit) :
    ∃ (jointLaw : Measure (ℝ × H)) (subsequence : ℕ → ℕ),
      JointWeakSubsequence subsequence P statistic centralSequence
        limitLaw scoreLimit jointLaw := by
  let pair : (n : ℕ) → Ω n → ℝ × H := fun n ω => (statistic n ω, centralSequence n ω)
  have hpair (n : ℕ) : AEMeasurable (pair n) (P n) :=
    (hstatistic.1 n).prodMk (hcentral.1 n)
  let jointPM : ℕ → ProbabilityMeasure (ℝ × H) := fun n =>
    ⟨Measure.map (pair n) (P n), Measure.isProbabilityMeasure_map (hpair n)⟩
  let statPM : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨Measure.map (statistic n) (P n),
      Measure.isProbabilityMeasure_map (hstatistic.1 n)⟩
  let scorePM : ℕ → ProbabilityMeasure H := fun n =>
    ⟨Measure.map (centralSequence n) (P n),
      Measure.isProbabilityMeasure_map (hcentral.1 n)⟩
  let statLimitPM : ProbabilityMeasure ℝ := ⟨limitLaw, hlimit⟩
  let scoreLimitPM : ProbabilityMeasure H := ⟨scoreLimit, hscore⟩
  have hstatPM : Tendsto statPM atTop (𝓝 statLimitPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa only [statPM, statLimitPM, ProbabilityMeasure.coe_mk,
      integral_map (hstatistic.1 _) f.continuous.aestronglyMeasurable] using hstatistic.2 f
  have hscorePM : Tendsto scorePM atTop (𝓝 scoreLimitPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa only [scorePM, scoreLimitPM, ProbabilityMeasure.coe_mk,
      integral_map (hcentral.1 _) f.continuous.aestronglyMeasurable] using hcentral.2 f
  have hstatCompact : IsCompact (closure (Set.range statPM)) :=
    hstatPM.isCompact_insert_range.closure_of_subset
      (Set.range_subset_iff.mpr fun n => Set.mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩))
  have hscoreCompact : IsCompact (closure (Set.range scorePM)) :=
    hscorePM.isCompact_insert_range.closure_of_subset
      (Set.range_subset_iff.mpr fun n => Set.mem_insert_iff.mpr (Or.inr ⟨n, rfl⟩))
  have hstatTight : IsTightMeasureSet (Set.range fun n => (statPM n : Measure ℝ)) := by
    convert isTightMeasureSet_of_isCompact_closure hstatCompact using 1
    ext μ
    simp
  have hscoreTight : IsTightMeasureSet (Set.range fun n => (scorePM n : Measure H)) := by
    convert isTightMeasureSet_of_isCompact_closure hscoreCompact using 1
    ext μ
    simp
  have hfst (n : ℕ) : Measure.fst (jointPM n : Measure (ℝ × H)) = statPM n := by
    dsimp [jointPM, statPM]
    change Measure.map Prod.fst (Measure.map (pair n) (P n)) = _
    rw [(continuous_fst.aemeasurable).map_map_of_aemeasurable (hpair n)]
    rfl
  have hsnd (n : ℕ) : Measure.snd (jointPM n : Measure (ℝ × H)) = scorePM n := by
    dsimp [jointPM, scorePM]
    change Measure.map Prod.snd (Measure.map (pair n) (P n)) = _
    rw [(continuous_snd.aemeasurable).map_map_of_aemeasurable (hpair n)]
    rfl
  have hjointTight : IsTightMeasureSet (Set.range fun n => (jointPM n : Measure (ℝ × H))) := by
    apply IsTightMeasureSet.prodMk
    · convert hstatTight using 1
      ext μ
      simp [hfst]
    · convert hscoreTight using 1
      ext μ
      simp [hsnd]
  have hjointCompact : IsCompact (closure (Set.range jointPM)) := by
    apply isCompact_closure_of_isTightMeasureSet
    convert hjointTight using 1
    ext μ
    simp
  obtain ⟨jointLimitPM, -, subsequence, hsubseq, hjointLim⟩ :=
    hjointCompact.isSeqCompact.subseq_of_frequently_in
      (Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => subset_closure
        (Set.mem_range_self n)))
  refine ⟨jointLimitPM, subsequence, ?_⟩
  have hfstLim : Tendsto (fun n => (jointPM (subsequence n)).map continuous_fst.aemeasurable)
      atTop (𝓝 (jointLimitPM.map continuous_fst.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hjointLim continuous_fst
  have hsndLim : Tendsto (fun n => (jointPM (subsequence n)).map continuous_snd.aemeasurable)
      atTop (𝓝 (jointLimitPM.map continuous_snd.aemeasurable)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hjointLim continuous_snd
  have hstatSubseq : Tendsto (fun n => statPM (subsequence n)) atTop (𝓝 statLimitPM) :=
    hstatPM.comp hsubseq.tendsto_atTop
  have hscoreSubseq : Tendsto (fun n => scorePM (subsequence n)) atTop (𝓝 scoreLimitPM) :=
    hscorePM.comp hsubseq.tendsto_atTop
  have hfstPM (n : ℕ) : (jointPM n).map continuous_fst.aemeasurable = statPM n :=
    Subtype.ext (hfst n)
  have hsndPM (n : ℕ) : (jointPM n).map continuous_snd.aemeasurable = scorePM n :=
    Subtype.ext (hsnd n)
  have hfstEq : jointLimitPM.map continuous_fst.aemeasurable = statLimitPM := by
    apply tendsto_nhds_unique hfstLim
    simpa only [hfstPM] using hstatSubseq
  have hsndEq : jointLimitPM.map continuous_snd.aemeasurable = scoreLimitPM := by
    apply tendsto_nhds_unique hsndLim
    simpa only [hsndPM] using hscoreSubseq
  refine
    { subsequence_strictMono := hsubseq
      probability := jointLimitPM.property
      converges := ?_
      fst_marginal := ?_
      snd_marginal := ?_ }
  · intro f
    have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hjointLim) f
    have hf' : Tendsto (fun n => ∫ z, f z ∂(jointPM (subsequence n) : Measure (ℝ × H)))
        atTop (𝓝 (∫ z, f z ∂(jointLimitPM : Measure (ℝ × H)))) := by
      simpa only [Function.comp_apply] using hf
    have heq : (fun n => ∫ ω,
        f (statistic (subsequence n) ω, centralSequence (subsequence n) ω)
          ∂P (subsequence n)) =
        (fun n => ∫ z, f z ∂(jointPM (subsequence n) : Measure (ℝ × H))) := by
      funext n
      rw [show (jointPM (subsequence n) : Measure (ℝ × H)) =
          Measure.map (pair (subsequence n)) (P (subsequence n)) from rfl]
      rw [integral_map (hpair _) f.continuous.aestronglyMeasurable]
    rw [heq]
    exact hf'
  · exact congr_arg ProbabilityMeasure.toMeasure hfstEq
  · exact congr_arg ProbabilityMeasure.toMeasure hsndEq

/-- A joint LAN limit couples the scalar estimator limit with the Gaussian central-sequence
limit and satisfies the exponential-tilt identity forced by regularity under every fixed local
direction.  It is an intermediate conclusion of the LAN change-of-measure argument, not an
assumption in the public convolution theorem. -/
structure RegularLANJointLimit
    (information : LinearMap.BilinForm ℝ H) (targetDerivative : H →ₗ[ℝ] ℝ)
    (limitLaw : Measure ℝ) (scoreLimit : Measure H) (jointLaw : Measure (ℝ × H)) : Prop where
  /-- The joint limit has total mass one. -/
  probability : IsProbabilityMeasure jointLaw
  /-- Its estimator marginal is the regular limit law. -/
  fst_marginal : Measure.map Prod.fst jointLaw = limitLaw
  /-- Its score marginal is the LAN Gaussian limit law. -/
  snd_marginal : Measure.map Prod.snd jointLaw = scoreLimit
  /-- Exponential tilting by a local direction translates the estimator limit by the target
  derivative in that direction. -/
  tilt_identity : ∀ (t : ℝ) (h : H),
    ∫ z, Complex.exp ((t * z.1 : ℂ) * Complex.I) *
        Complex.exp ((inner ℝ h z.2 - (1 / 2 : ℝ) * information h h : ℝ)) ∂jointLaw =
      Complex.exp ((t * targetDerivative h : ℂ) * Complex.I) * charFun limitLaw t

/-- The limiting log likelihood ratio in direction `h` is the affine projection
`inner h Z - information(h,h)/2` of the LAN Gaussian central-sequence limit. -/
noncomputable def lanLogLikelihoodLimit (information : LinearMap.BilinForm ℝ H)
    (scoreLimit : Measure H) (h : H) : Measure ℝ :=
  Measure.map (fun z => inner ℝ h z - (1 / 2 : ℝ) * information h h) scoreLimit

private lemma weaklyConverges_add_tendstoInProbability
    {P : (n : ℕ) → Measure (Ω n)} {X R : (n : ℕ) → Ω n → ℝ}
    {Q : Measure ℝ}
    (hP : ∀ n, IsProbabilityMeasure (P n)) (hQ : IsProbabilityMeasure Q)
    (hX : WeaklyConverges P X Q)
    (hR : TendstoInProbability P R 0)
    (hRmeas : ∀ n, AEMeasurable (R n) (P n)) :
    WeaklyConverges P (fun n ω => X n ω + R n ω) Q := by
  rw [tendstoInProbability_iff_real] at hR
  let xPM : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨Measure.map (X n) (P n), Measure.isProbabilityMeasure_map (hX.1 n)⟩
  let yPM : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨Measure.map (fun ω => X n ω + R n ω) (P n),
      Measure.isProbabilityMeasure_map ((hX.1 n).add (hRmeas n))⟩
  let qPM : ProbabilityMeasure ℝ := ⟨Q, hQ⟩
  have hxPM : Tendsto xPM atTop (𝓝 qPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simpa only [xPM, qPM, ProbabilityMeasure.coe_mk,
      integral_map (hX.1 _) f.continuous.aestronglyMeasurable] using hX.2 f
  have hyPM : Tendsto yPM atTop (𝓝 qPM) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro F hF_bounded hF_lip
    obtain ⟨M, hF_bounded⟩ := hF_bounded
    obtain ⟨L, hF_lip⟩ := hF_lip
    have hF_cont : Continuous F := hF_lip.continuous
    by_cases hL0 : L = 0
    · subst L
      simp only [LipschitzWith.zero_iff] at hF_lip
      have hconst := hF_lip 0
      simp only [← hconst, yPM, qPM, ProbabilityMeasure.coe_mk, integral_const,
        smul_eq_mul]
      have hpy n : IsProbabilityMeasure
          (Measure.map (fun ω => X n ω + R n ω) (P n)) :=
        Measure.isProbabilityMeasure_map ((hX.1 n).add (hRmeas n))
      simpa using! tendsto_const_nhds
    have hL : 0 < (L : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hL0)
    simp_rw [Metric.tendsto_nhds, Real.dist_eq]
    suffices ∀ ε > 0, ∀ᶠ n in atTop,
        |∫ ω, F ω ∂(yPM n : Measure ℝ) - ∫ ω, F ω ∂(qPM : Measure ℝ)| <
          (L : ℝ) * ε by
      intro ε hε
      convert! this (ε / L) (by positivity)
      field_simp
    intro ε hε
    have h_le n :
        |∫ ω, F ω ∂(yPM n : Measure ℝ) - ∫ ω, F ω ∂(qPM : Measure ℝ)|
          ≤ (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ |R n ω|}
            + |∫ ω, F ω ∂(xPM n : Measure ℝ) - ∫ ω, F ω ∂(qPM : Measure ℝ)| := by
      refine (abs_sub_le (∫ ω, F ω ∂(yPM n : Measure ℝ))
        (∫ ω, F ω ∂(xPM n : Measure ℝ))
        (∫ ω, F ω ∂(qPM : Measure ℝ))).trans ?_
      gcongr
      have h_int_Y : Integrable (fun ω => F (X n ω + R n ω)) (P n) := by
        refine Integrable.of_bound
          (hF_cont.aestronglyMeasurable.comp_aemeasurable ((hX.1 n).add (hRmeas n)))
          (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
        specialize hF_bounded (X n a + R n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (X n a + R n a)) (F 0)).trans hF_bounded
      have h_int_X : Integrable (fun ω => F (X n ω)) (P n) := by
        refine Integrable.of_bound
          (hF_cont.aestronglyMeasurable.comp_aemeasurable (hX.1 n))
          (‖F 0‖ + M) (ae_of_all _ fun a => ?_)
        specialize hF_bounded (X n a) 0
        rw [← sub_le_iff_le_add']
        exact (abs_sub_abs_le_abs_sub (F (X n a)) (F 0)).trans hF_bounded
      have h_int_sub :
          Integrable (fun a => ‖F (X n a + R n a) - F (X n a)‖) (P n) :=
        (h_int_Y.sub h_int_X).norm
      change |∫ ω, F ω ∂Measure.map (fun ω => X n ω + R n ω) (P n) -
        ∫ ω, F ω ∂Measure.map (X n) (P n)| ≤ _
      rw [integral_map (φ := fun ω => X n ω + R n ω)
          ((hX.1 n).add (hRmeas n)) hF_cont.aestronglyMeasurable,
        integral_map (φ := X n) (hX.1 n) hF_cont.aestronglyMeasurable,
        ← integral_sub h_int_Y h_int_X, ← Real.norm_eq_abs]
      calc
        ‖∫ a, F (X n a + R n a) - F (X n a) ∂P n‖
            ≤ ∫ a, ‖F (X n a + R n a) - F (X n a)‖ ∂P n :=
              norm_integral_le_integral_norm _
        _ = ∫ a in {x | |R n x| < ε / 2},
                ‖F (X n a + R n a) - F (X n a)‖ ∂P n
              + ∫ a in {x | ε / 2 ≤ |R n x|},
                ‖F (X n a + R n a) - F (X n a)‖ ∂P n := by
            symm
            simp_rw [← not_lt]
            refine integral_add_compl₀ ?_ h_int_sub
            exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
        _ ≤ ∫ a in {x | |R n x| < ε / 2}, (L : ℝ) * (ε / 2) ∂P n
              + ∫ a in {x | ε / 2 ≤ |R n x|}, M ∂P n := by
            gcongr ?_ + ?_
            · refine setIntegral_mono_on₀ h_int_sub.integrableOn integrableOn_const ?_ ?_
              · exact nullMeasurableSet_lt (by fun_prop) (by fun_prop)
              · intro x hx
                apply hF_lip.norm_sub_le_of_le
                simpa using hx.le
            · refine setIntegral_mono h_int_sub.integrableOn integrableOn_const fun a => ?_
              rw [← dist_eq_norm]
              exact hF_bounded _ _
        _ = (L : ℝ) * (ε / 2) * (P n).real {x | |R n x| < ε / 2}
              + M * (P n).real {ω | ε / 2 ≤ |R n ω|} := by
            simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
              Set.univ_inter, smul_eq_mul]
            ring
        _ ≤ (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ |R n ω|} := by
            rw [mul_assoc]
            gcongr
            grw [measureReal_le_one, mul_one]
    have hbadENN := hR (ε / 2) (by positivity)
    have hbadReal :
        Tendsto (fun n => (P n).real {ω | ε / 2 ≤ |R n ω|}) atTop (𝓝 0) := by
      change Tendsto (fun n => ENNReal.toReal ((P n) {ω | ε / 2 ≤ |R n ω|}))
        atTop (𝓝 0)
      simpa only [Function.comp_def, sub_zero, ENNReal.toReal_zero] using
        ((ENNReal.tendsto_toReal (by simp : (0 : ENNReal) ≠ ⊤)).comp hbadENN)
    have h_tendsto :
        Tendsto (fun n => (L : ℝ) * (ε / 2) + M * (P n).real {ω | ε / 2 ≤ |R n ω|}
            + |∫ ω, F ω ∂(xPM n : Measure ℝ) - ∫ ω, F ω ∂(qPM : Measure ℝ)|)
          atTop (𝓝 ((L : ℝ) * ε / 2)) := by
      have hxF := (tendsto_iff_forall_lipschitz_integral_tendsto.mp hxPM)
        F ⟨M, hF_bounded⟩ ⟨L, hF_lip⟩
      have hxabs :
          Tendsto (fun n =>
            |∫ ω, F ω ∂(xPM n : Measure ℝ) - ∫ ω, F ω ∂(qPM : Measure ℝ)|)
            atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => ∫ ω, F ω ∂(qPM : Measure ℝ)) atTop
            (𝓝 (∫ ω, F ω ∂(qPM : Measure ℝ))) := tendsto_const_nhds
        have hd := hxF.sub hc
        simpa only [Function.comp_def, sub_self, abs_zero] using
          ((continuous_abs : Continuous fun x : ℝ => |x|).tendsto
            ((∫ ω, F ω ∂(qPM : Measure ℝ)) - ∫ ω, F ω ∂(qPM : Measure ℝ))).comp hd
      have hc : Tendsto (fun _ : ℕ => (L : ℝ) * (ε / 2)) atTop
          (𝓝 ((L : ℝ) * (ε / 2))) := tendsto_const_nhds
      have hm : Tendsto (fun n => M * (P n).real {ω | ε / 2 ≤ |R n ω|})
          atTop (𝓝 0) := by simpa using tendsto_const_nhds.mul hbadReal
      convert (hc.add hm).add hxabs using 1 <;> ring
    have h_lt : (L : ℝ) * ε / 2 < (L : ℝ) * ε := half_lt_self (by positivity)
    filter_upwards [h_tendsto.eventually_lt_const h_lt] with n hn
    exact (h_le n).trans_lt hn
  refine ⟨fun n => (hX.1 n).add (hRmeas n), ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hyPM
  intro f
  have hf := hyPM f
  change Tendsto (fun n => ∫ ω, f (X n ω + R n ω) ∂P n) atTop
    (𝓝 (∫ x, f x ∂Q))
  convert hf using 1
  · funext n
    exact (integral_map (φ := fun ω => X n ω + R n ω)
      ((hX.1 n).add (hRmeas n)) f.continuous.aestronglyMeasurable).symm
  · simp [qPM]

/-- A [locally asymptotically normal experiment](hyp:lan) and [a fixed local direction](hyp:h) [make its guarded log likelihood ratio converge weakly to the affine Gaussian limit](goal). -/
theorem lan_logLikelihoodRatio_weaklyConverges
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H} {scoreLimit : Measure H}
    (lan : IsLAN E centralSequence information scoreLimit) (h : H) :
    WeaklyConverges E.baseLaw (fun n ω => E.logLikelihoodRatio n h ω)
      (lanLogLikelihoodLimit information scoreLimit h) := by
  let g : H → ℝ := fun z => inner ℝ h z - (1 / 2 : ℝ) * information h h
  let R : (n : ℕ) → Ω n → ℝ := fun n ω =>
    E.logLikelihoodRatio n h ω - inner ℝ h (centralSequence n ω) +
      (1 / 2 : ℝ) * information h h
  have hg : Continuous g := by fun_prop
  have hX : WeaklyConverges E.baseLaw (fun n ω => g (centralSequence n ω))
      (lanLogLikelihoodLimit information scoreLimit h) := by
    refine ⟨fun n => hg.aemeasurable.comp_aemeasurable (lan.central_measurable n), ?_⟩
    intro f
    have hf := lan.central_converges.2
      (f.compContinuous ⟨g, hg⟩)
    simpa only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk,
      Function.comp_apply, g, lanLogLikelihoodLimit,
      integral_map hg.aemeasurable f.continuous.aestronglyMeasurable] using hf
  have hllr (n : ℕ) : AEMeasurable (E.logLikelihoodRatio n h) (E.baseLaw n) := by
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    have hr : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    unfold LocalExperiment.logLikelihoodRatio
    exact (Measurable.ite (hr (measurableSet_singleton 0)) measurable_const hr.log).aemeasurable
  have hRmeas (n : ℕ) : AEMeasurable (R n) (E.baseLaw n) := by
    dsimp only [R]
    have hi : Continuous (fun z : H => inner ℝ h z) := by fun_prop
    exact ((hllr n).sub
      (hi.aemeasurable.comp_aemeasurable (lan.central_measurable n))).add aemeasurable_const
  have hlimitProb : IsProbabilityMeasure
      (lanLogLikelihoodLimit information scoreLimit h) := by
    letI : IsProbabilityMeasure scoreLimit := lan.gaussian_probability
    exact Measure.isProbabilityMeasure_map hg.aemeasurable
  have hsum := weaklyConverges_add_tendstoInProbability E.base_probability
    hlimitProb hX (lan.expansion h) hRmeas
  convert hsum using 1
  funext n ω
  dsimp only [g, R]
  ring

/-- The expectation of the exponential of the guarded log likelihood ratio is bounded by the
local probability mass plus the artificial `exp (-n)` contribution on its zero-density set. -/
theorem integral_exp_logLikelihoodRatio_le (E : LocalExperiment Ω H) (n : ℕ) (h : H) :
    ∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n ≤
      1 + Real.exp (-(n : ℝ)) := by
  letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
  letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
  let r : Ω n → ℝ := fun ω =>
    ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
  have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hllr_meas : Measurable (E.logLikelihoodRatio n h) := by
    unfold LocalExperiment.logLikelihoodRatio
    exact Measurable.ite (hr_meas (measurableSet_singleton 0))
      measurable_const hr_meas.log
  have hpoint : ∀ ω, Real.exp (E.logLikelihoodRatio n h ω) ≤
      r ω + Real.exp (-(n : ℝ)) := by
    intro ω
    unfold LocalExperiment.logLikelihoodRatio
    dsimp only
    by_cases hz : r ω = 0
    · rw [if_pos hz, hz, zero_add]
    · rw [if_neg hz, Real.exp_log
          (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))]
      exact le_add_of_nonneg_right (Real.exp_pos _).le
  have hr_int : Integrable r (E.baseLaw n) := by
    simpa only [integrableOn_univ] using
      (Measure.integrableOn_toReal_rnDeriv
        (μ := E.localLaw n h) (ν := E.baseLaw n) (s := Set.univ)
        (measure_ne_top _ _))
  have hexp_int : Integrable (fun ω => Real.exp (E.logLikelihoodRatio n h ω))
      (E.baseLaw n) := by
    apply (hr_int.add (integrable_const (Real.exp (-(n : ℝ))))).mono'
      hllr_meas.exp.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact hpoint ω
  calc
    (∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n)
        ≤ ∫ ω, (r ω + Real.exp (-(n : ℝ))) ∂E.baseLaw n :=
          integral_mono_ae hexp_int
            (hr_int.add (integrable_const (Real.exp (-(n : ℝ)))))
            (ae_of_all _ hpoint)
    _ = (∫ ω, r ω ∂E.baseLaw n) + Real.exp (-(n : ℝ)) := by
      rw [integral_add hr_int (integrable_const _), integral_const]
      simp
    _ ≤ 1 + Real.exp (-(n : ℝ)) := by
      gcongr
      rw [← setIntegral_univ]
      exact (Measure.setIntegral_toReal_rnDeriv_le
        (μ := E.localLaw n h) (ν := E.baseLaw n) (s := Set.univ)
        (measure_ne_top _ _)).trans measureReal_le_one

/-- The exponential moment of the affine Gaussian LAN log-likelihood limit equals one. -/
theorem integral_exp_lanLogLikelihoodLimit
    {information : LinearMap.BilinForm ℝ H} {scoreLimit : Measure H}
    (hscoreProb : IsProbabilityMeasure scoreLimit)
    (hscoreChar : ∀ t : H,
      charFun scoreLimit t = Complex.exp (-((information t t : ℂ) / 2))) (h : H) :
    ∫ y, Real.exp y ∂lanLogLikelihoodLimit information scoreLimit h = 1 := by
  letI : IsProbabilityMeasure scoreLimit := hscoreProb
  have hv : 0 ≤ information h h := by
    have hn := norm_charFun_le_one (μ := scoreLimit) h
    rw [hscoreChar h, Complex.norm_exp] at hn
    norm_num at hn
    linarith
  have hproj : Measure.map (fun z => inner ℝ h z) scoreLimit =
      gaussianReal 0 (information h h).toNNReal := by
    apply Measure.ext_of_charFun
    funext t
    rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
    have heq :
        (∫ x, Complex.exp ((inner ℝ (inner ℝ h x) t : ℂ) * Complex.I) ∂scoreLimit) =
          charFun scoreLimit (t • h) := by
      rw [charFun_apply]
      congr with x
      congr 2
      simp [inner_smul_right, real_inner_comm]
    rw [heq, hscoreChar (t • h), charFun_gaussianReal]
    simp [Real.coe_toNNReal _ hv, map_smul]
    congr 1
    ring
  have hlaw : lanLogLikelihoodLimit information scoreLimit h =
      Measure.map (fun x : ℝ => x - (1 / 2 : ℝ) * information h h)
        (gaussianReal 0 (information h h).toNNReal) := by
    unfold lanLogLikelihoodLimit
    have hmap := AEMeasurable.map_map_of_aemeasurable
      (μ := scoreLimit) (g := fun x : ℝ => x - (1 / 2 : ℝ) * information h h)
      (f := fun z : H => inner ℝ h z) (by fun_prop) (by fun_prop)
    calc
      Measure.map (fun z : H => inner ℝ h z - (1 / 2 : ℝ) * information h h)
          scoreLimit =
          Measure.map ((fun x : ℝ => x - (1 / 2 : ℝ) * information h h) ∘
            fun z : H => inner ℝ h z) scoreLimit := rfl
      _ = Measure.map (fun x : ℝ => x - (1 / 2 : ℝ) * information h h)
            (Measure.map (fun z : H => inner ℝ h z) scoreLimit) := hmap.symm
      _ = _ := congrArg _ hproj
  rw [hlaw, integral_map (by fun_prop) (by fun_prop)]
  have hexp (x : ℝ) : Real.exp (x - (1 / 2 : ℝ) * information h h) =
      Real.exp x * Real.exp (-(1 / 2 : ℝ) * information h h) := by
    rw [sub_eq_add_neg, Real.exp_add]
    congr 2
    ring
  simp_rw [hexp]
  rw [integral_mul_const]
  have hmgf := congr_fun
    (mgf_id_gaussianReal (μ := 0) (v := (information h h).toNNReal)) 1
  simp [mgf, Real.coe_toNNReal _ hv] at hmgf ⊢
  rw [hmgf, ← Real.exp_add]
  rw [← Real.exp_zero]
  congr 1
  ring

/-- In a LAN experiment, the exponential of the guarded log likelihood ratio has expectation
tending to one under the base law.  Equivalently, the asymptotically negligible singular part
of the local law cannot lose mass in the Gaussian likelihood-ratio limit. -/
theorem lan_likelihoodRatio_integral_tendsto_one
    {E : LocalExperiment Ω H} {centralSequence : (n : ℕ) → Ω n → H}
    {information : LinearMap.BilinForm ℝ H} {scoreLimit : Measure H}
    (lan : IsLAN E centralSequence information scoreLimit) (h : H) :
    Tendsto (fun n => ∫ ω, Real.exp (E.logLikelihoodRatio n h ω) ∂E.baseLaw n)
      atTop (𝓝 1) := by
  have hlimitProb : IsProbabilityMeasure
      (lanLogLikelihoodLimit information scoreLimit h) := by
    letI : IsProbabilityMeasure scoreLimit := lan.gaussian_probability
    exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hrowIntegrable : ∀ n,
      Integrable (fun ω => Real.exp (E.logLikelihoodRatio n h ω)) (E.baseLaw n) := by
    intro n
    letI : IsProbabilityMeasure (E.baseLaw n) := E.base_probability n
    letI : IsProbabilityMeasure (E.localLaw n h) := E.local_probability n h
    let r : Ω n → ℝ := fun ω =>
      ((E.localLaw n h).rnDeriv (E.baseLaw n) ω).toReal
    have hr_meas : Measurable r := (Measure.measurable_rnDeriv _ _).ennreal_toReal
    have hllr_meas : Measurable (E.logLikelihoodRatio n h) := by
      unfold LocalExperiment.logLikelihoodRatio
      exact Measurable.ite (hr_meas (measurableSet_singleton 0))
        measurable_const hr_meas.log
    have hr_int : Integrable r (E.baseLaw n) := by
      simpa only [integrableOn_univ] using
        (Measure.integrableOn_toReal_rnDeriv
          (μ := E.localLaw n h) (ν := E.baseLaw n) (s := Set.univ)
          (measure_ne_top _ _))
    apply (hr_int.add (integrable_const (Real.exp (-(n : ℝ))))).mono'
      hllr_meas.exp.aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      change Real.exp (E.logLikelihoodRatio n h ω) ≤
        r ω + Real.exp (-(n : ℝ))
      unfold LocalExperiment.logLikelihoodRatio
      dsimp only
      by_cases hz : r ω = 0
      · rw [if_pos hz, hz, zero_add]
      · rw [if_neg hz, Real.exp_log
            (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hz))]
        exact le_add_of_nonneg_right (Real.exp_pos _).le
  exact exp_integral_tendsto_one_of_weaklyConverges
    E.base_probability hlimitProb
    (lan_logLikelihoodRatio_weaklyConverges lan h) hrowIntegrable
    (integral_exp_lanLogLikelihoodLimit lan.gaussian_probability lan.gaussian_charFun h)
    (fun n => integral_exp_logLikelihoodRatio_le E n h)

end Causalean.Estimation.Efficiency.AsymptoticLanConvolution
