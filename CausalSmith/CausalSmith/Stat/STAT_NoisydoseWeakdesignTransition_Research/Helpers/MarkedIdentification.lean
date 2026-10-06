module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.LatentIdentification
/-! Weighted observation factorization for identification. -/
public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
variable {S : Type*} [MeasurableSpace S]

/-- Weighting by a function of the mapped coordinate commutes with pushforward. [Under the stated conditions](hyp:f,hf,g,hg). [This is the stated conclusion](goal). -/
-- @node: identification_map_withDensity
lemma identification_map_withDensity {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (fun a => g (f a))).map f = (μ.map f).withDensity g := by
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ hf]
  change (∫⁻ a, (φ ∘ f) a ∂μ.withDensity (g ∘ f)) = _
  rw [lintegral_withDensity_eq_lintegral_mul μ (hg.comp hf) (hφ.comp hf),
    lintegral_withDensity_eq_lintegral_mul (μ.map f) hg hφ,
    lintegral_map (hg.mul hφ) hf]
  rfl

/-- A bounded nonnegative mark gives its pushforward mass by an ordinary integral. [Under the stated conditions](hyp:f,hf,g,hi,hn,hB). [This is the stated conclusion](goal). -/
-- @node: identification_marked_map_apply
lemma identification_marked_map_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f)
    (g : α → ℝ) (hi : Integrable g μ) (hn : 0 ≤ᵐ[μ] g)
    (B : Set β) (hB : MeasurableSet B) :
    ((μ.withDensity (fun a => ENNReal.ofReal (g a))).map f) B =
      ENNReal.ofReal (∫ a, (f ⁻¹' B).indicator g a ∂μ) := by
  rw [Measure.map_apply hf hB, withDensity_apply _ (hf hB),
    ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (hn.filter_mono (ae_mono Measure.restrict_le_self)), integral_indicator (hf hB)]

/-- An independent additive channel also factors after marking the latent coordinate. [Under the stated conditions](hyp:hT,hN,H,hH,hpair). [This is the stated conclusion](goal). -/
-- @node: identification_weighted_sum_convolution
lemma identification_weighted_sum_convolution {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (T N : α → ℝ) (hT : Measurable T) (hN : Measurable N)
    (ν γ : Measure ℝ) [SFinite γ]
    (hpair : μ.map (fun a => (T a, N a)) = ν.prod γ)
    (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (μ.withDensity (fun a => H (T a))).map (fun a => T a + N a) =
      (ν.withDensity H).conv γ := by
  have hw := identification_map_withDensity μ (fun a => (T a, N a))
    (hT.prodMk hN) (fun p : ℝ × ℝ => H p.1) (hH.comp measurable_fst)
  rw [hpair, ← prod_withDensity_left hH] at hw
  have hs := congrArg (Measure.map (fun p : ℝ × ℝ => p.1+p.2)) hw
  rw [Measure.map_map (by fun_prop) (hT.prodMk hN)] at hs
  exact hs

/-- Observational equivalence identifies the outcome-marked centered dose measure. [Under the stated conditions](hyp:hobs). [This is the stated conclusion](goal). -/
-- @node: observedMarked_eq_of_obsLaw_eq
lemma observedMarked_eq_of_obsLaw_eq (sigma : ℝ) (P P' : Measure (StructSpace S))
    (hobs : obsLaw sigma P = obsLaw sigma P') (x : Bool) :
    ((stratumLaw P x).withDensity (fun w => ENNReal.ofReal (sY w))).map (observedCentered sigma) =
      ((stratumLaw P' x).withDensity (fun w => ENNReal.ofReal (sY w))).map (observedCentered sigma) := by
  have hm : Measurable (obsMap (S := S) sigma) := by unfold obsMap contaminatedDose; fun_prop
  have hg : Measurable (fun o : Obs => ENNReal.ofReal o.2.2) := by fun_prop
  have h := congrArg (fun μ : Measure Obs => μ.withDensity (fun o => ENNReal.ofReal o.2.2))
    (show (stratumLaw P x).map (obsMap sigma) = (stratumLaw P' x).map (obsMap sigma) by
      rw [stratumLaw_map_obsMap, stratumLaw_map_obsMap, hobs])
  rw [← identification_map_withDensity _ _ hm _ hg,
    ← identification_map_withDensity _ _ hm _ hg] at h
  have h' := congrArg (Measure.map (fun o : Obs => o.2.1-a0)) h
  rw [Measure.map_map (by fun_prop) hm, Measure.map_map (by fun_prop) hm] at h'
  exact h'

/-- Bounded regression tests replace the realized mark by its conditional potential mean. [Under the stated conditions](hyp:hP,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: observedMarked_eq_meanMarked
lemma observedMarked_eq_meanMarked (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (x : Bool) :
    ((stratumLaw P x).withDensity (fun w => ENNReal.ofReal (sY w))).map (observedCentered sigma) =
      ((stratumLaw P x).withDensity (fun w => ENNReal.ofReal
        (projectedMean E P (sA w) x))).map (observedCentered sigma) := by
  letI := stratumLaw_probability P hP.strataPos x
  have hb : 0 < beta := hbeta.1
  have hY := realized_dose_mean E beta kappa sigma hbeta hkappa hsigma P hP
  have hiY := integrable_stratumLaw P hP.strataPos x _
    (realized_outcome_integrable E P hP.strataPos hP.scheduleUnconfoundedness
      hP.latentSupport hP.boundedPO hP.consistency)
  have hiM : Integrable (fun w => projectedMean E P (sA w) x) (stratumLaw P x) := by
    apply Integrable.of_bound
      (((projectedMean_measurable E P beta hb hP.holderMean).comp
        (show Measurable (fun w : StructSpace S => (sA w,x)) by fun_prop)).aestronglyMeasurable) 1
    filter_upwards with w
    have hm := projectedMean_mem_Icc E P hP.meanRange (sA w) x
    simpa [Real.norm_eq_abs, abs_of_nonneg hm.1] using hm.2
  have hnY : 0 ≤ᵐ[stratumLaw P x] sY :=
    (ae_stratumLaw_of_ae P x hY.1).mono (fun _ h => h.1)
  have hnM : 0 ≤ᵐ[stratumLaw P x] (fun w => projectedMean E P (sA w) x) :=
    Eventually.of_forall (fun w => (projectedMean_mem_Icc E P hP.meanRange (sA w) x).1)
  have hV : Measurable (observedCentered (S := S) sigma) := by
    unfold observedCentered contaminatedDose; fun_prop
  apply Measure.ext
  intro B hB
  rw [identification_marked_map_apply _ _ hV _ hiY hnY B hB,
    identification_marked_map_apply _ _ hV _ hiM hnM B hB]
  congr 1
  rw [stratumLaw_integral, stratumLaw_integral]
  congr 1
  let F : (ℝ × Bool × ℝ) → ℝ := fun p =>
    if p.2.1 = x ∧ p.1+sigma*p.2.2-a0 ∈ B then 1 else 0
  have hF : Measurable F := by
    apply Measurable.ite
    · exact (measurableSet_eq_fun (by fun_prop) measurable_const).inter
        (hB.preimage (by fun_prop))
    · fun_prop
    · fun_prop
  have ht := hY.2.2.2 F hF ⟨1, by intro p; dsimp [F]; split_ifs <;> norm_num⟩
  calc
    _ = ∫ w, F (sA w,sX w,sZ w)*sY w ∂P := by
      apply integral_congr_ae
      filter_upwards with w
      by_cases hx : sX w = x <;> by_cases hv : observedCentered sigma w ∈ B <;>
        simp [F, hx, hv, indicator_apply, mem_preimage, observedCentered, contaminatedDose]
    _ = ∫ w, F (sA w,sX w,sZ w)*condPotMean E P (sX w) (sA w) ∂P := ht
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hP.latentSupport] with w hw
      by_cases hx : sX w = x <;> by_cases hv : observedCentered sigma w ∈ B <;>
        simp [F, hx, hv, indicator_apply, mem_preimage, observedCentered, contaminatedDose,
          projectedMean, Set.projIcc_of_mem zero_le_one hw]

/-- The centered latent dose and scaled Gaussian error have a product law in each stratum. [Under the stated conditions](hyp:hoverlap,herr,hgauss). [This is the stated conclusion](goal). -/
-- @node: latent_noise_product_stratum
lemma latent_noise_product_stratum (sigma : ℝ)
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    (hoverlap : StratumPositive P) (herr : ErrorIndependence P)
    (hgauss : GaussianChannel P) (x : Bool) :
    (stratumLaw P x).map (fun w => (latentCentered w, sigma*sZ w)) =
      (latentDoseLaw P x).prod (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) := by
  letI := stratumLaw_probability P hoverlap x
  letI := latentDoseLaw_probability P hoverlap x
  have hT : Measurable (latentCentered (S := S)) := by unfold latentCentered; fun_prop
  have hswap := congrArg (Measure.map (Prod.swap : ℝ × ℝ → ℝ × ℝ))
    (error_centered_product_stratum P hoverlap herr x)
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.prod_swap, hgauss] at hswap
  have hscale := congrArg (Measure.map (Prod.map (id : ℝ → ℝ) (fun z : ℝ => sigma*z))) hswap
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id] at hscale
  have hg : (gaussianReal (0 : ℝ) 1).map (fun z => sigma*z) =
      gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)) := by
    simpa using (gaussianReal_map_const_mul (μ := 0) (v := 1) sigma)
  rw [hg] at hscale
  exact hscale

/-- The bounded projected version is the same latent mark on the supported dose interval. [Under the stated conditions](hyp:hdesign). [This is the stated conclusion](goal). -/
-- @node: latentMeanMeasure_projected
lemma latentMeanMeasure_projected (E : PathSpace S) (P : Measure (StructSpace S))
    (kappa : ℝ) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (x : Bool) :
    latentMeanMeasure E P x = (latentDoseLaw P x).withDensity
      (fun t => ENNReal.ofReal (projectedMean E P (t+a0) x)) := by
  apply withDensity_congr_ae
  filter_upwards [latentDoseLaw_ae_mem P kappa hdesign x] with t ht
  have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
    dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
  simp only [projectedMean, Set.projIcc_of_mem zero_le_one ha]

/-- The observed outcome-marked conditional measure is the marked latent Gaussian convolution. [Under the stated conditions](hyp:hP,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: observedMarked_stratum_convolution
lemma observedMarked_stratum_convolution (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P : Measure (StructSpace S)) [IsProbabilityMeasure P]
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P) (x : Bool) :
    ((stratumLaw P x).withDensity (fun w => ENNReal.ofReal (sY w))).map (observedCentered sigma) =
      (latentMeanMeasure E P x).conv (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma))) := by
  have hb : 0 < beta := hbeta.1
  have hH : Measurable (fun t : ℝ => ENNReal.ofReal (projectedMean E P (t+a0) x)) :=
    ((projectedMean_measurable E P beta hb hP.holderMean).comp
      (show Measurable (fun t : ℝ => (t+a0,x)) by fun_prop)).ennreal_ofReal
  have h := identification_weighted_sum_convolution (stratumLaw P x)
    latentCentered (fun w => sigma*sZ w) (by unfold latentCentered; fun_prop) (by fun_prop)
    (latentDoseLaw P x) (gaussianReal 0 (NNReal.mk (sigma^2) (sq_nonneg sigma)))
    (latent_noise_product_stratum sigma P hP.strataPos hP.errorIndependence hP.gaussianChannel x)
    _ hH
  rw [observedMarked_eq_meanMarked E beta kappa sigma hbeta hkappa hsigma P hP x,
    latentMeanMeasure_projected E P kappa hP.weakDesign x]
  have hv : observedCentered (S := S) sigma =
      (fun w => latentCentered w + sigma*sZ w) := by
    funext w
    dsimp [observedCentered, contaminatedDose, latentCentered]
    ring
  rw [hv]
  simpa only [latentCentered, sub_add_cancel] using h

/-- Mean-range finiteness supplies a finite marked latent measure without moment assumptions. [Under the stated conditions](hyp:hbeta,hoverlap,hdesign,hholder,hrange). [This is the stated conclusion](goal). -/
-- @node: latentMeanMeasure_finite
lemma latentMeanMeasure_finite (E : PathSpace S) (P : Measure (StructSpace S))
    [IsProbabilityMeasure P] (beta kappa : ℝ) (hbeta : 0 < beta)
    (hoverlap : StratumPositive P) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P)
    (hholder : HolderMean E beta P) (hrange : MeanRange E P) (x : Bool) :
    IsFiniteMeasure (latentMeanMeasure E P x) := by
  have hi := latentMean_integrable E P beta kappa hbeta hoverlap hdesign hholder hrange x
  apply isFiniteMeasure_withDensity
  have hn : 0 ≤ᵐ[latentDoseLaw P x] (fun t => condPotMean E P x (t+a0)) := by
    filter_upwards [latentDoseLaw_ae_mem P kappa hdesign x] with t ht
    have ha : t+a0 ∈ Icc (0 : ℝ) 1 := by
      dsimp [a0]; constructor <;> linarith [ht.1, ht.2]
    exact le_trans (by norm_num) (hrange x _ ha).1
  exact ((hasFiniteIntegral_iff_ofReal hn).mp hi.hasFiniteIntegral).ne

/-- The marked law inherits compact support by absolute continuity with respect to latent dose. [Under the stated conditions](hyp:hdesign). [This is the stated conclusion](goal). -/
-- @node: latentMeanMeasure_support
lemma latentMeanMeasure_support (E : PathSpace S) (P : Measure (StructSpace S))
    (kappa : ℝ) {K : ClassConstants} (hdesign : WeakDesign K.clo K.chi kappa P) (x : Bool) :
    (latentMeanMeasure E P x) (Icc (-1/2 : ℝ) (1/2))ᶜ = 0 := by
  exact withDensity_absolutelyContinuous _ _ (ae_iff.mp (latentDoseLaw_ae_mem P kappa hdesign x))

/-- Gaussian injectivity recovers the mean-marked latent law from observational equivalence. [Under the stated conditions](hyp:hP,hP',hobs,hbeta,hkappa,hsigma). [This is the stated conclusion](goal). -/
-- @node: latentMeanMeasure_eq_of_obsLaw_eq
lemma latentMeanMeasure_eq_of_obsLaw_eq (E : PathSpace S) (beta kappa sigma : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (hsigma : sigma ∈ Icc (0 : ℝ) (1/4))
    (P P' : Measure (StructSpace S)) [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {K : ClassConstants} (hP : NoisyDoseModelClass E K beta kappa sigma P)
    (hP' : NoisyDoseModelClass E K beta kappa sigma P')
    (hobs : obsLaw sigma P = obsLaw sigma P') (x : Bool) :
    latentMeanMeasure E P x = latentMeanMeasure E P' x := by
  have hb : 0 < beta := hbeta.1
  letI := latentMeanMeasure_finite E P beta kappa hb hP.strataPos hP.weakDesign
    hP.holderMean hP.meanRange x
  letI := latentMeanMeasure_finite E P' beta kappa hb hP'.strataPos hP'.weakDesign
    hP'.holderMean hP'.meanRange x
  have hc := observedMarked_eq_of_obsLaw_eq sigma P P' hobs x
  rw [observedMarked_stratum_convolution E beta kappa sigma hbeta hkappa hsigma P hP x,
    observedMarked_stratum_convolution E beta kappa sigma hbeta hkappa hsigma P' hP' x] at hc
  have hi := compact_gaussian_convolution_injective sigma hsigma
    (latentMeanMeasure E P x) 0 (latentMeanMeasure E P' x) 0
    (latentMeanMeasure_support E P kappa hP.weakDesign x) (by simp)
    (latentMeanMeasure_support E P' kappa hP'.weakDesign x) (by simp) (by simpa using hc)
  simpa using hi

end CausalSmith.Stat.NoisydoseWeakdesignTransition
