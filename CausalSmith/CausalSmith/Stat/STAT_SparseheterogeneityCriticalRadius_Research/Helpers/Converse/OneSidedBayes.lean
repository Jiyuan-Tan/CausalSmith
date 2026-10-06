module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.DecisionTransfer
public import Causalean.Stat.Minimax.FuzzyHypotheses
public import Causalean.Stat.Minimax.Mixture

/-! A one-sided fuzzy-hypothesis risk lemma. -/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open Causalean.Stat.Minimax.FuzzyHypotheses Causalean.Stat.Minimax.MomentMatchedMixture

@[fun_prop] lemma rawSignedScoreTotal_measurable (n J : ℕ) (kappa : ℝ) :
    Measurable (rawSignedScoreTotal n J kappa) := by
  unfold rawSignedScoreTotal
  exact measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    latentSignedScore_stronglyMeasurable.measurable.comp (measurable_pi_apply k))

@[fun_prop] lemma selectedRawMassTotal_measurable (n : ℕ) (rho : ℝ) :
    Measurable (selectedRawMassTotal n rho) := by
  exact rawMassTotal_measurable n (dualDegree n rho) converseKappa

@[fun_prop] lemma selectedAlignedScoreTotal_measurable
    (n : ℕ) (rho : ℝ) (h : Bool) :
    Measurable (selectedAlignedScoreTotal n rho h) := by
  unfold selectedAlignedScoreTotal
  exact measurable_const.mul
    (rawSignedScoreTotal_measurable n (dualDegree n rho) converseKappa)

/-- The deterministic normalization event is measurable in the latent vector. -/
lemma normalizationGood_measurableSet (n : ℕ) (rho : ℝ) (h : Bool) :
    MeasurableSet {theta | normalizationGood n rho h theta} := by
  unfold normalizationGood
  exact (measurableSet_le
      ((selectedRawMassTotal_measurable n rho).sub measurable_const).abs
      measurable_const).inter
    (measurableSet_le
      ((measurable_const.mul (selectedAlignedScoreTotal_measurable n rho h)).sub
        measurable_const).abs measurable_const)

/-- The exceptional normalization set is measurable in the latent vector. -/
lemma normalizationBad_measurableSet (n : ℕ) (rho : ℝ) (h : Bool) :
    MeasurableSet {theta | ¬ normalizationGood n rho h theta} := by
  simpa only [Set.compl_setOf] using (normalizationGood_measurableSet n rho h).compl

/-- One finite-support kernel simultaneously represents the complete
fixed-sample fibre under both selected priors. -/
lemma selectedMixtureSampleLaw_exists_commonSampleKernel
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∃ K : Kernel (Fin (n - 1) → LatentCell) (Fin n → SampleObs n),
      (∀ theta, IsProbabilityMeasure (K theta)) ∧
      K =ᵐ[selectedLatentPrior n rho false] (fun theta =>
        DiscreteAteHeterogeneityFrontier.productLaw n
          (latentToLaw n M rho converseKappa (selectedGamma n rho)
            (dualDegree n rho) theta (by omega) (by unfold dualDegree; omega)
            (by linarith) hrho (by unfold converseKappa; norm_num)
            (selectedGamma_mem_Icc n rho hn))) ∧
      K =ᵐ[selectedLatentPrior n rho true] (fun theta =>
        DiscreteAteHeterogeneityFrontier.productLaw n
          (latentToLaw n M rho converseKappa (selectedGamma n rho)
            (dualDegree n rho) theta (by omega) (by unfold dualDegree; omega)
            (by linarith) hrho (by unfold converseKappa; norm_num)
            (selectedGamma_mem_Icc n rho hn))) := by
  let f : (Fin (n - 1) → LatentCell) → Measure (Fin n → SampleObs n) :=
    fun theta => DiscreteAteHeterogeneityFrontier.productLaw n
      (latentToLaw n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (by omega) (by unfold dualDegree; omega)
        (by linarith) hrho (by unfold converseKappa; norm_num)
        (selectedGamma_mem_Icc n rho hn))
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by unfold dualDegree; omega)
    positivity
  have hJ : 1 ≤ dualDegree n rho := by unfold dualDegree; omega
  obtain ⟨s₀, hs₀, hm₀⟩ := latentProductPrior_ae_mem_finite n
    (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) false) ha hJ
  obtain ⟨s₁, hs₁, hm₁⟩ := latentProductPrior_ae_mem_finite n
    (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) true) ha hJ
  let s := s₀ ∪ s₁
  let _ : ∀ theta, IsProbabilityMeasure (f theta) := fun _ => by
    dsimp [f]
    infer_instance
  let K := finiteSupportKernel f s (hs₀.union hs₁) (fun _ => referenceLatent)
  have hKprob : ∀ theta, IsProbabilityMeasure (K theta) :=
    finiteSupportKernel_isProbabilityMeasure f s (hs₀.union hs₁)
      (fun _ => referenceLatent)
  refine ⟨K, hKprob, ?_, ?_⟩
  · filter_upwards [hm₀] with theta htheta
    exact finiteSupportKernel_apply f s (hs₀.union hs₁)
      (fun _ => referenceLatent) theta (Or.inl htheta)
  · filter_upwards [hm₁] with theta htheta
    exact finiteSupportKernel_apply f s (hs₀.union hs₁)
      (fun _ => referenceLatent) theta (Or.inr htheta)

/-- Signed separation outside two bad parameter sets converts a testing-error
lower bound into a Bayes squared-risk lower bound. -/
lemma oneSidedFuzzy_bayesRisk_lower
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π₀ π₁ : Measure Θ) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (K : Kernel Θ X) [IsMarkovKernel K] (target : Θ → ℝ)
    (T : X → ℝ) (hT : Measurable T)
    (B₀ B₁ : Set Θ) (hB₀ : MeasurableSet B₀) (hB₁ : MeasurableSet B₁)
    (s eta b₀ b₁ : ℝ) (hs : 0 ≤ s)
    (hsep₀ : ∀ᵐ theta ∂π₀, theta ∉ B₀ → target theta ≤ -s)
    (hsep₁ : ∀ᵐ theta ∂π₁, theta ∉ B₁ → s ≤ target theta)
    (hbad₀ : π₀.real B₀ ≤ b₀) (hbad₁ : π₁.real B₁ ≤ b₁)
    (htest : eta ≤ (priorPredictive π₀ K).real {x | 0 ≤ T x} +
      (priorPredictive π₁ K).real {x | T x < 0}) :
    ENNReal.ofReal (s ^ 2 * (eta - b₀ - b₁) / 2) ≤
      max (bayesSquaredRisk π₀ K target T)
        (bayesSquaredRisk π₁ K target T) := by
  let A : Set X := {x | 0 ≤ T x}
  let c : ℝ≥0∞ := ENNReal.ofReal (s ^ 2)
  let R₀ := bayesSquaredRisk π₀ K target T
  let R₁ := bayesSquaredRisk π₁ K target T
  have hA : MeasurableSet A := measurableSet_le measurable_const hT
  have hp₀ : ∀ᵐ theta ∂π₀,
      c * K theta A ≤ squaredRisk K target T theta + B₀.indicator (fun _ => c) theta := by
    filter_upwards [hsep₀] with theta htheta
    by_cases hb : theta ∈ B₀
    · rw [Set.indicator_of_mem hb]
      have hle : K theta A ≤ 1 := by
        calc K theta A ≤ K theta Set.univ := measure_mono (Set.subset_univ A)
          _ = 1 := measure_univ
      exact (mul_le_mul (le_refl c) hle bot_le bot_le).trans (by simp)
    · simp only [Set.indicator_of_notMem hb, add_zero]
      unfold squaredRisk
      calc
        c * K theta A = ∫⁻ x, A.indicator (fun _ => c) x ∂K theta := by simp [hA]
        _ ≤ ∫⁻ x, ENNReal.ofReal ((T x - target theta) ^ 2) ∂K theta := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ A
          · simp only [Set.indicator_of_mem hx]
            apply ENNReal.ofReal_le_ofReal
            change 0 ≤ T x at hx
            nlinarith [htheta hb]
          · simp [Set.indicator_of_notMem hx]
  have hp₁ : ∀ᵐ theta ∂π₁,
      c * K theta Aᶜ ≤ squaredRisk K target T theta + B₁.indicator (fun _ => c) theta := by
    filter_upwards [hsep₁] with theta htheta
    by_cases hb : theta ∈ B₁
    · rw [Set.indicator_of_mem hb]
      have hle : K theta Aᶜ ≤ 1 := by
        calc K theta Aᶜ ≤ K theta Set.univ := measure_mono (Set.subset_univ Aᶜ)
          _ = 1 := measure_univ
      exact (mul_le_mul (le_refl c) hle bot_le bot_le).trans (by simp)
    · simp only [Set.indicator_of_notMem hb, add_zero]
      unfold squaredRisk
      calc
        c * K theta Aᶜ = ∫⁻ x, Aᶜ.indicator (fun _ => c) x ∂K theta := by simp [hA.compl]
        _ ≤ ∫⁻ x, ENNReal.ofReal ((T x - target theta) ^ 2) ∂K theta := by
          apply lintegral_mono
          intro x
          by_cases hx : x ∈ Aᶜ
          · simp only [Set.indicator_of_mem hx]
            apply ENNReal.ofReal_le_ofReal
            have hx' : T x < 0 := by simpa [A] using hx
            nlinarith [htheta hb]
          · simp [Set.indicator_of_notMem hx]
  have hm₀ : c * priorPredictive π₀ K A ≤ R₀ + c * π₀ B₀ := by
    calc
      _ = ∫⁻ theta, c * K theta A ∂π₀ := by
        rw [lintegral_const_mul'' c ((Kernel.measurable_coe K hA).aemeasurable),
          ← priorPredictive_apply π₀ K hA]
      _ ≤ _ := lintegral_mono_ae hp₀
      _ = _ := by
        rw [lintegral_add_right _ (measurable_const.indicator hB₀)]
        simp [R₀, bayesSquaredRisk, hB₀]
  have hm₁ : c * priorPredictive π₁ K Aᶜ ≤ R₁ + c * π₁ B₁ := by
    calc
      _ = ∫⁻ theta, c * K theta Aᶜ ∂π₁ := by
        rw [lintegral_const_mul'' c ((Kernel.measurable_coe K hA.compl).aemeasurable),
          ← priorPredictive_apply π₁ K hA.compl]
      _ ≤ _ := lintegral_mono_ae hp₁
      _ = _ := by
        rw [lintegral_add_right _ (measurable_const.indicator hB₁)]
        simp [R₁, bayesSquaredRisk, hB₁]
  rw [show Aᶜ = {x | T x < 0} by ext x; simp [A]] at hm₁
  by_cases hR : max R₀ R₁ = ∞
  · simp [R₀, R₁, hR]
  have hR₀ : R₀ ≠ ∞ := fun h => hR (by simp [h])
  have hR₁ : R₁ ≠ ∞ := fun h => hR (by simp [h])
  have hc : c ≠ ∞ := by simp [c]
  have hcbad₀ : c * π₀ B₀ ≠ ∞ :=
    ENNReal.mul_ne_top hc (measure_ne_top _ _)
  have hcbad₁ : c * π₁ B₁ ≠ ∞ :=
    ENNReal.mul_ne_top hc (measure_ne_top _ _)
  have hm₀r := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hR₀, hcbad₀⟩) hm₀
  have hm₁r := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hR₁, hcbad₁⟩) hm₁
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hR₀ hcbad₀,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hm₀r
  rw [ENNReal.toReal_mul, ENNReal.toReal_add hR₁ hcbad₁,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hm₁r
  have hcReal : c.toReal = s ^ 2 := by simp [c, ENNReal.toReal_ofReal (sq_nonneg s)]
  rw [hcReal] at hm₀r hm₁r
  rw [ENNReal.ofReal_le_iff_le_toReal hR]
  have hR₀max := ENNReal.toReal_mono hR (le_max_left R₀ R₁)
  have hR₁max := ENNReal.toReal_mono hR (le_max_right R₀ R₁)
  have htest' : eta ≤ (priorPredictive π₀ K).real A +
      (priorPredictive π₁ K).real {x | T x < 0} := htest
  nlinarith [sq_nonneg s]

/-- A positive lower bound on a probability-prior average yields a parameter
fibre carrying half that bound, without any finiteness assumption on the
individual risks. -/
lemma exists_fibre_half_of_ofReal_le_lintegral
    {Θ : Type*} [MeasurableSpace Θ] (π : Measure Θ)
    [IsProbabilityMeasure π] (f : Θ → ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (havg : ENNReal.ofReal q ≤ ∫⁻ theta, f theta ∂π) :
    ∃ theta, ENNReal.ofReal (q / 2) ≤ f theta := by
  by_contra h
  push_neg at h
  have hle : ∫⁻ theta, f theta ∂π ≤ ENNReal.ofReal (q / 2) := by
    apply lintegral_le_const
    filter_upwards with theta
    exact (h theta).le
  have hbad : ENNReal.ofReal q ≤ ENNReal.ofReal (q / 2) := havg.trans hle
  have := ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ q / 2) |>.mp hbad
  linarith

/-- Fibre extraction can retain any almost-sure legality or class-membership
property of the prior. -/
lemma exists_ae_fibre_half_of_ofReal_le_lintegral
    {Θ : Type*} [MeasurableSpace Θ] (π : Measure Θ)
    [IsProbabilityMeasure π] (f : Θ → ℝ≥0∞) (p : Θ → Prop)
    (hp : ∀ᵐ theta ∂π, p theta) (q : ℝ) (hq : 0 < q)
    (havg : ENNReal.ofReal q ≤ ∫⁻ theta, f theta ∂π) :
    ∃ theta, p theta ∧ ENNReal.ofReal (q / 2) ≤ f theta := by
  by_contra h
  push_neg at h
  have hle : ∫⁻ theta, f theta ∂π ≤ ENNReal.ofReal (q / 2) := by
    apply lintegral_le_const
    filter_upwards [hp] with theta hptheta
    exact (h theta hptheta).le
  have hbad : ENNReal.ofReal q ≤ ENNReal.ofReal (q / 2) := havg.trans hle
  have := ENNReal.ofReal_le_ofReal_iff (by linarith : 0 ≤ q / 2) |>.mp hbad
  linarith

/-- Extract one parameter fibre from the larger of two Bayes risks. -/
lemma exists_fibre_of_oneSidedFuzzy_bayesRisk
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π₀ π₁ : Measure Θ) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (K : Kernel Θ X) (target : Θ → ℝ) (T : X → ℝ)
    (q : ℝ) (hq : 0 < q)
    (hbayes : ENNReal.ofReal q ≤
      max (bayesSquaredRisk π₀ K target T)
        (bayesSquaredRisk π₁ K target T)) :
    ∃ theta, ENNReal.ofReal (q / 2) ≤ squaredRisk K target T theta := by
  rcases le_max_iff.mp hbayes with h₀ | h₁
  · exact exists_fibre_half_of_ofReal_le_lintegral π₀
      (squaredRisk K target T) q hq h₀
  · exact exists_fibre_half_of_ofReal_le_lintegral π₁
      (squaredRisk K target T) q hq h₁

/-- Two-prior extraction retaining the almost-sure property belonging to the
selected side. -/
lemma exists_ae_fibre_of_oneSidedFuzzy_bayesRisk
    {Θ X : Type*} [MeasurableSpace Θ] [MeasurableSpace X]
    (π₀ π₁ : Measure Θ) [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (K : Kernel Θ X) (target : Θ → ℝ) (T : X → ℝ)
    (p₀ p₁ : Θ → Prop) (hp₀ : ∀ᵐ theta ∂π₀, p₀ theta)
    (hp₁ : ∀ᵐ theta ∂π₁, p₁ theta)
    (q : ℝ) (hq : 0 < q)
    (hbayes : ENNReal.ofReal q ≤
      max (bayesSquaredRisk π₀ K target T)
        (bayesSquaredRisk π₁ K target T)) :
    ∃ b : Bool, ∃ theta, (if b then p₁ theta else p₀ theta) ∧
      ENNReal.ofReal (q / 2) ≤ squaredRisk K target T theta := by
  rcases le_max_iff.mp hbayes with h₀ | h₁
  · obtain ⟨theta, hp, hrisk⟩ :=
      exists_ae_fibre_half_of_ofReal_le_lintegral π₀
        (squaredRisk K target T) p₀ hp₀ q hq h₀
    exact ⟨false, theta, by simpa using hp, hrisk⟩
  · obtain ⟨theta, hp, hrisk⟩ :=
      exists_ae_fibre_half_of_ofReal_le_lintegral π₁
        (squaredRisk K target T) p₁ hp₁ q hq h₁
    exact ⟨true, theta, by simpa using hp, hrisk⟩

/-- In the high regime, every measurable estimator has a legal selected
latent fibre whose squared risk carries the explicit fuzzy-testing bound. -/
theorem selectedLatent_exists_squaredRisk_lower
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hrho0 : 0 < rho)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T)
    (hbudget :
      2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) +
          8 * Real.exp (-(n : ℝ) /
            (100000000000000 * (dualDegree n rho : ℝ) ^ 2)) < 3 / 4) :
    ∃ P : KnownRadiusClass n M rho,
      ENNReal.ofReal
          (((3 * converseC2 * M * rho / (4 * Hrho n rho)) ^ 2 *
            (3 / 4 - 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) -
              8 * Real.exp (-(n : ℝ) /
                (100000000000000 * (dualDegree n rho : ℝ) ^ 2))) / 4)) ≤
        ∫⁻ x, ENNReal.ofReal ((T x - ateTarget P.law) ^ 2)
          ∂DiscreteAteHeterogeneityFrontier.productLaw n P.law ∧
      (M = 1 →
        P.law.fullLaw {z | z.y0 ∉ ({-1 / 2, 1 / 2} : Set ℝ) ∨
          z.y1 ∉ ({-1 / 2, 1 / 2} : Set ℝ)} = 0 ∧
        ∀ a k, 0 < P.law.cellMass k →
          P.law.outcomeLaw a k (({-1 / 2, 1 / 2} : Set ℝ)ᶜ) = 0) := by
  let pi0 := selectedLatentPrior n rho false
  let pi1 := selectedLatentPrior n rho true
  let Q : (Fin (n - 1) → LatentCell) → Law n := fun theta =>
    latentToLaw n M rho converseKappa (selectedGamma n rho)
      (dualDegree n rho) theta (by omega) (by unfold dualDegree; omega)
      (by linarith) hrho (by unfold converseKappa; norm_num)
      (selectedGamma_mem_Icc n rho hn)
  let target : (Fin (n - 1) → LatentCell) → ℝ := fun theta => ateTarget (Q theta)
  let s : ℝ := 3 * converseC2 * M * rho / (4 * Hrho n rho)
  let ep : ℝ := Real.exp (-(n : ℝ) * (1 - Real.log 2))
  let eb : ℝ := Real.exp (-(n : ℝ) /
    (100000000000000 * (dualDegree n rho : ℝ) ^ 2))
  let eta : ℝ := 3 / 4 - 2 * ep
  let q : ℝ := s ^ 2 * (eta - 4 * eb - 4 * eb) / 2
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    have : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by unfold dualDegree; omega)
    positivity
  let _ : IsProbabilityMeasure pi0 := by
    dsimp [pi0, selectedLatentPrior]
    exact latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) false) ha (by unfold dualDegree; omega)
  let _ : IsProbabilityMeasure pi1 := by
    dsimp [pi1, selectedLatentPrior]
    exact latentProductPrior_isProbabilityMeasure n (dualInterval n rho)
      (dualDegree n rho) (radiusDual n rho)
      (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
        (radiusDual n rho) true) ha (by unfold dualDegree; omega)
  obtain ⟨K, hKprob, hK0, hK1⟩ :=
    selectedMixtureSampleLaw_exists_commonSampleKernel n M rho hn hM hrho
  let _ : IsMarkovKernel K := ⟨fun theta => hKprob theta⟩
  have hpred0 : priorPredictive pi0 K =
      selectedMixtureSampleLaw n M rho false hn hM hrho := by
    rw [selectedMixtureSampleLaw_eq_bind_productLaw]
    unfold priorPredictive pi0
    exact Measure.bind_congr_right hK0
  have hpred1 : priorPredictive pi1 K =
      selectedMixtureSampleLaw n M rho true hn hM hrho := by
    rw [selectedMixtureSampleLaw_eq_bind_productLaw]
    unfold priorPredictive pi1
    exact Measure.bind_congr_right hK1
  let B0 : Set (Fin (n - 1) → LatentCell) :=
    {theta | ¬ normalizationGood n rho false theta}
  let B1 : Set (Fin (n - 1) → LatentCell) :=
    {theta | ¬ normalizationGood n rho true theta}
  have hsnonneg : 0 ≤ s := by
    have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
    have hc : 0 < converseC2 := by unfold converseC2; norm_num
    dsimp [s]
    positivity
  have hsep0 : ∀ᵐ theta ∂pi0, theta ∉ B0 → target theta ≤ -s := by
    filter_upwards [selectedLatentPrior_ae_signedTarget_lower
      n M rho false hn hM hrho] with theta htheta
    intro hnot
    have hgood : normalizationGood n rho false theta := by simpa [B0] using hnot
    have h := htheta hgood
    dsimp [target, Q, s]
    simp only [Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at h
    linarith
  have hsep1 : ∀ᵐ theta ∂pi1, theta ∉ B1 → s ≤ target theta := by
    filter_upwards [selectedLatentPrior_ae_signedTarget_lower
      n M rho true hn hM hrho] with theta htheta
    intro hnot
    have hgood : normalizationGood n rho true theta := by simpa [B1] using hnot
    simpa [target, Q, s] using htheta hgood
  have hbad0 : pi0.real B0 ≤ 4 * eb := by
    simpa [pi0, B0, eb] using
      selectedLatentPrior_normalizationGood_compl_le_exp n rho false hn
  have hbad1 : pi1.real B1 ≤ 4 * eb := by
    simpa [pi1, B1, eb] using
      selectedLatentPrior_normalizationGood_compl_le_exp n rho true hn
  have htest : eta ≤ (priorPredictive pi0 K).real {x | 0 ≤ T x} +
      (priorPredictive pi1 K).real {x | T x < 0} := by
    rw [hpred0, hpred1]
    have h := selectedMixtureSampleLaw_signTest_error_lower
      n M rho hn hM hrho T hT
    dsimp [eta, ep]
    linarith
  have hbayes : ENNReal.ofReal q ≤
      max (bayesSquaredRisk pi0 K target T)
        (bayesSquaredRisk pi1 K target T) := by
    exact oneSidedFuzzy_bayesRisk_lower pi0 pi1 K target T hT B0 B1
      (by simpa [B0] using normalizationBad_measurableSet n rho false)
      (by simpa [B1] using normalizationBad_measurableSet n rho true)
      s eta (4 * eb) (4 * eb) hsnonneg hsep0 hsep1 hbad0 hbad1 htest
  have hq : 0 < q := by
    have hH : 0 < Hrho n rho := lt_of_lt_of_le zero_lt_one (Hrho_one_le n rho)
    have hc : 0 < converseC2 := by unfold converseC2; norm_num
    have hspos : 0 < s := by dsimp [s]; positivity
    have hrem : 0 < eta - 4 * eb - 4 * eb := by
      dsimp [eta, ep, eb] at hbudget ⊢
      linarith
    dsimp [q]
    positivity
  let p0 : (Fin (n - 1) → LatentCell) → Prop := fun theta =>
    (∃ P : KnownRadiusClass n M rho, P.law = Q theta) ∧
      K theta = DiscreteAteHeterogeneityFrontier.productLaw n (Q theta) ∧
      LatentLawSpec n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta (Q theta)
  let p1 := p0
  have hp0 : ∀ᵐ theta ∂pi0, p0 theta := by
    filter_upwards [selectedLatentPrior_ae_class_embedding
      n M rho false hn hM hrho, hK0,
      selectedLatentPrior_ae_latentToLaw_spec n M rho false hn hM hrho]
      with theta hclass hkernel hspec
    exact ⟨hclass, hkernel, hspec⟩
  have hp1 : ∀ᵐ theta ∂pi1, p1 theta := by
    filter_upwards [selectedLatentPrior_ae_class_embedding
      n M rho true hn hM hrho, hK1,
      selectedLatentPrior_ae_latentToLaw_spec n M rho true hn hM hrho]
      with theta hclass hkernel hspec
    exact ⟨hclass, hkernel, hspec⟩
  obtain ⟨b, theta, hp, hrisk⟩ :=
    exists_ae_fibre_of_oneSidedFuzzy_bayesRisk pi0 pi1 K target T
      p0 p1 hp0 hp1 q hq hbayes
  have hp' : p0 theta := by simpa [p1] using hp
  obtain ⟨P, hPQ⟩ := hp'.1
  refine ⟨P, ?_, ?_⟩
  have hqhalf : q / 2 =
      (3 * converseC2 * M * rho / (4 * Hrho n rho)) ^ 2 *
        (3 / 4 - 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) -
          8 * Real.exp (-(n : ℝ) /
            (100000000000000 * (dualDegree n rho : ℝ) ^ 2))) / 4 := by
    dsimp [q, s, eta, ep, eb]
    ring
  rw [← hqhalf]
  unfold squaredRisk at hrisk
  rw [hp'.2.1] at hrisk
  dsimp [target] at hrisk
  rw [← hPQ] at hrisk
  exact hrisk
  intro hMone
  have hspec := hp'.2.2
  constructor
  · rw [hPQ]
    convert hspec.2.2.2.2.2.1 using 1 <;> norm_num [hMone]
  · intro a k hk
    rw [hPQ]
    convert hspec.2.2.2.2.1 a k using 1 <;> norm_num [hMone]

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
