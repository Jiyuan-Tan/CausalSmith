module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.CountReservoirTransfer
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.NormalizationBernstein

/-! Concrete fixed-mixture packaging for the decision-theoretic converse. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open scoped ENNReal NNReal

/-- The selected fixed-sample predictive law, with all selected parameters
made explicit once for the decision layer. -/
@[no_expose]
noncomputable def selectedMixtureSampleLaw (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    Measure (Fin n → SampleObs n) :=
  mixtureSampleLaw n M rho converseKappa (selectedGamma n rho)
    (dualInterval n rho) (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h)
    (by omega)
    (by unfold dualDegree
        exact lt_of_lt_of_le (by decide) (le_max_left _ _))
    (by linarith) hrho (by unfold converseKappa; norm_num)
    (selectedGamma_mem_Icc n rho hn)

/-- Expose the selected mixture as the bind of its selected latent prior and
complete fixed-sample fibre. -/
lemma selectedMixtureSampleLaw_eq_bind_productLaw
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    selectedMixtureSampleLaw n M rho h hn hM hrho =
      (selectedLatentPrior n rho h).bind (fun theta =>
        DiscreteAteHeterogeneityFrontier.productLaw n
          (latentToLaw n M rho converseKappa (selectedGamma n rho)
            (dualDegree n rho) theta (by omega)
            (by unfold dualDegree
                exact lt_of_lt_of_le (by decide) (le_max_left _ _))
            (by linarith) hrho (by unfold converseKappa; norm_num)
            (selectedGamma_mem_Icc n rho hn))) := by
  rfl

lemma selectedMixtureSampleLaw_isProbabilityMeasure
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    IsProbabilityMeasure (selectedMixtureSampleLaw n M rho h hn hM hrho) := by
  unfold selectedMixtureSampleLaw
  apply mixtureSampleLaw_isProbabilityMeasure
  · unfold dualInterval
    have hdegree : 0 < (dualDegree n rho : ℝ) := by
      exact_mod_cast (show 0 < dualDegree n rho by
        unfold dualDegree
        omega)
    positivity

/-- The finite-support observable kernel simultaneously represents the
concrete selected fixed-sample mixture and the reconstructed raw Poisson
mixture. -/
lemma selectedMixtureSampleLaw_exists_transferKernel
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∃ P : Kernel (Fin (n - 1) → LatentCell) (SampleObs n),
      ∃ hPprob : ∀ theta, IsProbabilityMeasure (P theta),
      P =ᵐ[selectedLatentPrior n rho h] (fun theta =>
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree
              exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)).observedLaw) ∧
      let _ := hPprob
      selectedMixtureSampleLaw n M rho h hn hM hrho =
          fixedMixture (selectedLatentPrior n rho h) P n ∧
        signedScoreHistogramReconstructionKernel n M ∘ₘ
            signedScoreReservoirCountLaw n
              (signedScoreIntensityPrior converseKappa
                (selectedGamma n rho) rho (dualInterval n rho)
                (dualDegree n rho) (radiusDual n rho)
                (orientedHypothesis (dualInterval n rho)
                  (dualDegree n rho) (radiusDual n rho) h)) =
          rawMixture (selectedLatentPrior n rho h) P
            (fun theta => Real.toNNReal
              (rawMassTotal n (dualDegree n rho) converseKappa theta))
            (2 * (n : ℝ≥0)) := by
  obtain ⟨P, hPprob, hP, hraw⟩ :=
    selectedSignedScoreHistogramReconstruction_exists_rawMixtureKernel
      n M rho h hn hM hrho
  refine ⟨P, hPprob, hP, ?_, hraw⟩
  let _ : ∀ theta, IsProbabilityMeasure (P theta) := hPprob
  unfold selectedMixtureSampleLaw
  exact mixtureSampleLaw_eq_fixedMixture_of_ae_eq n M rho converseKappa
    (selectedGamma n rho) (dualInterval n rho) (dualDegree n rho)
    (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h)
    (by omega)
    (by unfold dualDegree
        exact lt_of_lt_of_le (by decide) (le_max_left _ _))
    (by linarith) hrho (by unfold converseKappa; norm_num)
    (selectedGamma_mem_Icc n rho hn) P hP

/-- One finite-support kernel agrees with the selected observable-law fibre
under both hypothesis priors. -/
-- keep: explicit common experiment kernel needed to audit the two-prior decision transfer
lemma selectedMixtureSampleLaw_exists_commonKernel
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∃ P : Kernel (Fin (n - 1) → LatentCell) (SampleObs n),
      ∃ hPprob : ∀ theta, IsProbabilityMeasure (P theta),
      P =ᵐ[selectedLatentPrior n rho false] (fun theta =>
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree; omega) (by linarith) hrho
          (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)).observedLaw) ∧
      P =ᵐ[selectedLatentPrior n rho true] (fun theta =>
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree; omega) (by linarith) hrho
          (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)).observedLaw) := by
  let f : (Fin (n - 1) → LatentCell) → Measure (SampleObs n) := fun theta =>
    (latentToLaw n M rho converseKappa (selectedGamma n rho)
      (dualDegree n rho) theta (by omega) (by unfold dualDegree; omega)
      (by linarith) hrho (by unfold converseKappa; norm_num)
      (selectedGamma_mem_Icc n rho hn)).observedLaw
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
  let _ : ∀ theta, IsProbabilityMeasure (f theta) := fun theta => by
    dsimp [f]
    infer_instance
  let P := finiteSupportKernel f s (hs₀.union hs₁) (fun _ => referenceLatent)
  have hPprob : ∀ theta, IsProbabilityMeasure (P theta) :=
    finiteSupportKernel_isProbabilityMeasure f s (hs₀.union hs₁)
      (fun _ => referenceLatent)
  refine ⟨P, hPprob, ?_, ?_⟩
  · filter_upwards [hm₀] with theta htheta
    exact finiteSupportKernel_apply f s (hs₀.union hs₁)
      (fun _ => referenceLatent) theta (Or.inl htheta)
  · filter_upwards [hm₁] with theta htheta
    exact finiteSupportKernel_apply f s (hs₀.union hs₁)
      (fun _ => referenceLatent) theta (Or.inr htheta)

/-- The two concrete selected fixed-sample mixture laws inherit the numerical
TV comparison proved through the common Poisson-count reconstruction. -/
lemma selectedMixtureSampleLaw_tv_lt_one_quarter_add_two_exp
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    Causalean.Stat.tvDist
        (selectedMixtureSampleLaw n M rho false hn hM hrho)
        (selectedMixtureSampleLaw n M rho true hn hM hrho) <
      1 / 4 + 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2)) := by
  obtain ⟨P₀, hP₀prob, hP₀, hfixed₀, hrec₀⟩ :=
    selectedMixtureSampleLaw_exists_transferKernel
      n M rho false hn hM hrho
  obtain ⟨P₁, hP₁prob, hP₁, hfixed₁, hrec₁⟩ :=
    selectedMixtureSampleLaw_exists_transferKernel
      n M rho true hn hM hrho
  let _ : ∀ theta, IsProbabilityMeasure (P₀ theta) := hP₀prob
  let _ : ∀ theta, IsProbabilityMeasure (P₁ theta) := hP₁prob
  have htails := selectedFixedMixture_tv_lt_one_quarter_add_tails
    n M rho hn hM hrho P₀ P₁ hP₀ hP₁ hrec₀ hrec₁
  have hnum := selectedFixedMixture_tv_lt_one_quarter_add_two_exp
    n rho hn P₀ P₁ htails
  rwa [← hfixed₀, ← hfixed₁] at hnum

/-- Every measurable sign test makes a substantial combined error under the
two concrete selected fixed-sample mixtures. -/
lemma selectedMixtureSampleLaw_signTest_error_lower
    (n : ℕ) (M rho : ℝ) (hn : 3 ≤ n) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (T : (Fin n → SampleObs n) → ℝ) (hT : Measurable T) :
    1 - (1 / 4 + 2 * Real.exp (-(n : ℝ) * (1 - Real.log 2))) <
      (selectedMixtureSampleLaw n M rho false hn hM hrho).real
          {x | 0 ≤ T x} +
        (selectedMixtureSampleLaw n M rho true hn hM hrho).real
          {x | T x < 0} := by
  let μ₀ := selectedMixtureSampleLaw n M rho false hn hM hrho
  let μ₁ := selectedMixtureSampleLaw n M rho true hn hM hrho
  let _ : IsProbabilityMeasure μ₀ :=
    selectedMixtureSampleLaw_isProbabilityMeasure n M rho false hn hM hrho
  let _ : IsProbabilityMeasure μ₁ :=
    selectedMixtureSampleLaw_isProbabilityMeasure n M rho true hn hM hrho
  have htv := selectedMixtureSampleLaw_tv_lt_one_quarter_add_two_exp
    n M rho hn hM hrho
  have hA : MeasurableSet {x : Fin n → SampleObs n | 0 ≤ T x} :=
    measurableSet_le measurable_const hT
  have htest := Causalean.Stat.one_sub_tvDist_le_test
    (μ := μ₀) (ν := μ₁) hA
  have hcomp : ({x : Fin n → SampleObs n | 0 ≤ T x}ᶜ) =
      {x | T x < 0} := by
    ext x
    simp
  rw [hcomp] at htest
  dsimp only [μ₀, μ₁] at htv htest
  linarith

/-- Almost every selected latent vector has the advertised signed target
separation whenever its normalization event holds. -/
lemma selectedLatentPrior_ae_signedTarget_lower
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∀ᵐ theta ∂selectedLatentPrior n rho h,
      normalizationGood n rho h theta →
        3 * converseC2 * M * rho / (4 * Hrho n rho) ≤
          (if h then 1 else -1) *
            ateTarget
              (latentToLaw n M rho converseKappa (selectedGamma n rho)
                (dualDegree n rho) theta (by omega)
                (by unfold dualDegree
                    exact lt_of_lt_of_le (by decide) (le_max_left _ _))
                (by linarith) hrho (by unfold converseKappa; norm_num)
                (selectedGamma_mem_Icc n rho hn)) := by
  filter_upwards [selectedLatentPrior_ae_admissible n rho h]
    with theta hadm
  intro hgood
  exact latentToLaw_oriented_ate_lower n M rho h theta hn hM hrho
    hadm.1 hadm.2.1 hadm.2.2 hgood

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
