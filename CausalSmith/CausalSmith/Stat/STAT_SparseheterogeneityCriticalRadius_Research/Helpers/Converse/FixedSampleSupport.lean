module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.TargetSeparation

/-! Almost-sure legality and class membership of the selected fixed-sample
latent construction. -/

public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory Set Filter

/-- The one-cell prior is almost surely supported on nonnegative intensities,
the fixed-overlap propensity interval, and unit-interval scores. -/
lemma oneCellPrior_ae_admissible (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) :
    ∀ᵐ z ∂oneCellPrior a J D h,
      0 ≤ latentIntensity z ∧
      latentPropensity z ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
      latentScore z ∈ Icc (0 : ℝ) 1 := by
  have hgood : MeasurableSet {z : LatentCell |
      0 ≤ latentIntensity z ∧
      latentPropensity z ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
      latentScore z ∈ Icc (0 : ℝ) 1} := by
    simp only [Set.mem_Icc]
    have hq : Measurable latentIntensity := by
      unfold latentIntensity
      fun_prop
    have he : Measurable latentPropensity := by
      unfold latentPropensity
      fun_prop
    have hu : Measurable latentScore := by
      unfold latentScore
      fun_prop
    exact (measurableSet_le measurable_const hq).inter
      (((measurableSet_le measurable_const he).inter
          (measurableSet_le he measurable_const)).inter
        ((measurableSet_le measurable_const hu).inter
          (measurableSet_le hu measurable_const)))
  rw [oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    rw [ae_dirac_iff hgood]
    exact referenceLatent_admissible
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D (!h)] with x hx
      exact latentFromIntensity_admissible false ha (hx.imp_right And.left)
    · apply Measure.ae_smul_measure
      rw [ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hgood]
      filter_upwards [tiltedSide_ae_zero_or_mem_interval a J D h] with x hx
      exact latentFromIntensity_admissible true ha (hx.imp_right And.left)

/-- Any function is almost-everywhere measurable under a measure concentrated
on a finite measurable set.  The measurable representative interpolates the
function on that set and is constant off it. -/
lemma aemeasurable_of_ae_mem_finite {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [Inhabited β] {μ : Measure α} (f : α → β) (s : Set α)
    (hs : s.Finite) (hμ : ∀ᵐ x ∂μ, x ∈ s) : AEMeasurable f μ := by
  classical
  let g : α → β := fun x => if _hx : x ∈ s then f x else default
  have hg : Measurable g := by
    let _ : Finite s := hs.to_subtype
    simpa only [g] using
      (Measurable.dite (s := s)
        (measurable_of_finite (fun x : s => f x))
        (measurable_const : Measurable (fun _ : (sᶜ : Set α) => (default : β)))
        hs.measurableSet)
  exact hg.aemeasurable.congr (hμ.mono fun x hx => by simp [g, hx])

/-- Each tilted dual prior is concentrated on the finite set consisting of
zero and the approximation-dual nodes. -/
lemma tiltedSide_ae_mem_finite (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    ∃ s : Set ℝ, s.Finite ∧ ∀ᵐ x ∂tiltedSide a J D h, x ∈ s := by
  classical
  let s : Set ℝ := {0} ∪ Set.range D.nodes
  have hs : s.Finite := Set.finite_singleton 0 |>.union (Set.finite_range D.nodes)
  have hsmeas : MeasurableSet s := hs.measurableSet
  refine ⟨s, hs, ?_⟩
  rw [tiltedSide, ae_add_measure_iff]
  constructor
  · rw [ae_finsetSum_measure_iff]
    intro i hi
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff hsmeas).2 (Or.inr ⟨i, rfl⟩)
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hsmeas).2 (Or.inl rfl)

/-- The one-cell prior is concentrated on a finite collection of the reference
atom and the two images of the finite tilted supports. -/
lemma oneCellPrior_ae_mem_finite (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) :
    ∃ s : Set LatentCell, s.Finite ∧ ∀ᵐ z ∂oneCellPrior a J D h, z ∈ s := by
  classical
  obtain ⟨s₀, hs₀, hfalse⟩ := tiltedSide_ae_mem_finite a J D (!h)
  obtain ⟨s₁, hs₁, htrue⟩ := tiltedSide_ae_mem_finite a J D h
  let s : Set LatentCell :=
    {referenceLatent} ∪ latentFromIntensity false a '' s₀ ∪
      latentFromIntensity true a '' s₁
  have hs : s.Finite :=
    (Set.finite_singleton referenceLatent).union (hs₀.image _)
      |>.union (hs₁.image _)
  have hsmeas : MeasurableSet s := hs.measurableSet
  refine ⟨s, hs, ?_⟩
  rw [oneCellPrior, ae_add_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hsmeas).2 (Or.inl (Or.inl rfl))
  · apply Measure.ae_smul_measure
    rw [ae_add_measure_iff]
    constructor
    · apply Measure.ae_smul_measure
      exact (ae_map_iff (latentFromIntensity_measurable false a).aemeasurable hsmeas).2
        (hfalse.mono fun x hx => Or.inl (Or.inr ⟨x, hx, rfl⟩))
    · apply Measure.ae_smul_measure
      exact (ae_map_iff (latentFromIntensity_measurable true a).aemeasurable hsmeas).2
        (htrue.mono fun x hx => Or.inr ⟨x, hx, rfl⟩)

/-- A finite product of one-cell priors is concentrated on a finite set of
latent vectors. -/
lemma latentProductPrior_ae_mem_finite (n : ℕ) (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∃ s : Set (Fin (n - 1) → LatentCell), s.Finite ∧
      ∀ᵐ theta ∂latentProductPrior n a J D h, theta ∈ s := by
  classical
  obtain ⟨s₀, hs₀, hcell⟩ := oneCellPrior_ae_mem_finite a J D h
  let s : Set (Fin (n - 1) → LatentCell) := {theta | ∀ k, theta k ∈ s₀}
  have hs : s.Finite := Set.Finite.pi' fun _ => hs₀
  have hall : ∀ᵐ theta ∂Measure.pi
      (fun _ : Fin (n - 1) => oneCellPrior a J D h), ∀ k, theta k ∈ s₀ := by
    let _ (k : Fin (n - 1)) : IsProbabilityMeasure (oneCellPrior a J D h) :=
      oneCellPrior_isProbabilityMeasure a J D h ha hJ
    apply ae_all_iff.mpr
    intro k
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n - 1) => oneCellPrior a J D h)
      (i := k)).eventually hcell
  exact ⟨s, hs, by simpa only [latentProductPrior, s, Set.mem_ofPred_eq] using hall⟩

/-- Every function out of the finite-atomic latent product is
almost-everywhere measurable, regardless of how it is defined away from the
finite support. -/
lemma latentProductPrior_aemeasurable (n : ℕ) (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J)
    {β : Type*} [MeasurableSpace β] [Inhabited β]
    (f : (Fin (n - 1) → LatentCell) → β) :
    AEMeasurable f (latentProductPrior n a J D h) := by
  obtain ⟨s, hs, hmem⟩ := latentProductPrior_ae_mem_finite n a J D h ha hJ
  exact aemeasurable_of_ae_mem_finite f s hs hmem

/-- A finite product of legal one-cell priors is almost surely legal in every
coordinate. -/
lemma latentProductPrior_ae_admissible (n : ℕ) (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    ∀ᵐ theta ∂latentProductPrior n a J D h,
      (∀ k, 0 ≤ latentIntensity (theta k)) ∧
      (∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1) := by
  have hcell := oneCellPrior_ae_admissible a J D h ha
  have hall : ∀ᵐ theta ∂Measure.pi
      (fun _ : Fin (n - 1) => oneCellPrior a J D h),
      ∀ k, 0 ≤ latentIntensity (theta k) ∧
        latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4) ∧
        latentScore (theta k) ∈ Icc (0 : ℝ) 1 := by
    let _ (k : Fin (n - 1)) : IsProbabilityMeasure (oneCellPrior a J D h) :=
      oneCellPrior_isProbabilityMeasure a J D h ha hJ
    apply ae_all_iff.mpr
    intro k
    exact (Measure.tendsto_eval_ae_ae
      (μ := fun _ : Fin (n - 1) => oneCellPrior a J D h)
      (i := k)).eventually hcell
  simpa only [latentProductPrior] using hall.mono (fun theta htheta =>
    ⟨fun k => (htheta k).1,
      fun k => (htheta k).2.1,
      fun k => (htheta k).2.2⟩)

/-- The selected converse product prior is almost surely legal in every latent
coordinate. -/
lemma selectedLatentPrior_ae_admissible (n : ℕ) (rho : ℝ) (h : Bool) :
    ∀ᵐ theta ∂selectedLatentPrior n rho h,
      (∀ k, 0 ≤ latentIntensity (theta k)) ∧
      (∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1) := by
  have hJ : 1 ≤ dualDegree n rho := by
    unfold dualDegree
    exact le_trans (by decide : 1 ≤ 2) (le_max_left _ _)
  have hJpos : 0 < (dualDegree n rho : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hJ)
  have ha : 0 < dualInterval n rho := by
    unfold dualInterval
    positivity
  exact latentProductPrior_ae_admissible n (dualInterval n rho)
    (dualDegree n rho) (radiusDual n rho)
    (orientedHypothesis (dualInterval n rho) (dualDegree n rho)
      (radiusDual n rho) h) ha hJ

/-- On legal latent coordinates, the total `latentToLaw` selector satisfies
the intended finite-law specification rather than taking its fallback branch. -/
lemma latentToLaw_spec_of_admissible
    (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 0 < n) (hJ : 0 < J) (hM : 0 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1) :
    LatentLawSpec n M rho kappa gamma J theta
      (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma) := by
  unfold latentToLaw
  rw [dif_pos hq, dif_pos he, dif_pos hu]
  exact Classical.choose_spec
    (latentLaw_exists n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma
      hq he hu)

/-- On legal latent coordinates, `latentToLaw` embeds directly in the full
known-radius class. -/
lemma latentToLaw_class_embedding_of_admissible
    (n : ℕ) (M rho kappa gamma : ℝ) (J : ℕ)
    (theta : Fin (n - 1) → LatentCell)
    (hn : 3 ≤ n) (hJ : 0 < J) (hM : 1 ≤ M)
    (hrho : 0 ≤ rho ∧ rho ≤ 2) (hkappa : 0 ≤ kappa)
    (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k))
    (he : ∀ k, latentPropensity (theta k) ∈ Icc (1 / 4 : ℝ) (3 / 4))
    (hu : ∀ k, latentScore (theta k) ∈ Icc (0 : ℝ) 1) :
    ∃ P : KnownRadiusClass n M rho,
      P.law = latentToLaw n M rho kappa gamma J theta (by omega) hJ
        (by linarith) hrho hkappa hgamma := by
  let Q := latentToLaw n M rho kappa gamma J theta (by omega) hJ
    (by linarith) hrho hkappa hgamma
  have hs : LatentLawSpec n M rho kappa gamma J theta Q :=
    latentToLaw_spec_of_admissible n M rho kappa gamma J theta (by omega) hJ
      (by linarith) hrho hkappa hgamma hq he hu
  exact latentLawSpec_class_embedding_general hn hM hrho hgamma he hu hs

/-- Almost every selected latent vector produces the advertised latent-law
specification. -/
lemma selectedLatentPrior_ae_latentToLaw_spec
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∀ᵐ theta ∂selectedLatentPrior n rho h,
      LatentLawSpec n M rho converseKappa (selectedGamma n rho)
        (dualDegree n rho) theta
        (latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn)) := by
  filter_upwards [selectedLatentPrior_ae_admissible n rho h] with theta htheta
  exact latentToLaw_spec_of_admissible n M rho converseKappa
    (selectedGamma n rho) (dualDegree n rho) theta (by omega)
    (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
    (by linarith) hrho (by unfold converseKappa; norm_num)
    (selectedGamma_mem_Icc n rho hn) htheta.1 htheta.2.1 htheta.2.2

/-- Almost every selected latent vector maps to a law in the full known-radius
class. -/
lemma selectedLatentPrior_ae_class_embedding
    (n : ℕ) (M rho : ℝ) (h : Bool)
    (hn : 3 ≤ n) (hM : 1 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2) :
    ∀ᵐ theta ∂selectedLatentPrior n rho h,
      ∃ P : KnownRadiusClass n M rho,
        P.law = latentToLaw n M rho converseKappa (selectedGamma n rho)
          (dualDegree n rho) theta (by omega)
          (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
          (by linarith) hrho (by unfold converseKappa; norm_num)
          (selectedGamma_mem_Icc n rho hn) := by
  filter_upwards [selectedLatentPrior_ae_admissible n rho h] with theta htheta
  exact latentToLaw_class_embedding_of_admissible n M rho converseKappa
    (selectedGamma n rho) (dualDegree n rho) theta hn
    (by unfold dualDegree; exact lt_of_lt_of_le (by decide) (le_max_left _ _))
    hM hrho (by unfold converseKappa; norm_num)
    (selectedGamma_mem_Icc n rho hn) htheta.1 htheta.2.1 htheta.2.2

/-- The finite product latent prior is a probability measure once its one-cell
factors are probability measures. -/
lemma latentProductPrior_isProbabilityMeasure (n : ℕ) (a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool) (ha : 0 < a) (hJ : 1 ≤ J) :
    IsProbabilityMeasure (latentProductPrior n a J D h) := by
  let _ (k : Fin (n - 1)) : IsProbabilityMeasure (oneCellPrior a J D h) :=
    oneCellPrior_isProbabilityMeasure a J D h ha hJ
  unfold latentProductPrior
  infer_instance

/-- The fixed-sample law-valued fibre is almost-everywhere measurable because
the latent product prior has finite support; no measurability property of the
choice-based `latentToLaw` selector is needed. -/
lemma mixtureSampleLaw_kernel_aemeasurable
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J) (ha : 0 < a)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    AEMeasurable
      (fun theta => DiscreteAteHeterogeneityFrontier.productLaw n
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma))
      (latentProductPrior n a J D h) := by
  exact latentProductPrior_aemeasurable n a J D h ha (by omega) _

/-- Once the fixed-sample law-valued fibre is almost-everywhere measurable,
the mixture defined by `Measure.bind` is a probability measure.  This isolates
the sole kernel hypothesis needed for the normalization of the mixture. -/
lemma mixtureSampleLaw_isProbabilityMeasure_of_aemeasurable
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J) (ha : 0 < a)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hkernel : AEMeasurable
      (fun theta => DiscreteAteHeterogeneityFrontier.productLaw n
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma))
      (latentProductPrior n a J D h)) :
    IsProbabilityMeasure
      (mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma) := by
  let _ : IsProbabilityMeasure (latentProductPrior n a J D h) :=
    latentProductPrior_isProbabilityMeasure n a J D h ha (by omega)
  unfold mixtureSampleLaw
  exact isProbabilityMeasure_bind hkernel
    (Filter.Eventually.of_forall fun theta => inferInstance)

/-- Under the same fibre measurability hypothesis, a measurable event under
the fixed-sample mixture is the latent-prior integral of its fibre
probabilities. -/
lemma mixtureSampleLaw_apply_of_aemeasurable
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (hkernel : AEMeasurable
      (fun theta => DiscreteAteHeterogeneityFrontier.productLaw n
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma))
      (latentProductPrior n a J D h))
    (s : Set (Fin n → SampleObs n)) (hs : MeasurableSet s) :
    mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma s =
      ∫⁻ theta, DiscreteAteHeterogeneityFrontier.productLaw n
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma) s
        ∂latentProductPrior n a J D h := by
  exact Measure.bind_apply hs hkernel

/-- The finite-atomic latent prior makes the fixed-sample mixture a probability
measure without any separate kernel-measurability assumption. -/
lemma mixtureSampleLaw_isProbabilityMeasure
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J) (ha : 0 < a)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    IsProbabilityMeasure
      (mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma) := by
  exact mixtureSampleLaw_isProbabilityMeasure_of_aemeasurable
    n M rho kappa gamma a J D h hn hJ ha hM hrho hkappa hgamma
    (mixtureSampleLaw_kernel_aemeasurable
      n M rho kappa gamma a J D h hn hJ ha hM hrho hkappa hgamma)

/-- A measurable event under the fixed-sample mixture is the latent-prior
integral of its fibre probabilities. -/
-- keep: event-level disintegration formula for the fixed-sample mixture API
lemma mixtureSampleLaw_apply
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J) (ha : 0 < a)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (s : Set (Fin n → SampleObs n)) (hs : MeasurableSet s) :
    mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma s =
      ∫⁻ theta, DiscreteAteHeterogeneityFrontier.productLaw n
        (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma) s
        ∂latentProductPrior n a J D h := by
  exact mixtureSampleLaw_apply_of_aemeasurable
    n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma
    (mixtureSampleLaw_kernel_aemeasurable
      n M rho kappa gamma a J D h hn hJ ha hM hrho hkappa hgamma) s hs

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
