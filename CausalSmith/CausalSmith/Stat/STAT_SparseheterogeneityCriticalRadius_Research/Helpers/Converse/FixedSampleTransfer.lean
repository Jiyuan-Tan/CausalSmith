module
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.FixedSampleSupport
public import CausalSmith.Stat.STAT_SparseheterogeneityCriticalRadius_Research.Helpers.Converse.TensorCalibration
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer.Mixture
public import Mathlib.MeasureTheory.Group.Convolution

/-! Ordered-prefix transfer tools for the selected fixed-sample mixtures. -/

@[expose] public section

namespace CausalSmith.Stat.SparseheterogeneityCriticalRadius

open MeasureTheory ProbabilityTheory Set Filter
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.RandomScaleMinimaxTransfer
open Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.RandomScaleTransfer
open scoped ENNReal NNReal

/-- A measure-valued map restricted to a finite measurable set extends to a
kernel by using one of its probability fibres off that set. -/
@[no_expose]
noncomputable def finiteSupportKernel {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (f : α → Measure β) (s : Set α) (hs : s.Finite) (x₀ : α) : Kernel α β := by
  classical
  exact Kernel.mk (fun x => if x ∈ s then f x else f x₀) (by
    let _ : Finite s := hs.to_subtype
    simpa using (Measurable.dite (s := s)
      (measurable_of_finite (fun x : s => f x))
      (measurable_const : Measurable (fun _ : (sᶜ : Set α) => f x₀))
      hs.measurableSet))

lemma finiteSupportKernel_apply {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (f : α → Measure β) (s : Set α) (hs : s.Finite) (x₀ x : α)
    (hx : x ∈ s) : finiteSupportKernel f s hs x₀ x = f x := by
  classical
  simp [finiteSupportKernel, hx]

lemma finiteSupportKernel_isProbabilityMeasure {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    (f : α → Measure β) (s : Set α) (hs : s.Finite) (x₀ : α)
    [∀ x, IsProbabilityMeasure (f x)] :
    ∀ x, IsProbabilityMeasure (finiteSupportKernel f s hs x₀ x) := by
  classical
  intro x
  simp only [finiteSupportKernel, Kernel.coe_mk]
  split <;> infer_instance

/-- Finite almost-sure support upgrades an arbitrary family of probability
measures to a genuine probability kernel without changing it almost surely. -/
lemma exists_probabilityKernel_ae_eq_of_ae_mem_finite {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
    [Nonempty α] {μ : Measure α} (f : α → Measure β)
    [∀ x, IsProbabilityMeasure (f x)] (s : Set α) (hs : s.Finite)
    (hμ : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ K : Kernel α β, (∀ x, IsProbabilityMeasure (K x)) ∧ K =ᵐ[μ] f := by
  classical
  let x₀ : α := Classical.choice inferInstance
  let K := finiteSupportKernel f s hs x₀
  refine ⟨K, finiteSupportKernel_isProbabilityMeasure f s hs x₀, ?_⟩
  filter_upwards [hμ] with x hx
  exact finiteSupportKernel_apply f s hs x₀ x hx

/-- A kernel that agrees almost surely with the selected observed-law fibre
represents exactly the already-defined fixed-sample mixture. -/
lemma mixtureSampleLaw_eq_fixedMixture_of_ae_eq
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1)
    (K : Kernel (Fin (n - 1) → LatentCell) (SampleObs n))
    [∀ theta, IsProbabilityMeasure (K theta)]
    (hK : ∀ᵐ theta ∂latentProductPrior n a J D h,
      K theta = (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho
        hkappa hgamma).observedLaw) :
    mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma =
      fixedMixture (latentProductPrior n a J D h) K n := by
  unfold mixtureSampleLaw fixedMixture
  apply Measure.bind_congr_right
  filter_upwards [hK] with theta htheta
  unfold DiscreteAteHeterogeneityFrontier.productLaw
  simp only [htheta]

/-- The finite-atomic latent construction admits a genuine observed-data
kernel whose fixed mixture is definitionally faithful to `mixtureSampleLaw`. -/
-- keep: probability-kernel existence certificate for the fixed-sample mixture construction
lemma mixtureSampleLaw_exists_probabilityKernel
    (n : ℕ) (M rho kappa gamma a : ℝ) (J : ℕ)
    (D : Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.FiniteMomentDual
      (Causalean.Mathlib.Analysis.FinitePolynomialAlternationDuality.rationalTarget a)
      a 1 (3 * J)) (h : Bool)
    (hn : 0 < n) (hJ : 0 < J) (ha : 0 < a)
    (hM : 0 ≤ M) (hrho : 0 ≤ rho ∧ rho ≤ 2)
    (hkappa : 0 ≤ kappa) (hgamma : gamma ∈ Icc (0 : ℝ) 1) :
    ∃ K : Kernel (Fin (n - 1) → LatentCell) (SampleObs n),
      (∀ theta, IsProbabilityMeasure (K theta)) ∧
      mixtureSampleLaw n M rho kappa gamma a J D h hn hJ hM hrho hkappa hgamma =
        (latentProductPrior n a J D h).bind
          (fun theta => Measure.pi (fun _ : Fin n => K theta)) := by
  let f : (Fin (n - 1) → LatentCell) → Measure (SampleObs n) := fun theta =>
    (latentToLaw n M rho kappa gamma J theta hn hJ hM hrho hkappa hgamma).observedLaw
  let _ (theta : Fin (n - 1) → LatentCell) : IsProbabilityMeasure (f theta) := by
    dsimp [f]
    infer_instance
  obtain ⟨s, hs, hmem⟩ := latentProductPrior_ae_mem_finite n a J D h ha (by omega)
  obtain ⟨K, hKprob, hK⟩ :=
    exists_probabilityKernel_ae_eq_of_ae_mem_finite f s hs hmem
  refine ⟨K, hKprob, ?_⟩
  let _ (theta : Fin (n - 1) → LatentCell) : IsProbabilityMeasure (K theta) :=
    hKprob theta
  simpa only [fixedMixture] using
    mixtureSampleLaw_eq_fixedMixture_of_ae_eq n M rho kappa gamma a J D h
      hn hJ hM hrho hkappa hgamma K hK

/-- The ordered-prefix comparison permits different latent spaces and priors
on the two sides.  The same deterministic prefix map is applied to both raw
experiments, so their TV distance contracts; each side pays its own short-count
probability. -/
lemma twoPrior_fixedMixture_tv_le_randomScalePoisson
    {Θ₀ Θ₁ X : Type*}
    [MeasurableSpace Θ₀] [MeasurableSpace Θ₁] [MeasurableSpace X]
    (π₀ : Measure Θ₀) (π₁ : Measure Θ₁)
    [IsProbabilityMeasure π₀] [IsProbabilityMeasure π₁]
    (P₀ : Kernel Θ₀ X) (P₁ : Kernel Θ₁ X)
    [∀ θ, IsProbabilityMeasure (P₀ θ)]
    [∀ θ, IsProbabilityMeasure (P₁ θ)]
    (S₀ : Θ₀ → ℝ≥0) (S₁ : Θ₁ → ℝ≥0)
    (hS₀ : Measurable S₀) (hS₁ : Measurable S₁) (u : ℝ≥0)
    (n : ℕ) (fallback : Fin n → X)
    (hfixed₀ : AEMeasurable
      (fun θ => Measure.pi (fun _ : Fin n => P₀ θ)) π₀)
    (hfixed₁ : AEMeasurable
      (fun θ => Measure.pi (fun _ : Fin n => P₁ θ)) π₁)
    (hraw₀ : AEMeasurable
      (fun θ => finitePoissonSampleLaw (P₀ θ) (u * S₀ θ)) π₀)
    (hraw₁ : AEMeasurable
      (fun θ => finitePoissonSampleLaw (P₁ θ) (u * S₁ θ)) π₁) :
    Causalean.Stat.tvDist (fixedMixture π₀ P₀ n) (fixedMixture π₁ P₁ n) ≤
      Causalean.Stat.tvDist (rawMixture π₀ P₀ S₀ u)
        (rawMixture π₁ P₁ S₁ u) +
      (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
      ∫ θ, (poissonMeasure (u * S₁ θ) (Set.Iio n)).toReal ∂π₁ := by
  let f := orderedPrefix fallback
  let μ₀ := fixedMixture π₀ P₀ n
  let μ₁ := fixedMixture π₁ P₁ n
  let ρ₀ := rawMixture π₀ P₀ S₀ u
  let ρ₁ := rawMixture π₁ P₁ S₁ u
  let _ : IsProbabilityMeasure μ₀ := isProbabilityMeasure_bind hfixed₀
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let _ : IsProbabilityMeasure μ₁ := isProbabilityMeasure_bind hfixed₁
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let _ : IsProbabilityMeasure ρ₀ := isProbabilityMeasure_bind hraw₀
    (Filter.Eventually.of_forall fun _ => inferInstance)
  let _ : IsProbabilityMeasure ρ₁ := isProbabilityMeasure_bind hraw₁
    (Filter.Eventually.of_forall fun _ => inferInstance)
  have hf : Measurable f := measurable_orderedPrefix fallback
  let _ : IsProbabilityMeasure (Measure.map f ρ₀) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  let _ : IsProbabilityMeasure (Measure.map f ρ₁) :=
    Measure.isProbabilityMeasure_map hf.aemeasurable
  have herr₀ := tvDist_fixedMixture_map_rawMixture_le π₀ P₀ S₀ u n
    fallback hfixed₀ hraw₀
  have herr₁ := tvDist_fixedMixture_map_rawMixture_le π₁ P₁ S₁ u n
    fallback hfixed₁ hraw₁
  have hcontract : Causalean.Stat.tvDist (Measure.map f ρ₀)
      (Measure.map f ρ₁) ≤ Causalean.Stat.tvDist ρ₀ ρ₁ := by
    simpa only [Measure.deterministic_comp_eq_map] using
      Causalean.Stat.tvDist_bind_le ρ₀ ρ₁ (Kernel.deterministic f hf)
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have h₀ := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := μ₀) (ν := Measure.map f ρ₀) hA).trans herr₀
  have h₁ := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := μ₁) (ν := Measure.map f ρ₁) hA).trans herr₁
  have hc := (Causalean.Stat.abs_measureReal_sub_le_tvDist
    (μ := Measure.map f ρ₀) (ν := Measure.map f ρ₁) hA).trans hcontract
  have ht₀ := abs_sub_le (μ₀.real A) ((Measure.map f ρ₀).real A) (μ₁.real A)
  have ht₁ := abs_sub_le ((Measure.map f ρ₀).real A)
    ((Measure.map f ρ₁).real A) (μ₁.real A)
  rw [abs_sub_comm ((Measure.map f ρ₁).real A) (μ₁.real A)] at ht₁
  change |μ₀.real A - μ₁.real A| ≤
    Causalean.Stat.tvDist ρ₀ ρ₁ +
      (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
      ∫ θ, (poissonMeasure (u * S₁ θ) (Set.Iio n)).toReal ∂π₁
  calc
    |μ₀.real A - μ₁.real A| ≤
        |μ₀.real A - (Measure.map f ρ₀).real A| +
          |(Measure.map f ρ₀).real A - μ₁.real A| := ht₀
    _ ≤ (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
        (|(Measure.map f ρ₀).real A - (Measure.map f ρ₁).real A| +
          |μ₁.real A - (Measure.map f ρ₁).real A|) :=
      add_le_add h₀ ht₁
    _ ≤ (∫ θ, (poissonMeasure (u * S₀ θ) (Set.Iio n)).toReal ∂π₀) +
        (Causalean.Stat.tvDist ρ₀ ρ₁ +
          ∫ θ, (poissonMeasure (u * S₁ θ) (Set.Iio n)).toReal ∂π₁) :=
      add_le_add le_rfl (add_le_add hc h₁)
    _ = _ := by ring

/-- A larger Poisson mean has a smaller probability of missing a fixed prefix. -/
lemma poisson_lowerTail_antitone {lam mu : ℝ≥0} (h : lam ≤ mu) (n : ℕ) :
    poissonMeasure mu (Set.Iio n) ≤ poissonMeasure lam (Set.Iio n) := by
  have hsum : lam + (mu - lam) = mu := by
    rw [add_comm, tsub_add_cancel_of_le h]
  rw [← hsum, ← poissonMeasure_conv_poissonMeasure]
  rw [Measure.conv, Measure.map_apply (by fun_prop) measurableSet_Iio]
  calc
    (poissonMeasure lam).prod (poissonMeasure (mu - lam))
        ((fun z : ℕ × ℕ => z.1 + z.2) ⁻¹' Set.Iio n) ≤
        (poissonMeasure lam).prod (poissonMeasure (mu - lam))
          (Set.Iio n ×ˢ Set.univ) := by
      apply measure_mono
      intro z hz
      change z.1 + z.2 < n at hz
      change z.1 < n ∧ z.2 ∈ Set.univ
      exact ⟨by omega, Set.mem_univ z.2⟩
    _ = poissonMeasure lam (Set.Iio n) *
        poissonMeasure (mu - lam) Set.univ := by rw [Measure.prod_prod]
    _ = poissonMeasure lam (Set.Iio n) := by simp

/-- Equation (77), in its explicit form: a `Pois(2 n S)` reservoir with
`S ≥ 1` misses `n` observations with at most the doubled-mean Poisson tail. -/
lemma poisson_two_n_mul_scale_lower_tail (n : ℕ) (S : ℝ≥0) (hS : 1 ≤ S) :
    poissonMeasure (2 * (n : ℝ≥0) * S) (Set.Iio n) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  have hmean : 2 * (n : ℝ≥0) ≤ 2 * (n : ℝ≥0) * S := by
    calc
      2 * (n : ℝ≥0) = 2 * (n : ℝ≥0) * 1 := by ring
      _ ≤ 2 * (n : ℝ≥0) * S := by gcongr
  exact (poisson_lowerTail_antitone hmean n).trans (poisson_two_n_lower_tail n)

/-- The raw normalization scale contains the unit-mass reservoir, so it is at
least one whenever all rare latent intensities are nonnegative. -/
lemma one_le_rawMassTotal (n J : ℕ) (kappa : ℝ)
    (theta : Fin (n - 1) → LatentCell) (hn : 0 < n) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k)) :
    1 ≤ rawMassTotal n J kappa theta := by
  have hraw (k : Fin n) : 0 ≤ rawRareMass n J kappa theta k := by
    unfold rawRareMass
    split_ifs with hk
    · exact mul_nonneg
        (div_nonneg (mul_nonneg hkappa (Nat.cast_nonneg J))
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n)))
        (hq ⟨k.val, hk⟩)
    · norm_num
  let reservoir : Fin n := ⟨n - 1, by omega⟩
  have hreservoir : rawRareMass n J kappa theta reservoir = 1 := by
    simp only [rawRareMass]
    split_ifs with hk
    · exact (Nat.lt_irrefl (n - 1) hk).elim
    · rfl
  rw [rawMassTotal, ← hreservoir]
  exact Finset.single_le_sum (fun k _ => hraw k) (Finset.mem_univ reservoir)

/-- The qid normalization therefore satisfies the exponential reservoir tail
bound pointwise on every admissible latent vector. -/
lemma rawMassTotal_poisson_lower_tail
    (n J : ℕ) (kappa : ℝ) (theta : Fin (n - 1) → LatentCell)
    (hn : 0 < n) (hkappa : 0 ≤ kappa)
    (hq : ∀ k, 0 ≤ latentIntensity (theta k)) :
    poissonMeasure
        (2 * (n : ℝ≥0) * Real.toNNReal (rawMassTotal n J kappa theta))
        (Set.Iio n) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ) * (1 - Real.log 2))) := by
  apply poisson_two_n_mul_scale_lower_tail
  have htotal := one_le_rawMassTotal n J kappa theta hn hkappa hq
  rw [← NNReal.coe_le_coe]
  rw [Real.coe_toNNReal _ (by linarith : 0 ≤ rawMassTotal n J kappa theta)]
  exact htotal

end CausalSmith.Stat.SparseheterogeneityCriticalRadius
