module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.ActualPoissonMoments
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.Depoissonize
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OrderedGrouping
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OrderedPoisson
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.NullOutcomes
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OutcomeCrossMoment
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.PoissonPartition
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.RateBounds
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.SampleFactorization
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.UniversalAmplitude
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Procedure
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.TNonFlatSanity

/-!
Fixed-sample actual-law non-flat-null finite-mixture certificate at the sharp rough-equality
scale.
-/

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Universal constants precede sample size; both finite uniform sign priors live on
actual laws satisfying the unchanged model, with fixed non-flat null marginals and common energy. -/
-- @node: rough_null_lower_sign_mixture
lemma rough_null_lower_sign_mixture :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ,
    ∀ n, n0 ≤ n →
    ∀ sampler : ObsLaw → Measure (SampleSpace n),
      (∀ P, SamplingLaw P n (sampler P)) →
    ∃ k j : ℕ,
    ∃ nullFamily : ((Fin k → Bool) × (Fin j → Bool)) → ObsLaw,
    ∃ altFamily : ((Fin k → Bool) × (Fin j → Bool)) → ObsLaw,
    ∃ rho : ℝ, rho ∈ Set.Ioc 0 16 ∧ c * frontierRate n ≤ rho ∧
      (∀ signs, NullModel (nullFamily signs) ∧
        ∀ a y, y ∈ Set.Icc 0 1 → marginalDensity (nullFamily signs) a y = baselineDensity y) ∧
      (∀ signs, Model (altFamily signs) ∧ Psi (altFamily signs) = rho) ∧
      Causalean.Stat.tvDist (uniformSampleMixture n nullFamily)
        (uniformSampleMixture n altFamily) ≤ 1 / 4 := by
  let theta := lowerPublicAmplitude
  let c := theta ^ 4 / (4 * (210 : ℝ) ^ 3) * (2 : ℝ) ^ (-2 / 5 : ℝ)
  refine ⟨c, lower_separation_constant_pos theta lowerPublicAmplitude_mem.1, 16, ?_⟩
  intro n hn sampler hSampling
  let k := lowerCovariateRank n
  let j := lowerOutcomeRank k
  let hp := lower_tuned_parameters theta lowerPublicAmplitude_mem n
  let nullFamily : ((Fin k → Bool) × (Fin j → Bool)) → ObsLaw :=
    fun s => lowerNullLaw theta k j hp s.1 s.2
  let altFamily : ((Fin k → Bool) × (Fin j → Bool)) → ObsLaw :=
    fun s => lowerAlternativeLaw theta k j hp s.1 s.2
  refine ⟨k, j, nullFamily, altFamily, lowerSeparation theta k j,
    lowerSeparation_mem_Ioc theta k j hp,
    lower_tuned_separation_bound theta lowerPublicAmplitude_mem n (by omega), ?_, ?_, ?_⟩
  · intro s
    have hm := lower_membership theta k j hp s.1 s.2
    exact ⟨hm.1, hm.2.1⟩
  · intro s
    have hm := lower_membership theta k j hp s.1 s.2
    exact hm.2.2
  · exact lower_fixed_tv_le_quarter nullFamily altFamily n hn
      (lower_public_poisson_tv_le n hn)

/-- The uniform sign-family prior as an ordinary finitely supported weighted prior. -/
def uniformFinitePrior {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) : FinitePrior :=
  ⟨Fintype.card S, family ∘ (Fintype.equivFin S).symm,
    ⟨fun _ => (Fintype.card S : ℝ≥0∞)⁻¹, by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel
        (by exact_mod_cast (Fintype.card_ne_zero : Fintype.card S ≠ 0)) (by simp)⟩⟩

/-- A property of every sign-family component holds on the weighted prior support. -/
lemma uniformFinitePrior_supported {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (C : ObsLaw → Prop) (h : ∀ s, C (family s)) :
    PriorSupported (uniformFinitePrior family) C := by
  intro i _
  exact h ((Fintype.equivFin S).symm i)

/-- Enumerating the sign family preserves its observation mixture exactly. -/
-- @node: uniformFinitePrior_sampleMixture
lemma uniformFinitePrior_sampleMixture {S : Type*} [Fintype S] [Nonempty S]
    (n : ℕ) (family : S → ObsLaw) :
    finiteSampleMixture n (uniformFinitePrior family) = uniformSampleMixture n family := by
  classical
  change (∑ i : Fin (Fintype.card S),
    (Fintype.card S : ℝ≥0∞)⁻¹ • dataLaw (family ((Fintype.equivFin S).symm i)) n) =
    ∑ s : S, (Fintype.card S : ℝ≥0∞)⁻¹ • dataLaw (family s) n
  exact (Fintype.equivFin S).symm.sum_comp
    (fun s => (Fintype.card S : ℝ≥0∞)⁻¹ • dataLaw (family s) n)

-- @node: lem:rough-null-lower-mixture
/-- Public constants give finite-support probability priors on actual normalized laws,
with common non-flat null marginals, common alternative energy and the fixed-sample TV bound. -/
lemma rough_null_lower_mixture :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, -- @realizes c(universal positive lower constant)
      -- @realizes n0(universal natural threshold)
    ∀ n, n0 ≤ n →
    ∀ sampler : ObsLaw → Measure (SampleSpace n),
      (∀ P, SamplingLaw P n (sampler P)) →
    ∃ nu0 nu1 : FinitePrior, -- @realizes nu0(finite-support null probability prior)
      -- @realizes nu1(finite-support alternative probability prior)
    ∃ rho : ℝ, rho ∈ Set.Ioc 0 16 ∧ c * frontierRate n ≤ rho ∧
      PriorSupported nu0 (fun P => NullModel P ∧
        ∀ a y, y ∈ Set.Icc 0 1 → marginalDensity P a y = baselineDensity y) ∧
      PriorSupported nu1 (fun P => Model P ∧ Psi P = rho) ∧
      Causalean.Stat.tvDist (finiteSampleMixture n nu0)
        (finiteSampleMixture n nu1) ≤ 1 / 4 := by
  obtain ⟨c, hc, n0, h⟩ := rough_null_lower_sign_mixture
  refine ⟨c, hc, n0, ?_⟩
  intro n hn sampler hSampling
  obtain ⟨k, j, nullFamily, altFamily, rho, hrho, hrate, hnull, halt, htv⟩ :=
    h n hn sampler hSampling
  refine ⟨uniformFinitePrior nullFamily, uniformFinitePrior altFamily,
    rho, hrho, hrate, ?_, ?_, ?_⟩
  · exact uniformFinitePrior_supported nullFamily _ hnull
  · exact uniformFinitePrior_supported altFamily _ halt
  · simpa only [uniformFinitePrior_sampleMixture] using htv

end CausalSmith.Stat.DensityEffectRoughNull
