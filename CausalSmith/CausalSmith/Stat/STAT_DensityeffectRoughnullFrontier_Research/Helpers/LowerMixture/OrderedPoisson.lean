module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.PoissonPartition
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.SampleFactorization

/-!
Lift the actual ordered fixed-count likelihood to the complete ordered Poisson
experiment. The same latent sign is shared across every observation; the Poisson
count is independent of it. No reconstruction kernel or likelihood assumption
is needed for this measure-level lift.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CausalSmith.Stat.DensityEffectRoughNull
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

/-- The actual ordered Poisson experiment, averaged over a finite uniform prior. -/
-- @node: lowerUniformPoissonMixture
def lowerUniformPoissonMixture {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (lam : NNReal) : Measure (FiniteSample Omega) :=
  Causalean.Stat.Minimax.Mixture.uniformMixture
    (fun s => finitePoissonSampleLaw (family s).law lam)

/-- The complete Poisson mixture is a probability law. -/
-- @node: lowerUniformPoissonMixture_probability
instance lowerUniformPoissonMixture_probability {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (lam : NNReal) :
    IsProbabilityMeasure (lowerUniformPoissonMixture family lam) :=
  Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _

/-- Conditioning only on count leaves the whole-sample shared-sign prior intact. -/
-- @node: lower_uniform_poisson_count_fiber
lemma lower_uniform_poisson_count_fiber {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (lam : NNReal) (n : ℕ) :
    (lowerUniformPoissonMixture family lam).restrict (FiniteSample.count ⁻¹' {n}) =
      poissonMeasure lam {n} • (uniformSampleMixture n family).map (fixedSizeEmbed n) := by
  classical
  unfold lowerUniformPoissonMixture uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  have hsum (t : Finset S) (nu : S → Measure (FiniteSample Omega)) :
      (∑ s ∈ t, nu s).restrict (FiniteSample.count ⁻¹' {n}) =
        ∑ s ∈ t, (nu s).restrict (FiniteSample.count ⁻¹' {n}) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert a t ha ih => simp only [Finset.sum_insert ha, Measure.restrict_add, ih]
  rw [hsum]
  simp_rw [Measure.restrict_smul, finitePoissonSampleLaw_restrict_count_eq]
  rw [Measure.map_finset_sum' (measurable_fixedSizeEmbed n).aemeasurable]
  simp only [Measure.map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  rw [smul_comm]
  rfl

/-- The entire Poisson mixture is the sum of its genuine fixed-count laws. -/
-- @node: lower_uniform_poisson_eq_sum
lemma lower_uniform_poisson_eq_sum {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (lam : NNReal) :
    lowerUniformPoissonMixture family lam =
      Measure.sum (fun n => poissonMeasure lam {n} •
        (uniformSampleMixture n family).map (fixedSizeEmbed n)) := by
  have hcover : (⋃ n : ℕ,
      (FiniteSample.count : FiniteSample Omega → ℕ) ⁻¹' {n}) = Set.univ := by
    ext s
    simp
  have hdis : Pairwise (Function.onFun Disjoint
      (fun n : ℕ => (FiniteSample.count : FiniteSample Omega → ℕ) ⁻¹' {n})) := by
    intro n m hnm
    exact (Set.disjoint_singleton.mpr hnm).preimage _
  rw [← Measure.restrict_univ (μ := lowerUniformPoissonMixture family lam), ← hcover,
    Measure.restrict_iUnion hdis
      (fun n => (measurableSet_singleton n).preimage measurable_finiteSample_count)]
  simp_rw [lower_uniform_poisson_count_fiber]

/-- A jointly count-dependent density is measurable if it is measurable on each
fixed-count observation space. -/
-- @node: lower_measurable_count_density
lemma lower_measurable_count_density
    (f : (n : ℕ) → Data n → ℝ≥0∞) (hf : ∀ n, Measurable (f n)) :
    Measurable (fun s : FiniteSample Omega => f s.count s.points) := by
  intro B hB
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact hf n hB

/-- Fixed-count density equalities lift to the actual ordered Poisson experiments. -/
-- @node: lower_uniform_poisson_withDensity
lemma lower_uniform_poisson_withDensity {S : Type*} [Fintype S] [Nonempty S]
    (nullFamily altFamily : S → ObsLaw) (lam : NNReal)
    (f : (n : ℕ) → Data n → ℝ≥0∞) (hf : ∀ n, Measurable (f n))
    (h : ∀ n, uniformSampleMixture n altFamily =
      (uniformSampleMixture n nullFamily).withDensity (f n)) :
    lowerUniformPoissonMixture altFamily lam =
      (lowerUniformPoissonMixture nullFamily lam).withDensity
        (fun s => f s.count s.points) := by
  rw [lower_uniform_poisson_eq_sum, lower_uniform_poisson_eq_sum, withDensity_sum]
  congr 1
  funext n
  rw [withDensity_smul_measure, h n]
  congr 1
  exact lower_map_withDensity_comp (uniformSampleMixture n nullFamily)
    (fixedSizeEmbed n) (measurable_fixedSizeEmbed n)
    (fun s => f s.count s.points) (lower_measurable_count_density f hf)

/-- Each fixed-outcome-sign cell product is nonnegative, as a quotient of
actual positive-null and nonnegative-alternative sample densities. -/
-- @node: lowerSampleCellRatio_nonneg
lemma lowerSampleCellRatio_nonneg (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (omega : Fin j → Bool) (o : Data n) :
    0 ≤ lowerSampleCellRatio theta k j n hk omega o := by
  rw [← lower_sample_sign_quotient_eq_cell_product theta k j n hp hk omega o]
  apply div_nonneg
  · exact Finset.sum_nonneg (fun lambda _ => Finset.prod_nonneg (fun i _ =>
      lower_alternative_recordDensity_nonneg theta k j hp lambda omega (o i)))
  · exact Finset.sum_nonneg (fun lambda _ => Finset.prod_nonneg (fun i _ =>
      (lower_null_recordDensity_pos theta k j hp lambda omega (o i)).le))

/-- Averaging the actual nonnegative likelihood over the common outcome sign
preserves nonnegativity. -/
-- @node: lowerOutcomeAveragedSampleRatio_nonneg
lemma lowerOutcomeAveragedSampleRatio_nonneg (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (o : Data n) :
    0 ≤ lowerOutcomeAveragedSampleRatio theta k j n hk o := by
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
  exact Finset.sum_nonneg (fun omega _ =>
    lowerSampleCellRatio_nonneg theta k j n hp hk omega o)

/-- The actual averaged likelihood is measurable on every count fiber. -/
-- @node: measurable_lowerOutcomeAveragedSampleRatio
@[fun_prop] lemma measurable_lowerOutcomeAveragedSampleRatio (theta : ℝ) (k j n : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) :
    Measurable (lowerOutcomeAveragedSampleRatio theta k j n hk) := by
  have hm : Measurable (fun o : Data n =>
      ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o)) := by
    simp_rw [← lower_full_sample_density_quotient_eq_cell_average theta k j n hp hk]
    exact (lowerUniformSampleDensity_measurable
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) n).div
      (lowerUniformSampleDensity_measurable
        (fun s : (Fin k → Bool) × (Fin j → Bool) =>
          lowerNullLaw theta k j hp s.1 s.2) n)
  simpa only [ENNReal.toReal_ofReal (lowerOutcomeAveragedSampleRatio_nonneg
    theta k j n hp hk _)] using hm.ennreal_toReal

/-- The ordered Poisson likelihood is the outcome-sign average of actual cell
products on the observed count fiber. -/
-- @node: lower_full_poisson_withDensity_cell_average
lemma lower_full_poisson_withDensity_cell_average (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    lowerUniformPoissonMixture
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) lam =
    (lowerUniformPoissonMixture
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam).withDensity
      (fun s => ENNReal.ofReal
        (lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points)) := by
  let nullFamily := fun s : (Fin k → Bool) × (Fin j → Bool) =>
    lowerNullLaw theta k j hp s.1 s.2
  let altFamily := fun s : (Fin k → Bool) × (Fin j → Bool) =>
    lowerAlternativeLaw theta k j hp s.1 s.2
  have hm (n : ℕ) : Measurable (fun o : Data n =>
      ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o)) := by
    simp_rw [← lower_full_sample_density_quotient_eq_cell_average theta k j n hp hk]
    exact (lowerUniformSampleDensity_measurable altFamily n).div
      (lowerUniformSampleDensity_measurable nullFamily n)
  exact lower_uniform_poisson_withDensity nullFamily altFamily lam
    (fun n o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o)) hm
    (fun n => lower_full_ordered_mixture_withDensity_cell_average theta k j n hp hk)

/-- The genuine Poisson Radon--Nikodym derivative is the same cell average, with
no abstract experiment or unproved likelihood representation. -/
-- @node: lower_full_poisson_rnDeriv_cell_average
lemma lower_full_poisson_rnDeriv_cell_average (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    (lowerUniformPoissonMixture
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerAlternativeLaw theta k j hp s.1 s.2) lam).rnDeriv
    (lowerUniformPoissonMixture
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam) =ᵐ[
    lowerUniformPoissonMixture
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) lam]
      (fun s => ENNReal.ofReal
        (lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points)) := by
  rw [lower_full_poisson_withDensity_cell_average theta k j hp hk lam]
  apply Measure.rnDeriv_withDensity
  apply lower_measurable_count_density
    (fun n o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o))
  intro n
  simp_rw [← lower_full_sample_density_quotient_eq_cell_average theta k j n hp hk]
  exact (lowerUniformSampleDensity_measurable
    (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerAlternativeLaw theta k j hp s.1 s.2) n).div
    (lowerUniformSampleDensity_measurable
      (fun s : (Fin k → Bool) × (Fin j → Bool) =>
        lowerNullLaw theta k j hp s.1 s.2) n)

/-- The complete ordered Poisson likelihood integrates to one under the actual
null prior. This follows from the alternative law's normalization. -/
-- @node: lower_full_poisson_likelihood_lintegral
lemma lower_full_poisson_likelihood_lintegral (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    (∫⁻ s, ENNReal.ofReal
      (lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points)
      ∂lowerUniformPoissonMixture
        (fun s : (Fin k → Bool) × (Fin j → Bool) =>
          lowerNullLaw theta k j hp s.1 s.2) lam) = 1 := by
  have h := congrArg (fun mu : Measure (FiniteSample Omega) => mu Set.univ)
    (lower_full_poisson_withDensity_cell_average theta k j hp hk lam)
  rw [measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h
  exact h.symm

/-- First-moment integrability of the actual likelihood is derived from its
normalization, including all Poisson count fibers. -/
-- @node: lower_full_poisson_likelihood_integrable
lemma lower_full_poisson_likelihood_integrable (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    Integrable (fun s => lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points)
      (lowerUniformPoissonMixture
        (fun s : (Fin k → Bool) × (Fin j → Bool) =>
          lowerNullLaw theta k j hp s.1 s.2) lam) := by
  have hm := lower_measurable_count_density
    (fun n o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o))
    (fun n => (measurable_lowerOutcomeAveragedSampleRatio theta k j n hp hk).ennreal_ofReal)
  have hi := integrable_toReal_of_lintegral_ne_top hm.aemeasurable (by
    rw [lower_full_poisson_likelihood_lintegral theta k j hp hk lam]
    exact ENNReal.one_ne_top)
  simpa only [ENNReal.toReal_ofReal (lowerOutcomeAveragedSampleRatio_nonneg
    theta k j _ hp hk _)] using hi

/-- The actual real-valued Poisson likelihood has mean one. -/
-- @node: lower_full_poisson_likelihood_integral
lemma lower_full_poisson_likelihood_integral (theta : ℝ) (k j : ℕ)
    (hp : LowerParameters theta k j) (hk : 0 < k) (lam : NNReal) :
    (∫ s, lowerOutcomeAveragedSampleRatio theta k j s.count hk s.points
      ∂lowerUniformPoissonMixture
        (fun s : (Fin k → Bool) × (Fin j → Bool) =>
          lowerNullLaw theta k j hp s.1 s.2) lam) = 1 := by
  have hm := lower_measurable_count_density
    (fun n o => ENNReal.ofReal (lowerOutcomeAveragedSampleRatio theta k j n hk o))
    (fun n => (measurable_lowerOutcomeAveragedSampleRatio theta k j n hp hk).ennreal_ofReal)
  have h := integral_toReal (μ := lowerUniformPoissonMixture
    (fun s : (Fin k → Bool) × (Fin j → Bool) =>
      lowerNullLaw theta k j hp s.1 s.2) lam) hm.aemeasurable
    (Filter.Eventually.of_forall (fun s => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (lowerOutcomeAveragedSampleRatio_nonneg
    theta k j _ hp hk _), lower_full_poisson_likelihood_lintegral theta k j hp hk lam,
    ENNReal.toReal_one] at h
  exact h

end CausalSmith.Stat.DensityEffectRoughNull
