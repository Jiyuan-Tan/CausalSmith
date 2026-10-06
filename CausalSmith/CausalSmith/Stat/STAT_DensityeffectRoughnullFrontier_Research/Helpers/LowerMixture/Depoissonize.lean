module
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OutcomeWeights
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.MixtureTransfer
public import CausalSmith.Stat.STAT_DensityeffectRoughnullFrontier_Research.Helpers.LowerMixture.OrderedPoisson
public import Causalean.Stat.Minimax.Multinomial.TwoSampleL1.FinitePoissonPrefix
public import Causalean.Mathlib.Probability.Poisson.FinitePartition.Depoissonization
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Real.Pointwise

/-!
Total-variation cancellation for the common short-count fallback in the fixed-sample experiment.
-/

public section

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
namespace CausalSmith.Stat.DensityEffectRoughNull


/-- Both hypotheses use the same fallback law on a short Poisson sample;
their difference is exactly scaled by the success probability. -/
-- @node: common_fallback_tv
lemma common_fallback_tv (n : ℕ) (μ ν R : Measure (Data n))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure R]
    (delta : ℝ) (hd : delta ∈ Set.Ico 0 1) :
    Causalean.Stat.tvDist
      (ENNReal.ofReal (1 - delta) • μ + ENNReal.ofReal delta • R)
      (ENNReal.ofReal (1 - delta) • ν + ENNReal.ofReal delta • R) =
      (1 - delta) * Causalean.Stat.tvDist μ ν := by
  have hscale : 0 ≤ 1 - delta := sub_nonneg.mpr hd.2.le
  have hmass (ρ : Measure (Data n)) [IsProbabilityMeasure ρ] (S : Set (Data n)) :
      (ENNReal.ofReal (1 - delta) • ρ + ENNReal.ofReal delta • R).real S =
        (1 - delta) * ρ.real S + delta * R.real S := by
    rw [measureReal_add_apply
      (by simp only [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ρ S))
      (by simp only [Measure.smul_apply, smul_eq_mul]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top R S))]
    simp only [measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal hscale,
      ENNReal.toReal_ofReal hd.1]
  unfold Causalean.Stat.tvDist
  rw [Real.mul_iSup_of_nonneg hscale]
  apply iSup_congr
  intro S
  rw [hmass μ, hmass ν]
  rw [show (1 - delta) * μ.real S.val + delta * R.real S.val -
      ((1 - delta) * ν.real S.val + delta * R.real S.val) =
        (1 - delta) * (μ.real S.val - ν.real S.val) by ring,
    abs_mul, abs_of_nonneg hscale]

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Stat.Minimax.Multinomial.TwoSampleL1

/-- The common prefix map preserves the entire finite sign prior, with a common
fallback on the short-count event, as in (46). -/
-- @node: lower_uniform_poisson_prefix
lemma lower_uniform_poisson_prefix {S : Type*} [Fintype S] [Nonempty S]
    (family : S → ObsLaw) (lam : NNReal) (x0 : Omega) (n : ℕ) :
    (lowerUniformPoissonMixture family lam).map (finitePoissonPrefix x0 n) =
      poissonMeasure lam (Set.Ici n) • uniformSampleMixture n family +
      poissonMeasure lam (Set.Iio n) • Measure.dirac (fun _ : Fin n => x0) := by
  classical
  unfold lowerUniformPoissonMixture uniformSampleMixture
    Causalean.Stat.Minimax.Mixture.uniformMixture Causalean.Stat.mixture
  rw [Measure.map_finset_sum' (measurable_finitePoissonPrefix x0 n).aemeasurable]
  simp_rw [Measure.map_smul, finitePoissonSampleLaw_map_prefix, smul_add, smul_smul]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [smul_smul, mul_comm]
    rfl
  · rw [← Finset.sum_smul]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← mul_assoc, ENNReal.mul_inv_cancel]
    · simp
    · exact_mod_cast Fintype.card_ne_zero
    · simp

/-- Prefix reconstruction contracts TV; cancellation of its common fallback
leaves precisely the successful-count mass multiplying the fixed-sample distance. -/
-- @node: lower_fixed_tv_scaled_le_poisson
lemma lower_fixed_tv_scaled_le_poisson {S : Type*} [Fintype S] [Nonempty S]
    (f0 f1 : S → ObsLaw) (lam : NNReal) (n : ℕ)
    (hd : (poissonMeasure lam (Set.Iio n)).toReal < 1) :
    (1 - (poissonMeasure lam (Set.Iio n)).toReal) *
      Causalean.Stat.tvDist (uniformSampleMixture n f0) (uniformSampleMixture n f1) ≤
    Causalean.Stat.tvDist (lowerUniformPoissonMixture f0 lam)
      (lowerUniformPoissonMixture f1 lam) := by
  letI (s : S) : IsProbabilityMeasure (dataLaw (f0 s) n) := by
    unfold dataLaw; infer_instance
  letI (s : S) : IsProbabilityMeasure (dataLaw (f1 s) n) := by
    unfold dataLaw; infer_instance
  letI : IsProbabilityMeasure (uniformSampleMixture n f0) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  letI : IsProbabilityMeasure (uniformSampleMixture n f1) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  let x0 : Omega := (0, false, 0)
  let p := poissonMeasure lam (Set.Iio n)
  let q := poissonMeasure lam (Set.Ici n)
  have hp : p ≠ ⊤ := measure_ne_top _ _
  have hq : q ≠ ⊤ := measure_ne_top _ _
  have hsum : q + p = 1 := by
    dsimp only [q, p]
    rw [show Set.Iio n = (Set.Ici n)ᶜ by ext i; simp]
    simpa using measure_add_measure_compl (μ := poissonMeasure lam) measurableSet_Ici
  have hr : q.toReal = 1 - p.toReal := by
    have hh := congrArg ENNReal.toReal hsum
    rw [ENNReal.toReal_add hq hp, ENNReal.toReal_one] at hh
    linarith
  have hp' : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hp
  have hq' : ENNReal.ofReal (1 - p.toReal) = q := by
    rw [← hr]; exact ENNReal.ofReal_toReal hq
  have hfall := common_fallback_tv n (uniformSampleMixture n f0)
    (uniformSampleMixture n f1) (Measure.dirac (fun _ : Fin n => x0)) p.toReal
    ⟨ENNReal.toReal_nonneg, hd⟩
  rw [hq', hp'] at hfall
  rw [← hfall, ← lower_uniform_poisson_prefix f0 lam x0 n,
    ← lower_uniform_poisson_prefix f1 lam x0 n]
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  rw [map_measureReal_apply_of_aemeasurable
      (measurable_finitePoissonPrefix x0 n).aemeasurable hA,
    map_measureReal_apply_of_aemeasurable
      (measurable_finitePoissonPrefix x0 n).aemeasurable hA]
  exact le_ciSup Causalean.Stat.bddAbove_tvDist_range
    ⟨finitePoissonPrefix x0 n ⁻¹' A, hA.preimage (measurable_finitePoissonPrefix x0 n)⟩

/-- The explicit Poisson lower-tail estimate (47) is below one half from n=16. -/
-- @node: lower_poisson_short_count_le_half
lemma lower_poisson_short_count_le_half (n : ℕ) (hn : 16 ≤ n) :
    (poissonMeasure (2 * (n : NNReal)) (Set.Iio n)).toReal ≤ 1 / 2 := by
  have hlog : Real.log 2 ≤ 3 / 4 := by linarith [Real.log_two_lt_d9]
  have hnn : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 2 ≤ Real.exp ((n : ℝ) * (1 - Real.log 2)) := by
    have he := Real.add_one_le_exp ((n : ℝ) * (1 - Real.log 2))
    nlinarith
  have he : Real.exp (-(n : ℝ) * (1 - Real.log 2)) ≤ 1 / 2 := by
    rw [show -(n : ℝ) * (1 - Real.log 2) = -((n : ℝ) * (1 - Real.log 2)) by ring,
      Real.exp_neg]
    rw [← one_div]
    apply (div_le_iff₀ (Real.exp_pos _)).2
    linarith
  have ht := poisson_two_n_lower_tail n
  change poissonMeasure (2 * (n : NNReal)) (Set.Iio n) ≤ _ at ht
  have htr := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le] at htr
  exact htr.trans he

/-- Equations (45)--(47) transfer the 1/8 Poisson TV budget to a 1/4
fixed-sample budget, using the same measurable reconstruction in both hypotheses. -/
-- @node: lower_fixed_tv_le_quarter
lemma lower_fixed_tv_le_quarter {S : Type*} [Fintype S] [Nonempty S]
    (f0 f1 : S → ObsLaw) (n : ℕ) (hn : 16 ≤ n)
    (htv : Causalean.Stat.tvDist (lowerUniformPoissonMixture f0 (2 * (n : NNReal)))
      (lowerUniformPoissonMixture f1 (2 * (n : NNReal))) ≤ 1 / 8) :
    Causalean.Stat.tvDist (uniformSampleMixture n f0) (uniformSampleMixture n f1) ≤ 1 / 4 := by
  have hd := lower_poisson_short_count_le_half n hn
  have hs := lower_fixed_tv_scaled_le_poisson f0 f1 (2 * (n : NNReal)) n (by linarith)
  have hb := hs.trans htv
  letI (s : S) : IsProbabilityMeasure (dataLaw (f0 s) n) := by
    unfold dataLaw; infer_instance
  letI (s : S) : IsProbabilityMeasure (dataLaw (f1 s) n) := by
    unfold dataLaw; infer_instance
  letI : IsProbabilityMeasure (uniformSampleMixture n f0) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  letI : IsProbabilityMeasure (uniformSampleMixture n f1) :=
    Causalean.Stat.Minimax.Mixture.uniformMixture_isProbability _
  have hv := Causalean.Stat.tvDist_nonneg
    (μ := uniformSampleMixture n f0) (ν := uniformSampleMixture n f1)
  nlinarith

end CausalSmith.Stat.DensityEffectRoughNull
