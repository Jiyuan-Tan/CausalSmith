module
public import Causalean.Stat.Concentration.Poisson.Threshold
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.IndependentPrefix.ProductPools.Risk
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Finite-prefix risk transfer for independent product pools

This module turns a bounded statistic for heterogeneous independent Poisson prefixes into a
total measurable statistic for fixed finite pools. It controls zero-output overflow by marginal
Poisson tails and specializes those tails when each Poisson mean is one eighth of its pool size.
-/

public section

namespace Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily

open MeasureTheory ProbabilityTheory
open Causalean.Stat
open scoped BigOperators ENNReal NNReal
attribute [local instance] Classical.propDecidable

/-- For [a finite coordinate type](hyp:I), [coordinatewise observation spaces](hyp:X),
[coordinatewise probability laws](hyp:P), [Poisson intensities](hyp:lambda), [fixed pool
capacities](hyp:N), [a prefix statistic](hyp:T), [its measurability](hyp:hT), [its values between
minus one and one](hyp:hTmem), [a target](hyp:theta), and [that target's membership between minus
one and one](hyp:htheta), [the squared risk of finite-prefix averaging with zero output on overflow
is at most the Poissonized risk plus the sum of the marginal overflow probabilities](goal). -/
theorem zero_overflow_prefix_risk {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (P : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (lambda : I → NNReal) (N : I → Nat) {T : PrefixFamily X → Real}
    (hT : Measurable T) (hTmem : ∀ s, T s ∈ Set.Icc (-1) 1)
    {theta : Real} (htheta : theta ∈ Set.Icc (-1) 1) :
    sqRisk (fixedPoolsLaw P N) (prefixRaoBlackwellStatistic lambda T 0) theta ≤
      sqRisk (independentPoissonPrefixLaw P lambda) T theta +
        ∑ i, (poissonMeasure (lambda i)).real (Set.Ioi (N i)) := by
  classical
  have hTb : UniformlyBounded T := ⟨1, by norm_num, fun s => abs_le.mpr (hTmem s)⟩
  have hCb : ∀ z : RandomizedPools X N, |cappedPrefixStatistic T 0 z| ≤ 1 := by
    intro z
    by_cases hz : ∀ i, (z i).2 ≤ N i
    · rw [cappedPrefixStatistic, dif_pos hz]
      exact abs_le.mpr (hTmem _)
    · rw [cappedPrefixStatistic, dif_neg hz]
      norm_num
  let mu := randomizedPoolsLaw P lambda N
  let : IsProbabilityMeasure mu := by
    dsimp [mu, randomizedPoolsLaw]
    infer_instance
  let good := nonoverflowSet (X := X) N
  have hgood : MeasurableSet good := measurableSet_nonoverflowSet N
  have hInt : Integrable (fun z => (cappedPrefixStatistic T 0 z - theta) ^ 2) mu := by
    apply Integrable.of_bound
      (((measurable_cappedPrefixStatistic hT 0).sub measurable_const).pow_const 2
        ).aestronglyMeasurable 4
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hdist : |cappedPrefixStatistic T 0 z - theta| ≤ 2 :=
      (abs_sub _ _).trans (by
        have ht := abs_le.mpr htheta
        linarith [hCb z])
    change (cappedPrefixStatistic T 0 z - theta) ^ 2 ≤ 4
    nlinarith [sq_abs (cappedPrefixStatistic T 0 z - theta),
      abs_nonneg (cappedPrefixStatistic T 0 z - theta)]
  have hsplit : sqRisk mu (cappedPrefixStatistic T 0) theta =
      sqRisk (mu.restrict good) (cappedPrefixStatistic T 0) theta +
        sqRisk (mu.restrict goodᶜ) (cappedPrefixStatistic T 0) theta := by
    unfold sqRisk
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := mu) hgood,
      integral_add_measure hInt.restrict hInt.restrict]
  have hcomp : goodᶜ = overflowSet (X := X) N := by
    simp only [good, nonoverflowSet_eq_compl_overflowSet, compl_compl]
  have hbad : sqRisk (mu.restrict (overflowSet (X := X) N))
      (cappedPrefixStatistic T 0) theta = theta ^ 2 * mu.real (overflowSet (X := X) N) := by
    unfold sqRisk
    have hae : ∀ᵐ z ∂mu.restrict (overflowSet (X := X) N),
        (cappedPrefixStatistic T 0 z - theta) ^ 2 = theta ^ 2 := by
      filter_upwards [ae_restrict_mem (measurableSet_overflowSet N)] with z hz
      obtain ⟨i, hi⟩ := hz
      rw [cappedPrefixStatistic, dif_neg (fun hz => (Nat.not_lt_of_ge (hz i)) hi)]
      ring
    rw [integral_congr_ae hae, integral_const]
    simp only [smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    ring
  have hthetaSq : theta ^ 2 ≤ 1 := by
    have ht := abs_le.mpr htheta
    nlinarith [sq_abs theta, abs_nonneg theta]
  calc
    _ ≤ sqRisk mu (cappedPrefixStatistic T 0) theta :=
      sqRisk_prefixRaoBlackwellStatistic_le_capped P lambda N hT hTmem (by norm_num)
    _ = sqRisk ((independentPoissonPrefixLaw P lambda).restrict
        {s : PrefixFamily X | ∀ i, (s i).count ≤ N i}) T theta +
        theta ^ 2 * mu.real (overflowSet (X := X) N) := by
      rw [hsplit, hcomp, hbad]
      rw [sqRisk_cappedPrefixStatistic_restrict_nonoverflow_eq P lambda N hT 0 theta]
    _ ≤ sqRisk (independentPoissonPrefixLaw P lambda) T theta +
        mu.real (overflowSet (X := X) N) :=
      add_le_add
        (sqRisk_independentPoissonPrefixLaw_restrict_nonoverflow_le P lambda N hT hTb theta)
        (by
          simpa using (mul_le_mul_of_nonneg_right hthetaSq
            (by positivity : 0 ≤ mu.real (overflowSet (X := X) N))))
    _ ≤ _ := add_le_add le_rfl (overflowSet_measureReal_le_sum_poisson_tails P lambda N)

/-- For [a pool capacity](hyp:N), [a Poisson prefix whose mean is one eighth of that
capacity has overflow probability at most the negative-capacity exponential](goal). -/
theorem eighth_pool_poisson_overflow (N : Nat) :
    (poissonMeasure ((N : NNReal) / 8)).real (Set.Ioi N) ≤ Real.exp (-(N : Real)) := by
  have htail := Causalean.Stat.Concentration.Poisson.poisson_upper_tail_mul_exp_le
    ((N : NNReal) / 8) N (r := 7) (by norm_num)
  have hlog : 15 / 8 ≤ Real.log 8 := by
    have hh : Real.log (8 : Real) = 3 * Real.log 2 := by
      rw [show (8 : Real) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [hh]
    linarith [Real.log_two_gt_d9]
  have hmul : Real.exp (-(N : Real)) *
      Real.exp (-7 * (((N : NNReal) / 8 : NNReal) : Real)) =
      Real.exp (-(15 / 8) * (N : Real)) := by
    rw [← Real.exp_add]
    congr 1
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_ofNat]
    ring
  apply (mul_le_mul_iff_left₀
    (Real.exp_pos (-7 * (((N : NNReal) / 8 : NNReal) : Real)))).mp
  calc
    _ ≤ Real.exp (-Real.log (1 + 7) * (N : Real)) := htail
    _ ≤ Real.exp (-(15 / 8) * (N : Real)) := by
      apply Real.exp_le_exp.mpr
      norm_num only at *
      nlinarith [(Nat.cast_nonneg N : (0 : Real) ≤ N)]
    _ = _ := hmul.symm

/-- For [a finite coordinate type](hyp:I), [coordinatewise observation spaces](hyp:X),
[coordinatewise probability laws](hyp:P), [fixed pool capacities](hyp:N), [a prefix
statistic](hyp:T), [its measurability](hyp:hT), [its values between minus one and
one](hyp:hTmem), [a target](hyp:theta), [a proposed risk bound](hyp:Ab), [the target's membership
between minus one and one](hyp:htheta), and [the Poissonized squared-risk
bound](hyp:hA), [finite independent prefix averaging at one-eighth intensities is measurable,
remains between minus one and one, and has fixed-pool squared risk at most that bound plus the sum
of negative-capacity exponentials](goal).
-/
theorem finite_prefix_transfer {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, MeasurableSpace (X i)]
    (P : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (P i)]
    (N : I → Nat) {T : PrefixFamily X → Real}
    (hT : Measurable T) (hTmem : ∀ s, T s ∈ Set.Icc (-1) 1)
    {theta Ab : Real} (htheta : theta ∈ Set.Icc (-1) 1)
    (hA : sqRisk (independentPoissonPrefixLaw P (fun i => (N i : NNReal) / 8)) T theta ≤ Ab) :
    Measurable (prefixRaoBlackwellStatistic (N := N) (fun i => (N i : NNReal) / 8) T 0) ∧
    (∀ s, prefixRaoBlackwellStatistic (N := N) (fun i => (N i : NNReal) / 8) T 0 s ∈ Set.Icc
      (-1) 1) ∧
    sqRisk (fixedPoolsLaw P N)
      (prefixRaoBlackwellStatistic (N := N) (fun i => (N i : NNReal) / 8) T 0) theta ≤
        Ab + ∑ i, Real.exp (-(N i : Real)) := by
  classical
  have hCb : ∀ z : RandomizedPools X N, |cappedPrefixStatistic T 0 z| ≤ 1 := by
    intro z
    by_cases hz : ∀ i, (z i).2 ≤ N i
    · rw [cappedPrefixStatistic, dif_pos hz]
      exact abs_le.mpr (hTmem _)
    · rw [cappedPrefixStatistic, dif_neg hz]
      norm_num
  refine ⟨?_, ?_, ?_⟩
  · fun_prop
  · intro s
    exact abs_le.mp (abs_kernelMean_le (independentPoissonCountKernel _)
      (by norm_num : (0 : Real) ≤ 1) hCb s)
  · calc
      _ ≤ sqRisk (independentPoissonPrefixLaw P (fun i => (N i : NNReal) / 8)) T theta +
          ∑ i, (poissonMeasure ((N i : NNReal) / 8)).real (Set.Ioi (N i)) :=
        zero_overflow_prefix_risk P _ N hT hTmem htheta
      _ ≤ Ab + ∑ i, Real.exp (-(N i : Real)) :=
        add_le_add hA (Finset.sum_le_sum (fun i _ => eighth_pool_poisson_overflow (N i)))

end Causalean.Stat.FiniteRaoBlackwell.IndependentPoissonPrefix.FiniteFamily
