import Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture.MarkedPoisson.Basic

/-!
# Palm comparison for marked Poisson mixtures

This module proves the Palm decomposition that reduces marked-Poisson discrepancy to aggregate-Poisson discrepancy.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture

namespace NormalizedFiniteSignedMomentCertificate

/-- The [stated conclusion](goal) follows from [the source measurable space](hyp:X), [the observation measurable space](hyp:Y), [the first probability law](hyp:μ), [the second probability law](hyp:ν), [the experiment kernel](hyp:K). -/
theorem tvDist_bind_le
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K : Kernel X Y) [IsMarkovKernel K] :
    Causalean.Stat.tvDist (K ∘ₘ μ) (K ∘ₘ ν) ≤
      Causalean.Stat.tvDist μ ν := by
  let _ : IsProbabilityMeasure (K ∘ₘ μ) := by infer_instance
  let _ : IsProbabilityMeasure (K ∘ₘ ν) := by infer_instance
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hreal (ρ : Measure X) [IsProbabilityMeasure ρ] :
      (K ∘ₘ ρ).real A = ∫ x, (K x A).toReal ∂ρ := by
    rw [measureReal_def, Measure.bind_apply hA K.aemeasurable,
      integral_toReal (K.measurable_coe hA).aemeasurable]
    filter_upwards with x
    exact measure_lt_top (K x) A
  rw [hreal μ, hreal ν]
  have hrange : ∀ x, (K x A).toReal ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    constructor
    · exact ENNReal.toReal_nonneg
    · have hle := ENNReal.toReal_mono (measure_ne_top (K x) _)
        (measure_mono (Set.subset_univ A))
      simpa using hle
  simpa only [zero_add, mul_one, Causalean.Stat.tvDist] using
    Causalean.Stat.tvDist_integral_range μ ν
      (fun x => (K x A).toReal) (K.measurable_coe hA).ennreal_toReal
      0 1 (by norm_num) (by simpa using hrange)

/-- The [stated conclusion](goal) follows from [the source measurable space](hyp:X), [the first probability law](hyp:μ), [the second probability law](hyp:ν), [the reference measure](hyp:ξ), [the centering constant](hyp:c), [the centering condition](hyp:hc), [the tail-scale constant](hyp:A). -/
theorem measureReal_add_ennreal_smul_add
    {X : Type*} [MeasurableSpace X]
    (μ ν ξ : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure ξ] (c : ℝ≥0∞) (hc : c ≠ ∞) (A : Set X) :
    (μ + c • (ν + ξ)).real A =
      μ.real A + c.toReal * (ν.real A + ξ.real A) := by
  let _ : IsFiniteMeasure (c • (ν + ξ)) := Measure.smul_finite _ hc
  rw [MeasureTheory.measureReal_add_apply
        (μ₁ := μ) (μ₂ := c • (ν + ξ)),
    MeasureTheory.measureReal_ennreal_smul_apply,
    MeasureTheory.measureReal_add_apply (μ₁ := ν) (μ₂ := ξ)]

/-- The [defined object](goal) is determined by [the marked component](hyp:first), [the observed count vector](hyp:z), [the number of independent coordinates](hyp:k) and is given by [the following defining expression](step:1). -/
def palmSplitEmbed
    (first : Bool) (z : AggregatePoissonObservation) (k : ℕ) :
    MarkedPoissonObservation :=
  if k ≤ z.1 then
    if first then ((k + 1, 0), (z.1 - k, z.2))
    else ((0, k + 1), (z.1 - k, z.2))
  else ((0, 0), (0, 0))

/-- The [defined object](goal) is determined by [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z) and is given by [the following defining expression](step:1). -/
noncomputable def palmSplitSubmeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  ∑ k ∈ Finset.range (z.1 + 1),
    ENNReal.ofReal
      ((binomial z.1 q).real {k} * (1 / ((k : ℝ) + 1))) •
        Measure.dirac (palmSplitEmbed first z k)

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z). -/
theorem palmSplitSubmeasure_univ_le
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    palmSplitSubmeasure q first z Set.univ ≤ 1 := by
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _),
    smul_eq_mul, mul_one]
  calc
    ∑ k ∈ Finset.range (z.1 + 1),
        ENNReal.ofReal ((binomial z.1 q).real {k} * (1 / ((k : ℝ) + 1))) ≤
        ∑ k ∈ Finset.range (z.1 + 1), (binomial z.1 q) {k} := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def]
      apply ENNReal.ofReal_le_ofReal
      have hprob : 0 ≤ (binomial z.1 q).real {k} := measureReal_nonneg
      have hrecip : 1 / ((k : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).2 (by norm_num)
      nlinarith
    _ ≤ (binomial z.1 q) Set.univ := by
      rw [sum_measure_singleton]
      exact measure_mono (Set.subset_univ _)
    _ = 1 := by simp

/-- The [defined object](goal) is determined by [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z) and is given by [the following defining expression](step:1). -/
noncomputable def palmSplitMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    Measure MarkedPoissonObservation :=
  palmSplitSubmeasure q first z +
    (1 - palmSplitSubmeasure q first z Set.univ) •
      Measure.dirac ((0, 0), (0, 0))

/-- The [defined object](goal) is determined by [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z) and is given by [the following defining expression](step:1). -/
noncomputable instance palmSplitMeasure_isProbabilityMeasure
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation) :
    IsProbabilityMeasure (palmSplitMeasure q first z) := by
  constructor
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  exact add_tsub_cancel_of_le (palmSplitSubmeasure_univ_le q first z)

/-- The [defined object](goal) is determined by [the rate intercept](hyp:q), [the marked component](hyp:first) and is given by [the following defining expression](step:1). -/
noncomputable def palmSplitKernel
    (q : unitInterval) (first : Bool) :
    Kernel AggregatePoissonObservation MarkedPoissonObservation :=
  Kernel.ofFunOfCountable (palmSplitMeasure q first)

/-- The [defined object](goal) is determined by [the rate intercept](hyp:q), [the marked component](hyp:first) and is given by [the following defining expression](step:1). -/
noncomputable instance palmSplitKernel_isMarkovKernel
    (q : unitInterval) (first : Bool) :
    IsMarkovKernel (palmSplitKernel q first) where
  isProbabilityMeasure z := palmSplitMeasure_isProbabilityMeasure q first z

/-- The [defined object](goal) is determined by [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t) and is given by [the following defining expression](step:1). -/
def palmSplitTarget
    (first : Bool) (k s t : ℕ) : MarkedPoissonObservation :=
  if first then ((k + 1, 0), (s, t)) else ((0, k + 1), (s, t))

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitSubmeasure_target
    (q : unitInterval) (first : Bool) (k s t : ℕ) :
    palmSplitSubmeasure q first (k + s, t) {palmSplitTarget first k s t} =
      ENNReal.ofReal
        ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1))) := by
  classical
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  rw [Finset.sum_eq_single k]
  · rw [Measure.smul_apply, Measure.dirac_apply_of_mem, smul_eq_mul, mul_one]
    cases first <;> simp [palmSplitEmbed, palmSplitTarget]
  · intro j hj hjk
    rw [Measure.smul_apply]
    have hjle : j ≤ k + s := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hne : palmSplitEmbed first (k + s, t) j ≠
        palmSplitTarget first k s t := by
      cases first <;> simp [palmSplitEmbed, palmSplitTarget, hjle] at * <;> omega
    simp [hne]
  · simp

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitSubmeasure_target_eq_ite
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitSubmeasure q first z {palmSplitTarget first k s t} =
      if z = (k + s, t) then
        ENNReal.ofReal
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 := by
  classical
  by_cases hz : z = (k + s, t)
  · subst z
    rw [if_pos rfl]
    exact palmSplitSubmeasure_target q first k s t
  · rw [if_neg hz, palmSplitSubmeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Measure.smul_apply]
    have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hne : palmSplitEmbed first z j ≠ palmSplitTarget first k s t := by
      intro heq
      cases z with
      | mk n c =>
        simp only [palmSplitEmbed, palmSplitTarget, hjle, ↓reduceIte] at heq hz
        cases first <;> simp_all <;> omega
    simp [hne]

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitMeasure_target_eq_ite
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitMeasure q first z {palmSplitTarget first k s t} =
      if z = (k + s, t) then
        ENNReal.ofReal
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 := by
  have hne : palmSplitTarget first k s t ≠ ((0, 0), (0, 0)) := by
    cases first <;> simp [palmSplitTarget]
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Set.indicator_of_notMem (by simpa using hne.symm), smul_eq_mul,
    mul_zero, add_zero]
  exact palmSplitSubmeasure_target_eq_ite q first z k s t

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitMeasure_wrong_target
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k s t : ℕ) :
    palmSplitMeasure q (!first) z {palmSplitTarget first k s t} = 0 := by
  classical
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  have hne : palmSplitTarget first k s t ≠ ((0, 0), (0, 0)) := by
    cases first <;> simp [palmSplitTarget]
  rw [Set.indicator_of_notMem (by simpa using hne.symm), smul_eq_mul,
    mul_zero, add_zero]
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hemb : palmSplitEmbed (!first) z j ≠ palmSplitTarget first k s t := by
    cases first <;> simp [palmSplitEmbed, palmSplitTarget, hjle]
  simp [hemb]

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the observed count vector](hyp:z), [the number of independent coordinates](hyp:k), [the supplied input l](hyp:l), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitMeasure_both_positive
    (q : unitInterval) (first : Bool) (z : AggregatePoissonObservation)
    (k l s t : ℕ) :
    palmSplitMeasure q first z {((k + 1, l + 1), (s, t))} = 0 := by
  classical
  rw [palmSplitMeasure, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton _)]
  rw [Set.indicator_of_notMem (by simp), smul_eq_mul, mul_zero, add_zero]
  rw [palmSplitSubmeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hemb : palmSplitEmbed first z j ≠ ((k + 1, l + 1), (s, t)) := by
    cases first <;> simp [palmSplitEmbed, hjle]
  simp [hemb]

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the observed count vector](hyp:z), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplitMeasure_no_labeled_eq
    (q : unitInterval) (z : AggregatePoissonObservation) (s t : ℕ) :
    palmSplitMeasure q false z {((0, 0), (s, t))} =
      palmSplitMeasure q true z {((0, 0), (s, t))} := by
  classical
  have hsub (first : Bool) :
      palmSplitSubmeasure q first z {((0, 0), (s, t))} = 0 := by
    rw [palmSplitSubmeasure, Measure.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [Measure.smul_apply]
    have hjle : j ≤ z.1 := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    have hemb : palmSplitEmbed first z j ≠ ((0, 0), (s, t)) := by
      cases first <;> simp [palmSplitEmbed, hjle]
    simp [hemb]
  have huniv (first : Bool) :
      palmSplitSubmeasure q first z Set.univ =
        ∑ j ∈ Finset.range (z.1 + 1),
          ENNReal.ofReal
            ((binomial z.1 q).real {j} * (1 / ((j : ℝ) + 1))) := by
    rw [palmSplitSubmeasure, Measure.finsetSum_apply]
    simp
  unfold palmSplitMeasure
  rw [Measure.add_apply, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply, hsub, hsub, huniv, huniv]

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the geometric decay factor](hyp:ρ), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplit_bind_wrong_target
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k s t : ℕ) :
    (palmSplitKernel q (!first) ∘ₘ ρ).real
      {palmSplitTarget first k s t} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q (!first) z
      {palmSplitTarget first k s t} = 0 from
    fun z => palmSplitMeasure_wrong_target q first z k s t]
  simp

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the marked component](hyp:first), [the geometric decay factor](hyp:ρ), [the number of independent coordinates](hyp:k), [the supplied input l](hyp:l), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplit_bind_both_positive
    (q : unitInterval) (first : Bool) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (k l s t : ℕ) :
    (palmSplitKernel q first ∘ₘ ρ).real {((k + 1, l + 1), (s, t))} = 0 := by
  rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  simp_rw [show ∀ z, palmSplitKernel q first z {((k + 1, l + 1), (s, t))} = 0 from
    fun z => palmSplitMeasure_both_positive q first z k l s t]
  simp

/-- The [stated conclusion](goal) follows from [the rate intercept](hyp:q), [the geometric decay factor](hyp:ρ), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplit_bind_no_labeled_eq
    (q : unitInterval) (ρ : Measure AggregatePoissonObservation)
    [IsProbabilityMeasure ρ] (s t : ℕ) :
    (palmSplitKernel q false ∘ₘ ρ).real {((0, 0), (s, t))} =
      (palmSplitKernel q true ∘ₘ ρ).real {((0, 0), (s, t))} := by
  rw [measureReal_def, measureReal_def,
    Measure.bind_apply (measurableSet_singleton _) (by fun_prop),
    Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
  apply congrArg ENNReal.toReal
  apply lintegral_congr
  intro z
  exact palmSplitMeasure_no_labeled_eq q z s t

/-- The [stated conclusion](goal) follows from [the source measurable space](hyp:X), [the observation measurable space](hyp:Y), [the first probability law](hyp:μ), [the second probability law](hyp:ν), [the evaluation point](hyp:x), [the supplied input y](hyp:y). -/
theorem prod_real_singleton
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : X) (y : Y) :
    (μ.prod ν).real {(x, y)} = μ.real {x} * ν.real {y} := by
  rw [measureReal_def, ← Set.singleton_prod_singleton, Measure.prod_prod,
    ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]

/-- The [stated conclusion](goal) follows from [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the lower endpoint](hyp:r), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [the supplied input hr](hyp:hr), [positive total intensity](hyp:ht), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s). -/
theorem poisson_binomial_split
    (u v r : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hr : 0 ≤ r)
    (ht : 0 < u + v) (k s : ℕ) :
    (poissonMeasure (Real.toNNReal ((u + v) * r))).real {k + s} *
        (binomial (k + s)
          (⟨u / (u + v), by
            constructor
            · positivity
            · rw [div_le_one ht]
              linarith⟩ : unitInterval)).real {k} =
      (poissonMeasure (Real.toNNReal (u * r))).real {k} *
        (poissonMeasure (Real.toNNReal (v * r))).real {s} := by
  rw [poissonMeasure_real_singleton, binomial_real_singleton,
    poissonMeasure_real_singleton, poissonMeasure_real_singleton]
  have hfacNat :=
    Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k s)
  rw [Nat.add_sub_cancel_left] at hfacNat
  have hfac :
      ((k + s).choose k : ℝ) * (k.factorial : ℝ) * (s.factorial : ℝ) =
        ((k + s).factorial : ℝ) := by
    exact_mod_cast hfacNat
  simp only [Nat.add_sub_cancel_left]
  rw [Real.coe_toNNReal _ (mul_nonneg (add_nonneg hu hv) hr),
    Real.coe_toNNReal _ (mul_nonneg hu hr),
    Real.coe_toNNReal _ (mul_nonneg hv hr)]
  rw [show (1 - u / (u + v) : ℝ) = v / (u + v) by
    field_simp
    ring]
  have hexp : Real.exp (-((u + v) * r)) =
      Real.exp (-(u * r)) * Real.exp (-(v * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp, pow_add, mul_pow, mul_pow, div_pow, div_pow]
  field_simp
  rw [← hfac]
  ring

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the latent mass](hyp:p), [the supplied input hrate](hyp:hrate), [the supplied input hpa](hyp:hpa), [the number of independent coordinates](hyp:k). -/
theorem poisson_palm
    (ε a u p : ℝ) (hrate : 0 ≤ u * (ε * (p + a)))
    (hpa : 0 < p + a) (k : ℕ) :
    a / (p + a) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k + 1} =
      (u * ε * a / ((k : ℝ) + 1)) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k} := by
  rw [poissonMeasure_real_singleton, poissonMeasure_real_singleton,
    Real.coe_toNNReal _ hrate, show k + 1 = Nat.succ k by omega,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the latent mass](hyp:p), [the supplied input sign](hyp:sign), [the supplied input hsign](hyp:hsign), [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem markedPoissonLaw_real_target_sub
    (ε a u v p sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    (first : Bool) (k s t : ℕ) :
    (markedPoissonLaw ε a u v (fun _ => sign) false p).real
        {palmSplitTarget first k s t} -
      (markedPoissonLaw ε a u v (fun _ => sign) true p).real
        {palmSplitTarget first k s t} =
      (if first then -sign else sign) *
        (poissonMeasure
          (Real.toNNReal (u * (ε * (p + a))))).real {k + 1} *
        (poissonMeasure
          (Real.toNNReal (v * (ε * (p + a))))).real {s} *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by
  rcases hsign with rfl | rfl <;> cases first <;>
    simp [markedPoissonLaw, palmSplitTarget, branchMark, treatedMass,
      prod_real_singleton, poissonMeasure_real_singleton,
      zero_pow (by omega : 1 + k ≠ 0)] <;> ring

/-- The [stated conclusion](goal) follows from [the overlap fraction](hyp:ε), [the positive shift](hyp:a), [the labeled treated intensity](hyp:u), [the auxiliary treated intensity](hyp:v), [the latent mass](hyp:p), [nonnegative labeled intensity](hyp:hu), [nonnegative auxiliary intensity](hyp:hv), [positive total intensity](hyp:ht), [the supplied input hr](hyp:hr), [the centering condition](hyp:hc), [the marked component](hyp:first), [the number of independent coordinates](hyp:k), [the upper endpoint](hyp:s), [the aggregate intensity](hyp:t). -/
theorem palmSplit_aggregatePoissonLaw_real_target
    (ε a u v p : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < u + v)
    (hr : 0 ≤ ε * (p + a)) (hc : 0 ≤ controlMass ε a p)
    (first : Bool) (k s t : ℕ) :
    (palmSplitKernel
        (⟨u / (u + v), by
          constructor
          · positivity
          · rw [div_le_one ht]
            linarith⟩ : unitInterval) first ∘ₘ
      aggregatePoissonLaw ε a (u + v) p).real
        {palmSplitTarget first k s t} =
      (1 / ((k : ℝ) + 1)) *
        (poissonMeasure (Real.toNNReal (u * (ε * (p + a))))).real {k} *
        (poissonMeasure (Real.toNNReal (v * (ε * (p + a))))).real {s} *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by
  let q : unitInterval :=
    ⟨u / (u + v), by
      constructor
      · positivity
      · rw [div_le_one ht]
        linarith⟩
  let A : Set MarkedPoissonObservation := {palmSplitTarget first k s t}
  have hreal :
      (palmSplitKernel q first ∘ₘ aggregatePoissonLaw ε a (u + v) p).real A =
        ∫ z, (palmSplitMeasure q first z).real A
          ∂aggregatePoissonLaw ε a (u + v) p := by
    rw [measureReal_def, Measure.bind_apply (measurableSet_singleton _) (by fun_prop)]
    rw [← integral_toReal (by fun_prop)]
    · apply integral_congr_ae
      filter_upwards with z
      rfl
    · filter_upwards with z
      exact measure_lt_top _ _
  change (palmSplitKernel q first ∘ₘ aggregatePoissonLaw ε a (u + v) p).real A = _
  rw [hreal]
  rw [integral_countable (by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (Set.subset_univ A) (measure_ne_top _ _)).trans_eq
      (by simp))]
  simp only [smul_eq_mul]
  rw [show (fun z : AggregatePoissonObservation =>
      (aggregatePoissonLaw ε a (u + v) p).real {z} *
        (palmSplitMeasure q first z).real A) = fun z =>
      if z = (k + s, t) then
        (aggregatePoissonLaw ε a (u + v) p).real {z} *
          ((binomial (k + s) q).real {k} * (1 / ((k : ℝ) + 1)))
      else 0 by
    funext z
    dsimp [A]
    simp only [measureReal_def]
    rw [palmSplitMeasure_target_eq_ite]
    split_ifs with hz
    · rw [ENNReal.toReal_ofReal
        (mul_nonneg measureReal_nonneg (by positivity))]
      rfl
    · simp]
  rw [tsum_ite_eq (k + s, t)]
  rw [aggregatePoissonLaw, prod_real_singleton,
    aggregateTreatedRate, aggregateControlRate]
  have hcontrol : (1 - ε) * p - ε * a = controlMass ε a p := by
    simp [controlMass, treatedMass]
    ring
  rw [hcontrol]
  rw [show (u + v) * ε * (p + a) = (u + v) * (ε * (p + a)) by ring]
  dsimp [q]
  have hsplit := poisson_binomial_split u v (ε * (p + a)) hu hv hr ht k s
  calc
    _ = ((poissonMeasure
          (Real.toNNReal ((u + v) * (ε * (p + a))))).real {k + s} *
          (binomial (k + s)
            (⟨u / (u + v), by
              constructor
              · positivity
              · rw [div_le_one ht]
                linarith⟩ : unitInterval)).real {k}) *
        (1 / ((k : ℝ) + 1)) *
        (poissonMeasure
          (Real.toNNReal ((u + v) * controlMass ε a p))).real {t} := by ring
    _ = _ := by rw [hsplit]; ring


end NormalizedFiniteSignedMomentCertificate

end Causalean.Stat.Minimax.MomentMatchedMixture.FiniteSignedMomentMarkedPoissonMixture
