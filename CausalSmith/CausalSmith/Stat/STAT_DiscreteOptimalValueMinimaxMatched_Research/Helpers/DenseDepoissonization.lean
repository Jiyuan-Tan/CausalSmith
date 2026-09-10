import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseConstruction
import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.TEqualPropensityL1Reduction

/-! Exact prefix-law substrate for the dense fixed/Poisson risk transfer. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: fixedPrefixObservations
/-- The first `n` observations of a finite sample, totalized by a fallback
array when the sample contains fewer than `n` points. -/
def fixedPrefixObservations {X : Type*} [MeasurableSpace X]
    (x0 : X) (n : ℕ) (s : FiniteSample X) : Fin n → X :=
  if h : n ≤ s.count then fun k => s.points (Fin.castLE h k) else fun _ => x0

-- @node: measurable_fixedPrefixObservations
/-- The totalized fixed-prefix map is measurable. [The displayed identity or bound is the asserted conclusion](goal). -/
@[fun_prop]
lemma measurable_fixedPrefixObservations {X : Type*} [MeasurableSpace X]
    (x0 : X) (n : ℕ) :
    Measurable (fixedPrefixObservations x0 n : FiniteSample X → Fin n → X) := by
  unfold fixedPrefixObservations
  apply measurable_pi_lambda
  intro k t ht
  rw [MeasurableSpace.measurableSet_iInf]
  intro m
  change MeasurableSet ((fun x : Fin m → X =>
    (if h : n ≤ m then fun k => x (Fin.castLE h k) else fun _ => x0) k) ⁻¹' t)
  by_cases h : n ≤ m
  · simp only [dif_pos h]
    exact ht.preimage (measurable_pi_apply (Fin.castLE h k))
  · simp only [dif_neg h]
    exact measurable_const ht

-- @node: map_fixedPrefixObservations_restrict_count_ge
/-- On the event that a finite Poisson sample contains at least `n` points,
its first `n` observations have the unnormalised `n`-fold product law. This uses [the stated lam condition holds](hyp:lam). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma map_fixedPrefixObservations_restrict_count_ge
    {X : Type*} [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P]
    (lam : ℝ≥0) (x0 : X) (n : ℕ) :
    Measure.map (fixedPrefixObservations x0 n)
        ((finitePoissonSampleLaw P lam).restrict (FiniteSample.count ⁻¹' Ici n)) =
      (poissonMeasure lam) (Ici n) • Measure.pi (fun _ : Fin n => P) := by
  unfold finitePoissonSampleLaw
  rw [Measure.restrict_map measurable_streamToFiniteSample
    (measurable_finiteSample_count (measurableSet_Ici))]
  rw [Measure.map_map (measurable_fixedPrefixObservations x0 n)
    measurable_streamToFiniteSample]
  have hpre : streamToFiniteSample ⁻¹' (FiniteSample.count ⁻¹' Ici n) =
      Ici n ×ˢ (Set.univ : Set (ℕ → X)) := by
    ext z
    simp [streamToFiniteSample, FiniteSample.count]
  rw [hpre]
  unfold poissonIIDStreamLaw
  rw [← Measure.restrict_prod_eq_prod_univ]
  have hmprod : ∀ᵐ z ∂((poissonMeasure lam).restrict (Ici n)).prod (iidStreamLaw P),
      z.1 ∈ Ici n :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  have hmapcongr : fixedPrefixObservations x0 n ∘ streamToFiniteSample =ᵐ[
      ((poissonMeasure lam).restrict (Ici n)).prod (iidStreamLaw P)]
      (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i) := by
    filter_upwards [hmprod] with z hz
    change n ≤ z.1 at hz
    unfold fixedPrefixObservations streamToFiniteSample FiniteSample.count FiniteSample.points
    simp only [Function.comp_apply]
    simp [hz]
  rw [Measure.map_congr hmapcongr]
  rw [show (fun z : ℕ × (ℕ → X) => fun i : Fin n => z.2 i) =
      (fun stream : ℕ → X => fun i : Fin n => stream i) ∘ Prod.snd by rfl,
    ← Measure.map_map (by fun_prop) (by fun_prop), Measure.map_snd_prod,
    Measure.map_smul, iidStreamLaw_map_finPrefix]
  rw [Measure.restrict_apply_univ]

-- @node: densePrefixPoissonEstimator
/-- A fixed-sample estimator applied to the first `n` points of a Poisson
sample, with zero output when the Poisson sample is too short. -/
def densePrefixPoissonEstimator {n d : ℕ} (x0 : Obs d) (est : Estimator n d) :
    DensePoissonEstimator d :=
  ⟨fun s => if n ≤ s.count then est.1 (fixedPrefixObservations x0 n s)
    else 0, by
      apply Measurable.ite
      · exact measurable_finiteSample_count measurableSet_Ici
      · exact est.2.comp (measurable_fixedPrefixObservations x0 n)
      · exact measurable_const⟩

-- @node: sq_clip_unitInterval_le_denseDepoissonization
/-- Projection to the unit interval cannot increase squared distance from a
point already in that interval. This uses [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma sq_clip_unitInterval_le_denseDepoissonization (x theta : ℝ)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    (max 0 (min 1 x) - theta) ^ 2 ≤ (x - theta) ^ 2 := by
  by_cases hx0 : x ≤ 0
  · rw [min_eq_right (hx0.trans (by norm_num)), max_eq_left hx0]
    have hfac : 0 ≤ (-x) * (2 * theta - x) :=
      mul_nonneg (by linarith) (by linarith [htheta.1])
    nlinarith
  by_cases hx1 : 1 ≤ x
  · rw [min_eq_left hx1, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]
    have hfac : 0 ≤ (x - 1) * (x + 1 - 2 * theta) :=
      mul_nonneg (by linarith) (by linarith [htheta.2])
    nlinarith
  · rw [min_eq_right (le_of_not_ge hx1), max_eq_right (le_of_not_ge hx0)]

-- @node: poissonObservedRisk_densePrefix_le
/-- Applying a fixed-sample estimator to a successful Poisson prefix costs at
most its fixed-sample risk; the short-sample event costs at most its
probability. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma poissonObservedRisk_densePrefix_le {n d : ℕ} {epsilon : ℝ}
    (est : Estimator n d) (P : ModelLaw d epsilon) :
    poissonObservedRisk (2 * n)
        (densePrefixPoissonEstimator
          (⟨0, by have hd := P.2.d_ge_two; omega⟩, false, false) est) P ≤
      observedRisk n (d := d) (epsilon := epsilon) est P +
        (poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal := by
  let mu := finitePoissonSampleLaw (obsLaw P.1) (Real.toNNReal (2 * n))
  let good : Set (DensePoissonSample d) := FiniteSample.count ⁻¹' Ici n
  let theta := observedOptimalValue P.1 P.2
  let x0 : Obs d := (⟨0, by have hd := P.2.d_ge_two; omega⟩, false, false)
  have htheta : theta ∈ Set.Icc (0 : ℝ) 1 :=
    observedOptimalValue_mem_unitInterval P.1 P.2
  have hgood : MeasurableSet good :=
    measurable_finiteSample_count measurableSet_Ici
  let loss : DensePoissonSample d → ℝ := fun s =>
    (max 0 (min 1 ((densePrefixPoissonEstimator x0 est).1 s)) - theta) ^ 2
  have hloss_meas : Measurable loss := by
    dsimp [loss]
    fun_prop
  have hloss_le : ∀ s, loss s ≤ 1 := by
    intro s
    have hs : max 0 (min 1 ((densePrefixPoissonEstimator x0 est).1 s)) ∈
        Set.Icc (0 : ℝ) 1 :=
      ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    dsimp [loss]
    rw [← sq_abs]
    have habs :
        |max 0 (min 1 ((densePrefixPoissonEstimator x0 est).1 s)) - theta| ≤ 1 := by
      rw [abs_sub_le_iff]
      constructor <;> linarith [hs.1, hs.2, htheta.1, htheta.2]
    calc
      |max 0 (min 1 ((densePrefixPoissonEstimator x0 est).1 s)) - theta| ^ 2 ≤
          (1 : ℝ) ^ 2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
      _ = 1 := by norm_num
  have hloss_int : Integrable loss mu := by
    refine (integrable_const (1 : ℝ)).mono' hloss_meas.aestronglyMeasurable ?_
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hloss_le s
  have hsplit : (∫ s, loss s ∂mu) =
      ∫ s, loss s ∂mu.restrict good + ∫ s, loss s ∂mu.restrict goodᶜ := by
    rw [← integral_add_measure hloss_int.restrict hloss_int.restrict,
      Measure.restrict_add_restrict_compl hgood]
  have hgood_loss : ∀ᵐ s ∂mu.restrict good,
      loss s = (max 0 (min 1 (est.1 (fixedPrefixObservations x0 n s))) -
        theta) ^ 2 := by
    filter_upwards [ae_restrict_mem hgood] with s hs
    change n ≤ s.count at hs
    simp [loss, densePrefixPoissonEstimator, x0, hs]
  have hgood_eq : (∫ s, loss s ∂mu.restrict good) =
      (poissonMeasure (Real.toNNReal (2 * n)) (Ici n)).toReal *
        Causalean.Stat.sqRisk (productLaw P.1 n)
          (fun z => max 0 (min 1 (est.1 z))) theta := by
    rw [integral_congr_ae hgood_loss]
    let fixedLoss : (Fin n → Obs d) → ℝ := fun z =>
      (max 0 (min 1 (est.1 z)) - theta) ^ 2
    have hfixed : AEStronglyMeasurable fixedLoss
        (Measure.map (fixedPrefixObservations x0 n) (mu.restrict good)) :=
      (((measurable_const.max (measurable_const.min est.2)).sub measurable_const).pow_const 2
        ).aestronglyMeasurable
    calc
      (∫ s, (max 0 (min 1 (est.1 (fixedPrefixObservations x0 n s))) - theta) ^ 2
          ∂mu.restrict good) =
          ∫ z, fixedLoss z
            ∂Measure.map (fixedPrefixObservations x0 n) (mu.restrict good) :=
        (integral_map (measurable_fixedPrefixObservations x0 n).aemeasurable hfixed).symm
      _ = _ := by
        rw [show Measure.map (fixedPrefixObservations x0 n) (mu.restrict good) =
            (poissonMeasure (Real.toNNReal (2 * n))) (Ici n) • productLaw P.1 n by
          exact map_fixedPrefixObservations_restrict_count_ge
            (obsLaw P.1) (Real.toNNReal (2 * n)) x0 n]
        unfold Causalean.Stat.sqRisk fixedLoss
        rw [MeasureTheory.integral_smul_measure]
        simp [Measure.real, mul_comm]
  have hclip : Causalean.Stat.sqRisk (productLaw P.1 n)
      (fun z => max 0 (min 1 (est.1 z))) theta ≤
        observedRisk n (d := d) (epsilon := epsilon) est P := by
    unfold Causalean.Stat.sqRisk observedRisk
    apply integral_mono
    · refine (integrable_const (1 : ℝ)).mono'
        (((measurable_const.max (measurable_const.min est.2)).sub
          measurable_const).pow_const 2).aestronglyMeasurable ?_
      filter_upwards [] with z
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hz : max 0 (min 1 (est.1 z)) ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
      have habs : |max 0 (min 1 (est.1 z)) - theta| ≤ 1 := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hz.1, hz.2, htheta.1, htheta.2]
      rw [← sq_abs]
      calc
        |max 0 (min 1 (est.1 z)) - theta| ^ 2 ≤ (1 : ℝ) ^ 2 :=
          (sq_le_sq₀ (abs_nonneg _) (by norm_num)).2 habs
        _ = 1 := by norm_num
    · let M := ∑ z : Fin n → Obs d, |(est.1 z - theta) ^ 2|
      refine (integrable_const M).mono'
        ((est.2.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
      filter_upwards [] with z
      exact Finset.single_le_sum (fun w _hw => abs_nonneg ((est.1 w - theta) ^ 2))
        (Finset.mem_univ z)
    · intro z
      exact sq_clip_unitInterval_le_denseDepoissonization (est.1 z) theta htheta
  have hprob_good :
      (poissonMeasure (Real.toNNReal (2 * n)) (Ici n)).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    apply ENNReal.toReal_mono (by norm_num)
    calc
      poissonMeasure (Real.toNNReal (2 * n)) (Ici n) ≤
          poissonMeasure (Real.toNNReal (2 * n)) Set.univ :=
            measure_mono (Set.subset_univ (Ici n))
      _ = 1 := measure_univ
  have hrisk_nonneg : 0 ≤ Causalean.Stat.sqRisk (productLaw P.1 n)
      (fun z => max 0 (min 1 (est.1 z))) theta := by
    unfold Causalean.Stat.sqRisk
    positivity
  have hgood_le : (∫ s, loss s ∂mu.restrict good) ≤
      observedRisk n (d := d) (epsilon := epsilon) est P := by
    rw [hgood_eq]
    exact (mul_le_of_le_one_left hrisk_nonneg hprob_good).trans hclip
  have hbad_set : goodᶜ = FiniteSample.count ⁻¹' {k | k < n} := by
    ext s
    simp [good]
  have hbad_le : (∫ s, loss s ∂mu.restrict goodᶜ) ≤
      (poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal := by
    calc
      (∫ s, loss s ∂mu.restrict goodᶜ) ≤ ∫ _s, (1 : ℝ) ∂mu.restrict goodᶜ := by
        apply integral_mono hloss_int.restrict (integrable_const (1 : ℝ)) hloss_le
      _ = (mu goodᶜ).toReal := by simp [Measure.real]
      _ = _ := by
        rw [hbad_set]
        have hmap := finitePoissonSampleLaw_map_count (obsLaw P.1)
          (Real.toNNReal (2 * n))
        rw [← hmap]
        rw [Measure.map_apply measurable_finiteSample_count (by measurability)]
  have htotal : (∫ s, loss s ∂mu) ≤
      observedRisk n (d := d) (epsilon := epsilon) est P +
        (poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal := by
    rw [hsplit]
    exact add_le_add hgood_le hbad_le
  simpa [poissonObservedRisk, Causalean.Stat.sqRisk, mu, loss, x0, Nat.cast_mul] using htotal

-- @node: minimaxRisk_ge_poissonOptimalValueRisk_sub_lowerTail
/-- The first-`n` prefix construction transfers the genuine mean-`2n`
Poisson minimax lower bound to the fixed-sample experiment, losing only the
Poisson lower-tail probability. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma minimaxRisk_ge_poissonOptimalValueRisk_sub_lowerTail
    {n d : ℕ} {epsilon : ℝ} [Nonempty (ModelLaw d epsilon)] :
    poissonOptimalValueRisk (2 * n) d epsilon -
        (poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal ≤
      minimaxRisk n d epsilon := by
  let tail := (poissonMeasure (Real.toNNReal (2 * n)) {k | k < n}).toReal
  letI : Nonempty (Estimator n d) := ⟨⟨fun _ => 0, measurable_const⟩⟩
  apply Causalean.Stat.le_minimaxValue
  intro est
  let x0 : Obs d := (⟨0, by
    let P : ModelLaw d epsilon := Classical.choice inferInstance
    have hd := P.2.d_ge_two
    omega⟩, false, false)
  let pest : DensePoissonEstimator d := densePrefixPoissonEstimator x0 est
  have hpois_nonneg : ∀ e : DensePoissonEstimator d, ∀ P : ModelLaw d epsilon,
      0 ≤ poissonObservedRisk (2 * n) e P := by
    intro e P
    unfold poissonObservedRisk Causalean.Stat.sqRisk
    positivity
  have hupper : poissonOptimalValueRisk (2 * n) d epsilon ≤
      Causalean.Stat.worstCaseRisk
        (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) pest :=
    Causalean.Stat.minimaxValue_le_worstCaseRisk_of_nonneg hpois_nonneg pest
  have hworst : Causalean.Stat.worstCaseRisk
        (poissonObservedRisk (2 * n) (d := d) (epsilon := epsilon)) pest ≤
      Causalean.Stat.worstCaseRisk
          (observedRisk n (d := d) (epsilon := epsilon)) est + tail := by
    apply Causalean.Stat.worstCaseRisk_le
    intro P
    have hp := poissonObservedRisk_densePrefix_le est P
    have hx0 : x0 = (⟨0, by have hd := P.2.d_ge_two; omega⟩, false, false) := by
      ext <;> simp [x0]
    rw [show pest = densePrefixPoissonEstimator
        (⟨0, by have hd := P.2.d_ge_two; omega⟩, false, false) est by
      simp [pest, hx0]]
    exact hp.trans (add_le_add
      (Causalean.Stat.le_worstCaseRisk (observedRisk_bddAbove est) P) le_rfl)
  change poissonOptimalValueRisk (2 * n) d epsilon - tail ≤ _
  linarith

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
