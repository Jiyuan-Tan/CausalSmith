import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.PilotControlTheorem
import Causalean.Stat.Minimax.MarkovKernelTransport

/-! The marked finite-Poisson statistic and its capped fixed-sample Rao--Blackwell coupling. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open scoped BigOperators

-- @node: jacksonUncappedStatistic
/-- The projected Jackson cell sum on an uncapped marked finite sample. -/
noncomputable def jacksonUncappedStatistic {d : ℕ} (tuning : JacksonTuning)
    (epsilon : ℝ) (n : ℕ) (hn : 0 < n) (s : FiniteSample (Obs d × Bool)) : ℝ :=
  let m : ℝ := n / 8
  let hm : 0 < m := by positivity
  let table := (uncappedMarkedCountMap s).2
  max 0 (min 1 (∑ x : Fin d,
    jacksonCellStatistic tuning epsilon d m (table.1 x) (table.2 x) hm))

-- @node: measurable_jacksonUncappedStatistic
/-- The uncapped projected statistic is measurable. This uses [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
@[fun_prop] lemma measurable_jacksonUncappedStatistic {d : ℕ}
    (tuning : JacksonTuning) (epsilon : ℝ) (n : ℕ) (hn : 0 < n) :
    Measurable (jacksonUncappedStatistic (d := d) tuning epsilon n hn) := by
  apply Measurable.max measurable_const
  apply Measurable.min measurable_const
  apply Finset.measurable_sum
  intro x _hx
  exact (Measurable.of_discrete : Measurable
    (fun table : UncappedCountTable d =>
      jacksonCellStatistic tuning epsilon d (n / 8) (table.1 x) (table.2 x)
        (by positivity))).comp measurable_uncappedMarkedCountMap.snd

-- @node: jacksonUncappedStatistic_mem_unitInterval
/-- Projection places the uncapped statistic in the unit interval. This uses [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonUncappedStatistic_mem_unitInterval {d : ℕ} (tuning : JacksonTuning)
    (epsilon : ℝ) (n : ℕ) (hn : 0 < n) (s : FiniteSample (Obs d × Bool)) :
    jacksonUncappedStatistic tuning epsilon n hn s ∈ Set.Icc (0 : ℝ) 1 := by
  unfold jacksonUncappedStatistic
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

-- @node: sum_fin_prefix_indicator
/-- Extending a prefix indicator by zero preserves its finite sum. This uses [the stated m condition holds](hyp:hM). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma sum_fin_prefix_indicator {n M : ℕ} (hM : M ≤ n) (p : Fin n → Prop)
    [DecidablePred p] :
    (∑ i : Fin M, if p (Fin.castLE hM i) then 1 else 0) =
      ∑ i : Fin n, if i.1 < M ∧ p i then 1 else 0 := by
  rw [← Finset.card_filter, ← Finset.card_filter]
  apply Finset.card_bij (fun i _hi => Fin.castLE hM i)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨i.2, hi⟩
  · intro i _hi j _hj hij
    exact Fin.castLE_injective hM hij
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    refine ⟨⟨j.1, hj.1⟩, ?_, ?_⟩
    · simpa using hj.2
    · apply Fin.ext
      rfl

-- @node: uncappedMarkedCountMap_prefix_table
/-- The uncapped count table of a fixed-array prefix is exactly the table used
by the randomized estimator. This uses [the stated m condition holds](hyp:hM). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma uncappedMarkedCountMap_prefix_table {n d : ℕ}
    (sample : Fin n → Obs d) (marks : Fin n → Bool) (M : ℕ) (hM : M ≤ n) :
    (uncappedMarkedCountMap
      (prefixOfLE (fun i => (sample i, marks i)) M hM)).2 =
      ((fun x j => markedCellCount sample M marks false x j),
        fun x j => markedCellCount sample M marks true x j) := by
  classical
  apply Prod.ext <;> funext x j
  · let p : Fin n → Prop := fun i => marks i = false ∧ (sample i).1 = x ∧
        (sample i).2.1 = finTwoEquiv j.1 ∧ (sample i).2.2 = finTwoEquiv j.2
    change (∑ i : Fin M, if p (Fin.castLE hM i) then 1 else 0) =
      ∑ i : Fin n, if i.1 < M ∧ p i then 1 else 0
    exact sum_fin_prefix_indicator hM p
  · let p : Fin n → Prop := fun i => marks i = true ∧ (sample i).1 = x ∧
        (sample i).2.1 = finTwoEquiv j.1 ∧ (sample i).2.2 = finTwoEquiv j.2
    change (∑ i : Fin M, if p (Fin.castLE hM i) then 1 else 0) =
      ∑ i : Fin n, if i.1 < M ∧ p i then 1 else 0
    exact sum_fin_prefix_indicator hM p

-- @node: jacksonUncappedStatistic_prefix
/-- On nonoverflow, the generic prefix statistic is the paper's randomized statistic. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the stated m condition holds](hyp:hM). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonUncappedStatistic_prefix {n d : ℕ} (tuning : JacksonTuning)
    (epsilon : ℝ) (hn : 0 < n) (sample : Fin n → Obs d)
    (marks : Fin n → Bool) (M : ℕ) (hM : M ≤ n) :
    jacksonUncappedStatistic tuning epsilon n hn
        (prefixOfLE (fun i => (sample i, marks i)) M hM) =
      jacksonRandomizedStatistic tuning epsilon sample M marks := by
  rw [jacksonRandomizedStatistic, dif_pos hn, if_pos hM]
  unfold jacksonUncappedStatistic
  rw [uncappedMarkedCountMap_prefix_table sample marks M hM]

-- @node: raoBlackwell_jacksonUncappedStatistic_apply
/-- The inner Poisson average in the estimator is the generic capped
Rao--Blackwell statistic associated with the uncapped marked statistic. This uses [the sample size satisfies its stated restriction](hyp:hn). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma raoBlackwell_jacksonUncappedStatistic_apply {n d : ℕ}
    (tuning : JacksonTuning) (epsilon : ℝ) (hn : 0 < n)
    (sample : Fin n → Obs d) (marks : Fin n → Bool) :
    Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
        (jacksonUncappedStatistic tuning epsilon n hn) 0
        (fun i => (sample i, marks i)) =
      ∫ M : ℕ, jacksonRandomizedStatistic tuning epsilon sample M marks
        ∂ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4)) := by
  rw [Causalean.Stat.raoBlackwellStatistic_eq_integral _ _
    (measurable_jacksonUncappedStatistic tuning epsilon n hn)]
  apply integral_congr_ae
  filter_upwards with M
  unfold Causalean.Stat.cappedStatistic
  split_ifs with hM
  · exact jacksonUncappedStatistic_prefix tuning epsilon hn sample marks M hM
  · simp [jacksonRandomizedStatistic, hn, hM]

-- @node: jacksonRandomizedStatistic_mem_unitInterval
/-- The capped randomized statistic always belongs to the unit interval. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonRandomizedStatistic_mem_unitInterval {n d : ℕ}
    (tuning : JacksonTuning) (epsilon : ℝ) (sample : Fin n → Obs d)
    (M : ℕ) (marks : Fin n → Bool) :
    jacksonRandomizedStatistic tuning epsilon sample M marks ∈ Set.Icc (0 : ℝ) 1 := by
  unfold jacksonRandomizedStatistic
  split_ifs
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  all_goals simp

-- @node: jacksonFactorialEstimator_eq_marked_raoBlackwell
/-- In its Jackson regime, the explicit estimator is the fair-mark average of
the generic capped Rao--Blackwell statistic. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the alphabet exceeds the bounded-alphabet cutoff](hyp:hcutoff), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma jacksonFactorialEstimator_eq_marked_raoBlackwell {n d : ℕ}
    (tuning : JacksonTuning) (epsilon : ℝ) (hn : 0 < n)
    (hcutoff : ¬ d < tuning.boundedAlphabetCutoff)
    (hscale : ¬ (n : ℝ) < d / logAlphabet d) (sample : Fin n → Obs d) :
    jacksonFactorialEstimator tuning epsilon sample =
      ∫ marks : Fin n → Bool,
        Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
          (jacksonUncappedStatistic tuning epsilon n hn) 0
          (fun i => (sample i, marks i)) ∂fairMarkLaw n := by
  rw [jacksonFactorialEstimator, if_neg hcutoff, if_neg hscale]
  letI : IsProbabilityMeasure (fairMarkLaw n) := by
    unfold fairMarkLaw
    infer_instance
  have hInt : Integrable
      (fun z : ℕ × (Fin n → Bool) =>
        jacksonRandomizedStatistic tuning epsilon sample z.1 z.2)
      ((ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4))).prod
        (fairMarkLaw n)) :=
    (integrable_const (1 : ℝ)).mono'
      (Measurable.of_discrete.aestronglyMeasurable) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg
          (jacksonRandomizedStatistic_mem_unitInterval tuning epsilon sample z.1 z.2).1]
        exact (jacksonRandomizedStatistic_mem_unitInterval
          tuning epsilon sample z.1 z.2).2)
  rw [integral_integral_swap hInt]
  apply integral_congr_ae
  filter_upwards with marks
  rw [raoBlackwell_jacksonUncappedStatistic_apply tuning epsilon hn sample marks]

-- @node: sqRisk_marked_raoBlackwell_jackson_le
/-- The fixed marked-sample risk is bounded by the uncapped finite-Poisson
risk plus the exact overflow probability. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the target or contrast satisfies the stated unit-range restriction](hyp:htheta). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma sqRisk_marked_raoBlackwell_jackson_le {n d : ℕ} (P : DiscreteLaw d)
    (tuning : JacksonTuning) (epsilon theta : ℝ) (hn : 0 < n)
    (htheta : theta ∈ Set.Icc (0 : ℝ) 1) :
    Causalean.Stat.sqRisk
        (Measure.pi (fun _ : Fin n => (obsLaw P).prod uncappedFairMarkLaw))
        (Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
          (jacksonUncappedStatistic tuning epsilon n hn) 0) theta ≤
      Causalean.Stat.sqRisk
          (finitePoissonSampleLaw ((obsLaw P).prod uncappedFairMarkLaw)
            (Real.toNNReal (n / 4)))
          (jacksonUncappedStatistic tuning epsilon n hn) theta +
        (ProbabilityTheory.poissonMeasure (Real.toNNReal (n / 4))).real
          (Set.Ioi n) := by
  exact Causalean.Stat.sqRisk_raoBlackwellStatistic_unitInterval_le
    ((obsLaw P).prod uncappedFairMarkLaw) (Real.toNNReal (n / 4)) n
    (measurable_jacksonUncappedStatistic tuning epsilon n hn)
    (jacksonUncappedStatistic_mem_unitInterval tuning epsilon n hn)
    htheta (by simp)

-- @node: fairMarkLaw_eq_pi_uncappedFairMarkLaw
/-- The explicit uniform law on all mark arrays is the independent product of
the one-coordinate fair mark laws. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma fairMarkLaw_eq_pi_uncappedFairMarkLaw (n : ℕ) :
    fairMarkLaw n = Measure.pi (fun _ : Fin n => uncappedFairMarkLaw) := by
  apply Measure.ext_of_singleton
  intro marks
  simp [fairMarkLaw, uncappedFairMarkLaw]
  exact ENNReal.inv_pow

-- @node: fairObservationMarkKernel
/-- Adjoin one independent fair Boolean mark to an observation. -/
noncomputable def fairObservationMarkKernel {d : ℕ} :
    Kernel (Obs d) (Obs d × Bool) :=
  Causalean.Mathlib.GraphMapProd.mechanismKernel uncappedFairMarkLaw id

-- @node: fairObservationMarkKernel.isMarkovKernel
/-- [The fair observation-marking kernel preserves total probability one](goal). -/
instance fairObservationMarkKernel.isMarkovKernel {d : ℕ} :
    IsMarkovKernel (fairObservationMarkKernel (d := d)) := by
  unfold fairObservationMarkKernel
  exact Causalean.Mathlib.GraphMapProd.instIsMarkovKernelMechanismKernel _ measurable_id

-- @node: fairObservationMarkKernel_apply
/-- Pointwise, adjoining a fair mark is the pushforward of the fair law by pairing. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma fairObservationMarkKernel_apply {d : ℕ} (o : Obs d) :
    fairObservationMarkKernel o =
      Measure.map (fun b => (o, b)) uncappedFairMarkLaw := by
  unfold fairObservationMarkKernel
  rw [Causalean.Mathlib.GraphMapProd.mechanismKernel_apply _ measurable_id]
  rfl

-- @node: finProductFairObservationMarkKernel_apply
/-- Conditional on an observation array, the coordinatewise marking kernel is
the pushforward of the explicit fair array law. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma finProductFairObservationMarkKernel_apply {n d : ℕ}
    (sample : Fin n → Obs d) :
    Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d)) sample =
      Measure.map (fun marks : Fin n → Bool => fun i => (sample i, marks i))
        (fairMarkLaw n) := by
  rw [Causalean.Stat.finProductKernel_apply]
  simp_rw [fairObservationMarkKernel_apply]
  calc
    Measure.pi (fun i : Fin n =>
        Measure.map (fun b => (sample i, b)) uncappedFairMarkLaw) =
        Measure.map (fun marks : Fin n → Bool => fun i => (sample i, marks i))
          (Measure.pi (fun _ : Fin n => uncappedFairMarkLaw)) := by
      symm
      exact Measure.pi_map_pi (fun _ => Measurable.of_discrete.aemeasurable)
    _ = _ := by rw [← fairMarkLaw_eq_pi_uncappedFairMarkLaw]

-- @node: kernelMean_finProductFairObservationMarkKernel
/-- Averaging a statistic through the coordinatewise marking kernel is exactly
integration over the paper's fair mark array. This uses [the stated t condition holds](hyp:hT). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma kernelMean_finProductFairObservationMarkKernel {n d : ℕ}
    (T : (Fin n → Obs d × Bool) → ℝ) (hT : Measurable T)
    (sample : Fin n → Obs d) :
    Causalean.Stat.kernelMean
        (Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d))) T sample =
      ∫ marks : Fin n → Bool, T (fun i => (sample i, marks i)) ∂fairMarkLaw n := by
  unfold Causalean.Stat.kernelMean
  rw [finProductFairObservationMarkKernel_apply sample]
  exact integral_map Measurable.of_discrete.aemeasurable hT.aestronglyMeasurable

-- @node: fairObservationMarkKernel_comp_obsLaw
/-- Marking a single observation produces its product with the fair mark law. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma fairObservationMarkKernel_comp_obsLaw {d : ℕ} (P : DiscreteLaw d) :
    fairObservationMarkKernel (d := d) ∘ₘ obsLaw P =
      (obsLaw P).prod uncappedFairMarkLaw := by
  have hgraph :
      Measure.map (fun p : Obs d × Bool => (p.1, p))
          ((obsLaw P).prod uncappedFairMarkLaw) =
        (obsLaw P).compProd (fairObservationMarkKernel (d := d)) := by
    simpa [fairObservationMarkKernel] using
      (Causalean.Mathlib.GraphMapProd.map_graph_prod_eq_compProd
        (obsLaw P) uncappedFairMarkLaw
        (show Measurable (id : Obs d × Bool → Obs d × Bool) from measurable_id))
  have hsnd := congrArg (Measure.map Prod.snd) hgraph
  rw [Measure.map_map measurable_snd
      (show Measurable (fun p : Obs d × Bool => (p.1, p)) from
        measurable_fst.prodMk measurable_id)] at hsnd
  change _ = ((obsLaw P) ⊗ₘ fairObservationMarkKernel (d := d)).snd at hsnd
  rw [Measure.snd_compProd] at hsnd
  simpa [Function.comp_def] using hsnd.symm

-- @node: finProductFairObservationMarkKernel_comp_productLaw
/-- Coordinatewise fair marking of an iid observation array gives the iid law
of independently marked observations. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma finProductFairObservationMarkKernel_comp_productLaw {n d : ℕ}
    (P : DiscreteLaw d) :
    Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d)) ∘ₘ
        productLaw P n =
      Measure.pi (fun _ : Fin n => (obsLaw P).prod uncappedFairMarkLaw) := by
  unfold productLaw
  rw [Causalean.Stat.finProductKernel_comp_pi]
  congr 1
  funext i
  exact fairObservationMarkKernel_comp_obsLaw P

-- @node: sqRisk_jacksonFactorialEstimator_le_marked
/-- In the Jackson regime, outer Rao--Blackwellization over the fair marks
cannot increase risk relative to the marked fixed-array statistic. This uses [the sample size satisfies its stated restriction](hyp:hn), and [the alphabet exceeds the bounded-alphabet cutoff](hyp:hcutoff), and [the stated scale inequality holds](hyp:hscale). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma sqRisk_jacksonFactorialEstimator_le_marked {n d : ℕ} (P : DiscreteLaw d)
    (tuning : JacksonTuning) (epsilon theta : ℝ) (hn : 0 < n)
    (hcutoff : ¬ d < tuning.boundedAlphabetCutoff)
    (hscale : ¬ (n : ℝ) < d / logAlphabet d) :
    Causalean.Stat.sqRisk (productLaw P n)
        (jacksonFactorialEstimator tuning epsilon) theta ≤
      Causalean.Stat.sqRisk
        (Measure.pi (fun _ : Fin n => (obsLaw P).prod uncappedFairMarkLaw))
        (Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
          (jacksonUncappedStatistic tuning epsilon n hn) 0) theta := by
  let T : (Fin n → Obs d × Bool) → ℝ :=
    Causalean.Stat.raoBlackwellStatistic (Real.toNNReal (n / 4))
      (jacksonUncappedStatistic tuning epsilon n hn) 0
  have hbaseBound : Causalean.Stat.UniformlyBounded
      (fun z : (Fin n → Obs d × Bool) × ℕ =>
        Causalean.Stat.cappedStatistic
          (jacksonUncappedStatistic tuning epsilon n hn) 0 z.1 z.2) := by
    refine ⟨1, by norm_num, ?_⟩
    intro z
    change |if h : z.2 ≤ n then
        jacksonUncappedStatistic tuning epsilon n hn
          (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.prefixOfLE
            z.1 z.2 h) else 0| ≤ 1
    split_ifs with h
    · have hz := jacksonUncappedStatistic_mem_unitInterval
          tuning epsilon n hn
            (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.prefixOfLE
              z.1 z.2 h)
      rw [abs_of_nonneg hz.1]
      exact hz.2
    · simp
  have hTmeas : Measurable T := by
    dsimp [T, Causalean.Stat.raoBlackwellStatistic]
    exact Causalean.Stat.measurable_kernelMean _
      (Causalean.Stat.measurable_cappedStatistic
        (measurable_jacksonUncappedStatistic tuning epsilon n hn) 0)
  have hTbound : Causalean.Stat.UniformlyBounded T := by
    dsimp [T, Causalean.Stat.raoBlackwellStatistic]
    exact Causalean.Stat.uniformlyBounded_kernelMean _ hbaseBound
  have hmean : Causalean.Stat.kernelMean
      (Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d))) T =
      jacksonFactorialEstimator tuning epsilon := by
    funext sample
    rw [kernelMean_finProductFairObservationMarkKernel T hTmeas sample]
    exact (jacksonFactorialEstimator_eq_marked_raoBlackwell
      tuning epsilon hn hcutoff hscale sample).symm
  calc
    Causalean.Stat.sqRisk (productLaw P n)
        (jacksonFactorialEstimator tuning epsilon) theta =
        Causalean.Stat.sqRisk (productLaw P n)
          (Causalean.Stat.kernelMean
            (Causalean.Stat.finProductKernel n
              (fairObservationMarkKernel (d := d))) T) theta := by rw [hmean]
    _ ≤ Causalean.Stat.sqRisk
        (Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d)) ∘ₘ
          productLaw P n) T theta :=
      Causalean.Stat.sqRisk_kernelMean_le_comp (productLaw P n)
        (Causalean.Stat.finProductKernel n (fairObservationMarkKernel (d := d)))
        hTmeas hTbound theta
    _ = _ := by rw [finProductFairObservationMarkKernel_comp_productLaw]

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
