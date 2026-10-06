module
public import Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition.StreamLaw

/-!
# Squared-risk transfer for a capped labeled Poisson experiment

Conditional averaging over a Poisson count and finite labels contracts squared
loss. The cap contributes at most interval diameter squared times the scalar
Poisson upper-tail probability.
-/

public section

open MeasureTheory ProbabilityTheory Causalean.Stat
open scoped ENNReal NNReal BigOperators

namespace Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition
open Causalean.Mathlib.GraphMapProd

variable {X I : Type*} [MeasurableSpace X] [MeasurableSpace I]
  [Fintype I] [MeasurableSingletonClass I]

/-- Given [an iid observation law](hyp:P), [finite label masses](hyp:p,hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable interval-bounded
stream statistic](hyp:hT,hTmem), [an interval-bounded overflow value](hyp:hzOver),
and [a target](hyp:theta), the capped squared risk is the sum of its
[nonoverflow and overflow restrictions](goal). -/
theorem sqRisk_capped_split
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    {a b zOver : ℝ} (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (hzOver : zOver ∈ Set.Icc a b) (theta : ℝ) :
    sqRisk ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n))
        (fun z => cappedStatistic z.1 T zOver z.2) theta =
      sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 ≤ n})
        (fun z => cappedStatistic z.1 T zOver z.2) theta +
      sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | n < z.2.1})
        (fun z => cappedStatistic z.1 T zOver z.2) theta := by
  letI : IsProbabilityMeasure (auxiliaryLaw p hp lambda n) := by
    unfold auxiliaryLaw
    letI := labelLaw_isProbabilityMeasure p hp
    infer_instance
  letI : IsProbabilityMeasure (fixedPoolLaw P n) := by
    unfold fixedPoolLaw
    infer_instance
  let μ : Measure ((Fin n → X) × (ℕ × (Fin n → I))) :=
    (fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hMeas : Measurable
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        cappedStatistic z.1 T zOver z.2) := by
    let g : ℕ × ((Fin n → X) × (Fin n → I)) → ℝ :=
      fun z => cappedStatistic z.2.1 T zOver (z.1, z.2.2)
    have hg : Measurable g := by
      apply measurable_from_prod_countable_right
      intro m
      by_cases hm : m ≤ n
      · have hprefix : Measurable
            (fun z : (Fin n → X) × (Fin n → I) =>
              labeledPrefix z.1 m hm
                (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩)) := by
          exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
            (measurable_pi_lambda _ fun k =>
              ((measurable_pi_apply _).comp measurable_fst).prodMk
                ((measurable_pi_apply _).comp measurable_snd)))
        have heq : (fun y : (Fin n → X) × (Fin n → I) => g (m, y)) =
            (fun y => T (labeledPrefix y.1 m hm
              (fun k => y.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩))) := by
          funext y
          simp [g, cappedStatistic, hm]
        rw [heq]
        exact hT.comp hprefix
      · simpa [g, cappedStatistic, hm] using
          (measurable_const : Measurable
            (fun _ : (Fin n → X) × (Fin n → I) => zOver))
    exact hg.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hBound : UniformlyBounded
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        cappedStatistic z.1 T zOver z.2) := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro z
    by_cases hm : z.2.1 ≤ n
    · simp only [cappedStatistic, dif_pos hm]
      exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
    · simp only [cappedStatistic, dif_neg hm]
      exact abs_le_max_abs_abs hzOver.1 hzOver.2
  obtain ⟨M, hM, hTb⟩ := hBound
  let s : Set ((Fin n → X) × (ℕ × (Fin n → I))) := {z | z.2.1 ≤ n}
  have hs : MeasurableSet s :=
    (measurable_fst.comp measurable_snd) measurableSet_Iic
  have hlossInt : Integrable
      (fun z => (cappedStatistic z.1 T zOver z.2 - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hMeas.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable
      (fun z => (cappedStatistic z.1 T zOver z.2 - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable
      (fun z => (cappedStatistic z.1 T zOver z.2 - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  have hscompl : sᶜ = {z | n < z.2.1} := by
    ext z
    simp [s, not_le]
  unfold sqRisk
  rw [← hscompl]
  change (∫ z, (cappedStatistic z.1 T zOver z.2 - theta) ^ 2 ∂μ) =
    (∫ z, (cappedStatistic z.1 T zOver z.2 - theta) ^ 2 ∂μ.restrict s) +
    (∫ z, (cappedStatistic z.1 T zOver z.2 - theta) ^ 2 ∂μ.restrict sᶜ)
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable stream statistic](hyp:hT)
[confined to an interval](hyp:hTmem), and [an overflow value in that interval](hyp:hzOver),
[conditional averaging does not increase squared risk](goal). -/
theorem fixedRisk_le_cappedRisk
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    {a b zOver : ℝ} (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (hzOver : zOver ∈ Set.Icc a b) (theta : ℝ) :
    sqRisk (fixedPoolLaw P n)
        (fun x => fixedStatistic p hp lambda x T zOver) theta ≤
      sqRisk ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n))
        (fun z => cappedStatistic z.1 T zOver z.2) theta := by
  letI : IsProbabilityMeasure (auxiliaryLaw p hp lambda n) := by
    unfold auxiliaryLaw
    letI := labelLaw_isProbabilityMeasure p hp
    infer_instance
  letI : IsProbabilityMeasure (fixedPoolLaw P n) := by
    unfold fixedPoolLaw
    infer_instance
  let K : Kernel (Fin n → X) ((Fin n → X) × (ℕ × (Fin n → I))) :=
    mechanismKernel (auxiliaryLaw p hp lambda n) id
  have hK : IsMarkovKernel K := by
    dsimp [K]
    exact instIsMarkovKernelMechanismKernel _ measurable_id
  letI := hK
  have hMeas : Measurable
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        cappedStatistic z.1 T zOver z.2) := by
    let g : ℕ × ((Fin n → X) × (Fin n → I)) → ℝ :=
      fun z => cappedStatistic z.2.1 T zOver (z.1, z.2.2)
    have hg : Measurable g := by
      apply measurable_from_prod_countable_right
      intro m
      by_cases hm : m ≤ n
      · have hprefix : Measurable
            (fun z : (Fin n → X) × (Fin n → I) =>
              labeledPrefix z.1 m hm
                (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩)) := by
          exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
            (measurable_pi_lambda _ fun k =>
              ((measurable_pi_apply _).comp measurable_fst).prodMk
                ((measurable_pi_apply _).comp measurable_snd)))
        have heq : (fun y : (Fin n → X) × (Fin n → I) => g (m, y)) =
            (fun y => T (labeledPrefix y.1 m hm
              (fun k => y.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩))) := by
          funext y
          simp [g, cappedStatistic, hm]
        rw [heq]
        exact hT.comp hprefix
      · simpa [g, cappedStatistic, hm] using
          (measurable_const : Measurable
            (fun _ : (Fin n → X) × (Fin n → I) => zOver))
    exact hg.comp ((measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hBound : UniformlyBounded
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        cappedStatistic z.1 T zOver z.2) := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro z
    by_cases hm : z.2.1 ≤ n
    · simp only [cappedStatistic, dif_pos hm]
      exact abs_le_max_abs_abs (hTmem _).1 (hTmem _).2
    · simp only [cappedStatistic, dif_neg hm]
      exact abs_le_max_abs_abs hzOver.1 hzOver.2
  have hmean : kernelMean K
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) =>
        cappedStatistic z.1 T zOver z.2) =
      (fun x => fixedStatistic p hp lambda x T zOver) := by
    funext x
    unfold kernelMean K fixedStatistic
    rw [mechanismKernel_apply _ measurable_id x]
    exact integral_map measurable_prodMk_left.aemeasurable hMeas.aestronglyMeasurable
  have hcomp : K ∘ₘ fixedPoolLaw P n =
      (fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n) := by
    have hgraph := map_graph_prod_eq_compProd
      (fixedPoolLaw P n) (auxiliaryLaw p hp lambda n)
      (show Measurable
        (fun z : (Fin n → X) × (ℕ × (Fin n → I)) => z) from measurable_id)
    have hsnd := congrArg (Measure.map Prod.snd) hgraph
    rw [Measure.map_map measurable_snd
      (show Measurable
        (fun z : (Fin n → X) × (ℕ × (Fin n → I)) => (z.1, z)) from
          measurable_fst.prodMk measurable_id)] at hsnd
    change _ = ((fixedPoolLaw P n) ⊗ₘ K).snd at hsnd
    rw [Measure.snd_compProd] at hsnd
    simpa [Function.comp_def, K] using hsnd.symm
  rw [← hmean, ← hcomp]
  exact sqRisk_kernelMean_le_comp (fixedPoolLaw P n) K hMeas hBound theta

/-! ## Restricted-risk bridges -/

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable stream statistic](hyp:hT),
[an overflow value](hyp:zOver), and [a target](hyp:theta), [the capped squared risk on
nonoverflow equals the uncapped stream risk restricted to total count at most the pool
size](goal). -/
theorem sqRisk_capped_restrict_nonoverflow_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    (zOver theta : ℝ) :
    sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 ≤ n})
        (fun z => cappedStatistic z.1 T zOver z.2) theta =
      sqRisk ((labeledStreamLaw P p hp lambda).restrict
        {s | ∑ i, (s i).count ≤ n}) T theta := by
  let f : (Fin n → X) × (ℕ × (Fin n → I)) → I → FiniteSample X := fun z =>
    if h : z.2.1 ≤ n then
      labeledPrefix z.1 z.2.1 h
        (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
    else fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X)
  have hf : Measurable f := by
    let g : ℕ × ((Fin n → X) × (Fin n → I)) → I → FiniteSample X := fun z =>
      if h : z.1 ≤ n then
        labeledPrefix z.2.1 z.1 h
          (fun k => z.2.2 ⟨k.val, lt_of_lt_of_le k.isLt h⟩)
      else fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X)
    have hg : Measurable g := by
      apply measurable_from_prod_countable_right
      intro m
      by_cases hm : m ≤ n
      · have hprefix : Measurable (fun z : (Fin n → X) × (Fin n → I) =>
            labeledPrefix z.1 m hm
              (fun k => z.2 ⟨k.val, lt_of_lt_of_le k.isLt hm⟩)) := by
          exact measurable_unshuffle.comp (measurable_fixedSizeEmbed m |>.comp
            (measurable_pi_lambda _ fun k =>
              ((measurable_pi_apply _).comp measurable_fst).prodMk
                ((measurable_pi_apply _).comp measurable_snd)))
        simpa only [g, hm, dite_true] using hprefix
      · simpa only [g, hm, dite_false] using
          (measurable_const : Measurable (fun _ : (Fin n → X) × (Fin n → I) =>
            (fun _ => (⟨0, Fin.elim0⟩ : FiniteSample X))))
    exact hg.comp (by fun_prop : Measurable
      (fun z : (Fin n → X) × (ℕ × (Fin n → I)) => (z.2.1, (z.1, z.2.2))))
  unfold sqRisk
  rw [← map_capped_restrict_nonoverflow P p hp lambda n]
  rw [integral_map (μ := ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
      {z | z.2.1 ≤ n}) (φ := f) (f := fun s => (T s - theta) ^ 2)
      hf.aemeasurable ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem
    ((measurable_fst.comp measurable_snd) measurableSet_Iic)] with z hz
  simp [f, cappedStatistic, hz]

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a stream statistic](hyp:T),
[an overflow value](hyp:zOver), and [a target](hyp:theta), [the capped squared risk on
overflow equals the constant overflow loss times the Poisson upper tail](goal). -/
theorem sqRisk_capped_restrict_overflow_eq
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    (T : (I → FiniteSample X) → ℝ) (zOver theta : ℝ) :
    sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | n < z.2.1})
        (fun z => cappedStatistic z.1 T zOver z.2) theta =
      (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- The integrand is constant on overflow. The event depends only on the
  -- Poisson count, so its product-law mass is the scalar upper tail.
  letI := labelLaw_isProbabilityMeasure p hp
  haveI : IsProbabilityMeasure (fixedPoolLaw P n) := by
    unfold fixedPoolLaw
    infer_instance
  unfold sqRisk
  have hae : ∀ᵐ z ∂
      ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | n < z.2.1},
      (cappedStatistic z.1 T zOver z.2 - theta) ^ 2 =
        (zOver - theta) ^ 2 := by
    have hs : MeasurableSet
        {z : (Fin n → X) × (ℕ × (Fin n → I)) | n < z.2.1} :=
      (measurable_fst.comp measurable_snd) measurableSet_Ioi
    filter_upwards [ae_restrict_mem hs] with z hz
    simp [cappedStatistic, not_le_of_gt hz]
  rw [integral_congr_ae hae, integral_const]
  simp only [smul_eq_mul, measureReal_def]
  have hset : {z : (Fin n → X) × (ℕ × (Fin n → I)) | n < z.2.1} =
      (Set.univ : Set (Fin n → X)) ×ˢ
        (Set.Ioi n ×ˢ (Set.univ : Set (Fin n → I))) := by
    ext z
    simp
  have haux : (auxiliaryLaw p hp lambda n)
      (Set.Ioi n ×ˢ (Set.univ : Set (Fin n → I))) =
        (poissonMeasure lambda) (Set.Ioi n) := by
    unfold auxiliaryLaw
    rw [Measure.prod_prod]
    simp
  rw [Measure.restrict_apply_univ, hset, Measure.prod_prod]
  simp [haux, mul_comm]

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable uniformly bounded
stream statistic](hyp:hT,hTb), and [a target](hyp:theta), [restricting the uncapped
stream law to total counts at most the pool size cannot increase squared risk](goal). -/
theorem sqRisk_labeledStreamLaw_restrict_nonoverflow_le
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (theta : ℝ) :
    sqRisk ((labeledStreamLaw P p hp lambda).restrict
        {s | ∑ i, (s i).count ≤ n}) T theta ≤
      sqRisk (labeledStreamLaw P p hp lambda) T theta := by
  -- Show bounded-loss integrability; split the measure into the measurable
  -- nonoverflow event and its complement, then discard nonnegative loss.
  obtain ⟨M, hM, hTb⟩ := hTb
  let μ : Measure (I → FiniteSample X) := labeledStreamLaw P p hp lambda
  letI := labelLaw_isProbabilityMeasure p hp
  haveI : IsProbabilityMeasure μ := by
    unfold μ labeledStreamLaw
    exact Measure.isProbabilityMeasure_map measurable_unshuffle.aemeasurable
  let s : Set (I → FiniteSample X) := {z | ∑ i, (z i).count ≤ n}
  have hs : MeasurableSet s := by
    have hc : Measurable (fun z : I → FiniteSample X => ∑ i, (z i).count) := by
      fun_prop
    exact hc measurableSet_Iic
  have hlossInt : Integrable (fun z => (T z - theta) ^ 2) μ := by
    refine (integrable_const ((M + |theta|) ^ 2)).mono'
      ((hT.sub measurable_const).pow_const 2).aestronglyMeasurable ?_
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_sq,
      abs_of_nonneg (add_nonneg hM (abs_nonneg theta))]
    exact (abs_sub _ _).trans (add_le_add (hTb z) le_rfl)
  have hsInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict s) :=
    hlossInt.restrict
  have hscInt : Integrable (fun z => (T z - theta) ^ 2) (μ.restrict sᶜ) :=
    hlossInt.restrict
  unfold sqRisk
  change (∫ z, (T z - theta) ^ 2 ∂μ.restrict s) ≤
    ∫ z, (T z - theta) ^ 2 ∂μ
  conv_rhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hs,
    integral_add_measure hsInt hscInt]
  exact le_add_of_nonneg_right
    (integral_nonneg fun z => sq_nonneg (T z - theta))

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable stream statistic](hyp:hT),
[a uniform bound](hyp:hTb), [an overflow value](hyp:zOver), and [a target](hyp:theta),
[the nonoverflow capped risk is at most independent-stream risk](goal). -/
theorem sqRisk_capped_restrict_nonoverflow_le_independent
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    (hTb : UniformlyBounded T) (zOver theta : ℝ) :
    sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
        {z | z.2.1 ≤ n})
        (fun z => cappedStatistic z.1 T zOver z.2) theta ≤
      sqRisk (Measure.pi (fun i : I => finitePoissonSampleLaw P (lambda * p i)))
        T theta := by
  rw [sqRisk_capped_restrict_nonoverflow_eq P p hp lambda n hT zOver theta,
    ← labeledStreamLaw_eq_independent P p hp lambda]
  exact sqRisk_labeledStreamLaw_restrict_nonoverflow_le P p hp lambda n hT hTb theta

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable stream statistic](hyp:hT)
[confined to an ordered interval](hyp:hab,hTmem), [a target in that interval](hyp:htheta), and [an
overflow value in it](hyp:hzOver), [capped risk is bounded by independent-stream risk plus
squared interval diameter times the Poisson upper tail](goal). -/
theorem cappedRisk_le_independentRisk_add_tail
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n))
        (fun z => cappedStatistic z.1 T zOver z.2) theta ≤
      sqRisk (Measure.pi (fun i : I => finitePoissonSampleLaw P (lambda * p i)))
        T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  -- Split at count ≤ n. On the good piece, use the capped law theorem and
  -- independent stream law; discard complementary nonnegative risk. On
  -- overflow, use the constant loss `(zOver - theta)^2 ≤ (b-a)^2` and the
  -- Poisson count marginal of the auxiliary law.
  have hTb : UniformlyBounded T := by
    refine ⟨max |a| |b|, (abs_nonneg a).trans (le_max_left _ _), ?_⟩
    intro s
    exact abs_le_max_abs_abs (hTmem s).1 (hTmem s).2
  have hsq : (zOver - theta) ^ 2 ≤ (b - a) ^ 2 := by
    have hleft : 0 ≤ (b - a) - (zOver - theta) := by
      linarith [hzOver.2, htheta.1]
    have hright : 0 ≤ (b - a) + (zOver - theta) := by
      linarith [hzOver.1, htheta.2]
    nlinarith [mul_nonneg hleft hright]
  calc
    sqRisk ((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n))
        (fun z => cappedStatistic z.1 T zOver z.2) theta =
      sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
          {z | z.2.1 ≤ n})
          (fun z => cappedStatistic z.1 T zOver z.2) theta +
      sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
          {z | n < z.2.1})
          (fun z => cappedStatistic z.1 T zOver z.2) theta :=
      sqRisk_capped_split P p hp lambda n hT hTmem hzOver theta
    _ ≤ sqRisk (Measure.pi (fun i : I =>
          finitePoissonSampleLaw P (lambda * p i))) T theta +
        sqRisk (((fixedPoolLaw P n).prod (auxiliaryLaw p hp lambda n)).restrict
          {z | n < z.2.1})
          (fun z => cappedStatistic z.1 T zOver z.2) theta := by
      exact add_le_add_left
        (sqRisk_capped_restrict_nonoverflow_le_independent
          P p hp lambda n hT hTb zOver theta) _
    _ = sqRisk (Measure.pi (fun i : I =>
          finitePoissonSampleLaw P (lambda * p i))) T theta +
        (zOver - theta) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
      rw [sqRisk_capped_restrict_overflow_eq P p hp lambda n T zOver theta]
    _ ≤ _ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_right hsq measureReal_nonneg) _

/-- For [an iid observation law](hyp:P), [label masses](hyp:p) [summing to one](hyp:hp),
[a Poisson mean](hyp:lambda), [a pool size](hyp:n), [a measurable stream statistic](hyp:hT)
[confined to an ordered interval](hyp:hab,hTmem), [a target in that interval](hyp:htheta), and [an
overflow value in it](hyp:hzOver), [fixed-sample squared risk is at most independent
Poisson-stream risk plus squared interval diameter times the Poisson upper tail](goal). -/
theorem fixedRisk_le_independentRisk_add_tail
    (P : Measure X) [IsProbabilityMeasure P]
    (p : I → ℝ≥0) (hp : ∑ i, p i = 1) (lambda : ℝ≥0) (n : ℕ)
    {T : (I → FiniteSample X) → ℝ} (hT : Measurable T)
    {a b theta zOver : ℝ} (hab : a ≤ b)
    (hTmem : ∀ s, T s ∈ Set.Icc a b)
    (htheta : theta ∈ Set.Icc a b) (hzOver : zOver ∈ Set.Icc a b) :
    sqRisk (fixedPoolLaw P n)
        (fun x => fixedStatistic p hp lambda x T zOver) theta ≤
      sqRisk (Measure.pi (fun i : I => finitePoissonSampleLaw P (lambda * p i)))
        T theta +
        (b - a) ^ 2 * (poissonMeasure lambda).real (Set.Ioi n) := by
  exact (fixedRisk_le_cappedRisk P p hp lambda n hT hTmem hzOver theta).trans
    (cappedRisk_le_independentRisk_add_tail P p hp lambda n hT hab hTmem htheta hzOver)

end Causalean.Stat.FiniteRaoBlackwell.Poisson.FinitePartition
