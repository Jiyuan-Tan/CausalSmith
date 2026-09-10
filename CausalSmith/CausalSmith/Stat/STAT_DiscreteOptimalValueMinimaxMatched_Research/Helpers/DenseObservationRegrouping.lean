import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DenseObservationStatisticLaw

/-! Measure-theoretic tools for regrouping the dense Poisson observation experiment. -/

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory

-- @node: densePoissonSampleLaw_reconstruct
/-- The baseline conditional law given the dense sign statistic reconstructs
every member of the dense Poisson family from its sign-count pushforward. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma densePoissonSampleLaw_reconstruct {n d : ℕ}
    [Nonempty (DensePoissonSample d)] (theta : DenseContrast d) :
    ProbabilityTheory.condDistrib id denseSignStatistic
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))))
          (Real.toNNReal (2 * n))) ∘ₘ
      Measure.map denseSignStatistic
        (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n))) =
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) := by
  let Q0 :=
    Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))))
      (Real.toNNReal (2 * n))
  let g : (Fin d → DenseSignCounts) → ENNReal := fun r ↦
    ∏ x, ENNReal.ofReal (oneCellLikelihood 0 (theta.1 x) (r x))
  have hg : Measurable g := measurable_of_countable _
  have hfactor : denseSampleLikelihoodENN theta = g ∘ denseSignStatistic := by
    funext s
    rw [denseSampleLikelihoodENN_factors]
    rfl
  have hQ :
      Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) =
        Q0.withDensity (g ∘ denseSignStatistic) := by
    rw [densePoissonSampleLaw_eq_withDensity, hfactor]
  letI : IsProbabilityMeasure (Q0.withDensity (g ∘ denseSignStatistic)) := by
    rw [← hQ]
    infer_instance
  rw [hQ]
  exact condDistrib_reconstruct_withDensity_factor Q0 denseSignStatistic
    measurable_denseSignStatistic g hg

-- @node: denseSupportedSignKernel_apply_of_abs_le
/-- On the Cai--Low support, the totalized supported sign kernel is the
scaled one-cell Poisson sign law. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the argument satisfies the stated support or positivity restriction](hyp:ht). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseSupportedSignKernel_apply_of_abs_le {n d : ℕ}
    (hregime : DenseRegime n d) (t : ℝ) (ht : |t| ≤ 1) :
    denseSupportedSignKernel n d t =
      denseSignLaw (poissonCellIntensity n d) (denseAmplitude n d * t) := by
  let Q : Measure DenseSignCounts := denseSignBaseline (poissonCellIntensity n d)
  have hf : Measurable (Function.uncurry fun t r ↦
      if |t| ≤ 1 then ENNReal.ofReal (scaledDenseLikelihood n d t r) else 1) := by
    exact (measurable_scaledDenseLikelihood n d).ennreal_ofReal.ite
      (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const)
      measurable_const
  dsimp [denseSupportedSignKernel]
  rw [Kernel.withDensity_apply
    (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))) hf t]
  simp only [ht, ↓reduceIte]
  exact (scaledDenseSignLaw_eq_withDensity n d hregime t ht).symm

-- @node: denseSupportedSignKernel_isProbability
/-- The supported sign kernel is probability-valued both on and off the
Cai--Low support. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseSupportedSignKernel_isProbability {n d : ℕ}
    (hregime : DenseRegime n d) (t : ℝ) :
    IsProbabilityMeasure (denseSupportedSignKernel n d t) := by
  letI : IsProbabilityMeasure (denseSignBaseline (poissonCellIntensity n d)) := by
    unfold denseSignBaseline
    infer_instance
  rw [isProbabilityMeasure_iff]
  by_cases ht : |t| ≤ 1
  · rw [denseSupportedSignKernel_apply_of_abs_le hregime t ht]
    simp [denseSignLaw]
  · have hf : Measurable (Function.uncurry fun t r ↦
        if |t| ≤ 1 then ENNReal.ofReal (scaledDenseLikelihood n d t r) else 1) := by
      exact (measurable_scaledDenseLikelihood n d).ennreal_ofReal.ite
        (measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const)
        measurable_const
    dsimp [denseSupportedSignKernel]
    rw [Kernel.withDensity_apply
      (Kernel.const ℝ (denseSignBaseline (poissonCellIntensity n d))) hf t]
    simp [ht]

-- @node: map_denseObservationMixture_eq_productPriorPredictive
/-- Pushing the genuine dense observation mixture through its sufficient sign
statistic gives exactly the supported product prior-predictive law. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma map_denseObservationMixture_eq_productPriorPredictive
    {n d : ℕ} {epsilon : ℝ} (hregime : DenseRegime n d)
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ)
    [IsProbabilityMeasure nu] (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    Measure.map denseSignStatistic
        (denseObservationMixture n d hdom.1 epsilon hdom nu) =
      Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu
        (denseSupportedSignKernel n d) := by
  classical
  have hK : ∀ t, IsProbabilityMeasure (denseSupportedSignKernel n d t) :=
    denseSupportedSignKernel_isProbability hregime
  letI (_x : Fin d) : IsProbabilityMeasure
      (Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive nu
        (denseSupportedSignKernel n d)) :=
    Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_isProbability
      nu (denseSupportedSignKernel n d) hK
  apply Measure.ext_of_singleton
  intro r
  rw [Measure.map_apply measurable_denseSignStatistic (measurableSet_singleton r)]
  rw [denseObservationMixture, Measure.bind_apply
    (measurable_denseSignStatistic (measurableSet_singleton r))
    (denseObservationKernel n d hdom.1).aemeasurable]
  have hkernel (theta : DenseContrast d) :
      denseObservationKernel n d hdom.1 theta (denseSignStatistic ⁻¹' {r}) =
        (Measure.pi fun x : Fin d ↦
          denseSignLaw (poissonCellIntensity n d) (theta.1 x)) {r} := by
    rw [show denseObservationKernel n d hdom.1 theta =
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) by
      exact Classical.choose_spec (denseObservationKernel_exists n d hdom.1) theta]
    have hm := congrArg (fun mu : Measure (Fin d → DenseSignCounts) ↦ mu {r})
      (map_denseSignStatistic_denseLaw (n := n) theta)
    rw [Measure.map_apply measurable_denseSignStatistic (measurableSet_singleton r)] at hm
    exact hm
  simp_rw [hkernel]
  unfold Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive
  rw [Measure.pi_singleton]
  simp_rw [Causalean.Stat.Minimax.MomentMatchedMixture.priorPredictive_apply _ _
    (measurableSet_singleton (r _))]
  let mu : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d ↦ nu)
  have hmem : ∀ᵐ t ∂mu, ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1 := by
    have hj : ∀ j : Fin d, ∀ᵐ t ∂mu, t j ∈ Set.Icc (-1 : ℝ) 1 := by
      intro j
      have hs : ∀ᵐ x ∂nu, x ∈ Set.Icc (-1 : ℝ) 1 := mem_ae_iff.mpr hsupp
      exact (MeasureTheory.measurePreserving_eval
        (fun _ : Fin d ↦ nu) j).quasiMeasurePreserving.ae hs
    exact ae_all_iff.mpr hj
  have hrestrict : mu.restrict {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1} = mu :=
    Measure.restrict_eq_self_of_ae_mem hmem
  letI (a : DenseContrast d) (x : Fin d) : IsProbabilityMeasure
      (denseSignLaw (poissonCellIntensity n d) (a.1 x)) := by
    unfold denseSignLaw
    infer_instance
  have hsingle (x : Fin d) : Measurable (fun a : DenseContrast d ↦
      denseSignLaw (poissonCellIntensity n d) (a.1 x) {r x}) := by
    have heq (a : DenseContrast d) :
        denseSignLaw (poissonCellIntensity n d) (a.1 x) {r x} =
          denseSignBaseline (poissonCellIntensity n d) {r x} *
            ENNReal.ofReal
              (oneCellLikelihood (poissonCellIntensity n d) (a.1 x) (r x)) := by
      rw [denseSignLaw_eq_withDensity]
      · rw [withDensity_apply _ (measurableSet_singleton (r x)), lintegral_singleton]
        ring
      · unfold poissonCellIntensity
        positivity
      · rw [abs_le]
        constructor <;> linarith [(a.2.2 x).1, (a.2.2 x).2]
    simp_rw [heq]
    have hcoord : Measurable (fun a : DenseContrast d ↦ a.1 x) :=
      (measurable_pi_apply x).comp measurable_subtype_coe
    exact measurable_const.mul (ENNReal.measurable_ofReal.comp
      (((measurable_const.add hcoord).pow_const (r x).1).mul
        ((measurable_const.sub hcoord).pow_const (r x).2)))
  have hmeas : Measurable (fun a : DenseContrast d ↦
      (Measure.pi fun x ↦ denseSignLaw
        (poissonCellIntensity n d) (a.1 x)) {r}) := by
    simp_rw [Measure.pi_singleton]
    exact Finset.univ.measurable_prod fun x _ ↦ hsingle x
  rw [denseScaledProductPrior, show
    (Measure.pi (fun _ : Fin d ↦ nu)).restrict
      {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1} = mu by exact hrestrict]
  rw [lintegral_map]
  · simp_rw [Measure.pi_singleton]
    calc
      (∫⁻ a : Fin d → ℝ, ∏ i,
          denseSignLaw (poissonCellIntensity n d)
            ((if ht : ∀ j, a j ∈ Set.Icc (-1 : ℝ) 1 then
              (⟨fun j ↦ denseAmplitude n d * a j, hdom.1, by
                intro j
                have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
                have hjlo := mul_le_mul_of_nonneg_left (ht j).1 ha0
                have hjhi := mul_le_mul_of_nonneg_left (ht j).2 ha0
                constructor <;> nlinarith [hdom.2.2.2.2]⟩ : DenseContrast d)
            else ⟨fun _ ↦ 0, hdom.1, by intro; norm_num⟩).1 i) {r i} ∂mu) =
          ∫⁻ a : Fin d → ℝ, ∏ i,
            denseSupportedSignKernel n d (a i) {r i} ∂mu := by
        apply lintegral_congr_ae
        filter_upwards [hmem] with t ht
        simp only [dif_pos ht]
        apply Finset.prod_congr rfl
        intro x _hx
        rw [← denseSupportedSignKernel_apply_of_abs_le hregime (t x)]
        simpa [abs_le] using ht x
      _ = ∏ x, ∫⁻ theta : ℝ,
          denseSupportedSignKernel n d theta {r x} ∂nu := by
        let X : Fin d → (Fin d → ℝ) → ENNReal := fun x t ↦
          denseSupportedSignKernel n d (t x) {r x}
        have hXm (x : Fin d) : Measurable (X x) :=
          ((denseSupportedSignKernel n d).measurable_coe
            (measurableSet_singleton (r x))).comp (measurable_pi_apply x)
        have hXi : iIndepFun X mu := by
          simpa [X, mu] using (iIndepFun_pi
            (X := fun x (t : ℝ) ↦ denseSupportedSignKernel n d t {r x})
            (fun x ↦ ((denseSupportedSignKernel n d).measurable_coe
              (measurableSet_singleton (r x))).aemeasurable))
        rw [show (∫⁻ a : Fin d → ℝ, ∏ i,
            denseSupportedSignKernel n d (a i) {r i} ∂mu) =
            ∏ x, ∫⁻ a : Fin d → ℝ,
              denseSupportedSignKernel n d (a x) {r x} ∂mu by
          simpa [X] using
            (lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ X hXi hXm)]
        apply Finset.prod_congr rfl
        intro x _hx
        exact (measurePreserving_eval (fun _ : Fin d ↦ nu) x).lintegral_comp
          ((denseSupportedSignKernel n d).measurable_coe
            (measurableSet_singleton (r x)))
  · exact hmeas
  · let S : Set (Fin d → ℝ) := {t | ∀ j, t j ∈ Set.Icc (-1 : ℝ) 1}
    have htrue : Measurable (fun t : S ↦
        (⟨fun j ↦ denseAmplitude n d * t.1 j, hdom.1, by
          intro j
          have ha0 : 0 ≤ denseAmplitude n d := le_of_lt hdom.2.2.2.1
          have hjlo := mul_le_mul_of_nonneg_left (t.2 j).1 ha0
          have hjhi := mul_le_mul_of_nonneg_left (t.2 j).2 ha0
          constructor <;> nlinarith [hdom.2.2.2.2]⟩ : DenseContrast d)) := by
      apply Measurable.subtype_mk
      apply measurable_pi_lambda
      intro j
      exact measurable_const.mul
        ((measurable_pi_apply j).comp measurable_subtype_coe)
    have hS : MeasurableSet S := by
      dsimp [S]
      convert MeasurableSet.iInter (fun j : Fin d ↦
        (measurableSet_Icc : MeasurableSet (Set.Icc (-1 : ℝ) 1)).preimage
          (measurable_pi_apply j)) using 1 <;> ext t <;> simp
    exact htrue.dite measurable_const hS

-- @node: denseObservationMixture_reconstruct_from_product
/-- The same baseline conditional kernel reconstructs the full observation
mixture from the supported product sign-count predictive law. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the dense construction domain conditions hold](hyp:hdom), and [the prior is supported on the unit interval](hyp:hsupp). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseObservationMixture_reconstruct_from_product
    {n d : ℕ} {epsilon : ℝ} (hregime : DenseRegime n d)
    (hdom : DenseConstructionDomain n d epsilon) (nu : Measure ℝ)
    [IsProbabilityMeasure nu] [Nonempty (DensePoissonSample d)]
    (hsupp : nu (Set.Icc (-1) 1)ᶜ = 0) :
    let Krec := ProbabilityTheory.condDistrib id denseSignStatistic
      (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
        (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hdom.1))))
        (Real.toNNReal (2 * n)))
    Krec ∘ₘ
        Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu
          (denseSupportedSignKernel n d) =
      denseObservationMixture n d hdom.1 epsilon hdom nu := by
  let prior := denseScaledProductPrior n d epsilon hdom nu
  let Kobs := denseObservationKernel n d hdom.1
  let Kstat := Kobs.map denseSignStatistic
  let Q0 :=
    Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hdom.1))))
      (Real.toNNReal (2 * n))
  let Krec := ProbabilityTheory.condDistrib id denseSignStatistic Q0
  have hstatKernel :
      Kernel.deterministic denseSignStatistic measurable_denseSignStatistic ∘ₖ Kobs =
        Kstat := by
    ext theta
    rw [Kernel.comp_apply, Measure.deterministic_comp_eq_map,
      Kernel.map_apply _ measurable_denseSignStatistic]
  have hreconstruct : Krec ∘ₖ Kstat = Kobs := by
    ext theta s
    rw [Kernel.comp_apply, Kernel.map_apply _ measurable_denseSignStatistic]
    have hKobs : Kobs theta =
        Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw theta))) (Real.toNNReal (2 * n)) :=
      Classical.choose_spec (denseObservationKernel_exists n d hdom.1) theta
    exact congrArg (fun mu : Measure (DensePoissonSample d) ↦ mu s) (by
      rw [hKobs]
      simpa [Krec, Q0] using (densePoissonSampleLaw_reconstruct (n := n) theta))
  have hmapMixture :
      Measure.map denseSignStatistic (Kobs ∘ₘ prior) = Kstat ∘ₘ prior := by
    calc
      Measure.map denseSignStatistic (Kobs ∘ₘ prior) =
          Kernel.deterministic denseSignStatistic measurable_denseSignStatistic ∘ₘ
            (Kobs ∘ₘ prior) := by
        rw [Measure.deterministic_comp_eq_map]
      _ = (Kernel.deterministic denseSignStatistic measurable_denseSignStatistic ∘ₖ
            Kobs) ∘ₘ prior := Measure.comp_assoc
      _ = Kstat ∘ₘ prior := by rw [hstatKernel]
  rw [← map_denseObservationMixture_eq_productPriorPredictive
    hregime hdom nu hsupp]
  change Krec ∘ₘ Measure.map denseSignStatistic (Kobs ∘ₘ prior) = Kobs ∘ₘ prior
  rw [hmapMixture, Measure.comp_assoc, hreconstruct]

-- @node: tvDist_bind_le_denseRegrouping
/-- Passing two probability laws through the same Markov kernel cannot increase
their total-variation distance. [The displayed identity or bound is the asserted conclusion](goal). -/
lemma tvDist_bind_le_denseRegrouping
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (K : Kernel X Y) [IsMarkovKernel K] :
    Causalean.Stat.tvDist (K ∘ₘ mu) (K ∘ₘ nu) ≤
      Causalean.Stat.tvDist mu nu := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  rw [Measure.real, Measure.real, Measure.bind_apply hA K.aemeasurable,
    Measure.bind_apply hA K.aemeasurable]
  have hmeas : Measurable (fun x => (K x A).toReal) :=
    (K.measurable_coe hA).ennreal_toReal
  have hrange : ∀ x, (K x A).toReal ∈ Set.Icc (0 : ℝ) (0 + 1) := by
    intro x
    letI : IsProbabilityMeasure (K x) := inferInstance
    exact ⟨ENNReal.toReal_nonneg, by
      simpa only [Measure.real, zero_add] using
        (measureReal_le_one : (K x).real A ≤ 1)⟩
  have hfinite : ∀ x, K x A < ⊤ := by
    intro x
    letI : IsProbabilityMeasure (K x) := inferInstance
    exact measure_lt_top _ _
  rw [← integral_toReal (K.measurable_coe hA).aemeasurable
      (Filter.Eventually.of_forall hfinite),
    ← integral_toReal (K.measurable_coe hA).aemeasurable
      (Filter.Eventually.of_forall hfinite)]
  change |∫ x, (K x A).toReal ∂mu - ∫ x, (K x A).toReal ∂nu| ≤
    Causalean.Stat.tvDist mu nu
  simpa only [zero_add, mul_one] using
    (Causalean.Stat.tvDist_integral_range mu nu
      (fun x => (K x A).toReal) hmeas 0 1 zero_le_one hrange)

-- @node: denseObservationMixtures_tv_le_product
/-- Dense full-observation prior mixtures are no farther apart than their
product sign-count prior predictives. This uses [the sample size and alphabet lie in the dense regime](hyp:hregime), and [the dense construction domain conditions hold](hyp:hdom), and [the first prior is supported on the unit interval](hyp:hsupp0), and [the second prior is supported on the unit interval](hyp:hsupp1). [The displayed identity or bound is the asserted conclusion](goal). -/
lemma denseObservationMixtures_tv_le_product
    {n d : ℕ} {epsilon : ℝ} (hregime : DenseRegime n d)
    (hdom : DenseConstructionDomain n d epsilon) (nu0 nu1 : Measure ℝ)
    [IsProbabilityMeasure nu0] [IsProbabilityMeasure nu1]
    (hsupp0 : nu0 (Set.Icc (-1) 1)ᶜ = 0)
    (hsupp1 : nu1 (Set.Icc (-1) 1)ᶜ = 0) :
    Causalean.Stat.tvDist
        (denseObservationMixture n d hdom.1 epsilon hdom nu0)
        (denseObservationMixture n d hdom.1 epsilon hdom nu1) ≤
      Causalean.Stat.tvDist
        (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu0
          (denseSupportedSignKernel n d))
        (Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu1
          (denseSupportedSignKernel n d)) := by
  letI : Nonempty (DensePoissonSample d) :=
    ⟨⟨0, fun i ↦ Fin.elim0 i⟩⟩
  let Krec := ProbabilityTheory.condDistrib id denseSignStatistic
    (Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition.finitePoissonSampleLaw
      (obsLaw (observedMarginal (denseLaw (denseZeroContrast d hdom.1))))
      (Real.toNNReal (2 * n)))
  let pred0 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu0
      (denseSupportedSignKernel n d)
  let pred1 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive d nu1
      (denseSupportedSignKernel n d)
  have hK : ∀ t, IsProbabilityMeasure (denseSupportedSignKernel n d t) :=
    denseSupportedSignKernel_isProbability hregime
  letI : IsProbabilityMeasure pred0 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive_isProbability
      d nu0 (denseSupportedSignKernel n d) hK
  letI : IsProbabilityMeasure pred1 :=
    Causalean.Stat.Minimax.MomentMatchedMixture.productPriorPredictive_isProbability
      d nu1 (denseSupportedSignKernel n d) hK
  have hrec0 : Krec ∘ₘ pred0 =
      denseObservationMixture n d hdom.1 epsilon hdom nu0 := by
    simpa [Krec, pred0] using
      denseObservationMixture_reconstruct_from_product hregime hdom nu0 hsupp0
  have hrec1 : Krec ∘ₘ pred1 =
      denseObservationMixture n d hdom.1 epsilon hdom nu1 := by
    simpa [Krec, pred1] using
      denseObservationMixture_reconstruct_from_product hregime hdom nu1 hsupp1
  rw [← hrec0, ← hrec1]
  exact tvDist_bind_le_denseRegrouping pred0 pred1 Krec

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
