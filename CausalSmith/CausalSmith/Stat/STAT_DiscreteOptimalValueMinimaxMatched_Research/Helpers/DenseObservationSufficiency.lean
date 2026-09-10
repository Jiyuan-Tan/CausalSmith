import CausalSmith.Stat.STAT_DiscreteOptimalValueMinimaxMatched_Research.Helpers.DensePriorSetup

namespace CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

-- @node: denseObservedAtomMass
/-- [each dense observed atom has mass $(1+	heta_x)/(4d)$ when treatment and outcome agree and $(1-	heta_x)/(4d)$ otherwise](goal). -/
lemma denseObservedAtomMass {d : ℕ} (theta : DenseContrast d)
    (x : Fin d) (a y : Bool) :
    jointMass (observedMarginal (denseLaw theta)) x a y =
      (1 + (if a = y then theta.1 x else -theta.1 x)) / (4 * d) := by
  have h := denseLaw_jointMass theta
  fin_cases a <;> fin_cases y
  · rw [h.1]; simp; ring
  · rw [h.2.1]; simp; ring
  · rw [h.2.2.1]; simp; ring
  · rw [h.2.2.2]; simp; ring

open Causalean.Mathlib.Probability.FiniteMarkedPoissonPartition

-- @node: finitePoissonSampleLaw_singleton_denseSufficiency
/-- If [the stated lam condition holds](hyp:lam), then [the stated finite poisson sample law singleton dense sufficiency relation holds](goal). -/
lemma finitePoissonSampleLaw_singleton_denseSufficiency
    {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (P : Measure X) [IsProbabilityMeasure P] (lam : ℝ≥0)
    (s : FiniteSample X) :
    finitePoissonSampleLaw P lam {s} =
      poissonMeasure lam {s.count} * ∏ i, P {s.points i} := by
  rcases s with ⟨m, s⟩
  have hm : Measure.map (fixedSizeEmbed m)
      (Measure.pi (fun _ : Fin m => P)) {⟨m, s⟩} =
      Measure.pi (fun _ : Fin m => P) {s} := by
    rw [Measure.map_apply (measurable_fixedSizeEmbed m)
      (measurableSet_singleton ⟨m, s⟩)]
    congr 1
    ext x
    simp [fixedSizeEmbed]
  have h := congrArg (fun mu : Measure (FiniteSample X) => mu {⟨m, s⟩})
    (finitePoissonSampleLaw_restrict_count_eq P lam m)
  convert h using 1 <;>
    simp [Measure.restrict_apply, hm, Measure.pi_singleton,
      FiniteSample.count, FiniteSample.points]
  all_goals congr

-- @node: denseObservedAtomMeasure_likelihood
/-- [each dense observed atom equals its zero-contrast mass times the corresponding one-observation likelihood factor](goal). -/
lemma denseObservedAtomMeasure_likelihood {d : ℕ} (theta : DenseContrast d)
    (z : Obs d) :
    obsLaw (observedMarginal (denseLaw theta)) {z} =
      obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))) {z} *
        ENNReal.ofReal (if z.2.1 = z.2.2 then 1 + theta.1 z.1 else 1 - theta.1 z.1) := by
  have hf : 0 ≤ (if z.2.1 = z.2.2 then 1 + theta.1 z.1 else 1 - theta.1 z.1) := by
    split_ifs <;> linarith [(theta.2.2 z.1).1, (theta.2.2 z.1).2]
  apply (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _)
    (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hf]
  simpa [obsLaw, jointMass, PMF.toMeasure_apply_singleton] using
    denseLaw_atom_likelihood theta z.1 z.2.1 z.2.2

-- @node: denseSampleLikelihoodENN
/-- For [the specified contrast, smaller alphabet size](hyp:theta,s), the [dense sample likelihood is the product of the observation-level likelihood factors relative to the zero contrast](goal). -/
noncomputable def denseSampleLikelihoodENN {d : ℕ} (theta : DenseContrast d)
    (s : DensePoissonSample d) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal
    (if (s.points i).2.1 = (s.points i).2.2
      then 1 + theta.1 (s.points i).1 else 1 - theta.1 (s.points i).1)

-- @node: densePoissonSample_singleton_likelihood
/-- [each dense Poisson sample probability equals its zero-contrast probability times the dense sample likelihood](goal). -/
lemma densePoissonSample_singleton_likelihood {n d : ℕ}
    (theta : DenseContrast d) (s : DensePoissonSample d) :
    finitePoissonSampleLaw (obsLaw (observedMarginal (denseLaw theta)))
        (Real.toNNReal (2 * n)) {s} =
      finitePoissonSampleLaw
          (obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))))
          (Real.toNNReal (2 * n)) {s} * denseSampleLikelihoodENN theta s := by
  rw [finitePoissonSampleLaw_singleton_denseSufficiency,
    finitePoissonSampleLaw_singleton_denseSufficiency]
  simp_rw [denseObservedAtomMeasure_likelihood theta]
  rw [Finset.prod_mul_distrib]
  unfold denseSampleLikelihoodENN
  ring

-- @node: denseSignStatistic
/-- For [the specified smaller alphabet size](hyp:s), the [dense sign statistic counts, in each cell, observations where treatment and outcome agree and disagree](goal). -/
noncomputable def denseSignStatistic {d : ℕ} (s : DensePoissonSample d) :
    Fin d → DenseSignCounts := fun x =>
  ((Finset.univ.filter fun i =>
      (s.points i).1 = x ∧ (s.points i).2.1 = (s.points i).2.2).card,
   (Finset.univ.filter fun i =>
      (s.points i).1 = x ∧ (s.points i).2.1 ≠ (s.points i).2.2).card)

-- @node: measurable_denseSignStatistic
/-- [the stated measurable dense sign statistic relation holds](goal). -/
@[fun_prop]
lemma measurable_denseSignStatistic {d : ℕ} :
    Measurable (denseSignStatistic : DensePoissonSample d → Fin d → DenseSignCounts) := by
  exact measurable_of_countable _

-- @node: denseSampleLikelihoodENN_factors
/-- [the dense sample likelihood factors across alphabet cells into one-cell likelihoods](goal). -/
lemma denseSampleLikelihoodENN_factors {d : ℕ} (theta : DenseContrast d)
    (s : DensePoissonSample d) :
    denseSampleLikelihoodENN theta s =
      ∏ x : Fin d, ENNReal.ofReal
        (oneCellLikelihood 0 (theta.1 x) (denseSignStatistic s x)) := by
  classical
  have hp (x : Fin d) : 0 ≤ 1 + theta.1 x := by
    linarith [(theta.2.2 x).1]
  have hm (x : Fin d) : 0 ≤ 1 - theta.1 x := by
    linarith [(theta.2.2 x).2]
  simp only [denseSampleLikelihoodENN, oneCellLikelihood, denseSignStatistic]
  simp_rw [ENNReal.ofReal_mul (pow_nonneg (hp _) _),
    ENNReal.ofReal_pow (hp _), ENNReal.ofReal_pow (hm _)]
  let f : Fin s.count → ℝ≥0∞ := fun i => ENNReal.ofReal
    (if (s.points i).2.1 = (s.points i).2.2
      then 1 + theta.1 (s.points i).1 else 1 - theta.1 (s.points i).1)
  rw [← Finset.prod_fiberwise Finset.univ (fun i => (s.points i).1) f]
  apply Finset.prod_congr rfl
  intro x _hx
  rw [← Finset.prod_filter_mul_prod_filter_not
    (Finset.univ.filter fun i => (s.points i).1 = x)
    (fun i => (s.points i).2.1 = (s.points i).2.2) f]
  have hplus :
      (∏ i ∈ (Finset.univ.filter fun i => (s.points i).1 = x) with
          (s.points i).2.1 = (s.points i).2.2, f i) =
        ENNReal.ofReal (1 + theta.1 x) ^
          (Finset.univ.filter fun i =>
            (s.points i).1 = x ∧ (s.points i).2.1 = (s.points i).2.2).card := by
    rw [Finset.prod_eq_pow_card]
    · congr 2
      ext i
      simp
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [f, hi.2, hi.1]
  have hminus :
      (∏ i ∈ (Finset.univ.filter fun i => (s.points i).1 = x) with
          ¬(s.points i).2.1 = (s.points i).2.2, f i) =
        ENNReal.ofReal (1 - theta.1 x) ^
          (Finset.univ.filter fun i =>
            (s.points i).1 = x ∧ (s.points i).2.1 ≠ (s.points i).2.2).card := by
    rw [Finset.prod_eq_pow_card]
    · congr 2
      ext i
      simp
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp [f, hi.2, hi.1]
  rw [hplus, hminus]

-- @node: measurable_denseSampleLikelihoodENN
/-- [the stated measurable dense sample likelihood enn relation holds](goal). -/
@[fun_prop]
lemma measurable_denseSampleLikelihoodENN {d : ℕ} (theta : DenseContrast d) :
    Measurable (denseSampleLikelihoodENN theta) := by
  exact measurable_of_countable _

-- @node: densePoissonSampleLaw_eq_withDensity
/-- [the dense Poisson sample law is the zero-contrast law tilted by the dense sample likelihood](goal). -/
lemma densePoissonSampleLaw_eq_withDensity {n d : ℕ} (theta : DenseContrast d) :
    finitePoissonSampleLaw (obsLaw (observedMarginal (denseLaw theta)))
        (Real.toNNReal (2 * n)) =
      (finitePoissonSampleLaw
        (obsLaw (observedMarginal (denseLaw (denseZeroContrast d theta.2.1))))
        (Real.toNNReal (2 * n))).withDensity (denseSampleLikelihoodENN theta) := by
  apply Measure.ext_of_singleton
  intro s
  rw [withDensity_apply _ (measurableSet_singleton s),
    lintegral_singleton]
  simpa [mul_comm] using
    (densePoissonSample_singleton_likelihood (n := n) theta s)

-- @node: map_withDensity_comp_singleton
/-- If [the stated stat condition holds](hyp:hstat), and [the stated g condition holds](hyp:g), then [the stated map with density composition singleton relation holds](goal). -/
lemma map_withDensity_comp_singleton
    {Z S : Type*} [MeasurableSpace Z] [MeasurableSpace S]
    [MeasurableSingletonClass S]
    (Q0 : Measure Z) (stat : Z → S) (hstat : Measurable stat)
    (g : S → ℝ≥0∞) (_hg : Measurable g) (s : S) :
    Measure.map stat (Q0.withDensity (g ∘ stat)) {s} =
      g s * Measure.map stat Q0 {s} := by
  rw [Measure.map_apply hstat (measurableSet_singleton s),
    withDensity_apply _ (hstat (measurableSet_singleton s)),
    Measure.map_apply hstat (measurableSet_singleton s)]
  calc
    (∫⁻ z in stat ⁻¹' {s}, (g ∘ stat) z ∂Q0) =
        ∫⁻ _z in stat ⁻¹' {s}, g s ∂Q0 := by
      apply setLIntegral_congr_fun (hstat (measurableSet_singleton s))
      intro z hz
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
      simp [Function.comp_apply, hz]
    _ = g s * Q0 (stat ⁻¹' {s}) := by simp

-- @node: condDistrib_tilt_eq_of_factor
/-- If [the stated stat condition holds](hyp:hstat), and [the stated g condition holds](hyp:g), and [the stated g condition holds](hyp:hg), and [the stated support condition holds](hyp:hs), and [the stated base condition holds](hyp:hbase), then [at every supported statistic value with positive baseline mass, tilting by a statistic-measurable density leaves the conditional distribution unchanged](goal). -/
lemma condDistrib_tilt_eq_of_factor
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Countable Z] [Nonempty Z]
    [MeasurableSpace S] [StandardBorelSpace S] [Countable S]
    [MeasurableSingletonClass S]
    (Q0 : Measure Z) [IsProbabilityMeasure Q0]
    (stat : Z → S) (hstat : Measurable stat)
    (g : S → ℝ≥0∞) (hg : Measurable g)
    [IsProbabilityMeasure (Q0.withDensity (g ∘ stat))]
    (s : S) (hs : g s ≠ 0) (hbase : Measure.map stat Q0 {s} ≠ 0) :
    ProbabilityTheory.condDistrib id stat (Q0.withDensity (g ∘ stat)) s =
      ProbabilityTheory.condDistrib id stat Q0 s := by
  classical
  let Q := Q0.withDensity (g ∘ stat)
  have hmapQ : Measure.map stat Q {s} ≠ 0 := by
    rw [show Measure.map stat Q {s} = g s * Measure.map stat Q0 {s} by
      exact map_withDensity_comp_singleton Q0 stat hstat g hg s]
    exact mul_ne_zero hs hbase
  apply Measure.ext_of_singleton
  intro z
  rw [ProbabilityTheory.condDistrib_apply_of_ne_zero
      (μ := Q) measurable_id s hmapQ {z},
    ProbabilityTheory.condDistrib_apply_of_ne_zero
      (μ := Q0) measurable_id s hbase {z}]
  have hjoint (mu : Measure Z) :
      Measure.map (fun a => (stat a, id a)) mu ({s} ×ˢ {z}) =
        if stat z = s then mu {z} else 0 := by
    rw [Measure.map_apply (hstat.prodMk measurable_id)
      (MeasurableSet.singleton s |>.prod (MeasurableSet.singleton z))]
    split_ifs with hsz
    · congr 1
      ext w
      simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
        id_eq, and_iff_right_iff_imp]
      intro hw
      simpa [hw] using hsz
    · have hempty : (fun a => (stat a, id a)) ⁻¹' ({s} ×ˢ {z}) = ∅ := by
        ext w
        simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff,
          id_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro hw hwz
        apply hsz
        simpa [hwz] using hw
      rw [hempty, measure_empty]
  rw [hjoint Q, hjoint Q0]
  by_cases hzs : stat z = s
  · simp only [hzs, ↓reduceIte]
    have hQz : Q {z} = g s * Q0 {z} := by
      dsimp [Q]
      rw [withDensity_apply _ (measurableSet_singleton z), lintegral_singleton]
      simp [Function.comp_apply, hzs]
    rw [hQz]
    rw [show Measure.map stat Q {s} = g s * Measure.map stat Q0 {s} by
      exact map_withDensity_comp_singleton Q0 stat hstat g hg s]
    have hgsTop : g s ≠ ⊤ := by
      intro htop
      have hfinite : Measure.map stat Q {s} ≠ ⊤ := measure_ne_top _ _
      rw [show Measure.map stat Q {s} = g s * Measure.map stat Q0 {s} by
        exact map_withDensity_comp_singleton Q0 stat hstat g hg s,
        htop, ENNReal.top_mul hbase] at hfinite
      exact hfinite rfl
    rw [ENNReal.mul_inv (Or.inl hs) (Or.inr hbase)]
    calc
      (g s)⁻¹ * (Measure.map stat Q0 {s})⁻¹ * (g s * Q0 {z}) =
          ((g s)⁻¹ * g s) * ((Measure.map stat Q0 {s})⁻¹ * Q0 {z}) := by
        ring
      _ = (Measure.map stat Q0 {s})⁻¹ * Q0 {z} := by
        rw [ENNReal.inv_mul_cancel hs hgsTop]
        simp
  · simp [hzs]

-- @node: ae_singleton_measure_ne_zero
/-- [almost every point has nonzero singleton mass](goal). -/
lemma ae_singleton_measure_ne_zero
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (μ : Measure S) : ∀ᵐ s ∂μ, μ {s} ≠ 0 := by
  apply mem_ae_iff.mpr
  have hbad : {s : S | μ {s} = 0} =
      ⋃ s : {s : S // μ {s} = 0}, ({s.1} : Set S) := by
    ext s
    simp
  have hcompl : {s : S | μ {s} ≠ 0}ᶜ = {s : S | μ {s} = 0} := by
    ext s
    simp
  rw [hcompl, hbad]
  exact measure_iUnion_null fun s ↦ s.property

-- @node: condDistrib_reconstruct_withDensity_factor
/-- If [the stated stat condition holds](hyp:hstat), and [the stated g condition holds](hyp:g), and [the stated g condition holds](hyp:hg), then [the baseline conditional kernel, mixed against the tilted statistic law, reconstructs the tilted distribution](goal). -/
lemma condDistrib_reconstruct_withDensity_factor
    {Z S : Type*} [MeasurableSpace Z] [StandardBorelSpace Z] [Countable Z] [Nonempty Z]
    [MeasurableSpace S] [StandardBorelSpace S] [Countable S]
    [MeasurableSingletonClass S]
    (Q0 : Measure Z) [IsProbabilityMeasure Q0]
    (stat : Z → S) (hstat : Measurable stat)
    (g : S → ℝ≥0∞) (hg : Measurable g)
    [IsProbabilityMeasure (Q0.withDensity (g ∘ stat))] :
    ProbabilityTheory.condDistrib id stat Q0 ∘ₘ
        Measure.map stat (Q0.withDensity (g ∘ stat)) =
      Q0.withDensity (g ∘ stat) := by
  let Q := Q0.withDensity (g ∘ stat)
  have hnonzero : ∀ᵐ s ∂Measure.map stat Q, g s ≠ 0 := by
    apply mem_ae_iff.mpr
    have hzero : Measure.map stat Q {s | g s = 0} = 0 := by
      have hset : {s | g s = 0} = g ⁻¹' {0} := by ext; simp
      rw [hset, Measure.map_apply hstat (hg (measurableSet_singleton 0)),
        show Q = Q0.withDensity (g ∘ stat) by rfl,
        withDensity_apply _ (hstat (hg (measurableSet_singleton 0)))]
      apply setLIntegral_eq_zero
      · exact hstat (hg (measurableSet_singleton 0))
      · intro z hz
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz
        simp [Function.comp_apply, hz]
    have hcomp : {s | g s ≠ 0}ᶜ = {s | g s = 0} := by
      ext s
      simp
    rw [hcomp]
    exact hzero
  have hcond : ProbabilityTheory.condDistrib id stat Q0 =ᵐ[Measure.map stat Q]
      ProbabilityTheory.condDistrib id stat Q := by
    have hbaseQ0 : ∀ᵐ s ∂Measure.map stat Q0,
        Measure.map stat Q0 {s} ≠ 0 :=
      ae_singleton_measure_ne_zero (Measure.map stat Q0)
    have hmap : Measure.map stat Q =
        (Measure.map stat Q0).withDensity g := by
      apply Measure.ext_of_singleton
      intro s
      rw [show Q = Q0.withDensity (g ∘ stat) by rfl,
        map_withDensity_comp_singleton Q0 stat hstat g hg s,
        withDensity_apply _ (measurableSet_singleton s), lintegral_singleton]
    have hbaseQ : ∀ᵐ s ∂Measure.map stat Q,
        Measure.map stat Q0 {s} ≠ 0 := by
      rw [hmap]
      apply (ae_withDensity_iff hg).2
      filter_upwards [hbaseQ0] with s hs
      exact fun _ ↦ hs
    filter_upwards [hnonzero, hbaseQ] with s hs hbase
    symm
    exact condDistrib_tilt_eq_of_factor Q0 stat hstat g hg s hs hbase
  calc
    ProbabilityTheory.condDistrib id stat Q0 ∘ₘ Measure.map stat Q =
        ProbabilityTheory.condDistrib id stat Q ∘ₘ Measure.map stat Q := by
      exact Measure.comp_congr hcond
    _ = Q := by
      simpa using ProbabilityTheory.condDistrib_comp_map
        (μ := Q) (X := stat) (Y := id) hstat.aemeasurable aemeasurable_id

end CausalSmith.Stat.DiscreteOptimalValueMinimaxMatched
