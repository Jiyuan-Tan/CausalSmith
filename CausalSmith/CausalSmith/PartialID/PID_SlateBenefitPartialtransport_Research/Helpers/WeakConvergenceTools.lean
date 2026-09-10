import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.CitedGates
import CausalSmith.PartialID.PID_SlateBenefitPartialtransport_Research.Helpers.Estimator
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Small measure-theoretic bridges used by the pointwise limit theorem. -/

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace CausalSmith.PartialID.SlateBenefitPartialTransport

/-- A Gaussian measure in Mathlib's sense has total mass one. The definition does not expose this as a typeclass instance, so we recover it from the pushforward by the zero continuous linear functional. Given [the stated hypotheses](hyp:hQ), [the stated conclusion follows](goal). -/
theorem IsGaussian.isProbabilityMeasure_of_normed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Q : Measure E) (hQ : IsGaussian Q) : IsProbabilityMeasure Q := by
  rw [isProbabilityMeasure_iff]
  have hz := hQ.map_eq_gaussianReal (0 : StrongDual ℝ E)
  have hm : (Measure.map (fun _ : E => (0 : ℝ)) Q) univ = Q univ := by
    rw [Measure.map_apply (measurable_const) MeasurableSet.univ]
    simp
  have hz' : Measure.map (fun _ : E => (0 : ℝ)) Q = gaussianReal 0 0 := by
    simpa using hz
  rw [← hm, hz']
  exact measure_univ

/-- Probability laws on the finite-dimensional spaces used here are tight. [the stated conclusion follows](goal). -/
theorem tightProbabilityLaw_of_probability
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace E]
    [SecondCountableTopology E] [BorelSpace E]
    (Q : Measure E) [IsProbabilityMeasure Q] : TightProbabilityLaw Q := by
  intro ε hε
  have ht : IsTightMeasureSet ({Q} : Set (Measure E)) :=
    isTightMeasureSet_singleton
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  obtain ⟨C, hC, hbound⟩ := ht ε hε
  exact ⟨C, hC, hbound Q (by simp)⟩

/-- The centered vector used by the multinomial CLT is definitionally the scaled empirical probability vector. [the stated conclusion follows](goal). -/
theorem empiricalAtomVector_eq_smul_sub
    {Ω 𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (Pobs : Measure (ObservedDatum 𝒳 K)) (n : ℕ) (ω : Ω) :
    empiricalAtomVector O Pobs n ω = Real.sqrt n •
      (empiricalProbabilityVector O n ω - fun o => Pobs.real {o}) := by
  funext o
  simp only [empiricalAtomVector, empiricalProbabilityVector, empiricalFreq,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  have hs : (∑ r ∈ Finset.range n, if O r ω = o then (1 : ℝ) else 0) =
      ∑ r ∈ Finset.range n, if decide (O r ω = o) = true then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : O r ω = o <;> simp [h]
  rw [hs]

/-- Measurability of the finite empirical atom vector. Given [the stated hypotheses](hyp:hO), [the stated conclusion follows](goal). -/
theorem measurable_empiricalProbabilityVector
    {Ω 𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace 𝒳] [MeasurableSingletonClass 𝒳]
    (O : ℕ → Ω → ObservedDatum 𝒳 K) (hO : ∀ i, Measurable (O i)) (n : ℕ) :
    Measurable (empiricalProbabilityVector O n) := by
  rw [measurable_pi_iff]
  intro o
  unfold empiricalProbabilityVector empiricalFreq
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro r hr
  apply Measurable.ite
  · have heq : {a | decide (O r a = o) = true} = O r ⁻¹' {o} := by
      ext a
      simp
    rw [heq]
    exact hO r (measurableSet_singleton o)
  · exact measurable_const
  · exact measurable_const

/-- Given [the stated hypotheses](hyp:h), [the observations whenever iid sampling all map is measurable](goal). -/
theorem measurable_observations_of_iidSampling_all
    {Ω 𝒳 : Type*} [Fintype 𝒳] [DecidableEq 𝒳] {K : ℕ}
    [MeasurableSpace Ω] [MeasurableSpace 𝒳]
    {μ : Measure Ω} {Pobs : Measure (ObservedDatum 𝒳 K)}
    (O : ℕ → Ω → ObservedDatum 𝒳 K)
    (h : ∀ n, IidSampling n μ Pobs O) : ∀ i, Measurable (O i) := by
  intro i
  exact (h (i + 1)).measurable i (by omega)

/-- Repackage the paper's test-integral definition as Mathlib weak convergence of probability measures. Given [the stated hypotheses](hyp:hX), [the stated conclusion follows](goal). -/
theorem WeakConverges.tendsto_probabilityMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoEMetricSpace E]
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [TopologicalSpace.IsCompletelyPseudoMetrizableSpace E]
    [SecondCountableTopology E] [BorelSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Measure E} [IsProbabilityMeasure Q]
    {Xn : ℕ → Ω → E} (hX : ∀ n, Measurable (Xn n))
    (h : WeakConverges Xn Q μ) :
    let Qn : ℕ → ProbabilityMeasure E := fun n =>
      ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
    let Qlim : ProbabilityMeasure E := ⟨Q, inferInstance⟩
    Tendsto Qn atTop (𝓝 Qlim) := by
  let Qn : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  let Qlim : ProbabilityMeasure E := ⟨Q, inferInstance⟩
  change Tendsto Qn atTop (𝓝 Qlim)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hf := h f f.continuous ⟨‖f‖, fun x => by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x⟩
  simpa only [Qn, Qlim, ProbabilityMeasure.coe_mk,
    MeasureTheory.integral_map (hX _).aemeasurable f.continuous.aestronglyMeasurable] using hf

/-- A weakly convergent sequence of random vectors has uniformly tight laws. Given [the stated hypotheses](hyp:hX), [the stated conclusion follows](goal). -/
theorem WeakConverges.isTightMeasureSet_range_map
    {Ω E : Type*} [MeasurableSpace Ω] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Measure E} [IsProbabilityMeasure Q]
    {Xn : ℕ → Ω → E} (hX : ∀ n, Measurable (Xn n))
    (h : WeakConverges Xn Q μ) :
    IsTightMeasureSet (Set.range fun n => μ.map (Xn n)) := by
  let Qn : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (Xn n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  let Qlim : ProbabilityMeasure E := ⟨Q, inferInstance⟩
  have ht : Tendsto Qn atTop (𝓝 Qlim) := h.tendsto_probabilityMeasure hX
  have hc : IsCompact (insert Qlim (Set.range Qn)) := ht.isCompact_insert_range
  have htc : IsTightMeasureSet
      {((q : ProbabilityMeasure E) : Measure E) | q ∈ insert Qlim (Set.range Qn)} := by
    apply isTightMeasureSet_of_isCompact_closure
    simpa only [hc.isClosed.closure_eq] using hc
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htc ⊢
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := htc ε hε
  exact ⟨C, hC, fun q hq => by
    obtain ⟨n, rfl⟩ := hq
    apply hbound
    exact ⟨Qn n, Or.inr ⟨n, rfl⟩, by simp [Qn]⟩⟩

/-- Uniform stochastic boundedness in the real-probability form used by the screening argument. Given [the stated hypotheses](hyp:hX), [the stated conclusion follows](goal). -/
theorem WeakConverges.eventually_norm_le
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [ProperSpace E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Measure E} [IsProbabilityMeasure Q]
    {Xn : ℕ → Ω → E} (hX : ∀ n, Measurable (Xn n))
    (h : WeakConverges Xn Q μ) :
    ∀ ε > 0, ∃ R : ℝ, ∀ n, μ.real {ω | R < ‖Xn n ω‖} ≤ ε := by
  intro ε hε
  have ht := h.isTightMeasureSet_range_map hX
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at ht
  obtain ⟨C, hC, hbound⟩ := ht (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
  obtain ⟨R, hCR⟩ := hC.isBounded.subset_closedBall (0 : E)
  refine ⟨R, fun n => ?_⟩
  have hset : {ω | R < ‖Xn n ω‖} ⊆ Xn n ⁻¹' Cᶜ := by
    intro ω hω hmem
    have := hCR hmem
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    exact (not_le_of_gt hω) this
  have hmeasC : MeasurableSet Cᶜ := hC.isClosed.measurableSet.compl
  have hμle : μ {ω | R < ‖Xn n ω‖} ≤ ENNReal.ofReal ε := by
    calc
      μ {ω | R < ‖Xn n ω‖} ≤ μ (Xn n ⁻¹' Cᶜ) := measure_mono hset
      _ = (μ.map (Xn n)) Cᶜ := (Measure.map_apply (hX n) hmeasC).symm
      _ ≤ ENNReal.ofReal ε := hbound _ ⟨n, rfl⟩
  unfold Measure.real
  calc
    (μ {ω | R < ‖Xn n ω‖}).toReal ≤ (ENNReal.ofReal ε).toReal :=
      ENNReal.toReal_mono (by simp) hμle
    _ = ε := ENNReal.toReal_ofReal hε.le

/-- Weak convergence is unchanged by a perturbation converging to zero in probability. Given [the stated hypotheses](hyp:hX,hY,hweak,hsub), [the stated conclusion follows](goal). -/
theorem WeakConverges.congr_of_tendstoInMeasure_sub
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Q : Measure E} [IsProbabilityMeasure Q]
    {X Y : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n)) (hweak : WeakConverges X Q μ)
    (hsub : TendstoInMeasure μ (Y - X) atTop 0) : WeakConverges Y Q μ := by
  let Qn : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (X n), Measure.isProbabilityMeasure_map (hX n).aemeasurable⟩
  let Qlim : ProbabilityMeasure E := ⟨Q, inferInstance⟩
  have ht : Tendsto Qn atTop (𝓝 Qlim) := hweak.tendsto_probabilityMeasure hX
  have hdistX : TendstoInDistribution X atTop (id : E → E) (fun _ => μ) Q := by
    refine ⟨fun n => (hX n).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Qn, Qlim, Measure.map_id, ProbabilityMeasure.coe_mk] using ht
  have hdistY := tendstoInDistribution_of_tendstoInMeasure_sub Y (id : E → E)
    hdistX hsub (fun n => (hY n).aemeasurable)
  intro f hf hfb
  let fb : BoundedContinuousFunction E ℝ :=
    { toFun := f
      continuous_toFun := hf
      map_bounded' := by
        obtain ⟨C, hC⟩ := hfb
        exact ⟨2 * C, fun x y => by
          rw [Real.dist_eq]
          calc
            |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
            _ ≤ C + C := add_le_add (hC x) (hC y)
            _ = 2 * C := by ring⟩ }
  let Rn : ℕ → ProbabilityMeasure E := fun n =>
    ⟨μ.map (Y n), Measure.isProbabilityMeasure_map (hY n).aemeasurable⟩
  let Rlim : ProbabilityMeasure E := ⟨Q, inferInstance⟩
  have ht' : Tendsto Rn atTop (𝓝 Rlim) := by
    simpa only [Rn, Rlim, Measure.map_id] using hdistY.tendsto
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at ht'
  have hf' := ht' fb
  simp only [Rn, Rlim, ProbabilityMeasure.coe_mk] at hf'
  convert hf' using 1
  · funext n
    symm
    change (∫ y, f y ∂μ.map (Y n)) = _
    rw [MeasureTheory.integral_map (hY n).aemeasurable hf.aestronglyMeasurable]
  · rfl

/-- Equality with probability tending to one makes the difference converge to zero in probability. Given [the stated hypotheses](hyp:hX,hY,heq), [the stated conclusion follows](goal). -/
theorem tendstoInMeasure_sub_of_probability_eq_one
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableEq E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X Y : ℕ → Ω → E} (hX : ∀ n, Measurable (X n))
    (hY : ∀ n, Measurable (Y n))
    (heq : Tendsto (fun n => μ.real {ω | X n ω = Y n ω}) atTop (𝓝 1)) :
    TendstoInMeasure μ (Y - X) atTop 0 := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hcomp : Tendsto (fun n => μ.real {ω | X n ω = Y n ω}ᶜ) atTop (𝓝 0) := by
    have hsub := (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub heq
    convert hsub using 1
    · funext n
      rw [measureReal_compl (measurableSet_eq_fun (hX n) (hY n))]
      simp
    · norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcomp
  · exact Filter.Eventually.of_forall fun n => measureReal_nonneg
  · exact Filter.Eventually.of_forall fun n => measureReal_mono fun ω hω hxy => by
      have hzero : (Y - X) n ω - (0 : Ω → E) ω = 0 := by
        simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]
        exact sub_eq_zero.mpr hxy.symm
      change ε ≤ ‖(Y - X) n ω - (0 : Ω → E) ω‖ at hω
      rw [hzero, norm_zero] at hω
      exact (not_le_of_gt hε) hω

end CausalSmith.PartialID.SlateBenefitPartialTransport
