import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.Inference
import Causalean.Stat.Concentration.TailBounds.McDiarmid
import FoML.McDiarmid
import Causalean.Mathlib.Indep
import Causalean.Estimation.OrthogonalLearning.LocalEmpProcess.RandomParam
import Causalean.Stat.Concentration.HilbertEmpiricalMean
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Integration

/-!
# Uniform Hilbert-valued empirical-mean deviation

The statement is made against the local unit-norm feature-map interface and is
designed for the reused scalar McDiarmid concentration engine.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

/-- A training-measurable localization of the random-parameter product-law bound. -/
-- @node: randomParam_event_inter_le
lemma randomParam_event_inter_le
    {Ω β : Type*} [mΩ : MeasurableSpace Ω] [mβ : MeasurableSpace β]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → β} (hY : @Measurable Ω β mΩ mβ Y)
    {ν : Measure β} [IsProbabilityMeasure ν] (hY_law : μ.map Y = ν)
    (mA : MeasurableSpace Ω) (hmA : mA ≤ mΩ)
    (hindep : @Indep Ω mA (MeasurableSpace.comap Y mβ) mΩ μ)
    {δ : ℝ} (Bad : Ω → Set β)
    (hBad : @MeasurableSet (Ω × β) (mA.prod mβ) {p | p.2 ∈ Bad p.1})
    (hsec : ∀ ω, ν (Bad ω) ≤ ENNReal.ofReal δ)
    (B : Set Ω) (hB : @MeasurableSet Ω mA B) :
    μ ({ω | Y ω ∈ Bad ω} ∩ B) ≤ ENNReal.ofReal δ * μ B := by
  have hJ : @Measurable Ω (Ω × β) mΩ (mA.prod mβ) (fun ω => (ω, Y ω)) :=
    (measurable_id'' hmA).prod hY
  have hfst : @Measurable (Ω × β) Ω (mA.prod mβ) mA Prod.fst := measurable_fst
  have hset : @MeasurableSet (Ω × β) (mA.prod mβ)
      ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B) :=
    hBad.inter (hB.preimage hfst)
  have hYa : @AEMeasurable Ω β mβ mΩ Y μ := hY.aemeasurable
  have hmap := @Causalean.Mathlib.indep_trim_prod_map_eq Ω β mΩ mβ μ _
    mA hmA Y hYa hindep
  have heq : {ω | Y ω ∈ Bad ω} ∩ B =
      (fun ω => (ω, Y ω)) ⁻¹' ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B) := by
    ext ω
    simp
  rw [heq, ← Measure.map_apply hJ hset, hmap, hY_law, Measure.prod_apply hset]
  calc
    (∫⁻ ω, ν (Prod.mk ω ⁻¹' ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B))
        ∂μ.trim hmA)
        ≤ ∫⁻ ω, B.indicator (fun _ => ENNReal.ofReal δ) ω ∂μ.trim hmA := by
          apply lintegral_mono
          intro ω
          change ν (Prod.mk ω ⁻¹'
            ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B)) ≤
              B.indicator (fun _ => ENNReal.ofReal δ) ω
          by_cases hω : ω ∈ B
          · have he : Prod.mk ω ⁻¹'
                ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B) = Bad ω := by
              ext x
              simp [hω]
            rw [he]
            simpa [hω] using hsec ω
          · have he : Prod.mk ω ⁻¹'
                ({p | p.2 ∈ Bad p.1} ∩ Prod.fst ⁻¹' B) = ∅ := by
              ext x
              simp [hω]
            simp [he, hω]
    _ = ENNReal.ofReal δ * μ B := by
      rw [lintegral_indicator hB, lintegral_const,
        Measure.restrict_apply_univ, trim_measurableSet_eq hmA hB]

private lemma unitNormFeatureMap_dist_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : UnitNormFeatureMap H) (a b : ℝ) :
    ‖U.Φ a - U.Φ b‖ ^ 2 = 2 - 2 * gaussianKernel a b := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, U.inner_eq_kernel]
  simp only [gaussianKernel, sub_self]
  ring_nf
  simp

/-- Every realization of the Gaussian kernel is `sqrt 2`-Lipschitz. -/
-- @node: unitNormFeatureMap_dist_le
lemma unitNormFeatureMap_dist_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : UnitNormFeatureMap H) (a b : ℝ) :
    ‖U.Φ a - U.Φ b‖ ≤ Real.sqrt 2 * |a - b| := by
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hexp := Real.one_sub_le_exp_neg ((a - b) ^ 2)
  have hsq : ‖U.Φ a - U.Φ b‖ ^ 2 ≤ 2 * (a - b) ^ 2 := by
    rw [unitNormFeatureMap_dist_sq U]
    unfold gaussianKernel
    nlinarith
  have habs : 0 ≤ |a - b| := abs_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hsqrt habs)).mp
  calc
    ‖U.Φ a - U.Φ b‖ ^ 2 ≤ 2 * (a - b) ^ 2 := hsq
    _ = (Real.sqrt 2 * |a - b|) ^ 2 := by
      rw [mul_pow, hsqrt_sq, sq_abs]

private lemma unitNormFeatureMap_continuous
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : UnitNormFeatureMap H) :
    Continuous U.Φ := by
  rw [continuous_iff_continuousAt]
  intro a
  change Tendsto U.Φ (𝓝 a) (𝓝 (U.Φ a))
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hcont : Tendsto (fun b : ℝ => ‖U.Φ b - U.Φ a‖ ^ 2) (𝓝 a) (𝓝 0) := by
    have h : ContinuousAt (fun b : ℝ => 2 - 2 * gaussianKernel b a) a := by
      unfold gaussianKernel
      fun_prop
    have heq : (fun b : ℝ => ‖U.Φ b - U.Φ a‖ ^ 2) =
        fun b => 2 - 2 * gaussianKernel b a := by
      funext b
      exact unitNormFeatureMap_dist_sq U b a
    rw [heq]
    change Tendsto (fun b : ℝ => 2 - 2 * gaussianKernel b a) (𝓝 a)
      (𝓝 ((fun b : ℝ => 2 - 2 * gaussianKernel b a) a)) at h
    simpa [gaussianKernel] using h
  have hev : ∀ᶠ b in 𝓝 a, ‖U.Φ b - U.Φ a‖ ^ 2 < ε ^ 2 :=
    (tendsto_order.1 hcont).2 _ (sq_pos_of_pos hε)
  filter_upwards [hev] with b hb
  rw [dist_eq_norm]
  have hnonneg := norm_nonneg (U.Φ b - U.Φ a)
  nlinarith

private lemma unitNormFeatureMap_stronglyMeasurable
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : UnitNormFeatureMap H) :
    StronglyMeasurable U.Φ :=
  (unitNormFeatureMap_continuous U).stronglyMeasurable

/-- Gaussian mean embeddings are controlled by `sqrt 2` times the input `L¹` distance. -/
-- @node: meanEmbedding_map_sub_le_l1
lemma meanEmbedding_map_sub_le_l1
    {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (U : UnitNormFeatureMap H) (μ : Measure X) [IsProbabilityMeasure μ]
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfg : Integrable (fun x => |f x - g x|) μ) :
    ‖meanEmbedding U (Measure.map f μ) - meanEmbedding U (Measure.map g μ)‖ ≤
      Real.sqrt 2 * ∫ x, |f x - g x| ∂μ := by
  have hΦf : Integrable (fun x => U.Φ (f x)) μ :=
    Integrable.of_bound
      ((unitNormFeatureMap_stronglyMeasurable U).comp_measurable hf).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun x => by rw [U.norm_eq_one])
  have hΦg : Integrable (fun x => U.Φ (g x)) μ :=
    Integrable.of_bound
      ((unitNormFeatureMap_stronglyMeasurable U).comp_measurable hg).aestronglyMeasurable
      1 (Filter.Eventually.of_forall fun x => by rw [U.norm_eq_one])
  unfold meanEmbedding
  rw [integral_map hf.aemeasurable
      (unitNormFeatureMap_stronglyMeasurable U).aestronglyMeasurable,
    integral_map hg.aemeasurable
      (unitNormFeatureMap_stronglyMeasurable U).aestronglyMeasurable,
    ← integral_sub hΦf hΦg]
  calc
    ‖∫ x, U.Φ (f x) - U.Φ (g x) ∂μ‖
        ≤ ∫ x, ‖U.Φ (f x) - U.Φ (g x)‖ ∂μ :=
          norm_integral_le_integral_norm _
    _ ≤ ∫ x, Real.sqrt 2 * |f x - g x| ∂μ := by
      exact integral_mono_ae (hΦf.sub hΦg).norm (hfg.const_mul _)
        (Filter.Eventually.of_forall fun x => unitNormFeatureMap_dist_le U (f x) (g x))
    _ = Real.sqrt 2 * ∫ x, |f x - g x| ∂μ := integral_const_mul _ _

/-- Conditional population embedding of the fitted ratio under environment `e`. -/
def fittedMeanEmbedding
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    {W : ObservedWorld G θ} {Ω H : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : SampleSplitWorld W Ω) (U : UnitNormFeatureMap H)
    (e : Fin (n + 1)) (i : Fin n) (ω : Ω) : H :=
  meanEmbedding U (Measure.map (S.ratioEstimate ω i) (W.law e))

set_option maxHeartbeats 2000000 in
-- @node: lem:bounded-rkhs-empirical-mean
/-- Conditional on training, all environment/ratio empirical feature means obey the stated
unit-norm Hilbert-space deviation bound with probability at least `1-α`. -/
lemma bounded_rkhs_empirical_mean
    {n : ℕ} {G : Causalean.DAG (Fin n)} {θ : Mechanism n G}
    {W : ObservedWorld G θ} {Ω H : Type*} [mΩ : MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]
    (S : SampleSplitWorld W Ω) (U : UnitNormFeatureMap H)
    (hSampling : ConditionalEvaluationSampling S)
    (hn : 1 ≤ n) (hN : ∀ e, 1 ≤ S.sampleSize e)
    (hα : S.alpha ∈ Set.Ioo (0 : ℝ) 1) :
    ConditionalProbabilityAtLeast S.probability
      (MeasurableSpace.comap (trainingFold S) inferInstance)
      {ω | ∀ i : Fin n, ∀ e : Fin (n + 1),
        ‖empiricalMeanEmbedding S U e i ω - fittedMeanEmbedding S U e i ω‖ ≤
          (1 + Real.sqrt (2 * Real.log
            ((n : ℝ) * (n + 1 : ℝ) / S.alpha))) /
            Real.sqrt (minimumSampleSize S)} Set.univ (1 - S.alpha) := by
  classical
  rcases hSampling with
    ⟨hprob, hlaw, htrain, hevalMeas, hevalIndep, hevalLaw, hsplit, hratioJoint⟩
  letI : IsProbabilityMeasure S.probability := hprob
  have hmA : trainingSigma S ≤ mΩ := htrain.comap_le
  have hmin (e : Fin (n + 1)) : minimumSampleSize S ≤ S.sampleSize e :=
    Finset.inf'_le S.sampleSize (Finset.mem_univ e)
  have hmin_pos : 0 < minimumSampleSize S := by
    rw [minimumSampleSize]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one
      (Finset.le_inf' ⟨0, Finset.mem_univ 0⟩ S.sampleSize (fun e _ => hN e))
  let δ : ℝ := S.alpha / ((n : ℝ) * (n + 1 : ℝ))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hK : 1 ≤ (n : ℝ) * (n + 1 : ℝ) := by
    calc
      (1 : ℝ) = 1 * 1 := by ring
      _ ≤ (n : ℝ) * (n + 1 : ℝ) :=
        mul_le_mul hn1 (by linarith) (by norm_num) hnR.le
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact div_pos hα.1 (mul_pos hnR (by linarith))
  have hδone : δ < 1 := by
    dsimp [δ]
    exact (div_le_self hα.1.le hK).trans_lt hα.2
  have hradius (e : Fin (n + 1)) :
      1 / Real.sqrt (S.sampleSize e) +
          Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e) ≤
        (1 + Real.sqrt (2 * Real.log
          ((n : ℝ) * (n + 1 : ℝ) / S.alpha))) /
          Real.sqrt (minimumSampleSize S) := by
    have hm0 : 0 < (S.sampleSize e : ℝ) := by exact_mod_cast hN e
    have hmin0 : 0 < (minimumSampleSize S : ℝ) := by exact_mod_cast hmin_pos
    have hle : Real.sqrt (minimumSampleSize S) ≤ Real.sqrt (S.sampleSize e) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hmin e)
    have hlogarg : 1 / δ = (n : ℝ) * (n + 1 : ℝ) / S.alpha := by
      dsimp [δ]
      field_simp
    have hratio_one : 1 ≤ (n : ℝ) * (n + 1 : ℝ) / S.alpha := by
      apply (le_div_iff₀ hα.1).2
      simpa only [one_mul] using hα.2.le.trans hK
    have hlog_nonneg : 0 ≤ 2 * Real.log
        ((n : ℝ) * (n + 1 : ℝ) / S.alpha) := by
      exact mul_nonneg (by norm_num) (Real.log_nonneg hratio_one)
    rw [hlogarg, Real.sqrt_div hlog_nonneg]
    have hnum : 0 ≤ 1 + Real.sqrt
        (2 * Real.log ((n : ℝ) * (n + 1 : ℝ) / S.alpha)) := by positivity
    rw [← add_div]
    exact div_le_div_of_nonneg_left hnum (Real.sqrt_pos.2 hmin0) hle
  intro B hB
  have hBfull : @MeasurableSet Ω mΩ B := hmA B hB
  have hpair (i : Fin n) (e : Fin (n + 1)) :
      MeasurableSet
          {ω | (1 / Real.sqrt (S.sampleSize e) +
              Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e)) <
            ‖empiricalMeanEmbedding S U e i ω - fittedMeanEmbedding S U e i ω‖} ∧
      S.probability
          ({ω | (1 / Real.sqrt (S.sampleSize e) +
              Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e)) <
            ‖empiricalMeanEmbedding S U e i ω - fittedMeanEmbedding S U e i ω‖} ∩ B)
        ≤ ENNReal.ofReal δ * S.probability B := by
    let Y : Ω → (Fin (S.sampleSize e) → LatentState n) :=
      fun ω r => S.evaluation e r ω
    have hY : Measurable Y := by
      apply measurable_pi_lambda
      intro r
      exact hevalMeas e r
    let ν : Measure (Fin (S.sampleSize e) → LatentState n) :=
      Measure.pi (fun _ => W.law e)
    letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    have hYlaw : S.probability.map Y = ν := by
      have hp := (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
        (fun r => (hevalMeas e r).aemeasurable)).mp (hevalIndep e)
      calc
        S.probability.map Y = Measure.pi
            (fun r => S.probability.map (S.evaluation e r)) := hp
        _ = ν := by
          congr 1
          funext r
          exact hevalLaw e r
    have hindepY : @Indep Ω (trainingSigma S) (MeasurableSpace.comap Y inferInstance)
        mΩ S.probability := by
      change IndepFun (trainingFold S) Y S.probability
      have he : Measurable (fun z : (∀ e, Fin (S.sampleSize e) → LatentState n) => z e) :=
        measurable_pi_apply e
      convert hsplit.comp measurable_id he using 1 <;> rfl
    let f : Ω → LatentState n → H := fun ω x =>
      U.Φ (@SampleSplitWorld.ratioEstimate n G θ W Ω mΩ S ω i x)
    have hf_joint : @StronglyMeasurable (Ω × LatentState n) H
        inferInstance ((trainingSigma S).prod inferInstance) (Function.uncurry f) := by
      apply (unitNormFeatureMap_stronglyMeasurable U).comp_measurable
      exact hratioJoint i
    have hf_int : @StronglyMeasurable Ω H inferInstance (trainingSigma S)
        (fun ω => ∫ x, f ω x ∂W.law e) :=
      @MeasureTheory.StronglyMeasurable.integral_prod_right Ω (LatentState n) H
        (trainingSigma S) inferInstance (W.law e) inferInstance inferInstance
        inferInstance f hf_joint
    have hf_eval (r : Fin (S.sampleSize e)) : @StronglyMeasurable
        (Ω × (Fin (S.sampleSize e) → LatentState n)) H
        inferInstance ((trainingSigma S).prod inferInstance)
        (fun p => f p.1 (p.2 r)) := by
      exact hf_joint.comp_measurable (Measurable.prodMk measurable_fst
        ((measurable_pi_apply r).comp measurable_snd))
    let Bad : Ω → Set (Fin (S.sampleSize e) → LatentState n) := fun ω =>
      {z | 1 / Real.sqrt (S.sampleSize e) +
          Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e) <
        ‖(S.sampleSize e : ℝ)⁻¹ • ∑ r, f ω (z r) - ∫ x, f ω x ∂W.law e‖}
    have hBad : @MeasurableSet
        (Ω × (Fin (S.sampleSize e) → LatentState n))
        ((trainingSigma S).prod inferInstance)
        {p | p.2 ∈ Bad p.1} := by
      change @MeasurableSet
        (Ω × (Fin (S.sampleSize e) → LatentState n))
        ((trainingSigma S).prod inferInstance)
        {(p : Ω × (Fin (S.sampleSize e) → LatentState n)) |
        (1 / Real.sqrt (S.sampleSize e) +
          Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e)) <
        ‖(S.sampleSize e : ℝ)⁻¹ • ∑ r, f p.1 (p.2 r) -
          ∫ x, f p.1 x ∂W.law e‖}
      apply measurableSet_lt measurable_const
      apply StronglyMeasurable.measurable
      apply StronglyMeasurable.norm
      apply StronglyMeasurable.sub
      · apply StronglyMeasurable.const_smul
        rw [← Finset.sum_fn]
        exact Finset.stronglyMeasurable_sum _ (fun r _ => hf_eval r)
      · exact hf_int.comp_measurable measurable_fst
    have hsec (ω : Ω) : ν (Bad ω) ≤ ENNReal.ofReal δ := by
      have ht := Causalean.Stat.Concentration.HilbertEmpiricalMean.centeredEmpiricalMean_norm_tail_le
        (W.law e) (f ω) ((unitNormFeatureMap_stronglyMeasurable U).comp_measurable
          (S.ratioFit_measurable (trainingFold S ω) i))
        (fun x => by rw [U.norm_eq_one]) (hN e) hδpos hδone
      have hne : ν (Bad ω) ≠ ⊤ := measure_ne_top _ _
      rw [← ENNReal.ofReal_toReal hne]
      exact ENNReal.ofReal_le_ofReal (by simpa [ν, Bad, f] using ht)
    have hJ : @Measurable Ω
        (Ω × (Fin (S.sampleSize e) → LatentState n)) mΩ
        ((trainingSigma S).prod inferInstance) (fun ω => (ω, Y ω)) :=
      (measurable_id'' hmA).prod hY
    have hevent : MeasurableSet {ω | Y ω ∈ Bad ω} := by
      change MeasurableSet ((fun ω => (ω, Y ω)) ⁻¹' {p | p.2 ∈ Bad p.1})
      exact hBad.preimage hJ
    have hraw := randomParam_event_inter_le hY hYlaw (trainingSigma S) hmA
      hindepY Bad hBad hsec B hB
    have heq : {ω | Y ω ∈ Bad ω} =
        {ω | (1 / Real.sqrt (S.sampleSize e) +
              Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize e)) <
            ‖empiricalMeanEmbedding S U e i ω - fittedMeanEmbedding S U e i ω‖} := by
      ext ω
      simp only [Y, Bad, f, Set.mem_setOf_eq]
      unfold empiricalMeanEmbedding fittedMeanEmbedding meanEmbedding
      have hint : (∫ r, U.Φ r ∂Measure.map (S.ratioEstimate ω i) (W.law e)) =
          ∫ x, U.Φ (S.ratioEstimate ω i x) ∂W.law e :=
        integral_map
          (S.ratioFit_measurable (trainingFold S ω) i).aemeasurable
          (unitNormFeatureMap_stronglyMeasurable U).aestronglyMeasurable
      rw [hint]
    rw [heq] at hevent hraw
    exact ⟨hevent, hraw⟩
  let BadPair : Fin n × Fin (n + 1) → Set Ω := fun ie =>
    {ω | (1 / Real.sqrt (S.sampleSize ie.2) +
        Real.sqrt (2 * Real.log (1 / δ) / S.sampleSize ie.2)) <
      ‖empiricalMeanEmbedding S U ie.2 ie.1 ω -
        fittedMeanEmbedding S U ie.2 ie.1 ω‖}
  let BadAll : Set Ω := ⋃ ie, BadPair ie
  have hBadAllMeas : MeasurableSet BadAll := by
    dsimp only [BadAll]
    exact MeasurableSet.iUnion fun ie => (hpair ie.1 ie.2).1
  have hUnion : S.probability (BadAll ∩ B) ≤
      ENNReal.ofReal S.alpha * S.probability B := by
    calc
      S.probability (BadAll ∩ B)
          = S.probability (⋃ ie, BadPair ie ∩ B) := by
              congr 1
              dsimp only [BadAll]
              ext ω
              simp
      _ ≤ ∑ ie : Fin n × Fin (n + 1), S.probability (BadPair ie ∩ B) :=
        measure_iUnion_fintype_le _ _
      _ ≤ ∑ _ie : Fin n × Fin (n + 1),
          (ENNReal.ofReal δ * S.probability B) := by
            gcongr with ie
            exact (hpair ie.1 ie.2).2
      _ = ENNReal.ofReal S.alpha * S.probability B := by
        simp only [Finset.sum_const, Fintype.card_prod, Fintype.card_fin,
          nsmul_eq_mul]
        have hcoeff : ((Finset.univ : Finset (Fin n × Fin (n + 1))).card : ENNReal) *
            ENNReal.ofReal δ = ENNReal.ofReal S.alpha := by
          rw [← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity : 0 ≤
              ((Finset.univ : Finset (Fin n × Fin (n + 1))).card : ℝ))]
          congr 1
          simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          dsimp [δ]
          field_simp
        calc
          ((Finset.univ : Finset (Fin n × Fin (n + 1))).card : ENNReal) *
              (ENNReal.ofReal δ * S.probability B) =
              (((Finset.univ : Finset (Fin n × Fin (n + 1))).card : ENNReal) *
                ENNReal.ofReal δ) *
                S.probability B := (mul_assoc _ _ _).symm
          _ = _ := by rw [hcoeff]
  let Good : Set Ω :=
      {ω | ∀ i : Fin n, ∀ e : Fin (n + 1),
        ‖empiricalMeanEmbedding S U e i ω - fittedMeanEmbedding S U e i ω‖ ≤
          (1 + Real.sqrt (2 * Real.log
            ((n : ℝ) * (n + 1 : ℝ) / S.alpha))) /
            Real.sqrt (minimumSampleSize S)}
  have hgood : B \ BadAll ⊆ Good ∩ Set.univ ∩ B := by
    intro ω hω
    dsimp only [BadAll] at hω
    simp only [Set.mem_diff, Set.mem_iUnion, not_exists, BadPair, Set.mem_setOf_eq,
      Set.mem_inter_iff, Set.mem_univ, true_and] at hω ⊢
    refine ⟨⟨?_, trivial⟩, hω.1⟩
    intro i e
    exact (not_lt.mp (hω.2 (i, e))).trans (hradius e)
  have hBfinite : S.probability B ≠ ⊤ := measure_ne_top _ _
  have hbadfinite : S.probability (BadAll ∩ B) ≠ ⊤ := measure_ne_top _ _
  have hmeasure : S.probability B - S.probability (BadAll ∩ B) ≤
      S.probability (Good ∩ Set.univ ∩ B) := by
    rw [← measure_diff Set.inter_subset_right
      ((hBadAllMeas.inter hBfull).nullMeasurableSet)
      hbadfinite]
    apply measure_mono
    intro ω hω
    refine hgood ⟨hω.1, ?_⟩
    exact fun hbad => hω.2 ⟨hbad, hω.1⟩
  have hbadB : S.probability (BadAll ∩ B) ≤ S.probability B :=
    measure_mono (Set.inter_subset_right)
  have hUnionReal :
      (S.probability (BadAll ∩ B)).toReal ≤
        S.alpha * (S.probability B).toReal := by
    rw [← ENNReal.toReal_ofReal hα.1.le, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hBfinite) hUnion
  have hmeasureReal :
          (S.probability B).toReal -
          (S.probability (BadAll ∩ B)).toReal ≤
        (S.probability (Good ∩ Set.univ ∩ B)).toReal := by
    rw [← ENNReal.toReal_sub_of_le hbadB hBfinite]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hmeasure
  change (1 - S.alpha) * (S.probability.real (Set.univ ∩ B)) ≤
    S.probability.real (Good ∩ Set.univ ∩ B)
  simp only [Set.univ_inter, Measure.real]
  linarith

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
