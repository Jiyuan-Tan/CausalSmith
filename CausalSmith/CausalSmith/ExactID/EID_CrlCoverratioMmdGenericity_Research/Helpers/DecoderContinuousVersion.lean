module
public import CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity_Research.Helpers.DecoderCompProd
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Continuous equation-(11) conditional-CDF version

This file proves continuity of the equation-(11) fiber integral and packages the
ambient Markov kernel as the continuous conditional-CDF version selected by the decoder.
-/

@[expose] public section

open Causalean.Graph


open MeasureTheory ProbabilityTheory Set Filter

noncomputable section

namespace CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity

-- @node: continuous_equationElevenClampedScore
/-- The clamped equation-(11) score is jointly continuous in predecessor and target
coordinates.  Given [the stated inputs and conditions](hyp:hpos), [the stated conclusion](goal) follows. -/
lemma continuous_equationElevenClampedScore
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (order : Fin n → ℕ) (i : Fin n) : Continuous (equationElevenClampedScore W order i) := by
  have hw : Continuous (fun zw : PredecessorLatentCube order i × ℝ =>
      max 0 (min 1 zw.2)) := by fun_prop
  have hwmem : ∀ zw : PredecessorLatentCube order i × ℝ,
      max 0 (min 1 zw.2) ∈ Set.Icc (0 : ℝ) 1 := by
    intro zw
    exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  have hbase : Continuous (predecessorCubeLatentState W order i) := by
    apply continuous_pi
    intro a
    simp only [predecessorCubeLatentState]
    split <;> fun_prop
  have hv : Continuous (fun zw : PredecessorLatentCube order i × ℝ =>
      Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2))) := by
    apply continuous_pi
    intro k
    by_cases hki : k = W.targetPerm i
    · subst k
      simpa using hw
    · have heq : (fun a : PredecessorLatentCube order i × ℝ =>
          Function.update (predecessorCubeLatentState W order i a.1)
              (W.targetPerm i) (max 0 (min 1 a.2)) k) =
          fun a => predecessorCubeLatentState W order i a.1 k := by
        funext a
        simp [Function.update, hki]
      rw [heq]
      exact (continuous_apply k).comp (hbase.comp continuous_fst)
  have hvmem : ∀ zw : PredecessorLatentCube order i × ℝ,
      Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2)) ∈ latentCube n := by
    intro zw k hk
    by_cases hki : k = W.targetPerm i
    · subst k
      simpa using hwmem zw
    · simp [Function.update, hki]
      exact predecessorCubeLatentState_mem_latentCube W order i zw.1 k (Set.mem_univ k)
  have hq := (hpos.2.2.2.1 (W.targetPerm i)).continuousOn.comp_continuous hw hwmem
  have hp := (hpos.2.2.1 (W.targetPerm i)).continuousOn.comp_continuous hv hvmem
  have hpne : ∀ zw : PredecessorLatentCube order i × ℝ, θ.p (W.targetPerm i)
      (Function.update (predecessorCubeLatentState W order i zw.1)
        (W.targetPerm i) (max 0 (min 1 zw.2))) ≠ 0 := fun zw =>
    ne_of_gt (hpos.1 _ _ (hvmem zw))
  have hqne : ∀ zw : PredecessorLatentCube order i × ℝ,
      θ.q (W.targetPerm i) (max 0 (min 1 zw.2)) ≠ 0 := fun zw =>
    ne_of_gt (hpos.2.1 _ _ (hwmem zw))
  exact (hq.div hp hpne).log (fun zw => div_ne_zero (hqne zw) (hpne zw))

-- @node: equationElevenPredecessorCDF
/-- The equation-(11) fiber integral on the compact predecessor cube. -/
def equationElevenPredecessorCDF
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (z : ℝ × PredecessorLatentCube order i) : ℝ :=
  ∫ w in Set.Icc (0 : ℝ) 1,
    if equationElevenClampedScore W order i (z.2, w) ≤ z.1
    then θ.q (W.targetPerm i) w else 0

-- @node: continuous_equationElevenPredecessorCDF
/-- The equation-(11) fiber integral varies continuously with both its threshold and
predecessor coordinates.  Given [the stated inputs and conditions](hyp:hpos,hsign), [the stated conclusion](goal) follows. -/
lemma continuous_equationElevenPredecessorCDF
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hsign : FixedOwnDerivativeSign G s θ)
    (order : Fin n → ℕ) (i : Fin n) :
    Continuous (equationElevenPredecessorCDF W order i) := by
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : (ℝ × PredecessorLatentCube order i) → ℝ → ℝ := fun z w =>
    if equationElevenClampedScore W order i (z.2, w) ≤ z.1
    then θ.q (W.targetPerm i) w else 0
  have hqcont : ContinuousOn (θ.q (W.targetPerm i)) (Set.Icc (0 : ℝ) 1) :=
    (hpos.2.2.2.1 (W.targetPerm i)).continuousOn
  have hqint : Integrable (fun w => ‖θ.q (W.targetPerm i) w‖) μ := by
    exact (hqcont.norm.integrableOn_compact isCompact_Icc)
  rw [continuous_iff_continuousAt]
  intro z
  have hmono : StrictMonoOn
      (fun w => equationElevenClampedScore W order i (z.2, w))
      (Set.Icc (0 : ℝ) 1) ∨
      StrictAntiOn (fun w => equationElevenClampedScore W order i (z.2, w))
        (Set.Icc (0 : ℝ) 1) := by
    let v := predecessorCubeLatentState W order i z.2
    have hv : v ∈ latentCube n := predecessorCubeLatentState_mem_latentCube W order i z.2
    rcases s.signed (W.targetPerm i) with hneg | hposi
    · right
      have h := fixedOwnDerivativeSign_strictAntiOn s θ hpos hsign
        (W.targetPerm i) v hv hneg
      apply h.congr
      intro w hw
      simp only [equationElevenClampedScore]
      rw [min_eq_right hw.2, max_eq_right hw.1]
    · left
      have h := fixedOwnDerivativeSign_strictMonoOn s θ hpos hsign
        (W.targetPerm i) v hv hposi
      apply h.congr
      intro w hw
      simp only [equationElevenClampedScore]
      rw [min_eq_right hw.2, max_eq_right hw.1]
  have hlevel : Set.Subsingleton {w : ℝ | w ∈ Set.Icc (0 : ℝ) 1 ∧
      equationElevenClampedScore W order i (z.2, w) = z.1} := by
    intro a ha b hb
    rcases hmono with hm | hm
    · apply hm.injOn ha.1 hb.1
      calc
        equationElevenClampedScore W order i (z.2, a) = z.1 := ha.2
        _ = equationElevenClampedScore W order i (z.2, b) := hb.2.symm
    · apply hm.injOn ha.1 hb.1
      calc
        equationElevenClampedScore W order i (z.2, a) = z.1 := ha.2
        _ = equationElevenClampedScore W order i (z.2, b) := hb.2.symm
  have hne : ∀ᵐ w ∂μ,
      equationElevenClampedScore W order i (z.2, w) ≠ z.1 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc, MeasureTheory.ae_iff]
    have hset : {w | ¬(w ∈ Set.Icc (0 : ℝ) 1 →
        equationElevenClampedScore W order i (z.2, w) ≠ z.1)} =
        {w | w ∈ Set.Icc (0 : ℝ) 1 ∧
          equationElevenClampedScore W order i (z.2, w) = z.1} := by
      ext w
      by_cases hwmem : w ∈ Set.Icc (0 : ℝ) 1 <;>
        by_cases heq : equationElevenClampedScore W order i (z.2, w) = z.1 <;>
        simp [hwmem, heq]
    rw [hset]
    exact hlevel.measure_zero volume
  apply MeasureTheory.continuousAt_of_dominated
    (F := F) (bound := fun w => ‖θ.q (W.targetPerm i) w‖)
  · filter_upwards with z'
    have hscore : Measurable (fun w => equationElevenClampedScore W order i (z'.2, w)) :=
      (continuous_equationElevenClampedScore W hpos order i).measurable.comp
        (measurable_const.prodMk measurable_id)
    have hq : AEMeasurable (θ.q (W.targetPerm i)) μ :=
      hqcont.aemeasurable measurableSet_Icc
    let qm := hq.mk (θ.q (W.targetPerm i))
    have hm : Measurable (fun w =>
        if equationElevenClampedScore W order i (z'.2, w) ≤ z'.1
        then qm w else 0) :=
      Measurable.ite (measurableSet_le hscore measurable_const)
        hq.measurable_mk measurable_const
    apply hm.aestronglyMeasurable.congr
    filter_upwards [hq.ae_eq_mk] with w hw
    simp only [F, qm]
    rw [← hw]
  · filter_upwards with z'
    filter_upwards with w
    by_cases h : equationElevenClampedScore W order i (z'.2, w) ≤ z'.1
    · simp [F, h]
    · simp [F, h]
  · exact hqint
  · filter_upwards [hne] with w hw
    have hscore : ContinuousAt
        (fun z' : ℝ × PredecessorLatentCube order i =>
          equationElevenClampedScore W order i (z'.2, w)) z :=
      (continuous_equationElevenClampedScore W hpos order i).continuousAt.comp
        (continuousAt_snd.prodMk continuousAt_const)
    rcases lt_or_gt_of_ne hw with hlt | hgt
    · have hev := hscore.eventually_lt continuousAt_fst hlt
      have hc : ContinuousAt
          (fun _ : ℝ × PredecessorLatentCube order i => θ.q (W.targetPerm i) w) z :=
        continuousAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [hev] with z' hz'
      simp [F, hz'.le]
    · have hev := continuousAt_fst.eventually_lt hscore hgt
      have hc : ContinuousAt (fun _ : ℝ × PredecessorLatentCube order i => (0 : ℝ)) z :=
        continuousAt_const
      apply hc.congr_of_eventuallyEq
      filter_upwards [hev] with z' hz'
      simp [F, not_le_of_gt hz']

-- @node: equationElevenPredecessorCDF_eq
/-- The compact fiber CDF is the explicit equation-(11) integral.  [the stated conclusion](goal) follows. -/
lemma equationElevenPredecessorCDF_eq
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ) (order : Fin n → ℕ) (i : Fin n)
    (t : ℝ) (z : PredecessorLatentCube order i) :
    equationElevenPredecessorCDF W order i (t, z) =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t
        (predecessorCubeLatentState W order i z) := by
  unfold equationElevenPredecessorCDF equationElevenConditionalRatioCDF
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with w hw
  simp only [equationElevenClampedScore]
  have hclamp : max 0 (min 1 w) = w := by
    simp [min_eq_right hw.2, max_eq_right hw.1]
  simp [hclamp]

-- @node: equationElevenAmbientCDF
/-- The ambient equation-(11) Markov kernel evaluated on lower intervals, packaged as a
unit-interval-valued conditional CDF. -/
def equationElevenAmbientCDF
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n)
    (t : ℝ) (ell : PredecessorLogRatios order i) : Set.Icc (0 : ℝ) 1 := by
  let κ := equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i
  let y := (κ ell (Set.Iic t)).toReal
  have hle : κ ell (Set.Iic t) ≤ 1 := by
    calc
      κ ell (Set.Iic t) ≤ κ ell Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  exact ⟨y, ENNReal.toReal_nonneg, by
    have hy : κ ell (Set.Iic t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
    simpa [y] using (ENNReal.toReal_le_toReal hy ENNReal.one_ne_top).2 hle⟩

-- @node: measurable_equationElevenAmbientCDF
/-- The ambient equation-(11) conditional CDF is jointly measurable.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma measurable_equationElevenAmbientCDF
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    Measurable (fun z : ℝ × PredecessorLogRatios order i =>
      equationElevenAmbientCDF s W hpos hmix hone hsign horder hgraphOrder i z.1 z.2) := by
  apply Measurable.subtype_mk
  exact ENNReal.measurable_toReal.comp
    (measurable_kernel_Iic_uncurry
      (equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i))

-- @node: continuousOn_equationElevenAmbientCDF_scoreRange
/-- On the realized predecessor-score range, the ambient equation-(11) CDF is continuous.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma continuousOn_equationElevenAmbientCDF_scoreRange
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    ContinuousOn (fun z : ℝ × PredecessorLogRatios order i =>
      (equationElevenAmbientCDF s W hpos hmix hone hsign horder hgraphOrder i z.1 z.2 : ℝ))
      (Set.univ ×ˢ Set.range (predecessorScoreMap W order i)) := by
  classical
  let R := Set.range (predecessorScoreMap W order i)
  let r := predecessorScoreRangeRetraction W order i
  let e := predecessorScoreHomeomorph s W hpos hmix hone hsign horder hgraphOrder i
  have hr : ContinuousOn r R := by
    rw [continuousOn_iff_continuous_restrict]
    have hre : R.domRestrict r = id := by
      funext ell
      apply Subtype.ext
      simp [R, r, predecessorScoreRangeRetraction, ell.property]
    rw [hre]
    exact continuous_id
  let H : ℝ × PredecessorLogRatios order i →
      ℝ × PredecessorLatentCube order i := fun z => (z.1, e.symm (r z.2))
  have hH : ContinuousOn H (Set.univ ×ˢ R) := by
    apply ContinuousOn.prodMk continuousOn_fst
    apply e.symm.continuous.comp_continuousOn
    apply hr.comp continuousOn_snd
    intro z hz
    exact hz.2
  have hcont : ContinuousOn (equationElevenPredecessorCDF W order i ∘ H)
      (Set.univ ×ˢ R) :=
    (continuous_equationElevenPredecessorCDF s W hpos hsign order i).comp_continuousOn hH
  apply hcont.congr
  intro z hz
  have hzrange : z.2 ∈ Set.range (predecessorScoreMap W order i) := hz.2
  let ell : R := ⟨z.2, hzrange⟩
  have hretract : r z.2 = ell := by
    apply Subtype.ext
    change (predecessorScoreRangeRetraction W order i z.2).1 = z.2
    simp [predecessorScoreRangeRetraction, hzrange]
  have hinv : e.symm ell = e.symm (r z.2) := by rw [hretract]
  change (equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i
      z.2 (Set.Iic z.1)).toReal = equationElevenPredecessorCDF W order i (H z)
  rw [equationElevenAmbientKernel, Kernel.comap_apply,
    show predecessorScoreRangeRetraction W order i z.2 = ell from hretract,
    equationElevenScoreImageKernel, Kernel.comap_apply]
  change ((equationElevenPredecessorKernel W hpos order i)
      (e.symm ell) (Set.Iic z.1)).toReal = _
  rw [equationElevenPredecessorKernel_apply_Iic]
  rw [equationElevenPredecessorCDF_eq]
  exact equationElevenConditionalRatioCDF_eq_of_parents_eq θ (W.targetPerm i) z.1
    (fun _ _ => congrFun
      (congrArg (fun z0 => predecessorCubeLatentState W order i z0) hinv) _)

-- @node: observedConditionalRatioSupport_subset_scoreRange
/-- The observed joint ratio/predecessor support has predecessor component in the compact
triangular score range.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma observedConditionalRatioSupport_subset_scoreRange
    {n : ℕ} {G : DAG (Fin n)} {θ : Mechanism n G}
    (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    observedConditionalRatioSupport W.law order i ⊆
      Set.univ ×ˢ Set.range (predecessorScoreMap W order i) := by
  let μ := interventionalLaw θ (W.targetPerm i)
  let pred := familyProjection (observedLawLogRatio W.law) (predecessorSet order i)
  let R := Set.range (predecessorScoreMap W order i)
  have hclosedRange : IsClosed (Set.range (predecessorScoreMap W order i)) := by
    simpa only [Set.image_univ] using
      (isCompact_univ.image (continuous_predecessorScoreMap W hpos order i)).isClosed
  have hcube : ∀ᵐ v ∂μ, v ∈ latentCube n := by
    filter_upwards [Measure.support_mem_ae (μ := μ)] with v hv
    simpa [μ, interventionalLaw_support_eq_latentCube W hpos i] using hv
  have hmixAE : AEMeasurable W.mix μ := by
    apply Causalean.Mathlib.MeasureTheory.aemeasurable_of_supportMeasurableOn (by
      rw [latentCube]
      exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
      hcube hmix.1.continuousOn.domRestrict.measurable
  have hpred : Measurable pred := by
    dsimp only [pred]
    apply measurable_pi_lambda
    intro j
    exact measurable_observedLawLogRatio W.law j
  have hcomp : AEMeasurable (pred ∘ W.mix) μ :=
    hpred.aemeasurable.comp_aemeasurable hmixAE
  have hRae : R ∈ ae (Measure.map (pred ∘ W.mix) μ) := by
    refine (MeasureTheory.ae_map_iff hcomp (p := fun y => y ∈ R)
      hclosedRange.measurableSet).2 ?_
    filter_upwards [hcube] with v hv
    exact observedPredecessorLogRatio_mem_scoreRange
      W hpos hmix hone horder hgraphOrder i v hv
  have hsupp : Measure.support (Measure.map pred (W.law i.succ)) ⊆ R := by
    apply Measure.support_subset_of_isClosed hclosedRange
    rw [hone.2.1 i]
    rw [AEMeasurable.map_map_of_aemeasurable hpred.aemeasurable hmixAE]
    exact hRae
  rw [observedConditionalRatioSupport]
  intro z hz
  exact ⟨Set.mem_univ _, hsupp hz.2⟩

-- @node: rawObservedConditionalRatioCDF_joint_ae_eq_kernel_of_compProd
/-- Conditional-kernel uniqueness holds jointly under the observed threshold/predecessor law,
not merely separately at each fixed threshold.  Given [the stated inputs and conditions](hyp:hjoint), [the stated conclusion](goal) follows. -/
lemma rawObservedConditionalRatioCDF_joint_ae_eq_kernel_of_compProd
    {n : ℕ}
    (laws : ObservedProbabilityLawFamily n) (order : Fin n → ℕ) (i : Fin n)
    (κ : Kernel (PredecessorLogRatios order i) ℝ) [IsFiniteKernel κ]
    (hjoint : Measure.map
      (fun x ↦
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i) x,
          observedLawLogRatio laws.1 i x)) (laws.1 i.succ) =
      Measure.map
          (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
          (laws.1 i.succ) ⊗ₘ κ) :
    (fun z : ℝ × PredecessorLogRatios order i => (κ z.2 (Set.Iic z.1)).toReal) =ᵐ[
      Measure.map (conditionalRatioArgument laws.1 order i) (laws.1 i.succ)]
      (fun z => rawObservedConditionalRatioCDF laws order i z.1 z.2) := by
  letI : IsProbabilityMeasure (laws.1 i.succ) := laws.2 i.succ
  let pred := familyProjection (observedLawLogRatio laws.1) (predecessorSet order i)
  let score := observedLawLogRatio laws.1 i
  let predLaw := Measure.map pred (laws.1 i.succ)
  have hcond := ProbabilityTheory.condDistrib_ae_eq_of_measure_eq_compProd
    pred (measurable_observedLawLogRatio laws.1 i).aemeasurable hjoint
  have hall : ∀ᵐ ell ∂predLaw, ∀ t,
      (κ ell (Set.Iic t)).toReal = rawObservedConditionalRatioCDF laws order i t ell := by
    filter_upwards [hcond] with ell hell
    intro t
    have hfinite : ∀ e, IsFiniteMeasure (laws.1 e) := by
      intro e
      letI : IsProbabilityMeasure (laws.1 e) := laws.2 e
      infer_instance
    rw [rawObservedConditionalRatioCDF, dif_pos hfinite, hell]
  let joint := Measure.map (conditionalRatioArgument laws.1 order i) (laws.1 i.succ)
  have hmap : Measure.map Prod.snd joint = predLaw := by
    dsimp only [joint, predLaw, pred]
    rw [Measure.map_map measurable_snd
      (measurable_conditionalRatioArgument laws.1 order i)]
    rfl
  rw [← hmap] at hall
  have hpull := MeasureTheory.mem_ae_of_mem_ae_map measurable_snd.aemeasurable hall
  filter_upwards [hpull] with z hz
  exact hz z.1

-- @node: equationElevenAmbientCDF_isContinuousVersion
/-- The ambient equation-(11) CDF is a continuous conditional-distribution version for the
observed intervention law.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder), [the stated conclusion](goal) follows. -/
lemma equationElevenAmbientCDF_isContinuousVersion
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order) (i : Fin n) :
    IsContinuousConditionalRatioCDFVersion (observedProbabilityLawFamily W.law) order i
      (equationElevenAmbientCDF s W hpos hmix hone hsign horder hgraphOrder i) := by
  let laws := observedProbabilityLawFamily W.law
  let κ := equationElevenAmbientKernel s W hpos hmix hone hsign horder hgraphOrder i
  have hprob : ∀ e, IsProbabilityMeasure (W.law e) :=
    observedWorld_laws_isProbabilityMeasure W hpos hmix hone
  have hlaws : laws.1 = W.law := by
    simp [laws, observedProbabilityLawFamily, hprob]
  have hjoint := observedRatioPredecessor_compProd
    s W hpos hmix hone hsign horder hgraphOrder i
  have hjoint' : Measure.map
      (fun x ↦
        (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i) x,
          observedLawLogRatio laws.1 i x)) (laws.1 i.succ) =
      Measure.map
          (familyProjection (observedLawLogRatio laws.1) (predecessorSet order i))
          (laws.1 i.succ) ⊗ₘ κ := by
    simpa only [hlaws] using hjoint
  have hfixed := rawObservedConditionalRatioCDF_ae_eq_kernel_of_compProd
    laws order i κ hjoint'
  have hjointAE := rawObservedConditionalRatioCDF_joint_ae_eq_kernel_of_compProd
    laws order i κ hjoint'
  have hsupp : observedConditionalRatioSupport laws.1 order i ⊆
      Set.univ ×ˢ Set.range (predecessorScoreMap W order i) := by
    rw [hlaws]
    exact observedConditionalRatioSupport_subset_scoreRange
      W hpos hmix hone horder hgraphOrder i
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact measurable_subtype_coe.comp
      (measurable_equationElevenAmbientCDF
        s W hpos hmix hone hsign horder hgraphOrder i)
  · intro t
    simpa [κ, equationElevenAmbientCDF] using (hfixed t).symm
  · simpa [κ, equationElevenAmbientCDF] using hjointAE
  · exact (continuousOn_equationElevenAmbientCDF_scoreRange
      s W hpos hmix hone hsign horder hgraphOrder i).mono
        hsupp

-- @node: equationElevenAmbientCDF_apply_of_latentState
/-- On every realized predecessor score, the continuous version evaluates to the explicit
equation-(11) integral.  Given [the stated inputs and conditions](hyp:hpos,hmix,hone,hsign,horder,hgraphOrder,hv), [the stated conclusion](goal) follows. -/
lemma equationElevenAmbientCDF_apply_of_latentState
    {n : ℕ} {G : DAG (Fin n)} (s : SignVector n)
    {θ : Mechanism n G} (W : ObservedWorld G θ)
    (hpos : PositiveNormalizedSmoothMechanisms G θ)
    (hmix : SharedDiffeomorphicMixing G θ W)
    (hone : OnePerfectInterventionPerNode G θ W)
    (hsign : FixedOwnDerivativeSign G s θ)
    {order : Fin n → ℕ}
    (horder : IsTopologicalOrdering (observedLawRatioGraph gaussianFeatureMap W.law) order)
    (hgraphOrder : PermutedGraphOrdered W order)
    (i : Fin n) (t : ℝ) (v : LatentState n) (hv : v ∈ latentCube n) :
    (equationElevenAmbientCDF s W hpos hmix hone hsign horder hgraphOrder i t
      (familyProjection (observedLawLogRatio W.law) (predecessorSet order i) (W.mix v)) : ℝ) =
      equationElevenConditionalRatioCDF θ (W.targetPerm i) t v := by
  exact equationElevenAmbientKernel_apply_Iic_of_latentState
    s W hpos hmix hone hsign horder hgraphOrder i v hv t

end CausalSmith.ExactID.EID_CrlCoverratioMmdGenericity
