import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.StudentizedWitness
import CausalSmith.SCM.SCM_ProxyTargetspanTransport_Research.Helpers.FiniteSampleCoverage

/-! Local deterministic control of the rank-one Wald rule at the explicit baseline. -/

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open Finset Matrix MeasureTheory

namespace CausalSmith.SCM.ProxyTargetspanTransport

private abbrev BaselinePO := Fin 2 → Fin 2 → Fin 1 → Fin 2 → ℝ
private abbrev BaselineB := Fin 2 → ℝ
private abbrev BaselineHz := Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ)
private abbrev BaselineInput :=
  Causalean.Mathlib.Analysis.WaldInput (Fin 2)

private theorem continuousAt_finsetSum {ι X : Type*} [TopologicalSpace X]
    [DecidableEq ι]
    (s : Finset ι) (f : ι → X → ℝ) (x : X)
    (hf : ∀ i ∈ s, ContinuousAt (f i) x) :
    ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : X => (0 : ℝ)) x)
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self _ _)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private theorem continuousAt_quadForm_family {I X : Type*}
    [Fintype I] [DecidableEq I] [TopologicalSpace X]
    (v d : X → I → ℝ) (x : X)
    (hv : ∀ i, ContinuousAt (fun q => v q i) x)
    (hd : ∀ i, ContinuousAt (fun q => d q i) x) :
    ContinuousAt (fun q => quadForm (multinomialCov (v q)) (d q)) x := by
  unfold quadForm multinomialCov Matrix.mulVec dotProduct
  apply continuousAt_finsetSum
  intro i hi
  apply (hd i).mul
  apply continuousAt_finsetSum
  intro j hj
  apply ContinuousAt.mul
  · by_cases hij : i = j
    · subst j
      change ContinuousAt (fun y => (if i = i then v y i else 0) - v y i * v y i) x
      simp only [if_pos rfl]
      exact (hv i).sub ((hv i).mul (hv i))
    · change ContinuousAt (fun y => (if i = j then v y i else 0) - v y i * v y j) x
      simp only [if_neg hij]
      exact continuousAt_const.sub ((hv i).mul (hv j))
  · exact hd j

private noncomputable def baselineInput : BaselineInput :=
  (proxyMomentMatrix studentizedBaseline 0,
    outcomeMomentVector studentizedBaseline 0 1,
    targetProxyVector studentizedBaseline)

private noncomputable def empiricalInput (q : BaselinePO × BaselineB) : BaselineInput :=
  ((unconditionalBalancingMoments q.1 0 1).1,
    (unconditionalBalancingMoments q.1 0 1).2, q.2)

private theorem continuousAt_empiricalInput :
    ContinuousAt empiricalInput
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) := by
  unfold empiricalInput
  fun_prop

private theorem continuousAt_baseline_sourceDerivative :
    ContinuousAt
      (fun ξ : BaselineInput =>
        fderiv ℝ
          (fun hz : BaselineHz => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) hz.1 hz.2 ξ.2.2)
          (ξ.1, ξ.2.1))
      baselineInput := by
  let F : BaselineInput → ℝ := fun ξ => regularWaldFunctional
    (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) ξ.1 ξ.2.1 ξ.2.2
  have hF : ContDiffAt ℝ 1 F baselineInput := by
    apply contDiffAt_regularWaldFunctional_one
    · rfl
    · exact studentizedBaseline_waldRegular
  let f : BaselineInput → BaselineHz → ℝ := fun ξ hz =>
    regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
      hz.1 hz.2 ξ.2.2
  let g : BaselineInput → BaselineHz := fun ξ => (ξ.1, ξ.2.1)
  have hfg : ContDiffAt ℝ 1 (Function.uncurry f) (baselineInput, g baselineInput) := by
    have hm : ContDiffAt ℝ 1
        (fun q : BaselineInput × BaselineHz => (q.2.1, q.2.2, q.1.2.2))
        (baselineInput, g baselineInput) := by fun_prop
    convert hF.comp (baselineInput, g baselineInput) hm using 1
    funext q
    rfl
  have hg : ContDiffAt ℝ 0 g baselineInput := by fun_prop
  exact (ContDiffAt.fderiv hfg hg (by norm_num)).continuousAt

private theorem continuousAt_baseline_targetDerivative :
    ContinuousAt
      (fun ξ : BaselineInput =>
        fderiv ℝ
          (fun b : BaselineB => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) ξ.1 ξ.2.1 b)
          ξ.2.2)
      baselineInput := by
  let F : BaselineInput → ℝ := fun ξ => regularWaldFunctional
    (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) ξ.1 ξ.2.1 ξ.2.2
  have hF : ContDiffAt ℝ 1 F baselineInput := by
    apply contDiffAt_regularWaldFunctional_one
    · rfl
    · exact studentizedBaseline_waldRegular
  let f : BaselineInput → BaselineB → ℝ := fun ξ b =>
    regularWaldFunctional (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) ξ.1 ξ.2.1 b
  let g : BaselineInput → BaselineB := fun ξ => ξ.2.2
  have hfg : ContDiffAt ℝ 1 (Function.uncurry f) (baselineInput, g baselineInput) := by
    have hm : ContDiffAt ℝ 1
        (fun q : BaselineInput × BaselineB => (q.1.1, q.1.2.1, q.2))
        (baselineInput, g baselineInput) := by fun_prop
    convert hF.comp (baselineInput, g baselineInput) hm using 1
    funext q
    rfl
  have hg : ContDiffAt ℝ 0 g baselineInput := by fun_prop
  exact (ContDiffAt.fderiv hfg hg (by norm_num)).continuousAt

private theorem continuousAt_baseline_waldDeltaVariance
    (p : Set.Ioo (0 : ℝ) 1) :
    ContinuousAt
      (fun q : BaselinePO × BaselineB =>
        waldDeltaVariance (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
          q.1 0 1 q.2)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) := by
  have hin := continuousAt_empiricalInput
  have heq : empiricalInput
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) =
      baselineInput := rfl
  have hs := continuousAt_baseline_sourceDerivative.comp_of_eq
    continuousAt_empiricalInput heq
  have ht := continuousAt_baseline_targetDerivative.comp_of_eq
    continuousAt_empiricalInput heq
  have hs' : ContinuousAt
      (fun q : BaselinePO × BaselineB =>
        fderiv ℝ
          (fun hz : BaselineHz => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) hz.1 hz.2 q.2)
          (unconditionalBalancingMoments q.1 0 1))
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) := by
    simpa [Function.comp_def, empiricalInput] using hs
  have ht' : ContinuousAt
      (fun q : BaselinePO × BaselineB =>
        fderiv ℝ
          (fun b : BaselineB => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
              (unconditionalBalancingMoments q.1 0 1).1
              (unconditionalBalancingMoments q.1 0 1).2 b)
          q.2)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) := by
    simpa [Function.comp_def, empiricalInput] using ht
  have hs_eval (d : BaselineHz) : ContinuousAt
      (fun q : BaselinePO × BaselineB =>
        (fderiv ℝ
          (fun hz : BaselineHz => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) hz.1 hz.2 q.2)
          (unconditionalBalancingMoments q.1 0 1)) d)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) :=
    hs'.clm_apply continuousAt_const
  have ht_eval (d : BaselineB) : ContinuousAt
      (fun q : BaselinePO × BaselineB =>
        (fderiv ℝ
          (fun b : BaselineB => regularWaldFunctional
            (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
              (unconditionalBalancingMoments q.1 0 1).1
              (unconditionalBalancingMoments q.1 0 1).2 b)
          q.2) d)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) :=
    ht'.clm_apply continuousAt_const
  unfold waldDeltaVariance
  dsimp only
  apply ContinuousAt.add
  · apply ContinuousAt.const_mul
    apply continuousAt_quadForm_family
    · intro o
      unfold sourceCellVector
      fun_prop
    · intro o
      exact hs_eval (sourceStatisticDirection 0 1 o)
  · apply ContinuousAt.const_mul
    apply continuousAt_quadForm_family
    · intro w
      fun_prop
    · intro w
      exact ht_eval (targetDirection w)

/-- Given [positivity of the deviation radius](hyp:heps), [within a fixed neighborhood of the baseline law, the rank-one estimator stays near one half and its totalized plug-in variance remains bounded](goal). -/
theorem studentizedBaseline_local_wald_control
    (p : Set.Ioo (0 : ℝ) 1) {eps : ℝ} (heps : 0 < eps) :
    ∃ U ∈ nhds (observedLaw studentizedBaseline,
        targetProxyVector studentizedBaseline),
      ∃ K : ℝ, 0 ≤ K ∧ ∀ q ∈ U,
        |regularWaldEstimator (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
            (unconditionalBalancingMoments q.1 0 1).1
            (unconditionalBalancingMoments q.1 0 1).2 q.2 - 1 / 2| < eps ∧
        regularWaldVariance (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
            p q.1 0 1 q.2 ≤ K := by
  let q0 : BaselinePO × BaselineB :=
    (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)
  let theta : BaselinePO × BaselineB → ℝ := fun q =>
    regularWaldEstimator (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
      (unconditionalBalancingMoments q.1 0 1).1
      (unconditionalBalancingMoments q.1 0 1).2 q.2
  let variance : BaselinePO × BaselineB → ℝ := fun q =>
    waldDeltaVariance (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p q.1 0 1 q.2
  have heq : empiricalInput q0 = baselineInput := rfl
  have htheta : ContinuousAt theta q0 := by
    have hF := (contDiffAt_regularWaldFunctional_one
      (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) rfl
      studentizedBaseline_waldRegular).continuousAt
    simpa [q0, theta, regularWaldEstimator, Function.comp_def, empiricalInput] using
      hF.comp_of_eq continuousAt_empiricalInput heq
  have htheta0 : theta q0 = 1 / 2 := by
    rw [show theta q0 = regularWaldFunctional
      (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
      (proxyMomentMatrix studentizedBaseline 0)
      (outcomeMomentVector studentizedBaseline 0 1)
      (targetProxyVector studentizedBaseline) by rfl,
      studentizedBaseline_regularWaldFunctional]
    norm_num [studentizedBaseline_outcomeMoment, Fin.sum_univ_two]
  have hvariance : ContinuousAt variance q0 := by
    exact continuousAt_baseline_waldDeltaVariance p
  let Utheta : Set (BaselinePO × BaselineB) := {q | |theta q - 1 / 2| < eps}
  let Uvariance : Set (BaselinePO × BaselineB) :=
    {q | |variance q - variance q0| < 1}
  have hUtheta : Utheta ∈ nhds q0 := by
    have hc : ContinuousAt (fun _ : BaselinePO × BaselineB => (1 / 2 : ℝ)) q0 :=
      continuousAt_const
    have hcont := (htheta.sub hc).abs
    have hmem : |theta q0 - 1 / 2| < eps := by rw [htheta0]; simpa using heps
    have hpre := hcont (isOpen_Iio.mem_nhds hmem)
    change (fun q => |theta q - 1 / 2|) ⁻¹' Set.Iio eps ∈ nhds q0
    exact hpre
  have hUvariance : Uvariance ∈ nhds q0 := by
    have hc : ContinuousAt (fun _ : BaselinePO × BaselineB => variance q0) q0 :=
      continuousAt_const
    have hcont := (hvariance.sub hc).abs
    have hmem : |variance q0 - variance q0| < 1 := by norm_num
    have hpre := hcont (isOpen_Iio.mem_nhds hmem)
    change (fun q => |variance q - variance q0|) ⁻¹' Set.Iio 1 ∈ nhds q0
    exact hpre
  refine ⟨Utheta ∩ Uvariance, Filter.inter_mem hUtheta hUvariance,
    |variance q0| + 1, by positivity, ?_⟩
  intro q hq
  change |theta q - 1 / 2| < eps ∧ |variance q - variance q0| < 1 at hq
  refine ⟨hq.1, ?_⟩
  simp only [regularWaldVariance]
  split_ifs
  · change variance q ≤ |variance q0| + 1
    have habs : |variance q| < |variance q0| + 1 := by
      calc
        |variance q| = |(variance q - variance q0) + variance q0| := by ring_nf
        _ ≤ |variance q - variance q0| + |variance q0| := abs_add_le _ _
        _ < 1 + |variance q0| := by linarith [hq.2]
        _ = |variance q0| + 1 := by ring
    exact (le_abs_self _).trans habs.le
  · positivity

private theorem waldCriticalValue_pos (alpha : Set.Ioo (0 : ℝ) 1) :
    0 < Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2) := by
  have harg := waldQuantileArg_mem alpha
  have hinv := Causalean.Mathlib.stdNormalCDF_probit harg.1 harg.2
  have hzero : Causalean.Mathlib.stdNormalCDF 0 = 1 / 2 := by
    have hsym := Causalean.Mathlib.stdNormalCDF_neg 0
    norm_num at hsym ⊢
    linarith
  apply (Causalean.Mathlib.stdNormalCDF_strictMono.lt_iff_lt).mp
  rw [hinv, hzero]
  linarith [alpha.2.2]

/-- Given [the genuine-row or nonnegative-size condition, positivity of the deviation radius, the half-radius bound, localization of the interval center, control of its half-width](hyp:hn,heps,heps_half,htheta,hwidth), [a nonnegative-variance Wald interval whose center and half-width are each within half the requested radius of one half is nonempty and lies inside that radius](goal). -/
theorem regularWaldInterval_localizes_at_half
    (alpha : Set.Ioo (0 : ℝ) 1) (theta V : ℝ) (n : ℕ) (hn : 2 ≤ n)
    {eps : ℝ} (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (htheta : |theta - 1 / 2| < eps / 2)
    (hwidth : Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2) *
      Real.sqrt (V / n) < eps / 2) :
    (regularWaldInterval theta V n hn alpha).Nonempty ∧
      ∀ t ∈ regularWaldInterval theta V n hn alpha, |t - 1 / 2| < eps := by
  let zcrit := Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2)
  let width := zcrit * Real.sqrt (V / n)
  have hz : 0 < zcrit := waldCriticalValue_pos alpha
  have hwidth0 : 0 ≤ width := mul_nonneg hz.le (Real.sqrt_nonneg _)
  have htheta_bounds : theta ∈ Set.Icc (0 : ℝ) 1 := by
    rw [abs_lt] at htheta
    constructor <;> linarith
  constructor
  · refine ⟨theta, ?_⟩
    exact ⟨⟨by linarith, by linarith⟩, htheta_bounds⟩
  · intro t ht
    have htI : t ∈ Set.Icc (theta - width) (theta + width) := ht.1
    have hdist : |t - theta| ≤ width := by
      rw [abs_le]
      constructor <;> linarith [htI.1, htI.2]
    calc
      |t - 1 / 2| = |(t - theta) + (theta - 1 / 2)| := by ring_nf
      _ ≤ |t - theta| + |theta - 1 / 2| := abs_add_le _ _
      _ < eps := by dsimp [width] at hdist hwidth; linarith

/-- Given [positivity of the source sample size, nonnegativity of the deviation radius](hyp:hns,hr), [one empirical full observed-law coordinate satisfies the stated Hoeffding tail bound under a finite source block](goal). -/
theorem source_observed_coordinate_tail
    {E U W X Y : Type*}
    [Fintype E] [Fintype U] [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq E] [DecidableEq U] [DecidableEq W] [DecidableEq X] [DecidableEq Y]
    [MeasurableSpace E] [MeasurableSpace W] [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass E] [MeasurableSingletonClass W]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (Mdl : LatentShiftSCM E U W X Y) (o : E × W × X × Y)
    (ns nt : ℕ) (hns : 0 < ns) (r : ℝ) (hr : 0 ≤ r) :
    (twoSampleLaw Mdl ns nt).real {s |
      r ≤ |finEmpObservedLaw ns s o.1 o.2.1 o.2.2.1 o.2.2.2 -
        observedLaw Mdl o.1 o.2.1 o.2.2.1 o.2.2.2|} ≤
      2 * Real.exp (-2 * ns * r ^ 2) := by
  let g : (E × W × X × Y) → ℝ := fun z => if z = o then 1 else 0
  have hg : Measurable g := measurable_of_finite _
  have hgb : ∀ᵐ z ∂observedMeasure Mdl, g z ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with z
    dsimp [g]
    split_ifs <;> norm_num
  have hint : ∫ z, g z ∂observedMeasure Mdl =
      observedLaw Mdl o.1 o.2.1 o.2.2.1 o.2.2.2 := by
    rw [observedMeasure, PMF.integral_eq_sum]
    simp only [observedPMF, PMF.ofFintype_apply]
    simp_rw [ENNReal.toReal_ofReal (observedLaw_nonneg Mdl _ _ _ _)]
    rw [Fintype.sum_eq_single o]
    · simp [g]
    · intro z hzo
      simp [g, hzo]
  have hh := pi_hoeffding_cell (observedMeasure Mdl) g hg hgb ns hns r hr
  let A : Set (Fin ns → E × W × X × Y) := {s |
    r ≤ |(ns : ℝ)⁻¹ * ∑ i, g (s i) - ∫ z, g z ∂observedMeasure Mdl|}
  have hA : MeasurableSet A := A.toFinite.measurableSet
  have hevent : {s : Omega E W X Y ns nt |
      r ≤ |finEmpObservedLaw ns s o.1 o.2.1 o.2.2.1 o.2.2.2 -
        observedLaw Mdl o.1 o.2.1 o.2.2.1 o.2.2.2|} =
      sourceBlock ns nt ⁻¹' A := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    dsimp [A, g, finEmpObservedLaw]
    rw [hint]
    have ho : (o.1, o.2.1, o.2.2.1, o.2.2.2) = o := by
      rcases o with ⟨e, w, x, y⟩
      rfl
    rw [ho]
    rfl
  rw [hevent]
  have hmap : ((twoSampleLaw Mdl ns nt).map
      (sourceBlock (E := E) (W := W) (X := X) (Y := Y) ns nt)).real A =
      (twoSampleLaw Mdl ns nt).real (sourceBlock ns nt ⁻¹' A) := by
    exact congrArg ENNReal.toReal (Measure.map_apply measurable_fst hA)
  rw [← hmap, twoSampleLaw_sourceBlock]
  exact hh

/-- [The two-sample observation](hyp:s) determines [the baseline empirical pair](goal), whose
components are [the empirical full observed law](step:1) and [the empirical target-proxy
vector](step:2). -/
noncomputable def baselineEmpiricalPair {ns nt : ℕ}
    (s : Omega (Fin 2) (Fin 2) (Fin 1) (Fin 2) ns nt) :
    BaselinePO × BaselineB :=
  (finEmpObservedLaw ns s, finEmpTargetProxy nt s)

/-- Given [positivity of the source sample size, positivity of the target sample size, nonnegativity of the deviation radius](hyp:hns,hnt,hr), [the baseline empirical source-and-target pair leaves a fixed norm ball with at most the stated finite-union exponential probability](goal). -/
theorem studentizedBaseline_empiricalPair_tail
    (ns nt : ℕ) (hns : 0 < ns) (hnt : 0 < nt)
    (r : ℝ) (hr : 0 < r) :
    (twoSampleLaw studentizedBaseline ns nt).real {s |
      r ≤ dist (baselineEmpiricalPair s)
        (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)} ≤
      16 * Real.exp (-2 * ns * r ^ 2) +
        4 * Real.exp (-2 * nt * r ^ 2) := by
  let O := Fin 2 × Fin 2 × Fin 1 × Fin 2
  let I := O ⊕ Fin 2
  let bad : I → Set (Omega (Fin 2) (Fin 2) (Fin 1) (Fin 2) ns nt) := fun i =>
    match i with
    | Sum.inl o => {s | r ≤ |finEmpObservedLaw ns s o.1 o.2.1 o.2.2.1 o.2.2.2 -
        observedLaw studentizedBaseline o.1 o.2.1 o.2.2.1 o.2.2.2|}
    | Sum.inr w => {s | r ≤ |finEmpTargetProxy nt s w -
        targetProxyVector studentizedBaseline w|}
  have htail : ∀ i, (twoSampleLaw studentizedBaseline ns nt).real (bad i) ≤
      match i with
      | Sum.inl _ => 2 * Real.exp (-2 * ns * r ^ 2)
      | Sum.inr _ => 2 * Real.exp (-2 * nt * r ^ 2) := by
    intro i
    rcases i with o | w
    · exact source_observed_coordinate_tail studentizedBaseline o ns nt hns r hr.le
    · exact target_proxy_coordinate_tail studentizedBaseline w ns nt hnt
        (twoSampleLaw studentizedBaseline ns nt)
        (twoSampleLaw_targetBlock studentizedBaseline ns nt) r hr.le
  have hsub : {s | r ≤ dist (baselineEmpiricalPair s)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)} ⊆
      ⋃ i, bad i := by
    intro s hs
    by_contra hnot
    simp only [Set.mem_iUnion, not_exists] at hnot
    have hPO : ∀ o : O,
        |finEmpObservedLaw ns s o.1 o.2.1 o.2.2.1 o.2.2.2 -
          observedLaw studentizedBaseline o.1 o.2.1 o.2.2.1 o.2.2.2| < r := by
      intro o
      exact lt_of_not_ge (hnot (Sum.inl o))
    have hb : ∀ w : Fin 2,
        |finEmpTargetProxy nt s w - targetProxyVector studentizedBaseline w| < r := by
      intro w
      exact lt_of_not_ge (hnot (Sum.inr w))
    have hnorm : ‖baselineEmpiricalPair s -
        (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)‖ < r := by
      simp only [Prod.norm_def, max_lt_iff, pi_norm_lt_iff hr, Real.norm_eq_abs,
        baselineEmpiricalPair, Pi.sub_apply, Prod.fst_sub, Prod.snd_sub]
      exact ⟨fun e w x y => hPO (e, w, x, y), hb⟩
    change r ≤ dist (baselineEmpiricalPair s)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline) at hs
    rw [dist_eq_norm] at hs
    exact (not_le_of_gt hnorm) hs
  calc
    (twoSampleLaw studentizedBaseline ns nt).real {s |
        r ≤ dist (baselineEmpiricalPair s)
          (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)}
        ≤ (twoSampleLaw studentizedBaseline ns nt).real (⋃ i, bad i) :=
          measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ i, (twoSampleLaw studentizedBaseline ns nt).real (bad i) :=
      measureReal_iUnion_fintype_le bad
    _ ≤ ∑ i : I, match i with
        | Sum.inl _ => 2 * Real.exp (-2 * ns * r ^ 2)
        | Sum.inr _ => 2 * Real.exp (-2 * nt * r ^ 2) :=
      Finset.sum_le_sum fun i _ => htail i
    _ = 16 * Real.exp (-2 * ns * r ^ 2) +
        4 * Real.exp (-2 * nt * r ^ 2) := by
      simp [I, O, Fintype.card_prod]
      ring

/-- Given [positivity of the source sample size, positivity of the target sample size, nonnegativity of the deviation radius](hyp:hns,hnt,hr), [the fixed-radius empirical-pair tail bound tends to zero when both allocation blocks diverge](goal). -/
theorem studentizedBaseline_empiricalPair_tail_tendsto_zero
    (ns nt : ℕ → ℕ)
    (hns : Filter.Tendsto (fun n => (ns n : ℝ)) Filter.atTop Filter.atTop)
    (hnt : Filter.Tendsto (fun n => (nt n : ℝ)) Filter.atTop Filter.atTop)
    (r : ℝ) (hr : 0 < r) :
    Filter.Tendsto (fun n =>
      (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {s |
        r ≤ dist (baselineEmpiricalPair s)
          (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)})
      Filter.atTop (nhds 0) := by
  have hcoef : 0 < 2 * r ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hr)
  have hnegS : Filter.Tendsto (fun n => -2 * (ns n : ℝ) * r ^ 2)
      Filter.atTop Filter.atBot := by
    have hpos := hns.const_mul_atTop hcoef
    have hneg := Filter.tendsto_neg_atTop_atBot.comp hpos
    simpa [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using hneg
  have hnegT : Filter.Tendsto (fun n => -2 * (nt n : ℝ) * r ^ 2)
      Filter.atTop Filter.atBot := by
    have hpos := hnt.const_mul_atTop hcoef
    have hneg := Filter.tendsto_neg_atTop_atBot.comp hpos
    simpa [Function.comp_def, mul_assoc, mul_left_comm, mul_comm] using hneg
  have hbound : Filter.Tendsto (fun n =>
      16 * Real.exp (-2 * (ns n : ℝ) * r ^ 2) +
        4 * Real.exp (-2 * (nt n : ℝ) * r ^ 2)) Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hnegS)).add
        (tendsto_const_nhds.mul (Real.tendsto_exp_atBot.comp hnegT))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => measureReal_nonneg
  · filter_upwards [hns.eventually (Filter.eventually_gt_atTop 0),
      hnt.eventually (Filter.eventually_gt_atTop 0)] with n hsn htn
    exact studentizedBaseline_empiricalPair_tail (ns n) (nt n)
      (by exact_mod_cast hsn) (by exact_mod_cast htn) r hr
  · exact hbound

private theorem block_tendsto_atTop_of_ratio
    (m : ℕ → ℕ) (q : ℝ) (hq : 0 < q)
    (hratio : Filter.Tendsto (fun n => (m n : ℝ) / n)
      Filter.atTop (nhds q)) :
    Filter.Tendsto (fun n => (m n : ℝ)) Filter.atTop Filter.atTop := by
  have hlower : ∀ᶠ n in Filter.atTop, q / 2 ≤ (m n : ℝ) / n := by
    exact hratio.eventually (Ici_mem_nhds (by linarith : q / 2 < q))
  have hscale : Filter.Tendsto (fun n : ℕ => q / 2 * (n : ℝ))
      Filter.atTop Filter.atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop (by positivity)
  apply Filter.tendsto_atTop_mono' Filter.atTop _ hscale
  filter_upwards [hlower, Filter.eventually_ge_atTop 1] with n hnratio hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    q / 2 * (n : ℝ) ≤ ((m n : ℝ) / n) * n := by gcongr
    _ = m n := by field_simp

/-- Given [the admissible allocation condition](hyp:halloc), [both real-valued source and target block sizes diverge under an admissible triangular allocation](goal). -/
theorem triangularAllocation_blocks_tendsto_atTop_real
    (p : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p) :
    Filter.Tendsto (fun n => (ns n : ℝ)) Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n => (nt n : ℝ)) Filter.atTop Filter.atTop := by
  have hsource := block_tendsto_atTop_of_ratio ns p p.2.1 halloc.2.2.2
  have htargetRatio : Filter.Tendsto (fun n => (nt n : ℝ) / n)
      Filter.atTop (nhds (1 - (p : ℝ))) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    have hsub := hconst.sub halloc.2.2.2
    apply hsub.congr'
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hsum := (halloc.2.2.1 n hn).2.2
    have hsumR : (ns n : ℝ) + (nt n : ℝ) = n := by exact_mod_cast hsum
    have hntR : (nt n : ℝ) = (n : ℝ) - ns n := by linarith
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    rw [hntR]
    field_simp
  exact ⟨hsource, block_tendsto_atTop_of_ratio nt (1 - p) (by linarith [p.2.2])
    htargetRatio⟩

/-- Given [the admissible allocation condition, the specified empirical neighborhood](hyp:halloc,hU), [the probability that the baseline empirical source-and-target pair leaves any fixed neighborhood tends to zero](goal). -/
theorem studentizedBaseline_empiricalPair_compl_tendsto_zero
    (p : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p)
    (U : Set (BaselinePO × BaselineB))
    (hU : U ∈ nhds (observedLaw studentizedBaseline,
      targetProxyVector studentizedBaseline)) :
    Filter.Tendsto (fun n =>
      (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {s |
        baselineEmpiricalPair s ∉ U}) Filter.atTop (nhds 0) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hblocks := triangularAllocation_blocks_tendsto_atTop_real p ns nt halloc
  have htail := studentizedBaseline_empiricalPair_tail_tendsto_zero ns nt
    hblocks.1 hblocks.2 r hr
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => measureReal_nonneg
  · apply Filter.Eventually.of_forall
    intro n
    change (twoSampleLaw studentizedBaseline (ns n) (nt n)).real
        {s | baselineEmpiricalPair s ∉ U} ≤
      (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {s |
        r ≤ dist (baselineEmpiricalPair s)
          (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)}
    apply measureReal_mono (μ := twoSampleLaw studentizedBaseline (ns n) (nt n))
      _ (measure_ne_top _ _)
    intro s hs
    change baselineEmpiricalPair s ∉ U at hs
    change r ≤ dist (baselineEmpiricalPair s)
      (observedLaw studentizedBaseline, targetProxyVector studentizedBaseline)
    by_contra hdist
    apply hs
    apply hball
    exact lt_of_not_ge hdist
  · exact htail

/-- Given [the admissible allocation condition](hyp:halloc), [at the fixed baseline, the probability that the empirical Wald interval is empty or fails the requested localization tends to zero](goal). -/
theorem studentizedBaseline_waldLocalization_bad_tendsto_zero
    (p alpha : Set.Ioo (0 : ℝ) 1) (ns nt : ℕ → ℕ)
    (halloc : TriangularAllocation ns nt p)
    (eps : Set.Ioo (0 : ℝ) (1 / 2)) :
    Filter.Tendsto (fun n =>
      (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {omega |
        if hn : 2 ≤ n then
          ¬ ((regularWaldInterval
              (regularWaldEstimator
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                (finEmpProxyMoment (ns n) 0 omega)
                (finEmpOutcomeMoment (ns n) 0 1 omega)
                (finEmpTargetProxy (nt n) omega))
              (regularWaldVariance
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
                (finEmpObservedLaw (ns n) omega) 0 1
                (finEmpTargetProxy (nt n) omega)) n hn alpha).Nonempty ∧
            ∀ t ∈ regularWaldInterval
              (regularWaldEstimator
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                (finEmpProxyMoment (ns n) 0 omega)
                (finEmpOutcomeMoment (ns n) 0 1 omega)
                (finEmpTargetProxy (nt n) omega))
              (regularWaldVariance
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
                (finEmpObservedLaw (ns n) omega) 0 1
                (finEmpTargetProxy (nt n) omega)) n hn alpha,
              |t - 1 / 2| < eps)
        else False}) Filter.atTop (nhds 0) := by
  obtain ⟨U, hU, K, hK0, hcontrol⟩ :=
    studentizedBaseline_local_wald_control p (half_pos eps.2.1)
  have hcompl := studentizedBaseline_empiricalPair_compl_tendsto_zero
    p ns nt halloc U hU
  let zcrit := Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2)
  have hwidth : Filter.Tendsto (fun n : ℕ =>
      zcrit * Real.sqrt (K / (n : ℝ))) Filter.atTop (nhds 0) := by
    have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have hinv := tendsto_inv_atTop_zero.comp hcast
    have hratio : Filter.Tendsto (fun n : ℕ => K * (n : ℝ)⁻¹)
        Filter.atTop (nhds 0) := by
      simpa using (show Filter.Tendsto (fun n : ℕ => K * (n : ℝ)⁻¹)
        Filter.atTop (nhds (K * 0)) from tendsto_const_nhds.mul hinv)
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hratio
    simpa [div_eq_mul_inv, zcrit] using tendsto_const_nhds.mul hsqrt
  have hwidth_small : ∀ᶠ n : ℕ in Filter.atTop,
      zcrit * Real.sqrt (K / (n : ℝ)) < (eps : ℝ) / 2 :=
    hwidth.eventually (Iio_mem_nhds (half_pos eps.2.1))
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n => measureReal_nonneg
  · filter_upwards [Filter.eventually_ge_atTop 2, hwidth_small] with n hn hsmall
    simp only [dif_pos hn]
    change (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {omega |
        ¬ ((regularWaldInterval
              (regularWaldEstimator
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                (finEmpProxyMoment (ns n) 0 omega)
                (finEmpOutcomeMoment (ns n) 0 1 omega)
                (finEmpTargetProxy (nt n) omega))
              (regularWaldVariance
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
                (finEmpObservedLaw (ns n) omega) 0 1
                (finEmpTargetProxy (nt n) omega)) n hn alpha).Nonempty ∧
            ∀ t ∈ regularWaldInterval
              (regularWaldEstimator
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
                (finEmpProxyMoment (ns n) 0 omega)
                (finEmpOutcomeMoment (ns n) 0 1 omega)
                (finEmpTargetProxy (nt n) omega))
              (regularWaldVariance
                (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
                (finEmpObservedLaw (ns n) omega) 0 1
                (finEmpTargetProxy (nt n) omega)) n hn alpha,
              |t - 1 / 2| < eps)} ≤
      (twoSampleLaw studentizedBaseline (ns n) (nt n)).real {omega |
        baselineEmpiricalPair omega ∉ U}
    apply measureReal_mono _ (measure_ne_top _ _)
    intro omega hbad hmem
    apply hbad
    let q := baselineEmpiricalPair omega
    have hc := hcontrol q hmem
    have hmom : unconditionalBalancingMoments q.1 0 1 =
        (finEmpProxyMoment (ns n) 0 omega,
          finEmpOutcomeMoment (ns n) 0 1 omega) := by
      subst q
      simp only [baselineEmpiricalPair]
      apply Prod.ext
      · ext w e
        simp only [unconditionalBalancingMoments, finEmpObservedLaw,
          finEmpProxyMoment, Fin.sum_univ_two]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rcases hobs : omega.1 i with ⟨ei, wi, xi, yi⟩
        fin_cases ei <;> fin_cases wi <;> fin_cases xi <;> fin_cases yi <;>
          fin_cases e <;> fin_cases w <;> simp_all
      · ext e
        simp only [unconditionalBalancingMoments, finEmpObservedLaw,
          finEmpOutcomeMoment, Fin.sum_univ_two]
        rw [← mul_add, ← Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        rcases hobs : omega.1 i with ⟨ei, wi, xi, yi⟩
        fin_cases ei <;> fin_cases wi <;> fin_cases xi <;> fin_cases yi <;>
          fin_cases e <;> simp_all
    have hcenter : |regularWaldEstimator
        (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2))
        (finEmpProxyMoment (ns n) 0 omega)
        (finEmpOutcomeMoment (ns n) 0 1 omega)
        (finEmpTargetProxy (nt n) omega) - 1 / 2| < (eps : ℝ) / 2 := by
      rw [hmom] at hc
      simpa [q, baselineEmpiricalPair] using hc.1
    have hVle : regularWaldVariance
        (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
        (finEmpObservedLaw (ns n) omega) 0 1
        (finEmpTargetProxy (nt n) omega) ≤ K := hc.2
    have hsqrt : Real.sqrt
        (regularWaldVariance (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
          (finEmpObservedLaw (ns n) omega) 0 1
          (finEmpTargetProxy (nt n) omega) / n) ≤ Real.sqrt (K / n) := by
      apply Real.sqrt_le_sqrt
      gcongr
    have hw : Causalean.Mathlib.probit (1 - (alpha : ℝ) / 2) * Real.sqrt
        (regularWaldVariance (⟨1, by decide⟩ : RankIndex (Fin 2) (Fin 2)) p
          (finEmpObservedLaw (ns n) omega) 0 1
          (finEmpTargetProxy (nt n) omega) / n) < (eps : ℝ) / 2 := by
      calc
        _ ≤ zcrit * Real.sqrt (K / n) :=
          mul_le_mul_of_nonneg_left hsqrt (waldCriticalValue_pos alpha).le
        _ < _ := hsmall
    exact regularWaldInterval_localizes_at_half alpha _ _ n hn eps.2.1 eps.2.2
      hcenter hw
  · exact hcompl

end CausalSmith.SCM.ProxyTargetspanTransport
