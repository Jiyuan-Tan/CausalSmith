module
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Calibration
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Defs.Upper
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.Helpers.TwoPointLength
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ObservableOdds
public import CausalSmith.Stat.STAT_LogoddsLowsmoothFrontier_Research.T_ProjectionControl

/-! # Coordinate mean identities and variance bounds

The empirical mean uses independent original records. The projection statistic
uses the sharp order-two Hoeffding bound; adding the independent seed preserves
variance. Together these give the two public coordinate variance radii.
Disintegration also identifies both biases with projection residual inner products.
-/
public section
set_option linter.style.longLine false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace CausalSmith.Stat.LogoddsLowsmoothFrontier

/-- [Both binary marks are continuous on the original record space. [The stated conclusion follows](goal). -/
-- @node: continuous_treatment_mark
@[fun_prop] lemma continuous_treatment_mark : Continuous treatment := by
  exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
    continuous_snd.fst

/-- The outcome mark is continuous on the original record space. [The stated conclusion follows](goal). -/
-- @node: continuous_outcome_mark
@[fun_prop] lemma continuous_outcome_mark : Continuous outcome := by
  exact (continuous_of_discreteTopology : Continuous (fun b : Bool => if b then (1 : ℝ) else 0)).comp
    continuous_snd.snd

/-- Finite cosine statistics are continuous functions of the original sample. Under the stated assumptions. [The stated hypotheses](hyp:hW,hV) hold, and [the stated conclusion follows](goal). -/
-- @node: continuous_projectionStatistic_sample
lemma continuous_projectionStatistic_sample (n k : ℕ) (W V : Record → ℝ)
    (hW : Continuous W) (hV : Continuous V) :
    Continuous (projectionStatistic n k W V) := by
  have hb (j : ℕ) : Continuous (cosineBasis j) := by
    unfold cosineBasis
    split_ifs <;> fun_prop
  unfold projectionStatistic projectionKernel covariate
  fun_prop

/-- [The two coordinate estimates have finite second moments, including the seed. [the stated conclusion](goal) holds. -/
-- @node: coordinateEstimates_memLp
lemma coordinateEstimates_memLp (P : ObservedLaw) (n kC kS : ℕ) :
    MemLp (fun ω : Experiment n => cHat n kC ω.1) 2 (experimentLaw P n) ∧
    MemLp (fun ω : Experiment n => sHat n kS ω.1) 2 (experimentLaw P n) := by
  let := experimentLaw_probability P n
  have hc : Continuous (cHat n kC) := by
    unfold cHat
    apply Continuous.sub
    · fun_prop
    · exact continuous_projectionStatistic_sample n kC _ _
        continuous_treatment_mark continuous_outcome_mark
  have hs : Continuous (sHat n kS) := by
    unfold sHat
    apply continuous_projectionStatistic_sample
    all_goals fun_prop
  exact ⟨(hc.comp continuous_fst).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _),
    (hs.comp continuous_fst).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)⟩

/-- Continuous marks give a square-integrable finite projection statistic. Under the stated assumptions. [The stated hypotheses](hyp:hW,hV) hold, and [the stated conclusion follows](goal). -/
-- @node: projectionStatistic_sample_memLp
lemma projectionStatistic_sample_memLp (P : ObservedLaw) (n k : ℕ)
    (W V : Record → ℝ) (hW : Continuous W) (hV : Continuous V) :
    MemLp (projectionStatistic n k W V) 2
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
  letI : IsProbabilityMeasure
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
    unfold Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
    infer_instance
  exact (continuous_projectionStatistic_sample n k W V hW hV).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- [Tensoring the unused independent seed preserves the sharp projection variance.](goal) Under [the stated assumptions](hyp:hDesign,hn,hW,hV,hWR,hVR). -/
-- @node: projectionStatistic_experiment_variance_le
lemma projectionStatistic_experiment_variance_le (P : ObservedLaw)
    (hDesign : UniformDesign P) (n k : ℕ) (hn : 2 ≤ n)
    (W V : Record → ℝ) (hW : Continuous W) (hV : Continuous V)
    (hWR : ∀ o, 0 ≤ W o ∧ W o ≤ 1) (hVR : ∀ o, 0 ≤ V o ∧ V o ≤ 1) :
    variance (fun ω : Experiment n => projectionStatistic n k W V ω.1)
      (experimentLaw P n) ≤ 4/(n : ℝ)+2*k/((n : ℝ)*((n : ℝ)-1)) := by
  let WM : BoundedMark := ⟨W, hW.measurable, hWR⟩
  let VM : BoundedMark := ⟨V, hV.measurable, hVR⟩
  have hMeas := (continuous_projectionStatistic_sample n k W V hW hV).measurable
  rw [experimentLaw, measurePreserving_fst.variance_fun_comp hMeas.aemeasurable,
    variance_eq_integral hMeas.aemeasurable]
  exact projectionStatistic_variance_le P hDesign WM VM k n hn

/-- [Independence of the original records gives the unit-range empirical mean
variance bound used for the numerator coordinate. [the documented result](goal) Under [the stated assumptions](hyp:hW,hWR). Under [the stated assumptions](hyp:hn). -/
-- @node: bounded_sampleMean_variance_le
lemma bounded_sampleMean_variance_le (P : ObservedLaw) (n : ℕ) (hn : 1 ≤ n)
    (W : Record → ℝ) (hW : Continuous W) (hWR : ∀ o, 0 ≤ W o ∧ W o ≤ 1) :
    variance (fun ω : Experiment n => (n : ℝ)⁻¹ * ∑ i, W (ω.1 i))
      (experimentLaw P n) ≤ 1/(n : ℝ) := by
  have hMem : MemLp W 2 P.measure :=
    hW.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hVar : variance W P.measure ≤ 1 := by
    have h := variance_le_sq_of_bounded (μ := P.measure) (Filter.Eventually.of_forall hWR) hW.measurable.aemeasurable
    norm_num at h
    linarith
  have hMeas : Measurable (fun o : Fin n → Record => (n : ℝ)⁻¹ * ∑ i, W (o i)) := by
    fun_prop
  rw [experimentLaw, measurePreserving_fst.variance_fun_comp hMeas.aemeasurable,
    variance_const_mul]
  have hSum : variance (fun o : Fin n → Record => ∑ i, W (o i))
      (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) =
      (n : ℝ) * variance W P.measure := by
    have heq : (fun o : Fin n → Record => ∑ i, W (o i)) =
        ∑ i : Fin n, fun o : Fin n → Record => W (o i) := by
      funext o
      simp
    rw [heq]
    simpa [Causalean.Stat.UStatistic.LocalizedVariance.iidLaw] using
      (variance_sum_pi (μ := fun _ : Fin n => P.measure) (X := fun _ => W) (fun _ => hMem))
  rw [hSum]
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc
    (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * variance W P.measure) ≤
        (n : ℝ)⁻¹ ^ 2 * ((n : ℝ) * 1) := by gcongr
    _ = 1/(n : ℝ) := by field_simp

/-- [Nonnegativity of the sum variance bounds the variance of a difference,
without requiring the two coordinates to be independent. [the documented result](goal) Under [the stated assumptions](hyp:μ,hX,hY). -/
-- @node: coordinate_variance_sub_le
lemma coordinate_variance_sub_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y : Ω → ℝ)
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    variance (fun ω => X ω-Y ω) μ ≤ 2*variance X μ+2*variance Y μ := by
  have hAdd := variance_nonneg (fun ω => X ω+Y ω) μ
  rw [variance_fun_add hX hY] at hAdd
  rw [variance_fun_sub hX hY]
  linarith

/-- [Both exact coordinate estimates obey the prescribed public variance radius.](goal) Under [the stated assumptions](hyp:hDesign,hn). -/
-- @node: coordinateEstimates_variance_bounds
lemma coordinateEstimates_variance_bounds (P : ObservedLaw) (hDesign : UniformDesign P)
    (n kC kS : ℕ) (hn : 2 ≤ n) :
    variance (fun ω : Experiment n => cHat n kC ω.1) (experimentLaw P n) ≤ varianceRadius n kC ∧
    variance (fun ω : Experiment n => sHat n kS ω.1) (experimentLaw P n) ≤ varianceRadius n kS := by
  letI := experimentLaw_probability P n
  have hTreat (o : Record) : 0 ≤ treatment o ∧ treatment o ≤ 1 := by
    unfold treatment; split <;> norm_num
  have hOutcome (o : Record) : 0 ≤ outcome o ∧ outcome o ≤ 1 := by
    unfold outcome; split <;> norm_num
  have hAY (o : Record) : 0 ≤ treatment o * outcome o ∧ treatment o * outcome o ≤ 1 := by
    rcases o with ⟨x, a, y⟩; cases a <;> cases y <;> norm_num [treatment, outcome]
  have h10 (o : Record) : 0 ≤ treatment o * (1-outcome o) ∧ treatment o * (1-outcome o) ≤ 1 := by
    rcases o with ⟨x, a, y⟩; cases a <;> cases y <;> norm_num [treatment, outcome]
  have h01 (o : Record) : 0 ≤ (1-treatment o) * outcome o ∧ (1-treatment o) * outcome o ≤ 1 := by
    rcases o with ⟨x, a, y⟩; cases a <;> cases y <;> norm_num [treatment, outcome]
  have hCproj := projectionStatistic_experiment_variance_le P hDesign n kC hn
    treatment outcome continuous_treatment_mark continuous_outcome_mark hTreat hOutcome
  have hSproj := projectionStatistic_experiment_variance_le P hDesign n kS hn
    (fun o => treatment o * (1-outcome o)) (fun o => (1-treatment o) * outcome o)
    (by fun_prop) (by fun_prop) h10 h01
  have hMean := bounded_sampleMean_variance_le P n (by omega)
    (fun o => treatment o * outcome o) (by fun_prop) hAY
  have hMeanMem : MemLp (fun ω : Experiment n => (n : ℝ)⁻¹ * ∑ i, treatment (ω.1 i) * outcome (ω.1 i))
      2 (experimentLaw P n) := by
    have hCont : Continuous (fun ω : Experiment n => (n : ℝ)⁻¹ * ∑ i, treatment (ω.1 i) * outcome (ω.1 i)) := by
      fun_prop
    exact hCont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCprojMem : MemLp (fun ω : Experiment n => projectionStatistic n kC treatment outcome ω.1)
      2 (experimentLaw P n) := by
    exact ((continuous_projectionStatistic_sample n kC _ _ continuous_treatment_mark
      continuous_outcome_mark).comp continuous_fst).memLp_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  constructor
  · have h := coordinate_variance_sub_le (experimentLaw P n) _ _ hMeanMem hCprojMem
    change variance (fun ω : Experiment n =>
      (n : ℝ)⁻¹ * ∑ i, treatment (ω.1 i) * outcome (ω.1 i) -
        projectionStatistic n kC treatment outcome ω.1) (experimentLaw P n) ≤ _
    unfold varianceRadius
    simp only [div_eq_mul_inv] at hMean hCproj ⊢
    nlinarith [h]
  · change variance (fun ω : Experiment n => projectionStatistic n kS
      (fun o => treatment o * (1-outcome o)) (fun o => (1-treatment o) * outcome o) ω.1)
        (experimentLaw P n) ≤ _
    have hnR : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hExtra : 0 ≤ 6/(n : ℝ)+2*kS/((n : ℝ)*((n : ℝ)-1)) := by positivity
    unfold varianceRadius
    simp only [div_eq_mul_inv] at hSproj hExtra ⊢
    nlinarith

/-- [Integrating a statistic that ignores the independent probability seed gives
its original finite-sample expectation. [the documented result](goal) -/
-- @node: experiment_integral_sample
lemma experiment_integral_sample (P : ObservedLaw) (n : ℕ) (f : (Fin n → Record) → ℝ) :
    (∫ ω : Experiment n, f ω.1 ∂experimentLaw P n) =
      ∫ o, f o ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n := by
  letI : IsProbabilityMeasure (Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n) := by
    unfold Causalean.Stat.UStatistic.LocalizedVariance.iidLaw
    infer_instance
  rw [experimentLaw, integral_fun_fst]
  simp

/-- The seed-free empirical mean has the original one-record expectation. Under the stated assumptions. [The stated hypotheses](hyp:hn,hW) hold, and [the stated conclusion follows](goal). -/
-- @node: sampleMean_experiment_integral
lemma sampleMean_experiment_integral (P : ObservedLaw) (n : ℕ) (hn : 1 ≤ n)
    (W : Record → ℝ) (hW : Continuous W) :
    (∫ ω : Experiment n, (n : ℝ)⁻¹ * ∑ i, W (ω.1 i) ∂experimentLaw P n) =
      ∫ o, W o ∂P.measure := by
  let μ := Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n
  letI : IsProbabilityMeasure μ := by
    dsimp [μ, Causalean.Stat.UStatistic.LocalizedVariance.iidLaw]
    infer_instance
  have hi (i : Fin n) : Integrable (fun o : Fin n → Record => W (o i)) μ :=
    (hW.comp (continuous_apply i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [experiment_integral_sample P n (fun o => (n : ℝ)⁻¹ * ∑ i, W (o i)),
    integral_const_mul, integral_finsetSum _ (fun i _ => hi i)]
  have heval (i : Fin n) : (∫ o : Fin n → Record, W (o i) ∂μ) = ∫ o, W o ∂P.measure := by
    exact integral_comp_eval hW.measurable.aestronglyMeasurable
  change (n : ℝ)⁻¹ * (∑ i : Fin n, ∫ o : Fin n → Record, W (o i) ∂μ) = _
  simp_rw [heval]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

/-- [Disintegration identifies the conditional treatment mean with propensity.](goal) Under [the stated assumptions](hyp:hW). -/
-- @node: conditionalMarkMean_treatment
lemma conditionalMarkMean_treatment (P : ObservedLaw) (W : BoundedMark)
    (hW : W.value = treatment) : conditionalMarkMean P W = propensity P := by
  funext x
  simp [conditionalMarkMean, hW, treatment, propensity]
  ring

/-- [Disintegration identifies the conditional outcome mean with the marginal risk.](goal) Under [the stated assumptions](hyp:hW). -/
-- @node: conditionalMarkMean_outcome
lemma conditionalMarkMean_outcome (P : ObservedLaw) (W : BoundedMark)
    (hW : W.value = outcome) : conditionalMarkMean P W = marginalMean P := by
  funext x
  rw [marginalMean_eq_cells]
  simp [conditionalMarkMean, hW, outcome, add_comm]

/-- [The two off-diagonal marks have exactly the model's off-diagonal cell means. [the stated conclusion](goal) holds. Under [the stated assumptions](hyp:hW,hV). -/
-- @node: conditionalMarkMean_offdiagonal
lemma conditionalMarkMean_offdiagonal (P : ObservedLaw) (W V : BoundedMark)
    (hW : W.value = fun o => treatment o * (1-outcome o))
    (hV : V.value = fun o => (1-treatment o) * outcome o) :
    conditionalMarkMean P W = cellProbability P true false ∧
    conditionalMarkMean P V = cellProbability P false true := by
  constructor <;> funext x <;> rw [cellProbability_eq_cells]
  · simp [conditionalMarkMean, hW, treatment, outcome]
  · simp [conditionalMarkMean, hV, treatment, outcome]

/-- The coordinate biases are precisely the two projection residual inner products;
no nuisance smoothness or approximation premise is used in these identities. [the documented result](goal) Under [the stated assumptions](hyp:hn). Under [the stated assumptions](hyp:hDesign). -/
-- @node: coordinateEstimates_bias_identities
lemma coordinateEstimates_bias_identities (P : ObservedLaw) (hDesign : UniformDesign P)
    (n kC kS : ℕ) (hn : 2 ≤ n) :
    (∫ ω : Experiment n, cHat n kC ω.1 ∂experimentLaw P n) - covarianceCoordinate P =
      uniformInner (fun x => propensity P x-cosineProjection kC (propensity P) x)
        (fun x => marginalMean P x-cosineProjection kC (marginalMean P) x) ∧
    (∫ ω : Experiment n, sHat n kS ω.1 ∂experimentLaw P n) - denominatorCoordinate P =
      -uniformInner (fun x => cellProbability P true false x-cosineProjection kS (cellProbability P true false) x)
        (fun x => cellProbability P false true x-cosineProjection kS (cellProbability P false true) x) := by
  letI := experimentLaw_probability P n
  let A : BoundedMark := ⟨treatment, continuous_treatment_mark.measurable, by
    intro o; unfold treatment; split <;> norm_num⟩
  let Y : BoundedMark := ⟨outcome, continuous_outcome_mark.measurable, by
    intro o; unfold outcome; split <;> norm_num⟩
  let W : BoundedMark := ⟨(fun o => treatment o*(1-outcome o)), by fun_prop, by
    rintro ⟨x,a,y⟩; cases a <;> cases y <;> norm_num [treatment,outcome]⟩
  let V : BoundedMark := ⟨(fun o => (1-treatment o)*outcome o), by fun_prop, by
    rintro ⟨x,a,y⟩; cases a <;> cases y <;> norm_num [treatment,outcome]⟩
  have hA := conditionalMarkMean_treatment P A rfl
  have hY := conditionalMarkMean_outcome P Y rfl
  obtain ⟨hW,hV⟩ := conditionalMarkMean_offdiagonal P W V rfl rfl
  have hCbias := projectionStatistic_bias P hDesign A Y kC n hn
  have hSbias := projectionStatistic_bias P hDesign W V kS n hn
  rw [hA,hY] at hCbias
  rw [hW,hV] at hSbias
  have hCCont := continuous_projectionStatistic_sample n kC treatment outcome
    continuous_treatment_mark continuous_outcome_mark
  have hSCont := continuous_projectionStatistic_sample n kS W.value V.value
    (by dsimp [W]; fun_prop) (by dsimp [V]; fun_prop)
  have hCmean : (∫ ω : Experiment n, projectionStatistic n kC treatment outcome ω.1 ∂experimentLaw P n) =
      ∫ o, projectionStatistic n kC treatment outcome o
        ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n :=
    experiment_integral_sample P n _
  have hSmean : (∫ ω : Experiment n, projectionStatistic n kS W.value V.value ω.1 ∂experimentLaw P n) =
      ∫ o, projectionStatistic n kS W.value V.value o
        ∂Causalean.Stat.UStatistic.LocalizedVariance.iidLaw P.measure n :=
    experiment_integral_sample P n _
  constructor
  · have hMeanCont : Continuous (fun ω : Experiment n =>
        (n : ℝ)⁻¹ * ∑ i, treatment (ω.1 i)*outcome (ω.1 i)) := by fun_prop
    have hMeanInt : Integrable (fun ω : Experiment n =>
        (n : ℝ)⁻¹ * ∑ i, treatment (ω.1 i)*outcome (ω.1 i)) (experimentLaw P n) :=
      hMeanCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hProjInt : Integrable (fun ω : Experiment n =>
        projectionStatistic n kC treatment outcome ω.1) (experimentLaw P n) :=
      (hCCont.comp continuous_fst).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [cHat]
    rw [integral_sub hMeanInt hProjInt,
      sampleMean_experiment_integral P n (by omega) (fun o => treatment o*outcome o) (by fun_prop), hCmean]
    unfold covarianceCoordinate
    rw [← hCbias]
    unfold uniformInner
    dsimp [A,Y]
    ring
  · change (∫ ω : Experiment n, projectionStatistic n kS W.value V.value ω.1 ∂experimentLaw P n) - _ = _
    rw [hSmean, ← hSbias]
    unfold denominatorCoordinate uniformInner
    ring

end CausalSmith.Stat.LogoddsLowsmoothFrontier
