module
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.Helpers.TransitionWindows
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TFiniteHonesty
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TObservableUpper
public import CausalSmith.Stat.STAT_NoisydoseWeakdesignTransition_Research.TObservedLower
public import Causalean.Stat.Minimax.HonestConfidenceSet
public import Causalean.Stat.Minimax.LeCam

/-! Uniform matched risk and honest-length frontier, full transition windows, and fixed-noise order. -/
public section
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology BigOperators
namespace CausalSmith.Stat.NoisydoseWeakdesignTransition
universe u


/-- Appending the same independent probability seed cannot increase total variation. [This is the stated conclusion](goal). -/
-- @node: tvDist_common_seed_le
lemma tvDist_common_seed_le {Ω U : Type*} [MeasurableSpace Ω] [MeasurableSpace U]
    (P Q : Measure Ω) (R : Measure U) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] [IsProbabilityMeasure R] :
    Causalean.Stat.tvDist (P.prod R) (Q.prod R) ≤ Causalean.Stat.tvDist P Q := by
  unfold Causalean.Stat.tvDist
  apply ciSup_le
  rintro ⟨A, hA⟩
  have hreal (M : Measure Ω) [IsProbabilityMeasure M] :
      (M.prod R).real A = ∫ x, (R (Prod.mk x ⁻¹' A)).toReal ∂M := by
    rw [measureReal_def, Measure.prod_apply hA, ← integral_toReal
      (measurable_measure_prodMk_left hA).aemeasurable]
    filter_upwards with x
    exact measure_lt_top R _
  rw [hreal P, hreal Q]
  simpa only [zero_add, mul_one, Causalean.Stat.tvDist] using
    Causalean.Stat.tvDist_integral_range P Q
      (fun x => (R (Prod.mk x ⁻¹' A)).toReal)
      (measurable_measure_prodMk_left hA).ennreal_toReal 0 1 (by norm_num)
      (fun x => ⟨ENNReal.toReal_nonneg, by
        simpa only [measureReal_def, zero_add] using (measureReal_le_one (μ := R)
          (s := Prod.mk x ⁻¹' A))⟩)

/-- A nonnegative loss dominates its threshold times the probability of exceeding it. [Under the stated conditions](hyp:f,hf). [This is the stated conclusion](goal). -/
-- @node: loss_threshold_lintegral_lower
lemma loss_threshold_lintegral_lower {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ) (hf : Measurable f) (r : ℝ) :
    ENNReal.ofReal r * P {x | r ≤ f x} ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂P := by
  rw [← lintegral_indicator_const (measurableSet_le measurable_const hf)]
  apply lintegral_mono
  intro x
  by_cases hx : r ≤ f x
  · rw [Set.indicator_of_mem (show x ∈ {x | r ≤ f x} from hx)]
    exact ENNReal.ofReal_le_ofReal hx
  · rw [Set.indicator_of_notMem (show x ∉ {x | r ≤ f x} from hx)]
    exact bot_le

/-- The two-point testing bound implies an extended absolute-risk floor without integrability. [Under the stated conditions](hyp:hT,hdelta,hsep,htv). [This is the stated conclusion](goal). -/
-- @node: absolute_risk_two_point_lower
lemma absolute_risk_two_point_lower {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (T : Ω → ℝ) (hT : Measurable T) (a b delta : ℝ) (hdelta : 0 ≤ delta)
    (hsep : delta ≤ |a-b|) (htv : Causalean.Stat.tvDist P Q ≤ 1/5) :
    ENNReal.ofReal (delta / 5) ≤
      max (∫⁻ x, ENNReal.ofReal |T x-a| ∂P)
        (∫⁻ x, ENNReal.ofReal |T x-b| ∂Q) := by
  have hsep' : 2 * (delta / 2) ≤ dist a b := by
    rw [Real.dist_eq]
    linarith
  have htest := Causalean.Stat.half_one_sub_tvDist_le_max_error
    (P₀ := P) (P₁ := Q) hT hsep'
  have hprob : (2/5 : ℝ) ≤
      max (P.real {x | delta/2 ≤ |T x-a|}) (Q.real {x | delta/2 ≤ |T x-b|}) := by
    simp only [Real.dist_eq] at htest
    linarith
  have hprob' : ENNReal.ofReal (2/5 : ℝ) ≤
      max (P {x | delta/2 ≤ |T x-a|}) (Q {x | delta/2 ≤ |T x-b|}) := by
    simpa [ENNReal.ofReal_max, measureReal_def] using ENNReal.ofReal_le_ofReal hprob
  have hP := loss_threshold_lintegral_lower P (fun x => |T x-a|)
    (by fun_prop) (delta/2)
  have hQ := loss_threshold_lintegral_lower Q (fun x => |T x-b|)
    (by fun_prop) (delta/2)
  calc
    ENNReal.ofReal (delta/5) =
        ENNReal.ofReal (delta/2) * ENNReal.ofReal (2/5 : ℝ) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (delta/2) *
        max (P {x | delta/2 ≤ |T x-a|}) (Q {x | delta/2 ≤ |T x-b|}) :=
      mul_le_mul_right hprob' _
    _ = max (ENNReal.ofReal (delta/2) * P {x | delta/2 ≤ |T x-a|})
        (ENNReal.ofReal (delta/2) * Q {x | delta/2 ≤ |T x-b|}) := mul_max _ _ _
    _ ≤ _ := max_le_max hP hQ

/-- Connected intervals covering each of two separated laws with probability at least one minus α, whose laws are within total variation τ, have expected length at least the separation times 1 − 2α − τ. [Under the stated conditions](hyp:hgraph,hdelta,halpha,hsep,htv,hconnected,hcoverP,hcoverQ). [This is the stated conclusion](goal). -/
-- @node: connected_interval_two_point_lower
lemma connected_interval_two_point_lower {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (C : Ω → Set ℝ) (hconnected : ∀ x, (C x).OrdConnected)
    (hgraph : MeasurableSet {p : Ω × ℝ | p.2 ∈ C p.1}) (a b delta alpha tau : ℝ)
    (hdelta : 0 ≤ delta) (halpha : alpha ≤ 1) (hsep : delta ≤ |a-b|)
    (hcoverP : ENNReal.ofReal (1-alpha) ≤ P {x | a ∈ C x})
    (hcoverQ : ENNReal.ofReal (1-alpha) ≤ Q {x | b ∈ C x})
    (htv : Causalean.Stat.tvDist P Q ≤ tau) :
    ENNReal.ofReal (delta*(1-2*alpha-tau)) ≤ ∫⁻ x, volume (C x) ∂P := by
  let A : Set Ω := {x | a ∈ C x}
  let B : Set Ω := {x | b ∈ C x}
  have hA : MeasurableSet A := hgraph.preimage (measurable_id.prodMk measurable_const)
  have hB : MeasurableSet B := hgraph.preimage (measurable_id.prodMk measurable_const)
  have hp : 1-alpha ≤ P.real A := by
    have h := ENNReal.toReal_mono (measure_ne_top P _) hcoverP
    rw [ENNReal.toReal_ofReal (by linarith)] at h
    exact h
  have hq : 1-alpha ≤ Q.real B := by
    have h := ENNReal.toReal_mono (measure_ne_top Q _) hcoverQ
    rw [ENNReal.toReal_ofReal (by linarith)] at h
    exact h
  have hgap := Causalean.Stat.measureReal_sub_le_tvDist (μ := P) (ν := Q) hB
  have hcompA : P.real Aᶜ = 1 - P.real A := by
    simpa using measureReal_compl hA (μ := P)
  have hcompB : P.real Bᶜ = 1 - P.real B := by
    simpa using measureReal_compl hB (μ := P)
  have hcompAB : P.real (A ∩ B)ᶜ = 1 - P.real (A ∩ B) := by
    simpa using measureReal_compl (hA.inter hB) (μ := P)
  have hunion := measureReal_union_le (μ := P) Aᶜ Bᶜ
  rw [← Set.compl_inter] at hunion
  have hboth : 1-2*alpha-tau ≤ P.real (A ∩ B) := by
    linarith
  have hboth' : ENNReal.ofReal (1-2*alpha-tau) ≤ P (A ∩ B) := by
    simpa [measureReal_def] using ENNReal.ofReal_le_ofReal hboth
  have hlength : ∀ x ∈ A ∩ B, ENNReal.ofReal delta ≤ volume (C x) := by
    intro x hx
    have hsub := (hconnected x).uIcc_subset hx.1 hx.2
    have hv : volume (uIcc a b) = ENNReal.ofReal |a-b| := by
      rcases le_total a b with hab | hba
      · rw [uIcc_of_le hab, Real.volume_Icc, abs_of_nonpos (sub_nonpos.mpr hab)]
        congr 1
        ring
      · rw [uIcc_of_ge hba, Real.volume_Icc, abs_of_nonneg (sub_nonneg.mpr hba)]
    exact (ENNReal.ofReal_le_ofReal hsep).trans (hv ▸ measure_mono hsub)
  calc
    ENNReal.ofReal (delta*(1-2*alpha-tau)) = ENNReal.ofReal delta * ENNReal.ofReal (1-2*alpha-tau) := by
      rw [← ENNReal.ofReal_mul hdelta]
    _ ≤ ENNReal.ofReal delta * P (A ∩ B) := mul_le_mul_right hboth' _
    _ = ∫⁻ x, (A ∩ B).indicator (fun _ => ENNReal.ofReal delta) x ∂P :=
      (lintegral_indicator_const (hA.inter hB) _).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A ∩ B
      · rw [Set.indicator_of_mem hx]
        exact hlength x hx
      · rw [Set.indicator_of_notMem hx]
        exact bot_le

/-- Ignoring the independent uniform seed preserves the observable estimator's absolute risk. [This is the stated conclusion](goal). -/
-- @node: totalEstimator_randomized_risk
lemma totalEstimator_randomized_risk {S : Type u} [MeasurableSpace S]
    (E : PathSpace S) (K : ClassConstants) (beta kappa : ℝ) (n : ℕ) (sigma : ℝ)
    (P : modelClass E K beta kappa sigma) :
    (∫⁻ z, ENNReal.ofReal |totalEstimator K beta kappa n sigma z.1 -
      causalTarget E (P.1 : Measure (StructSpace S))|
      ∂randomizedExperiment n sigma (P.1 : Measure (StructSpace S))) =
    ENNReal.ofReal (∫ data, |totalEstimator K beta kappa n sigma data -
      causalTarget E (P.1 : Measure (StructSpace S))|
      ∂experiment n sigma (P.1 : Measure (StructSpace S))) := by
  haveI := experiment_isProbabilityMeasure (P.1 : Measure (StructSpace S)) n sigma
  have ht := causalTarget_mem_Icc E (P.1 : Measure (StructSpace S))
    P.2.strataPos P.2.boundedPO P.2.meanRange
  have hi : Integrable (fun data => |totalEstimator K beta kappa n sigma data -
      causalTarget E (P.1 : Measure (StructSpace S))|)
      (experiment n sigma (P.1 : Measure (StructSpace S))) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with data
    have he := totalEstimator_mem_Icc K beta kappa n sigma data
    rw [Real.norm_eq_abs, abs_abs]
    apply abs_le.mpr
    constructor <;> linarith [he.1, he.2, ht.1, ht.2]
  unfold randomizedExperiment seedLaw
  rw [lintegral_prod _ (by fun_prop)]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one, mul_one]
  exact (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => abs_nonneg _))).symm

/-- The observable estimator is admissible for randomized minimax risk and attains its upper frontier. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa). -/
-- @node: minimaxRisk_frontier_upper
lemma minimaxRisk_frontier_upper (K : ClassConstants) (beta kappa : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ,
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      minimaxRisk E K beta kappa n sigma ≤ ENNReal.ofReal (C * frontierRate beta kappa sigma n) := by
  obtain ⟨C, hC, n0, hupper⟩ := observable_upper.{u} K beta kappa hbeta hkappa
  refine ⟨C, hC, n0, ?_⟩
  intro S _ E n hn sigma hsigma
  let T : Estimator n := ⟨fun z => totalEstimator K beta kappa n sigma z.1, by fun_prop⟩
  apply (Causalean.Stat.minimaxValueENNReal_le_worstCaseRisk T).trans
  apply Causalean.Stat.worstCaseRiskENNReal_le
  intro P
  change (∫⁻ z, ENNReal.ofReal |totalEstimator K beta kappa n sigma z.1 -
    causalTarget E (P.1 : Measure (StructSpace S))|
    ∂randomizedExperiment n sigma (P.1 : Measure (StructSpace S))) ≤ _
  rw [totalEstimator_randomized_risk]
  exact ENNReal.ofReal_le_ofReal ((hupper S E n hn sigma hsigma).1 P
    (iidSampling_holds n sigma _))

/-- The finite-honesty interval is admissible for the infimum defining honest expected length at noncoverage level α. [This is the stated conclusion](goal). [Under the stated conditions](hyp:hbeta,hkappa,halpha). -/
-- @node: honestLength_frontier_upper
lemma honestLength_frontier_upper (K : ClassConstants) (beta kappa alpha : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ n0 : ℕ,
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ∀ sigma ∈ Icc (0 : ℝ) (1/4),
      honestLength E K beta kappa alpha n sigma ≤
        ENNReal.ofReal (C * frontierRate beta kappa sigma n) := by
  obtain ⟨hcover, C, hC, n0, hlength⟩ := finite_honesty.{u} K beta kappa alpha hbeta hkappa halpha
  refine ⟨C, hC, n0, ?_⟩
  intro S _ E n hn sigma hsigma
  have hh : IsHonest E K beta kappa alpha n sigma
      (honestIntervalProcedure K beta kappa alpha n sigma) := by
    intro P
    have hc := hcover S E n sigma hsigma P
    exact (ENNReal.ofReal_le_ofReal hc).trans ENNReal.ofReal_toReal_le
  unfold honestLength
  apply (iInf_le _ ⟨honestIntervalProcedure K beta kappa alpha n sigma, hh⟩).trans
  exact iSup_le (fun P => hlength S E n hn sigma hsigma P)

/-- Every branch of the frontier is nonnegative on the public noise domain for nonzero samples. [Under the stated conditions](hyp:hn,hsigma). [This is the stated conclusion](goal). -/
-- @node: frontierRate_nonneg
lemma frontierRate_nonneg (beta kappa sigma : ℝ) (n : ℕ)
    (hn : 1 ≤ n) (hsigma : 0 ≤ sigma) : 0 ≤ frontierRate beta kappa sigma n := by
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 0 ≤ logScale n := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hnreal)
  apply Real.rpow_nonneg
  unfold frontierScale
  split_ifs
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · exact div_nonneg hsigma (Real.sqrt_nonneg _)
  · apply div_nonneg _ hlog
    apply Real.log_nonneg
    have hprod : 0 ≤ sigma^2 * logScale n := mul_nonneg (sq_nonneg sigma) hlog
    have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    linarith

/-- The observed separated witnesses imply both uniform minimax and honest-length floors at any noncoverage level below one half. [Under the stated conditions](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate,hbeta,hkappa,halpha,hK). [This is the stated conclusion](goal). -/
-- @node: frontier_both_lower
lemma frontier_both_lower (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (K : ClassConstants) (beta kappa alpha : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) (1/2))
    (hK : K.clo ≤ (kappa+1)*(2 : ℝ)^kappa ∧ (kappa+1)*(2 : ℝ)^kappa ≤ K.chi) :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 1 ≤ n0 ∧
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ∀ sigma ∈ Icc (0 : ℝ) (1/4),
        ENNReal.ofReal (c * frontierRate beta kappa sigma n) ≤ minimaxRisk E K beta kappa n sigma ∧
        ENNReal.ofReal (c * frontierRate beta kappa sigma n) ≤ honestLength E K beta kappa alpha n sigma := by
  let tau : ℝ := min (1/5) ((1-2*alpha)/2)
  have htau : 0 < tau := lt_min (by norm_num) (by linarith [halpha.2])
  have htau5 : tau ≤ 1/5 := min_le_left _ _
  have htauA : tau ≤ 1-2*alpha-tau := by
    have := min_le_right (1/5 : ℝ) ((1-2*alpha)/2)
    linarith
  obtain ⟨c, C, epsilon, Cpacket, cPacket, hc, hC, hepsilon, hCpacket, hcPacket,
    hpacket, n0, hwitness⟩ := observed_lower.{u} hLocalization_of_gate
      hLipschitz_of_gate hNorm_of_gate hGamma_of_gate K beta kappa hbeta hkappa hK tau htau
  refine ⟨c*tau, mul_pos hc htau, max n0 1, le_max_right _ _, ?_⟩
  intro S _ E n hn sigma hsigma
  obtain ⟨Pplus, Pminus, Pstar, hp, hm, hs, hbp, hbm, hbs, hlegal,
    hdesign, hdesignStar, hsep, htv, hconstruction⟩ :=
      hwitness S E n ((le_max_left _ _).trans hn) sigma hsigma
  let pp : modelClass E K beta kappa sigma := ⟨Pplus, hp⟩
  let pm : modelClass E K beta kappa sigma := ⟨Pminus, hm⟩
  have hrho := frontierRate_nonneg beta kappa sigma n ((le_max_right _ _).trans hn) hsigma.1
  have hdelta : 0 ≤ c * frontierRate beta kappa sigma n := mul_nonneg hc.le hrho
  have := experiment_isProbabilityMeasure (Pplus : Measure (StructSpace S)) n sigma
  have := experiment_isProbabilityMeasure (Pminus : Measure (StructSpace S)) n sigma
  have : IsProbabilityMeasure seedLaw := by
    constructor
    norm_num [seedLaw, Measure.restrict_apply_univ, Real.volume_Icc]
  have : IsProbabilityMeasure (randomizedExperiment n sigma (Pplus : Measure (StructSpace S))) := by
    unfold randomizedExperiment
    infer_instance
  have : IsProbabilityMeasure (randomizedExperiment n sigma (Pminus : Measure (StructSpace S))) := by
    unfold randomizedExperiment
    infer_instance
  have htvSeed : Causalean.Stat.tvDist
      (randomizedExperiment n sigma (Pplus : Measure (StructSpace S)))
      (randomizedExperiment n sigma (Pminus : Measure (StructSpace S))) ≤ 1/5 :=
    (tvDist_common_seed_le _ _ seedLaw).trans (htv.trans htau5)
  have hrisk : ENNReal.ofReal ((c * frontierRate beta kappa sigma n)/5) ≤
      minimaxRisk E K beta kappa n sigma := by
    apply Causalean.Stat.le_minimaxValueENNReal_of_two_point pp pm
    intro T
    exact absolute_risk_two_point_lower _ _ T.1 T.2 _ _ _ hdelta hsep htvSeed
  have hlen : ENNReal.ofReal ((c * frontierRate beta kappa sigma n)*(1-2*alpha-tau)) ≤
      honestLength E K beta kappa alpha n sigma := by
    unfold honestLength
    apply le_iInf
    intro CI
    apply le_iSup_of_le pp
    have hcoverP := CI.2 pp
    have hcoverM := CI.2 pm
    exact connected_interval_two_point_lower _ _ CI.1.C CI.1.connected CI.1.measurable
      _ _ _ alpha tau hdelta (by linarith [halpha.2]) hsep hcoverP hcoverM htv
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hrisk
    nlinarith [mul_le_mul_of_nonneg_left htau5 hdelta]
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlen
    nlinarith [mul_le_mul_of_nonneg_left htauA hdelta]

/-- [Assuming the four cited Jacobi-packet facts](hyp:hLocalization_of_gate,hLipschitz_of_gate,hNorm_of_gate,hGamma_of_gate), [for any public class constants](hyp:K) [whose envelope constants bracket the power-density coefficient (κ+1)2^κ](hyp:hK), [smoothness exponent positive and at most one](hyp:hbeta), [design exponent between zero and two](hyp:hkappa) and [noncoverage level strictly between zero and one half](hyp:halpha), [minimax absolute risk and honest expected connected length at that level share the full uniform three-regime frontier, its elbows, and the fixed-positive-noise order](goal); the constants depend on the noncoverage level and on the class constants. -/
-- @node: thm:uniform-frontier
theorem uniform_frontier (hLocalization_of_gate : FilteredJacobiLocalization)
    (hLipschitz_of_gate : FilteredJacobiLipschitz)
    (hNorm_of_gate : JacobiNormOrthogonality)
    (hGamma_of_gate : GammaRatioAsymptotic) (K : ClassConstants) (beta kappa alpha : ℝ)
    (hbeta : beta ∈ Ioc (0 : ℝ) 1) (hkappa : kappa ∈ Icc (0 : ℝ) 2)
    (halpha : alpha ∈ Ioo (0 : ℝ) (1/2)) -- @realizes alpha(public noncoverage level below one half for the frontier)
    (hK : K.clo ≤ (kappa+1)*(2 : ℝ)^kappa ∧ (kappa+1)*(2 : ℝ)^kappa ≤ K.chi) :
    (∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ n0 : ℕ, ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      (∀ sigma ∈ Icc (0 : ℝ) (1/4),
        ENNReal.ofReal (c*frontierRate beta kappa sigma n) ≤ minimaxRisk E K beta kappa n sigma ∧
        minimaxRisk E K beta kappa n sigma ≤ ENNReal.ofReal (C*frontierRate beta kappa sigma n) ∧
        ENNReal.ofReal (c*frontierRate beta kappa sigma n) ≤ honestLength E K beta kappa alpha n sigma ∧
        honestLength E K beta kappa alpha n sigma ≤ ENNReal.ofReal (C*frontierRate beta kappa sigma n)) ∧
      (directScale beta kappa n ≤ C*fourierScale beta kappa (directScale beta kappa n) n ∧
        fourierScale beta kappa (directScale beta kappa n) n ≤ C*directScale beta kappa n) ∧
      (fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤ C*polynomialScale ((logScale n)^(-1/2 : ℝ)) n ∧
        polynomialScale ((logScale n)^(-1/2 : ℝ)) n ≤ C*fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n)) ∧
    (∀ W : ℝ, 1 ≤ W → ∃ CK : ℝ, 1 ≤ CK ∧ ∃ nK : ℕ, ∀ n ≥ nK,
      0 < directScale beta kappa n / W ∧ W * directScale beta kappa n ≤ 1/4 ∧
      0 < (logScale n)^(-1/2 : ℝ) / W ∧ W * (logScale n)^(-1/2 : ℝ) ≤ 1/4 ∧
      (∀ sigma ∈ Icc (directScale beta kappa n / W) (W * directScale beta kappa n),
        CK⁻¹ * directScale beta kappa n ≤ fourierScale beta kappa sigma n ∧
        fourierScale beta kappa sigma n ≤ CK * directScale beta kappa n) ∧
      (∀ sigma ∈ Icc ((logScale n)^(-1/2 : ℝ) / W) (W * (logScale n)^(-1/2 : ℝ)),
        CK⁻¹ * polynomialScale sigma n ≤ fourierScale beta kappa sigma n ∧
        fourierScale beta kappa sigma n ≤ CK * polynomialScale sigma n)) ∧
    (∀ sigma ∈ Ioc (0 : ℝ) (1/4), ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∃ n0 : ℕ,
      ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
      ENNReal.ofReal (c*(Real.log (Real.log n)/Real.log n)^beta) ≤ minimaxRisk E K beta kappa n sigma ∧
      minimaxRisk E K beta kappa n sigma ≤ ENNReal.ofReal (C*(Real.log (Real.log n)/Real.log n)^beta) ∧
      ENNReal.ofReal (c*(Real.log (Real.log n)/Real.log n)^beta) ≤ honestLength E K beta kappa alpha n sigma ∧
      honestLength E K beta kappa alpha n sigma ≤ ENNReal.ofReal (C*(Real.log (Real.log n)/Real.log n)^beta)) := by
  obtain ⟨CR, hCR, nR, hRiskUpper⟩ := minimaxRisk_frontier_upper.{u} K beta kappa hbeta hkappa
  obtain ⟨CH, hCH, nH, hLengthUpper⟩ := honestLength_frontier_upper.{u} K beta kappa alpha hbeta hkappa
    ⟨halpha.1, by linarith [halpha.2]⟩
  constructor
  · obtain ⟨c, hc, nL, hnL1, hlower⟩ := frontier_both_lower.{u}
      hLocalization_of_gate hLipschitz_of_gate hNorm_of_gate hGamma_of_gate
      K beta kappa alpha hbeta hkappa halpha hK
    -- The second-elbow scales are comparable by the logarithmic denominator bounds.
    have hSecondElbow : ∃ CE : ℝ, 0 < CE ∧ ∃ nE : ℕ, ∀ n ≥ nE,
        fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤
          CE * polynomialScale ((logScale n)^(-1/2 : ℝ)) n ∧
        polynomialScale ((logScale n)^(-1/2 : ℝ)) n ≤
          CE * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n := by
      apply secondElbow_comparison beta kappa
      unfold effDim
      linarith [hbeta.1, hkappa.1]
    obtain ⟨CE, hCE, nE, hsecond⟩ := hSecondElbow
    have hLowerAndSecondElbow : ∃ c C : ℝ, 0 < c ∧ c < C ∧ CR ≤ C ∧ CH ≤ C ∧
        Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C ∧
        1 / Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C ∧
        ∃ n0 : ℕ, nR ≤ n0 ∧ nH ≤ n0 ∧ 1 ≤ n0 ∧
        ∀ (S : Type u) [MeasurableSpace S], ∀ E : PathSpace S, ∀ n ≥ n0,
        (∀ sigma ∈ Icc (0 : ℝ) (1/4),
          ENNReal.ofReal (c * frontierRate beta kappa sigma n) ≤ minimaxRisk E K beta kappa n sigma ∧
          ENNReal.ofReal (c * frontierRate beta kappa sigma n) ≤ honestLength E K beta kappa alpha n sigma) ∧
        (fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n ≤ C * polynomialScale ((logScale n)^(-1/2 : ℝ)) n ∧
          polynomialScale ((logScale n)^(-1/2 : ℝ)) n ≤ C * fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n) := by
      let C := max CR (max CH (max (Real.sqrt (Real.log (Real.exp 1 + 1)))
        (max (1 / Real.sqrt (Real.log (Real.exp 1 + 1))) (max CE (c+1)))))
      have hCRle : CR ≤ C := by simp only [C, le_max_iff, le_refl, true_or]
      have hCHle : CH ≤ C := by simp only [C, le_max_iff, le_refl, or_true, true_or]
      have hrootle : Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C := by simp only [C, le_max_iff, le_refl, or_true, true_or]
      have hinvle : 1 / Real.sqrt (Real.log (Real.exp 1 + 1)) ≤ C := by simp only [C, le_max_iff, le_refl, or_true, true_or]
      have hCEle : CE ≤ C := by simp only [C, le_max_iff, le_refl, or_true, true_or]
      have hcC : c < C := by
        have : c+1 ≤ C := by simp only [C, le_max_iff, le_refl, or_true]
        linarith
      let n0 := max nR (max nH (max nL nE))
      have hnR : nR ≤ n0 := by omega
      have hnH : nH ≤ n0 := by omega
      have hnL : nL ≤ n0 := by omega
      have hnE : nE ≤ n0 := by omega
      refine ⟨c, C, hc, hcC, hCRle, hCHle, hrootle, hinvle, n0, hnR, hnH,
        hnL1.trans hnL, ?_⟩
      intro S _ E n hn
      refine ⟨hlower S E n (hnL.trans hn), ?_⟩
      have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (hnL1.trans (hnL.trans hn))
      have hlog : 0 ≤ logScale n := Real.log_nonneg
        (one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by norm_num)) hnreal)
      have hp : 0 ≤ polynomialScale ((logScale n)^(-1/2 : ℝ)) n := by
        apply div_nonneg _ hlog
        apply Real.log_nonneg
        have hx : 0 ≤ ((logScale n)^(-1/2 : ℝ))^2 * logScale n :=
          mul_nonneg (sq_nonneg _) hlog
        have hexp : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        linarith
      have hf : 0 ≤ fourierScale beta kappa ((logScale n)^(-1/2 : ℝ)) n :=
        div_nonneg (Real.rpow_nonneg hlog _) (Real.sqrt_nonneg _)
      obtain ⟨hfp, hpf⟩ := hsecond n (hnE.trans hn)
      exact ⟨hfp.trans (mul_le_mul_of_nonneg_right hCEle hp),
        hpf.trans (mul_le_mul_of_nonneg_right hCEle hf)⟩
    obtain ⟨c, C, hc, hcC, hCRle, hCHle, hrootle, hinvle, n0, hnR, hnH, hn1,
      hremaining⟩ := hLowerAndSecondElbow
    refine ⟨c, C, hc, hcC, n0, ?_⟩
    intro S _ E n hn
    obtain ⟨hlower, helbow2⟩ := hremaining S E n hn
    have hd : effDim beta kappa ≠ 0 := by
      unfold effDim
      linarith [hbeta.1, hkappa.1]
    have helbow1 := direct_fourier_elbow_comparison beta kappa C n hd
      (hn1.trans hn) hrootle hinvle
    refine ⟨?_, helbow1, helbow2⟩
    intro sigma hsigma
    have hrho := frontierRate_nonneg beta kappa sigma n (hn1.trans hn) hsigma.1
    obtain ⟨hRiskLower, hLengthLower⟩ := hlower sigma hsigma
    refine ⟨hRiskLower, ?_, hLengthLower, ?_⟩
    · exact (hRiskUpper S E n (hnR.trans hn) sigma hsigma).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCRle hrho))
    · exact (hLengthUpper S E n (hnH.trans hn) sigma hsigma).trans
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hCHle hrho))
  · constructor
    · intro W hW
      apply frontier_transition_windows beta kappa _ W hW
      unfold effDim
      linarith [hbeta.1, hkappa.1]
    · intro sigma hsigma
      have hb : 0 ≤ beta := by linarith [hbeta.1]
      have hd : 0 < effDim beta kappa := by
        unfold effDim
        linarith [hbeta.1, hkappa.1]
      obtain ⟨nF, hF⟩ := eventually_atTop.1
        (fixedNoise_frontierRate_bounds beta kappa sigma hb hd hsigma.1)
      obtain ⟨cL, hcL, nL, hnL, hlower⟩ := frontier_both_lower.{u}
        hLocalization_of_gate hLipschitz_of_gate hNorm_of_gate hGamma_of_gate
        K beta kappa alpha hbeta hkappa halpha hK
      let c := cL * (1/4 : ℝ)^beta
      let C := max (max CR CH * (2 : ℝ)^beta) c + 1
      have hc : 0 < c := mul_pos hcL (Real.rpow_pos_of_pos (by norm_num) _)
      have hcC : c < C := by
        dsimp [C]
        linarith [le_max_right (max CR CH * (2 : ℝ)^beta) c]
      have hC : max CR CH * (2 : ℝ)^beta ≤ C := by
        dsimp [C]
        linarith [le_max_left (max CR CH * (2 : ℝ)^beta) c]
      refine ⟨c, C, hc, hcC, max nF (max nL (max nR nH)), ?_⟩
      intro S _ E n hn
      have hnF := (le_max_left nF (max nL (max nR nH))).trans hn
      have hnLR := (le_max_right nF (max nL (max nR nH))).trans hn
      have hnL' := (le_max_left nL (max nR nH)).trans hnLR
      have hnRH := (le_max_right nL (max nR nH)).trans hnLR
      have hnR' := (le_max_left nR nH).trans hnRH
      have hnH' := (le_max_right nR nH).trans hnRH
      obtain ⟨ht, hrateLo, hrateHi⟩ := hF n hnF
      have hs : sigma ∈ Icc (0 : ℝ) (1/4) := ⟨hsigma.1.le, hsigma.2⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply (ENNReal.ofReal_le_ofReal ?_).trans (hlower S E n hnL' sigma hs).1
        calc
          c * (Real.log (Real.log n) / Real.log n)^beta =
              cL * ((1/4 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta) := by
                dsimp [c]; ring
          _ ≤ cL * frontierRate beta kappa sigma n :=
            mul_le_mul_of_nonneg_left hrateLo hcL.le
      · apply (hRiskUpper S E n hnR' sigma hs).trans (ENNReal.ofReal_le_ofReal ?_)
        calc
          CR * frontierRate beta kappa sigma n ≤
              CR * ((2 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta) :=
            mul_le_mul_of_nonneg_left hrateHi hCR.le
          _ = (CR * (2 : ℝ)^beta) * (Real.log (Real.log n) / Real.log n)^beta := by ring
          _ ≤ C * (Real.log (Real.log n) / Real.log n)^beta :=
            mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right (le_max_left CR CH) (by positivity)).trans hC) ht
      · apply (ENNReal.ofReal_le_ofReal ?_).trans (hlower S E n hnL' sigma hs).2
        calc
          c * (Real.log (Real.log n) / Real.log n)^beta =
              cL * ((1/4 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta) := by
                dsimp [c]; ring
          _ ≤ cL * frontierRate beta kappa sigma n :=
            mul_le_mul_of_nonneg_left hrateLo hcL.le
      · apply (hLengthUpper S E n hnH' sigma hs).trans (ENNReal.ofReal_le_ofReal ?_)
        calc
          CH * frontierRate beta kappa sigma n ≤
              CH * ((2 : ℝ)^beta * (Real.log (Real.log n) / Real.log n)^beta) :=
            mul_le_mul_of_nonneg_left hrateHi hCH.le
          _ = (CH * (2 : ℝ)^beta) * (Real.log (Real.log n) / Real.log n)^beta := by ring
          _ ≤ C * (Real.log (Real.log n) / Real.log n)^beta :=
            mul_le_mul_of_nonneg_right
              ((mul_le_mul_of_nonneg_right (le_max_right CR CH) (by positivity)).trans hC) ht

end CausalSmith.Stat.NoisydoseWeakdesignTransition
