module
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.Helpers.LawConstruction
public import CausalSmith.Stat.STAT_PointcateFinitepSmoothnessFrontier_Research.TOracleExperiment
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Probability.Distributions.Pareto

/-! Finite-moment point-CATE frontier: TMomentEndpoint. -/
@[expose] public section
set_option linter.style.longLine false
set_option linter.unusedVariables false
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators Topology
namespace CausalSmith.Stat.PointcateFinitepSmoothnessFrontier


/-- The scalar concave power bound used for moment-class nesting. -/
-- @node: endpoint_power_majorant
lemma endpoint_power_majorant (p y : ℝ) (hp : 1 < p ∧ p < 2) :
    |y| ^ p ≤ (1-p/2) + (p/2) * |y| ^ (2 : ℝ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted
    (show 0 ≤ p/2 by linarith) (show 0 ≤ 1-p/2 by linarith)
    (Real.rpow_nonneg (abs_nonneg y) 2) (show (0 : ℝ) ≤ 1 by norm_num)
    (by ring : p/2 + (1-p/2) = 1)
  rw [Real.one_rpow, mul_one, ← Real.rpow_mul (abs_nonneg y)] at h
  have he : (2 : ℝ) * (p/2) = p := by ring
  rw [he] at h
  simpa only [add_comm, mul_one] using h

/-- A probability law with raw second moment at most ten has every intermediate raw
moment at most ten, by integrating the scalar concave power majorant. -/
-- @node: endpoint_moment_bound
lemma endpoint_moment_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 1 < p ∧ p < 2)
    (h2 : (∫⁻ y, ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ) ≤ 10) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂μ) ≤ 10 := by
  have hs : 0 ≤ p/2 := by linarith
  have hc : 0 ≤ 1-p/2 := by linarith
  have hm : Measurable (fun y : ℝ => ENNReal.ofReal (|y| ^ (2 : ℝ))) := by fun_prop
  calc
    (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂μ) ≤
        ∫⁻ y, ENNReal.ofReal (1-p/2) + ENNReal.ofReal (p/2) *
          ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ := by
      apply lintegral_mono
      intro y
      dsimp only
      rw [← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_add hc (by positivity)]
      exact ENNReal.ofReal_le_ofReal (endpoint_power_majorant p y hp)
    _ = ENNReal.ofReal (1-p/2) + ENNReal.ofReal (p/2) *
        (∫⁻ y, ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ) := by
      rw [lintegral_add_left measurable_const, lintegral_const_mul _ hm]
      simp
    _ ≤ ENNReal.ofReal (1-p/2) + ENNReal.ofReal (p/2) * 10 := by gcongr
    _ ≤ 10 := by
      rw [show (10 : ℝ≥0∞) = ENNReal.ofReal (10 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul hs, ← ENNReal.ofReal_add hc (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      linarith

/-- All non-moment atoms are identical, and the scalar moment bound transfers both arms. -/
-- @node: second_moment_model_inclusion
lemma second_moment_model_inclusion (p α β γ : ℝ) (hp : 1 < p ∧ p < 2)
    (law : ObservedLaw) (hmodel : InModel ⟨2, α, β, γ⟩ law) :
    InModel ⟨p, α, β, γ⟩ law := by
  refine ⟨hmodel.uniform, hmodel.overlap, hmodel.propensityHolder,
    hmodel.baselineHolder, hmodel.effectHolder, hmodel.effectRange, ?_⟩
  filter_upwards [hmodel.conditionalMoment] with x hx
  intro a
  exact endpoint_moment_bound (law.Q a x) p hp (hx a)

/-- Substitution of the second-moment exponent gives the two diagnostic powers. -/
-- @node: second_moment_exponents
lemma second_moment_exponents (α β γ : ℝ) :
    rOracle ⟨2, α, β, γ⟩ = γ/(2*γ+1) ∧
    rInter ⟨2, α, β, γ⟩ = 2*(α+β)/(1+(α+β)/γ+2*(α+β)) := by
  constructor
  · unfold rOracle qExp
    dsimp only
    norm_num
    rw [mul_one_div, div_div]
    congr 1
    ring
  · unfold rInter sumReg qExp
    dsimp only
    norm_num
    congr 1
    ring

/-- The second-moment benchmark and all four revelation quantities have the endpoint powers.
The revelation inequalities use the original-experiment oracle certificate. -/
-- @node: second_moment_rate_revelation
lemma second_moment_rate_revelation (α β γ : ℝ)
    (hs : (0 < α ∧ α ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧ (0 < γ ∧ γ ≤ 1))
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
    ∀ n : ℕ, 2 ≤ n → rate ⟨2,α,β,γ⟩ n =
      max ((n : ℝ)^(-γ/(2*γ+1))) ((n : ℝ)^(-2*(α+β)/(1+(α+β)/γ+2*(α+β)))) ∧
      ∀ j : Fin 4, (3/256 : ℝ)*(n : ℝ)^(-γ/(2*γ+1)) ≤ oracleValues ⟨2,α,β,γ⟩ n expLaw j ∧
        oracleValues ⟨2,α,β,γ⟩ n expLaw j ≤ oracleUpper ⟨2,α,β,γ⟩*(n : ℝ)^(-γ/(2*γ+1)) := by
  have hκ : (Params.mk 2 α β γ).Valid := ⟨by norm_num, hs⟩
  have he := second_moment_exponents α β γ
  have ho := (oracle_experiment_concrete ⟨2,α,β,γ⟩ hκ expLaw hiid).2.1
  intro n hn
  constructor
  · unfold rate
    rw [he.1, he.2]
    simp only [neg_div, neg_mul]
  · simpa only [he.1, neg_div] using ho n hn

/-- Response moments under the Pareto density reduce to a power integral on its support. -/
-- @node: endpoint_pareto_moment_integral
lemma endpoint_pareto_moment_integral (t r s : ℝ) (ht : 0 < t) (hr : 0 < r) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂paretoMeasure t r) =
      ENNReal.ofReal (r * t ^ r) *
        ∫⁻ y in Ici t, ENNReal.ofReal (y ^ (s - r - 1)) := by
  have hm : Measurable (paretoPDF t r) := (measurable_paretoPDFReal t r).ennreal_ofReal
  rw [paretoMeasure, lintegral_withDensity_eq_lintegral_mul _ hm (by fun_prop)]
  rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator measurableSet_Ici]
  apply lintegral_congr
  intro y
  by_cases hy : t ≤ y
  · have hypos : 0 < y := ht.trans_le hy
    dsimp only [Pi.mul_apply]
    rw [indicator_of_mem (show y ∈ Ici t from hy), paretoPDF_of_le hy, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [abs_of_pos (ht.trans_le hy)]
    calc
      r * t ^ r * y ^ (-(r + 1)) * y ^ s =
          r * t ^ r * (y ^ (-(r + 1)) * y ^ s) := by ring
      _ = r * t ^ r * y ^ (s - r - 1) := by
        rw [← Real.rpow_add (ht.trans_le hy)]
        congr 2
        ring
  · simp [indicator_of_notMem (show y ∉ Ici t from hy), paretoPDF_of_lt (lt_of_not_ge hy)]

/-- A Pareto moment below the shape parameter is its explicit finite value. -/
-- @node: endpoint_pareto_finite_moment
lemma endpoint_pareto_finite_moment (t r s : ℝ) (ht : 0 < t) (hr : 0 < r)
    (hs : s < r) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂paretoMeasure t r) =
      ENNReal.ofReal (r * t ^ s / (r - s)) := by
  rw [endpoint_pareto_moment_integral t r s ht hr]
  have hi : IntegrableOn (fun y : ℝ => y ^ (s-r-1)) (Ici t) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_Ioi_rpow_of_lt (by linarith) ht)
  have hn : 0 ≤ᵐ[volume.restrict (Ici t)] (fun y : ℝ => y ^ (s-r-1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    exact Real.rpow_nonneg (ht.le.trans hy) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) ht,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hden : s-r ≠ 0 := by linarith
  rw [show s-r-1+1 = s-r by ring]
  have hden' : r-s ≠ 0 := by linarith
  field_simp [hden, hden']
  rw [← Real.rpow_add ht]
  rw [show r+(s-r)=s by ring]
  ring
/-- A Pareto moment at or above the shape parameter is infinite. -/
-- @node: endpoint_pareto_infinite_moment
lemma endpoint_pareto_infinite_moment (t r s : ℝ) (ht : 0 < t) (hr : 0 < r)
    (hs : r ≤ s) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂paretoMeasure t r) = ∞ := by
  rw [endpoint_pareto_moment_integral t r s ht hr]
  have hinf : (∫⁻ y in Ici t, ENNReal.ofReal (y ^ (s-r-1))) = ∞ := by
    by_contra h
    have hn : 0 ≤ᵐ[volume.restrict (Ici t)] (fun y : ℝ => y ^ (s-r-1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
      exact Real.rpow_nonneg (ht.le.trans hy) _
    have hi : IntegrableOn (fun y : ℝ => y ^ (s-r-1)) (Ici t) :=
      (lintegral_ofReal_ne_top_iff_integrable (by fun_prop) hn).mp h
    have hi' := (integrableOn_Ioi_rpow_iff ht).mp
      (Iff.mp integrableOn_Ici_iff_integrableOn_Ioi hi)
    linarith
  rw [hinf, ENNReal.mul_top]
  simp [ENNReal.ofReal_eq_zero, not_le.mpr (mul_pos hr (Real.rpow_pos_of_pos ht r))]

/-- Equal mixture of a positive Pareto law and its reflection. -/
-- @node: endpoint_symmetric_pareto
def endpoint_symmetric_pareto (t r : ℝ) : Measure ℝ :=
  (1/2 : ℝ≥0∞) • paretoMeasure t r +
    (1/2 : ℝ≥0∞) • (paretoMeasure t r).map (fun y => -y)

/-- The equally weighted Pareto law and its reflection form a probability measure. -/
-- @node: endpoint_symmetric_pareto_probability
lemma endpoint_symmetric_pareto_probability (t r : ℝ) (ht : 0 < t) (hr : 0 < r) :
    IsProbabilityMeasure (endpoint_symmetric_pareto t r) := by
  have := isProbabilityMeasure_paretoMeasure ht hr
  constructor
  simpa [endpoint_symmetric_pareto, Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_neg MeasurableSet.univ] using ENNReal.inv_two_add_inv_two

/-- Reflection preserves absolute moments, so the symmetric mixture has the Pareto moments. -/
-- @node: endpoint_symmetric_pareto_moment
lemma endpoint_symmetric_pareto_moment (t r s : ℝ) :
    (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂endpoint_symmetric_pareto t r) =
      ∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂paretoMeasure t r := by
  rw [endpoint_symmetric_pareto, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_map (by fun_prop) measurable_neg]
  simp only [abs_neg, smul_eq_mul, ← add_mul]
  simp only [one_div, ENNReal.inv_two_add_inv_two, one_mul]

/-- Shape greater than one gives an integrable Pareto response. -/
-- @node: endpoint_pareto_integrable
lemma endpoint_pareto_integrable (t r : ℝ) (ht : 0 < t) (hr : 1 < r) :
    Integrable (fun y : ℝ => y) (paretoMeasure t r) := by
  have hm := endpoint_pareto_finite_moment t r 1 ht (by linarith) hr
  simp only [Real.rpow_one] at hm
  have hi : Integrable (fun y : ℝ => |y|) (paretoMeasure t r) :=
    (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (ae_of_all _ fun y => abs_nonneg y)).mp (hm.trans_ne ENNReal.ofReal_ne_top)
  exact (integrable_norm_iff (by fun_prop)).mp hi

/-- The integrable reflected responses cancel in the symmetric mixture. -/
-- @node: endpoint_symmetric_pareto_mean
lemma endpoint_symmetric_pareto_mean (t r : ℝ) (ht : 0 < t) (hr : 1 < r) :
    (∫ y, y ∂endpoint_symmetric_pareto t r) = 0 := by
  have hi := endpoint_pareto_integrable t r ht hr
  have hm : Integrable (fun y : ℝ => y) ((paretoMeasure t r).map (fun y => -y)) :=
    (integrable_map_measure (by fun_prop) measurable_neg.aemeasurable).mpr hi.neg
  rw [endpoint_symmetric_pareto, integral_add_measure
    (hi.smul_measure (by norm_num)) (hm.smul_measure (by norm_num)),
    integral_smul_measure, integral_smul_measure,
    integral_map measurable_neg.aemeasurable (by fun_prop)]
  rw [integral_neg]
  ring
/-- The scaled symmetric Pareto witness in the endpoint proof roadmap. -/
-- @node: endpoint_heavy_tail_witness
lemma endpoint_heavy_tail_witness (p : ℝ) (hp : 1 < p ∧ p < 2) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ (∫ y, y ∂μ) = 0 ∧
      (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂μ) = 5 ∧
      (∫⁻ y, ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ) = ∞ := by
  let r := (p+2)/2
  have hpr : p < r := by dsimp [r]; linarith
  have hr2 : r < 2 := by dsimp [r]; linarith
  have hr1 : 1 < r := by linarith
  have hr : 0 < r := by linarith
  have hp0 : 0 < p := by linarith
  have hb : 0 < 5*(r-p)/r := by positivity
  let t := (5*(r-p)/r) ^ (1/p)
  have ht : 0 < t := Real.rpow_pos_of_pos hb _
  have htp : t ^ p = 5*(r-p)/r := by
    dsimp [t]
    rw [← Real.rpow_mul hb.le, one_div_mul_cancel (ne_of_gt hp0), Real.rpow_one]
  refine ⟨endpoint_symmetric_pareto t r,
    endpoint_symmetric_pareto_probability t r ht hr,
    endpoint_symmetric_pareto_mean t r ht hr1, ?_, ?_⟩
  · rw [endpoint_symmetric_pareto_moment,
      endpoint_pareto_finite_moment t r p ht hr hpr, htp]
    have he : r * (5*(r-p)/r) / (r-p) = 5 := by
      field_simp [ne_of_gt hr, ne_of_gt (sub_pos.mpr hpr)]
    rw [he]
    norm_num
  · rw [endpoint_symmetric_pareto_moment]
    exact endpoint_pareto_infinite_moment t r 2 ht hr hr2.le
/-- Integrating a response moment under the explicit Bernoulli record kernel. -/
-- @node: endpoint_record_moment
lemma endpoint_record_moment (e : unitInterval → ℝ) (he : Measurable e)
    (Q : Bool → Kernel unitInterval ℝ) (hq : ∀ a, IsMarkovKernel (Q a))
    (x : unitInterval) (s : ℝ) :
    (∫⁻ z, ENNReal.ofReal (|z.2| ^ s) ∂recordKernel e he Q x) =
      ENNReal.ofReal (e x) * (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂Q true x) +
      ENNReal.ofReal (1-e x) * (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂Q false x) := by
  have (a : Bool) := hq a
  change (∫⁻ z, ENNReal.ofReal (|z.2| ^ s) ∂recordMeasure e Q x) = _
  rw [recordMeasure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_prod _ (by fun_prop), lintegral_prod _ (by fun_prop)]
  simp

/-- Original-law response moments are obtained by mixing the two conditional moments. -/
-- @node: endpoint_observed_moment
lemma endpoint_observed_moment (law : ObservedLaw) (s : ℝ) :
    (∫⁻ o, ENNReal.ofReal (|Y o| ^ s) ∂law.P) =
      ∫⁻ x, ENNReal.ofReal (law.e x) * (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂law.Q true x) +
        ENNReal.ofReal (1-law.e x) * (∫⁻ y, ENNReal.ofReal (|y| ^ s) ∂law.Q false x)
        ∂law.P.map X := by
  have := recordKernel_markov law.e law.e_measurable law.e_range law.Q law.markov
  conv_lhs => rw [law.record_version]
  rw [Measure.lintegral_compProd (by unfold Y; fun_prop)]
  apply lintegral_congr
  intro x
  exact endpoint_record_moment law.e law.e_measurable law.Q law.markov x s

/-- The conditional moment envelope also bounds the original observed response moment. -/
-- @node: endpoint_model_observed_moment_bound
lemma endpoint_model_observed_moment_bound (κ : Params) (law : ObservedLaw)
    (h : InModel κ law) : (∫⁻ o, ENNReal.ofReal (|Y o| ^ κ.p) ∂law.P) ≤ 10 := by
  rw [endpoint_observed_moment, h.uniform]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (law.e x) * 10 + ENNReal.ofReal (1-law.e x) * 10
        ∂design := by
      apply lintegral_mono_ae
      filter_upwards [h.conditionalMoment] with x hx
      gcongr
      · exact hx true
      · exact hx false
    _ = 10 := by
      have hw (x : unitInterval) :
          ENNReal.ofReal (law.e x) + ENNReal.ofReal (1-law.e x) = 1 := by
        rw [← ENNReal.ofReal_add (law.e_range x).1
          (sub_nonneg.mpr (law.e_range x).2)]
        simp
      simp_rw [← add_mul, hw, one_mul]
      simp [design]
/-- The heavy-tailed witness has constant nuisance functions and cannot be represented
by any second-moment model law on the original observation space. -/
-- @node: endpoint_strict_model_witness
lemma endpoint_strict_model_witness (p α β γ : ℝ) (hp : 1 < p ∧ p < 2) :
    ∃ law, InModel ⟨p,α,β,γ⟩ law ∧
      ∀ law', law'.P = law.P → ¬ InModel ⟨2,α,β,γ⟩ law' := by
  obtain ⟨μ, hμ, hmean, hpm, h2m⟩ := endpoint_heavy_tail_witness p hp
  have := hμ
  let Q : Bool → Kernel unitInterval ℝ := fun _ => Kernel.const unitInterval μ
  have hQ : ∀ a, IsMarkovKernel (Q a) := fun _ => inferInstance
  have hm0 : ∀ᵐ x ∂design, (0 : ℝ) = ∫ y, y ∂Q false x := by
    filter_upwards [] with x
    exact hmean.symm
  have hm1 : ∀ᵐ x ∂design, (0 : ℝ)+0 = ∫ y, y ∂Q true x := by
    filter_upwards [] with x
    change (0 : ℝ)+0 = ∫ y, y ∂μ
    simpa only [zero_add] using hmean.symm
  let law := lawFromUniform (fun _ => 1/2) measurable_const half_range Q hQ
    (fun _ => 0) (fun _ => 0) hm0 hm1
  have huniform : law.P.map X = design :=
    uniformRecord_marginal _ _ half_range Q hQ
  have hconst (s c : ℝ) (hc : |c| ≤ 20) : holderBall s (fun _ => c) := by
    refine ⟨continuous_const, fun _ => hc, ?_⟩
    intro x z
    simp only [sub_self, abs_zero]
    positivity
  have hmodel : InModel ⟨p,α,β,γ⟩ law := by
    refine ⟨huniform, ?_, hconst α (1/2) (by norm_num),
      hconst β 0 (by norm_num), hconst γ 0 (by norm_num), ?_, ?_⟩
    · intro x
      change (1/4 : ℝ) ≤ 1/2 ∧ (1/2 : ℝ) ≤ 3/4
      constructor <;> norm_num
    · intro x
      change |(0 : ℝ)| ≤ 1/2
      norm_num
    · filter_upwards [] with x
      intro a
      change (∫⁻ y, ENNReal.ofReal (|y| ^ p) ∂μ) ≤ 10
      rw [hpm]
      norm_num
  have hinf : (∫⁻ o, ENNReal.ofReal (|Y o| ^ (2 : ℝ)) ∂law.P) = ∞ := by
    rw [endpoint_observed_moment, huniform]
    change (∫⁻ x : unitInterval,
      ENNReal.ofReal (1/2 : ℝ) * (∫⁻ y, ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ) +
        ENNReal.ofReal (1-1/2 : ℝ) * (∫⁻ y, ENNReal.ofReal (|y| ^ (2 : ℝ)) ∂μ)
        ∂design) = ∞
    rw [h2m]
    norm_num [ENNReal.mul_top, design]
  refine ⟨law, hmodel, ?_⟩
  intro law' heq hmodel'
  have hbound := endpoint_model_observed_moment_bound ⟨2,α,β,γ⟩ law' hmodel'
  change (∫⁻ o, ENNReal.ofReal (|Y o| ^ (2 : ℝ)) ∂law'.P) ≤ 10 at hbound
  rw [heq, hinf] at hbound
  exact (by norm_num : ¬ (∞ : ℝ≥0∞) ≤ 10) hbound

-- @node: prop:moment-endpoint
/-- For [a moment exponent strictly between one and two](hyp:p,hp),
[fixed valid smoothness exponents](hyp:α,β,γ,hs), and [iid experiments](hyp:expLaw,hiid),
[the finite-p model strictly contains the second-moment model with the same target, and the
second-moment benchmark and revelation powers reduce to point-regression precision](goal). -/
theorem moment_endpoint (p α β γ : ℝ) (hp : 1 < p ∧ p < 2)
    (hs : (0 < α ∧ α ≤ 1) ∧ (0 < β ∧ β ≤ 1) ∧ (0 < γ ∧ γ ≤ 1))
    (expLaw : ExperimentFamily) (hiid : IIDSampling expLaw) :
  (∀ law, InModel ⟨2,α,β,γ⟩ law → InModel ⟨p,α,β,γ⟩ law) ∧
  (∃ law, InModel ⟨p,α,β,γ⟩ law ∧
    ∀ law', law'.P = law.P → ¬ InModel ⟨2,α,β,γ⟩ law') ∧
  rOracle ⟨2,α,β,γ⟩ = γ/(2*γ+1) ∧
  rInter ⟨2,α,β,γ⟩ = 2*(α+β)/(1+(α+β)/γ+2*(α+β)) ∧
  (∀ n : ℕ, 2 ≤ n → rate ⟨2,α,β,γ⟩ n =
    max ((n : ℝ)^(-γ/(2*γ+1))) ((n : ℝ)^(-2*(α+β)/(1+(α+β)/γ+2*(α+β))))) ∧
  (∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ n : ℕ, 2 ≤ n → ∀ j : Fin 4,
    c*(n : ℝ)^(-γ/(2*γ+1)) ≤ oracleValues ⟨2,α,β,γ⟩ n expLaw j ∧
      oracleValues ⟨2,α,β,γ⟩ n expLaw j ≤ C*(n : ℝ)^(-γ/(2*γ+1))) := by
  have hκ : (Params.mk 2 α β γ).Valid := ⟨by norm_num, hs⟩
  have he := second_moment_exponents α β γ
  have hr := second_moment_rate_revelation α β γ hs expLaw hiid
  have hc := (oracle_experiment_concrete ⟨2,α,β,γ⟩ hκ expLaw hiid).1
  refine ⟨second_moment_model_inclusion p α β γ hp,
    endpoint_strict_model_witness p α β γ hp, he.1, he.2, ?_, ?_⟩
  · intro n hn
    exact (hr n hn).1
  · refine ⟨3/256, oracleUpper ⟨2,α,β,γ⟩, hc.1, hc.2.1, ?_⟩
    intro n hn j
    exact (hr n hn).2 j

end CausalSmith.Stat.PointcateFinitepSmoothnessFrontier
