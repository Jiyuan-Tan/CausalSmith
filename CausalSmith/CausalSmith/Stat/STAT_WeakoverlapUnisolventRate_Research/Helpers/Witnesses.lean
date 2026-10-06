module
public import CausalSmith.Stat.STAT_WeakoverlapUnisolventRate_Research.Helpers.Template
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Thin-strip and radial testing constructions, and cited gates

The three cited logical claims are explicit proposition-valued inputs. Dorn,
*Minimax Rates Under Global Overlap Bounds* (2026), Assumptions 1–2, fixes the
remaining model recorded by `DornRemainingClassSpec`; Assumption 3 and
Theorem 1 are recorded separately by `DornSourceRateTranscription`. Gaïffas,
*Convergence Rates for Pointwise Curve Estimation with a Degenerate Design*
(2005), arXiv:math/0410354, Eq. (2.1), Definition 2, Assumption M and
Theorem 1, is the scope of
`GaiffasDegenerateDesignRate`.
-/
@[expose] public section
namespace CausalSmith.Stat.WeakOverlap
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

/-- A Bernoulli law, extended definitionally to all real parameters. For [the stated inputs and conditions](hyp:p), [the `realBernoulli` object being defined](goal). -/
noncomputable def realBernoulli (p : ℝ) : Measure Bool :=
  (ENNReal.ofReal (1 - p)) • Measure.dirac false +
    (ENNReal.ofReal p) • Measure.dirac true

/-- A valid Bernoulli parameter gives a probability measure. [For the stated inputs and conditions](hyp:p,hp), [the asserted conclusion holds](goal). -/
lemma realBernoulli_probability (p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (realBernoulli p) := by
  apply isProbabilityMeasure_iff.mpr
  simp [realBernoulli]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hp.2) hp.1]
  norm_num

/-- The law of `B` times a Bernoulli draw. For [the stated inputs and conditions](hyp:B,p), [the `scaledBernoulli` object being defined](goal). -/
noncomputable def scaledBernoulli (B p : ℝ) : Measure ℝ :=
  (realBernoulli p).map (fun b => if b then B else 0)

/-- Scaling a Bernoulli outcome preserves its total probability. [For the stated inputs and conditions](hyp:B,p,hp), [the asserted conclusion holds](goal). -/
lemma scaledBernoulli_probability (B p : ℝ) (hp : p ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (scaledBernoulli B p) := by
  haveI := realBernoulli_probability p hp
  apply isProbabilityMeasure_iff.mpr
  change (Measure.map (fun b : Bool => if b then B else 0) (realBernoulli p))
    Set.univ = 1
  rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]
  simpa using (measure_univ : (realBernoulli p) Set.univ = 1)

/-- Every scaled Bernoulli outcome lies at one of its two endpoints. [For the stated inputs and conditions](hyp:B,p), [the asserted conclusion holds](goal). -/
lemma scaledBernoulli_supported_on_endpoints (B p : ℝ) :
    ∀ᵐ y ∂scaledBernoulli B p, y ∈ ({0, B} : Set ℝ) := by
  unfold scaledBernoulli
  apply (ae_map_iff
    (by fun_prop : AEMeasurable (fun b : Bool => if b then B else 0)
      (realBernoulli p))
    (by measurability : MeasurableSet {y : ℝ | y ∈ ({0, B} : Set ℝ)})).2
  filter_upwards [] with b
  cases b <;> simp


/-- Cube-centre radial coordinate. For [the stated inputs and conditions](hyp:x), [the `centreRadius` object being defined](goal). -/
noncomputable def centreRadius {d : ℕ} (x : Fin d → ℝ) : ℝ :=
  ‖x - fun _ => (1 / 2 : ℝ)‖

/-- CDF of the centre radius on the unit cube. For [the stated inputs and conditions](hyp:d,r), [the `centreRadiusCDF` object being defined](goal). -/
noncomputable def centreRadiusCDF (d : ℕ) (r : ℝ) : ℝ :=
  min 1 ((2 * r) ^ d)

/-- The thin strip through the cube centre. For [the stated inputs and conditions](hyp:d,hd,a), [the `thinStrip` object being defined](goal). -/
noncomputable def thinStrip (d : ℕ) (hd : 2 ≤ d) (a : ℝ) : Set (Fin d → ℝ) :=
  {x | |x ⟨1, by omega⟩ - 1 / 2| ≤
    |x ⟨0, by omega⟩ - 1 / 2| ^ a}

/-- Thin-strip propensity. For [the stated inputs and conditions](hyp:d,hd,γ,a,x), [the `stripPropensity` object being defined](goal). -/
noncomputable def stripPropensity (d : ℕ) (hd : 2 ≤ d) (γ a : ℝ)
    (x : Fin d → ℝ) : ℝ := by
  classical
  exact
  min 1 ((centreRadiusCDF d (centreRadius x)) ^ ((1 : ℝ) / (γ - 1)) +
    (1 / 4 : ℝ) * if x ∈ thinStrip d hd a then 1 else 0)

/-- Kernel giving `(A,Y0,Y1,Y)` at fixed covariate `x`. For [the stated inputs and conditions](hyp:B,e,p₀,p₁,x), [the `completionAt` object being defined](goal). -/
noncomputable def completionAt {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Measure (Completion d) :=
  ((realBernoulli (e x)).prod
    ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))).map
      (fun z => (x, z.1, z.2.1, z.2.2,
        if z.1 then z.2.2 else z.2.1))

/-- Valid treatment and outcome probabilities give a causal probability kernel. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_probability {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    IsProbabilityMeasure (completionAt B e p₀ p₁ x) := by
  haveI := realBernoulli_probability (e x) he
  haveI := scaledBernoulli_probability B (p₀ x) hp₀
  haveI := scaledBernoulli_probability B (p₁ x) hp₁
  haveI : IsProbabilityMeasure
      ((realBernoulli (e x)).prod
        ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) := by
    infer_instance
  apply isProbabilityMeasure_iff.mpr
  change (((realBernoulli (e x)).prod
      ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))).map
        (fun z => (x, z.1, z.2.1, z.2.2,
          if z.1 then z.2.2 else z.2.1))) Set.univ = 1
  have hm : Measurable (fun z : Bool × ℝ × ℝ =>
      (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) := by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop
  rw [Measure.map_apply hm MeasurableSet.univ]
  simpa using (measure_univ :
    ((realBernoulli (e x)).prod
      ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) Set.univ = 1)

/-- The fixed-covariate completion records the selected potential outcome. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x), [the asserted conclusion holds](goal). -/
lemma completionAt_consistency {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    OutcomeConsistency (completionAt B e p₀ p₁ x) := by
  unfold OutcomeConsistency completionAt
  have hm : Measurable (fun z : Bool × ℝ × ℝ =>
      (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) := by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop
  have hsel : Measurable (fun ω : Completion d =>
      if ω.2.1 then ω.2.2.2.1 else ω.2.2.1) := by
    apply Measurable.ite (by measurability : MeasurableSet {ω : Completion d | ω.2.1 = true})
      (by fun_prop) (by fun_prop)
  have hs : MeasurableSet {ω : Completion d |
      ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1} := by
    exact measurableSet_eq_fun (by fun_prop) hsel
  apply (ae_map_iff hm.aemeasurable hs).2
  filter_upwards [] with z
  cases z.1 <;> simp

/-- The fixed-covariate completion retains its input covariate. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_covariate_marginal {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    (completionAt B e p₀ p₁ x).map Prod.fst = Measure.dirac x := by
  haveI := realBernoulli_probability (e x) he
  haveI := scaledBernoulli_probability B (p₀ x) hp₀
  haveI := scaledBernoulli_probability B (p₁ x) hp₁
  unfold completionAt
  have hm : Measurable (fun z : Bool × ℝ × ℝ =>
      (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) := by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop
  rw [Measure.map_map measurable_fst hm]
  change Measure.map (fun _ : Bool × ℝ × ℝ => x)
    ((realBernoulli (e x)).prod
      ((scaledBernoulli B (p₀ x)).prod (scaledBernoulli B (p₁ x)))) = _
  rw [Measure.map_const, measure_univ, one_smul]

/-- Integrating valid fixed-covariate completions preserves the base law. [For the stated inputs and conditions](hyp:d,μ,B,e,p₀,p₁,hk,hp), [the asserted conclusion holds](goal). -/
lemma completionBind_covariate_marginal {d : ℕ} (μ : Measure (Fin d → ℝ))
    (B : ℝ) (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (hk : AEMeasurable (completionAt B e p₀ p₁) μ)
    (hp : ∀ᵐ x ∂μ, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    (μ.bind (completionAt B e p₀ p₁)).map Prod.fst = μ := by
  ext s hs
  rw [Measure.map_apply measurable_fst hs, Measure.bind_apply (measurable_fst hs) hk]
  simp_rw [← Measure.map_apply measurable_fst hs]
  calc
    _ = ∫⁻ x, (Measure.dirac x) s ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hp] with x hx
      rw [completionAt_covariate_marginal B e p₀ p₁ x hx.1 hx.2.1 hx.2.2]
    _ = μ s := by
      simp only [Measure.dirac_apply' _ hs]
      exact lintegral_indicator_one hs

/-- Mixing fixed-covariate completions preserves outcome consistency. [For the stated inputs and conditions](hyp:d,μ,B,e,p₀,p₁,hk), [the asserted conclusion holds](goal). -/
lemma completionBind_consistency {d : ℕ} (μ : Measure (Fin d → ℝ))
    (B : ℝ) (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (hk : AEMeasurable (completionAt B e p₀ p₁) μ) :
    OutcomeConsistency (μ.bind (completionAt B e p₀ p₁)) := by
  let S : Set (Completion d) :=
    {ω | ω.2.2.2.2 = if ω.2.1 then ω.2.2.2.1 else ω.2.2.1}
  have hsel : Measurable (fun ω : Completion d =>
      if ω.2.1 then ω.2.2.2.1 else ω.2.2.1) := by
    apply Measurable.ite (by measurability : MeasurableSet {ω : Completion d | ω.2.1 = true})
      (by fun_prop) (by fun_prop)
  have hS : MeasurableSet S := by
    exact measurableSet_eq_fun (by fun_prop) hsel
  have hzero : (μ.bind (completionAt B e p₀ p₁)) Sᶜ = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ ∫⁻ x, (completionAt B e p₀ p₁ x) Sᶜ ∂μ :=
        Measure.bind_apply_le _ hS.compl
      _ = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [] with x
        exact (measure_eq_zero_iff_ae_notMem).2
          (by simpa only [OutcomeConsistency, S, Set.mem_compl_iff, not_not,
                Set.mem_ofPred_eq] using
            completionAt_consistency B e p₀ p₁ x)
  simpa only [OutcomeConsistency, S, Set.mem_compl_iff, not_not,
    Set.mem_ofPred_eq] using (measure_eq_zero_iff_ae_notMem).mp hzero

/-- Both potential outcomes in a Bernoulli completion lie at its two endpoints. [For the stated inputs and conditions](hyp:d,B,e,p₀,p₁,x,he,hp₀,hp₁), [the asserted conclusion holds](goal). -/
lemma completionAt_supported_on_endpoints {d : ℕ} (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (he : e x ∈ Set.Icc 0 1) (hp₀ : p₀ x ∈ Set.Icc 0 1)
    (hp₁ : p₁ x ∈ Set.Icc 0 1) :
    ∀ᵐ ω ∂completionAt B e p₀ p₁ x,
      ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
        ω.2.2.2.1 ∈ ({0, B} : Set ℝ) := by
  unfold completionAt
  have hmap : Measurable (fun z : Bool × ℝ × ℝ =>
      (x, z.1, z.2.1, z.2.2, if z.1 then z.2.2 else z.2.1)) := by
    have hlast : Measurable (fun z : Bool × ℝ × ℝ =>
        if z.1 then z.2.2 else z.2.1) :=
      Measurable.ite (measurable_fst (MeasurableSet.singleton true))
        (by fun_prop) (by fun_prop)
    fun_prop
  haveI := realBernoulli_probability (e x) he
  haveI := scaledBernoulli_probability B (p₀ x) hp₀
  haveI := scaledBernoulli_probability B (p₁ x) hp₁
  rw [ae_map_iff hmap.aemeasurable
    (by measurability : MeasurableSet
      {ω : Completion d | ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
        ω.2.2.2.1 ∈ ({0, B} : Set ℝ)})]
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [] with b
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
  filter_upwards [scaledBernoulli_supported_on_endpoints B (p₀ x)] with y₀ hy₀
  filter_upwards [scaledBernoulli_supported_on_endpoints B (p₁ x)] with y₁ hy₁
  exact ⟨hy₀, hy₁⟩

/-- Mixing valid Bernoulli completions retains the endpoint support of both
potential outcomes. [For the stated inputs and conditions](hyp:d,μ,B,e,p₀,p₁,hp), [the asserted conclusion holds](goal). -/
lemma completionBind_supported_on_endpoints {d : ℕ}
    (μ : Measure (Fin d → ℝ)) (B : ℝ)
    (e p₀ p₁ : (Fin d → ℝ) → ℝ)
    (hp : ∀ᵐ x ∂μ, e x ∈ Set.Icc 0 1 ∧ p₀ x ∈ Set.Icc 0 1 ∧
      p₁ x ∈ Set.Icc 0 1) :
    ∀ᵐ ω ∂μ.bind (completionAt B e p₀ p₁),
      ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
        ω.2.2.2.1 ∈ ({0, B} : Set ℝ) := by
  let S : Set (Completion d) :=
    {ω | ω.2.2.1 ∈ ({0, B} : Set ℝ) ∧
      ω.2.2.2.1 ∈ ({0, B} : Set ℝ)}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  have hzero : (μ.bind (completionAt B e p₀ p₁)) Sᶜ = 0 := by
    apply le_antisymm _ zero_le
    calc
      _ ≤ ∫⁻ x, (completionAt B e p₀ p₁ x) Sᶜ ∂μ :=
        Measure.bind_apply_le _ hS.compl
      _ = 0 := by
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards [hp] with x hx
        apply (measure_eq_zero_iff_ae_notMem).2
        filter_upwards [completionAt_supported_on_endpoints B e p₀ p₁ x
          hx.1 hx.2.1 hx.2.2] with ω hω
        simpa only [S, Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hω
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp hzero] with ω hω
  simpa only [S, Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hω


/-- Common bounded Bernoulli response success probability. For [the stated inputs and conditions](hyp:B,L), [the `baselineSuccess` object being defined](goal). -/
noncomputable def baselineSuccess (B L : ℝ) : ℝ :=
  min (1 / 4) (L / (4 * B))

/-- Causal completion of the thin-strip law. For [the stated inputs and conditions](hyp:d,hd,γ,L,B,a), [the `thinStripCompletion` object being defined](goal). -/
noncomputable def thinStripCompletion (d : ℕ) (hd : 2 ≤ d) (γ L B a : ℝ) :
    Measure (Completion d) :=
  (volume.restrict (cube d)).bind
    (completionAt B (stripPropensity d hd γ a)
      (fun _ => baselineSuccess B L) (fun _ => baselineSuccess B L))

-- @node: def:thin-strip
/-- Observed thin-strip law on its stated exponent domain. For [the stated inputs and conditions](hyp:d,hd,γ,L,B,a,_ha), [the `thinStripLaw` object being defined](goal). -/
noncomputable def thinStripLaw (d : ℕ) (hd : 2 ≤ d)
    (γ L B a : ℝ) (_ha : 1 < a ∧ a < 1 + d / (γ - 1)) : Measure (Obs d) :=
  (thinStripCompletion d hd γ L B a).map observed -- @realizes Pstrip(observed witness law)

/-- Cube-truncated radial CDF around any point, including boundary points. For [the stated inputs and conditions](hyp:x₀,r), [the `radialCDF` object being defined](goal). -/
noncomputable def radialCDF {d : ℕ} (x₀ : Fin d → ℝ) (r : ℝ) : ℝ :=
  ∏ i, max 0 (min 1 (x₀ i + r) - max 0 (x₀ i - r))

/-- Radial propensity for the Bernoulli testing experiment. For [the stated inputs and conditions](hyp:x₀,γ,x), [the `radialPropensity` object being defined](goal). -/
noncomputable def radialPropensity {d : ℕ} (x₀ : Fin d → ℝ) (γ : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  (radialCDF x₀ ‖x - x₀‖) ^ ((1 : ℝ) / (γ - 1))

/-- The radial treatment probability is a measurable covariate function. [For the stated inputs and conditions](hyp:d,x₀,γ), [the asserted conclusion holds](goal). -/
lemma radialPropensity_measurable {d : ℕ} (x₀ : Fin d → ℝ) (γ : ℝ) :
    Measurable (radialPropensity x₀ γ) := by
  unfold radialPropensity radialCDF
  fun_prop

/-- Explicit smooth product bump supported on the closed sup-norm unit box. For [the stated inputs and conditions](hyp:z), [the `smoothBump` object being defined](goal). -/
noncomputable def smoothBump {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  ∏ i, if |z i| < 1 then Real.exp (1 - 1 / (1 - (z i) ^ 2)) else 0

/-- Treated Bernoulli success parameter for one testing law. For [the stated inputs and conditions](hyp:j,x₀,β,B,L,a,h,x), [the `pairSuccess` object being defined](goal). -/
noncomputable def pairSuccess {d : ℕ} (j : Bool) (x₀ : Fin d → ℝ)
    (β B L a h : ℝ) (x : Fin d → ℝ) : ℝ :=
  baselineSuccess B L + if j then a * h ^ β *
    smoothBump (fun i => (x i - x₀ i) / h) else 0

/-- Both Bernoulli response probabilities are measurable, including at the
boundary of the bump support. [For the stated inputs and conditions](hyp:d,j,x₀,β,B,L,a,h), [the asserted conclusion holds](goal). -/
lemma pairSuccess_measurable {d : ℕ} (j : Bool) (x₀ : Fin d → ℝ)
    (β B L a h : ℝ) : Measurable (pairSuccess j x₀ β B L a h) := by
  have hfactor (i : Fin d) : Measurable (fun x : Fin d → ℝ =>
      if |(x i - x₀ i) / h| < 1 then
        Real.exp (1 - 1 / (1 - ((x i - x₀ i) / h) ^ 2)) else 0) := by
    apply Measurable.ite
    · exact measurableSet_lt (by fun_prop) measurable_const
    · fun_prop
    · fun_prop
  have hprod : Measurable (fun x : Fin d → ℝ =>
      ∏ i : Fin d, if |(x i - x₀ i) / h| < 1 then
        Real.exp (1 - 1 / (1 - ((x i - x₀ i) / h) ^ 2)) else 0) := by
    fun_prop (disch := assumption)
  cases j
  · unfold pairSuccess
    simp
  · unfold pairSuccess smoothBump
    simp only [↓reduceIte]
    exact measurable_const.add (measurable_const.mul hprod)

/-- The positive pair constants for which every Bernoulli parameter is in
`[0,1]` on the cube at every positive sample size. The measure construction
below remains total even outside this probability-law domain. For [the stated inputs and conditions](hyp:d,β,B,L,γ,a,c,x₀), [the `boundedLowerPairAdmissible` object being defined](goal). -/
def boundedLowerPairAdmissible (d : ℕ) (β B L γ a c : ℝ)
    (x₀ : Fin d → ℝ) : Prop :=
  0 < a ∧ 0 < c ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x ∈ cube d,
      radialPropensity x₀ γ x ∈ Set.Icc 0 1 ∧
      pairSuccess false x₀ β B L a (c * oracleMesh d n β γ) x ∈ Set.Icc 0 1 ∧
      pairSuccess true x₀ β B L a (c * oracleMesh d n β γ) x ∈ Set.Icc 0 1

/-- Completion for one law in the bounded radial testing pair. For [the stated inputs and conditions](hyp:d,n,β,B,L,γ,a,c,x₀,j), [the `lowerPairCompletion` object being defined](goal). -/
noncomputable def lowerPairCompletion (d n : ℕ) (β B L γ a c : ℝ)
    (x₀ : Fin d → ℝ) (j : Bool) : Measure (Completion d) :=
  let h := c * oracleMesh d n β γ
  (volume.restrict (cube d)).bind
    (completionAt B (radialPropensity x₀ γ)
      (fun _ => baselineSuccess B L) (pairSuccess j x₀ β B L a h))

-- @node: def:bounded-lower-pair
/-- Totalized observed bounded Bernoulli testing pair for every positive
`a,c`. On `boundedLowerPairAdmissible`, all three Bernoulli parameters lie
in `[0,1]` for every `n ≥ 1` and every covariate in the cube. For [the stated inputs and conditions](hyp:d,β,B,L,γ,a,c,x₀,_ha,_hc), [the `boundedLowerPair` object being defined](goal). -/
noncomputable def boundedLowerPair (d : ℕ) (β B L γ a c : ℝ)
    (x₀ : Fin d → ℝ) (_ha : 0 < a) (_hc : 0 < c) : Bool → ℕ → Measure (Obs d) :=
  fun j n => (lowerPairCompletion d n β B L γ a c x₀ j).map observed
  -- @realizes Ppair(pair of radial Bernoulli law families)

-- @node: def:joint-adaptation-handle
/-- Descriptive, nonassertive adaptation proposal. It defines no estimator,
comparison rule, envelope functional, existence claim, or risk theorem. [the `jointAdaptationHandle` object being defined](goal). -/
def jointAdaptationHandle : _root_.String :=
  "Descriptive, nonassertive proposal: sample splitting would compare equal-cell " ++
  "fits across polynomial degrees and treatment-count-feasible meshes. The count " ++
  "selector would control the overlap axis, and held-out Lepski inequalities " ++
  "would control the smoothness axis. The target is one response estimator with " ++
  "an adaptive-risk envelope over compact rectangles of beta and gamma. No " ++
  "sample split, comparison rule, Lepski threshold, estimator, or envelope " ++
  "functional is defined, and no estimator-existence or risk-bound claim is asserted."

-- @node: oeq:joint-adaptation
/-- Open question, recorded as a nonassertive text carrier. [the `jointAdaptationQuestion` object being defined](goal). -/
def jointAdaptationQuestion : _root_.String :=
  "Over compact rectangles in (1,infinity)^2 for (beta,gamma) in the " ++
  "bounded-outcome global-tail class, can the two-axis sample-splitting and " ++
  "held-out Lepski handle produce one estimator attaining oracle pointwise and " ++
  "expected-supremum scales? What logarithmic penalty, if any, is minimax " ++
  "unavoidable? Open: neither a multiscale comparison theorem across changing " ++
  "polynomial degrees nor an adaptive lower experiment is available. Count " ++
  "selection adapts to gamma without a logarithm when beta is known. " ++
  "Gaiffas's narrower univariate experiment does not transfer its lower bound " ++
  "to this bounded causal class. No answer, procedure, penalty value, or " ++
  "estimator witness is asserted."

/-- Regular variation at zero from the right, on the positive-radius domain. For [the stated inputs and conditions](hyp:r,g), [the `RegularlyVaryingAtZero` object being defined](goal). -/
def RegularlyVaryingAtZero (r : ℝ) (g : ℝ → ℝ) : Prop :=
  ContinuousOn g (Set.Ioi 0) ∧
  (∀ h : ℝ, 0 < h → 0 < g h) ∧
  ∀ y : ℝ, 0 < y → Filter.Tendsto
    (fun h : ℝ => g (y * h) / g h)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (y ^ r))

/-- Slow variation at zero from the right is regular variation of index zero. For [the stated inputs and conditions](hyp:ℓ), [the `SlowlyVaryingAtZero` object being defined](goal). -/
def SlowlyVaryingAtZero (ℓ : ℝ → ℝ) : Prop :=
  RegularlyVaryingAtZero 0 ℓ

/-- Gaussian random-design regression law with density on the real line. For [the stated inputs and conditions](hyp:ρ,σ,f), [the `gaiffasObservedLaw` object being defined](goal). -/
noncomputable def gaiffasObservedLaw (ρ : ℝ → ℝ) (σ : ℝ)
    (f : ℝ → ℝ) : Measure (ℝ × ℝ) :=
  (volume.withDensity
    (fun x => ENNReal.ofReal (ρ x))).bind
      (fun x => (gaussianReal (f x) ⟨σ ^ 2, sq_nonneg σ⟩).map
        (fun y => (x, y)))

/-- Local approximation class at the sample-size-dependent bandwidth. For [the stated inputs and conditions](hyp:x₀,s,δ,ω,f), [the `gaiffasLocalClass` object being defined](goal). -/
def gaiffasLocalClass (x₀ s δ : ℝ) (ω : ℝ → ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → h ≤ δ →
    ∃ coeff : ℕ → ℝ, ∀ x : ℝ, |x - x₀| ≤ h →
      |f x - ∑ j ∈ Finset.range (Nat.floor s + 1), coeff j * (x - x₀) ^ j| ≤ ω h

/-- Gaïffas's class Sigma_n = F_(h_n)(x₀,ω) ∩ U(α_n), on the
measurable regression functions defining the Gaussian experiment. For [the stated inputs and conditions](hyp:x₀,s,ω,hₙ,αₙ,n,f), [the `gaiffasSigma` object being defined](goal). -/
def gaiffasSigma (x₀ s : ℝ) (ω : ℝ → ℝ)
    (hₙ αₙ : ℕ → ℝ) (n : ℕ) (f : ℝ → ℝ) : Prop :=
  Measurable f ∧ gaiffasLocalClass x₀ s (hₙ n) ω f ∧
    ∀ x : ℝ, |f x| ≤ αₙ n

/-- Rooted pointwise L^p minimax risk in the fixed-design Gaussian experiment. For [the stated inputs and conditions](hyp:ρ,σ,p,s,x₀,ω,hₙ,αₙ,n), [the `gaiffasPointwiseRisk` object being defined](goal). -/
noncomputable def gaiffasPointwiseRisk (ρ : ℝ → ℝ) (σ p s x₀ : ℝ)
    (ω : ℝ → ℝ) (hₙ αₙ : ℕ → ℝ) (n : ℕ) : ℝ≥0∞ :=
  (⨅ (T : {T : (Fin n → ℝ × ℝ) → ℝ // Measurable T}),
    ⨆ (f : ℝ → ℝ)
      (_ : gaiffasSigma x₀ s ω hₙ αₙ n f),
      ∫⁻ z, ENNReal.ofReal (|T.1 z - f x₀| ^ p)
        ∂Measure.pi (fun _ : Fin n => gaiffasObservedLaw ρ σ f)) ^ (1 / p)

-- @node: lem:gaiffas-degenerate-design-rate
/-- Gaïffas (2005), *Convergence Rates for Pointwise Curve Estimation with a
Degenerate Design*, arXiv:math/0410354, Eq. (2.1), Definition 2,
Assumption M and Theorem 1 (2.4)–(2.5), with the positive, divergent
approximation radii used by Proposition 6 for the lower bound. Radial density
continuity is required only at positive radii, so a singularity at the target
point is allowed. This is the rooted L^p risk on the sample-size-dependent
local approximation class in the univariate Gaussian experiment. Both the
slowly varying rate and `ω (hₙ n)` have eventual two-sided risk bounds, with
comparison constants depending only on `s,b,p`, not on `σ`. [the `GaiffasDegenerateDesignRate` object being defined](goal). -/
def GaiffasDegenerateDesignRate : Sort 0 :=
  ∀ (p s b : ℝ), 0 < p → 0 < s → -1 < b →
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ (x₀ : ℝ) (ρ ν ω : ℝ → ℝ),
        Measurable ρ → (∀ x : ℝ, 0 ≤ ρ x) →
        (∃ W : Set ℝ, IsOpen W ∧ x₀ ∈ W ∧
          ∀ x ∈ W, ρ x = ν |x - x₀|) →
        RegularlyVaryingAtZero b ν →
        RegularlyVaryingAtZero s ω →
        (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) Set.univ = 1 →
        ∃ ℓ : ℝ → ℝ, SlowlyVaryingAtZero ℓ ∧
        ∀ (σ : ℝ) (hₙ αₙ : ℕ → ℝ), 0 < σ →
        (∀ n : ℕ, 1 ≤ n → 0 < hₙ n ∧
          ω (hₙ n) = σ / Real.sqrt (2 * n * ∫ t in (0 : ℝ)..hₙ n, ν t) ∧
          ∀ h : ℝ, 0 < h → h < hₙ n →
            ω h ≠ σ / Real.sqrt (2 * n * ∫ t in (0 : ℝ)..h, ν t)) →
        (∃ κ M : ℝ, 0 < κ ∧ 0 < M ∧ ∃ n₀ : ℕ,
          ∀ n ≥ n₀, αₙ n ≤ M * (n : ℝ) ^ κ) →
        (∀ n : ℕ, 0 < αₙ n) →
        Filter.Tendsto αₙ Filter.atTop Filter.atTop →
        ∃ n₀ : ℕ, ∀ n ≥ n₀,
          ENNReal.ofReal (c * σ ^ (2 * s / (1 + 2 * s + b)) *
            (n : ℝ) ^ (-s / (1 + 2 * s + b)) * ℓ ((n : ℝ)⁻¹)) ≤
            gaiffasPointwiseRisk ρ σ p s x₀ ω hₙ αₙ n ∧
          gaiffasPointwiseRisk ρ σ p s x₀ ω hₙ αₙ n ≤
            ENNReal.ofReal (C * σ ^ (2 * s / (1 + 2 * s + b)) *
              (n : ℝ) ^ (-s / (1 + 2 * s + b)) * ℓ ((n : ℝ)⁻¹)) ∧
          ENNReal.ofReal (c * ω (hₙ n)) ≤
            gaiffasPointwiseRisk ρ σ p s x₀ ω hₙ αₙ n ∧
          gaiffasPointwiseRisk ρ σ p s x₀ ω hₙ αₙ n ≤
            ENNReal.ofReal (C * ω (hₙ n))

/-- Conditional observed outcome distribution in arm `a`. For [the stated inputs and conditions](hyp:P,x,a), [the `armKernel` object being defined](goal). -/
noncomputable def armKernel {d : ℕ} (P : Measure (Obs d))
    [IsFiniteMeasure P] (x : Fin d → ℝ) (a : Bool) : Measure ℝ :=
  condDistrib (fun z : Obs d => z.2.2) (fun z => (z.1, z.2.1)) P (x, a)

/-- Dorn's `Σ(β,L₀)` controls only the highest coordinate derivatives on
the closed source cube, using intrinsic traces. It imposes no bound on the
function or its lower derivatives and selects no outside extension. For [the stated inputs and conditions](hyp:β,L₀,g), [the `DornTopDerivativeSeminorm` object being defined](goal). -/
def DornTopDerivativeSeminorm {d : ℕ} (β L₀ : ℝ)
    (g : (Fin d → ℝ) → ℝ) : Prop :=
  ContDiffOn ℝ (polynomialDegree β) g (dornCube d) ∧
  ∀ α : Fin d → ℕ, (∑ i, α i) = polynomialDegree β →
    ∀ f : Fin (∑ i, α i) → Fin d,
      (∀ i, (Finset.univ.filter (fun k => f k = i)).card = α i) →
      ∀ x ∈ dornCube d, ∀ y ∈ dornCube d,
        |Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
            (dornCube d) (∑ i, α i) g f x -
          Causalean.Mathlib.Analysis.Calculus.CubeExtension.coordJetOn
            (dornCube d) (∑ i, α i) g f y| ≤
          L₀ * (Real.sqrt (∑ i, (x i - y i) ^ 2)) ^
            (β - (polynomialDegree β : ℝ))

/-- A measurable selected conditional propensity, strictly between zero and
one almost surely. Assumptions 1–2 impose no pointwise range at null points. For [the stated inputs and conditions](hyp:P,e), [the `DornA12SelectedPropensity` object being defined](goal). -/
def DornA12SelectedPropensity {d : ℕ}
    (P : Measure (Obs d)) (e : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ hP : IsProbabilityMeasure P,
    letI : IsProbabilityMeasure P := hP
    Measurable e ∧
    (∀ᵐ x ∂covariateLaw P, e x = propensity P x ∧ 0 < e x ∧ e x < 1)

/-- An A3 selected version also meets the almost-sure A1/A2 requirements. [For the stated inputs and conditions](hyp:d,S,P,e,h), [the asserted conclusion holds](goal). -/
lemma DornSelectedPropensity.toA12 {d : ℕ} {S : Set (Fin d → ℝ)}
    {P : Measure (Obs d)} {e : (Fin d → ℝ) → ℝ}
    (h : DornSelectedPropensity S P e) : DornA12SelectedPropensity P e := by
  obtain ⟨hP, he, _, hae⟩ := h
  exact ⟨hP, he, hae⟩

/-- Dorn's Assumptions 1–2 without Assumption 3. Assumption 1(a)'s common
conditional `q`-moment bound implies `|μ₁| ≤ M`; it is derived in the transfer,
not imposed here. Assumption 1(b) is the variance bound, while the fixed Gaussian
variance in Assumption 2 supplies Assumption 1(c). The Hölder condition is only
Dorn's top-derivative seminorm, with no lower-derivative bound. The selected
propensity is measurable and almost surely the conditional
propensity in (0,1). For [the stated inputs and conditions](hyp:d,β,q,M,σ,C,L₀,γ,P,μ₁,μ₀,e), [the `DornRemainingModel` object being defined](goal). -/
def DornRemainingModel (d : ℕ) (β q M σ C L₀ γ : ℝ)
    (P : Measure (Obs d)) [IsProbabilityMeasure P]
    (μ₁ μ₀ e : (Fin d → ℝ) → ℝ) : Prop :=
  P.map Prod.fst = (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ •
    volume.restrict (dornCube d) ∧
  DornA12SelectedPropensity P e ∧
  (∀ᵐ x ∂covariateLaw P,
    Integrable (fun y : ℝ => |y| ^ q) (armKernel P x true) ∧
    (∫ y, |y| ^ q ∂armKernel P x true) ≤ M ^ q) ∧
  (∫ x, (μ₁ x - ∫ y, μ₁ y ∂covariateLaw P) ^ 2 ∂covariateLaw P) ≤ M ∧
  DornTopDerivativeSeminorm β L₀ μ₁ ∧
  DornTopDerivativeSeminorm β L₀ μ₀ ∧
  GlobalPropensityTail P e C γ ∧
  (∀ᵐ x ∂covariateLaw P,
    armKernel P x true = gaussianReal (μ₁ x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
    armKernel P x false = gaussianReal (μ₀ x) ⟨σ ^ 2, sq_nonneg σ⟩)

/-- The exact remaining class in Dorn's Section 2 after Assumption 3 is
deleted. Membership includes a probability law and every clause of
Assumptions 1–2, with only the top-derivative Hölder seminorm. For [the stated inputs and conditions](hyp:d,β,q,M,σ,C,L₀,γ), [the `DornRemainingClass` object being defined](goal). -/
def DornRemainingClass (d : ℕ) (β q M σ C L₀ γ : ℝ) :
    Set (DornSourceLaw d) :=
  {z | ∃ hP : IsProbabilityMeasure z.1,
    @DornRemainingModel d β q M σ C L₀ γ z.1 hP z.2.1 z.2.2.1 z.2.2.2}

/- Dorn's fixed-constant family formulation of Assumptions 1–2. The per-law
clauses are written directly, independently of the maximal envelope. -/
/-- For [the dimension, regularity, moment, variance, tail constants, and candidate family](hyp:d,β,q,M,σ,C,L₀,γ,𝔓),
[the Dorn Assumptions 1--2 family](goal) consists of laws satisfying [nonemptiness](step:1) and [the per-law model conditions](step:2). -/
def DornA12Family (d : ℕ) (β q M σ C L₀ γ : ℝ)
    (𝔓 : Set (DornSourceLaw d)) : Prop :=
  𝔓.Nonempty ∧
  ∀ z ∈ 𝔓, ∃ hP : IsProbabilityMeasure z.1,
    letI : IsProbabilityMeasure z.1 := hP
    covariateLaw z.1 (dornCube d) = 1 ∧
    DornA12SelectedPropensity z.1 z.2.2.2 ∧
    z.1.map Prod.fst =
      (ENNReal.ofReal ((2 : ℝ) ^ d))⁻¹ • volume.restrict (dornCube d) ∧
    (∀ᵐ x ∂covariateLaw z.1,
      Integrable (fun y : ℝ => |y| ^ q) (armKernel z.1 x true) ∧
      (∫ y, |y| ^ q ∂armKernel z.1 x true) ≤ M ^ q) ∧
    (∫ x, (z.2.1 x - ∫ y, z.2.1 y ∂covariateLaw z.1) ^ 2
      ∂covariateLaw z.1) ≤ M ∧
    (∀ᵐ x ∂covariateLaw z.1, ∀ a : Bool,
      σ ^ 2 ≤ ∫ y, (y - ∫ y, y ∂armKernel z.1 x a) ^ 2
        ∂armKernel z.1 x a) ∧
    DornTopDerivativeSeminorm β L₀ z.2.1 ∧
    DornTopDerivativeSeminorm β L₀ z.2.2.1 ∧
    GlobalPropensityTail z.1 z.2.2.2 C γ ∧
    (∀ᵐ x ∂covariateLaw z.1,
      armKernel z.1 x true =
        gaussianReal (z.2.1 x) ⟨σ ^ 2, sq_nonneg σ⟩ ∧
      armKernel z.1 x false =
        gaussianReal (z.2.2.1 x) ⟨σ ^ 2, sq_nonneg σ⟩)

-- @node: lem:dorn-remaining-class
/-- Dorn (2026), *Minimax Rates Under Global Overlap Bounds*, Section 2
Setting and Notation, Assumptions 1–2, author PDF pp. 3–7. The concrete
`DornA12Family` records the source's fixed-constant family assumptions.
The equivalence says that such a family is precisely an arbitrary nonempty
subfamily of the maximal remaining-class envelope; it does not require the
family itself to equal that envelope. For [the stated inputs and conditions](hyp:d,β,q,M,σ,C,L₀,γ), [the `DornRemainingClassSpec` object being defined](goal). -/
def DornRemainingClassSpec (d : ℕ) (β q M σ C L₀ γ : ℝ) : Sort 0 :=
  1 ≤ d → 0 < β → 3 < q → 0 < M → 0 < σ →
  0 < C → 0 < L₀ → 1 < γ →
  ∀ 𝔓 : Set (DornSourceLaw d),
    DornA12Family d β q M σ C L₀ γ 𝔓 ↔
      𝔓.Nonempty ∧ 𝔓 ⊆ DornRemainingClass d β q M σ C L₀ γ

/-- Dorn's Assumption 3 with constants shared by the whole source family. For [the stated inputs and conditions](hyp:classSet), [the `DornA3OnOriginalClass` object being defined](goal). -/
noncomputable def DornA3OnOriginalClass {d : ℕ}
    (classSet : Set (DornSourceLaw d)) : Prop :=
  DornA3 (dornCube d) classSet

-- @node: lem:dorn-source-rate-transcription
/-- Dorn (2026), *Minimax Rates Under Global Overlap Bounds*, Section 2
Notation and Setting, Assumptions 1–3, Theorem 1(ii) (author PDF pp. 3–7,
12), Lemma 11 (p. 23), Lemma 13 (p. 24), and the proof (pp. 27–28).
This source-scoped gate fixes one source
family, its common constants including gamma, and its selected propensity
representatives before selecting a measurable estimator and rate constants.
Each displayed `L∞(P_X)` exceedance event is required to be measurable, so the
upper probability comparison uses ordinary probability on the original
Gaussian cube and the source's `L∞(P_X)` norm. The printed lower clause (i)
is bibliographic attribution only: arbitrary singleton families obstruct it.
The no-gamma sentence and count thresholds are construction provenance only. [the `DornSourceRateTranscription` object being defined](goal). -/
def DornSourceRateTranscription : Sort 0 :=
  ∀ (d : ℕ) (β q M σ C L₀ γ : ℝ) (𝔓 : Set (DornSourceLaw d)),
    1 ≤ d → 0 < β → 3 < q → 0 < M → 0 < σ → 0 < C → 0 < L₀ →
    1 < γ →
      DornA12Family d β q M σ C L₀ γ 𝔓 →
      DornA3OnOriginalClass 𝔓 →
      ∃ T : ∀ n : ℕ, (Fin n → Obs d) → (Fin d → ℝ) → ℝ,
        (∀ (n : ℕ) (z : {z : DornSourceLaw d // z ∈ 𝔓}) (R : ℝ),
          MeasurableSet
            {ω | ENNReal.ofReal
                (R * (n : ℝ) ^ (-β / (2 * β + effectiveDimension d γ))) <
              eLpNorm (fun x => T n ω x - z.1.2.1 x) ⊤
                (covariateLaw z.1.1)}) ∧
        (∀ n x, Measurable (fun ω => T n ω x)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, 0 < R ∧
          Filter.limsup (fun n : ℕ =>
            ⨆ (z : {z : DornSourceLaw d // z ∈ 𝔓}),
              (Measure.pi (fun _ : Fin n => z.1.1)).real
                {ω | ENNReal.ofReal
                    (R * (n : ℝ) ^ (-β / (2 * β + effectiveDimension d γ))) <
                  eLpNorm (fun x => T n ω x - z.1.2.1 x) ⊤
                    (covariateLaw z.1.1)}) Filter.atTop ≤ ε
end CausalSmith.Stat.WeakOverlap
